import Catalan.Cyclotomic.Basic
import Catalan.Stickelberger.GaussCharacters

noncomputable section
namespace Catalan

/-- Coprime cyclotomic layers combine into the product conductor over the rationals. -/
lemma cyclotomic_tower_mul (p ell : ℕ) [NeZero p] [NeZero ell]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hcop : p.Coprime ell) :
    IsCyclotomicExtension {p * ell} ℚ (CyclotomicField ell K) := by
  let E := CyclotomicField ell K
  let : IsCyclotomicExtension ({p} ∪ {ell}) ℚ E :=
    IsCyclotomicExtension.trans {p} {ell} ℚ K E (algebraMap K E).injective
  apply (IsCyclotomicExtension.iff_singleton (p * ell) ℚ E).mpr
  constructor
  · have hp := (IsCyclotomicExtension.zeta_spec p ℚ K).map_of_injective
      (algebraMap K E).injective
    have he := IsCyclotomicExtension.zeta_spec ell K E
    exact ⟨_, by simpa only [hcop.lcm_eq_mul] using
      hp.pow_mul_pow_lcm he (NeZero.ne _) (NeZero.ne _)⟩
  · intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := ({p} ∪ {ell})) (A := ℚ) x
    apply Algebra.adjoin_mono _ hx
    intro z hz
    rcases hz with ⟨n, hn, hn0, hz⟩
    simp only [Set.mem_union, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl
    · simp only [Set.mem_ofPred_eq, pow_mul, hz, one_pow]
    · change z ^ (_ * _) = 1
      rw [mul_comm, pow_mul, hz, one_pow]


/-- A base cyclotomic automorphism extends while fixing the canonical additive root.
The extension is constructed by the Chinese remainder theorem. -/
lemma exists_cyclotomic_lift (p ell : ℕ) [hp : Fact p.Prime] [NeZero ell]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hcop : p.Coprime ell) (a : (ZMod p)ˣ) :
    ∃ s : CyclotomicField ell K ≃+* CyclotomicField ell K,
      s (IsCyclotomicExtension.zeta ell K (CyclotomicField ell K)) =
        IsCyclotomicExtension.zeta ell K (CyclotomicField ell K) ∧
      ∀ x : K, s (algebraMap K (CyclotomicField ell K) x) =
        algebraMap K (CyclotomicField ell K) (σ p K a x) := by
  let : NeZero p := ⟨hp.out.ne_zero⟩
  let E := CyclotomicField ell K
  let : NumberField E := IsCyclotomicExtension.numberField {ell} K E
  let : IsCyclotomicExtension {p * ell} ℚ E := cyclotomic_tower_mul p ell K hcop
  let b := Nat.chineseRemainder hcop (a : ZMod p).val 1
  have hbp : b.val.Coprime p := by
    rw [← ZMod.coprime_mod_iff_coprime, b.prop.1,
      ZMod.coprime_mod_iff_coprime]
    exact ZMod.val_coe_unit_coprime a
  have hbe : b.val.Coprime ell := by
    rw [← ZMod.coprime_mod_iff_coprime, b.prop.2,
      ZMod.coprime_mod_iff_coprime]
    exact Nat.coprime_one_left ell
  let u : (ZMod (p * ell))ˣ := ZMod.unitOfCoprime b.val (hbp.mul_right hbe)
  let s := (IsCyclotomicExtension.Rat.galEquivZMod (p * ell) E).symm u
  have hs (x : E) (hx : x ^ (p * ell) = 1) : s x = x ^ b.val := by
    have hs := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (p * ell) E s hx
    simp only [s, MulEquiv.apply_symm_apply, u, ZMod.coe_unitOfCoprime,
      ZMod.val_natCast] at hs
    exact hs.trans (pow_eq_pow_mod b.val hx).symm
  have hroot := IsCyclotomicExtension.zeta_spec ell K E
  refine ⟨s.toRingEquiv, ?_, ?_⟩
  · change s _ = _
    rw [hs _ (by rw [mul_comm, pow_mul, hroot.pow_eq_one, one_pow]),
      pow_eq_pow_mod b.val hroot.pow_eq_one, b.prop.2,
      ← pow_eq_pow_mod 1 hroot.pow_eq_one, pow_one]
  · have heq : s.toAlgHom.comp (IsScalarTower.toAlgHom ℚ K E) =
        (IsScalarTower.toAlgHom ℚ K E).comp (σ p K a).toAlgHom := by
      apply (ζ_spec p K).powerBasis ℚ |>.algHom_ext
      simp only [IsPrimitiveRoot.powerBasis_gen, AlgHom.comp_apply,
        AlgEquiv.coe_toAlgHom, IsScalarTower.toAlgHom_apply, σ_apply_ζ, map_pow]
      have hm : (algebraMap K E (ζ p K)) ^ p = 1 := by
        rw [← map_pow, (ζ_spec p K).pow_eq_one, map_one]
      rw [hs _ (by rw [pow_mul, hm, one_pow]),
        pow_eq_pow_mod b.val hm, b.prop.1, ← pow_eq_pow_mod _ hm]
    intro x
    exact DFunLike.congr_fun heq x


/-- The distinct-prime specialization of the CRT lift. -/
lemma exists_cyclotomic_lift_of_ne (p ell : ℕ) [hp : Fact p.Prime]
    [he : Fact ell.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (hne : p ≠ ell) (a : (ZMod p)ˣ) :
    ∃ s : CyclotomicField ell K ≃+* CyclotomicField ell K,
      s (IsCyclotomicExtension.zeta ell K (CyclotomicField ell K)) =
        IsCyclotomicExtension.zeta ell K (CyclotomicField ell K) ∧
      ∀ x : K, s (algebraMap K (CyclotomicField ell K) x) =
        algebraMap K (CyclotomicField ell K) (σ p K a x) := by
  let : NeZero ell := ⟨he.out.ne_zero⟩
  exact exists_cyclotomic_lift p ell K ((Nat.coprime_primes hp.out he.out).mpr hne) a

/-- The quotient of Gauss sums satisfies the cyclotomic automorphism identity
without a supplied extension automorphism. -/
theorem exists_cyclotomicTraceGaussSum_quotient_power
    (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K]
    (F : Type*) [Field F] [Fintype F] [Algebra (ZMod (ringChar F)) F]
    (hne : p ≠ ringChar F) (χ : MulChar F K) (hχ : χ ^ p = 1)
    (a : (ZMod p)ˣ) (Γ : K)
    (hΓ : cyclotomicTraceGaussSum χ ^ p =
      algebraMap K (CyclotomicField (ringChar F) K) Γ) :
    ∃ δ : Kˣ, (δ : K) ^ p = Γ ^ (a : ZMod p).val / σ p K a Γ := by
  let E := CyclotomicField (ringChar F) K
  let : NeZero p := ⟨hp.out.ne_zero⟩
  let : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  let : IsGalois K E := IsCyclotomicExtension.isGalois {ringChar F} K E
  let : FiniteDimensional K E := IsCyclotomicExtension.finite_of_singleton (ringChar F) K E
  obtain ⟨s, hsζ, hslift⟩ := exists_cyclotomic_lift_of_ne p (ringChar F) K hne a
  obtain ⟨δ, _, hδ⟩ := exists_traceGaussSum_quotient_power χ hχ (ζ_spec p K)
    (IsCyclotomicExtension.zeta_spec (ringChar F) K E) (σ p K a).toRingEquiv s
    (a : ZMod p).val (σ_apply_ζ p K a) hsζ hslift Γ hΓ
  exact ⟨δ, hδ⟩


end Catalan
