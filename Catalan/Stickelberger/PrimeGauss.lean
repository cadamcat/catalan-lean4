module

public import Catalan.Stickelberger.CharacterBridge
public import Catalan.Stickelberger.Values
public import Catalan.Stickelberger.Hout
public import Catalan.Stickelberger.Fiber
public import Catalan.Stickelberger.ConjugateValuation
public import Catalan.Stickelberger.IntegralQuotient

/-!
# `Catalan.Stickelberger.PrimeGauss`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Stickelberger
open NumberField

/-- Adjoining roots of an order divisible by the base conductor gives that conductor over Q. -/
theorem isCyclotomicExtension_base_tower_of_dvd
    (p N : ℕ) [NeZero p] (hN : N ≠ 0) (hdvd : p ∣ N)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    IsCyclotomicExtension {N} ℚ (CyclotomicField N K) := by
  let L := CyclotomicField N K
  have h := IsCyclotomicExtension.trans {p} {N} ℚ K L (algebraMap K L).injective
  have hu : IsCyclotomicExtension (({N} : Set ℕ) ∪ {p}) ℚ L := by
    rwa [Set.union_comm]
  exact (IsCyclotomicExtension.iff_union_of_dvd (S := ({N} : Set ℕ)) (n := p) ℚ L ⟨N, rfl, hN, hdvd⟩).mpr hu

theorem exists_prime_gauss_witnesses (p ell : ℕ) [hp : Fact p.Prime] [hl : Fact ell.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (q : Ideal (𝓞 K)) [q.IsMaximal] [q.LiesOver (Ideal.span {(ell : ℤ)})]
    (hell : 2 < ell) (hne : ell ≠ p) (hq0 : q ≠ ⊥) :
    ∃ Γ : Kˣ, ipow p K (idealUnit K q hq0) (pθ p K) = principalIdeal K Γ ∧
      ∀ a : (ZMod p)ˣ, ∃ δ : Kˣ,
        δ ^ p = Γ ^ (a : ZMod p).val / elementAct K (σ p K a) Γ := by
  classical
  have instLocal1 : NeZero p := ⟨hp.out.ne_zero⟩
  have instLocal2 : NeZero ell := ⟨hl.out.ne_zero⟩
  have hcop : ell.Coprime p := (Nat.coprime_primes hl.out hp.out).mpr hne
  let f := orderOf (ell : ZMod p)
  have hf : 0 < f := by
    have hu : orderOf (ZMod.unitOfCoprime ell hcop) = f := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime]
    rw [← hu]
    exact orderOf_pos _
  let m := ell ^ f - 1
  let N := ell * m
  have hm0 : m ≠ 0 := by
    have := Nat.one_lt_pow hf.ne' (by omega : 1 < ell)
    dsimp [m]; omega
  have instLocal3 : NeZero m := ⟨hm0⟩
  have hpm : p ∣ m := by
    have he : (ell : ZMod p) ^ f = 1 := pow_orderOf_eq_one _
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at he
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hl.out.pos)).mp he.symm
  have hN0 : N ≠ 0 := Nat.mul_ne_zero hl.out.ne_zero hm0
  let L := CyclotomicField N K
  have instLocal4 : IsCyclotomicExtension {N} ℚ L :=
    isCyclotomicExtension_base_tower_of_dvd p N hN0 (dvd_mul_of_dvd_right hpm ell) K
  have instLocal5 : IsGalois K L := IsCyclotomicExtension.isGalois {N} K L
  obtain ⟨P, hPmax, hPq⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) q
  have instLocal6 : P.IsMaximal := hPmax
  have instLocal7 : P.LiesOver q := hPq
  have instLocal8 : P.LiesOver (Ideal.span {(ell : ℤ)}) := Ideal.LiesOver.trans P q _
  have hmem := natCast_mem_of_liesOver ell L P
  let F := 𝓞 L ⧸ P
  let instLocal9 : Field F := Ideal.Quotient.field P
  let instLocal10 : Fintype F := Fintype.ofFinite F
  have instLocal11 : CharP F ell := charP_quotient_of_mem P ell hl.out (Ideal.IsMaximal.ne_top hPmax) hmem
  let instLocal12 : Algebra (ZMod ell) F := ZMod.algebra _ _
  have hcard : Fintype.card F = ell ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact card_residue_of_cyclotomic ell f m N L P hell hf rfl rfl
  obtain ⟨z, hz, τ, hred, hval⟩ :=
    exists_cyclotomic_gaussFamily_emultiplicity_eq_digitSum ell f m N L P hell hf rfl rfl
  have hdiv : p ∣ Fintype.card F - 1 := by rw [hcard]; exact hpm
  have hμ : IsPrimitiveRoot
      (Ideal.Quotient.mk P (algebraMap (𝓞 K) (𝓞 L) (Catalan.ζ_spec p K).toInteger)) p := by
    apply isPrimitiveRoot_quotient_of_not_dvd P p ell hl.out hmem
    · exact (Nat.Prime.coprime_iff_not_dvd hl.out).mp hcop
    · exact (Catalan.ζ_spec p K).toInteger_isPrimitiveRoot.map_of_injective
        (RingOfIntegers.algebraMap.injective K L)
  obtain ⟨χ, hχord, hχτ⟩ := exists_baseChar_eq_invTeichmuller_pow p K L
    (Ideal.Quotient.mk P) hdiv hμ τ hred
  have hχp : χ ^ p = 1 := hχord ▸ pow_orderOf_eq_one χ
  let χL := χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L))
  have hχLp : ∀ x : F, x ≠ 0 → (χL x) ^ p = 1 := by
    intro x hx
    have hu := DFunLike.congr_fun hχp x
    rw [χ.pow_apply' hp.out.ne_zero, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)] at hu
    change (algebraMap (𝓞 K) (𝓞 L) (χ x)) ^ p = 1
    rw [← map_pow, hu, map_one]
  obtain ⟨γ, hγ⟩ := exists_ringOfIntegers_gaussSum_pow p ell K L χL hz hl.out.one_lt hχLp
    (fun x => ⟨χ x, rfl⟩)
  have hχLne : χL ≠ 1 := by
    intro he
    have hc : χ = 1 := MulChar.injective_ringHomComp
      (RingOfIntegers.algebraMap.injective K L) (by simpa [χL] using he)
    rw [hc, orderOf_one] at hχord
    exact hp.out.ne_one hχord.symm
  obtain ⟨γ', hprod⟩ := exists_descended_gaussSum_mul_eq p ell f K L
    (Catalan.ζ_spec p K) χL hχLne hz hcard hχLp γ hγ
  have hγ0 : γ ≠ 0 := by
    intro h
    have he := hprod
    rw [h, zero_mul] at he
    exact pow_ne_zero (f * p) (Nat.cast_ne_zero.mpr hl.out.ne_zero) he.symm
  have hχτ' : χ.ringHomComp (algebraMap (𝓞 K) (𝓞 L)) = τ ^ (m / p) := by
    have hc : Fintype.card (𝓞 L ⧸ P) = ell ^ f := hcard
    simpa only [hc] using hχτ
  have hat (b : (ZMod p)ˣ) :
      emultiplicity (conjIdeal p K q b) (Ideal.span {γ}) =
        ((∑ i ∈ Finset.range f, ((b : ZMod p).val * ell ^ i) % p : ℕ) : ℕ∞) :=
    emultiplicity_conjIdeal_eq_orbit_sum_of_gaussFamily p ell f m N K L q P
      hell hne hf rfl rfl hpm χ hχp τ hχτ' hz hval γ hγ0 hγ b
  have instLocal13 : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  have hall : ∀ Q : Ideal (𝓞 K), Q.IsPrime → Q ≠ ⊥ →
      emultiplicity Q (Ideal.span {γ}) =
        ∑ a ∈ Finset.univ.filter (fun a : (ZMod p)ˣ => conjIdeal p K q a = Q),
          (((a : ZMod p).val : ℕ) : ℕ∞) := by
    intro Q hQ hQ0
    have : Q.IsMaximal := hQ.isMaximal hQ0
    by_cases hc : ∃ b : (ZMod p)ˣ, conjIdeal p K q b = Q
    · obtain ⟨b, rfl⟩ := hc
      rw [hat b, ← Nat.cast_sum]
      exact congrArg (fun n : ℕ => (n : ℕ∞))
        (conjIdeal_fiber_sum_eq_orbit_sum p ell K q hcop b).symm
    · have hneconj : ∀ t : K ≃ₐ[ℚ] K, Ideal.map (integerAut K t).toRingHom q ≠ Q := by
        intro t ht
        obtain ⟨a, ha⟩ := (σ_bijective p K).surjective t⁻¹
        apply hc
        refine ⟨a, ?_⟩
        simp only [conjIdeal, ha, inv_inv]
        exact ht
      have hzQ := emultiplicity_eq_zero_of_not_conj K ell (f * p) hl.out q
        (natCast_mem_of_liesOver ell K q) (u := 1) isUnit_one
        (by simpa only [one_mul] using hprod) Q hneconj
      rw [hzQ]
      have hempty : Finset.univ.filter (fun a : (ZMod p)ˣ => conjIdeal p K q a = Q) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro a _ ha
        exact hc ⟨a, ha⟩
      rw [hempty, Finset.sum_empty]
  let Γ : Kˣ := Units.mk0 (γ : K) (by exact_mod_cast hγ0)
  refine ⟨Γ, ipow_pθ_eq_principalIdeal_of_emultiplicity_fiber p K q hq0 γ hγ0 Γ rfl hall, ?_⟩
  intro a
  have hcopm : ell.Coprime m := (Nat.Prime.coprime_iff_not_dvd hl.out).mpr
    (not_dvd_of_eq_pow_sub_one hell hf rfl)
  obtain ⟨δ, hδ⟩ := exists_integralGaussSum_quotient_power p ell m N K L
    rfl hcopm hpm χ hχp hz γ hγ a
  refine ⟨δ, ?_⟩
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]
  change (δ : K) ^ p = (γ : K) ^ (a : ZMod p).val / σ p K a (γ : K)
  exact hδ

end Catalan.Stickelberger
