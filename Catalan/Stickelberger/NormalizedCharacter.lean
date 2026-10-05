module

public import Catalan.Stickelberger.ResidueGauss

/-!
# `Catalan.Stickelberger.NormalizedCharacter`

Part of the Catalan formalization.
-/

@[expose] public section

noncomputable section
open NumberField
namespace Catalan

lemma restrictRootsOfUnity_bijective_of_primitive
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    {p : ℕ} [NeZero p] (f : R →+* S) {μ : R}
    (hμ : IsPrimitiveRoot μ p) (hfμ : IsPrimitiveRoot (f μ) p) :
    Function.Bijective (restrictRootsOfUnity f p) := by
  constructor
  · intro x y hxy
    obtain ⟨i, hi, hxi⟩ := hμ.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' p _).mp x.prop)
    obtain ⟨j, hj, hyj⟩ := hμ.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' p _).mp y.prop)
    have he : (f μ) ^ i = (f μ) ^ j := by
      have h := congrArg (fun z : rootsOfUnity p S => ((z : Sˣ) : S)) hxy
      change f (x : Rˣ) = f (y : Rˣ) at h
      simpa only [← map_pow, hxi, hyj] using h
    apply rootsOfUnity.coe_injective
    change (x : Rˣ).val = (y : Rˣ).val
    rw [← hxi, ← hyj, hfμ.pow_inj hi hj he]
  · intro y
    obtain ⟨i, _, hi⟩ := hfμ.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' p _).mp y.prop)
    refine ⟨rootsOfUnity.mkOfPowEq (μ ^ i) (by rw [pow_right_comm, hμ.pow_eq_one, one_pow]), ?_⟩
    apply rootsOfUnity.coe_injective
    change f (μ ^ i) = _
    rwa [map_pow]

/-- Reduction is an isomorphism on the p-th roots of unity at primes away from p. -/
def residueRootsEquiv (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (I : Ideal (NumberField.RingOfIntegers K)) [I.IsPrime]
    (haway : (p : NumberField.RingOfIntegers K) ∉ I) :
    rootsOfUnity p (NumberField.RingOfIntegers K) ≃*
      rootsOfUnity p (NumberField.RingOfIntegers K ⧸ I) := by
  let : NeZero p := ⟨hp.out.ne_zero⟩
  exact MulEquiv.ofBijective (restrictRootsOfUnity (Ideal.Quotient.mk I) p)
    (restrictRootsOfUnity_bijective_of_primitive (Ideal.Quotient.mk I)
      (ζ_spec p K).toInteger_isPrimitiveRoot (residueZeta_isPrimitiveRoot p K I haway))

/-- The power-residue homomorphism on the multiplicative group of a finite field. -/
def residuePowerHom (F : Type*) [Field F] [Fintype F] (p : ℕ)
    (hdiv : p ∣ Fintype.card F - 1) : Fˣ →* rootsOfUnity p F where
  toFun x := ⟨x ^ ((Fintype.card F - 1) / p), by
    classical
    rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel hdiv,
      ← Fintype.card_units]
    exact pow_card_eq_one⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_pow]


/-- A normalized p-th power-residue character, with the orientation fixed by f. -/
theorem exists_normalized_powerResidueChar
    (F : Type*) [Field F] [Fintype F]
    (R : Type*) [CommRing R] [IsDomain R]
    (p : ℕ) [hp : Fact p.Prime] (hdiv : p ∣ Fintype.card F - 1)
    (f : R →+* F) {μ : R} (hμ : IsPrimitiveRoot μ p)
    (hfμ : IsPrimitiveRoot (f μ) p) :
    ∃ χ : MulChar F R, orderOf χ = p ∧
      ∀ x : Fˣ, f (χ x) = (x : F) ^ ((Fintype.card F - 1) / p) := by
  classical
  let : NeZero p := ⟨hp.out.ne_zero⟩
  let e : rootsOfUnity p R ≃* rootsOfUnity p F :=
    MulEquiv.ofBijective (restrictRootsOfUnity f p)
      (restrictRootsOfUnity_bijective_of_primitive f hμ hfμ)
  let h : Fˣ →* Rˣ := (rootsOfUnity p R).subtype.comp
    (e.symm.toMonoidHom.comp (residuePowerHom F p hdiv))
  let χ := MulChar.ofUnitHom h
  have hnorm (x : Fˣ) : f (χ x) = (x : F) ^ ((Fintype.card F - 1) / p) := by
    have hh := e.apply_symm_apply (residuePowerHom F p hdiv x)
    have hh' := congrArg (fun z : rootsOfUnity p F => ((z : Fˣ) : F)) hh
    change f ((e.symm (residuePowerHom F p hdiv x) : Rˣ) : R) = _ at hh'
    change f (MulChar.ofUnitHom h (x : F)) = _
    rw [MulChar.ofUnitHom_coe]
    exact hh'
  have hpow : χ ^ p = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    change (MulChar.ofUnitHom h (u : F)) ^ p = 1
    rw [MulChar.ofUnitHom_coe]
    exact (mem_rootsOfUnity' p _).mp (e.symm (residuePowerHom F p hdiv u)).prop
  have hne : χ ≠ 1 := by
    intro hc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
    have hg' : orderOf g = Fintype.card F - 1 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using hg
    have heq : g ^ ((Fintype.card F - 1) / p) = 1 := by
      apply Units.ext
      have hh := hnorm g
      simpa only [hc, MulChar.one_apply_coe, map_one, Units.val_pow_eq_pow_val,
        Units.val_one] using hh.symm
    have hle := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd
      (by have := Fintype.one_lt_card (α := F); omega) hdiv) hp.out.pos)
      (orderOf_dvd_of_pow_eq_one heq)
    rw [hg'] at hle
    exact (not_le_of_gt (Nat.div_lt_self
      (by have := Fintype.one_lt_card (α := F); omega) hp.out.one_lt)) hle
  exact ⟨χ, orderOf_eq_prime hpow hne, hnorm⟩


/-- The character has integral values and reduces to the specified power-residue
map. This fixes the orientation that an arbitrary exact-order character leaves open. -/
theorem exists_normalized_primeResidueChar
    (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (I : Ideal (𝓞 K)) [I.IsMaximal]
    (haway : (p : 𝓞 K) ∉ I) :
    ∃ χ : MulChar (𝓞 K ⧸ I) K, orderOf χ = p ∧
      ∀ x : 𝓞 K ⧸ I, ∃ z : 𝓞 K, (z : K) = χ x ∧
        Ideal.Quotient.mk I z = x ^ ((Nat.card (𝓞 K ⧸ I) - 1) / p) := by
  let : Field (𝓞 K ⧸ I) := Ideal.Quotient.field I
  let : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  have hI0 : I ≠ ⊥ := (I.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
  have hdiv : p ∣ Fintype.card (𝓞 K ⧸ I) - 1 := by
    simpa only [Fintype.card_eq_nat_card] using
      prime_dvd_residue_card_sub_one p K I inferInstance hI0 haway
  obtain ⟨χ₀, hχ₀, hnorm⟩ := exists_normalized_powerResidueChar
    (𝓞 K ⧸ I) (𝓞 K) p hdiv (Ideal.Quotient.mk I)
    (ζ_spec p K).toInteger_isPrimitiveRoot (residueZeta_isPrimitiveRoot p K I haway)
  let χ := χ₀.ringHomComp (algebraMap (𝓞 K) K)
  refine ⟨χ, ?_, ?_⟩
  · exact (orderOf_injective (MulChar.ringHomCompHom (algebraMap (𝓞 K) K))
      (MulChar.injective_ringHomComp RingOfIntegers.coe_injective) χ₀).trans hχ₀
  · intro x
    refine ⟨χ₀ x, rfl, ?_⟩
    by_cases hx : x = 0
    · have hd : 0 < (Nat.card (𝓞 K ⧸ I) - 1) / p := by
        rw [Nat.card_eq_fintype_card]
        exact Nat.div_pos (Nat.le_of_dvd
          (by have := Fintype.one_lt_card (α := 𝓞 K ⧸ I); omega) hdiv) hp.out.pos
      simp only [hx, MulChar.map_zero, map_zero, zero_pow hd.ne']
    · simpa only [Fintype.card_eq_nat_card, Units.val_mk0] using hnorm (Units.mk0 x hx)


/-- The inverse normalization used in the local Gauss-sum valuation formula. -/
theorem exists_inverse_normalized_primeResidueChar
    (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (I : Ideal (𝓞 K)) [I.IsMaximal]
    (haway : (p : 𝓞 K) ∉ I) :
    ∃ χ : MulChar (𝓞 K ⧸ I) K, orderOf χ = p ∧
      ∀ x : (𝓞 K ⧸ I)ˣ, ∃ z : 𝓞 K, (z : K) = χ x ∧
        Ideal.Quotient.mk I z =
          (((x ^ ((Nat.card (𝓞 K ⧸ I) - 1) / p))⁻¹ : (𝓞 K ⧸ I)ˣ) : 𝓞 K ⧸ I) := by
  let : Field (𝓞 K ⧸ I) := Ideal.Quotient.field I
  obtain ⟨χ, hχ, hnorm⟩ := exists_normalized_primeResidueChar p K I haway
  refine ⟨χ⁻¹, (orderOf_inv χ).trans hχ, ?_⟩
  intro x
  obtain ⟨z, hz, hred⟩ := hnorm (x⁻¹ : (𝓞 K ⧸ I)ˣ)
  refine ⟨z, ?_, ?_⟩
  · rw [MulChar.inv_apply']
    simpa only [Units.val_inv_eq_inv_val] using hz
  · simpa only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow] using hred


end Catalan
