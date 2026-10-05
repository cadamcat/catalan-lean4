module

public import Catalan.Cyclotomic.Basic

/-! Fractional-ideal action and group-ring exponentiation.
This module proves the algebraic bridge; Stickelberger's annihilation theorem
is proved separately in `Stickelberger/Annihilation.lean` and is not assumed here. -/

/-!
# `Catalan.IdealAction`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Pointwise
open NumberField

noncomputable section
namespace Catalan

section IdealAction
variable (K : Type*) [Field K] [NumberField K]

/-- Fractional `𝓞 K`-ideals, including zero. -/
abbrev FracIdeal := FractionalIdeal (𝓞 K)⁰ K
/-- Invertible (equivalently, nonzero) fractional `𝓞 K`-ideals. -/
abbrev FracIdealUnit := (FracIdeal K)ˣ

/-- Restriction of a field automorphism to its ring of integers. -/
noncomputable def integerAut (τ : K ≃ₐ[ℚ] K) : 𝓞 K ≃+* 𝓞 K :=
  NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv

lemma integerAut_preserves_nonZeroDivisors (τ : K ≃ₐ[ℚ] K) :
    (𝓞 K)⁰ ≤ Submonoid.comap (integerAut K τ).toRingHom (𝓞 K)⁰ := by
  exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
    (integerAut K τ).toRingHom (integerAut K τ).injective

/-- Semilinear transport of fractional ideals along `τ`.
`FractionalIdeal.map` is NOT usable directly: tau is not O_K-linear.
`extendedHom'` changes the base ring along `integerAut tau` as required. -/
noncomputable def fractionalAut (τ : K ≃ₐ[ℚ] K) :
    FracIdeal K →+* FracIdeal K :=
  FractionalIdeal.extendedHom'
    (A := 𝓞 K) (B := 𝓞 K) (K := K)
    (M := (𝓞 K)⁰) (N := (𝓞 K)⁰)
    (f := (integerAut K τ).toRingHom) K
    (integerAut_preserves_nonZeroDivisors K τ)

/-- `τ` acts on the group of nonzero fractional ideals. -/
noncomputable def idealAct (τ : K ≃ₐ[ℚ] K) :
    FracIdealUnit K →* FracIdealUnit K :=
  Units.map (fractionalAut K τ).toMonoidHom

/-- `τ` acts on nonzero field elements. -/
noncomputable def elementAct (τ : K ≃ₐ[ℚ] K) : Kˣ →* Kˣ :=
  Units.map τ.toRingEquiv.toRingHom.toMonoidHom

/-- The principal-ideal homomorphism `γ ↦ (γ)`. -/
noncomputable abbrev principalIdeal : Kˣ →* FracIdealUnit K :=
  toPrincipalIdeal (𝓞 K) K

/-- Embed a nonzero integral ideal in the group of fractional ideals. -/
noncomputable def idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    FracIdealUnit K :=
  FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr
    (by simpa only [Ideal.zero_eq_bot] using hI)⟩

lemma coe_idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (idealUnit K I hI : FracIdeal K) = (I : FracIdeal K) := by
  rfl

lemma localization_map_integerAut (τ : K ≃ₐ[ℚ] K) :
    IsLocalization.map (S := K) K (integerAut K τ).toRingHom
      (integerAut_preserves_nonZeroDivisors K τ) = τ.toRingEquiv.toRingHom := by
  apply IsFractionRing.ringHom_ext (A := 𝓞 K)
  intro x
  rw [IsLocalization.map_eq]
  rfl

lemma ideal_pointwise_smul_eq_map (τ : K ≃ₐ[ℚ] K) (I : Ideal (𝓞 K)) :
    τ • I = Ideal.map (integerAut K τ).toRingHom I := by
  rw [Ideal.pointwise_smul_def]
  congr 1

lemma idealAct_idealUnit (τ : K ≃ₐ[ℚ] K)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (idealAct K τ (idealUnit K I hI) : FracIdeal K) =
      ((Ideal.map (integerAut K τ).toRingHom I : Ideal (𝓞 K)) : FracIdeal K) := by
  change fractionalAut K τ (I : FracIdeal K) = _
  exact FractionalIdeal.extended_coeIdeal_eq_map K
    (integerAut_preserves_nonZeroDivisors K τ) I

lemma idealAct_principalIdeal (τ : K ≃ₐ[ℚ] K) (γ : Kˣ) :
    idealAct K τ (principalIdeal K γ) =
      principalIdeal K (elementAct K τ γ) := by
  apply Units.ext
  change fractionalAut K τ (↑(toPrincipalIdeal (𝓞 K) K γ)) =
    ↑(toPrincipalIdeal (𝓞 K) K (elementAct K τ γ))
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal]
  change (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ : K)).extended K
    (integerAut_preserves_nonZeroDivisors K τ) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (τ (γ : K))
  rw [FractionalIdeal.extended_spanSingleton, localization_map_integerAut]
  rfl

end IdealAction

section ExponentAction
variable (p : ℕ)
variable (K : Type*) [Field K] [NumberField K]

/-- Group-ring exponentiation of an ideal: J^Theta = product_tau (tau J)^(Theta tau).
The product is over finite support and all exponents are integers.
In v4.33.1 MonoidAlgebra is a structure, so Finsupp.prod receives Theta.coeff. -/
noncomputable def ipow (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Θ : R p K) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Finsupp.prod Θ.coeff (fun τ m => (idealAct K τ J) ^ m)

lemma ipow_zero (J : FracIdealUnit K) : ipow p K J 0 = 1 := by
  exact Finsupp.prod_zero_index

lemma ipow_add (J : FracIdealUnit K) (Θ Ψ : R p K) :
    ipow p K J (Θ + Ψ) = ipow p K J Θ * ipow p K J Ψ := by
  exact Finsupp.prod_add_index'
    (fun τ => zpow_zero (idealAct K τ J))
    (fun τ m n => zpow_add (idealAct K τ J) m n)

lemma ipow_single (J : FracIdealUnit K) (τ : G p K) (m : ℤ) :
    ipow p K J (MonoidAlgebra.single τ m) = (idealAct K τ J) ^ m := by
  exact Finsupp.prod_single_index (zpow_zero (idealAct K τ J))

lemma ipow_one (Θ : R p K) : ipow p K 1 Θ = 1 := by
  simp only [ipow, map_one, one_zpow, Finsupp.prod_fun_one]

lemma ipow_mul (I J : FracIdealUnit K) (Θ : R p K) :
    ipow p K (I * J) Θ = ipow p K I Θ * ipow p K J Θ := by
  simp only [ipow, Finsupp.prod, map_mul, mul_zpow, Finset.prod_mul_distrib]

/-- For a fixed exponent, ideal exponentiation is a group homomorphism. -/
noncomputable def ipowHom (Θ : R p K) : FracIdealUnit K →* FracIdealUnit K where
  toFun J := ipow p K J Θ
  map_one' := ipow_one p K Θ
  map_mul' I J := ipow_mul p K I J Θ

/-- For a fixed ideal, exponentiation is additive in the group-ring exponent. -/
noncomputable def ipowAddHom (J : FracIdealUnit K) : R p K →+ Additive (FracIdealUnit K) where
  toFun Θ := Additive.ofMul (ipow p K J Θ)
  map_zero' := congrArg Additive.ofMul (ipow_zero p K J)
  map_add' Θ Ψ := congrArg Additive.ofMul (ipow_add p K J Θ Ψ)

lemma ipow_inv (J : FracIdealUnit K) (Θ : R p K) :
    ipow p K J⁻¹ Θ = (ipow p K J Θ)⁻¹ := by
  exact map_inv (ipowHom p K Θ) J

lemma ipow_zpow (J : FracIdealUnit K) (Θ : R p K) (n : ℤ) :
    ipow p K (J ^ n) Θ = (ipow p K J Θ) ^ n := by
  exact map_zpow (ipowHom p K Θ) J n

lemma ipow_zsmul (J : FracIdealUnit K) (Θ : R p K) (n : ℤ) :
    ipow p K J (n • Θ) = (ipow p K J Θ) ^ n := by
  exact congrArg Additive.toMul (map_zsmul (ipowAddHom p K J) n Θ)

lemma ipow_sum {ι : Type*} (s : Finset ι)
    (J : FracIdealUnit K) (E : ι → R p K) :
    ipow p K J (∑ i ∈ s, E i) = ∏ i ∈ s, ipow p K J (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, ipow_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, ipow_add, ih]

lemma ipow_principalIdeal (γ : Kˣ) (Θ : R p K) :
    ipow p K (principalIdeal K γ) Θ =
      principalIdeal K (Θ.coeff.prod (fun τ m => (elementAct K τ γ) ^ m)) := by
  unfold ipow
  rw [map_finsuppProd]
  apply Finsupp.prod_congr
  intro τ hτ
  rw [idealAct_principalIdeal, map_zpow]

/-- The exponents taking a fixed ideal into the principal subgroup form a `ℤ`-submodule. -/
noncomputable def principalExponentSubmodule (J : FracIdealUnit K) :
    Submodule ℤ (R p K) where
  carrier := {Θ | ∃ γ : Kˣ, ipow p K J Θ = principalIdeal K γ}
  zero_mem' := ⟨1, by rw [ipow_zero, map_one]⟩
  add_mem' := by
    rintro Θ Ψ ⟨γ, hγ⟩ ⟨δ, hδ⟩
    exact ⟨γ * δ, by rw [ipow_add, hγ, hδ, map_mul]⟩
  smul_mem' := by
    rintro n Θ ⟨γ, hγ⟩
    exact ⟨γ ^ n, by rw [ipow_zsmul, hγ, map_zpow]⟩

lemma coe_ipow_nat_sum {ι : Type*} [Fintype ι]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (τ : ι → G p K) (n : ι → ℕ) :
    (ipow p K (idealUnit K I hI)
      (∑ i, MonoidAlgebra.single (τ i) (n i : ℤ)) : FracIdeal K) =
      ((∏ i, (Ideal.map (integerAut K (τ i)).toRingHom I) ^ n i :
        Ideal (𝓞 K)) : FracIdeal K) := by
  classical
  rw [ipow_sum]
  simp only [ipow_single, zpow_natCast]
  change (Units.coeHom (FracIdeal K))
    (∏ i, idealAct K (τ i) (idealUnit K I hI) ^ n i) =
      (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K)
        (∏ i, (Ideal.map (integerAut K (τ i)).toRingHom I) ^ n i)
  simp only [map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun A : FracIdeal K => A ^ n i)
    (idealAct_idealUnit K (τ i) I hI)

lemma principal_of_integral_factorization {ι : Type*} [Fintype ι]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (τ : ι → G p K) (n : ι → ℕ)
    (Γ : 𝓞 K) (hΓ : (Γ : K) ≠ 0)
    (hfactor : Ideal.span {Γ} =
      ∏ i, (Ideal.map (integerAut K (τ i)).toRingHom I) ^ n i) :
    ipow p K (idealUnit K I hI)
      (∑ i, MonoidAlgebra.single (τ i) (n i : ℤ)) =
      principalIdeal K (Units.mk0 (Γ : K) hΓ) := by
  apply Units.ext
  rw [coe_ipow_nat_sum, ← hfactor, coe_toPrincipalIdeal,
    FractionalIdeal.coeIdeal_span_singleton]
  rfl

end ExponentAction

end Catalan

#print axioms Catalan.ipow_add
#print axioms Catalan.ipow_mul
#print axioms Catalan.ipow_zsmul
#print axioms Catalan.ipow_principalIdeal
#print axioms Catalan.principal_of_integral_factorization
