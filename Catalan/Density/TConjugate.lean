module

public import Catalan.Density.GaloisModules
public import Catalan.Density.SelectorConjugate
public import Catalan.Density.AbsoluteT

/-!
# `Catalan.Density.TConjugate`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]

def restrictAbsoluteTToM (hp : 0 < p) : (T p q ≃ₐ[ℚ] T p q) →* (Msub p q ≃ₐ[ℚ] Msub p q) := by
  have instGaloisM : IsGalois ℚ (Msub p q) := isGalois_Msub_rat p q hp (Fact.out : q.Prime).pos
  exact AlgEquiv.restrictNormalHom (Msub p q)

lemma restrictAbsoluteTToM_commutes (hp : 0 < p)
    (rho : T p q ≃ₐ[ℚ] T p q) (x : Msub p q) :
    algebraMap (Msub p q) (T p q) (restrictAbsoluteTToM p q hp rho x) =
      rho (algebraMap (Msub p q) (T p q) x) := by
  have instGaloisM : IsGalois ℚ (Msub p q) := isGalois_Msub_rat p q hp (Fact.out : q.Prime).pos
  exact rho.restrictNormal_commutes (Msub p q) x

lemma restrictAbsoluteTToM_surjective (hp : 0 < p) :
    Function.Surjective (restrictAbsoluteTToM p q hp) := by
  have instGaloisM : IsGalois ℚ (Msub p q) := isGalois_Msub_rat p q hp (Fact.out : q.Prime).pos
  have instGaloisT : IsGalois ℚ (T p q) := isGalois_T_rat p q hp (Fact.out : q.Prime).pos
  exact AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := Msub p q) (E := T p q)

def conjugateT (hp : 0 < p) (rho : T p q ≃ₐ[ℚ] T p q)
    (sigma : T p q ≃ₐ[Bsub p q] T p q) : T p q ≃ₐ[Bsub p q] T p q := by
  have instGaloisB : IsGalois ℚ (Bsub p q) := isGalois_Bsub_rat p q hp (Fact.out : q.Prime).pos
  exact Kummer.conjugateOver ℚ (Bsub p q) (T p q) rho sigma

lemma conjugateT_apply (hp : 0 < p) (rho : T p q ≃ₐ[ℚ] T p q)
    (sigma : T p q ≃ₐ[Bsub p q] T p q) (x : T p q) :
    conjugateT p q hp rho sigma x = rho (sigma (rho⁻¹ x)) := rfl

lemma conjugateT_restrictScalars (hp : 0 < p) (rho : T p q ≃ₐ[ℚ] T p q)
    (sigma : T p q ≃ₐ[Bsub p q] T p q) :
    (conjugateT p q hp rho sigma).restrictScalars ℚ =
      rho * sigma.restrictScalars ℚ * rho⁻¹ := by
  ext x
  rfl

lemma restrictTToM_conjugate (hp : 0 < p) (rho : T p q ≃ₐ[ℚ] T p q)
    (sigma : T p q ≃ₐ[Bsub p q] T p q) :
    restrictTToM p q (conjugateT p q hp rho sigma) =
      conjugateKummer p q hp (restrictAbsoluteTToM p q hp rho) (restrictTToM p q sigma) := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap (Msub p q) (T p q)).injective
  have hinv : algebraMap (Msub p q) (T p q) ((restrictAbsoluteTToM p q hp rho)⁻¹ x) =
      rho⁻¹ (algebraMap (Msub p q) (T p q) x) := by
    rw [← map_inv]
    exact restrictAbsoluteTToM_commutes p q hp rho⁻¹ x
  rw [restrictTToM_commutes, conjugateT_apply, conjugateKummer_apply,
    restrictAbsoluteTToM_commutes, restrictTToM_commutes, hinv]

lemma selector_conjugateT (hp : 0 < p) (rho : T p q ≃ₐ[ℚ] T p q)
    (sigma : T p q ≃ₐ[Bsub p q] T p q)
    (hsigma : Selector p q (sigma.restrictScalars ℚ)) :
    Selector p q ((conjugateT p q hp rho sigma).restrictScalars ℚ) := by
  rw [conjugateT_restrictScalars]
  exact selector_conjugate p q hp (Fact.out : q.Prime).pos _ rho hsigma

lemma conjugateT_inv_cancel (hp : 0 < p) (rho : T p q ≃ₐ[ℚ] T p q)
    (sigma : T p q ≃ₐ[Bsub p q] T p q) :
    conjugateT p q hp rho (conjugateT p q hp rho⁻¹ sigma) = sigma := by
  apply AlgEquiv.ext
  intro x
  simp [conjugateT_apply]

lemma conjugateKummer_inv_cancel (hp : 0 < p) (rho : Msub p q ≃ₐ[ℚ] Msub p q)
    (tau : Msub p q ≃ₐ[Bsub p q] Msub p q) :
    conjugateKummer p q hp rho⁻¹ (conjugateKummer p q hp rho tau) = tau := by
  apply AlgEquiv.ext
  intro x
  simp [conjugateKummer_apply]

end Catalan.A3
