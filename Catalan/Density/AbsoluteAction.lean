import Catalan.Density.PerfectKummer
import Catalan.Density.AbsoluteB
import Catalan.Density.AbsoluteM
import Catalan.Density.FUnits
import Catalan.Density.ConjugateOver

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
variable (p q : ℕ)

/-- Restriction of an actual absolute automorphism to the literal real field F. -/
def restrictToF (hp : 0 < p) (σ : Msub p q ≃ₐ[ℚ] Msub p q) : F p ≃ₐ[ℚ] F p := by
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp
  exact σ.restrictNormal (F p)

lemma restrictToF_commutes (hp : 0 < p) (σ : Msub p q ≃ₐ[ℚ] Msub p q) (a : F p) :
    algebraMap (F p) (Msub p q) (restrictToF p q hp σ a) =
      σ (algebraMap (F p) (Msub p q) a) := by
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp
  exact AlgEquiv.restrictNormal_commutes σ (F p) a

lemma restrictToF_inv (hp : 0 < p) (σ : Msub p q ≃ₐ[ℚ] Msub p q) :
    restrictToF p q hp σ⁻¹ = (restrictToF p q hp σ)⁻¹ := by
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp
  exact map_inv (AlgEquiv.restrictNormalHom (F p)) σ

lemma restrictToF_unitAction (hp : 0 < p) (σ : Msub p q ≃ₐ[ℚ] Msub p q)
    (u : (𝓞 (F p))ˣ) :
    σ (algebraMap (F p) (Msub p q) ((u : 𝓞 (F p)) : F p)) =
      algebraMap (F p) (Msub p q)
        (((Circular.unitAction p (F p) (restrictToF p q hp σ) u : (𝓞 (F p))ˣ) : 𝓞 (F p)) : F p) := by
  rw [Circular.unitAction_coe, restrictToF_commutes]

variable [Fact q.Prime]

/-- Actual conjugation of the relative Kummer Galois group. -/
def conjugateKummer (hp : 0 < p) (σ : Msub p q ≃ₐ[ℚ] Msub p q)
    (τ : Msub p q ≃ₐ[Bsub p q] Msub p q) : Msub p q ≃ₐ[Bsub p q] Msub p q := by
  have instGaloisB : IsGalois ℚ (Bsub p q) := isGalois_Bsub_rat p q hp (Fact.out : q.Prime).pos
  exact Kummer.conjugateOver ℚ (Bsub p q) (Msub p q) σ τ

lemma conjugateKummer_apply (hp : 0 < p) (σ : Msub p q ≃ₐ[ℚ] Msub p q)
    (τ : Msub p q ≃ₐ[Bsub p q] Msub p q) (x : Msub p q) :
    conjugateKummer p q hp σ τ x = σ (τ (σ⁻¹ x)) := rfl

lemma conjugateKummer_eq_self_of_commute (hp : 0 < p)
    (σ : Msub p q ≃ₐ[ℚ] Msub p q) (τ : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (h : σ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ) :
    conjugateKummer p q hp σ τ = τ := by
  have instGaloisB : IsGalois ℚ (Bsub p q) := isGalois_Bsub_rat p q hp (Fact.out : q.Prime).pos
  exact Kummer.conjugateOver_eq_self_of_commute ℚ (Bsub p q) (Msub p q) σ τ h

end Catalan.A3
