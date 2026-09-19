import Catalan.Density.AbsoluteAction
import Catalan.Density.RootCharacter

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
open UnitQuotient
variable (p q : ℕ) [Fact q.Prime]

/-- The action of an absolute automorphism on the chosen q-th root coordinate. -/
def cyclotomicScalar (σ : Msub p q ≃ₐ[ℚ] Msub p q) : ZMod q :=
  Kummer.rootCoordinateScalar (Msub p q) q (kummerZetaUnitM p q)
    (kummerZetaUnitM_spec p q) σ.toRingEquiv

lemma cyclotomicScalar_isUnit (σ : Msub p q ≃ₐ[ℚ] Msub p q) :
    IsUnit (cyclotomicScalar p q σ) :=
  Kummer.isUnit_rootCoordinateScalar (Msub p q) q (kummerZetaUnitM p q)
    (kummerZetaUnitM_spec p q) σ.toRingEquiv

lemma cyclotomicScalar_ne_zero (σ : Msub p q ≃ₐ[ℚ] Msub p q) :
    cyclotomicScalar p q σ ≠ 0 := (cyclotomicScalar_isUnit p q σ).ne_zero

lemma kummerValue_conjugate (hp : 0 < p) (σ : Msub p q ≃ₐ[ℚ] Msub p q)
    (τ : Msub p q ≃ₐ[Bsub p q] Msub p q) (u : (𝓞 (F p))ˣ) :
    kummerValue p q (conjugateKummer p q hp σ τ) u =
      σ.toRingEquiv.toMulEquiv.restrictRootsOfUnity q
        (kummerValue p q τ (Circular.unitAction p (F p) (restrictToF p q hp σ)⁻¹ u)) := by
  let hq := (Fact.out : q.Prime).pos
  let v := Circular.unitAction p (F p) (restrictToF p q hp σ)⁻¹ u
  have hpow : (σ⁻¹ (unitRoot p q hq u)) ^ q = unitRoot p q hq v ^ q := by
    rw [← map_pow, unitRoot_pow, unitRoot_pow, restrictToF_unitAction,
      restrictToF_inv]
  have hr := Kummer.root_ratio_independent (Bsub p q) (Msub p q) q
    (kummerZeta p q) (kummerZeta_spec p q hq) τ
    (σ⁻¹ (unitRoot p q hq u)) (unitRoot p q hq v)
    ((map_ne_zero σ⁻¹).2 (unitRoot_ne_zero p q hq u)) (unitRoot_ne_zero p q hq v) hpow
  have heq : σ (τ (σ⁻¹ (unitRoot p q hq u))) / unitRoot p q hq u =
      σ (τ (unitRoot p q hq v) / unitRoot p q hq v) := by
    calc
      _ = σ (τ (σ⁻¹ (unitRoot p q hq u)) / (σ⁻¹ (unitRoot p q hq u))) := by
        rw [map_div₀]
        simp
      _ = _ := congrArg σ hr
  apply Subtype.ext
  apply Units.ext
  exact heq

lemma kummerFunctional_conjugate_apply (hp : 0 < p) (σ : Msub p q ≃ₐ[ℚ] Msub p q)
    (τ : Msub p q ≃ₐ[Bsub p q] Msub p q) (z : PowerQuotient (𝓞 (F p))ˣ q) :
    kummerFunctional p q (conjugateKummer p q hp σ τ) z =
      cyclotomicScalar p q σ * kummerFunctional p q τ
        (UnitModule.unitRepresentation p (F p) q (restrictToF p q hp σ)⁻¹ z) := by
  induction z using QuotientGroup.induction_on with
  | _ u =>
    change kummerCoordinate p q (Additive.ofMul (kummerValue p q (conjugateKummer p q hp σ τ) u)) =
      cyclotomicScalar p q σ * kummerCoordinate p q
        (Additive.ofMul (kummerValue p q τ
          (Circular.unitAction p (F p) (restrictToF p q hp σ)⁻¹ u)))
    rw [kummerValue_conjugate]
    exact Kummer.rootsOfUnityCoordinate_aut (Msub p q) q (kummerZetaUnitM p q)
      (kummerZetaUnitM_spec p q) σ.toRingEquiv _

lemma kummerFunctional_conjugate (hp : 0 < p) (σ : Msub p q ≃ₐ[ℚ] Msub p q)
    (τ : Msub p q ≃ₐ[Bsub p q] Msub p q) :
    kummerFunctional p q (conjugateKummer p q hp σ τ) =
      cyclotomicScalar p q σ •
        ((UnitModule.unitRepresentation p (F p) q).dual (restrictToF p q hp σ)
          (kummerFunctional p q τ)) := by
  apply LinearMap.ext
  intro z
  exact kummerFunctional_conjugate_apply p q hp σ τ z

lemma commuting_kummerFunctional_eigen (hp : 0 < p)
    (σ : Msub p q ≃ₐ[ℚ] Msub p q) (τ : Msub p q ≃ₐ[Bsub p q] Msub p q)
    (h : σ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ) :
    (UnitModule.unitRepresentation p (F p) q).dual (restrictToF p q hp σ)
      (kummerFunctional p q τ) =
        (cyclotomicScalar p q σ)⁻¹ • kummerFunctional p q τ := by
  have hc := kummerFunctional_conjugate p q hp σ τ
  rw [conjugateKummer_eq_self_of_commute p q hp σ τ h] at hc
  calc
    _ = (cyclotomicScalar p q σ)⁻¹ •
        (cyclotomicScalar p q σ •
          ((UnitModule.unitRepresentation p (F p) q).dual (restrictToF p q hp σ)
            (kummerFunctional p q τ))) := by
      rw [smul_smul, inv_mul_cancel₀ (cyclotomicScalar_ne_zero p q σ), one_smul]
    _ = _ := congrArg (fun f => (cyclotomicScalar p q σ)⁻¹ • f) hc.symm

end Catalan.A3
