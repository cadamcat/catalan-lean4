module

public import Catalan.CaseOne.UnitRepresentation
public import Catalan.Runge.Reduction

/-!
# `Catalan.Thaine.IntegralUnitPow`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
open UnitQuotient
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

def integralUnitPow (u : (𝓞 K)ˣ) (Theta : R p K) : (𝓞 K)ˣ :=
  Theta.coeff.prod fun g m => (Circular.unitAction p K g u) ^ m

lemma map_integralUnitPow (u : (𝓞 K)ˣ) (Theta : R p K) :
    Units.map (algebraMap (𝓞 K) K).toMonoidHom (integralUnitPow p K u Theta) =
      upow p K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) Theta := by
  simp only [integralUnitPow, upow, map_finsuppProd, map_zpow]
  congr 1

lemma integralUnitPow_zero (u : (𝓞 K)ˣ) : integralUnitPow p K u 0 = 1 := by
  simp only [integralUnitPow, MonoidAlgebra.coeff_zero, Finsupp.prod_zero_index]

lemma integralUnitPow_add (u : (𝓞 K)ˣ) (Theta Psi : R p K) :
    integralUnitPow p K u (Theta + Psi) =
      integralUnitPow p K u Theta * integralUnitPow p K u Psi := by
  unfold integralUnitPow
  rw [MonoidAlgebra.coeff_add]
  exact Finsupp.prod_add_index' (fun _ => zpow_zero _)
    (fun _ _ _ => zpow_add _ _ _)

lemma integralUnitPow_single (u : (𝓞 K)ˣ) (g : G p K) (m : ℤ) :
    integralUnitPow p K u (MonoidAlgebra.single g m) =
      (Circular.unitAction p K g u) ^ m := by
  exact Finsupp.prod_single_index (zpow_zero _)

private lemma powerClass_mul {B : Type*} [CommGroup B] (q : ℕ) (u v : B) :
    powerClass q (u * v) = powerClass q u + powerClass q v :=
  (QuotientGroup.mk' (qPowers B q)).toAdditive.map_add
    (Additive.ofMul u) (Additive.ofMul v)

private lemma powerClass_zpow {B : Type*} [CommGroup B] (q : ℕ) (u : B) (m : ℤ) :
    powerClass q (u ^ m) = (m : ZMod q) • powerClass q u := by
  rw [Int.cast_smul_eq_zsmul]
  exact (QuotientGroup.mk' (qPowers B q)).toAdditive.map_zsmul m (Additive.ofMul u)

lemma powerClass_integralUnitPow (q : ℕ) (u : (𝓞 K)ˣ) (Theta : R p K) :
    powerClass q (integralUnitPow p K u Theta) =
      (unitRepresentation p K q).asAlgebraHom (Runge.reduceFull p K q Theta)
        (powerClass q u) := by
  refine MonoidAlgebra.induction_linear Theta ?_ ?_ ?_
  · rw [integralUnitPow_zero, map_zero, map_zero, LinearMap.zero_apply]
    rfl
  · intro A B hA hB
    rw [integralUnitPow_add, powerClass_mul, map_add, map_add, LinearMap.add_apply, hA, hB]
  · intro g m
    rw [integralUnitPow_single, powerClass_zpow]
    simp only [Runge.reduceFull, MonoidAlgebra.mapRingHom_single, Int.coe_castRingHom,
      Representation.asAlgebraHom_single, LinearMap.smul_apply]
    congr 1

end Catalan.UnitModule
