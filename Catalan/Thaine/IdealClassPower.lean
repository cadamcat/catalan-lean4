module

public import Catalan.Thaine.IntegralClassAction
public import Catalan.Stickelberger.ClassReduction
public import Catalan.Wieferich.IdealGenerator

/-!
# `Catalan.Thaine.IdealClassPower`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma integralClassRepresentation_mk_ipow
    (p : ℕ) (F : Type*) [Field F] [NumberField F]
    (J : FracIdealUnit F) (Psi : R p F) :
    Additive.ofMul (ClassGroup.mk F (ipow p F J Psi)) =
      (integralClassRepresentation F).asAlgebraHom Psi
        (Additive.ofMul (ClassGroup.mk F J)) := by
  refine MonoidAlgebra.induction_linear Psi ?_ ?_ ?_
  · simp only [ipow_zero, map_one, ofMul_one, map_zero, LinearMap.zero_apply]
  · intro A B hA hB
    simp only [ipow_add, map_mul, ofMul_mul, map_add, LinearMap.add_apply, hA, hB]
  · intro g m
    simp only [ipow_single, map_zpow, ofMul_zpow,
      Representation.asAlgebraHom_single, LinearMap.smul_apply]
    rw [integralClassRepresentation_apply, ordinaryClassAction_mk]

lemma upow_eq_unit_mul_pow_of_class_annihilation
    (p q : ℕ) (F : Type*) [Field F] [NumberField F]
    (lam : Fˣ) (J : FracIdealUnit F) (Psi : R p F)
    (hideal : principalIdeal F lam = J ^ q)
    (hkill : (integralClassRepresentation F).asAlgebraHom Psi
      (Additive.ofMul (ClassGroup.mk F J)) = 0) :
    ∃ u : (𝓞 F)ˣ, ∃ b : Fˣ,
      upow p F lam Psi = Units.map (algebraMap (𝓞 F) F).toMonoidHom u * b ^ q := by
  have hclass : ClassGroup.mk F (ipow p F J Psi) = 1 := by
    have hzero := (integralClassRepresentation_mk_ipow p F J Psi).trans hkill
    exact congrArg Additive.toMul hzero
  obtain ⟨b, hb⟩ := principalIdeal_of_class_eq_one F (ipow p F J Psi) hclass
  have heq : principalIdeal F (upow p F lam Psi) = principalIdeal F (b ^ q) := by
    have hcompat : ipow p F (principalIdeal F lam) Psi =
        principalIdeal F (upow p F lam Psi) := ipow_principalIdeal p F lam Psi
    rw [← hcompat, hideal, ← zpow_natCast J q, ipow_zpow, hb]
    simp only [zpow_natCast, map_pow]
  obtain ⟨u, hu⟩ := A1e.exists_unit_mul_of_principalIdeal_eq F _ _ heq
  exact ⟨u, b, hu⟩

end Catalan.Thaine
