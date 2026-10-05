module

public import Catalan.Density.GaloisModules
public import Catalan.Density.HLift

/-!
# `Catalan.Density.HRestriction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]
attribute [local instance] TGalCommGroup TGalModule HGalCommGroup HGalModule

lemma TToHLinear_surjective (hq : Odd q) : Function.Surjective (TToHLinear p q) := by
  intro tau
  obtain ⟨sigma, hsigma⟩ := exists_T_lift_H p q hq (Additive.toMul tau)
  refine ⟨Additive.ofMul sigma, ?_⟩
  apply Additive.toMul.injective
  change restrictTToH p q sigma = Additive.toMul tau
  apply AlgEquiv.ext
  intro x
  apply (algebraMap (Hsub p q) (T p q)).injective
  rw [restrictTToH_commutes, hsigma]

end Catalan.A3
