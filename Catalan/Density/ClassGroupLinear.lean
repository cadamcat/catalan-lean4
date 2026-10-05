module

public import Catalan.Density.GaloisModules
public import Catalan.Density.HClassQuotient

/-!
# `Catalan.Density.ClassGroupLinear`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]
attribute [local instance] HGalCommGroup HGalModule

def classGroupModQLinearEquivHGal (hq : Odd q) :
    UnitQuotient.PowerQuotient (ClassGroup (𝓞 (F p))) q ≃ₗ[ZMod q]
      Additive (Hsub p q ≃ₐ[F p] Hsub p q) := by
  let e := (classGroupModQEquivHGal p q hq).toAdditive
  exact LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap q) e.bijective

lemma classGroupModQLinearEquivHGal_powerClass (hq : Odd q) (c : ClassGroup (𝓞 (F p))) :
    classGroupModQLinearEquivHGal p q hq (UnitQuotient.powerClass q c) =
      Additive.ofMul (classGroupToHGal p q hq c) := rfl

end Catalan.A3
