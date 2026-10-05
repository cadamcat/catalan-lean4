module

public import Catalan.Density.SelectorSpan
public import Catalan.Density.HRestriction
public import Catalan.Density.ClassGroupLinear

/-!
# `Catalan.Density.SelectorClassSpan`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
private lemma span_image_top {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : Set M) (hs : Submodule.span R s = ⊤) : Submodule.span R (f '' s) = ⊤ := by
  rw [← Submodule.map_span, hs, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

variable (p q : ℕ) [Fact q.Prime]
attribute [local instance] TGalCommGroup TGalModule HGalCommGroup HGalModule

lemma selectors_H_span [Fact p.Prime]
    (hp7 : 7 ≤ p) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2) :
    Submodule.span (ZMod q) ((TToHLinear p q) '' selectorVectors p q) = ⊤ := by
  rw [← Submodule.map_span, selectors_span p q hp7 hq2 hdegree, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    (TToHLinear_surjective p q ((Fact.out : q.Prime).odd_of_ne_two hq2))

def selectorClassVectors (hq : Odd q) :
    Set (UnitQuotient.PowerQuotient (ClassGroup (𝓞 (F p))) q) :=
  (classGroupModQLinearEquivHGal p q hq).symm ''
    ((TToHLinear p q) '' selectorVectors p q)

lemma selectorClassVectors_span [Fact p.Prime]
    (hp7 : 7 ≤ p) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2) (hq : Odd q) :
    Submodule.span (ZMod q) (selectorClassVectors p q hq) = ⊤ := by
  exact span_image_top (classGroupModQLinearEquivHGal p q hq).symm.toLinearMap
    (classGroupModQLinearEquivHGal p q hq).symm.surjective
    ((TToHLinear p q) '' selectorVectors p q) (selectors_H_span p q hp7 hq2 hdegree)

end Catalan.A3
