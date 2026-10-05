module

public import Mathlib

/-!
# `Catalan.Thaine.OrbitReindex`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Catalan.Thaine

lemma finsum_reindex_subtype_equiv
    (X G V : Type*) [Fintype G] [AddCommMonoid V]
    (E : X → Prop) (e : G ≃ {x : X // E x}) (f : X → V)
    (hzero : ∀ x, ¬ E x → f x = 0) :
    (∑ᶠ x, f x) = ∑ g : G, f (e g).val := by
  classical
  let t : Finset X := Finset.univ.image (fun g : G => (e g).val)
  have hs : Function.support f ⊆ t := by
    intro x hx
    have hEx : E x := by
      by_contra h
      exact hx (hzero x h)
    obtain ⟨g, hg⟩ := e.surjective ⟨x, hEx⟩
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, congrArg Subtype.val hg⟩
  rw [finsum_eq_sum_of_support_subset _ hs]
  dsimp only [t]
  rw [Finset.sum_image]
  intro g _ h _ heq
  exact e.injective (Subtype.ext heq)

def groupAlgebraOfFunction
    (k G : Type*) [CommSemiring k] [Monoid G] [Fintype G] (f : G → k) :
    MonoidAlgebra k G := ∑ g : G, MonoidAlgebra.single g (f g)

lemma groupAlgebraOfFunction_coeff
    (k G : Type*) [CommSemiring k] [Monoid G] [Fintype G] (f : G → k) (g : G) :
    (groupAlgebraOfFunction k G f).coeff g = f g := by
  classical
  simp [groupAlgebraOfFunction, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

lemma groupAlgebraOfFunction_action
    (k G V : Type*) [CommSemiring k] [Monoid G] [Fintype G]
    [AddCommMonoid V] [Module k V]
    (rho : Representation k G V) (f : G → k) (v : V) :
    rho.asAlgebraHom (groupAlgebraOfFunction k G f) v = ∑ g : G, f g • rho g v := by
  simp only [groupAlgebraOfFunction, map_sum, Representation.asAlgebraHom_single,
    LinearMap.sum_apply, LinearMap.smul_apply]

end Catalan.Thaine
