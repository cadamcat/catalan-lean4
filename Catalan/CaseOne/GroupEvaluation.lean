module

public import Mathlib

/-!
# `Catalan.CaseOne.GroupEvaluation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma cyclic_group_algebra_aeval_surjective
    (k G : Type*) [CommRing k] [Group G] [Finite G]
    (τ : G) (hτ : ∀ g : G, g ∈ Subgroup.zpowers τ) :
    Function.Surjective (Polynomial.aeval (R := k) (MonoidAlgebra.single τ (1 : k))) := by
  classical
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨f, hf⟩ := hx
    obtain ⟨g, hg⟩ := hy
    exact ⟨f + g, by rw [map_add, hf, hg]⟩
  | single g c =>
    obtain ⟨n, hn⟩ := (isOfFinOrder_of_finite τ).mem_powers_iff_mem_zpowers.mpr (hτ g)
    change τ ^ n = g at hn
    refine ⟨Polynomial.C c * Polynomial.X ^ n, ?_⟩
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      MonoidAlgebra.single_pow, one_pow, hn]
    simp [MonoidAlgebra.coe_algebraMap]

end Catalan.UnitReduction
