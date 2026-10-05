module

public import Mathlib

/-!
# `Catalan.CaseOne.Involution`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma annihilator_span_one_add_involution
    {R : Type*} [CommRing R] (z : R) (hz : z ^ 2 = 1) (h2 : IsUnit (2 : R)) :
    (Ideal.span ({1 + z} : Set R)).annihilator = Ideal.span ({1 - z} : Set R) := by
  apply le_antisymm
  · intro x hx
    have hx0 : x * (1 + z) = 0 := by
      have hx' := (Submodule.mem_annihilator_span_singleton (1 + z) x).mp hx
      simpa only [smul_eq_mul] using hx'
    have hq : (1 - z : R) ∈ Ideal.span ({1 - z} : Set R) :=
      Ideal.subset_span (Set.mem_singleton (1 - z))
    have hprod : x * (1 - z) ∈ Ideal.span ({1 - z} : Set R) :=
      Ideal.mul_mem_left _ _ hq
    have h2x : (2 : R) * x ∈ Ideal.span ({1 - z} : Set R) := by
      rw [show (2 : R) * x = x * (1 - z) by
        calc
          (2 : R) * x = x * (1 + z) + x * (1 - z) := by ring
          _ = x * (1 - z) := by rw [hx0, zero_add]]
      exact hprod
    exact (Ideal.unit_mul_mem_iff_mem _ h2).mp h2x
  · rw [Ideal.span_le]
    intro x hx
    have hx' : x = 1 - z := by
      simpa only [Set.mem_singleton_iff] using hx
    rw [hx']
    apply (Submodule.mem_annihilator_span_singleton (1 + z) (1 - z)).mpr
    change (1 - z) * (1 + z) = 0
    calc
      (1 - z) * (1 + z) = 1 - z ^ 2 := by ring
      _ = 0 := by rw [hz, sub_self]

end Catalan.UnitReduction
