import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

lemma span_geometric_eq_norm_pair
    {R : Type*} [CommRing R] (u : R) (r : ℕ) (h2 : IsUnit (2 : R)) :
    Ideal.span ({∑ i ∈ Finset.range r, u ^ i} : Set R) =
      Ideal.span ({∑ i ∈ Finset.range (2 * r), u ^ i, 1 - u ^ r} : Set R) := by
  let P : R := ∑ i ∈ Finset.range r, u ^ i
  let N : R := ∑ i ∈ Finset.range (2 * r), u ^ i
  change Ideal.span ({P} : Set R) = Ideal.span ({N, 1 - u ^ r} : Set R)
  have hN : N = (1 + u ^ r) * P := by
    dsimp [N, P]
    rw [show 2 * r = r + r by omega, Finset.sum_range_add]
    simp_rw [pow_add]
    rw [← Finset.mul_sum]
    ring
  have hQ : 1 - u ^ r = P * (1 - u) := by
    dsimp [P]
    exact (geom_sum_mul_neg u r).symm
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    have hNmem : N ∈ Ideal.span ({N, 1 - u ^ r} : Set R) :=
      Ideal.subset_span (Set.mem_insert N (Set.singleton (1 - u ^ r)))
    have hQmem : 1 - u ^ r ∈ Ideal.span ({N, 1 - u ^ r} : Set R) :=
      Ideal.subset_span (by simp)
    have hPmem : P ∈ Ideal.span ({N, 1 - u ^ r} : Set R) := by
      have h2P : (2 : R) * P ∈ Ideal.span ({N, 1 - u ^ r} : Set R) := by
        have hsum : N + P * (1 - u ^ r) = (2 : R) * P := by
          rw [hN]
          ring
        have hprod : P * (1 - u ^ r) ∈ Ideal.span ({N, 1 - u ^ r} : Set R) :=
          Ideal.mul_mem_left _ _ hQmem
        rw [← hsum]
        exact add_mem hNmem hprod
      exact (Ideal.unit_mul_mem_iff_mem _ h2).mp h2P
    have hx' : x = P := by
      simpa only [Set.mem_singleton_iff] using hx
    rw [hx']
    exact hPmem
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [hN]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton P))
    · rw [hQ]
      exact Ideal.mul_mem_right (1 - u) _ (Ideal.subset_span (Set.mem_singleton P))

end Catalan.UnitReduction
