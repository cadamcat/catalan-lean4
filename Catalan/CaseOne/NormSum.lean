import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction

noncomputable def groupNorm (k G : Type*) [CommRing k] [Group G] [Fintype G] : MonoidAlgebra k G :=
  ∑ g : G, MonoidAlgebra.single g (1 : k)

lemma groupNorm_eq_sum_powers (k G : Type*) [CommRing k] [Group G] [Fintype G]
    (τ : G) (hτ : ∀ g : G, g ∈ Subgroup.zpowers τ) :
    groupNorm k G = ∑ i ∈ Finset.range (Nat.card G), (MonoidAlgebra.single τ (1 : k)) ^ i := by
  classical
  have horder : orderOf τ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hτ
  unfold groupNorm
  rw [← IsCyclic.image_range_orderOf hτ, Finset.sum_image]
  · simp only [MonoidAlgebra.single_pow, one_pow, horder]
  · intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

end Catalan.UnitReduction
