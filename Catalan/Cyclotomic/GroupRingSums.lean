module

public import Catalan.Cyclotomic.GroupRingMul

/-!
# `Catalan.Cyclotomic.GroupRingSums`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Catalan
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]
local instance instNextSizeFintypeG : Fintype (G p K) := Fintype.ofFinite _

lemma size_zsmul (z : ℤ) (T : R p K) :
    size p K (z • T) = |z| * size p K T := by
  rw [size_eq_sum, size_eq_sum]
  simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul]
  rw [Finset.mul_sum]

lemma weight_zsmul (z : ℤ) (T : R p K) :
    weight p K (z • T) = z * weight p K T := by
  rw [weight_eq_sum, weight_eq_sum]
  simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]

lemma size_sum_le {ι : Type*} (s : Finset ι) (f : ι → R p K) :
    size p K (∑ i ∈ s, f i) ≤ ∑ i ∈ s, size p K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, size_zero, le_refl]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (size_add_le p K (f i) _).trans (add_le_add le_rfl ih)

lemma weight_sum {ι : Type*} (s : Finset ι) (f : ι → R p K) :
    weight p K (∑ i ∈ s, f i) = ∑ i ∈ s, weight p K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, weight_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, weight_add, ih]

end Catalan
