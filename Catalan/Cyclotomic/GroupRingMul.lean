import Catalan.Cyclotomic.GroupRing

/-! Multiplicativity of weight and submultiplicativity of coefficient size. -/
open scoped BigOperators
noncomputable section
namespace Catalan
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]
local instance : Fintype (G p K) := Fintype.ofFinite _

lemma weight_single (τ : G p K) (m : ℤ) :
    weight p K (MonoidAlgebra.single τ m) = m := by
  exact Finsupp.sum_single_index rfl

lemma size_single (τ : G p K) (m : ℤ) :
    size p K (MonoidAlgebra.single τ m) = |m| := by
  exact Finsupp.sum_single_index abs_zero

lemma weight_mul (A B : R p K) :
    weight p K (A * B) = weight p K A * weight p K B := by
  refine MonoidAlgebra.induction_linear A ?_ ?_ ?_
  · rw [zero_mul, weight_zero, zero_mul]
  · intro A A' hA hA'
    rw [add_mul, weight_add, hA, hA', weight_add, add_mul]
  · intro τ m
    refine MonoidAlgebra.induction_linear B ?_ ?_ ?_
    · rw [mul_zero, weight_zero, mul_zero]
    · intro B B' hB hB'
      rw [mul_add, weight_add, hB, hB', weight_add, mul_add]
    · intro υ n
      rw [MonoidAlgebra.single_mul_single, weight_single, weight_single, weight_single]

lemma size_mul_le (A B : R p K) :
    size p K (A * B) ≤ size p K A * size p K B := by
  classical
  have hcoeff (g : G p K) : (A * B).coeff g =
      ∑ h : G p K, A.coeff h * B.coeff (h⁻¹ * g) := by
    rw [MonoidAlgebra.coeff_mul_apply_left]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)
  have hperm (h : G p K) :
      (∑ g : G p K, |B.coeff (h⁻¹ * g)|) = ∑ g : G p K, |B.coeff g| :=
    Equiv.sum_comp (Equiv.mulLeft h⁻¹) (fun g => |B.coeff g|)
  rw [size_eq_sum, size_eq_sum, size_eq_sum]
  simp_rw [hcoeff]
  calc
    (∑ g : G p K, |∑ h : G p K, A.coeff h * B.coeff (h⁻¹ * g)|) ≤
        ∑ g : G p K, ∑ h : G p K, |A.coeff h| * |B.coeff (h⁻¹ * g)| := by
      apply Finset.sum_le_sum
      intro g _
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun h : G p K => A.coeff h * B.coeff (h⁻¹ * g)) Finset.univ
    _ = ∑ h : G p K, |A.coeff h| * (∑ g : G p K, |B.coeff (h⁻¹ * g)|) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = (∑ h : G p K, |A.coeff h|) * ∑ g : G p K, |B.coeff g| := by
      simp_rw [hperm]
      rw [Finset.sum_mul]

end Catalan
