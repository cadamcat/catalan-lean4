import Mathlib

namespace Catalan
open NumberField

lemma finite_power_near_one (K : Type*) [Field K] [NumberField K]
    (q : ℕ) (v : FinitePlace K) (a : K)
    (ha : v (a - 1) < 1) : v (a ^ q - 1) ≤ v (a - 1) := by
  have hva : v a ≤ 1 := by
    simpa only [sub_add_cancel, map_one, max_eq_right ha.le] using v.add_le (a - 1) 1
  induction q with
  | zero => simpa only [pow_zero, sub_self, map_zero] using apply_nonneg v (a - 1)
  | succ q ih =>
      have hid : a ^ (q + 1) - 1 = a * (a ^ q - 1) + (a - 1) := by
        rw [pow_succ]
        ring
      rw [hid]
      refine (v.add_le _ _).trans (max_le ?_ le_rfl)
      rw [map_mul]
      calc
        v a * v (a ^ q - 1) ≤ 1 * v (a ^ q - 1) :=
          mul_le_mul_of_nonneg_right hva (apply_nonneg v _)
        _ ≤ v (a - 1) := by simpa only [one_mul] using ih

end Catalan

