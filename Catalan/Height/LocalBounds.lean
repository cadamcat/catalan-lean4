import Catalan.Height.Basic

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable {L : Type*} [Field L] [NumberField L]

lemma height_lt_of_local_bounds (a : L) (C D : ℝ) (hC : 1 < C)
    (harch : ∀ w : InfinitePlace L, w a < C)
    (hf : (∑ᶠ v : FinitePlace L, Real.log (max (v a) 1)) ≤ D) :
    logHeight a < Real.log C + D / (Module.finrank ℚ L : ℝ) := by
  have hd : 0 < (Module.finrank ℚ L : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ L)
  have harch_sum :
      (∑ w : InfinitePlace L,
          (w.mult : ℝ) * Real.log (max (w a) 1)) <
        (Module.finrank ℚ L : ℝ) * Real.log C := by
    have hterm (w : InfinitePlace L) :
        (w.mult : ℝ) * Real.log (max (w a) 1) <
          (w.mult : ℝ) * Real.log C := by
      have hmax : max (w a) 1 < C := max_lt (harch w) hC
      have hmax_pos : 0 < max (w a) 1 :=
        lt_of_lt_of_le zero_lt_one (le_max_right (w a) 1)
      have hlog : Real.log (max (w a) 1) < Real.log C :=
        Real.log_lt_log hmax_pos hmax
      have hmult : (0 : ℝ) < (w.mult : ℝ) := by
        exact_mod_cast (NumberField.InfinitePlace.mult_pos : 0 < w.mult)
      exact mul_lt_mul_of_pos_left hlog hmult
    have hsum := Finset.sum_lt_sum_of_nonempty
      (s := (Finset.univ : Finset (InfinitePlace L)))
      (Finset.univ_nonempty) (fun w _hw => hterm w)
    calc
      (∑ w : InfinitePlace L,
          (w.mult : ℝ) * Real.log (max (w a) 1)) <
          ∑ w : InfinitePlace L, (w.mult : ℝ) * Real.log C := hsum
      _ = (Module.finrank ℚ L : ℝ) * Real.log C := by
        rw [← Finset.sum_mul, ← Nat.cast_sum,
          NumberField.InfinitePlace.sum_mult_eq]
  have htotal :
      (∑ w : InfinitePlace L,
          (w.mult : ℝ) * Real.log (max (w a) 1)) +
          ∑ᶠ v : FinitePlace L, Real.log (max (v a) 1) <
        (Module.finrank ℚ L : ℝ) * Real.log C + D :=
    add_lt_add_of_lt_of_le harch_sum hf
  have hscaled := mul_lt_mul_of_pos_left htotal (inv_pos.mpr hd)
  unfold logHeight
  calc
    (↑(Module.finrank ℚ L))⁻¹ *
          ((∑ w : InfinitePlace L,
              (w.mult : ℝ) * Real.log (max (w a) 1)) +
            ∑ᶠ v : FinitePlace L, Real.log (max (v a) 1)) <
        (↑(Module.finrank ℚ L))⁻¹ *
          ((Module.finrank ℚ L : ℝ) * Real.log C + D) := hscaled
    _ = Real.log C + D / (Module.finrank ℚ L : ℝ) := by
      field_simp

end Catalan
