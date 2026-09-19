import Mathlib.NumberTheory.Height.NumberField
import Mathlib

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable {L : Type*} [Field L] [NumberField L]

def logHeight (a : L) : ℝ :=
  (Module.finrank ℚ L : ℝ)⁻¹ *
    ((∑ w : InfinitePlace L, (w.mult : ℝ) * Real.log (max (w a) 1)) +
      ∑ᶠ v : FinitePlace L, Real.log (max (v a) 1))

lemma logHeight_eq_normalized (a : L) :
    logHeight a = (Module.finrank ℚ L : ℝ)⁻¹ * Height.logHeight₁ a := by
  unfold logHeight
  rw [NumberField.logHeight₁_eq]
  simp_rw [Real.posLog_eq_log_max_one (apply_nonneg _ _), max_comm]

lemma height_pow (a : L) (n : ℕ) :
    logHeight (a ^ n) = (n : ℝ) * logHeight a := by
  rw [logHeight_eq_normalized, logHeight_eq_normalized, Height.logHeight₁_pow]
  ring

lemma height_inv (a : L) : logHeight a⁻¹ = logHeight a := by
  rw [logHeight_eq_normalized, logHeight_eq_normalized, Height.logHeight₁_inv]

lemma height_sub_le (a b : L) :
    logHeight (a - b) ≤ logHeight a + logHeight b + Real.log 2 := by
  have hd : 0 < (Module.finrank ℚ L : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ L)
  have h := Height.logHeight₁_sub_le a b
  rw [NumberField.totalWeight_eq_finrank] at h
  have hs := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hd.le)
  rw [logHeight_eq_normalized, logHeight_eq_normalized, logHeight_eq_normalized]
  calc
    (↑(Module.finrank ℚ L))⁻¹ * Height.logHeight₁ (a - b) ≤
        (↑(Module.finrank ℚ L))⁻¹ *
          (↑(Module.finrank ℚ L) * Real.log 2 + Height.logHeight₁ a +
            Height.logHeight₁ b) := hs
    _ = (↑(Module.finrank ℚ L))⁻¹ * Height.logHeight₁ a +
        (↑(Module.finrank ℚ L))⁻¹ * Height.logHeight₁ b + Real.log 2 := by
      field_simp
      ring

lemma height_div_le (a b : L) :
    logHeight (a / b) ≤ logHeight a + logHeight b := by
  have hd : 0 < (Module.finrank ℚ L : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ L)
  have h := Height.logHeight₁_mul_le a b⁻¹
  rw [Height.logHeight₁_inv] at h
  rw [div_eq_mul_inv]
  have hs := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hd.le)
  rw [logHeight_eq_normalized, logHeight_eq_normalized, logHeight_eq_normalized]
  simpa [mul_add, mul_assoc, add_assoc] using hs

lemma height_one : logHeight (1 : L) = 0 := by
  rw [logHeight_eq_normalized, Height.logHeight₁_one]
  simp

lemma height_intCast (x : ℤ) (hx : x ≠ 0) :
    logHeight (x : L) = Real.log (|x| : ℝ) := by
  have hd : 0 < (Module.finrank ℚ L : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ L)
  have hheight :
      Height.logHeight₁ (x : L) = (Module.finrank ℚ L : ℝ) * Real.log (|x| : ℝ) := by
    rw [NumberField.logHeight₁_eq]
    have hpos (w : InfinitePlace L) :
        (w (x : L)).posLog = Real.log (max (w (x : L)) 1) := by
      rw [Real.posLog_eq_log_max_one (apply_nonneg w (x : L)), max_comm]
    have hposf (v : FinitePlace L) :
        (v (x : L)).posLog = Real.log (max (v (x : L)) 1) := by
      rw [Real.posLog_eq_log_max_one (apply_nonneg v (x : L)), max_comm]
    simp_rw [hpos, hposf]
    have harch (w : InfinitePlace L) :
        (w.mult : ℝ) * Real.log (max (w (x : L)) 1) =
          (w.mult : ℝ) * Real.log (|x| : ℝ) := by
      have hcast : (1 : ℝ) ≤ (|x| : ℝ) := by
        exact_mod_cast Int.one_le_abs hx
      rw [NumberField.InfinitePlace.map_intCast, Int.norm_eq_abs, max_eq_left hcast]
    have hfin (v : FinitePlace L) : Real.log (max (v (x : L)) 1) = 0 := by
      have hv : IsNonarchimedean (v : L → ℝ) := NumberField.FinitePlace.add_le v
      have hle : v (x : L) ≤ 1 := IsNonarchimedean.apply_intCast_le_one hv
      rw [max_eq_right hle, Real.log_one]
    simp_rw [harch]
    rw [finsum_eq_zero_of_forall_eq_zero hfin]
    rw [← Finset.sum_mul]
    have hsum : (∑ w : InfinitePlace L, (w.mult : ℝ)) =
        (Module.finrank ℚ L : ℝ) := by
      rw [← Nat.cast_sum, NumberField.InfinitePlace.sum_mult_eq]
    rw [hsum]
    simp
  rw [logHeight_eq_normalized, hheight]
  field_simp

lemma height_root_unity (a : L) (n : ℕ) (hn : 0 < n) (ha : a ^ n = 1) :
    logHeight a = 0 := by
  have h := height_pow a n
  rw [ha, height_one] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

end Catalan
