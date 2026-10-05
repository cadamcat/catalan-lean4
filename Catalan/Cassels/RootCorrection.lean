module

public import Catalan.Cassels.Defs

/-!
# `Catalan.Cassels.RootCorrection`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

lemma cassels_rpow_sub_le {r L A B : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hL : 0 < L) (hA : L ≤ A) (hB : L ≤ B) :
    |Real.rpow B r - Real.rpow A r| ≤
      (r * Real.rpow L (r - 1)) * |B - A| := by
  have hd : ∀ x ∈ Set.Ici L,
      HasDerivWithinAt (fun x : ℝ => Real.rpow x r)
        (r * Real.rpow x (r - 1)) (Set.Ici L) x := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hL.trans_le hx)))).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ici L,
      ‖r * Real.rpow x (r - 1)‖ ≤ r * Real.rpow L (r - 1) := by
    intro x hx
    simp only [Real.rpow_eq_pow]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hr0 (Real.rpow_nonneg (hL.le.trans hx) _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hL hx (sub_nonpos.mpr hr1)) hr0
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici L) hA hB

lemma cassels_root_inputs_lower (p : ℕ) (hpodd : Odd p)
    (t : ℝ) (ht : |t| ≤ (1 : ℝ) / 2) :
    0 < (1 - |t|) ^ p ∧
      (1 - |t|) ^ p ≤ (1 + t) ^ p ∧
      (1 - |t|) ^ p ≤ (1 + t) ^ p - t ^ p := by
  have hb : 0 < 1 - |t| := by linarith
  have hb1 : 1 - |t| ≤ 1 := by linarith [abs_nonneg t]
  have hba : 1 - |t| ≤ 1 + t := by linarith [neg_abs_le t]
  have hA : (1 - |t|) ^ p ≤ (1 + t) ^ p := pow_le_pow_left₀ hb.le hba p
  refine ⟨pow_pos hb p, hA, ?_⟩
  by_cases ht0 : 0 ≤ t
  · have hp0 : p ≠ 0 := by rcases hpodd with ⟨k, hk⟩; omega
    have hbin := pow_add_pow_le (x := (1 : ℝ)) (y := t) (n := p)
      zero_le_one ht0 hp0
    have hbp : (1 - |t|) ^ p ≤ 1 := pow_le_one₀ hb.le hb1
    simp only [one_pow] at hbin
    linarith
  · have htp : t ^ p ≤ 0 := hpodd.pow_nonpos (le_of_not_ge ht0)
    linarith

lemma cassels_power_absorption (p m : ℕ) (hmp : m + 1 ≤ p)
    (α u b : ℝ) (hu : 0 ≤ u) (hb : 0 < b) (hb1 : b ≤ 1) (hub : u ≤ b)
    (hlo : (m : ℝ) - 1 ≤ α) :
    u ^ p * Real.rpow b (α - (p : ℝ)) ≤ u ^ (m + 1) / b ^ 2 := by
  obtain ⟨N, hN⟩ := Nat.exists_eq_add_of_le hmp
  have hcast : (p : ℝ) = (m : ℝ) + 1 + (N : ℝ) := by exact_mod_cast hN
  calc
    u ^ p * b ^ (α - (p : ℝ)) =
        (u ^ (m + 1) * u ^ N) * b ^ (α - (p : ℝ)) := by
      rw [hN, pow_add]
    _ ≤ (u ^ (m + 1) * b ^ N) * b ^ (α - (p : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hub N) (pow_nonneg hu _))
        (Real.rpow_nonneg hb.le _)
    _ = u ^ (m + 1) * b ^ (α - (m : ℝ) - 1) := by
      rw [mul_assoc, ← Real.rpow_natCast b N, ← Real.rpow_add hb]
      congr 2
      linarith
    _ ≤ u ^ (m + 1) * b ^ (-2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hb hb1 (by linarith)) (pow_nonneg hu _)
    _ = u ^ (m + 1) / b ^ 2 := by
      rw [Real.rpow_neg hb.le, Real.rpow_ofNat]
      rfl

lemma cassels_root_correction_bound
    (p q m : ℕ) (hpodd : Odd p) (hq0 : 0 < q) (hmp : m + 1 ≤ p)
    (hlo : (m : ℝ) - 1 ≤ (p : ℝ) / (q : ℝ))
    (t : ℝ) (ht : |t| ≤ (1 : ℝ) / 2) :
    |casselsF p q t - Real.rpow (1 + t) ((p : ℝ) / (q : ℝ))| ≤
      |t| ^ (m + 1) / ((q : ℝ) * (1 - |t|) ^ 2) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast hq0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hr0 : 0 ≤ (1 : ℝ) / q := le_of_lt (one_div_pos.mpr hq)
  have hr1 : (1 : ℝ) / q ≤ 1 := (div_le_one hq).mpr hq1
  have hb : 0 < 1 - |t| := by linarith
  have ha : 0 < 1 + t := by linarith [neg_abs_le t]
  obtain ⟨hL, hA, hB⟩ := cassels_root_inputs_lower p hpodd t ht
  have hroot := cassels_rpow_sub_le hr0 hr1 hL hA hB
  have hAr : Real.rpow ((1 + t) ^ p) ((1 : ℝ) / q) =
      Real.rpow (1 + t) ((p : ℝ) / q) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    ring
  have hLr : Real.rpow ((1 - |t|) ^ p) ((1 : ℝ) / q - 1) =
      Real.rpow (1 - |t|) ((p : ℝ) / q - (p : ℝ)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    congr 1
    ring
  have hdiff : |((1 + t) ^ p - t ^ p) - (1 + t) ^ p| = |t| ^ p := by
    rw [sub_sub_cancel_left, abs_neg, abs_pow]
  rw [hAr, hLr, hdiff] at hroot
  have habs := cassels_power_absorption p m hmp ((p : ℝ) / q) |t| (1 - |t|)
    (abs_nonneg t) hb (by linarith [abs_nonneg t]) (by linarith) hlo
  unfold casselsF
  calc
    |Real.rpow ((1 + t) ^ p - t ^ p) ((1 : ℝ) / q) -
        Real.rpow (1 + t) ((p : ℝ) / q)|
      ≤ ((1 : ℝ) / q * Real.rpow (1 - |t|) ((p : ℝ) / q - (p : ℝ))) * |t| ^ p := hroot
    _ = ((1 : ℝ) / q) *
        (|t| ^ p * Real.rpow (1 - |t|) ((p : ℝ) / q - (p : ℝ))) := by ring
    _ ≤ ((1 : ℝ) / q) * (|t| ^ (m + 1) / (1 - |t|) ^ 2) :=
      mul_le_mul_of_nonneg_left habs hr0
    _ = |t| ^ (m + 1) / ((q : ℝ) * (1 - |t|) ^ 2) := by
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring

end Catalan

#print axioms Catalan.cassels_rpow_sub_le
#print axioms Catalan.cassels_root_inputs_lower
#print axioms Catalan.cassels_power_absorption
#print axioms Catalan.cassels_root_correction_bound
