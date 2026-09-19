import Catalan.Cassels.Defs

open scoped BigOperators

namespace Catalan

lemma casselsCoeff_real_eq (p q k : ℕ) (hq0 : 0 < q) :
    (casselsCoeff p q k : ℝ) =
      (∏ i ∈ Finset.range k, ((p : ℝ) / (q : ℝ) - (i : ℝ))) /
        (k.factorial : ℝ) := by
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq0)
  have hfactor : ∀ i : ℕ,
      (p : ℚ) - (i : ℚ) * (q : ℚ) =
        (q : ℚ) * ((p : ℚ) / (q : ℚ) - (i : ℚ)) := by
    intro i
    field_simp
  have hprod :
      (∏ i ∈ Finset.range k, ((p : ℚ) - (i : ℚ) * (q : ℚ))) =
        (q : ℚ) ^ k *
          (∏ i ∈ Finset.range k, ((p : ℚ) / (q : ℚ) - (i : ℚ))) := by
    rw [show (∏ i ∈ Finset.range k, ((p : ℚ) - (i : ℚ) * (q : ℚ))) =
        ∏ i ∈ Finset.range k,
          ((q : ℚ) * ((p : ℚ) / (q : ℚ) - (i : ℚ))) by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hfactor i]]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    simp [Finset.card_range]
  have hrat : casselsCoeff p q k =
      (∏ i ∈ Finset.range k, ((p : ℚ) / (q : ℚ) - (i : ℚ))) /
        (k.factorial : ℚ) := by
    unfold casselsCoeff
    rw [hprod]
    field_simp
  rw [hrat]
  rw [Rat.cast_div_of_ne_zero]
  · simp
  · exact_mod_cast (Rat.den_ne_zero
      (∏ i ∈ Finset.range k, ((p : ℚ) / (q : ℚ) - (i : ℚ))))
  · simpa using (Nat.factorial_ne_zero k)

lemma cassels_coeff_cutoff_aux (alpha : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hlo : (m : ℝ) - 1 ≤ alpha) (hhi : alpha ≤ (m : ℝ)) :
    |(∏ i ∈ Finset.range (m + 1), (alpha - (i : ℝ))) /
        ((m + 1).factorial : ℝ)| ≤ 1 / ((m : ℝ) + 1) := by
  have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hfacpos : 0 < (m.factorial : ℝ) := by positivity
  have hfac_succ : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    norm_num
  have hprod_nonneg :
      0 ≤ ∏ i ∈ Finset.range m, (alpha - (i : ℝ)) := by
    apply Finset.prod_nonneg
    intro i hi
    have hi_lt : i < m := Finset.mem_range.mp hi
    have hi_le_pred : i ≤ m - 1 := Nat.le_pred_of_lt hi_lt
    have hi_le_alpha : (i : ℝ) ≤ alpha := by
      calc
        (i : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hi_le_pred
        _ = (m : ℝ) - 1 := by norm_num [Nat.cast_sub hm]
        _ ≤ alpha := hlo
    exact sub_nonneg.mpr hi_le_alpha
  have hprod_le :
      (∏ i ∈ Finset.range m, (alpha - (i : ℝ))) ≤
        ∏ i ∈ Finset.range m, ((m : ℝ) - (i : ℝ)) := by
    apply Finset.prod_le_prod
    · intro i hi
      have hi_lt : i < m := Finset.mem_range.mp hi
      have hi_le_pred : i ≤ m - 1 := Nat.le_pred_of_lt hi_lt
      have hi_le_alpha : (i : ℝ) ≤ alpha := by
        calc
          (i : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hi_le_pred
          _ = (m : ℝ) - 1 := by norm_num [Nat.cast_sub hm]
          _ ≤ alpha := hlo
      exact sub_nonneg.mpr hi_le_alpha
    · intro i hi
      exact sub_le_sub_right hhi _
  have hprod_factorial :
      ∏ i ∈ Finset.range m, ((m : ℝ) - (i : ℝ)) = (m.factorial : ℝ) := by
    have hterm : ∀ i ∈ Finset.range m,
        ((m : ℝ) - (i : ℝ)) = ((m - i : ℕ) : ℝ) := by
      intro i hi
      have hi_le : i ≤ m := Nat.le_of_lt (Finset.mem_range.mp hi)
      rw [Nat.cast_sub hi_le]
    rw [show (∏ i ∈ Finset.range m, ((m : ℝ) - (i : ℝ))) =
        ∏ i ∈ Finset.range m, ((m - i : ℕ) : ℝ) by
      apply Finset.prod_congr rfl
      intro i hi
      exact hterm i hi]
    have hnat : ∏ i ∈ Finset.range m, (m - i) = m.factorial := by
      rw [← Nat.descFactorial_eq_prod_range,
        Nat.descFactorial_eq_factorial_mul_choose]
      simp
    exact_mod_cast hnat
  have hprod_le_fac :
      (∏ i ∈ Finset.range m, (alpha - (i : ℝ))) ≤ (m.factorial : ℝ) := by
    rw [← hprod_factorial]
    exact hprod_le
  have hlast_abs : |alpha - (m : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hsplit :
      (∏ i ∈ Finset.range (m + 1), (alpha - (i : ℝ))) =
        (∏ i ∈ Finset.range m, (alpha - (i : ℝ))) * (alpha - (m : ℝ)) := by
    rw [Finset.prod_range_succ]
  have hdenpos : 0 < ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    positivity
  have hnum :
      (∏ i ∈ Finset.range m, (alpha - (i : ℝ))) * |alpha - (m : ℝ)| ≤
        (m.factorial : ℝ) * 1 := by
    exact mul_le_mul hprod_le_fac hlast_abs (abs_nonneg _) hfacpos.le
  calc
    |(∏ i ∈ Finset.range (m + 1), (alpha - (i : ℝ))) /
        ((m + 1).factorial : ℝ)| =
        ((∏ i ∈ Finset.range m, (alpha - (i : ℝ))) *
          |alpha - (m : ℝ)|) /
          (((m : ℝ) + 1) * (m.factorial : ℝ)) := by
      rw [abs_div, hsplit, abs_mul, abs_of_nonneg hprod_nonneg, hfac_succ,
        abs_of_pos hdenpos]
    _ ≤ ((m.factorial : ℝ) * 1) /
          (((m : ℝ) + 1) * (m.factorial : ℝ)) := by
      exact div_le_div_of_nonneg_right hnum hdenpos.le
    _ = 1 / ((m : ℝ) + 1) := by
      field_simp

lemma cassels_coeff_cutoff_bound (p q m : ℕ) (hq0 : 0 < q) (hm : 1 ≤ m)
    (hlo : (m : ℝ) - 1 ≤ (p : ℝ) / (q : ℝ))
    (hhi : (p : ℝ) / (q : ℝ) ≤ (m : ℝ)) :
    |(casselsCoeff p q (m + 1) : ℝ)| ≤ 1 / ((m : ℝ) + 1) := by
  rw [casselsCoeff_real_eq p q (m + 1) hq0]
  exact cassels_coeff_cutoff_aux ((p : ℝ) / (q : ℝ)) m hm hlo hhi

end Catalan

#print axioms Catalan.casselsCoeff_real_eq
#print axioms Catalan.cassels_coeff_cutoff_aux
#print axioms Catalan.cassels_coeff_cutoff_bound
