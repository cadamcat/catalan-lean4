import Catalan.Cassels.Defs

namespace Catalan

/-- The arithmetic bounds needed by the two analytic estimates. -/
lemma cassels_index_bounds (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p) :
    3 ≤ q ∧ Odd p ∧ 2 ≤ casselsIndex p q ∧ casselsIndex p q + 1 ≤ p ∧
      (casselsIndex p q : ℝ) - 1 ≤ (p : ℝ) / (q : ℝ) ∧
      (p : ℝ) / (q : ℝ) < (casselsIndex p q : ℝ) := by
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd : 1 ≤ p / q := Nat.div_pos (Nat.le_of_lt hqp) hq.pos
  have hmul : q * (p / q) ≤ p := Nat.mul_div_le p q
  have h3d : 3 * (p / q) ≤ q * (p / q) :=
    Nat.mul_le_mul_right (p / q) hq3
  have hm : 2 ≤ casselsIndex p q := by unfold casselsIndex; omega
  have hmp : casselsIndex p q + 1 ≤ p := by unfold casselsIndex; omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlo : (casselsIndex p q : ℝ) - 1 ≤ (p : ℝ) / (q : ℝ) := by
    apply (le_div_iff₀ hqR).mpr
    have hmulR : (q : ℝ) * (p / q : ℕ) ≤ (p : ℝ) := by exact_mod_cast hmul
    simp only [casselsIndex, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    nlinarith
  have hupper : p < (p / q + 1) * q := by
    have hmod := Nat.mod_lt p hq.pos
    have hdecomp := Nat.mod_add_div p q
    nlinarith
  have hhi : (p : ℝ) / (q : ℝ) < (casselsIndex p q : ℝ) := by
    apply (div_lt_iff₀ hqR).mpr
    exact_mod_cast hupper
  exact ⟨hq3, hp.odd_of_ne_two hp2, hm, hmp, hlo, hhi⟩

/-- Combine the two estimates using q≥3 and m+1≥3. -/
lemma cassels_remainder_of_bounds (p q m : ℕ) (hq : 3 ≤ q) (hm : 2 ≤ m)
    (t : ℝ) (ht : |t| < 1)
    (hTaylor : |Real.rpow (1 + t) ((p : ℝ) / (q : ℝ)) -
        casselsTaylor p q m t| ≤
      |t| ^ (m + 1) / (((m : ℝ) + 1) * (1 - |t|) ^ 2))
    (hRoot : |casselsF p q t - Real.rpow (1 + t) ((p : ℝ) / (q : ℝ))| ≤
      |t| ^ (m + 1) / ((q : ℝ) * (1 - |t|) ^ 2)) :
    |casselsF p q t - casselsTaylor p q m t| ≤
      |t| ^ (m + 1) / (1 - |t|) ^ 2 := by
  let R : ℝ := |t| ^ (m + 1) / (1 - |t|) ^ 2
  have hR : 0 ≤ R := div_nonneg (pow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (3 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (show 3 ≤ m + 1 by omega)
  have hRoot' : |casselsF p q t - Real.rpow (1 + t) ((p : ℝ) / (q : ℝ))| ≤ R / 3 := by
    apply hRoot.trans
    change _ ≤ (|t| ^ (m + 1) / (1 - |t|) ^ 2) / 3
    rw [div_div, mul_comm ((1 - |t|) ^ 2) 3]
    exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) _)
      (mul_pos (by norm_num) (sq_pos_of_pos (sub_pos.mpr ht)))
      (mul_le_mul_of_nonneg_right hqR (sq_nonneg _))
  have hTaylor' : |Real.rpow (1 + t) ((p : ℝ) / (q : ℝ)) - casselsTaylor p q m t| ≤ R / 3 := by
    apply hTaylor.trans
    change _ ≤ (|t| ^ (m + 1) / (1 - |t|) ^ 2) / 3
    rw [div_div, mul_comm ((1 - |t|) ^ 2) 3]
    exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) _)
      (mul_pos (by norm_num) (sq_pos_of_pos (sub_pos.mpr ht)))
      (mul_le_mul_of_nonneg_right hmR (sq_nonneg _))
  have htri := abs_sub_le (casselsF p q t)
    (Real.rpow (1 + t) ((p : ℝ) / (q : ℝ))) (casselsTaylor p q m t)
  change _ ≤ R
  linarith

#print axioms cassels_index_bounds
#print axioms cassels_remainder_of_bounds

end Catalan
