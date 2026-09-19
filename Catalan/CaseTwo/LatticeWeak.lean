import Catalan.Counting

set_option autoImplicit false
namespace Catalan

lemma q_lt_four_sq_of_lattice_upper
    (p q : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p)
    (hcount : S ((p - 1) / 2) (q / (p - 1) ^ 2) ≤ q) :
    q < 4 * (p - 1) ^ 2 := by
  by_contra hq
  have hqge : 4 * (p - 1) ^ 2 ≤ q := by omega
  have hDpos : 0 < (p - 1) ^ 2 := pow_pos (by omega : 0 < p - 1) 2
  have hr : 4 ≤ q / (p - 1) ^ 2 := (Nat.le_div_iff_mul_le hDpos).mpr hqge
  have hn : 5 ≤ (p - 1) / 2 := by omega
  have hodd := hp.mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
  have hpEq : p - 1 = 2 * ((p - 1) / 2) := by omega
  have hD : (p - 1) ^ 2 = 4 * ((p - 1) / 2) ^ 2 := by
    conv_lhs => rw [hpEq]
    ring
  have hs := S_gt' ((p - 1) / 2) (q / (p - 1) ^ 2) hn hr
  rw [← hD] at hs
  have hqdiv : q < (p - 1) ^ 2 * (q / (p - 1) ^ 2 + 1) := by
    have hmod := Nat.mod_lt q hDpos
    have he := Nat.mod_add_div q ((p - 1) ^ 2)
    nlinarith only [hmod, he]
  omega

lemma q_lt_180_of_lattice_upper (q : ℕ) (hcount : S 3 (q / 36) ≤ q) : q < 180 := by
  by_contra hq
  have hr : 5 ≤ q / 36 := by omega
  have hs := S_gt_three (q / 36) hr
  norm_num at hs
  have hqdiv : q < 36 * (q / 36 + 1) := by omega
  omega

lemma q_lt_144_of_lattice_upper (q : ℕ) (hcount : S 2 (q / 16) ≤ q) : q < 144 := by
  by_contra hq
  have hr : 9 ≤ q / 16 := by omega
  have hs := S_gt_two (q / 16) hr
  norm_num at hs
  have hqdiv : q < 16 * (q / 16 + 1) := by omega
  omega

end Catalan
