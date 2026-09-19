import Catalan.Counting.Formula
import Catalan.Counting.Bounds
import Catalan.Counting.SmallDimensions

set_option autoImplicit false
namespace Catalan

theorem S_gt (n r : ℕ) (hn : 11 ≤ n) (hr : 3 ≤ r) : 4 * n ^ 2 * (r + 1) < S n r := by
  rw [S_formula]
  exact LatticeCount.countPolynomial_gt n r hn hr

theorem S_gt' (n r : ℕ) (hn : 5 ≤ n) (hr : 4 ≤ r) : 4 * n ^ 2 * (r + 1) < S n r := by
  rw [S_formula]
  exact LatticeCount.countPolynomial_gt' n r hn hr

theorem S_gt_three (r : ℕ) (hr : 5 ≤ r) : 4 * 3 ^ 2 * (r + 1) < S 3 r := by
  rw [S_formula]
  exact LatticeCount.countPolynomial_gt_three r hr

theorem S_gt_two (r : ℕ) (hr : 9 ≤ r) : 4 * 2 ^ 2 * (r + 1) < S 2 r := by
  rw [S_formula]
  exact LatticeCount.countPolynomial_gt_two r hr

end Catalan
