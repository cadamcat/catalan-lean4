import Catalan.Counting.Recurrence
import Catalan.Counting.PolynomialRecurrence

set_option autoImplicit false
open scoped BigOperators
namespace Catalan

theorem S_formula (n r : ℕ) : S n r = ∑ k ∈ Finset.range (n + 1), 2 ^ k * n.choose k * r.choose k := by
  change S n r = LatticeCount.countPolynomial n r
  induction n generalizing r with
  | zero => rw [LatticeCount.S_zero_dim, LatticeCount.countPolynomial_zero_dim]
  | succ n ih =>
      rw [LatticeCount.S_succ_dim, LatticeCount.countPolynomial_succ_dim]
      simp_rw [ih]

end Catalan
