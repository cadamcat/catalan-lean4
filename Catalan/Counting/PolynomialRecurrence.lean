module

public import Catalan.Counting.Defs

/-!
# `Catalan.Counting.PolynomialRecurrence`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
namespace Catalan.LatticeCount

lemma countPolynomial_zero_dim (r : ℕ) : countPolynomial 0 r = 1 := by
  simp [countPolynomial]

lemma countPolynomial_succ_dim (n r : ℕ) :
    countPolynomial (n + 1) r =
      countPolynomial n r + 2 * ∑ t ∈ Finset.range r, countPolynomial n t := by
  classical
  have hockey : ∀ (s k : ℕ),
      ∑ t ∈ Finset.range s, t.choose k = s.choose (k + 1) := by
    intro s k
    induction s with
    | zero => simp
    | succ s ih =>
        rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ']
        ac_rfl
  simp only [countPolynomial]
  rw [show n + 1 + 1 = (n + 1) + 1 by rfl, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, pow_zero, mul_one]
  have hpascal : ∀ k : ℕ,
      2 ^ (k + 1) * (n + 1).choose (k + 1) * r.choose (k + 1) =
        2 * (2 ^ k * n.choose k * r.choose (k + 1)) +
          2 ^ (k + 1) * n.choose (k + 1) * r.choose (k + 1) := by
    intro k
    rw [Nat.choose_succ_succ']
    ring
  have hshift :
      (∑ k ∈ Finset.range (n + 1),
        2 ^ (k + 1) * (n + 1).choose (k + 1) * r.choose (k + 1)) =
        2 * (∑ k ∈ Finset.range (n + 1),
          2 ^ k * n.choose k * r.choose (k + 1)) +
          ∑ k ∈ Finset.range (n + 1),
            2 ^ (k + 1) * n.choose (k + 1) * r.choose (k + 1) := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          (2 * (2 ^ k * n.choose k * r.choose (k + 1)) +
            2 ^ (k + 1) * n.choose (k + 1) * r.choose (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hpascal k
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hbase :
      (∑ k ∈ Finset.range (n + 1), 2 ^ k * n.choose k * r.choose k) =
        (∑ k ∈ Finset.range (n + 1),
          2 ^ (k + 1) * n.choose (k + 1) * r.choose (k + 1)) + 1 := by
    calc
      _ = (∑ k ∈ Finset.range n,
          2 ^ (k + 1) * n.choose (k + 1) * r.choose (k + 1)) + 1 := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.choose_zero_right, mul_one]
      _ = _ := by
        rw [Finset.sum_range_succ]
        simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), mul_zero, zero_mul,
          add_zero]
  have hswap :
      (∑ t ∈ Finset.range r, ∑ k ∈ Finset.range (n + 1),
        2 ^ k * n.choose k * t.choose k) =
        ∑ k ∈ Finset.range (n + 1),
          2 ^ k * n.choose k * (∑ t ∈ Finset.range r, t.choose k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
  calc
    (∑ k ∈ Finset.range (n + 1),
        2 ^ (k + 1) * (n + 1).choose (k + 1) * r.choose (k + 1)) + 1 =
        (∑ k ∈ Finset.range (n + 1),
          2 ^ (k + 1) * n.choose (k + 1) * r.choose (k + 1)) +
          1 + 2 * (∑ k ∈ Finset.range (n + 1),
            2 ^ k * n.choose k * r.choose (k + 1)) := by
      rw [hshift]
      ring
    _ = (∑ k ∈ Finset.range (n + 1), 2 ^ k * n.choose k * r.choose k) +
          2 * (∑ t ∈ Finset.range r, ∑ k ∈ Finset.range (n + 1),
            2 ^ k * n.choose k * t.choose k) := by
      rw [hbase]
      rw [hswap]
      simp_rw [hockey]

end Catalan.LatticeCount
