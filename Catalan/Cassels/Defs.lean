import Mathlib

open scoped BigOperators

namespace Catalan

/-- The geometric-sum factor in `x ^ n - 1`, used in Cassels' divisibility
argument. -/
def casselsCyclo (n : ℕ) (x : ℤ) : ℤ :=
  ∑ i ∈ Finset.range n, x ^ i

/-- The rational coefficient `binom(p/q, k)` in Cassels' expansion. -/
def casselsCoeff (p q k : ℕ) : ℚ :=
  (∏ i ∈ Finset.range k, ((p : ℚ) - (i : ℚ) * (q : ℚ))) /
    ((q : ℚ) ^ k * (k.factorial : ℚ))

/-- The truncation index `floor(p/q) + 1`. -/
def casselsIndex (p q : ℕ) : ℕ := p / q + 1

/-- The denominator exponent `k + v_q(k!)` used in the identity proved
in `Catalan.Cassels.Denominator`. -/
def casselsDenExp (q k : ℕ) : ℕ := k + padicValNat q k.factorial

/-- The integer denominator-clearing scale used by the Cassels error term. -/
def casselsScale (p q : ℕ) : ℤ :=
  (q : ℤ) ^ casselsDenExp q (casselsIndex p q)

/-- Cassels' real function `((1+t)^p - t^p)^(1/q)`, with Real.rpow. -/
noncomputable def casselsF (p q : ℕ) (t : ℝ) : ℝ :=
  Real.rpow ((1 + t) ^ p - t ^ p) (1 / (q : ℝ))

/-- The finite Taylor polynomial in Cassels' expansion. -/
noncomputable def casselsTaylor (p q m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), (casselsCoeff p q k : ℝ) * t ^ k

/-- The rational error used in the final Cassels contradiction. -/
def casselsError (p q : ℕ) (a y : ℤ) : ℚ :=
  (a : ℚ) ^ (casselsIndex p q * q - p) * (y : ℚ) -
    ∑ k ∈ Finset.range (casselsIndex p q + 1),
      casselsCoeff p q k * (a : ℚ) ^ (q * (casselsIndex p q - k))

end Catalan
