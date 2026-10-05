module

public import Mathlib

/-!
# Catalan's conjecture and related Diophantine equations

This challenge states four theorems proved by the Catalan formalization. The
natural-number statement of Catalan's conjecture follows
[Formal Conjectures' Wikipedia statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Catalan.lean).
-/

@[expose] public section

namespace PalomarCatalan

/-- For natural exponents greater than one and positive natural bases, the
only solution of `x ^ a - y ^ b = 1` is `a = 2`, `b = 3`, `x = 3`, and
`y = 2`. -/
theorem catalans_conjecture (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 := by
  sorry

/-- For integers `x,y > 1` and natural exponents `a,b > 1`, the equation
`x ^ a = y ^ b + 1` has only the solution `a = 2`, `b = 3`, `x = 3`,
`y = 2`. -/
theorem catalan_int (x y : ℤ) (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hx : 1 < x) (hy : 1 < y) (h : x ^ a = y ^ b + 1) :
    a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 := by
  sorry

/-- If nonzero integers satisfy `x ^ p - y ^ q = 1` for exponents
`p,q ≥ 2`, then `p = 2`, `q = 3`, `y = 2`, and `x` is `3` or `-3`. -/
theorem catalan_int_signed (x y : ℤ) (p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p - y ^ q = 1) :
    p = 2 ∧ q = 3 ∧ (x = 3 ∨ x = -3) ∧ y = 2 := by
  sorry

/-- For odd primes `p,q`, no nonzero integers `x,y` satisfy
`x ^ p = y ^ q + 1`. -/
theorem mihailescu_odd_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ p ≠ y ^ q + 1 := by
  sorry

end PalomarCatalan
