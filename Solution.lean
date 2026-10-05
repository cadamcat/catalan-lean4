module

public import Catalan

/-!
# Catalan formalization solutions

These declarations provide the proofs from the project for the four
statements in `Challenge`.
-/

namespace PalomarCatalan

/-- The Catalan natural-number theorem from the project. -/
theorem catalans_conjecture (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 := by
  exact Catalan.catalans_conjecture a b x y ha hb hx hy heq

/-- The integer Catalan theorem from the project. -/
theorem catalan_int (x y : ℤ) (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hx : 1 < x) (hy : 1 < y) (h : x ^ a = y ^ b + 1) :
    a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 := by
  exact Catalan.catalan_int x y a b ha hb hx hy h

/-- The signed integer Catalan theorem from the project. -/
theorem catalan_int_signed (x y : ℤ) (p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p - y ^ q = 1) :
    p = 2 ∧ q = 3 ∧ (x = 3 ∨ x = -3) ∧ y = 2 := by
  exact Catalan.catalan_int_signed x y p q hp hq hx hy h

/-- Mihăilescu's theorem for nonzero integer solutions and odd prime
exponents, from the project. -/
theorem mihailescu_odd_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ p ≠ y ^ q + 1 := by
  exact Catalan.mihailescu_odd_primes p q hp hq hp2 hq2 x y hx hy

end PalomarCatalan
