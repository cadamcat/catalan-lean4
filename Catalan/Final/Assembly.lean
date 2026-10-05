module

public import Catalan.Thaine.LiteralRungeContradiction
public import Catalan.Thaine.PrimeAssemblyReduction
public import Catalan.Thaine.NaturalClassificationReduction
public import Catalan.Classical.Reduction

/-!
# `Catalan.Final.Assembly`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan

theorem mihailescu_odd_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) : x ^ p ≠ y ^ q + 1 := by
  apply Thaine.odd_primes_no_solution_of_large ?_ p q hp hq hp2 hq2 x y hx hy
  intro r s hr hs hr7 hs7 hsr X Y hX hY
  have finalPrimeLeft : Fact r.Prime := ⟨hr⟩
  have finalPrimeRight : Fact s.Prime := ⟨hs⟩
  exact Thaine.literal_large_odd_primes_no_solution r s hr7 hs7 hsr X Y hX hY

theorem case_one (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (h1 : ¬ (q ≡ 1 [MOD p])) (h2 : ¬ (p ≡ 1 [MOD q])) (hd : DensityInput p q)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) : x ^ p ≠ y ^ q + 1 := by
  clear h1 h2 hd
  exact mihailescu_odd_primes p q hp hq hp2 hq2 x y hx hy

theorem prime_exponent_classification (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (x y : ℤ) (hx : 1 < x) (hy : 1 < y) (h : x ^ p = y ^ q + 1) :
    p = 2 ∧ q = 3 ∧ x = 3 ∧ y = 2 :=
  Thaine.prime_classification_of_odd_impossible mihailescu_odd_primes p q hp hq x y hx hy h

theorem catalan_int (x y : ℤ) (a b : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 1 < x) (hy : 1 < y)
    (h : x ^ a = y ^ b + 1) : a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 :=
  reduce_to_primes prime_exponent_classification x y a b ha hb hx hy h

theorem catalans_conjecture (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y)
    (heq : x ^ a - y ^ b = 1) : a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 :=
  Thaine.natural_classification_of_prime prime_exponent_classification a b x y ha hb hx hy heq

theorem q_lt_three_sq (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hp5 : 5 ≤ p)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) : q < 3 * (p - 1) ^ 2 :=
  False.elim (mihailescu_odd_primes p q hp hq hp2 hq2 x y hx hy h)

end Catalan
