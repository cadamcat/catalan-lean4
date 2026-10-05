module

public import Catalan.Classical.Reduction

/-!
# `Catalan.Thaine.NaturalClassificationReduction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan.Thaine

lemma natural_classification_of_prime
    (hclass : ∀ p q : ℕ, p.Prime → q.Prime → ∀ x y : ℤ, 1 < x → 1 < y →
      x ^ p = y ^ q + 1 → p = 2 ∧ q = 3 ∧ x = 3 ∧ y = 2)
    (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y)
    (heq : x ^ a - y ^ b = 1) :
    a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 := by
  have hadd : x ^ a = y ^ b + 1 := by omega
  have hxgt : 1 < x := by
    by_contra hnot
    have hxone : x = 1 := by omega
    subst x
    have hpow : 0 < y ^ b := pow_pos hy b
    simp at hadd
    omega
  have hygt : 1 < y := by
    by_contra hnot
    have hyone : y = 1 := by omega
    subst y
    have hpow : x ^ a = 2 := by simpa using hadd
    obtain ⟨_, haone⟩ := Nat.prime_two.pow_eq_iff.mp hpow
    omega
  have hxInt : (1 : ℤ) < (x : ℤ) := by exact_mod_cast hxgt
  have hyInt : (1 : ℤ) < (y : ℤ) := by exact_mod_cast hygt
  have haddInt : (x : ℤ) ^ a = (y : ℤ) ^ b + 1 := by exact_mod_cast hadd
  obtain ⟨ha2, hb3, hx3, hy2⟩ :=
    Catalan.reduce_to_primes hclass (x : ℤ) (y : ℤ) a b ha hb hxInt hyInt haddInt
  have hxNat : x = 3 := by exact_mod_cast hx3
  have hyNat : y = 2 := by exact_mod_cast hy2
  exact ⟨ha2, hb3, hxNat, hyNat⟩

end Catalan.Thaine
