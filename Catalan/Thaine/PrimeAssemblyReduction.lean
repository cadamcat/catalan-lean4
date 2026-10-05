module

public import Catalan.Classical.SmallConductors
public import Catalan.Classical.KoChao
public import Catalan.Classical.Lebesgue
public import Catalan.CaseTwo.Assembly

/-!
# `Catalan.Thaine.PrimeAssemblyReduction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan.Thaine

lemma odd_primes_no_solution_of_large
    (hlarge : ∀ (p q : ℕ), p.Prime → q.Prime → 7 ≤ p → 7 ≤ q → q < p →
      ∀ (x y : ℤ), x ≠ 0 → y ≠ 0 → x ^ p ≠ y ^ q + 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ p ≠ y ^ q + 1 := by
  intro h
  by_cases hpq : p = q
  · subst q
    exact cassels_equal_exponents_false p hp hp2 x y hx hy h
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hswap := solution_symm p q hpodd hqodd x y h
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · by_cases hp7 : 7 ≤ p
    · exact hlarge q p hq hp (by omega) hp7 hpq (-y) (-x)
        (neg_ne_zero.mpr hy) (neg_ne_zero.mpr hx) hswap
    · have hsmall : p = 3 ∨ p = 5 := by
        have hpmin := hp.two_le
        have hpmod := Nat.odd_iff.mp hpodd
        omega
      apply small_odd_prime_no_solution p q hp hq hp2 hq2 hpq _ x y hx hy h
      exact hsmall.imp_right Or.inl
  · by_cases hq7 : 7 ≤ q
    · exact hlarge p q hp hq (by omega) hq7 hqp x y hx hy h
    · have hsmall : q = 3 ∨ q = 5 := by
        have hqmin := hq.two_le
        have hqmod := Nat.odd_iff.mp hqodd
        omega
      apply small_odd_prime_no_solution q p hq hp hq2 hp2 hqp _ (-y) (-x)
        (neg_ne_zero.mpr hy) (neg_ne_zero.mpr hx) hswap
      exact hsmall.imp_right Or.inl

lemma prime_classification_of_odd_impossible
    (hodd : ∀ (p q : ℕ), p.Prime → q.Prime → p ≠ 2 → q ≠ 2 →
      ∀ (x y : ℤ), x ≠ 0 → y ≠ 0 → x ^ p ≠ y ^ q + 1)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (x y : ℤ) (hx : 1 < x) (hy : 1 < y) (h : x ^ p = y ^ q + 1) :
    p = 2 ∧ q = 3 ∧ x = 3 ∧ y = 2 := by
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  by_cases hp2 : p = 2
  · subst p
    by_cases hq2 : q = 2
    · subst q
      have hyzero := (Euler.sq_sub_sq_eq_one x y (by omega)).2
      omega
    · obtain ⟨hxs, hy2, hq3⟩ := koChao_p_two q hq hq2 x y hx0 hy0 h
      rcases hxs with hx3 | hxm3
      · exact ⟨rfl, hq3, hx3, hy2⟩
      · omega
  · by_cases hq2 : q = 2
    · subst q
      exact False.elim (lebesgue_q_two p hp hp2 x y hx0 hy0 h)
    · exact False.elim (hodd p q hp hq hp2 hq2 x y hx0 hy0 h)

end Catalan.Thaine
