import Catalan.CaseTwo.WeakBounds
import Catalan.Classical.SmallConductors
import Catalan.CaseTwo.WeakBoundExclusion
import Catalan.Wieferich.DoubleWieferich

set_option autoImplicit false
namespace Catalan

private lemma case_two_left (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : ¬ (q ≡ 1 [MOD p]) := by
  by_cases hp3 : p = 3
  · subst p
    exact (nagell_p_three q hq hq2 x y hx hy h).elim
  obtain ⟨hw1, hw2⟩ := double_wieferich p q hp hq hp2 hq2 x y hx hy h
  by_cases hp5 : p = 5
  · have hb := q_lt_144_of_p_five p q hp hq hp2 hq2 hp5 x y hx hy h
    subst p
    exact CaseTwo.not_modEq_one_of_five_weak_bound q hq hb
      (by simpa using hw1) (by simpa using hw2)
  by_cases hp7 : p = 7
  · have hb := q_lt_180_of_p_seven p q hp hq hp2 hq2 hp7 x y hx hy h
    subst p
    exact CaseTwo.not_modEq_one_of_seven_weak_bound q hq hb (by simpa using hw1)
  have hp11 : 11 ≤ p := by
    by_contra! hlt
    interval_cases p <;> norm_num at *
  exact CaseTwo.not_modEq_one_of_large_weak_bound p q hp hq (by omega)
    (q_lt_four_sq p q hp hq hp2 hq2 hp11 x y hx hy h) hw1

theorem solution_symm (p q : ℕ) (hp : Odd p) (hq : Odd q) (x y : ℤ) (h : x ^ p = y ^ q + 1) :
    (-y) ^ q = (-x) ^ p + 1 := by
  exact cassels_solution_symm p q hp hq x y h

theorem case_two (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    ¬ (q ≡ 1 [MOD p]) ∧ ¬ (p ≡ 1 [MOD q]) := by
  refine ⟨case_two_left p q hp hq hp2 hq2 x y hx hy h, ?_⟩
  exact case_two_left q p hq hp hq2 hp2 (-y) (-x)
    (neg_ne_zero.mpr hy) (neg_ne_zero.mpr hx)
    (solution_symm p q (hp.odd_of_ne_two hp2) (hq.odd_of_ne_two hq2) x y h)

end Catalan
