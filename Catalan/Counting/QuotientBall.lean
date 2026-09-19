import Catalan.Counting.CoefficientBall
import Catalan.CaseTwo.RadiusArithmetic
import Catalan.CaseTwo.LatticeWeak

noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime]

lemma S_le_card_augBall_quotient
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    S ((p - 1) / 2) (q / (p - 1) ^ 2) ≤
      (augBall p K q x hp2 ((q : ℝ) / ((p : ℝ) - 1))).ncard := by
  refine (S_le_card_augBall p K q hp2 hq2 x y hx hy h _).trans ?_
  apply Set.ncard_le_ncard ?_ (finite_aug_ball p K q x hp2 _)
  intro T hT
  exact ⟨hT.1, hT.2.1, hT.2.2.trans
    (quotient_radius_le p q (Fact.out : p.Prime).one_lt)⟩

lemma q_lt_four_sq_of_aug_card_upper
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hp11 : 11 ≤ p)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (hcard : (augBall p K q x hp2 ((q : ℝ) / ((p : ℝ) - 1))).ncard ≤ q) :
    q < 4 * (p - 1) ^ 2 := by
  exact q_lt_four_sq_of_lattice_upper p q Fact.out hp11
    ((S_le_card_augBall_quotient p K q hp2 hq2 x y hx hy h).trans hcard)

lemma q_lt_180_of_aug_card_upper
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hp7 : p = 7)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (hcard : (augBall p K q x hp2 ((q : ℝ) / ((p : ℝ) - 1))).ncard ≤ q) :
    q < 180 := by
  have hs := (S_le_card_augBall_quotient p K q hp2 hq2 x y hx hy h).trans hcard
  rw [hp7] at hs
  norm_num at hs
  exact q_lt_180_of_lattice_upper q hs

lemma q_lt_144_of_aug_card_upper
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hp5 : p = 5)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (hcard : (augBall p K q x hp2 ((q : ℝ) / ((p : ℝ) - 1))).ncard ≤ q) :
    q < 144 := by
  have hs := (S_le_card_augBall_quotient p K q hp2 hq2 x y hx hy h).trans hcard
  rw [hp5] at hs
  norm_num at hs
  exact q_lt_144_of_lattice_upper q hs

end Catalan
