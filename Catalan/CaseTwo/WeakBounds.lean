import Catalan.Counting.QuotientBall
import Catalan.CaseTwo.HyyroThreshold
import Catalan.Mihailescu.KernelCardinality

noncomputable section
namespace Catalan

private lemma card_upper_of_order
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero p]
    [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    (hp2 : p ≠ 2) (hp5 : 5 ≤ p) (hpq : p < q)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    (augBall p (CyclotomicField p ℚ) q x hp2 ((q : ℝ) / ((p : ℝ) - 1))).ncard ≤ q := by
  have hp := (Fact.out : p.Prime)
  have hq := (Fact.out : q.Prime)
  have h8 := hyyro_implies_h8_one p q hp hq hp5 hpq x y hx hy h
  have h8' : (|x| : ℝ) ≥
      max ((36 * 2 ^ (p - 1) / ((p - 1 : ℝ) ^ 2)) ^ (1 / (1 : ℝ)))
        (4 / Real.pi * (q : ℝ) / (p - 1) + 1) := by
    simpa only [mihThreshold, div_one, Real.rpow_one] using h8
  have hcard := card_aug_ball_le p (CyclotomicField p ℚ) q x hp2 (by omega)
    1 (by norm_num) (by norm_num) h8'
  norm_num [augBall] at hcard ⊢
  exact hcard

lemma q_lt_four_sq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hp11 : 11 ≤ p)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : q < 4 * (p - 1) ^ 2 := by
  by_cases hpq : p < q
  · have instFactP : Fact p.Prime := ⟨hp⟩
    have instFactQ : Fact q.Prime := ⟨hq⟩
    have instNeZeroP : NeZero p := ⟨hp.ne_zero⟩
    have instCyclo : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
      CyclotomicField.isCyclotomicExtension p ℚ
    have hcard := card_upper_of_order p q hp2 (by omega) hpq x y hx hy h
    exact q_lt_four_sq_of_aug_card_upper p (CyclotomicField p ℚ) q hp2 hq2 hp11
      x y hx hy h hcard
  · have hqp : q ≤ p := Nat.le_of_not_gt hpq
    have hr : 10 ≤ p - 1 := by omega
    have hsq0 : ∀ r : ℕ, 10 ≤ r → r + 1 ≤ r ^ 2 := by
      intro r hr
      nlinarith
    have hsq : p ≤ (p - 1) ^ 2 := by
      calc
        p = p - 1 + 1 := by omega
        _ ≤ (p - 1) ^ 2 := hsq0 (p - 1) hr
    omega

lemma q_lt_180_of_p_seven (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hp7 : p = 7)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : q < 180 := by
  by_cases hpq : p < q
  · have instFactP : Fact p.Prime := ⟨hp⟩
    have instFactQ : Fact q.Prime := ⟨hq⟩
    have instNeZeroP : NeZero p := ⟨hp.ne_zero⟩
    have instCyclo : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
      CyclotomicField.isCyclotomicExtension p ℚ
    have hcard := card_upper_of_order p q hp2 (by omega) hpq x y hx hy h
    exact q_lt_180_of_aug_card_upper p (CyclotomicField p ℚ) q hp2 hq2 hp7
      x y hx hy h hcard
  · have hqp : q ≤ p := Nat.le_of_not_gt hpq
    omega

lemma q_lt_144_of_p_five (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hp5 : p = 5)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : q < 144 := by
  by_cases hpq : p < q
  · have instFactP : Fact p.Prime := ⟨hp⟩
    have instFactQ : Fact q.Prime := ⟨hq⟩
    have instNeZeroP : NeZero p := ⟨hp.ne_zero⟩
    have instCyclo : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
      CyclotomicField.isCyclotomicExtension p ℚ
    have hcard := card_upper_of_order p q hp2 (by omega) hpq x y hx hy h
    exact q_lt_144_of_aug_card_upper p (CyclotomicField p ℚ) q hp2 hq2 hp5
      x y hx hy h hcard
  · have hqp : q ≤ p := Nat.le_of_not_gt hpq
    omega

end Catalan
