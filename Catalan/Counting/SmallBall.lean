module

public import Catalan.Mihailescu.Ideal

/-!
# `Catalan.Counting.SmallBall`

Part of the Catalan formalization.
-/

@[expose] public section

noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime]

lemma augBall_eq_singleton_of_lt_two
    (x : ℤ) (hp2 : p ≠ 2) (r : ℝ) (hr0 : 0 ≤ r) (hr2 : r < 2) :
    augBall p K q x hp2 r = {0} := by
  ext Θ
  constructor
  · intro hΘ
    exact Set.mem_singleton_iff.mpr
      (aug_size_lt_two p K Θ hΘ.2.1 (hΘ.2.2.trans_lt hr2))
  · intro hΘ
    have hΘ0 : Θ = 0 := Set.mem_singleton_iff.mp hΘ
    subst Θ
    exact ⟨(mihIdeal p K q x hp2).zero_mem, weight_zero p K,
      by simpa only [size_zero, Int.cast_zero] using hr0⟩

lemma card_aug_ball_le_of_q_eq_two
    (x : ℤ) (hp2 : p ≠ 2) (hq : q = 2)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (augBall p K q x hp2 ((2 - ε) * (q : ℝ) / ((p : ℝ) - 1))).ncard ≤ q := by
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hr0 : 0 ≤ (2 - ε) * (q : ℝ) / ((p : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg q)) (by linarith)
  have hr2 : (2 - ε) * (q : ℝ) / ((p : ℝ) - 1) < 2 := by
    apply (div_lt_iff₀ (show 0 < (p : ℝ) - 1 by linarith)).mpr
    rw [hq]
    norm_num
    nlinarith
  rw [augBall_eq_singleton_of_lt_two p K q x hp2 _ hr0 hr2, Set.ncard_singleton, hq]
  norm_num



end Catalan
