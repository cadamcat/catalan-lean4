module

public import Mathlib

/-!
# `Catalan.Stickelberger.DirichletTail`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
namespace Catalan

lemma unit_circle_dirichlet_tail_bound
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (s : ℝ) (hs : 1 ≤ s)
    (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) :
    ‖∑ n ∈ Finset.Ico M N, z ^ n / (n : ℂ) ^ (s : ℂ)‖ ≤
      4 / ((M : ℝ) * ‖1 - z‖) := by
  classical
  by_cases hMNeq : M = N
  · subst N
    simp
    positivity
  have hMNlt : M < N := lt_of_le_of_ne hMN hMNeq
  have hden : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  let f : ℕ → ℝ := fun n => (n : ℝ) ^ (-s)
  let g : ℕ → ℂ := fun n => z ^ n
  have hterm (n : ℕ) (hn : 1 ≤ n) :
      z ^ n / (n : ℂ) ^ (s : ℂ) = (↑(f n) : ℂ) • g n := by
    have hnR : 0 ≤ (n : ℝ) := by positivity
    change z ^ n / (((n : ℝ) : ℂ) ^ (s : ℂ)) =
      (↑((n : ℝ) ^ (-s)) : ℂ) • z ^ n
    rw [← Complex.ofReal_cpow hnR, div_eq_mul_inv, ← Complex.ofReal_inv,
      ← Real.rpow_neg hnR]
    simp only [smul_eq_mul]
    ring
  have hsum_term :
      (∑ n ∈ Finset.Ico M N, z ^ n / (n : ℂ) ^ (s : ℂ)) =
        ∑ n ∈ Finset.Ico M N, f n • g n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hterm n (hM.trans (Finset.mem_Ico.mp hn).1)
  have hprefix (j : ℕ) :
      ‖∑ n ∈ Finset.range j, g n‖ ≤ 2 / ‖1 - z‖ := by
    have hgeom : (1 - z) * (∑ n ∈ Finset.range j, g n) = 1 - z ^ j := by
      calc
        (1 - z) * (∑ n ∈ Finset.range j, g n) =
            -((∑ n ∈ Finset.range j, g n) * (z - 1)) := by ring
        _ = -(z ^ j - 1) := by rw [geom_sum_mul]
        _ = 1 - z ^ j := by ring
    have hnum : ‖1 - z ^ j‖ ≤ 2 := by
      calc
        ‖1 - z ^ j‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ j‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_one, norm_pow, hz]; norm_num
    have hprod : ‖1 - z‖ * ‖∑ n ∈ Finset.range j, g n‖ = ‖1 - z ^ j‖ := by
      rw [← norm_mul, hgeom]
    apply (le_div_iff₀ hden).2
    nlinarith [hprod, hnum]
  have hf_le (n : ℕ) (hn : 1 ≤ n) : f (n + 1) ≤ f n := by
    dsimp [f]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · exact_mod_cast (Nat.le_succ n)
    · linarith
  have hvar :
      (∑ i ∈ Finset.Ico M (N - 1), (f i - f (i + 1))) = f M - f (N - 1) := by
    rw [Finset.sum_Ico_eq_sub _ (by omega)]
    rw [Finset.sum_range_sub' f, Finset.sum_range_sub' f]
    ring
  have hvar_abs :
      (∑ i ∈ Finset.Ico M (N - 1), |f (i + 1) - f i|) = f M - f (N - 1) := by
    rw [← hvar]
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (hf_le i
        (hM.trans (Finset.mem_Ico.mp hi).1))
  have hf_nonneg (n : ℕ) : 0 ≤ f n := by
    dsimp [f]
    exact Real.rpow_nonneg (by positivity) _
  have hvar_norm :
      (∑ i ∈ Finset.Ico M (N - 1),
        ‖(f (i + 1) - f i) • (∑ n ∈ Finset.range (i + 1), g n)‖) ≤
        (2 / ‖1 - z‖) * (f M - f (N - 1)) := by
    calc
      _ = ∑ i ∈ Finset.Ico M (N - 1),
          |f (i + 1) - f i| * ‖∑ n ∈ Finset.range (i + 1), g n‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i ∈ Finset.Ico M (N - 1),
          |f (i + 1) - f i| * (2 / ‖1 - z‖) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hprefix (i + 1)) (abs_nonneg _)
      _ = (2 / ‖1 - z‖) *
          (∑ i ∈ Finset.Ico M (N - 1), |f (i + 1) - f i|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (2 / ‖1 - z‖) * (f M - f (N - 1)) := by rw [hvar_abs]
  have hboundN : ‖f (N - 1) • (∑ n ∈ Finset.range N, g n)‖ ≤
      (2 / ‖1 - z‖) * f (N - 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf_nonneg _)]
    calc
      f (N - 1) * ‖∑ n ∈ Finset.range N, g n‖ ≤
          f (N - 1) * (2 / ‖1 - z‖) :=
        mul_le_mul_of_nonneg_left (hprefix N) (hf_nonneg _)
      _ = (2 / ‖1 - z‖) * f (N - 1) := by ring
  have hboundM : ‖f M • (∑ n ∈ Finset.range M, g n)‖ ≤
      (2 / ‖1 - z‖) * f M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf_nonneg _)]
    calc
      f M * ‖∑ n ∈ Finset.range M, g n‖ ≤
          f M * (2 / ‖1 - z‖) :=
        mul_le_mul_of_nonneg_left (hprefix M) (hf_nonneg _)
      _ = (2 / ‖1 - z‖) * f M := by ring
  have hnorm :
      ‖∑ n ∈ Finset.Ico M N, f n • g n‖ ≤
        (2 / ‖1 - z‖) * f (N - 1) +
          (2 / ‖1 - z‖) * f M +
          (2 / ‖1 - z‖) * (f M - f (N - 1)) := by
    rw [Finset.sum_Ico_by_parts f g hMNlt]
    calc
      ‖f (N - 1) • (∑ n ∈ Finset.range N, g n) -
          f M • (∑ n ∈ Finset.range M, g n) -
          ∑ i ∈ Finset.Ico M (N - 1),
            (f (i + 1) - f i) • (∑ n ∈ Finset.range (i + 1), g n)‖ ≤
        ‖f (N - 1) • (∑ n ∈ Finset.range N, g n) -
          f M • (∑ n ∈ Finset.range M, g n)‖ +
          ‖∑ i ∈ Finset.Ico M (N - 1),
            (f (i + 1) - f i) • (∑ n ∈ Finset.range (i + 1), g n)‖ :=
        norm_sub_le _ _
      _ ≤ (‖f (N - 1) • (∑ n ∈ Finset.range N, g n)‖ +
          ‖f M • (∑ n ∈ Finset.range M, g n)‖) +
          ‖∑ i ∈ Finset.Ico M (N - 1),
            (f (i + 1) - f i) • (∑ n ∈ Finset.range (i + 1), g n)‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ (2 / ‖1 - z‖) * f (N - 1) +
          (2 / ‖1 - z‖) * f M +
          (2 / ‖1 - z‖) * (f M - f (N - 1)) := by
        exact add_le_add (add_le_add hboundN hboundM)
          ((norm_sum_le _ _).trans hvar_norm)
  have hfM : f M ≤ 1 / (M : ℝ) := by
    dsimp [f]
    have hbase : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hexp : -s ≤ (-1 : ℝ) := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hbase hexp
    simpa only [Real.rpow_neg (by positivity : 0 ≤ (M : ℝ)), Real.rpow_one, one_div] using hpow
  rw [hsum_term]
  calc
    ‖∑ n ∈ Finset.Ico M N, f n • g n‖ ≤
        (2 / ‖1 - z‖) * f (N - 1) +
          (2 / ‖1 - z‖) * f M +
          (2 / ‖1 - z‖) * (f M - f (N - 1)) := hnorm
    _ = 2 * (2 / ‖1 - z‖) * f M := by ring
    _ ≤ 2 * (2 / ‖1 - z‖) * (1 / (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hfM (by positivity)
    _ = 4 / ((M : ℝ) * ‖1 - z‖) := by field_simp; ring

end Catalan
