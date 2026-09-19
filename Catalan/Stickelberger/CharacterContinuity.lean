import Catalan.Stickelberger.CharacterBoundary

open Filter
open scoped BigOperators Topology
namespace Catalan

lemma tendsto_expZeta_one_partial_sums_of_tail_bound
    (htail : ∀ (z : ℂ), ‖z‖ = 1 → z ≠ 1 → ∀ (s : ℝ), 1 ≤ s →
      ∀ (M N : ℕ), 1 ≤ M → M ≤ N →
        ‖∑ n ∈ Finset.Ico M N, z ^ n / (n : ℂ) ^ (s : ℂ)‖ ≤
          4 / ((M : ℝ) * ‖1 - z‖))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (n : ℂ)) / (n : ℂ))
      atTop (𝓝 (HurwitzZeta.expZeta (t : UnitAddCircle) 1))
 := by
  let z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
  have hphase : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hz : ‖z‖ = 1 := by
    dsimp only [z]
    rw [hphase]
    exact Complex.norm_exp_ofReal_mul_I _
  have hz1 : z ≠ 1 := by
    intro he
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
    have hi := congrArg Complex.im hm
    norm_num [Complex.mul_im, Complex.mul_re] at hi
    have hmt : (m : ℝ) = t := by nlinarith [Real.pi_pos]
    have hm0 : (0 : ℤ) < m := by exact_mod_cast (show (0 : ℝ) < m by rw [hmt]; exact ht.1)
    have hm1 : m < (1 : ℤ) := by exact_mod_cast (show (m : ℝ) < 1 by rw [hmt]; exact ht.2)
    omega
  have htne : (t : UnitAddCircle) ≠ 0 := by
    intro he
    exact ht.1.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico
      (p := (1 : ℝ)) ⟨ht.1.le, ht.2⟩).mp he)
  have hpow (n : ℕ) : z ^ n =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (n : ℂ)) := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  let F (M : ℕ) (s : ℝ) : ℂ :=
    ∑ n ∈ Finset.range M, z ^ n / (n : ℂ) ^ (s : ℂ)
  let E (s : ℝ) : ℂ := HurwitzZeta.expZeta (t : UnitAddCircle) (s : ℂ)
  have hsum (s : ℝ) (hs : 1 < s) :
      HasSum (fun n : ℕ => z ^ n / (n : ℂ) ^ (s : ℂ)) (E s) := by
    have hh := HurwitzZeta.hasSum_expZeta_of_one_lt_re t (s := (s : ℂ))
      (by simpa only [Complex.ofReal_re] using hs)
    simpa only [← hpow] using hh
  have hbound (s : ℝ) (hs : 1 < s) (M : ℕ) (hM : 1 ≤ M) :
      ‖E s - F M s‖ ≤ 4 / ((M : ℝ) * ‖1 - z‖) := by
    have hlim : Tendsto (fun N : ℕ => ‖F N s - F M s‖) atTop (𝓝 ‖E s - F M s‖) :=
      ((hsum s hs).tendsto_sum_nat.sub_const (F M s)).norm
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop M] with N hMN
    dsimp only [F]
    rw [← Finset.sum_Ico_eq_sub _ hMN]
    exact htail z hz hz1 s hs.le M N hM hMN
  let s (j : ℕ) : ℝ := 1 + 1 / ((j : ℝ) + 1)
  have hs (j : ℕ) : 1 < s j := by
    dsimp only [s]
    exact lt_add_of_pos_right 1 (by positivity)
  have hs0 (j : ℕ) : (s j : ℂ) ≠ 0 := by
    exact_mod_cast (show s j ≠ 0 by have := hs j; linarith)
  have hsT : Tendsto s atTop (𝓝 (1 : ℝ)) := by
    have hh := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
    simpa only [add_zero] using hh
  have hsC : Tendsto (fun j : ℕ => (s j : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one, Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hsT
  have hET : Tendsto (fun j : ℕ => E (s j)) atTop
      (𝓝 (HurwitzZeta.expZeta (t : UnitAddCircle) 1)) :=
    (HurwitzZeta.differentiable_expZeta_of_ne_zero htne 1).continuousAt.tendsto.comp hsC
  have hFT (M : ℕ) : Tendsto (fun j : ℕ => F M (s j)) atTop
      (𝓝 (∑ n ∈ Finset.range M, z ^ n / (n : ℂ))) := by
    apply tendsto_finsetSum
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      have he : (fun j : ℕ => z ^ 0 / (0 : ℂ) ^ (s j : ℂ)) = fun _ => (0 : ℂ) := by
        funext j
        rw [Complex.zero_cpow (hs0 j), div_zero]
      simp only [Nat.cast_zero]
      rw [he]
      simpa only [div_zero] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      have hpT : Tendsto (fun j : ℕ => (n : ℂ) ^ (s j : ℂ)) atTop (𝓝 (n : ℂ)) := by
        simpa only [Complex.cpow_one, Function.comp_def] using
          (continuousAt_const_cpow (a := (n : ℂ)) (b := 1) hnC).tendsto.comp hsC
      exact tendsto_const_nhds.div hpT hnC
  have hbound1 (M : ℕ) (hM : 1 ≤ M) :
      ‖HurwitzZeta.expZeta (t : UnitAddCircle) 1 -
        ∑ n ∈ Finset.range M, z ^ n / (n : ℂ)‖ ≤ 4 / ((M : ℝ) * ‖1 - z‖) := by
    exact le_of_tendsto' ((hET.sub (hFT M)).norm) (fun j => hbound (s j) (hs j) M hM)
  have hCT : Tendsto (fun M : ℕ => 4 / ((M : ℝ) * ‖1 - z‖)) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun M : ℕ => 1 / (M : ℝ)) atTop (𝓝 (0 : ℝ))).const_mul (4 / ‖1 - z‖)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
  have hlimit : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ n / (n : ℂ)) atTop
      (𝓝 (HurwitzZeta.expZeta (t : UnitAddCircle) 1)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hCT).2 ε hε)
    refine ⟨max M 1, fun N hN => ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact (hbound1 N ((le_max_right M 1).trans hN)).trans_lt
      (hM N ((le_max_left M 1).trans hN))
  simpa only [hpow] using hlimit

end Catalan
