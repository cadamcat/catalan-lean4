import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Complex.AbelLimit

open scoped BigOperators Topology
open Filter

namespace Catalan

lemma hurwitzZeta_zero_eq_sinZeta_one_div_pi
    (a : UnitAddCircle) (ha : a ≠ 0) :
    HurwitzZeta.hurwitzZeta a 0 = HurwitzZeta.sinZeta a 1 / (Real.pi : ℂ) := by
  have hone : ∀ n : ℕ, (1 : ℂ) ≠ -n := by
    intro n h
    have hr := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hfe := HurwitzZeta.hurwitzZetaOdd_one_sub a hone
  simp only [sub_self, Complex.Gamma_one, mul_one, Complex.sin_pi_div_two] at hfe
  rw [HurwitzZeta.hurwitzZeta, HurwitzZeta.hurwitzZetaEven_apply_zero, if_neg ha, zero_add,
    hfe, Complex.cpow_neg_one]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

lemma hurwitzZeta_zero_eq_sine_value_of_mem_Ioo
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HurwitzZeta.hurwitzZeta (t : UnitAddCircle) 0 =
      HurwitzZeta.sinZeta (t : UnitAddCircle) 1 / (Real.pi : ℂ) := by
  apply hurwitzZeta_zero_eq_sinZeta_one_div_pi
  intro h
  have hz := (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ)) ⟨ht.1.le, ht.2⟩).mp h
  exact ht.1.ne' hz

lemma cauchySeq_unit_circle_log_partial_sums
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n : ℂ) + 1)) := by
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hij
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound (N : ℕ) : ‖∑ n ∈ Finset.range N, z ^ (n + 1)‖ ≤ 2 / ‖z - 1‖ := by
    have he : (∑ n ∈ Finset.range N, z ^ (n + 1)) = z * ∑ n ∈ Finset.range N, z ^ n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => pow_succ' z n)
    rw [he, norm_mul, hz, one_mul, geom_sum_eq hz1, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    simpa only [norm_pow, hz, one_pow, norm_one, one_add_one_eq_two] using norm_sub_le (z ^ N) 1
  have hc := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded ht hbound
  convert hc using 1
  funext N
  apply Finset.sum_congr rfl
  intro n _
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

lemma tendsto_unit_circle_log_partial_sums
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ n / (n : ℂ))
      atTop (𝓝 (-Complex.log (1 - z))) := by
  have hc : CauchySeq (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ n / (n : ℂ)) := by
    rw [← cauchySeq_shift 1]
    simpa only [Finset.sum_range_succ', pow_zero, Nat.cast_zero, div_zero, add_zero,
      Nat.cast_add, Nat.cast_one] using cauchySeq_unit_circle_log_partial_sums z hz hz1
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  rw [Filter.tendsto_map'_iff] at hab
  have hre : z.re < 1 := by
    have hle : z.re ≤ 1 := hz ▸ Complex.re_le_norm z
    by_contra h
    have he : z.re = 1 := by linarith
    have hsq := Complex.sq_norm z
    rw [hz, Complex.normSq_apply, he] at hsq
    have hi : z.im = 0 := by nlinarith
    exact hz1 (Complex.ext he hi)
  have hslit : 1 - z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hre
  have hcont : Continuous (fun r : ℝ => 1 - (r : ℂ) * z) := by fun_prop
  have harg : Tendsto (fun r : ℝ => 1 - (r : ℂ) * z) (𝓝[<] (1 : ℝ)) (𝓝 (1 - z)) := by
    simpa only [Complex.ofReal_one, one_mul] using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlog := (harg.clog hslit).neg
  have hpositive : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hevent : (fun r : ℝ => ∑' n : ℕ, (z ^ n / (n : ℂ)) * (r : ℂ) ^ n) =ᶠ[𝓝[<] 1]
      (fun r : ℝ => -Complex.log (1 - (r : ℂ) * z)) := by
    filter_upwards [hpositive, self_mem_nhdsWithin] with r hr hr1
    have hn : ‖(r : ℂ) * z‖ < 1 := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one, Set.mem_Iio] using hr1
    calc
      (∑' n : ℕ, (z ^ n / (n : ℂ)) * (r : ℂ) ^ n) =
          ∑' n : ℕ, ((r : ℂ) * z) ^ n / (n : ℂ) := by
        apply tsum_congr
        intro n
        rw [mul_pow]
        ring
      _ = -Complex.log (1 - (r : ℂ) * z) := (Complex.hasSum_taylorSeries_neg_log hn).tsum_eq
  have heq : l = -Complex.log (1 - z) :=
    tendsto_nhds_unique hab (hlog.congr' hevent.symm)
  rwa [heq] at hl

end Catalan
