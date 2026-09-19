import Catalan.Runge.Definitions

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Catalan.Runge

lemma binomRat_eq_choose (a : ℚ) (k : ℕ) : binomRat a k = Ring.choose a k := by
  unfold binomRat
  rw [Ring.choose_eq_smul]
  have hs : (descPochhammer ℤ k).smeval a =
      (descPochhammer ℚ k).eval a := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    have he : (RingHom.smulOneHom : ℤ →+* ℚ) = Int.castRingHom ℚ := Subsingleton.elim _ _
    rw [he, ← descPochhammer_map (Int.castRingHom ℚ), Polynomial.eval_map]
  rw [hs, descPochhammer_eval_eq_prod_range]
  simp [smul_eq_mul, mul_comm, div_eq_mul_inv]

lemma hasSum_binomRat_mul_pow (a : ℚ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (binomRat a k : ℂ) * z ^ k) ((1 + z) ^ (a : ℂ)) := by
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball]
    simpa only [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hz
  have hs := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
    (a := (a : ℂ))).hasSum hz'
  have hterm (n : ℕ) :
      (binomialSeries ℂ (a : ℂ) n) (fun _ : Fin n => z) =
        (binomRat a n : ℂ) * z ^ n := by
    rw [binomialSeries_apply, List.prod_ofFn, Finset.prod_const, Finset.card_fin]
    have hchoose : Ring.choose (a : ℂ) n = ((Ring.choose a n : ℚ) : ℂ) := by
      simpa using (Ring.map_choose (algebraMap ℚ ℂ) a n).symm
    rw [hchoose]
    simp [binomRat_eq_choose]
  simpa only [hterm, zero_add] using hs

end Catalan.Runge
