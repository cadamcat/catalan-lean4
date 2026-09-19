import Catalan.Runge.ProductCoefficients

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Catalan.Runge

lemma binomialProduct_positive_real
    (ι : Type*) [Fintype ι] (a : ι → ℚ) (w : ι → ℂ) (e : ι ≃ ι)
    (ha : ∀ i, a (e i) = a i) (hwconj : ∀ i, w (e i) = conj (w i))
    (hw : ∀ i, ‖w i‖ ≤ 1) (t : ℝ) (ht : |t| < 1) :
    ∃ r : ℝ, 0 < r ∧ (∏ i, (1 + w i * (t : ℂ)) ^ (a i : ℂ)) = (r : ℂ) := by
  classical
  let b : ι → ℂ := fun i => 1 + w i * (t : ℂ)
  have hslit (i : ι) : b i ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_of_norm_lt_one
    calc
      ‖w i * (t : ℂ)‖ = ‖w i‖ * |t| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 * |t| := mul_le_mul_of_nonneg_right (hw i) (abs_nonneg t)
      _ < 1 := by simpa using ht
  have hbconj (i : ι) : b (e i) = conj (b i) := by
    simp only [b, hwconj, map_add, map_one, map_mul, Complex.conj_ofReal]
  let f : ι → ℂ := fun i => Complex.log (b i) * (a i : ℂ)
  have hfconj (i : ι) : f (e i) = conj (f i) := by
    dsimp only [f]
    rw [ha, hbconj, Complex.log_conj _ (Complex.slitPlane_arg_ne_pi (hslit i))]
    simp only [map_mul, map_ratCast]
  have hsum : conj (∑ i, f i) = ∑ i, f i := by
    rw [map_sum]
    calc
      ∑ i, conj (f i) = ∑ i, f (e i) := Finset.sum_congr rfl (fun i _ => (hfconj i).symm)
      _ = ∑ i, f i := Equiv.sum_comp e f
  have hreal : ((∑ i, f i).re : ℂ) = ∑ i, f i := Complex.conj_eq_iff_re.mp hsum
  refine ⟨Real.exp (∑ i, f i).re, Real.exp_pos _, ?_⟩
  calc
    (∏ i, (1 + w i * (t : ℂ)) ^ (a i : ℂ)) = ∏ i, Complex.exp (f i) :=
      Finset.prod_congr rfl (fun i _ => Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (hslit i)) _)
    _ = Complex.exp (∑ i, f i) := (Complex.exp_sum Finset.univ f).symm
    _ = Complex.exp ((∑ i, f i).re : ℂ) := congrArg Complex.exp hreal.symm
    _ = (Real.exp (∑ i, f i).re : ℂ) := (Complex.ofReal_exp _).symm

end Catalan.Runge
