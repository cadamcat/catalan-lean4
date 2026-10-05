module

public import Catalan.Runge.RootEvaluation
public import Catalan.Runge.CoefficientMajorant
public import Catalan.Runge.ProductSeries
public import Catalan.Runge.TailBound
public import Catalan.Runge.ApproximationMap

/-!
# `Catalan.Runge.Estimate`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.Runge

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance estimateGalFintype : Fintype (G p K) := Fintype.ofFinite _

lemma rungeCoeff_norm_le (q : ℕ) (hq : q ≠ 0) (Theta : R p K)
    (hn : ∀ g, 0 ≤ Theta.coeff g) (m : ℕ)
    (hw : weight p K Theta = (m * q : ℕ)) (τ : K →+* ℂ) (k : ℕ) :
    ‖τ (rungeCoeff p K q Theta k)‖ ≤ (Nat.multichoose m k : ℝ) := by
  rw [map_rungeCoeff_eq_binomialProductCoeff]
  apply norm_binomialProductCoeff_le_multichoose
  · intro g
    exact div_nonneg (by exact_mod_cast hn g) (Nat.cast_nonneg q)
  · intro g
    rw [norm_neg, norm_embedding_zeta_conj p K τ g]
  · rw [← Finset.sum_div]
    have hsumZ : (∑ g : G p K, Theta.coeff g) = ((m * q : ℕ) : ℤ) := by
      simpa only [← weight_eq_sum] using hw
    have hsumQ : (∑ g : G p K, (Theta.coeff g : ℚ)) = (m : ℚ) * (q : ℚ) := by
      exact_mod_cast hsumZ
    rw [hsumQ, mul_div_cancel_right₀ _ (by exact_mod_cast hq : (q : ℚ) ≠ 0)]

lemma hasSum_rungeCoeff (q : ℕ) (Theta : R p K) (τ : K →+* ℂ)
    (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => τ (rungeCoeff p K q Theta k) * z ^ k)
      (rungeFunction p K q Theta τ z) := by
  have hs := hasSum_binomialProductCoeff (G p K)
    (fun g => (Theta.coeff g : ℚ) / q) (fun g => -τ (g (ζ p K)))
    (fun g => by rw [norm_neg, norm_embedding_zeta_conj p K τ g]) z hz
  simpa only [← map_rungeCoeff_eq_binomialProductCoeff, rungeFunction] using hs

lemma runge_estimate (q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q)
    (hp2 : p ≠ 2) (hpq : p ≠ q) (x : ℤ) (hx : 1 < (|x| : ℝ))
    (Theta : R p K) (hn : ∀ g, 0 ≤ Theta.coeff g)
    (he : EvenCoefficients p K Theta) (m : ℕ) (hm : 0 < m)
    (hw : weight p K Theta = (m * q : ℕ)) (u : K)
    (hu : u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K)) :
    ∀ τ : K →+* ℂ,
      ‖τ ((q : K) ^ D q m * u - rungeApprox p K q Theta m x)‖ ≤
        errorBound q m (|x| : ℝ) := by
  intro τ
  have instQPrime : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  have hx0 : x ≠ 0 := by intro hx0; subst x; norm_num at hx
  have hXpos : (0 : ℝ) < (|x| : ℝ) := by linarith
  have hnormx : ‖(x : ℂ)‖ = (|x| : ℝ) := by simp
  have hnormz : ‖(x : ℂ)⁻¹‖ = (|x| : ℝ)⁻¹ := by rw [norm_inv, hnormx]
  have hz : ‖(x : ℂ)⁻¹‖ < 1 := by
    rw [hnormz]
    exact (inv_lt_one₀ hXpos).mpr hx
  have hs := hasSum_rungeCoeff p K q Theta τ ((x : ℂ)⁻¹) hz
  have htail := norm_series_tail_le m hm (fun k => τ (rungeCoeff p K q Theta k))
    ((x : ℂ)⁻¹) (rungeFunction p K q Theta τ ((x : ℂ)⁻¹)) hz
    (rungeCoeff_norm_le p K q hq.ne_zero Theta hn m hw τ) hs
  have hroot := root_eq_scaled_rungeFunction p K q hp2 hpq hq2 x hx Theta hn he m hw u hu τ
  have hdelta : τ ((q : K) ^ D q m * u - rungeApprox p K q Theta m x) =
      ((q : ℂ) ^ D q m * (x : ℂ) ^ m) *
        (rungeFunction p K q Theta τ ((x : ℂ)⁻¹) -
          ∑ k ∈ Finset.range (m + 1), τ (rungeCoeff p K q Theta k) * ((x : ℂ)⁻¹) ^ k) := by
    rw [map_sub, map_mul, map_pow, map_natCast, map_rungeApprox p K q Theta m x hx0 τ, hroot]
    ring
  rw [hdelta, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, hnormx]
  calc
    _ ≤ (q : ℝ) ^ D q m * (|x| : ℝ) ^ m *
        (((2 * m).choose (m + 1) : ℝ) * (|x| : ℝ)⁻¹ ^ (m + 1) /
          (1 - (|x| : ℝ)⁻¹) ^ (2 * m + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [hnormz] using htail
    _ = errorBound q m (|x| : ℝ) := scale_tail_eq_errorBound q m (|x| : ℝ) hx

end Catalan.Runge
