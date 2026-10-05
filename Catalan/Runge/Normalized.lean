module

public import Catalan.Runge.IntegralApproximation
public import Catalan.Runge.ReducedQuotient
public import Catalan.Runge.CoefficientBasis
public import Catalan.Runge.CoeffResidue
public import Catalan.Runge.Reduction

/-!
# `Catalan.Runge.Normalized`

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

local instance normalizedGalFintype : Fintype (G p K) := Fintype.ofFinite _

lemma integral_leadingCoeff_of_scaled_root (q : ℕ) (hq : q.Prime)
    (Theta : R p K) (hn : ∀ g, 0 ≤ Theta.coeff g) (m : ℕ) (x : ℤ) (u : K)
    (hu : IsIntegral ℤ u)
    (hscaled : (q : K) ^ D q m * u = rungeApprox p K q Theta m x) :
    IsIntegral ℤ ((q : K) ^ (D q m - 1) * rungeCoeff p K q Theta m) := by
  have hqK : (q : K) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hsum : u = ∑ k ∈ Finset.range (m + 1), rungeCoeff p K q Theta k * (x : K) ^ (m - k) := by
    apply mul_left_cancel₀ (pow_ne_zero (D q m) hqK)
    exact hscaled
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one] at hsum
  have hlead : rungeCoeff p K q Theta m =
      u - ∑ k ∈ Finset.range m, rungeCoeff p K q Theta k * (x : K) ^ (m - k) := by
    linear_combination -hsum
  have hnat : IsIntegral ℤ (q : K) := isIntegral_natCast q
  rw [hlead, mul_sub, Finset.mul_sum]
  apply ((hnat.pow (D q m - 1)).mul hu).sub
  apply IsIntegral.sum
  intro k hk
  have hD : D q k ≤ D q m - 1 := by
    have hlt := D_strictMono q hq (Finset.mem_range.mp hk)
    omega
  have hcoeff := (runge_coeff_integral p K q hq Theta hn k).2
  have hscaledk : IsIntegral ℤ ((q : K) ^ (D q m - 1) * rungeCoeff p K q Theta k) := by
    rw [← Nat.sub_add_cancel hD, pow_add, mul_assoc]
    exact (hnat.pow (D q m - 1 - D q k)).mul hcoeff
  rw [← mul_assoc]
  exact hscaledk.mul ((isIntegral_intCast x).pow (m - k))

lemma runge_normalized (q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q)
    (hp2 : p ≠ 2) (hpq : p ≠ q) (x : ℤ)
    (hx : (q : ℝ) ^ (p - 1) < (|x| : ℝ))
    (Theta : R p K) (hn : ∀ g, 0 ≤ Theta.coeff g)
    (he : EvenCoefficients p K Theta) (m : ℕ) (hm : 0 < m) (hmp : 2 * m ≤ p - 1)
    (hw : weight p K Theta = (m * q : ℕ))
    (hu : ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K)) :
    reduceFull p K q Theta = 0 := by
  classical
  obtain ⟨u, hu⟩ := hu
  have huInt : IsIntegral ℤ u := by
    apply IsIntegral.of_pow hq.pos
    rw [hu]
    exact integral_upow_xmζ_of_nonneg p K x hp2 Theta hn
  have hscaled := scaled_root_eq_rungeApprox p K q hq hq7 hp2 hpq x hx Theta hn he m hm hmp hw u hu
  have hlead := integral_leadingCoeff_of_scaled_root p K q hq Theta hn m x u huInt hscaled
  let A : 𝓞 K := ⟨(q : K) ^ (D q m - 1) * rungeCoeff p K q Theta m, hlead⟩
  have hDpos : 0 < D q m := by dsimp only [D, casselsDenExp]; omega
  have hfactor : (q : K) ^ m * (m.factorial : K) * rungeCoeff p K q Theta m =
      (q : K) * ((casselsFactorialCore q m : K) * (A : K)) := by
    obtain ⟨_, hfac, _, _⟩ := cassels_factorial_core_spec q m hq
    have hfacK : (m.factorial : K) = (q : K) ^ padicValNat q m.factorial * casselsFactorialCore q m := by
      exact_mod_cast hfac
    have hpow : (q : K) ^ D q m = (q : K) * (q : K) ^ (D q m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ D q m)]
    calc
      _ = (casselsFactorialCore q m : K) * ((q : K) ^ D q m * rungeCoeff p K q Theta m) := by
        rw [hfacK]
        dsimp only [D, casselsDenExp]
        rw [pow_add]
        ring
      _ = _ := by
        rw [hpow]
        change (casselsFactorialCore q m : K) *
          ((q : K) * (q : K) ^ (D q m - 1) * rungeCoeff p K q Theta m) =
          (q : K) * ((casselsFactorialCore q m : K) *
            ((q : K) ^ (D q m - 1) * rungeCoeff p K q Theta m))
        ring
  obtain ⟨w, hres⟩ := runge_coeff_residue p K q hq Theta hn m
  let S : 𝓞 K := ∑ g : G p K, (Theta.coeff g : 𝓞 K) * zetaConjInt p K g
  have hS : (S : K) = ∑ g : G p K, (Theta.coeff g : K) * g (ζ p K) := by
    change algebraMap (𝓞 K) K S = _
    simp only [S, map_sum, map_mul, map_intCast]
    rfl
  have hdiv : (q : 𝓞 K) ∣ (-S) ^ m := by
    refine ⟨(casselsFactorialCore q m : 𝓞 K) * A - w, ?_⟩
    apply RingOfIntegers.coe_injective
    change (-(S : K)) ^ m = (q : K) * ((casselsFactorialCore q m : K) * (A : K) - (w : K))
    rw [hS]
    linear_combination hfactor - hres
  have hSdiv : (q : 𝓞 K) ∣ S := by
    simpa only [dvd_neg] using cyclotomic_prime_dvd_of_dvd_pow p K q hq hpq (-S) m hdiv
  apply (reduceFull_eq_zero_iff p K q Theta).mpr
  exact dvd_coeff_of_dvd_zeta_sum p K q Theta hSdiv

end Catalan.Runge
