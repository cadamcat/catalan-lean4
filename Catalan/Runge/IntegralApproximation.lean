import Catalan.Runge.Estimate
import Catalan.Runge.ErrorBound
import Catalan.Runge.CoefficientIntegral
import Catalan.Runge.SmallConjugates
import Catalan.Mihailescu.PositiveProducts

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.Runge

lemma D_strictMono (q : ℕ) (hq : q.Prime) : StrictMono (D q) := by
  let instPrimeQ : Fact q.Prime := ⟨hq⟩
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [D, casselsDenExp, Nat.factorial_succ,
    padicValNat.mul (Nat.succ_ne_zero k) (Nat.factorial_ne_zero k)]
  omega

section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma integral_rungeApprox (q : ℕ) (hq : q.Prime) (Theta : R p K)
    (hn : ∀ g, 0 ≤ Theta.coeff g) (m : ℕ) (x : ℤ) :
    IsIntegral ℤ (rungeApprox p K q Theta m x) := by
  rw [rungeApprox, Finset.mul_sum]
  apply IsIntegral.sum
  intro k hk
  have hkm : k ≤ m := Finset.mem_range_succ_iff.mp hk
  have hD : D q k ≤ D q m := (D_strictMono q hq).monotone hkm
  have hcoeff := (runge_coeff_integral p K q hq Theta hn k).2
  have hnat : IsIntegral ℤ (q : K) := isIntegral_natCast q
  have hscaled : IsIntegral ℤ
      ((q : K) ^ D q m * rungeCoeff p K q Theta k) := by
    rw [← Nat.sub_add_cancel hD, pow_add, mul_assoc]
    exact (hnat.pow (D q m - D q k)).mul hcoeff
  rw [← mul_assoc]
  exact hscaled.mul ((isIntegral_intCast x).pow (m - k))

lemma scaled_root_eq_rungeApprox (q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q)
    (hp2 : p ≠ 2) (hpq : p ≠ q) (x : ℤ)
    (hx : (q : ℝ) ^ (p - 1) < (|x| : ℝ))
    (Theta : R p K) (hn : ∀ g, 0 ≤ Theta.coeff g)
    (he : EvenCoefficients p K Theta) (m : ℕ) (hm : 0 < m) (hmp : 2 * m ≤ p - 1)
    (hw : weight p K Theta = (m * q : ℕ)) (u : K)
    (hu : u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K)) :
    (q : K) ^ D q m * u = rungeApprox p K q Theta m x := by
  have huInt : IsIntegral ℤ u := by
    apply IsIntegral.of_pow hq.pos
    rw [hu]
    exact integral_upow_xmζ_of_nonneg p K x hp2 Theta hn
  have hnat : IsIntegral ℤ (q : K) := isIntegral_natCast q
  have hdelta : IsIntegral ℤ
      ((q : K) ^ D q m * u - rungeApprox p K q Theta m x) :=
    ((hnat.pow (D q m)).mul huInt).sub (integral_rungeApprox p K q hq Theta hn m x)
  let delta : 𝓞 K := ⟨(q : K) ^ D q m * u - rungeApprox p K q Theta m x, hdelta⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
  have hx1 : 1 < (|x| : ℝ) := (one_le_pow₀ hq1).trans_lt hx
  have hzero : delta = 0 := by
    apply small_conjugates_zero K delta
    intro τ
    exact (runge_estimate p K q hq hq7 hp2 hpq x hx1 Theta hn he m hm hw u hu τ).trans_lt
      (error_lt_one p q m (|x| : ℝ) hq hq7 hm hmp hx)
  have hz := congrArg (fun a : 𝓞 K => (a : K)) hzero
  change (q : K) ^ D q m * u - rungeApprox p K q Theta m x = 0 at hz
  exact sub_eq_zero.mp hz

end Cyclotomic
end Catalan.Runge
