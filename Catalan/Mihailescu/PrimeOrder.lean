import Catalan.Mihailescu.Ideal
import Catalan.Cyclotomic.OtherPrime
import Catalan.Mihailescu.Orders

/-! Positive integer orders on field units at a nonzero prime ideal. -/
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
namespace Catalan
variable (K : Type*) [Field K] [NumberField K]

/-- The exponent of a prime in the principal fractional ideal of a field unit. -/
def primeOrder (Q : HeightOneSpectrum (𝓞 K)) : Kˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd
    (FractionalIdeal.count K Q (principalIdeal K a : FracIdeal K))
  map_one' := by
    change Multiplicative.ofAdd (FractionalIdeal.count K Q _) = 1
    rw [map_one, Units.val_one, FractionalIdeal.count_one]
    rfl
  map_mul' a b := by
    rw [map_mul, Units.val_mul, FractionalIdeal.count_mul K Q
      (Units.ne_zero _) (Units.ne_zero _)]
    rfl

lemma primeOrder_integral (Q : HeightOneSpectrum (𝓞 K)) (a : Kˣ) (z : 𝓞 K)
    (hz : (a : K) = z) :
    (primeOrder K Q a).toAdd = FractionalIdeal.count K Q (Ideal.span {z} : FracIdeal K) := by
  change FractionalIdeal.count K Q (principalIdeal K a : FracIdeal K) = _
  rw [coe_toPrincipalIdeal, hz, FractionalIdeal.coeIdeal_span_singleton]

lemma primeOrder_integral_nonneg (Q : HeightOneSpectrum (𝓞 K)) (a : Kˣ) (z : 𝓞 K)
    (hz : (a : K) = z) : 0 ≤ (primeOrder K Q a).toAdd := by
  rw [primeOrder_integral K Q a z hz]
  exact FractionalIdeal.count_coe_nonneg K Q _

lemma primeOrder_integral_pos_iff (Q : HeightOneSpectrum (𝓞 K)) (a : Kˣ) (z : 𝓞 K)
    (hz : (a : K) = z) : 0 < (primeOrder K Q a).toAdd ↔ z ∈ Q.asIdeal := by
  have hz0 : z ≠ 0 := by
    intro h
    apply Units.ne_zero a
    rw [hz, h]
    rfl
  have hI0 : Ideal.span {z} ≠ (0 : Ideal (𝓞 K)) := Ideal.span_singleton_eq_bot.not.mpr hz0
  rw [primeOrder_integral K Q a z hz, FractionalIdeal.count_coe K Q hI0,
    Nat.cast_pos, Nat.pos_iff_ne_zero, Associates.count_ne_zero_iff_dvd hI0 Q.irreducible,
    Ideal.dvd_span_singleton]

lemma primeOrder_integral_eq_zero (Q : HeightOneSpectrum (𝓞 K)) (a : Kˣ) (z : 𝓞 K)
    (hz : (a : K) = z) (hnot : z ∉ Q.asIdeal) : (primeOrder K Q a).toAdd = 0 := by
  have hn := primeOrder_integral_nonneg K Q a z hz
  have hp := (primeOrder_integral_pos_iff K Q a z hz).not.mpr hnot
  omega

end Catalan
