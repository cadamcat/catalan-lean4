import Mathlib

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma primitiveRoot_sub_one_isUnit
    (K : Type*) [Field K] [NumberField K] (n : ℕ) [NeZero n]
    (hn : 2 < n) (hnpp : ∀ r : ℕ, r.Prime → ∀ k : ℕ, r ^ k ≠ n)
    (z : K) (hz : IsPrimitiveRoot z n) :
    IsUnit (hz.toInteger - 1) := by
  have hnpos : 0 < n := by omega
  have hzi : IsPrimitiveRoot hz.toInteger n := hz.toInteger_isPrimitiveRoot
  have hroot : (Polynomial.cyclotomic n (𝓞 K)).IsRoot hz.toInteger :=
    hzi.isRoot_cyclotomic hnpos
  have heval : Polynomial.eval 1 (Polynomial.cyclotomic n (𝓞 K)) = 1 :=
    Polynomial.eval_one_cyclotomic_not_prime_pow (fun {r} hr k => hnpp r hr k)
  have hdvdneg : hz.toInteger - 1 ∣ (-1 : 𝓞 K) := by
    have h := Polynomial.sub_dvd_eval_sub hz.toInteger 1
      (Polynomial.cyclotomic n (𝓞 K))
    change Polynomial.eval hz.toInteger (Polynomial.cyclotomic n (𝓞 K)) = 0 at hroot
    simpa only [hroot, heval, zero_sub] using h
  exact isUnit_of_dvd_one (dvd_neg.mp hdvdneg)

lemma primitive_roots_difference_isUnit
    (K : Type*) [Field K] [NumberField K]
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (z w : K) (hz : IsPrimitiveRoot z p) (hw : IsPrimitiveRoot w ell) :
    IsUnit (hz.toInteger - hw.toInteger) := by
  have hcop : p.Coprime ell := by
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hdiv
    rcases (Nat.dvd_prime (Fact.out : ell.Prime)).mp hdiv with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hpe h
  have hprod : IsPrimitiveRoot (z * w⁻¹) (p * ell) := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    have hzorder : orderOf z = p := (IsPrimitiveRoot.iff_orderOf).mp hz
    have hworder : orderOf w = ell := (IsPrimitiveRoot.iff_orderOf).mp hw
    have hwinvorder : orderOf w⁻¹ = ell :=
      (IsPrimitiveRoot.iff_orderOf).mp hw.inv
    have hcop' : (orderOf z).Coprime (orderOf w⁻¹) := by
      rw [hzorder, hwinvorder]
      exact hcop
    calc
      orderOf (z * w⁻¹) = orderOf z * orderOf w⁻¹ :=
        (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hcop'
      _ = p * ell := by
        rw [hzorder, hwinvorder]
  have hprimepow : ∀ r : ℕ, r.Prime → ∀ k : ℕ, r ^ k ≠ p * ell := by
    intro r hr k hk
    have hpdiv : p ∣ r ^ k := by
      rw [hk]
      exact dvd_mul_right p ell
    have heldiv : ell ∣ r ^ k := by
      rw [hk]
      exact dvd_mul_left ell p
    have hpdiv' : p ∣ r := (Fact.out : p.Prime).dvd_of_dvd_pow hpdiv
    have heldiv' : ell ∣ r := (Fact.out : ell.Prime).dvd_of_dvd_pow heldiv
    rcases (Nat.dvd_prime hr).mp hpdiv' with hpone | hpr
    · exact (Fact.out : p.Prime).ne_one hpone
    rcases (Nat.dvd_prime hr).mp heldiv' with hellone | hrell
    · exact (Fact.out : ell.Prime).ne_one hellone
    exact hpe (hpr.trans hrell.symm)
  have hprodunit : IsUnit ((hprod.toInteger) - 1) :=
    primitiveRoot_sub_one_isUnit K (p * ell) (by
      have hp2 := (Fact.out : p.Prime).two_le
      have hell2 := (Fact.out : ell.Prime).two_le
      nlinarith) hprimepow (z * w⁻¹) hprod
  have hwunit : IsUnit hw.toInteger := hw.toInteger_isPrimitiveRoot.isUnit
    (Fact.out : ell.Prime).ne_zero
  have hfactor : hz.toInteger - hw.toInteger =
      (hprod.toInteger - 1) * hw.toInteger := by
    apply RingOfIntegers.coe_injective
    change z - w = (z * w⁻¹ - 1) * w
    have hw0 : w ≠ 0 := hw.ne_zero (Fact.out : ell.Prime).ne_zero
    rw [sub_mul, mul_assoc, inv_mul_cancel₀ hw0, mul_one, one_mul]
  rw [hfactor]
  exact hprodunit.mul hwunit

end Catalan.Thaine
