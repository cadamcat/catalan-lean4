module

public import Mathlib

/-!
# `Catalan.Thaine.NormFactor`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

private lemma eval_cyclotomic_mul_sub_one
    {K : Type*} [Field K] (ell : ℕ) [Fact ell.Prime] (t : K) :
    Polynomial.eval t (Polynomial.cyclotomic ell K) * (t - 1) = t ^ ell - 1 := by
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_pow] using
    congrArg (Polynomial.eval t) (Polynomial.cyclotomic_prime_mul_X_sub_one K ell)

private lemma eval_cyclotomic_of_pow_self
    {K : Type*} [Field K] (ell : ℕ) [Fact ell.Prime] (t : K)
    (ht : t ≠ 1) (hpow : t ^ ell = t) :
    Polynomial.eval t (Polynomial.cyclotomic ell K) = 1 := by
  apply (mul_left_inj' (sub_ne_zero.mpr ht)).mp
  simpa only [hpow, one_mul] using eval_cyclotomic_mul_sub_one ell t

private lemma eval_cyclotomic_of_pow_inv
    {K : Type*} [Field K] (ell : ℕ) [Fact ell.Prime] (t : K)
    (ht0 : t ≠ 0) (ht : t ≠ 1) (hpow : t ^ ell = t⁻¹) :
    Polynomial.eval t (Polynomial.cyclotomic ell K) = -t⁻¹ := by
  apply (mul_left_inj' (sub_ne_zero.mpr ht)).mp
  rw [eval_cyclotomic_mul_sub_one, hpow]
  field_simp
  ring

lemma epsilon_norm_factor_eq_one
    (K : Type*) [Field K] (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (z : K) (hz : IsPrimitiveRoot z p) (a : (ZMod p)ˣ) (m : ℤ)
    (hm : z ^ (2 * m + ((a : ZMod p).val : ℤ) - 1) = 1)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p])) :
    (z ^ m) ^ (ell - 1) *
      Polynomial.eval (z ^ (a : ZMod p).val) (Polynomial.cyclotomic ell K) /
        Polynomial.eval z (Polynomial.cyclotomic ell K) = 1 := by
  have hp : p.Prime := Fact.out
  have hellprime : ell.Prime := Fact.out
  have hz0 : z ≠ 0 := hz.ne_zero hp.ne_zero
  have hz1 : z ≠ 1 := hz.ne_one hp.one_lt
  have hza : IsPrimitiveRoot (z ^ (a : ZMod p).val) p :=
    hz.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)
  have hza0 : z ^ (a : ZMod p).val ≠ 0 := pow_ne_zero _ hz0
  have hza1 : z ^ (a : ZMod p).val ≠ 1 := hza.ne_one hp.one_lt
  rcases hell with hplus | hminus
  · have hpowz : z ^ ell = z := by
      simpa only [pow_one] using pow_eq_pow_of_modEq hplus hz.pow_eq_one
    have hpowza : (z ^ (a : ZMod p).val) ^ ell = z ^ (a : ZMod p).val := by
      simpa only [pow_one] using pow_eq_pow_of_modEq hplus hza.pow_eq_one
    rw [eval_cyclotomic_of_pow_self ell z hz1 hpowz,
      eval_cyclotomic_of_pow_self ell _ hza1 hpowza, mul_one, div_one]
    rw [← zpow_natCast, ← zpow_mul]
    apply (hz.zpow_eq_one_iff_dvd _).mpr
    apply dvd_mul_of_dvd_right
    exact_mod_cast hplus.symm.dvd'
  · have hperiod : z ^ (ell + 1) = 1 := by
      simpa only [pow_zero] using pow_eq_pow_of_modEq hminus hz.pow_eq_one
    have hpowz : z ^ ell = z⁻¹ := by
      calc
        z ^ ell = (z ^ ell * z) * z⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hz0, mul_one]
        _ = z⁻¹ := by rw [← pow_succ, hperiod, one_mul]
    have hpowza : (z ^ (a : ZMod p).val) ^ ell = (z ^ (a : ZMod p).val)⁻¹ := by
      rw [← pow_mul, Nat.mul_comm _ ell, pow_mul, hpowz, inv_pow]
    rw [eval_cyclotomic_of_pow_inv ell z hz0 hz1 hpowz,
      eval_cyclotomic_of_pow_inv ell _ hza0 hza1 hpowza]
    have hdperiod : (p : ℤ) ∣ (ell : ℤ) + 1 := by
      exact_mod_cast Nat.modEq_zero_iff_dvd.mp hminus
    have hdm : (p : ℤ) ∣ 2 * m + ((a : ZMod p).val : ℤ) - 1 :=
      (hz.zpow_eq_one_iff_dvd _).mp hm
    have hfinal : z ^ (m * ((ell : ℤ) - 1) + 1 - ((a : ZMod p).val : ℤ)) = 1 := by
      apply (hz.zpow_eq_one_iff_dvd _).mpr
      have heq : m * ((ell : ℤ) - 1) + 1 - ((a : ZMod p).val : ℤ) =
          m * ((ell : ℤ) + 1) - (2 * m + ((a : ZMod p).val : ℤ) - 1) := by ring
      rw [heq]
      exact dvd_sub (dvd_mul_of_dvd_right hdperiod m) hdm
    have hcast : ((ell - 1 : ℕ) : ℤ) = (ell : ℤ) - 1 := by
      have hellpos := hellprime.one_le
      omega
    calc
      (z ^ m) ^ (ell - 1) * -(z ^ (a : ZMod p).val)⁻¹ / -z⁻¹ =
          z ^ (m * ((ell : ℤ) - 1) + 1 - ((a : ZMod p).val : ℤ)) := by
        rw [zpow_sub₀ hz0, zpow_add₀ hz0, zpow_one,
          ← hcast, zpow_mul, zpow_natCast, zpow_natCast]
        field_simp
      _ = 1 := hfinal

end Catalan.Thaine
