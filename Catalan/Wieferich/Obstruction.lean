module

public import Catalan.Wieferich.Core
public import Catalan.Wieferich.Defs
public import Catalan.Wieferich.Basis
public import Catalan.Wieferich.Frobenius

/-!
# `Catalan.Wieferich.Obstruction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField
open scoped BigOperators
namespace Catalan.A1e
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma liftProduct_expansion (q : ℕ) (x : ℤ) :
    ∃ r : 𝓞 K, liftProduct p K q x =
      1 - (x : 𝓞 K) * liftLinear p K q + (x : 𝓞 K) ^ 2 * r := by
  simpa only [liftProduct, liftLinear] using
    (prod_one_sub_remainder (Finset.univ : Finset (ZMod p)ˣ)
      (x : 𝓞 K) (inverseConjugate p K) (liftCoefficient p q))

lemma liftProduct_mod_q (q : ℕ) (x : ℤ) (hx : (q : ℤ) ∣ x) :
    (q : 𝓞 K) ∣ liftProduct p K q x - 1 := by
  obtain ⟨t, ht⟩ := hx
  have ht' : (x : 𝓞 K) = (q : 𝓞 K) * (t : 𝓞 K) := by
    exact_mod_cast ht
  obtain ⟨r, hr⟩ := liftProduct_expansion p K q x
  refine ⟨-(t : 𝓞 K) * liftLinear p K q +
    (q : 𝓞 K) * (t : 𝓞 K) ^ 2 * r, ?_⟩
  rw [hr, ht']
  ring

/-- This is the exact first-order obstruction: q^2 divides x times the
linear coefficient in the INTEGER ring. -/
lemma liftProduct_obstruction
    (q : ℕ) (hq : q.Prime) (hpq : p ≠ q)
    (x : ℤ) (hx : (q : ℤ) ∣ x)
    (hpow : ∃ b : K, b ^ q = (liftProduct p K q x : K)) :
    (q : 𝓞 K) ^ 2 ∣ (x : 𝓞 K) * liftLinear p K q := by
  obtain ⟨b, hb⟩ := hpow
  obtain ⟨B, hB⟩ := integral_qth_root q hq.pos (liftProduct p K q x) b hb
  obtain ⟨F, hF⟩ := cyclotomic_frobenius_lift p K q hq hpq
  have hd : (q : 𝓞 K) ∣ B ^ q - 1 := by
    rw [hB]
    exact liftProduct_mod_q p K q x hx
  have hd2 := primary_of_frobenius_lift q F hF B hd
  rw [hB] at hd2
  obtain ⟨s, hs⟩ := hd2
  obtain ⟨r, hr⟩ := liftProduct_expansion p K q x
  obtain ⟨t, ht⟩ := hx
  have ht' : (x : 𝓞 K) = (q : 𝓞 K) * (t : 𝓞 K) := by
    exact_mod_cast ht
  refine ⟨(t : 𝓞 K) ^ 2 * r - s, ?_⟩
  rw [hr, ht'] at hs
  rw [ht']
  linear_combination -hs

lemma liftCoefficient_one (q : ℕ) (hp2 : p ≠ 2) :
    liftCoefficient p q 1 = q ^ 2 - 1 := by
  have hp3 : 2 < p := by
    have hp := (Fact.out : p.Prime).two_le
    omega
  have hv : (1 : ZMod p).val = 1 :=
    ZMod.val_one'' (Fact.out : p.Prime).ne_one
  simp only [liftCoefficient, Units.val_one, hv, mul_one, if_pos hp3]

lemma square_dvd_x_from_obstruction
    (q : ℕ) (hq : q.Prime) (hp2 : p ≠ 2) (x : ℤ)
    (hd : (q : 𝓞 K) ^ 2 ∣ (x : 𝓞 K) * liftLinear p K q) :
    (q : ℤ) ^ 2 ∣ x := by
  have hcoeff : ∀ a : (ZMod p)ˣ,
      (q : ℤ) ^ 2 ∣ x * (liftCoefficient p q a : ℤ) := by
    apply inverseConjugates_dvd_coeff p K ((q : ℤ) ^ 2)
      (fun a => x * (liftCoefficient p q a : ℤ))
    simpa only [liftLinear, Int.cast_pow, Int.cast_natCast,
      Int.cast_mul, Finset.mul_sum, mul_assoc] using hd
  have hone := hcoeff 1
  rw [liftCoefficient_one p q hp2] at hone
  have hq1 : 1 ≤ q ^ 2 := by
    have hq0 := hq.two_le
    nlinarith
  have hcast : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one]
  rw [hcast] at hone
  obtain ⟨s, hs⟩ := hone
  refine ⟨x - s, ?_⟩
  linear_combination -hs


end Catalan.A1e
