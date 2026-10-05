module

public import Catalan.Cyclotomic.Basic

/-!
# `Catalan.Cyclotomic.Elements`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Pointwise
open NumberField

noncomputable section
namespace Catalan

section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma cyclotomic_degree : Module.finrank ℚ K = p - 1 := by
  rw [IsCyclotomicExtension.finrank (n := p) (K := ℚ) K
    (Polynomial.cyclotomic.irreducible_rat (Fact.out : p.Prime).pos)]
  simpa only [pow_one, Nat.sub_self, pow_zero, one_mul] using
    (Nat.totient_prime_pow (Fact.out : p.Prime) (show 0 < (1 : ℕ) by decide))

lemma embedding_isComplex (hp2 : p ≠ 2) (φ : K →+* ℂ) :
    (InfinitePlace.mk φ).IsComplex := by
  have hprime : p.Prime := Fact.out
  have hpgt : 2 < p := by
    have hpge : 2 ≤ p := hprime.two_le
    omega
  letI : NumberField.IsTotallyComplex K :=
    IsCyclotomicExtension.Rat.isTotallyComplex K hpgt
  exact InfinitePlace.isComplex_mk_iff.mpr
    (NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ)

lemma norm_conj_zeta (φ : K →+* ℂ) (τ : G p K) :
    ‖φ (τ (ζ p K))‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one
  · rw [← map_pow, ← map_pow, (ζ_spec p K).pow_eq_one, map_one, map_one]
  · exact (Fact.out : p.Prime).ne_zero

lemma x_sub_ζ_ne_zero (x : ℤ) (hp2 : p ≠ 2) :
    (x : K) - ζ p K ≠ 0 := by
  intro hzero
  have hxζ : (x : K) = ζ p K := sub_eq_zero.mp hzero
  have hxpK : (x : K) ^ p = (1 : K) := by
    rw [hxζ, (ζ_spec p K).pow_eq_one]
  have hxp : x ^ p = (1 : ℤ) := by
    exact_mod_cast hxpK
  have hprime : p.Prime := Fact.out
  have hpodd : Odd p := hprime.odd_of_ne_two hp2
  have hxone : x = 1 := hpodd.pow_injective (by simpa using hxp)
  have hζone : ζ p K = 1 := by
    rw [← hxζ]
    exact_mod_cast hxone
  exact (ζ_spec p K).ne_one hprime.one_lt hζone

lemma integral_conj_zeta (τ : G p K) : IsIntegral ℤ (τ (ζ p K)) := by
  have hprime : p.Prime := Fact.out
  apply IsIntegral.of_pow (R := ℤ) (n := p) hprime.pos
  have hpow : (τ (ζ p K)) ^ p = (1 : K) := by
    rw [← map_pow, (ζ_spec p K).pow_eq_one, map_one]
  simpa [hpow] using (isIntegral_one : IsIntegral ℤ (1 : K))

end Cyclotomic
end Catalan
