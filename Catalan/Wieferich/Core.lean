module

public import Mathlib

/-!
# `Catalan.Wieferich.Core`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open NumberField

namespace Catalan.A1e

/-- The symmetry used in Bilu, equation (2) and the discussion following it. -/
lemma symmetry (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (x y : ℤ) (h : x ^ p = y ^ q + 1) :
    (-y) ^ q = (-x) ^ p + 1 := by
  rw [hq.neg_pow, hp.neg_pow]
  linarith

/-- Candidate for Mathlib upstream: exact first-order binomial expansion,
with an unspecified but integral quadratic remainder. -/
lemma one_add_pow_remainder {A : Type*} [CommRing A] (a : A) (n : ℕ) :
    ∃ r : A, (1 + a) ^ n = 1 + (n : A) * a + a ^ 2 * r := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      simp only [pow_zero, Nat.cast_zero, zero_mul, mul_zero, add_zero]
  | succ n ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨(n : A) + r + a * r, ?_⟩
      rw [pow_succ, hr, Nat.cast_succ]
      ring

/-- Candidate for Mathlib upstream: `(1 + q*t)^q = 1 mod q^2`,
valid in any commutative ring and for every natural `q`. -/
lemma one_add_mul_pow_dvd {A : Type*} [CommRing A] (q : ℕ) (t : A) :
    (q : A) ^ 2 ∣ (1 + (q : A) * t) ^ q - 1 := by
  obtain ⟨r, hr⟩ := one_add_pow_remainder ((q : A) * t) q
  refine ⟨t + t ^ 2 * r, ?_⟩
  rw [hr]
  ring

/-- Candidate for Mathlib upstream: a natural power expanded to first order
in `t`, with the exact sign convention `1 - t*z`. -/
lemma one_sub_pow_remainder {A : Type*} [CommRing A]
    (t z : A) (n : ℕ) :
    ∃ r : A, (1 - t * z) ^ n = 1 - t * ((n : A) * z) + t ^ 2 * r := by
  obtain ⟨r, hr⟩ := one_add_pow_remainder (-t * z) n
  refine ⟨z ^ 2 * r, ?_⟩
  calc
    (1 - t * z) ^ n = (1 + (-t * z)) ^ n := by congr 1; ring
    _ = 1 + (n : A) * (-t * z) + (-t * z) ^ 2 * r := hr
    _ = 1 - t * ((n : A) * z) + t ^ 2 * (z ^ 2 * r) := by ring

/-- Candidate for Mathlib upstream: finite-product first-order expansion.
No positivity, convergence, completion, or analytic estimate is involved. -/
lemma prod_one_sub_remainder {A I : Type*} [CommRing A]
    (s : Finset I) (t : A) (z : I → A) (m : I → ℕ) :
    ∃ r : A, (∏ i ∈ s, (1 - t * z i) ^ m i) =
      1 - t * (∑ i ∈ s, (m i : A) * z i) + t ^ 2 * r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp only [Finset.prod_empty, Finset.sum_empty, mul_zero, sub_zero, add_zero]
  | @insert i s hi ih =>
      obtain ⟨r, hr⟩ := one_sub_pow_remainder t (z i) (m i)
      obtain ⟨r', hr'⟩ := ih
      let c : A := (m i : A) * z i
      let L : A := ∑ j ∈ s, (m j : A) * z j
      refine ⟨c * L + r + r' - t * (c * r' + r * L) + t ^ 2 * r * r', ?_⟩
      rw [Finset.prod_insert hi, Finset.sum_insert hi, hr, hr']
      dsimp only [c, L]
      ring

/-- A lift of Frobenius by an automorphism implies the required primary
property. This isolates the entire local argument as elementary ring algebra. -/
lemma primary_of_frobenius_lift {A : Type*} [CommRing A]
    (q : ℕ) (F : A ≃+* A)
    (hF : ∀ a : A, (q : A) ∣ a ^ q - F a)
    (b : A) (hb : (q : A) ∣ b ^ q - 1) :
    (q : A) ^ 2 ∣ b ^ q - 1 := by
  have hd : (q : A) ∣ F b - 1 := by
    convert dvd_sub hb (hF b) using 1
    ring
  obtain ⟨c, hc⟩ := hd
  have he : b - 1 = (q : A) * F.symm c := by
    have hh := congrArg F.symm hc
    simpa only [map_sub, map_one, map_mul, map_natCast,
      RingEquiv.symm_apply_apply] using hh
  have he' : b = 1 + (q : A) * F.symm c := by
    linear_combination he
  rw [he']
  exact one_add_mul_pow_dvd q (F.symm c)

/-- An algebraic-integer q-th power whose root lies in the field has an
algebraic-integer root. Uses the verified `IsIntegral.of_pow`. -/
lemma integral_qth_root {K : Type*} [Field K] [NumberField K]
    (q : ℕ) (hq : 0 < q) (A : 𝓞 K) (b : K) (hb : b ^ q = (A : K)) :
    ∃ B : 𝓞 K, B ^ q = A := by
  have hi : IsIntegral ℤ b := IsIntegral.of_pow hq (by
    rw [hb]
    exact A.isIntegral_coe)
  let B : 𝓞 K := ⟨b, hi⟩
  refine ⟨B, ?_⟩
  apply RingOfIntegers.coe_injective
  rw [map_pow]
  exact hb

/-- Kronecker's theorem applied to a quotient of two global units related by
complex conjugation under every embedding. This is the part of Kummer's
unit lemma that the double Wieferich proof actually needs. -/
lemma kronecker_unit_pair {K : Type*} [Field K] [NumberField K]
    (u v : (𝓞 K)ˣ)
    (hconj : ∀ φ : K →+* ℂ, φ (v : K) = conj (φ (u : K))) :
    ∃ n : ℕ, 0 < n ∧ ((u : K) / (v : K)) ^ n = 1 := by
  let w : (𝓞 K)ˣ := u / v
  have hw : ((w : 𝓞 K) : K) = (u : K) / (v : K) := by
    change (w : K) = (u : K) / (v : K)
    dsimp only [w]
    calc
      ((u / v : (𝓞 K)ˣ) : K) = ((u * v ^ (-1 : ℤ) : (𝓞 K)ˣ) : K) := by
        simp only [zpow_neg_one, div_eq_mul_inv]
      _ = (u : K) * (v : K) ^ (-1 : ℤ) := by
        rw [NumberField.Units.coe_mul, NumberField.Units.coe_zpow]
      _ = (u : K) / (v : K) := by
        simp only [zpow_neg_one, div_eq_mul_inv]
  have hi : IsIntegral ℤ ((u : K) / (v : K)) :=
    hw ▸ (w : 𝓞 K).isIntegral_coe
  have hn : ∀ φ : K →+* ℂ, ‖φ ((u : K) / (v : K))‖ = 1 := by
    intro φ
    have hu : φ (u : K) ≠ 0 := by
      intro hzero
      apply NumberField.Units.coe_ne_zero u
      apply φ.injective
      simpa only [map_zero] using hzero
    rw [map_div₀, hconj φ, norm_div, Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr hu)]
  obtain ⟨n, hn0, he⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hi hn
  exact ⟨n, hn0, he⟩

/-- Candidate for Mathlib upstream: extracting a q-th root from torsion,
with an explicit Bezout identity. -/
lemma qth_root_of_bezout {M : Type*} [CommGroup M]
    (z : M) (N q : ℕ) (r s : ℤ)
    (hN : z ^ N = 1) (hbez : r * (q : ℤ) + s * (N : ℤ) = 1) :
    ∃ w : M, w ^ q = z := by
  have hNz : z ^ (N : ℤ) = 1 := by
    simpa only [zpow_natCast] using hN
  have hh : z ^ (r * (q : ℤ) + s * (N : ℤ)) = z := by
    rw [hbez, zpow_one]
  rw [zpow_add, mul_comm s (N : ℤ),
    zpow_mul z r (q : ℤ), zpow_mul z (N : ℤ) s,
    hNz, one_zpow, mul_one] at hh
  refine ⟨z ^ r, ?_⟩
  simpa only [zpow_natCast] using hh

/-- Candidate for Mathlib upstream: the q-power map is surjective on the
N-torsion whenever q and N are coprime. -/
lemma qth_root_of_coprime {M : Type*} [CommGroup M]
    (z : M) (N q : ℕ) (hN : z ^ N = 1) (hc : Nat.Coprime q N) :
    ∃ w : M, w ^ q = z := by
  apply qth_root_of_bezout z N q (Nat.gcdA q N) (Nat.gcdB q N) hN
  have hg := Nat.gcd_eq_gcd_ab q N
  rw [hc.gcd_eq_one] at hg
  norm_num only [Nat.cast_one] at hg
  nlinarith [hg]


end Catalan.A1e
