module

public import Catalan.Cassels.Valuation
public import Catalan.Cassels.PowerFactors

/-!
# `Catalan.Cassels.Elementary`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators

namespace Catalan

lemma int_pow_sub_one_factor (n : ℕ) (x : ℤ) :
    x ^ n - 1 = (x - 1) * casselsCyclo n x := by
  exact (mul_geom_sum x n).symm

lemma cassels_cyclo_sub_dvd (n : ℕ) (x : ℤ) :
    x - 1 ∣ casselsCyclo n x - (n : ℤ) := by
  induction n with
  | zero =>
      simp only [casselsCyclo, Finset.range_zero, Finset.sum_empty,
        Nat.cast_zero, sub_zero]
      exact dvd_zero _
  | succ n ih =>
      have he : casselsCyclo (n + 1) x - ((n + 1 : ℕ) : ℤ) =
          (casselsCyclo n x - (n : ℤ)) + (x ^ n - 1) := by
        simp only [casselsCyclo, Finset.sum_range_succ, Nat.cast_add,
          Nat.cast_one]
        ring
      rw [he]
      exact dvd_add ih (sub_one_dvd_pow_sub_one x n)

lemma gcd_x_sub_one_cyclotomic (p : ℕ) (hp : p.Prime) (x : ℤ) :
    Int.gcd (x - 1) (casselsCyclo p x) = 1 ∨
      Int.gcd (x - 1) (casselsCyclo p x) = p := by
  let g : ℕ := Int.gcd (x - 1) (casselsCyclo p x)
  have hgx : (g : ℤ) ∣ x - 1 := Int.gcd_dvd_left _ _
  have hgs : (g : ℤ) ∣ casselsCyclo p x := Int.gcd_dvd_right _ _
  have hgd : (g : ℤ) ∣ casselsCyclo p x - (p : ℤ) :=
    dvd_trans hgx (cassels_cyclo_sub_dvd p x)
  have hgp : (g : ℤ) ∣ (p : ℤ) := by
    have ht := dvd_sub hgs hgd
    have he : casselsCyclo p x - (casselsCyclo p x - (p : ℤ)) = p := by ring
    rwa [he] at ht
  have hgpN : g ∣ p := by exact_mod_cast hgp
  exact (Nat.dvd_prime hp).mp hgpN

lemma cassels_emultiplicity_eq (p : ℕ) (hp : p.Prime)
    (a : ℤ) (ha : a ≠ 0) :
    emultiplicity (p : ℤ) a = (padicValInt p a : ℕ∞) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [← Int.emultiplicity_natAbs p a]
  exact (padicValNat_eq_emultiplicity (p := p)
    (Int.natAbs_ne_zero.mpr ha)).symm

lemma cassels_padicValInt_pow (p : ℕ) (hp : p.Prime)
    (a : ℤ) (n : ℕ) :
    padicValInt p (a ^ n) = n * padicValInt p a := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [padicValInt, Int.natAbs_pow] using
    (padicValNat.pow (p := p) a.natAbs n)

lemma cassels_padicValInt_mul (p : ℕ) (hp : p.Prime)
    (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
  letI : Fact p.Prime := ⟨hp⟩
  exact padicValInt.mul ha hb

lemma cassels_prime_dvd_of_dvd_pow (p : ℕ) (hp : p.Prime)
    (a : ℤ) (n : ℕ) (h : (p : ℤ) ∣ a ^ n) : (p : ℤ) ∣ a := by
  exact (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h

lemma cassels_bad_factor (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (x y : ℤ) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (hpy : ¬ (p : ℤ) ∣ y) :
    ∃ a : ℤ, a ≠ 0 ∧ x - 1 = a ^ q := by
  have hprod : (x - 1) * casselsCyclo p x = y ^ q := by
    rw [← int_pow_sub_one_factor p x]
    linarith
  have hA : x - 1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact (pow_ne_zero q hy) hprod.symm
  have hB : casselsCyclo p x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact (pow_ne_zero q hy) hprod.symm
  have hg : Int.gcd (x - 1) (casselsCyclo p x) = 1 := by
    rcases gcd_x_sub_one_cyclotomic p hp x with hg | hg
    · exact hg
    · exfalso
      have hpA : (p : ℤ) ∣ x - 1 := by
        have ht := Int.gcd_dvd_left (x - 1) (casselsCyclo p x)
        rwa [hg] at ht
      have hpPow : (p : ℤ) ∣ y ^ q := by
        rw [← hprod]
        exact dvd_mul_of_dvd_left hpA _
      exact hpy (cassels_prime_dvd_of_dvd_pow p hp y q hpPow)
  obtain ⟨a, b, ha, hb⟩ := cassels_coprime_power_factors q
    (hq.odd_of_ne_two hq2) (x - 1) (casselsCyclo p x) y hA hB hg hprod
  refine ⟨a, ?_, ha⟩
  intro ha0
  rw [ha0, zero_pow hq.ne_zero] at ha
  exact hA ha

lemma cassels_solution_symm (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (x y : ℤ) (h : x ^ p = y ^ q + 1) :
    (-y) ^ q = (-x) ^ p + 1 := by
  rw [hq.neg_pow, hp.neg_pow]
  linarith

lemma cassels_consecutive_gap (n : ℕ) (z : ℤ) (hz : 1 ≤ z) :
    (n : ℤ) ≤ (z + 1) ^ n - z ^ n := by
  have hpow : ∀ k : ℕ, (1 : ℤ) ≤ z ^ k := by
    intro k
    induction k with
    | zero => simp only [pow_zero, le_refl]
    | succ k ih =>
        rw [pow_succ]
        have hm := mul_le_mul_of_nonneg_right ih (show 0 ≤ z by omega)
        nlinarith
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hm := mul_le_mul_of_nonneg_left ih (show 0 ≤ z + 1 by omega)
      have hnz : 0 ≤ (n : ℤ) * z :=
        mul_nonneg (Nat.cast_nonneg n) (by omega)
      have hzpow := hpow n
      rw [pow_succ, pow_succ, Nat.cast_succ]
      nlinarith

lemma cassels_equal_exponents_false (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ p + 1) : False := by
  have ho : Odd p := hp.odd_of_ne_two hp2
  have hpZ : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  have hpos : ∀ X Y : ℤ, 1 ≤ Y → X ^ p = Y ^ p + 1 → False := by
    intro X Y hY H
    have hYX : Y < X := ho.pow_lt_pow.mp (by omega)
    have hmon : (Y + 1) ^ p ≤ X ^ p := ho.pow_le_pow.mpr (by omega)
    have hgap := cassels_consecutive_gap p Y hY
    omega
  by_cases hypos : 0 < y
  · exact hpos x y (by omega) h
  · have hyn : y < 0 := by omega
    have hyp : y ^ p < 0 := ho.pow_neg hyn
    have hxp : x ^ p ≤ 0 := by omega
    have hxn : x < 0 := by
      have ht : x ≤ 0 := ho.pow_nonpos_iff.mp hxp
      omega
    exact hpos (-y) (-x) (by omega)
      (cassels_solution_symm p p ho ho x y h)


#print axioms gcd_x_sub_one_cyclotomic
#print axioms cassels_bad_factor
#print axioms cassels_equal_exponents_false

end Catalan
