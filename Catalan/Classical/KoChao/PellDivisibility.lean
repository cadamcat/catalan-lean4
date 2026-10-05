module

public import Catalan.Cassels.Elementary
public import Catalan.Classical.Euler.Arithmetic
public import Mathlib.NumberTheory.PellMatiyasevic

/-!
# `Catalan.Classical.KoChao.PellDivisibility`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan.KoChao

lemma square_base_positive_even
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 2 = y ^ q + 1) : 0 < y ∧ Even y ∧ Odd x := by
  have ho : Odd q := hq.odd_of_ne_two hq2
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hyPow : 0 ≤ y ^ q := by have := sq_pos_of_ne_zero hx; omega
  have hyNonneg : 0 ≤ y := ho.pow_le_pow.mp (by
    simpa only [zero_pow hq.ne_zero] using hyPow)
  have hypos : 0 < y := lt_of_le_of_ne hyNonneg (Ne.symm hy)
  have hX : 1 < |x| := by
    have hyPowOne : (1 : ℤ) ≤ y ^ q := one_le_pow₀ (by omega : (1 : ℤ) ≤ y)
    nlinarith [sq_abs x, abs_nonneg x]
  have hyEven : Even y := by
    by_contra hn
    have hnot : ¬ (2 : ℤ) ∣ y := fun hd => hn (even_iff_two_dvd.mpr hd)
    have hpos : |x| ^ 2 = y ^ q + 1 := by simpa only [sq_abs] using h
    have hneg : (-|x|) ^ 2 = y ^ q + 1 := by simpa only [neg_sq, sq_abs] using h
    obtain ⟨a, _, ha⟩ := cassels_bad_factor 2 q Nat.prime_two hq hq2 |x| y hy hpos hnot
    obtain ⟨b, _, hb⟩ := cassels_bad_factor 2 q Nat.prime_two hq hq2 (-|x|) y hy hneg hnot
    have hb' : |x| + 1 = (-b) ^ q := by rw [ho.neg_pow]; omega
    have haPos : 1 ≤ a := by
      have hpowPos : (0 : ℤ) ^ q < a ^ q := by rw [zero_pow hq.ne_zero]; omega
      have := ho.pow_lt_pow.mp hpowPos
      omega
    have hab : a < -b := ho.pow_lt_pow.mp (by omega)
    have hmon : (a + 1) ^ q ≤ (-b) ^ q := ho.pow_le_pow.mpr (by omega)
    have hgap := cassels_consecutive_gap q a haPos
    have hq3Z : (3 : ℤ) ≤ q := by exact_mod_cast hq3
    omega
  refine ⟨hypos, hyEven, ?_⟩
  have hxsq : Odd (x ^ 2) := by rw [h]; exact (hyEven.pow_of_ne_zero hq.ne_zero).add_one
  exact (Int.odd_pow' (by decide : 2 ≠ 0)).mp hxsq

lemma square_base_q_dvd_x
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 2 = y ^ q + 1) : (q : ℤ) ∣ x := by
  obtain ⟨hypos, hyEven, _⟩ := square_base_positive_even q hq hq2 x y hx hy h
  have ho : Odd q := hq.odd_of_ne_two hq2
  by_contra hqx
  let Q : ℤ := casselsCyclo q (-y)
  have hprod : (y + 1) * Q = x ^ 2 := by
    have hh := int_pow_sub_one_factor q (-y)
    rw [ho.neg_pow] at hh
    change -y ^ q - 1 = (-y - 1) * Q at hh
    nlinarith only [hh, h]
  have hgcd : Int.gcd (y + 1) Q = 1 := by
    rcases gcd_x_sub_one_cyclotomic q hq (-y) with hg | hg
    · have he : -y - 1 = -(y + 1) := by ring
      simpa only [he, Int.neg_gcd, Q] using hg
    · have hqA : (q : ℤ) ∣ y + 1 := by
        have hd := Int.gcd_dvd_left (-y - 1) (casselsCyclo q (-y))
        rw [hg] at hd
        have he : -y - 1 = -(y + 1) := by ring
        rwa [he, dvd_neg] at hd
      have hqpow : (q : ℤ) ∣ x ^ 2 := by
        rw [← hprod]
        exact dvd_mul_of_dvd_left hqA Q
      exact (hqx (cassels_prime_dvd_of_dvd_pow q hq x 2 hqpow)).elim
  obtain ⟨r, hr0, hroot⟩ := Euler.sq_of_nonneg_coprime_product (y + 1) Q x
    (by omega) (Int.isCoprime_iff_gcd_eq_one.mpr hgcd) hprod
  let D : ℕ := y.natAbs
  let u : ℕ := r.natAbs
  have hD : (D : ℤ) = y := by
    dsimp only [D]
    rw [Int.natCast_natAbs, abs_of_nonneg hypos.le]
  have hu : (u : ℤ) = r := by
    dsimp only [u]
    rw [Int.natCast_natAbs, abs_of_nonneg hr0]
  have hDpos : 0 < D := by exact_mod_cast (hD ▸ hypos : (0 : ℤ) < D)
  have hDeven : Even D := hyEven.natAbs
  have hDu : D + 1 = u ^ 2 := by
    have he : (D : ℤ) + 1 = (u : ℤ) ^ 2 := by rw [hD, hu]; exact hroot
    exact_mod_cast he
  have hu1 : 1 < u := by nlinarith only [hDu, hDpos]
  have hcop : u.Coprime D := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    apply Nat.dvd_one.mp
    have hd := Nat.dvd_sub
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_left u D) u) (Nat.gcd_dvd_right u D)
    have he : u * u = D + 1 := by nlinarith only [hDu]
    rwa [he, Nat.add_sub_cancel_left] at hd
  let k : ℕ := (q - 1) / 2
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hkpos : 0 < k := by
    have hodd := Nat.odd_iff.mp ho
    dsimp only [k]
    omega
  have hqk : q = 2 * k + 1 := by
    have hodd := Nat.odd_iff.mp ho
    dsimp only [k]
    omega
  have hnat : x.natAbs ^ 2 = D ^ q + 1 := by
    have he : (x.natAbs : ℤ) ^ 2 = (D : ℤ) ^ q + 1 := by
      rw [Int.natCast_natAbs, sq_abs, hD]
      exact h
    exact_mod_cast he
  have hdiscr : u * u - 1 = D := by
    have he : u * u = D + 1 := by nlinarith only [hDu]
    omega
  have hpow : D ^ q = D * (D ^ k) * (D ^ k) := by
    rw [hqk, pow_succ, Nat.mul_comm 2 k, pow_mul]
    ring
  have hpell : x.natAbs * x.natAbs - (u * u - 1) * (D ^ k) * (D ^ k) = 1 := by
    rw [hdiscr]
    rw [pow_two, hpow] at hnat
    omega
  obtain ⟨n, _, hyn⟩ : ∃ n : ℕ,
      x.natAbs = Pell.xn hu1 n ∧ D ^ k = Pell.yn hu1 n := by
    apply Pell.eq_pell hu1
    change x.natAbs * x.natAbs - (u * u - 1) * (D ^ k) * (D ^ k) = 1
    exact hpell
  have htwo : 2 ∣ Pell.yn hu1 n := by
    rw [← hyn]
    exact even_iff_two_dvd.mp (hDeven.pow_of_ne_zero hkpos.ne')
  have hnEven : 2 ∣ n := Nat.modEq_zero_iff_dvd.mp
    ((Pell.yn_modEq_two hu1 n).symm.trans (Nat.modEq_zero_iff_dvd.mpr htwo))
  have hdiv := (Pell.y_dvd_iff hu1 2 n).mpr hnEven
  have hy2 : Pell.yn hu1 2 = 2 * u := by
    simpa only [Pell.xn_one, Pell.yn_one, one_mul, two_mul] using Pell.yn_succ hu1 1
  rw [hy2, ← hyn] at hdiv
  have hudvd : u ∣ D ^ k := (dvd_mul_left u 2).trans hdiv
  have hueq : u = 1 := Nat.eq_one_of_dvd_coprimes (hcop.pow_right k) dvd_rfl hudvd
  omega

end Catalan.KoChao
