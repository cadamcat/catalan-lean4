module

public import Mathlib

/-!
# `Catalan.Classical.Lebesgue.Gaussian`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan.Lebesgue

lemma lebesgue_solution_parity
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x y : ℤ)
    (h : x ^ p = y ^ 2 + 1) : Even y ∧ Odd x := by
  have hpgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have odd_not_even : ∀ z : ℤ, Odd z → Even z → False := by
    intro z ho he
    obtain ⟨a, ha⟩ := ho
    obtain ⟨b, hb⟩ := he
    omega
  have hy : Even y := by
    by_contra hye
    have hyodd : Odd y := (Int.even_or_odd y).resolve_left hye
    have hy2odd : Odd (y ^ 2) := by simpa only [pow_two] using hyodd.mul hyodd
    have hrhs : Even (y ^ 2 + 1) := hy2odd.add_one
    have hxpow : Even (x ^ p) := by
      rw [h]
      exact hrhs
    have hx_even : Even x := by
      by_contra hxe
      have hxodd : Odd x := (Int.even_or_odd x).resolve_left hxe
      exact odd_not_even (x ^ p) (hxodd.pow) hxpow
    obtain ⟨kx, hkx⟩ := hx_even
    obtain ⟨ky, hky⟩ := hyodd
    have hfour : (4 : ℤ) ∣ x ^ p := by
      refine ⟨x ^ (p - 2) * kx ^ 2, ?_⟩
      calc
        x ^ p = x ^ ((p - 2) + 2) :=
          congrArg (fun r : ℕ => x ^ r) (Nat.sub_add_cancel hpgt.le).symm
        _ = x ^ (p - 2) * x ^ 2 := pow_add x (p - 2) 2
        _ = 4 * (x ^ (p - 2) * kx ^ 2) := by rw [hkx]; ring
    obtain ⟨m, hm⟩ := hfour
    rw [h] at hm
    rw [hky] at hm
    have hmod : 4 * (ky ^ 2 + ky) + 2 = 4 * m := by
      nlinarith [hm]
    omega
  have hxpow : Odd (x ^ p) := by
    have hy2 : Even (y ^ 2) := by
      simpa only [pow_two] using hy.mul_left y
    rw [h]
    exact hy2.add_one
  have hx : Odd x := by
    by_contra hxo
    have hxe : Even x := (Int.even_or_odd x).resolve_right hxo
    have hpone : 1 ≤ p := hp.one_le
    have hxpow_even : Even (x ^ p) := by
      have he := Even.mul_left hxe (x ^ (p - 1))
      simpa only [← pow_succ, Nat.sub_add_cancel hpone] using he
    exact odd_not_even (x ^ p) hxpow hxpow_even
  exact ⟨hy, hx⟩

lemma gaussian_conjugate_coprime_of_even (y : ℤ) (hy : Even y) :
    IsCoprime (⟨1, y⟩ : GaussianInt) (⟨1, -y⟩ : GaussianInt) := by
  obtain ⟨k, hk⟩ := hy
  refine ⟨⟨1, -k⟩, ⟨0, -k⟩, ?_⟩
  subst y
  ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  all_goals ring

lemma gaussian_unit_pow_four (u : GaussianIntˣ) : u ^ 4 = 1 := by
  have hnorm : (u : GaussianInt).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) (u : GaussianInt)).mpr u.isUnit
  have hre_bound : -1 ≤ (u : GaussianInt).re ∧ (u : GaussianInt).re ≤ 1 := by
    rw [Zsqrtd.norm_def] at hnorm
    constructor <;> nlinarith [sq_nonneg (u : GaussianInt).re,
      sq_nonneg (u : GaussianInt).im]
  have him_bound : -1 ≤ (u : GaussianInt).im ∧ (u : GaussianInt).im ≤ 1 := by
    rw [Zsqrtd.norm_def] at hnorm
    constructor <;> nlinarith [sq_nonneg (u : GaussianInt).re,
      sq_nonneg (u : GaussianInt).im]
  have hre : (u : GaussianInt).re = -1 ∨ (u : GaussianInt).re = 0 ∨
      (u : GaussianInt).re = 1 := by omega
  have him : (u : GaussianInt).im = -1 ∨ (u : GaussianInt).im = 0 ∨
      (u : GaussianInt).im = 1 := by omega
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one]
  rcases hre with hre | hre | hre <;> rcases him with him | him | him
  all_goals
    try
      rw [Zsqrtd.norm_def, hre, him] at hnorm
      norm_num at hnorm
  all_goals
    change ((⟨(u : GaussianInt).re, (u : GaussianInt).im⟩ : GaussianInt) ^ 4) = 1
    rw [hre, him]
    ext <;> simp [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]

lemma gaussian_unit_pow_surjective (n : ℕ) (hn : Odd n)
    (u : GaussianIntˣ) : ∃ v : GaussianIntˣ, v ^ n = u := by
  have horder : orderOf u ∣ 4 := orderOf_dvd_of_pow_eq_one
    (gaussian_unit_pow_four u)
  have hcop4 : n.Coprime 4 := by
    have hcop4' := Nat.Coprime.pow_right 2 hn.coprime_two_left.symm
    norm_num at hcop4'
    exact hcop4'
  have hcop : n.Coprime (orderOf u) := Nat.Coprime.of_dvd_right horder hcop4
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨u ^ m, ?_⟩
  calc
    (u ^ m) ^ n = u ^ (m * n) := (pow_mul u m n).symm
    _ = u ^ (n * m) := by rw [Nat.mul_comm]
    _ = (u ^ n) ^ m := pow_mul u n m
    _ = u := hm

end Catalan.Lebesgue
