module

public import Mathlib

/-!
# `Catalan.Classical.KoChao.Inequalities`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan.KoChao

lemma integer_square_gap (b c : ℤ) (h : b ^ 2 ≠ c ^ 2) :
    2 * |b| - 1 ≤ |b ^ 2 - c ^ 2| := by
  have hne : |b| ≠ |c| := by
    intro he
    apply h
    calc
      b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ = |c| ^ 2 := by rw [he]
      _ = c ^ 2 := sq_abs c
  have hb := abs_nonneg b
  have hc := abs_nonneg c
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm : 0 ≤ (|c| - |b| - 1) * (|c| + |b| + 1) :=
      mul_nonneg (by omega) (by omega)
    have hsq : b ^ 2 ≤ c ^ 2 := by nlinarith [sq_abs b, sq_abs c]
    rw [abs_of_nonpos (by omega : b ^ 2 - c ^ 2 ≤ 0)]
    nlinarith [sq_abs b, sq_abs c]
  · have hm : 0 ≤ (|b| - |c| - 1) * (|b| + |c| - 1) :=
      mul_nonneg (by omega) (by omega)
    have hsq : c ^ 2 ≤ b ^ 2 := by nlinarith [sq_abs b, sq_abs c]
    rw [abs_of_nonneg (by omega : 0 ≤ b ^ 2 - c ^ 2)]
    nlinarith [sq_abs b, sq_abs c]

lemma oriented_factor_abs_lt
    (q : ℕ) (hq : 5 ≤ q) (z a b : ℤ) (hb : b ≠ 0)
    (hminus : z - 1 = 2 ^ (q - 1) * a ^ q)
    (hplus : z + 1 = 2 * b ^ q) : |a| < |b| := by
  have h2 : (16 : ℤ) ≤ 2 ^ (q - 1) := by
    calc
      (16 : ℤ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (q - 1) := by
        have hq4 : 4 ≤ q - 1 := by omega
        exact pow_le_pow_right₀ (by norm_num) hq4
  have haPow : 2 ^ (q - 1) * |a| ^ q = |z - 1| := by
    rw [hminus, abs_mul, abs_pow, abs_pow]
    norm_num
  have hbPow : 2 * |b| ^ q = |z + 1| := by
    rw [hplus, abs_mul, abs_pow]
    norm_num
  have hbpos : 0 < |b| ^ q := pow_pos (abs_pos.mpr hb) q
  have hz1 : 1 ≤ |z + 1| := by omega
  have htri : |z - 1| ≤ |z + 1| + 2 := by
    calc
      |z - 1| = |(z + 1) + (-2)| := by congr 1; ring
      _ ≤ |z + 1| + |(-2 : ℤ)| := abs_add_le _ _
      _ = |z + 1| + 2 := by norm_num
  have hscaled := mul_le_mul_of_nonneg_right h2 (pow_nonneg (abs_nonneg a) q)
  have hpow : |a| ^ q < |b| ^ q := by nlinarith
  by_contra! hab
  have hpow' : |b| ^ q ≤ |a| ^ q := by gcongr
  omega

lemma oriented_difference_not_square
    (q : ℕ) (hq : 5 ≤ q) (z a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hminus : z - 1 = 2 ^ (q - 1) * a ^ q)
    (hplus : z + 1 = 2 * b ^ q) : ¬ ∃ c : ℤ, b ^ 2 - 2 * a = c ^ 2 := by
  rintro ⟨c, hc⟩
  have hne : b ^ 2 ≠ c ^ 2 := by intro he; apply ha; omega
  have hgap := integer_square_gap b c hne
  have he : b ^ 2 - c ^ 2 = 2 * a := by omega
  rw [he, abs_mul] at hgap
  norm_num at hgap
  have hlt := oriented_factor_abs_lt q hq z a b hb hminus hplus
  omega

lemma oriented_square_identity
    (q : ℕ) (hq : 0 < q) (z a b : ℤ)
    (hminus : z - 1 = 2 ^ (q - 1) * a ^ q)
    (hplus : z + 1 = 2 * b ^ q) :
    (b ^ 2) ^ q - (2 * a) ^ q = (b ^ q - 2) ^ 2 := by
  have h2pow : (2 : ℤ) ^ q = 2 * 2 ^ (q - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ q from hq), pow_succ]
    ring
  have h2a : (2 * a) ^ q = 4 * b ^ q - 4 := by
    rw [mul_pow, h2pow]
    nlinarith only [hminus, hplus]
  have hb2 : (b ^ 2) ^ q = (b ^ q) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h2a, hb2]
  ring

end Catalan.KoChao
