import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma epsilon_inverse_root {K : Type*} [Field K]
    (z w : K) (hz : z ≠ 0) (hw : w ≠ 0) (a : ℕ) (m : ℤ)
    (hm : z ^ (2 * m + (a : ℤ) - 1) = 1) :
    (z⁻¹) ^ m * ((z⁻¹) ^ a - w) / (z⁻¹ - w) =
      z ^ m * (z ^ a - w⁻¹) / (z - w⁻¹) := by
  by_cases hzw : z * w = 1
  · have hwz : w = z⁻¹ := by
      exact eq_inv_of_mul_eq_one_right hzw
    simp [hwz]
  · have hden1 : z⁻¹ - w ≠ 0 := by
      intro h
      apply hzw
      have h' := congrArg (fun x : K => z * x) h
      have h'' : 1 - z * w = 0 := by simpa [mul_sub, hz] using h'
      exact (sub_eq_zero.mp h'').symm
    have hden2 : z - w⁻¹ ≠ 0 := by
      intro h
      apply hzw
      have h' := congrArg (fun x : K => x * w) h
      have h'' : z * w - 1 = 0 := by simpa [sub_mul, hw] using h'
      exact sub_eq_zero.mp h''
    have hzw1 : 1 - w * z ≠ 0 := by
      intro h
      apply hzw
      have := sub_eq_zero.mp h
      simpa [mul_comm] using this.symm
    have hzw2 : -1 + w * z ≠ 0 := by
      intro h
      apply hzw
      have := add_eq_zero_iff_eq_neg.mp h
      simpa [mul_comm] using this.symm
    have hzexp : z ^ ((1 : ℤ) - (a : ℤ) - 2 * m) = 1 := by
      have he : (1 : ℤ) - (a : ℤ) - 2 * m =
          -(2 * m + (a : ℤ) - 1) := by ring
      rw [he, zpow_neg, hm, inv_one]
    have hzm : (z⁻¹) ^ m = z ^ (-m) := by simp
    have hza : (z⁻¹) ^ a = z ^ (-(a : ℤ)) := by simp [zpow_natCast]
    have hcancel : z ^ (-(a : ℤ)) * z ^ a = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hz]
      simp
    have hkey : z * z ^ (-m) * z ^ (-(a : ℤ)) = z ^ m := by
      have hcomb : z * z ^ (-m) * z ^ (-(a : ℤ)) = z ^ (1 - m - (a : ℤ)) := by
        calc
          z * z ^ (-m) * z ^ (-(a : ℤ)) =
              z ^ (1 : ℤ) * z ^ (-m) * z ^ (-(a : ℤ)) := by simp
          _ = z ^ (1 + -m) * z ^ (-(a : ℤ)) := by
            rw [← zpow_add₀ hz 1 (-m)]
          _ = z ^ ((1 + -m) + -(a : ℤ)) := by
            rw [← zpow_add₀ hz (1 + -m) (-(a : ℤ))]
          _ = z ^ (1 - m - (a : ℤ)) := by congr 1
      have hrewrite : (1 : ℤ) - m - (a : ℤ) =
          m + (1 - (a : ℤ) - 2 * m) := by ring
      rw [hcomb, hrewrite, zpow_add₀ hz, hzexp, mul_one]
    have hkey' : z ^ (-m) * z ^ (-(a : ℤ)) * z = z ^ m := by
      calc
        z ^ (-m) * z ^ (-(a : ℤ)) * z = z * z ^ (-m) * z ^ (-(a : ℤ)) := by ring
        _ = z ^ m := hkey
    have hrelm : z ^ (-m) * z = z ^ a * z ^ m := by
      calc
        z ^ (-m) * z = (z ^ (-m) * z) * 1 := by rw [mul_one]
        _ = (z ^ (-m) * z) * (z ^ (-(a : ℤ)) * z ^ a) := by rw [hcancel]
        _ = (z * z ^ (-m) * z ^ (-(a : ℤ))) * z ^ a := by ring
        _ = z ^ m * z ^ a := by rw [hkey]
        _ = z ^ a * z ^ m := by ring
    rw [hzm, hza]
    apply (div_eq_div_iff hden1 hden2).2
    field_simp [hz, hw]
    linear_combination (w * z - 1) * hkey' + (w - w ^ 2 * z) * hrelm

lemma epsilon_pair_inverse_root {K : Type*} [Field K]
    (z w : K) (hz : z ≠ 0) (hw : w ≠ 0) (a : ℕ) (m : ℤ)
    (hm : z ^ (2 * m + (a : ℤ) - 1) = 1) :
    ((z⁻¹) ^ m * ((z⁻¹) ^ a - w) / (z⁻¹ - w)) *
        ((z⁻¹) ^ m * ((z⁻¹) ^ a - w⁻¹) / (z⁻¹ - w⁻¹)) =
      (z ^ m * (z ^ a - w) / (z - w)) *
        (z ^ m * (z ^ a - w⁻¹) / (z - w⁻¹)) := by
  rw [epsilon_inverse_root z w hz hw a m hm]
  rw [epsilon_inverse_root z w⁻¹ hz (inv_ne_zero hw) a m hm]
  simp only [inv_inv]
  ring

end Catalan.Thaine
