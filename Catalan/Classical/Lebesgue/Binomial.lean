import Mathlib

set_option autoImplicit false
namespace Catalan.Lebesgue
open scoped BigOperators

private def gaussianRe : GaussianInt →+ ℤ where
  toFun z := z.re
  map_zero' := rfl
  map_add' _ _ := rfl

lemma gaussian_imag_pow_even (v : ℤ) (j : ℕ) :
    (⟨0, v⟩ : GaussianInt) ^ (2 * j) = (((-1 : ℤ) ^ j * v ^ (2 * j) : ℤ) : GaussianInt) := by
  have hsq : (⟨0, v⟩ : GaussianInt) ^ 2 = ((-v ^ 2 : ℤ) : GaussianInt) := by
    ext <;> simp [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]
  rw [pow_mul, hsq, ← Int.cast_pow]
  congr 1
  rw [neg_pow, pow_mul]

lemma gaussian_imag_pow_odd_re (v : ℤ) (j : ℕ) :
    ((⟨0, v⟩ : GaussianInt) ^ (2 * j + 1)).re = 0 := by
  rw [pow_succ, gaussian_imag_pow_even]
  simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, zero_mul, add_zero]

lemma gaussian_imag_pow_re (v : ℤ) (k : ℕ) :
    ((⟨0, v⟩ : GaussianInt) ^ k).re =
      if Even k then (-1 : ℤ) ^ (k / 2) * v ^ k else 0 := by
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨j, hj⟩ := he
    have hk : k = 2 * j := by omega
    rw [hk, gaussian_imag_pow_even, if_pos (even_two_mul j)]
    have hd : 2 * j / 2 = j := by omega
    simp only [Zsqrtd.re_intCast, hd]
  · obtain ⟨j, hj⟩ := ho
    have hk : k = 2 * j + 1 := by omega
    rw [hk, gaussian_imag_pow_odd_re, if_neg (by
      intro hEven
      obtain ⟨t, ht⟩ := hEven
      omega : ¬Even (2 * j + 1))]

lemma gaussian_re_binomial (v : ℤ) (p : ℕ) :
    ((⟨1, v⟩ : GaussianInt) ^ p).re =
      ∑ j ∈ Finset.range (p / 2 + 1), (-1 : ℤ) ^ j * (p.choose (2 * j) : ℤ) * v ^ (2 * j) := by
  classical
  have hz : (⟨1, v⟩ : GaussianInt) = (⟨0, v⟩ : GaussianInt) + 1 := by ext <;> simp
  have hfull : ((⟨1, v⟩ : GaussianInt) ^ p).re =
      ∑ k ∈ Finset.range (p + 1), ((⟨0, v⟩ : GaussianInt) ^ k).re * (p.choose k : ℤ) := by
    change gaussianRe ((⟨1, v⟩ : GaussianInt) ^ p) = _
    rw [hz, add_pow, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (((⟨0, v⟩ : GaussianInt) ^ k * (1 : GaussianInt) ^ (p - k) * (p.choose k : GaussianInt))).re = _
    simp
  rw [hfull]
  have hfiltered :
      (∑ k ∈ Finset.range (p + 1), ((⟨0, v⟩ : GaussianInt) ^ k).re * (p.choose k : ℤ)) =
      ∑ k ∈ (Finset.range (p + 1)).filter Even,
        (-1 : ℤ) ^ (k / 2) * v ^ k * (p.choose k : ℤ) := by
    simp only [Finset.sum_filter, gaussian_imag_pow_re, ite_mul, zero_mul]
  rw [hfiltered]
  symm
  refine Finset.sum_bij (fun j _ => 2 * j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨by omega, even_two_mul j⟩
  · intro i hi j hj hij
    omega
  · intro k hk
    obtain ⟨hklt, j, hj⟩ := Finset.mem_filter.mp hk
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_range] at hklt ⊢
      omega
    · omega
  · intro j _
    have hj : 2 * j / 2 = j := by omega
    rw [hj]
    ring

end Catalan.Lebesgue
