import Mathlib

namespace Catalan.Lebesgue

lemma gaussian_re_dvd_re_pow_odd (z : GaussianInt) (n : ℕ) (hn : Odd n) :
    z.re ∣ (z ^ n).re
 := by
  obtain ⟨k, rfl⟩ := hn
  induction k with
  | zero => simp
  | succ k ih =>
      have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      have hrec : (z ^ (2 * (k + 1) + 1)).re =
          (z ^ (2 * k + 1)).re * (z.re ^ 2 - z.im ^ 2) -
            (z ^ (2 * k + 1)).im * (2 * z.re * z.im) := by
        rw [he, pow_add, pow_two]
        simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
        ring
      obtain ⟨t, ht⟩ := ih
      rw [hrec, ht]
      refine ⟨t * (z.re ^ 2 - z.im ^ 2) - 2 * (z ^ (2 * k + 1)).im * z.im, ?_⟩
      ring

lemma gaussian_re_pow_mod_four_of_even_im
    (z : GaussianInt) (hz : Even z.im) (n : ℕ) :
    (z ^ n).re ≡ z.re ^ n [ZMOD 4]
 := by
  have him (k : ℕ) : Even (z ^ k).im := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Zsqrtd.im_mul]
        exact (hz.mul_left _).add (ih.mul_right _)
  induction n with
  | zero => simp
  | succ n ih =>
      have hcross : (4 : ℤ) ∣ (z ^ n).im * z.im := by
        obtain ⟨r, hr⟩ := (even_iff_two_dvd.mp (him n))
        obtain ⟨s, hs⟩ := (even_iff_two_dvd.mp hz)
        refine ⟨r * s, ?_⟩
        rw [hr, hs]
        ring
      rw [Int.modEq_iff_dvd] at ih ⊢
      simp only [pow_succ, Zsqrtd.re_mul]
      have he : z.re ^ n * z.re -
          ((z ^ n).re * z.re + (-1) * (z ^ n).im * z.im) =
          (z.re ^ n - (z ^ n).re) * z.re + (z ^ n).im * z.im := by ring
      rw [he]
      exact dvd_add (dvd_mul_of_dvd_left ih _) hcross

end Catalan.Lebesgue

