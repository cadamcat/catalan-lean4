import Catalan.Classical.Lebesgue.Gaussian
import Catalan.Classical.Lebesgue.Normalize
import Catalan.Classical.Lebesgue.RealPart

set_option autoImplicit false
namespace Catalan.Lebesgue

lemma exists_gaussian_root_of_solution
    (p : ℕ) (hp : Odd p) (x y : ℤ) (hy : Even y)
    (h : x ^ p = y ^ 2 + 1) :
    ∃ z : GaussianInt, z ^ p = (⟨1, y⟩ : GaussianInt) := by
  have hprod : (⟨1, y⟩ : GaussianInt) * (⟨1, -y⟩ : GaussianInt) = (x : GaussianInt) ^ p := by
    rw [← Int.cast_pow, h]
    ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] <;> ring
  obtain ⟨z, u, hu⟩ := exists_associated_pow_of_mul_eq_pow'
    (gaussian_conjugate_coprime_of_even y hy) hprod
  obtain ⟨w, hw⟩ := gaussian_unit_pow_surjective p hp u
  refine ⟨z * (w : GaussianInt), ?_⟩
  rw [mul_pow, ← Units.val_pow_eq_pow_val, hw, hu]

end Catalan.Lebesgue

namespace Catalan

theorem lebesgue_q_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ p ≠ y ^ 2 + 1 := by
  intro h
  obtain ⟨hyeven, _⟩ := Lebesgue.lebesgue_solution_parity p hp hp2 x y h
  obtain ⟨z, hz⟩ := Lebesgue.exists_gaussian_root_of_solution p (hp.odd_of_ne_two hp2) x y hyeven h
  obtain ⟨v, hv, hv0, hshape⟩ := Lebesgue.gaussian_root_normalization p hp hp2 y hyeven hy z hz
  apply Lebesgue.gaussian_even_imag_real_ne_one p hp hp2 v hv hv0
  have hre := congrArg Zsqrtd.re hz
  simpa only [hshape] using hre

end Catalan

