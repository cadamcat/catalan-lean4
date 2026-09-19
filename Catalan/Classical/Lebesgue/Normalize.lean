import Catalan.Classical.Lebesgue.Coordinates

namespace Catalan.Lebesgue

lemma gaussian_root_normalization
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (y : ℤ) (hy : Even y) (hy0 : y ≠ 0)
    (z : GaussianInt) (hz : z ^ p = (⟨1, y⟩ : GaussianInt)) :
    ∃ v : ℤ, Even v ∧ v ≠ 0 ∧ z = (⟨1, v⟩ : GaussianInt)
 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hdiv : z.re ∣ (1 : ℤ) := by
    simpa only [hz] using gaussian_re_dvd_re_pow_odd z p hpodd
  have hrepm : z.re = 1 ∨ z.re = -1 := Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr hdiv)
  have hre2 : z.re ^ 2 = 1 := by
    rcases hrepm with h | h <;> simp [h]
  have hnormpow : z.norm ^ p = 1 + y ^ 2 := by
    calc
      z.norm ^ p = (z ^ p).norm :=
        (map_pow (Zsqrtd.normMonoidHom : GaussianInt →* ℤ) z p).symm
      _ = (⟨1, y⟩ : GaussianInt).norm := congrArg Zsqrtd.norm hz
      _ = 1 + y ^ 2 := by simp [Zsqrtd.norm_def, pow_two]
  have hnormodd : Odd z.norm := by
    apply (Int.odd_pow' hp.ne_zero).mp
    rw [hnormpow]
    exact (hy.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)).one_add
  have hnorm : z.norm = 1 + z.im ^ 2 := by
    rw [Zsqrtd.norm_def]
    nlinarith only [hre2]
  have him2 : Even (z.im ^ 2) := by
    rw [hnorm] at hnormodd
    exact (Int.odd_add.mp hnormodd).mp odd_one
  have him : Even z.im := by
    by_contra h
    have ho : Odd z.im := Int.not_even_iff_odd.mp h
    exact (Int.not_even_iff_odd.mpr (ho.pow (n := 2))) him2
  have hre : z.re = 1 := by
    rcases hrepm with h | h
    · exact h
    · have hm := gaussian_re_pow_mod_four_of_even_im z him p
      rw [hz, h, hpodd.neg_one_pow] at hm
      norm_num [Int.ModEq] at hm
  refine ⟨z.im, him, ?_, ?_⟩
  · intro hi0
    have hz1 : z = 1 := by
      apply Zsqrtd.ext
      · exact hre
      · exact hi0
    rw [hz1, one_pow] at hz
    have hy1 := congrArg Zsqrtd.im hz
    exact hy0 (by simpa using hy1.symm)
  · exact Zsqrtd.ext hre rfl

end Catalan.Lebesgue

