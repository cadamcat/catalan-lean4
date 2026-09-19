import Catalan.Stickelberger.CharacterLZero
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

set_option autoImplicit false
open scoped BigOperators
namespace Catalan

lemma LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero
    (hzero : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      HurwitzZeta.hurwitzZeta (t : UnitAddCircle) 0 = (1 / 2 : ℂ) - (t : ℂ))
    (p : ℕ) [hp : Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 =
      -(∑ a : ZMod p, (a.val : ℂ) * χ a) / (p : ℂ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  calc
    DirichletCharacter.LFunction χ 0 =
        ∑ a : ZMod p, χ a * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ)) := by
      simp only [DirichletCharacter.LFunction, ZMod.LFunction, neg_zero,
        Complex.cpow_zero, one_mul]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = 0
      · simp only [ha, χ.map_zero' hp.out.ne_one, zero_mul]
      · have haR : (0 : ℝ) < a.val := by exact_mod_cast ZMod.val_pos.mpr ha
        have haLt : (a.val : ℝ) < p := by exact_mod_cast ZMod.val_lt a
        have ht : (a.val : ℝ) / p ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨div_pos haR hpR, (div_lt_one hpR).mpr haLt⟩
        rw [ZMod.toAddCircle_apply, hzero _ ht]
        simp only [Complex.ofReal_div, Complex.ofReal_natCast]
    _ = (∑ a : ZMod p, χ a) / 2 -
        (∑ a : ZMod p, (a.val : ℂ) * χ a) / (p : ℂ) := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = -(∑ a : ZMod p, (a.val : ℂ) * χ a) / (p : ℂ) := by
      rw [χ.sum_eq_zero_of_ne_one hχ]
      ring

lemma odd_character_weighted_sum_ne_zero_of_hurwitz_zero
    (hzero : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      HurwitzZeta.hurwitzZeta (t : UnitAddCircle) 0 = (1 / 2 : ℂ) - (t : ℂ))
    (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) (hodd : χ.Odd) :
    (∑ a : ZMod p, (a.val : ℂ) * χ a) ≠ 0 := by
  intro hs
  have hL := LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero hzero p χ hχ
  rw [hs, neg_zero, zero_div] at hL
  exact LFunction_zero_ne_zero_of_prime_odd p χ hχ hodd hL

end Catalan
