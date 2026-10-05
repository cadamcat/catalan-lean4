module

public import Mathlib

/-!
# `Catalan.Stickelberger.CharacterRecovery`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace Catalan

lemma unit_character_recovery (p : ℕ) [Fact p.Prime]
    (c : (ZMod p)ˣ → ℂ) (b : (ZMod p)ˣ) :
    (∑ χ : DirichletCharacter ℂ p, χ ((b : ZMod p)⁻¹) *
      (∑ a : (ZMod p)ˣ, c a * χ (a : ZMod p))) =
      (Nat.totient p : ℂ) * c b := by
  classical
  calc
    _ = ∑ a : (ZMod p)ˣ, c a *
        (∑ χ : DirichletCharacter ℂ p, χ ((b : ZMod p)⁻¹) * χ (a : ZMod p)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = ∑ a : (ZMod p)ˣ, c a *
        (if (b : ZMod p) = (a : ZMod p) then (Nat.totient p : ℂ) else 0) := by
      simp_rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ b.isUnit]
    _ = _ := by simp [Units.val_inj, mul_comm]

lemma unit_character_transform_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective
      (fun c : (ZMod p)ˣ → ℂ => fun χ : DirichletCharacter ℂ p =>
        ∑ a : (ZMod p)ˣ, c a * χ (a : ZMod p)) := by
  intro c d h
  funext b
  have he := congrArg (fun f : DirichletCharacter ℂ p → ℂ =>
    ∑ χ : DirichletCharacter ℂ p, χ ((b : ZMod p)⁻¹) * f χ) h
  change (∑ χ : DirichletCharacter ℂ p, χ ((b : ZMod p)⁻¹) *
      (∑ a : (ZMod p)ˣ, c a * χ (a : ZMod p))) =
    (∑ χ : DirichletCharacter ℂ p, χ ((b : ZMod p)⁻¹) *
      (∑ a : (ZMod p)ˣ, d a * χ (a : ZMod p))) at he
  rw [unit_character_recovery, unit_character_recovery] at he
  have hφ : (Nat.totient p : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Fact.out : p.Prime).pos).ne'
  exact mul_left_cancel₀ hφ he

end Catalan
