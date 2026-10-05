module

public import Catalan.IdealAction

/-! Compatibility of the fractional-ideal action with multiplication of automorphisms. -/
/-!
# `Catalan.IdealAction.Composition`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace Catalan
variable (K : Type*) [Field K] [NumberField K]

lemma integerAut_mul (s t : K ≃ₐ[ℚ] K) :
    (integerAut K (s * t)).toRingHom =
      (integerAut K s).toRingHom.comp (integerAut K t).toRingHom := by
  ext x
  rfl

lemma fractionalAut_mul (s t : K ≃ₐ[ℚ] K) :
    fractionalAut K (s * t) = (fractionalAut K s).comp (fractionalAut K t) := by
  unfold fractionalAut
  rw [FractionalIdeal.extendedHom'_comp]
  congr 1

lemma idealAct_comp (s t : K ≃ₐ[ℚ] K) (J : FracIdealUnit K) :
    idealAct K (s * t) J = idealAct K s (idealAct K t J) := by
  apply Units.ext
  change fractionalAut K (s * t) (J : FracIdeal K) =
    fractionalAut K s (fractionalAut K t (J : FracIdeal K))
  rw [fractionalAut_mul]
  rfl

variable (p : ℕ)
lemma ipow_mul_single_int (J : FracIdealUnit K) (s : G p K) (m : ℤ) (Θ : R p K) :
    ipow p K J (MonoidAlgebra.single s m * Θ) =
      (idealAct K s (ipow p K J Θ)) ^ m := by
  refine MonoidAlgebra.induction_linear Θ ?_ ?_ ?_
  · simp only [mul_zero, ipow_zero, map_one, one_zpow]
  · intro Θ Ψ hΘ hΨ
    rw [mul_add, ipow_add, hΘ, hΨ, ipow_add, map_mul, mul_zpow]
  · intro t n
    rw [MonoidAlgebra.single_mul_single, ipow_single, ipow_single, map_zpow,
      ← idealAct_comp, mul_comm m n, zpow_mul]

lemma ipow_mul_single (J : FracIdealUnit K) (s : G p K) (Θ : R p K) :
    ipow p K J (MonoidAlgebra.single s 1 * Θ) = idealAct K s (ipow p K J Θ) := by
  simpa only [zpow_one] using ipow_mul_single_int K p J s 1 Θ

lemma ipow_exponent_mul (J : FracIdealUnit K) (A Θ : R p K) :
    ipow p K J (A * Θ) = ipow p K (ipow p K J Θ) A := by
  refine MonoidAlgebra.induction_linear A ?_ ?_ ?_
  · simp only [zero_mul, ipow_zero]
  · intro A B hA hB
    rw [add_mul, ipow_add, hA, hB, ipow_add]
  · intro s m
    rw [ipow_mul_single_int, ipow_single]

lemma ipow_neg (J : FracIdealUnit K) (Θ : R p K) :
    ipow p K J (-Θ) = (ipow p K J Θ)⁻¹ :=
  (ipowAddHom p K J).map_neg Θ

lemma ipow_sub (J : FracIdealUnit K) (A Θ : R p K) :
    ipow p K J (A - Θ) = ipow p K J A / ipow p K J Θ := by
  rw [sub_eq_add_neg, ipow_add, ipow_neg, div_eq_mul_inv]

end Catalan
