module

public import Catalan.Stickelberger.CharacterEvaluation
public import Catalan.Stickelberger.CharacterHalfBasis
public import Catalan.Stickelberger.CharacterSpanTransfer

/-!
# `Catalan.Stickelberger.MinusIndependent`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.MinusIndependence
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma thetaVector_linearIndependent : LinearIndependent ℂ (thetaVector p K) := by
  let f : ComplexRing p K →ₗ[ℂ] ComplexRing p K :=
    LinearMap.mulLeft ℂ (complexPTheta p K)
  have hhalf : Submodule.span ℂ (Set.range (halfVector p K)) ≤ minusRange p K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact halfVector_mem_minusRange p K i
  have hf : Set.InjOn f (Submodule.span ℂ (Set.range (halfVector p K))) := by
    intro x hx y hy hxy
    apply sub_eq_zero.mp
    apply complexPTheta_mul_eq_zero p K (x - y)
      ((minusRange p K).sub_mem (hhalf hx) (hhalf hy))
    change complexPTheta p K * x = complexPTheta p K * y at hxy
    rw [mul_sub, hxy, sub_self]
  have hprod : LinearIndependent ℂ (fun i => complexPTheta p K * halfVector p K i) :=
    (halfVector_linearIndependent p K).map_injOn f hf
  have hle :
      Submodule.span ℂ (Set.range (fun i => complexPTheta p K * halfVector p K i)) ≤
        Submodule.span ℂ (Set.range (thetaVector p K)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact complexPTheta_mul_halfVector_mem_span p K i
  have instThetaSpanFinite :
      Module.Finite ℂ (Submodule.span ℂ (Set.range (thetaVector p K))) :=
    Module.Finite.span_of_finite ℂ (Set.finite_range (thetaVector p K))
  apply linearIndependent_iff_card_le_finrank_span.mpr
  calc
    Fintype.card (Fin ((p - 1) / 2)) =
        Module.finrank ℂ (Submodule.span ℂ
          (Set.range (fun i => complexPTheta p K * halfVector p K i))) :=
      (finrank_span_eq_card hprod).symm
    _ ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range (thetaVector p K))) :=
      Submodule.finrank_mono hle

end Catalan.MinusIndependence

namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

theorem θminus_linIndep : Function.Injective (fun c : Fin ((p - 1) / 2) → ℤ => ∑ k, c k • θminus p K (k + 1)) := by
  intro c d h
  have he := congrArg (MinusIndependence.coeffCast p K) h
  have heC :
      Fintype.linearCombination ℂ (MinusIndependence.thetaVector p K) (fun i => (c i : ℂ)) =
        Fintype.linearCombination ℂ (MinusIndependence.thetaVector p K) (fun i => (d i : ℂ)) := by
    simpa only [Fintype.linearCombination_apply, MinusIndependence.thetaVector,
      map_sum, map_zsmul, Int.cast_smul_eq_zsmul] using he
  have hcoeff := (MinusIndependence.thetaVector_linearIndependent p K).fintypeLinearCombination_injective heC
  funext i
  have hi := congrFun hcoeff i
  exact_mod_cast hi

end Catalan
