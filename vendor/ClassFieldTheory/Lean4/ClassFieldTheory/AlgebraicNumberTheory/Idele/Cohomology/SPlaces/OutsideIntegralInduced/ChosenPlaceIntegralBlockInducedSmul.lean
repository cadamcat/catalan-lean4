/-
MODIFIED FROM UPSTREAM:
n-yamaguchi-0729/ClassFieldTheory commit 7713795234690681b4406ae198b07aa95e82716a.
Added Lean module-system visibility declarations and ported this file to Mathlib/Lean v4.35.0-rc3.
-/
module

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion


@[expose] public section

set_option autoImplicit false

/-!
# Equivariance of the induced integral block

This file proves that the inclusion of the chosen integral induced block is
equivariant for the global Galois action.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

omit [NumberField L] in
/-- The embedding of the chosen integral induced block is equivariant for
the full global Galois action. -/
theorem chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_smul
    (w₀ : HeightOneSpectrum (𝓞 K))
    (τ : L ≃ₐ[K] L) :
    ∀ f : ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀,
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
        (K := K) (L := L) w₀
        ((chosenFinitePlaceInducedIntegerUnitsAction
          (K := K) (L := L) w₀).smul τ f) =
      (chosenFinitePlaceLocalPlaceBlockAction
        (K := K) (L := L) w₀).smul τ
        (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
          (K := K) (L := L) w₀ f) := by
  intro f
  rfl

end ChosenFinitePlace
