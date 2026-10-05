module

public import Catalan.Density.Definitions

/-!
# `Catalan.Density.BaseFields`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

local instance instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega :=
  AlgebraicClosure.isAlgebraic ℚ

instance instFiniteDimensionalF (p : ℕ) : FiniteDimensional ℚ (F p) := by
  unfold F Fsub
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral

instance instNumberFieldF (p : ℕ) : NumberField (F p) := {}

instance instFiniteDimensionalB (p q : ℕ) : FiniteDimensional (F p) (Bsub p q) := by
  unfold Bsub
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral.tower_top

instance instNumberFieldB (p q : ℕ) : NumberField (Bsub p q) := by
  have instFiniteRatB : FiniteDimensional ℚ (Bsub p q) :=
    FiniteDimensional.trans ℚ (F p) (Bsub p q)
  exact {}


end Catalan.A3
