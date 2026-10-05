module

public import Mathlib

/-!
# `Catalan.Mihailescu.BoundsDefs`

Part of the Catalan formalization.
-/

@[expose] public section

noncomputable section
namespace Catalan

/-- Bilu's radius (Theorem 4.1). -/
def mihRadius (p q : ℕ) (ε : ℝ) : ℝ := (2 - ε) * q / (p - 1)

/-- Exponential part of the threshold in Bilu's equation (8). -/
def mihThreshold (p : ℕ) (ε : ℝ) : ℝ :=
  (36 * 2 ^ (p - 1) / ((p - 1 : ℝ) ^ 2)) ^ (1 / ε)

end Catalan
