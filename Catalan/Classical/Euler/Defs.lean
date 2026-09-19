import Mathlib.NumberTheory.PellMatiyasevic

namespace Catalan.Euler

/-- Coefficients of (2+sqrt(3))^n, using Mathlib's Pell sequence. -/
def pellX (n : ℕ) : ℕ := Pell.xn (by decide : 1 < 2) n

/-- The sqrt(3) coefficient of (2+sqrt(3))^n. -/
def pellY (n : ℕ) : ℕ := Pell.yn (by decide : 1 < 2) n

end Catalan.Euler
