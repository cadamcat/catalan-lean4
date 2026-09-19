import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace Catalan

lemma LFunction_zero_ne_zero_of_prime_odd
    (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (hodd : χ.Odd) :
    DirichletCharacter.LFunction χ 0 ≠ 0
 := by
  have hinv : χ⁻¹ ≠ 1 := fun h => hχ (inv_eq_one.mp h)
  have hprim : DirichletCharacter.IsPrimitive χ⁻¹ := by
    change DirichletCharacter.conductor χ⁻¹ = p
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp
        (DirichletCharacter.conductor_dvd_level χ⁻¹) with h | h
    · exact (hinv (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)).elim
    · exact h
  have hc1 : DirichletCharacter.completedLFunction χ⁻¹ 1 ≠ 0 := by
    intro hzero
    apply DirichletCharacter.LFunction_apply_one_ne_zero hinv
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 1
      (Or.inl one_ne_zero), hzero, zero_div]
  have hc0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
    intro hzero
    have hfe := hprim.completedLFunction_one_sub (0 : ℂ)
    simp only [sub_zero, inv_inv, hzero, mul_zero] at hfe
    exact hc1 hfe
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0
    (Or.inr (Fact.out : p.Prime).ne_one), hodd.gammaFactor_def,
    zero_add, Complex.Gammaℝ_one, div_one]
  exact hc0

end Catalan
