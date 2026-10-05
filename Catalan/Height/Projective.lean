module

public import Catalan.Height.Basic

/-!
# `Catalan.Height.Projective`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable {L : Type*} [Field L] [NumberField L]

lemma height_projective_integral_le (a b : L) (ha : a ≠ 0) (hb : b ≠ 0)
    (hai : IsIntegral ℤ a) (hbi : IsIntegral ℤ b)
    (C : ℝ) (hC : 1 ≤ C)
    (harch : ∀ w : InfinitePlace L, max (w a) (w b) ≤ C) :
    logHeight (a / b) ≤ Real.log C := by
  classical
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hquot : a / b ≠ 0 := div_ne_zero ha hb
  have hvec : (![a, b] : Fin 2 → L) ≠ 0 := by
    intro hz
    have he : a = 0 := by simpa using congrFun hz 0
    exact hquot (by rw [he, zero_div])
  have hsup (v : L → ℝ) : (⨆ i : Fin 2, v (![a, b] i)) = max (v a) (v b) := by
    have he : (fun i : Fin 2 => v (![a, b] i)) = ![v a, v b] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    apply eq_of_forall_ge_iff
    simp [ciSup_le_iff, Fin.forall_fin_two]
  have hfinite (v : FinitePlace L) : max (v a) (v b) ≤ 1 := by
    apply max_le
    · rw [← FinitePlace.norm_embedding_eq]
      exact FinitePlace.norm_le_one L v.maximalIdeal (⟨a, hai⟩ : 𝓞 L)
    · rw [← FinitePlace.norm_embedding_eq]
      exact FinitePlace.norm_le_one L v.maximalIdeal (⟨b, hbi⟩ : 𝓞 L)
  have hfin : 0 ≤ (∏ᶠ v : FinitePlace L, max (v a) (v b)) ∧
      (∏ᶠ v : FinitePlace L, max (v a) (v b)) ≤ 1 := by
    apply finprod_induction (fun x : ℝ => 0 ≤ x ∧ x ≤ 1)
    · exact ⟨zero_le_one, le_rfl⟩
    · intro x y hx hy
      exact ⟨mul_nonneg hx.1 hy.1, (mul_le_of_le_one_right hx.1 hy.2).trans hx.2⟩
    · intro v
      exact ⟨(apply_nonneg v a).trans (le_max_left _ _), hfinite v⟩
  have hinf : (∏ w : InfinitePlace L, max (w a) (w b) ^ w.mult) ≤
      C ^ Module.finrank ℚ L := by
    calc
      _ ≤ ∏ w : InfinitePlace L, C ^ w.mult := by
        apply Finset.prod_le_prod₀
        · intro w _
          exact pow_nonneg ((apply_nonneg w a).trans (le_max_left _ _)) _
        · intro w _
          exact pow_le_pow_left₀ ((apply_nonneg w a).trans (le_max_left _ _)) (harch w) _
      _ = C ^ Module.finrank ℚ L := by
        rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  have hheight : Height.mulHeight₁ (a / b) ≤ C ^ Module.finrank ℚ L := by
    rw [Height.mulHeight₁_div_eq_mulHeight, NumberField.mulHeight_eq hvec]
    simp only [hsup]
    simpa only [mul_one] using mul_le_mul hinf hfin.2 hfin.1
      (pow_nonneg hC0 (Module.finrank ℚ L))
  have hlog : Height.logHeight₁ (a / b) ≤
      (Module.finrank ℚ L : ℝ) * Real.log C := by
    have he := Real.log_le_log (Height.mulHeight₁_pos (a / b)) hheight
    simpa only [← Height.logHeight₁_eq_log_mulHeight₁, Real.log_pow] using he
  have hd : 0 < (Module.finrank ℚ L : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ L)
  rw [logHeight_eq_normalized]
  calc
    (Module.finrank ℚ L : ℝ)⁻¹ * Height.logHeight₁ (a / b) ≤
        (Module.finrank ℚ L : ℝ)⁻¹ * ((Module.finrank ℚ L : ℝ) * Real.log C) :=
      mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hd.le)
    _ = Real.log C := by field_simp

end Catalan
