module

public import Catalan.Stickelberger.MinusReflection
public import Catalan.Stickelberger.MinusSpanCore

/-!
# `Catalan.Stickelberger.MinusSpan`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

theorem theta_minus_spans :
    (stickSpan p K).map (minusLinearMap p K) = minusGeneratorSpan p K := by
  by_cases hp2 : p ≠ 2
  · exact theta_minus_spans_of_reflection p K hp2 (minus_theta_reflection p K)
  · have hp : p = 2 := by omega
    subst p
    have hunit : (-1 : (ZMod 2)ˣ) = 1 := by
      apply Units.ext
      change (-1 : ZMod 2) = 1
      apply neg_eq_iff_add_eq_zero.mpr
      rw [one_add_one_eq_two]
      exact ZMod.natCast_self 2
    have hi : ι 2 K = 1 := by
      rw [ι, hunit]
      unfold σ
      exact map_one _
    have hmap : minusLinearMap 2 K = 0 := by
      ext T
      simp [minusLinearMap, hi]
    have hspan : minusGeneratorSpan 2 K = ⊥ := by
      unfold minusGeneratorSpan
      have hr : Set.range (fun k : Fin ((2 - 1) / 2) => θminus 2 K (k.val + 1)) = ∅ := by
        ext T
        constructor
        · rintro ⟨k, _⟩
          exact Fin.elim0 k
        · intro h
          exact False.elim h
      rw [hr, Submodule.span_empty]
    simp only [hmap, Submodule.map_zero, hspan]

end Catalan
