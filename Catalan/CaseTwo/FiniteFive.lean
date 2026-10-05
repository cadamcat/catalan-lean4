module

public import Catalan.Classical.Reduction

/-!
# `Catalan.CaseTwo.FiniteFive`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

theorem small_five_wieferich_candidates (q : ℕ) (hq : q.Prime)
    (hq2 : q ≠ 2) (hq5 : q ≠ 5) (hbound : q < 144)
    (hmod : q ^ 4 ≡ 1 [MOD 25]) :
    q = 7 ∨ q = 43 ∨ q = 101 ∨ q = 107 := by
  interval_cases q <;> norm_num [Nat.ModEq] at *

theorem five_no_double_wieferich_small (q : ℕ) (hq : q.Prime)
    (hq2 : q ≠ 2) (hq5 : q ≠ 5) (hbound : q < 144) :
    ¬ ((q ^ 4 ≡ 1 [MOD 25]) ∧
      (5 ^ (q - 1) ≡ 1 [MOD q ^ 2])) := by
  rintro ⟨hmod, hother⟩
  rcases small_five_wieferich_candidates q hq hq2 hq5 hbound hmod with
    h7 | h43 | h101 | h107
  · subst q
    norm_num [Nat.ModEq] at hother
  · subst q
    norm_num [Nat.ModEq] at hother
  · subst q
    norm_num [Nat.ModEq] at hother
  · subst q
    norm_num [Nat.ModEq] at hother

end Catalan
