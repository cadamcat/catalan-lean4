module

public import Catalan.Final.Assembly

/-!
# `Catalan.JSP`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false

namespace Catalan.JSP

/-- `n` is a proper perfect power: `n = m ^ k` with base `m ≥ 2` and exponent `k ≥ 2`. -/
def IsProperPerfectPower (n : ℕ) : Prop := ∃ m k : ℕ, 2 ≤ m ∧ 2 ≤ k ∧ m ^ k = n

/-- Eight and nine are proper perfect powers, and they are the only consecutive pair. -/
def Statement : Prop :=
  (IsProperPerfectPower 8 ∧ IsProperPerfectPower 9) ∧
  ∀ n : ℕ, 0 < n → IsProperPerfectPower n → IsProperPerfectPower (n + 1) → n = 8

theorem eight_isProperPerfectPower : IsProperPerfectPower 8 :=
  ⟨2, 3, le_rfl, by norm_num, by norm_num⟩

theorem nine_isProperPerfectPower : IsProperPerfectPower 9 :=
  ⟨3, 2, by norm_num, le_rfl, by norm_num⟩

theorem uniqueness (n : ℕ) (_hn : 0 < n) (hlow : IsProperPerfectPower n)
    (hhigh : IsProperPerfectPower (n + 1)) : n = 8 := by
  obtain ⟨y, b, hy, hb, hyb⟩ := hlow
  obtain ⟨x, a, hx, ha, hxa⟩ := hhigh
  have hsub : x ^ a - y ^ b = 1 := by omega
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    Catalan.catalans_conjecture a b x y (by omega) (by omega) (by omega) (by omega) hsub
  norm_num at hyb
  omega

theorem statement : Statement :=
  ⟨⟨eight_isProperPerfectPower, nine_isProperPerfectPower⟩, uniqueness⟩

end Catalan.JSP
