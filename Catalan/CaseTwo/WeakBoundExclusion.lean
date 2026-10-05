module

public import Catalan.CaseTwo.WieferichLift
public import Catalan.CaseTwo.Mignotte
public import Catalan.CaseTwo.FiniteFive

/-!
# `Catalan.CaseTwo.WeakBoundExclusion`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan.CaseTwo

lemma not_modEq_one_of_large_weak_bound
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p)
    (hbound : q < 4 * (p - 1) ^ 2)
    (hw : q ^ (p - 1) ≡ 1 [MOD p ^ 2]) : ¬ q ≡ 1 [MOD p] := by
  intro h1
  have hlow := mignotte_lower_bound p q hp hq hp5 (wieferich_lift_congruence p q hp h1 hw)
  have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  nlinarith

lemma not_modEq_one_of_seven_weak_bound
    (q : ℕ) (hq : q.Prime) (hbound : q < 180)
    (hw : q ^ 6 ≡ 1 [MOD 49]) : ¬ q ≡ 1 [MOD 7] := by
  intro h1
  have hmod := wieferich_lift_congruence 7 q (by decide) h1 hw
  have hlow := mignotte_lower_bound 7 q (by decide) hq (by decide) hmod
  norm_num at hlow
  omega

lemma not_modEq_one_of_five_weak_bound
    (q : ℕ) (hq : q.Prime) (hbound : q < 144)
    (hw1 : q ^ 4 ≡ 1 [MOD 25]) (hw2 : 5 ^ (q - 1) ≡ 1 [MOD q ^ 2]) :
    ¬ q ≡ 1 [MOD 5] := by
  intro h1
  have hq2 : q ≠ 2 := by intro he; norm_num [he, Nat.ModEq] at h1
  have hq5 : q ≠ 5 := by intro he; norm_num [he, Nat.ModEq] at h1
  exact five_no_double_wieferich_small q hq hq2 hq5 hbound ⟨hw1, hw2⟩

end Catalan.CaseTwo
