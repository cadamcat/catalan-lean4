module

public import Catalan.CaseOne.CyclotomicPlaces
public import Catalan.CaseTwo.Assembly

/-!
# `Catalan.CaseOne.CaseTwoCard`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule

lemma not_dvd_half_pred_of_not_modEq_one (p q : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : ¬ (p ≡ 1 [MOD q])) : ¬ q ∣ (p - 1) / 2 := by
  intro hd
  obtain ⟨k, hk⟩ := hp.even_sub_one hp2
  have heq : p - 1 = 2 * ((p - 1) / 2) := by omega
  have hd' : q ∣ p - 1 := by
    rw [heq]
    exact dvd_mul_of_dvd_right hd 2
  exact hmod ((Nat.modEq_iff_dvd' hp.one_le).mpr hd').symm

lemma not_dvd_place_card_of_solution (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : ¬ q ∣ Fintype.card (InfinitePlace K) := by
  have hp : p.Prime := Fact.out
  rw [cyclotomicPlace_card p K (by have := hp.two_le; omega)]
  exact not_dvd_half_pred_of_not_modEq_one p q hp hp2
    (case_two p q hp Fact.out hp2 hq2 x y hx hy h).2

end Catalan.UnitModule
