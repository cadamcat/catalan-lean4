module

public import Catalan.Cassels.Defs

/-!
# `Catalan.Cassels.Valuation`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

/-- If the odd prime `p` divides `x - 1`, the geometric-sum factor has
exactly one factor of `p`. This includes `x = 1` and negative integers. -/
theorem cassels_cyclo_exact_valuation (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (x : ℤ) (hx : (p : ℤ) ∣ x - 1) :
    padicValInt p (casselsCyclo p x) = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpx : ¬ (p : ℤ) ∣ x := by
    intro hpx
    apply hpZ.not_dvd_one
    simpa only [sub_sub_cancel] using dvd_sub hpx hx
  have hm : emultiplicity (p : ℤ) (casselsCyclo p x) = 1 := by
    simpa [casselsCyclo] using
      (emultiplicity_geom_sum₂_eq_one hpZ (hp.odd_of_ne_two hp2) hx hpx)
  have hs : casselsCyclo p x ≠ 0 := by
    intro hzero
    simp [hzero] at hm
  rw [padicValInt.of_ne_one_ne_zero hp.ne_one hs]
  exact multiplicity_eq_of_emultiplicity_eq_some hm

#print axioms cassels_cyclo_exact_valuation

end Catalan
