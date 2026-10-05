module

public import Catalan.Cyclotomic.GroupRing

/-! Integer-valued multiplicative orders of a group-ring power. -/
/-!
# `Catalan.Mihailescu.Orders`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Catalan
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]
local instance ordersFintypeG : Fintype (G p K) := Fintype.ofFinite _

lemma order_upow (v : Kˣ →* Multiplicative ℤ) (a : Kˣ) (Θ : R p K) :
    (v (upow p K a Θ)).toAdd =
      ∑ τ : G p K, Θ.coeff τ * (v (actUnit p K τ a)).toAdd := by
  rw [upow_fintype, map_prod]
  simp only [map_zpow, toAdd_prod, toAdd_zpow, zsmul_eq_mul, Int.cast_id]

end Catalan
