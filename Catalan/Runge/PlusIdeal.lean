module

public import Catalan.Runge.FullInjective
public import Catalan.Runge.PlusInputs

/-!
# `Catalan.Runge.PlusIdeal`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Runge

section Reduction
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

lemma reduceFull_surjective (q : ℕ) : Function.Surjective (reduceFull p K q) :=
  MonoidAlgebra.map_surjective (Int.castRingHom (ZMod q)).toAddMonoidHom ZMod.intCast_surjective

end Reduction

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance rungePlusIdealGalComm : CommGroup (G p K) := UnitModule.cyclotomicGalCommGroup p K

lemma runge_of_mem_plusAugIdeal (q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q)
    (hp2 : p ≠ 2) (hpq : p ≠ q) (x : ℤ)
    (hx : (q : ℝ) ^ (p - 1) < (|x| : ℝ)) (Theta : R p K)
    (hTheta : reduceFull p K q Theta ∈ UnitModule.plusAugIdeal p K q)
    (hu : ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K)) :
    reduceFull p K q Theta = 0 := by
  obtain ⟨he, hw⟩ := even_weight_of_mem_plusAugIdeal p K q Theta hTheta
  exact runge_full_injective p K q hq hq7 hp2 hpq x hx Theta he hw hu

lemma reduce_mihIdeal_inf_plusAug_eq_bot (q : ℕ) [Fact q.Prime] (hq7 : 7 ≤ q)
    (hp2 : p ≠ 2) (hpq : p ≠ q) (x : ℤ)
    (hx : (q : ℝ) ^ (p - 1) < (|x| : ℝ)) :
    (mihIdeal p K q x hp2).map (reduceFull p K q) ⊓ UnitModule.plusAugIdeal p K q = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro theta htheta
  obtain ⟨Theta, hTheta, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (reduceFull p K q) (reduceFull_surjective p K q)).mp htheta.1
  apply Ideal.mem_bot.mpr
  obtain ⟨u, hu⟩ := hTheta
  apply runge_of_mem_plusAugIdeal p K q Fact.out hq7 hp2 hpq x hx Theta htheta.2
  refine ⟨(u : K), ?_⟩
  exact_mod_cast hu.symm

lemma reduce_mihIdeal_inf_plusAug_eq_bot_of_solution (q : ℕ) [Fact q.Prime]
    (hq7 : 7 ≤ q) (hqp : q < p) (hp2 : p ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    (mihIdeal p K q x hp2).map (reduceFull p K q) ⊓ UnitModule.plusAugIdeal p K q = ⊥ :=
  reduce_mihIdeal_inf_plusAug_eq_bot p K q hq7 hp2 (ne_of_gt hqp) x
    (cassels_growth p q Fact.out Fact.out hq7 hqp x y hx hy h)

end Catalan.Runge
