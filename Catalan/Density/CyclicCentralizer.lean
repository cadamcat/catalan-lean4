module

public import Mathlib

/-!
# `Catalan.Density.CyclicCentralizer`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.GroupTheory

lemma cyclic_subgroup_eq_zpowers_of_centralizer_exponent
    (G : Type*) [Group G] (q : ℕ) (hq : q.Prime)
    (σ : G) (hσ : σ ≠ 1) (hpow : σ ^ q = 1)
    (hcentral : ∀ τ : G, τ * σ = σ * τ → τ ^ q = 1)
    (D : Subgroup G) [IsCyclic D] (hmem : σ ∈ D) :
    D = Subgroup.zpowers σ := by
  have horder (x : G) (hx : x ≠ 1) (hxpow : x ^ q = 1) : orderOf x = q :=
    (hq.eq_one_or_self_of_dvd (orderOf x) (orderOf_dvd_of_pow_eq_one hxpow)).resolve_left
      (fun h => hx (orderOf_eq_one_iff.mp h))
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top D).mp inferInstance
  have hgmem : g ∈ D := hg ▸ Subgroup.mem_zpowers g
  have hgcomm : g * σ = σ * g :=
    congrArg (fun x : D => (x : G))
      ((isMulCommutative_iff.mp (inferInstance : IsMulCommutative D))
        ⟨g, hgmem⟩ ⟨σ, hmem⟩)
  have hgpow : g ^ q = 1 := hcentral g hgcomm
  have hgne : g ≠ 1 := by
    intro h
    apply hσ
    simpa [← hg, h] using hmem
  have hcard : Nat.card D = q := by
    rw [← hg, Nat.card_zpowers, horder g hgne hgpow]
  let instFiniteD : Finite D := Nat.finite_of_card_ne_zero (hcard ▸ hq.ne_zero)
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
  rw [hcard, Nat.card_zpowers, horder σ hσ hpow]

end Catalan.GroupTheory
