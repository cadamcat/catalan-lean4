module

public import Catalan.CaseOne.PowerQuotient

/-!
# `Catalan.Density.ResidueCoordinate`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma exists_residue_power_coordinate
    (q ell : ℕ) [Fact q.Prime] [Fact ell.Prime] (hdiv : q ∣ ell - 1) :
    ∃ g : (ZMod ell)ˣ, (∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers g) ∧
      ∃ e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q,
        e (UnitQuotient.powerClass q g) = 1 := by
  let G := (ZMod ell)ˣ
  let instCyclicG : IsCyclic G := by
    dsimp [G]
    exact ZMod.isCyclic_units_prime (Fact.out : ell.Prime)
  let g : G := IsCyclic.exists_generator (α := G) |>.choose
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g :=
    IsCyclic.exists_generator (α := G) |>.choose_spec
  have hcardG : Nat.card G = ell - 1 := by
    dsimp [G]
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_units, ZMod.card]
  have hqgcd : Nat.gcd (ell - 1) q = q := by
    rw [Nat.gcd_eq_right_iff_dvd]
    exact hdiv
  have hqPowers : UnitQuotient.qPowers G q =
      (powMonoidHom q : G →* G).range := by
    ext x
    rfl
  have hcardQ : Nat.card (G ⧸ UnitQuotient.qPowers G q) = q := by
    rw [← Subgroup.index_eq_card, hqPowers,
      IsCyclic.index_powMonoidHom_range G q, hcardG, hqgcd]
  let gQ : G ⧸ UnitQuotient.qPowers G q :=
    QuotientGroup.mk' (UnitQuotient.qPowers G q) g
  have hgQ : ∀ x : G ⧸ UnitQuotient.qPowers G q,
      x ∈ Subgroup.zpowers gQ := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (UnitQuotient.qPowers G q) x
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp (hg x)
    rw [← hk, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have hgQadd : ∀ x : Additive (G ⧸ UnitQuotient.qPowers G q),
      x ∈ AddSubgroup.zmultiples (Additive.ofMul gQ) := by
    intro x
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp (hgQ (Additive.toMul x))
    apply (AddSubgroup.mem_zmultiples_iff).mpr
    refine ⟨k, ?_⟩
    change Additive.ofMul (gQ ^ k) = x
    rw [hk]
    rfl
  let ea : ZMod q ≃+ Additive (G ⧸ UnitQuotient.qPowers G q) :=
    zmodAddEquivOfGenerator hgQadd hcardQ
  let e : UnitQuotient.PowerQuotient G q ≃ₗ[ZMod q] ZMod q :=
    LinearEquiv.ofBijective (ea.symm.toAddMonoidHom.toZModLinearMap q)
      ea.symm.bijective
  refine ⟨g, hg, ⟨e, ?_⟩⟩
  change ea.symm (Additive.ofMul gQ) = 1
  rw [← zmodAddEquivOfGenerator_apply_one hgQadd hcardQ]
  exact ea.symm_apply_apply 1

end Catalan.A3
