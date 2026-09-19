import Catalan.Density.FUnits
import Catalan.CaseOne.NormSum

set_option autoImplicit false
open NumberField
open scoped BigOperators
noncomputable section
namespace Catalan.A3

private lemma representation_sum_eq_sum_powers
    {k G V : Type*} [Field k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
    (pi : Representation k G V) (gamma : G) (hgamma : ∀ g : G, g ∈ Subgroup.zpowers gamma) :
    (∑ g : G, pi g) = ∑ i ∈ Finset.range (Nat.card G), (pi gamma) ^ i := by
  have h := congrArg pi.asAlgebraHom (UnitReduction.groupNorm_eq_sum_powers k G gamma hgamma)
  simpa only [UnitReduction.groupNorm, map_sum, map_pow,
    Representation.asAlgebraHom_single_one] using h

variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
local instance unitAugmentationGalFintype : Fintype (G p (F p)) := Fintype.ofFinite _

lemma F_unit_finrank_add_one (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    Module.finrank (ZMod q) (UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q) + 1 =
      Fintype.card (G p (F p)) := by
  have instCyclicF : IsCyclic (G p (F p)) := gal_F_cyclic p Fact.out
  obtain ⟨gamma, hgamma⟩ := IsCyclic.exists_generator (α := G p (F p))
  let T := UnitModule.unitRepresentation p (F p) q gamma
  have hpoly : T.charpoly * (Polynomial.X - Polynomial.C (1 : ZMod q)) =
      Polynomial.X ^ ((p - 1) / 2) - Polynomial.C (1 : ZMod q) := by
    rw [show T.charpoly = _ from F_unit_charpoly p q hp2 hq2 gamma hgamma]
    simpa only [Polynomial.C_1] using geom_sum_mul (Polynomial.X : Polynomial (ZMod q)) ((p - 1) / 2)
  have hdeg := congrArg Polynomial.natDegree hpoly
  rw [Polynomial.natDegree_mul T.charpoly_monic.ne_zero (Polynomial.X_sub_C_ne_zero 1),
    LinearMap.charpoly_natDegree, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_pow_sub_C] at hdeg
  rw [← Nat.card_eq_fintype_card, card_gal_F p Fact.out hp2]
  exact hdeg

lemma F_unit_norm_zero (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (z : UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q) :
    ∑ g : G p (F p), UnitModule.unitRepresentation p (F p) q g z = 0 := by
  have instCyclicF : IsCyclic (G p (F p)) := gal_F_cyclic p Fact.out
  obtain ⟨gamma, hgamma⟩ := IsCyclic.exists_generator (α := G p (F p))
  let pi := UnitModule.unitRepresentation p (F p) q
  have hCH := LinearMap.aeval_self_charpoly (pi gamma)
  rw [F_unit_charpoly p q hp2 hq2 gamma hgamma] at hCH
  simp only [map_sum, map_pow, Polynomial.aeval_X] at hCH
  have hsum : (∑ g : G p (F p), pi g) = 0 := by
    rw [representation_sum_eq_sum_powers pi gamma hgamma, card_gal_F p Fact.out hp2]
    exact hCH
  have h := LinearMap.congr_fun hsum z
  simpa only [LinearMap.sum_apply, LinearMap.zero_apply] using h

end Catalan.A3
