module

public import Catalan.Density.OrbitCoordinates
public import Catalan.Density.FUnitAugmentation
public import Catalan.Density.ResidueCoordinate
public import Catalan.Density.SeparatingPrimeClasses

/-!
# `Catalan.Density.UnitResidueCoordinates`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
open scoped BigOperators
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
local instance unitResidueGalFintype : Fintype (G p (F p)) := Fintype.ofFinite _

def unitResidueFunctional (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q) :
    Module.Dual (ZMod q) (UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q) :=
  e.toLinearMap.comp (UnitQuotient.powerMap q (Units.map red.toMonoidHom))

def unitResidueCoordinates (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q) :
    UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q →ₗ[ZMod q] (G p (F p) → ZMod q) :=
  Residue.inverseOrbitMap (UnitModule.unitRepresentation p (F p) q)
    (unitResidueFunctional p q ell red e)

omit [Fact p.Prime] in
lemma unitResidueCoordinates_powerClass (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (u : (𝓞 (F p))ˣ) (g : G p (F p)) :
    unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q u) g =
      e (UnitQuotient.powerClass q (Units.map red.toMonoidHom
        (Circular.unitAction p (F p) g⁻¹ u))) := by
  change e (UnitQuotient.powerMap q (Units.map red.toMonoidHom)
    (UnitQuotient.powerMap q (Circular.unitAction p (F p) g⁻¹)
      (UnitQuotient.powerClass q u))) = _
  rw [UnitQuotient.powerMap_apply, UnitQuotient.powerMap_apply]

omit [Fact p.Prime] in
lemma unitResidueCoordinates_equivariant (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (sigma : G p (F p)) (z : UnitQuotient.PowerQuotient (𝓞 (F p))ˣ q) (g : G p (F p)) :
    unitResidueCoordinates p q ell red e (UnitModule.unitRepresentation p (F p) q sigma z) g =
      unitResidueCoordinates p q ell red e z (sigma⁻¹ * g) :=
  Residue.inverseOrbitMap_equivariant _ _ sigma z g

omit [Fact p.Prime] in
lemma unitResidueCoordinates_injective (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (hsep : ∀ u : (𝓞 (F p))ˣ,
      (∀ g : G p (F p), ∃ w : (ZMod ell)ˣ,
        w ^ q = Units.map red.toMonoidHom (Circular.unitAction p (F p) g u)) →
      ∃ w : (𝓞 (F p))ˣ, w ^ q = u) :
    Function.Injective (unitResidueCoordinates p q ell red e) := by
  apply (injective_iff_map_eq_zero (unitResidueCoordinates p q ell red e)).mpr
  intro z hz
  induction z using QuotientGroup.induction_on with
  | _ u =>
    have hu : ∃ w : (𝓞 (F p))ˣ, w ^ q = u := hsep u (by
      intro g
      have h := congrFun hz g⁻¹
      change unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q u) g⁻¹ = 0 at h
      rw [unitResidueCoordinates_powerClass, inv_inv] at h
      have hzero : UnitQuotient.powerClass q
          (Units.map red.toMonoidHom (Circular.unitAction p (F p) g u)) = 0 := by
        apply e.injective
        simpa only [map_zero] using h
      change (QuotientGroup.mk (Units.map red.toMonoidHom (Circular.unitAction p (F p) g u)) :
        (ZMod ell)ˣ ⧸ UnitQuotient.qPowers (ZMod ell)ˣ q) = 1 at hzero
      exact (QuotientGroup.eq_one_iff _).mp hzero)
    change (QuotientGroup.mk u : (𝓞 (F p))ˣ ⧸ UnitQuotient.qPowers (𝓞 (F p))ˣ q) = 1
    exact (QuotientGroup.eq_one_iff u).mpr hu

lemma unitResidueCoordinates_range (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (hsep : ∀ u : (𝓞 (F p))ˣ,
      (∀ g : G p (F p), ∃ w : (ZMod ell)ˣ,
        w ^ q = Units.map red.toMonoidHom (Circular.unitAction p (F p) g u)) →
      ∃ w : (𝓞 (F p))ˣ, w ^ q = u) :
    LinearMap.range (unitResidueCoordinates p q ell red e) =
      Residue.sumZero (ZMod q) (G p (F p)) :=
  Residue.inverseOrbitMap_range_eq_sumZero _ _
    (unitResidueCoordinates_injective p q ell red e hsep)
    (F_unit_norm_zero p q hp2 hq2) (F_unit_finrank_add_one p q hp2 hq2)

lemma exists_unit_augmentation_coordinates (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hdegree : ¬ q ∣ (p - 1) / 2) (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (hsep : ∀ u : (𝓞 (F p))ˣ,
      (∀ g : G p (F p), ∃ w : (ZMod ell)ˣ,
        w ^ q = Units.map red.toMonoidHom (Circular.unitAction p (F p) g u)) →
      ∃ w : (𝓞 (F p))ˣ, w ^ q = u) :
    ∃ u : (𝓞 (F p))ˣ, ∀ g : G p (F p),
      unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q u) g =
        (1 : MonoidAlgebra (ZMod q) (G p (F p))).coeff g -
          (Fintype.card (G p (F p)) : ZMod q)⁻¹ := by
  classical
  have hn : (Fintype.card (G p (F p)) : ZMod q) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff (Fintype.card (G p (F p))) q).mp hz
    rw [← Nat.card_eq_fintype_card, card_gal_F p Fact.out hp2] at hd
    exact hdegree hd
  let a : G p (F p) → ZMod q := fun g =>
    (1 : MonoidAlgebra (ZMod q) (G p (F p))).coeff g -
      (Fintype.card (G p (F p)) : ZMod q)⁻¹
  have hone : (∑ g : G p (F p),
      (1 : MonoidAlgebra (ZMod q) (G p (F p))).coeff g) = 1 := by
    simp [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have ha : a ∈ Residue.sumZero (ZMod q) (G p (F p)) := by
    rw [Residue.mem_sumZero]
    dsimp only [a]
    rw [Finset.sum_sub_distrib, hone, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_inv_cancel₀ hn, sub_self]
  have harange : a ∈ LinearMap.range (unitResidueCoordinates p q ell red e) := by
    rw [unitResidueCoordinates_range p q hp2 hq2 ell red e hsep]
    exact ha
  obtain ⟨z, hz⟩ := harange
  induction z using QuotientGroup.induction_on with
  | _ u =>
    refine ⟨u, ?_⟩
    intro g
    exact congrFun hz g

end Catalan.A3
