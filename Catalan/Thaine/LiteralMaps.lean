module

public import Catalan.Thaine.RealUnramified
public import Catalan.CaseOne.CircularUnits
public import Catalan.CaseOne.PowerQuotient

/-!
# `Catalan.Thaine.LiteralMaps`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance literalFullCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) :=
  isCyclotomicExtension_Bsub_self_rat p (Fact.out : p.Prime).pos

local instance literalRealAbelian (p : ℕ) [Fact p.Prime] : IsAbelianGalois ℚ (A3.F p) :=
  A3.isAbelianGalois_F p (Fact.out : p.Prime).pos

def literalRealUnitMap (p : ℕ) : (𝓞 (A3.F p))ˣ →* (𝓞 (A3.Bsub p p))ˣ :=
  Units.map (algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p p))).toMonoidHom

def literalRealPowerMap (p q : ℕ) :
    UnitQuotient.PowerQuotient (𝓞 (A3.F p))ˣ q →ₗ[ZMod q]
      UnitQuotient.PowerQuotient (𝓞 (A3.Bsub p p))ˣ q :=
  UnitQuotient.powerMap q (literalRealUnitMap p)

def literalFullCircularUnits (p : ℕ) [Fact p.Prime] : Subgroup (𝓞 (A3.Bsub p p))ˣ :=
  Circular.circularUnits p (A3.Bsub p p)

lemma literalFullCircularUnits_eq
    (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} ℚ (A3.Bsub p p)] :
    literalFullCircularUnits p = Circular.circularUnits p (A3.Bsub p p) := rfl

def literalRestriction (p : ℕ) [Fact p.Prime] :
    (A3.Bsub p p ≃ₐ[ℚ] A3.Bsub p p) →* (A3.F p ≃ₐ[ℚ] A3.F p) :=
  AlgEquiv.restrictNormalHom (A3.F p)

lemma literalRestriction_commutes
    (p : ℕ) [Fact p.Prime] (g : A3.Bsub p p ≃ₐ[ℚ] A3.Bsub p p) (x : A3.F p) :
    algebraMap (A3.F p) (A3.Bsub p p) (literalRestriction p g x) =
      g (algebraMap (A3.F p) (A3.Bsub p p) x) :=
  AlgEquiv.restrictNormal_commutes g (A3.F p) x

def literalRestrictionRing (p : ℕ) [Fact p.Prime] :
    R p (A3.Bsub p p) →+* R p (A3.F p) :=
  MonoidAlgebra.mapDomainRingHom ℤ (literalRestriction p)

end Catalan.Thaine
