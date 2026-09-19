import Catalan.CaseOne.PowerQuotient
import Catalan.CaseOne.CircularUnits

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
open UnitQuotient
variable (p : ℕ) (K : Type*) [Field K] [NumberField K] (q : ℕ)

noncomputable def unitRepresentation :
    Representation (ZMod q) (G p K) (PowerQuotient (𝓞 K)ˣ q) where
  toFun τ := powerMap q (Circular.unitAction p K τ)
  map_one' := by
    apply LinearMap.ext
    intro v
    induction v using QuotientGroup.induction_on with
    | _ u =>
      change powerMap q (Circular.unitAction p K 1) (powerClass q u) = powerClass q u
      rw [powerMap_apply]
      congr 1

  map_mul' := by
    intro σ τ
    apply LinearMap.ext
    intro v
    induction v using QuotientGroup.induction_on with
    | _ u =>
      change powerMap q (Circular.unitAction p K (σ * τ)) (powerClass q u) =
        powerMap q (Circular.unitAction p K σ)
          (powerMap q (Circular.unitAction p K τ) (powerClass q u))
      rw [powerMap_apply, powerMap_apply, powerMap_apply]
      congr 1


abbrev UnitPowerModule := (unitRepresentation p K q).asModule

def unitClass (u : (𝓞 K)ˣ) : UnitPowerModule p K q :=
  (unitRepresentation p K q).asModuleEquiv.symm (powerClass q u)

lemma unitClass_surjective : Function.Surjective (unitClass p K q) := by
  intro v
  induction v using QuotientGroup.induction_on with
  | _ u => exact ⟨u, rfl⟩

lemma single_smul_unitClass (τ : G p K) (u : (𝓞 K)ˣ) :
    (MonoidAlgebra.single τ (1 : ZMod q)) • unitClass p K q u =
      unitClass p K q (Circular.unitAction p K τ u) := by
  apply (unitRepresentation p K q).asModuleEquiv.injective
  rw [Representation.asModuleEquiv_map_smul]
  simp only [unitClass, LinearEquiv.apply_symm_apply, Representation.asAlgebraHom_single_one]
  exact powerMap_apply q (Circular.unitAction p K τ) u

end Catalan.UnitModule
