module

public import Catalan.CaseOne.UnitRepresentation
public import Catalan.CaseOne.PowerImage
public import Catalan.CaseOne.CircularStability

/-!
# `Catalan.CaseOne.CircularModule`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
open UnitQuotient
variable (p : ℕ) (K : Type*) [Field K] [NumberField K] (q : ℕ)

/-- The actual image of a Galois-stable unit subgroup in the unit power quotient. -/
def stableUnitImage (S : Subgroup (𝓞 K)ˣ)
    (hS : ∀ τ : G p K, ∀ u ∈ S, Circular.unitAction p K τ u ∈ S) :
    Submodule (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) :=
  Subrepresentation.asSubmodule
    { toSubmodule := powerImage (𝓞 K)ˣ q S
      apply_mem_toSubmodule := by
        intro τ v hv
        obtain ⟨u, hu, rfl⟩ := (mem_powerImage_iff (𝓞 K)ˣ q S v).mp hv
        apply (mem_powerImage_iff (𝓞 K)ˣ q S _).mpr
        exact ⟨Circular.unitAction p K τ u, hS τ u hu,
          (powerMap_apply q (Circular.unitAction p K τ) u).symm⟩ }

lemma mem_stableUnitImage_iff (S : Subgroup (𝓞 K)ˣ)
    (hS : ∀ τ : G p K, ∀ u ∈ S, Circular.unitAction p K τ u ∈ S)
    (v : UnitPowerModule p K q) :
    v ∈ stableUnitImage p K q S hS ↔ ∃ u : (𝓞 K)ˣ, u ∈ S ∧ unitClass p K q u = v := by
  exact mem_powerImage_iff (𝓞 K)ˣ q S v

variable [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]

def circularImage : Submodule (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) :=
  stableUnitImage p K q (Circular.circularUnits p K) (Circular.circularUnits_stable p K)

def primaryCircularImage (hq : 0 < q) :
    Submodule (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) :=
  stableUnitImage p K q (Circular.primaryCircularUnits p K q)
    (Circular.primaryCircularUnits_stable p K q hq)

lemma primaryCircularImage_le (hq : 0 < q) :
    primaryCircularImage p K q hq ≤ circularImage p K q := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := (mem_stableUnitImage_iff p K q _ _ v).mp hv
  exact (mem_stableUnitImage_iff p K q _ _ _).mpr ⟨u, hu.1, rfl⟩

lemma primaryCircularImage_ne (hq : q.Prime) (hqp : q < p) :
    primaryCircularImage p K q hq.pos ≠ circularImage p K q := by
  intro heq
  have himage : powerImage (𝓞 K)ˣ q
      (Circular.circularUnits p K ⊓ primaryUnits (𝓞 K) q) =
      powerImage (𝓞 K)ˣ q (Circular.circularUnits p K) := by
    apply Submodule.ext
    intro v
    exact SetLike.ext_iff.mp heq v
  have hle := (powerImage_inf_eq_iff (𝓞 K)ˣ q (Circular.circularUnits p K)
    (primaryUnits (𝓞 K) q) (qPowers_le_primaryUnits (𝓞 K) q)).mp himage
  apply Circular.primaryCircularUnits_ne p K q hq hqp
  exact inf_eq_left.mpr hle

lemma primaryCircularImage_lt (hq : q.Prime) (hqp : q < p) :
    primaryCircularImage p K q hq.pos < circularImage p K q :=
  lt_of_le_of_ne (primaryCircularImage_le p K q hq.pos)
    (primaryCircularImage_ne p K q hq hqp)

end Catalan.UnitModule
