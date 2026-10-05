module

public import Catalan.CaseOne.UnitRepresentation
public import Catalan.CaseOne.TorsionReduction

/-!
# `Catalan.CaseOne.IntegralRepresentation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule

abbrev UnitLattice (K : Type*) [Field K] [NumberField K] :=
  Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K)

variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

noncomputable instance unitLatticeIntModule : Module ℤ (UnitLattice K) :=
  @AddCommGroup.toIntModule (UnitLattice K) Additive.addCommGroup

def integralUnitClass (u : (𝓞 K)ˣ) : UnitLattice K :=
  Additive.ofMul (QuotientGroup.mk u)

noncomputable def torsionAction (τ : G p K) :
    ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) →*
      ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) :=
  QuotientGroup.map (NumberField.Units.torsion K) (NumberField.Units.torsion K)
    (Circular.unitAction p K τ) (CommGroup.le_comap_torsion _)

lemma torsionAction_apply (τ : G p K) (u : (𝓞 K)ˣ) :
    torsionAction p K τ (QuotientGroup.mk u) =
      QuotientGroup.mk (Circular.unitAction p K τ u) := by
  exact QuotientGroup.map_mk _ _ _ _ _

noncomputable def integralUnitRepresentation : Representation ℤ (G p K) (UnitLattice K) where
  toFun τ := by
    let g := torsionAction p K τ
    let ga : @AddMonoidHom (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K))
        (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K))
        AddCommGroup.toAddGroup.toAddZeroClass.toAddZero
        AddCommGroup.toAddGroup.toAddZeroClass.toAddZero :=
      { toFun := fun x => Additive.ofMul (g (Additive.toMul x))
        map_zero' := by
          change g 1 = 1
          exact g.map_one
        map_add' := by
          intro x y
          change g ((Additive.toMul x) * (Additive.toMul y)) =
            g (Additive.toMul x) * g (Additive.toMul y)
          exact g.map_mul _ _ }
    exact ga.toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro v
    induction v using QuotientGroup.induction_on with
    | _ u =>
      dsimp
      change Additive.ofMul (torsionAction p K 1 (QuotientGroup.mk u)) =
        Additive.ofMul (QuotientGroup.mk u)
      rw [torsionAction_apply]
      congr 1
  map_mul' := by
    intro σ τ
    apply LinearMap.ext
    intro v
    induction v using QuotientGroup.induction_on with
    | _ u =>
      dsimp
      change Additive.ofMul (torsionAction p K (σ * τ) (QuotientGroup.mk u)) =
        Additive.ofMul (torsionAction p K σ
          (torsionAction p K τ (QuotientGroup.mk u)))
      rw [torsionAction_apply, torsionAction_apply, torsionAction_apply]
      congr 1

lemma integralUnitRepresentation_apply (τ : G p K) (u : (𝓞 K)ˣ) :
    integralUnitRepresentation p K τ (integralUnitClass K u) =
      integralUnitClass K (Circular.unitAction p K τ u) := by
  dsimp [integralUnitRepresentation, integralUnitClass]
  rw [torsionAction_apply]

lemma integralUnitClass_surjective : Function.Surjective (integralUnitClass K) := by
  intro v
  induction v using QuotientGroup.induction_on with
  | _ u => exact ⟨u, rfl⟩

lemma unitTorsionMap_equivariant (q : ℕ) (τ : G p K)
    (v : UnitQuotient.PowerQuotient (𝓞 K)ˣ q) :
    UnitQuotient.powerMap q (torsionAction p K τ) (UnitQuotient.unitTorsionMap K q v) =
      UnitQuotient.unitTorsionMap K q
        (UnitQuotient.powerMap q (Circular.unitAction p K τ) v) := by
  induction v using QuotientGroup.induction_on with
  | _ u =>
    change UnitQuotient.powerMap q (torsionAction p K τ)
        (UnitQuotient.powerClass q
          (QuotientGroup.mk' (NumberField.Units.torsion K) u)) =
      UnitQuotient.powerClass q
        (QuotientGroup.mk' (NumberField.Units.torsion K)
          (Circular.unitAction p K τ u))
    rw [UnitQuotient.powerMap_apply]
    have hact : torsionAction p K τ
        (QuotientGroup.mk' (NumberField.Units.torsion K) u) =
        QuotientGroup.mk' (NumberField.Units.torsion K)
          (Circular.unitAction p K τ u) := by
      change torsionAction p K τ (QuotientGroup.mk u) =
        QuotientGroup.mk (Circular.unitAction p K τ u)
      exact torsionAction_apply p K τ u
    rw [hact]

end Catalan.UnitModule
