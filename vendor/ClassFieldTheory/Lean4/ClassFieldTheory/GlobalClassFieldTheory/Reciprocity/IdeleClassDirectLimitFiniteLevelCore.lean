import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitCore
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
import ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup
import Mathlib.GroupTheory.QuotientGroup.Defs

set_option autoImplicit false

/-!
# Finite levels of the rational idele-class direct limit

Normal closures, finite-level scalar extension, tower base change, and the
canonical embeddings into the rational idele-class direct limit.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

attribute [local instance]
  relativeAdeleRingIntermediateAlgebra

local instance rationalIntermediateNumberField
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField K :=
  NumberField.of_module_finite ℚ K

instance rationalTowerClassGroupCommGroup
    (K N : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    [Algebra K N] [IsScalarTower ℚ K N] [FiniteDimensional K N] :
    CommGroup (TowerRelativeIdeleGroup.ClassGroup ℚ K N) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ K N) := inferInstance
  exact
    QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ K N)

instance rationalTowerClassGroupMul
    (K N : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    [Algebra K N] [IsScalarTower ℚ K N] [FiniteDimensional K N] :
    Mul (TowerRelativeIdeleGroup.ClassGroup ℚ K N) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ K N) := inferInstance
  exact
    (QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ K N)).toMul

/-- The canonical finite Galois closure, inside `SeparableClosure ℚ`,
of a finite rational intermediate field. -/
noncomputable def rationalNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
  { IntermediateField.normalClosure
      ℚ K (SeparableClosure ℚ) with
    finiteDimensional :=
      normalClosure.is_finiteDimensional
        ℚ K (SeparableClosure ℚ)
    isGalois :=
      IsGalois.normalClosure ℚ K (SeparableClosure ℚ) }

/-- Absolute left cosets fixing a finite rational intermediate field,
identified with its embeddings into the canonical normal closure. -/
noncomputable def
    rationalBaseFixingCosetEquivNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    ((RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ))).toSubgroup ⧸
      extensionSubgroup
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)) ≃
      (K →ₐ[ℚ] rationalNormalClosure K) :=
  (LocalClassFieldTheory.baseFixingCosetEquivAlgHom
      ℚ (SeparableClosure ℚ) K).trans
    (normalClosure.algHomEquiv
      (F := ℚ) (K := K) (L := SeparableClosure ℚ)).symm

/-- Embed the actual idele class group of a finite rational
intermediate field into the relative presentation at its canonical
finite Galois closure. -/
noncomputable def rationalIntermediateIdeleClassToNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    IdeleClassGroup K →*
      RelativeIdeleGroup.ClassGroup ℚ (rationalNormalClosure K) :=
  (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K))).comp
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm.toMonoidHom

/-- The canonical map from the actual idele class group of a finite
rational intermediate field to the absolute idele-class direct limit. -/
noncomputable def rationalIntermediateIdeleClassToDirectLimit
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    IdeleClassGroup K →* rationalIdeleClassDirectLimit :=
  (rationalRelativeIdeleClassToDirectLimit
      (rationalNormalClosure K)).comp
    (rationalIntermediateIdeleClassToNormalClosure K)

/-- Passing from the relative presentation of a finite rational
intermediate field to its ordinary idele class group commutes with the
canonical map to the absolute direct limit. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_baseChange
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    rationalIntermediateIdeleClassToDirectLimit K
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) c) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K)) c) := by
  simp only [rationalIntermediateIdeleClassToDirectLimit,
    rationalIntermediateIdeleClassToNormalClosure]
  change
    rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K))
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K)) c)
  rw [(_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := ℚ) (L := K)).symm_apply_apply]

/-- At a finite Galois rational intermediate field, the ordinary
idele-class comparison followed by the absolute direct-limit map is the
canonical finite-level map itself. -/
theorem
    rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    rationalIntermediateIdeleClassToDirectLimit
        (E : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) =
      rationalRelativeIdeleClassToDirectLimit E c := by
  rw [rationalIntermediateIdeleClassToDirectLimit_baseChange]
  exact rationalIdeleClassDirectLimit_mk_apply c
    (IntermediateField.le_normalClosure
      (E : IntermediateField ℚ (SeparableClosure ℚ)))

/-- The canonical maps from nested rational intermediate fields to the
idele-class direct limit agree after scalar extension. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_extension
    {F E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ E]
    (hFE : F ≤ E)
    (c : RelativeIdeleGroup.ClassGroup ℚ F) :
    rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)
          (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hFE) c)) =
      rationalIntermediateIdeleClassToDirectLimit F
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c) := by
  let U :
      FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
    rationalNormalClosure F ⊔ rationalNormalClosure E
  let hFN :
      F ≤ (rationalNormalClosure F :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure F
  let hEN :
      E ≤ (rationalNormalClosure E :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure E
  let hNFU : rationalNormalClosure F ≤ U :=
    le_sup_left
  let hNEU : rationalNormalClosure E ≤ U :=
    le_sup_right
  let hFU :
      F ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)) :=
    hFN.trans hNFU
  let hEU :
      E ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)) :=
    hEN.trans hNEU
  have hleft :
      RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hNEU)
          (RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hEN)
            (RelativeIdeleGroup.classEmbedding
              (IntermediateField.inclusion hFE) c)) =
        RelativeIdeleGroup.classEmbedding
          (IntermediateField.inclusion hFU) c := by
    calc
      _ =
          RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hEU)
            (RelativeIdeleGroup.classEmbedding
              (IntermediateField.inclusion hFE) c) := by
        simpa only [hEU] using
          rationalRelativeIdeleClassEmbedding_comp
            hEN hNEU
            (RelativeIdeleGroup.classEmbedding
              (IntermediateField.inclusion hFE) c)
      _ =
          RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hFU) c := by
        simpa only [hFU] using
          rationalRelativeIdeleClassEmbedding_comp
            hFE hEU c
  have hright :
      RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hNFU)
          (RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hFN) c) =
        RelativeIdeleGroup.classEmbedding
          (IntermediateField.inclusion hFU) c := by
    simpa only [hFU] using
      rationalRelativeIdeleClassEmbedding_comp
        hFN hNFU c
  rw [
    rationalIntermediateIdeleClassToDirectLimit_baseChange E
      (RelativeIdeleGroup.classEmbedding
        (IntermediateField.inclusion hFE) c),
    rationalIntermediateIdeleClassToDirectLimit_baseChange F c]
  calc
    rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure E)
        (RelativeIdeleGroup.classEmbedding
          (IntermediateField.inclusion hEN)
          (RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hFE) c)) =
        rationalRelativeIdeleClassToDirectLimit U
          (RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hNEU)
            (RelativeIdeleGroup.classEmbedding
              (IntermediateField.inclusion hEN)
              (RelativeIdeleGroup.classEmbedding
                (IntermediateField.inclusion hFE) c))) :=
      (rationalIdeleClassDirectLimit_mk_apply
        (RelativeIdeleGroup.classEmbedding
          (IntermediateField.inclusion hEN)
          (RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hFE) c))
        hNEU).symm
    _ =
        rationalRelativeIdeleClassToDirectLimit U
          (RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hNFU)
            (RelativeIdeleGroup.classEmbedding
              (IntermediateField.inclusion hFN) c)) := by
      rw [hleft, hright]
    _ =
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure F)
          (RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hFN) c) :=
      rationalIdeleClassDirectLimit_mk_apply
        (RelativeIdeleGroup.classEmbedding
          (IntermediateField.inclusion hFN) c)
        hNFU


end Reciprocity
end GlobalClassFieldTheory
