module

public import Catalan.Density.ClassGroupArtin
public import Catalan.Density.PowerFixedField
public import Catalan.Density.UnramifiedModel
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticHilbertClassFieldReciprocity
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality

/-!
# `Catalan.Density.HClassQuotient`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma exists_unramifiedAbelianQ_classQuotient_degree (p q : ℕ) :
    ∃ J : IntermediateField (F p) Omega,
      UnramifiedAbelianQ p q J ∧
      Nat.card (ClassGroup (𝓞 (F p)) ⧸ UnitQuotient.qPowers (ClassGroup (𝓞 (F p))) q) =
        Module.finrank (F p) J := by
  let L := GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField (F p)
  let instFieldL : Field L := inferInstance
  let instAlgebraFL : Algebra (F p) L :=
    GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal (F p)
  let instModuleFL : Module (F p) L := instAlgebraFL.toModule
  have instFiniteFL : FiniteDimensional (F p) L :=
    GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldFiniteDimensionalOverOriginal (F p)
  have instNumberFieldL : NumberField L := NumberField.of_module_finite (F p) L
  let e : (L ≃ₐ[F p] L) ≃* ClassGroup (𝓞 (F p)) :=
    GlobalClassFieldTheory.GlobalClassFields.arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal
      (K := F p)
  obtain ⟨S, hS, hpow, ⟨eS⟩⟩ := FieldTower.exists_intermediateField_of_galois_power_quotient
    (F p) L (ClassGroup (𝓞 (F p))) e q
  let instFieldS : Field S := IntermediateField.toField S
  let instAlgebraFS : Algebra (F p) S := S.toSubalgebra.algebra
  let instModuleFS : Module (F p) S := instAlgebraFS.toModule
  have instAbelianS : IsAbelianGalois (F p) S := hS
  have hunram : IsEverywhereUnramified (F p) S :=
    IsEverywhereUnramified.bot (k := F p) (K := S) (F := L)
      (GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_isEverywhereUnramified
        (K := F p))
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := exists_unramifiedAbelianQ_model p q S hpow hunram.finitePlaces
  refine ⟨J, hJ, ?_⟩
  calc
    Nat.card (ClassGroup (𝓞 (F p)) ⧸ UnitQuotient.qPowers (ClassGroup (𝓞 (F p))) q) =
        Nat.card (S ≃ₐ[F p] S) := (Nat.card_congr eS.toEquiv).symm
    _ = Module.finrank (F p) S := IsGalois.card_aut_eq_finrank (F p) S
    _ = Module.finrank (F p) J := eJ.toLinearEquiv.finrank_eq

lemma classGroupModQToHGal_injective (p q : ℕ) (hq : Odd q) :
    Function.Injective (classGroupModQToHGal p q hq) := by
  have instFiniteH : FiniteDimensional (F p) (Hsub p q) := finiteDimensional_Hsub p q hq
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  obtain ⟨J, hJ, hcard⟩ := exists_unramifiedAbelianQ_classQuotient_degree p q
  have hle : Nat.card (ClassGroup (𝓞 (F p)) ⧸ UnitQuotient.qPowers (ClassGroup (𝓞 (F p))) q) ≤
      Nat.card (Hsub p q ≃ₐ[F p] Hsub p q) := by
    rw [hcard, IsGalois.card_aut_eq_finrank (F p) (Hsub p q)]
    exact IntermediateField.finrank_le_of_le_right (K := F p)
      (F := J) (E := Hsub p q) (le_sSup hJ)
  exact ((classGroupModQToHGal_surjective p q hq).bijective_of_nat_card_le hle).1

def classGroupModQEquivHGal (p q : ℕ) (hq : Odd q) :
    (ClassGroup (𝓞 (F p)) ⧸ UnitQuotient.qPowers (ClassGroup (𝓞 (F p))) q) ≃*
      (Hsub p q ≃ₐ[F p] Hsub p q) :=
  MulEquiv.ofBijective (classGroupModQToHGal p q hq)
    ⟨classGroupModQToHGal_injective p q hq, classGroupModQToHGal_surjective p q hq⟩

lemma classGroupModQEquivHGal_mk (p q : ℕ) (hq : Odd q) (c : ClassGroup (𝓞 (F p))) :
    classGroupModQEquivHGal p q hq (QuotientGroup.mk c) = classGroupToHGal p q hq c := rfl

lemma classGroupToHGal_eq_one_iff (p q : ℕ) (hq : Odd q) (c : ClassGroup (𝓞 (F p))) :
    classGroupToHGal p q hq c = 1 ↔ c ∈ UnitQuotient.qPowers (ClassGroup (𝓞 (F p))) q := by
  change classGroupModQEquivHGal p q hq (QuotientGroup.mk c) = 1 ↔ _
  rw [← (classGroupModQEquivHGal p q hq).map_one,
    (classGroupModQEquivHGal p q hq).injective.eq_iff]
  exact QuotientGroup.eq_one_iff c

lemma classGroupToHGal_ker (p q : ℕ) (hq : Odd q) :
    (classGroupToHGal p q hq).ker = UnitQuotient.qPowers (ClassGroup (𝓞 (F p))) q := by
  ext c
  exact classGroupToHGal_eq_one_iff p q hq c

end Catalan.A3
