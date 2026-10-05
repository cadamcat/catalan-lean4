module

public import Catalan.Density.FiniteH
public import Catalan.Density.HRelative
public import Catalan.CaseOne.PowerQuotient
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

/-!
# `Catalan.Density.ClassGroupArtin`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

local instance classGroupArtinIdeleClassComm (K : Type) [Field K] [NumberField K] :
    IsMulCommutative (IdeleClassGroup K) := ⟨⟨fun a b => mul_comm a b⟩⟩

private lemma ramifiedBaseFinitePlaces_eq_empty
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (hunram : IsEverywhereUnramified K L) :
    ramifiedBaseFinitePlaces (K := K) (L := L) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  obtain ⟨Q, _, hQ⟩ := (mem_ramifiedBaseFinitePlaces_iff (K := K) (L := L) P).mp hP
  exact hQ (hunram.finitePlaces Q)

def classGroupArtinOfEverywhereUnramified
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (hunram : IsEverywhereUnramified K L) :
    ClassGroup (𝓞 K) →* (L ≃ₐ[K] L) := by
  let instInfiniteUnramified : IsUnramifiedAtInfinitePlaces K L := hunram.infinitePlaces
  exact (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv K L).symm.toMulEquiv.toMonoidHom.comp
    (GlobalClassFieldTheory.GlobalClassFields.classGroupToIdeleClassNormQuotient
      (K := K) (L := L) (ramifiedBaseFinitePlaces_eq_empty K L hunram))

lemma classGroupArtinOfEverywhereUnramified_surjective
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (hunram : IsEverywhereUnramified K L) :
    Function.Surjective (classGroupArtinOfEverywhereUnramified K L hunram) := by
  let instInfiniteUnramified : IsUnramifiedAtInfinitePlaces K L := hunram.infinitePlaces
  exact (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv K L).symm.surjective.comp
    (GlobalClassFieldTheory.GlobalClassFields.classGroupToIdeleClassNormQuotient_surjective
      (K := K) (L := L) (ramifiedBaseFinitePlaces_eq_empty K L hunram))

def classGroupToHGal (p q : ℕ) (hq : Odd q) :
    ClassGroup (𝓞 (F p)) →* (Hsub p q ≃ₐ[F p] Hsub p q) := by
  have instNumberFieldH : NumberField (Hsub p q) := numberField_Hsub p q hq
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  have instAbelianH : IsAbelianGalois (F p) (Hsub p q) := { is_comm.comm := Hsub_gal_mul_comm p q }
  have hw := unramifiedAbelianQ_Hsub p q hq
  exact classGroupArtinOfEverywhereUnramified (F p) (Hsub p q)
    ⟨unramifiedAbelianQ_finitePlaces p q (Hsub p q) hw,
      unramifiedAbelianQ_infinitePlaces p q hq (Hsub p q) hw⟩

lemma classGroupToHGal_surjective (p q : ℕ) (hq : Odd q) :
    Function.Surjective (classGroupToHGal p q hq) := by
  have instNumberFieldH : NumberField (Hsub p q) := numberField_Hsub p q hq
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  have instAbelianH : IsAbelianGalois (F p) (Hsub p q) := { is_comm.comm := Hsub_gal_mul_comm p q }
  have hw := unramifiedAbelianQ_Hsub p q hq
  exact classGroupArtinOfEverywhereUnramified_surjective (F p) (Hsub p q)
    ⟨unramifiedAbelianQ_finitePlaces p q (Hsub p q) hw,
      unramifiedAbelianQ_infinitePlaces p q hq (Hsub p q) hw⟩

lemma classGroupToHGal_pow (p q : ℕ) (hq : Odd q) (c : ClassGroup (𝓞 (F p))) :
    classGroupToHGal p q hq (c ^ q) = 1 := by
  rw [map_pow]
  exact Hsub_gal_pow_eq_one p q _

def classGroupModQToHGal (p q : ℕ) (hq : Odd q) :
    (ClassGroup (𝓞 (F p)) ⧸ UnitQuotient.qPowers (ClassGroup (𝓞 (F p))) q) →*
      (Hsub p q ≃ₐ[F p] Hsub p q) :=
  QuotientGroup.lift _ (classGroupToHGal p q hq) (by
    rintro c ⟨b, rfl⟩
    exact classGroupToHGal_pow p q hq b)

lemma classGroupModQToHGal_mk (p q : ℕ) (hq : Odd q) (c : ClassGroup (𝓞 (F p))) :
    classGroupModQToHGal p q hq (QuotientGroup.mk c) = classGroupToHGal p q hq c := rfl

lemma classGroupModQToHGal_surjective (p q : ℕ) (hq : Odd q) :
    Function.Surjective (classGroupModQToHGal p q hq) := by
  intro σ
  obtain ⟨c, hc⟩ := classGroupToHGal_surjective p q hq σ
  exact ⟨QuotientGroup.mk c, hc⟩

end Catalan.A3
