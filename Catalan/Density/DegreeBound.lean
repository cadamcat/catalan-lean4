import Catalan.Density.UnramifiedWitness
import ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertNormCharacterization
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma finrank_dvd_classNumber_of_everywhereUnramified
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] (hunram : IsEverywhereUnramified K L) :
    Module.finrank K L ∣ NumberField.classNumber K := by
  let instInfiniteUnramified : IsUnramifiedAtInfinitePlaces K L := hunram.infinitePlaces
  have hram : ramifiedBaseFinitePlaces (K := K) (L := L) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro P hP
    obtain ⟨Q, _, hQ⟩ := (mem_ramifiedBaseFinitePlaces_iff (K := K) (L := L) P).mp hP
    exact hQ (hunram.finitePlaces Q)
  simpa only [← Subgroup.index_eq_card,
    GlobalClassFieldTheory.Reciprocity.ideleClassNorm_index_eq_finrank_abelian K L] using
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotient_card_dvd_classNumber_of_everywhereUnramified
        (K := K) (L := L) hram


lemma unramifiedAbelianQ_finrank_dvd_classNumber (p q : ℕ) (hq : Odd q)
    (J : IntermediateField (F p) Omega) (hJ : UnramifiedAbelianQ p q J) :
    Module.finrank (F p) J ∣ NumberField.classNumber (F p) := by
  let instFiniteJ : FiniteDimensional (F p) J := hJ.1
  let instNumberFieldJ : NumberField J := NumberField.of_module_finite (F p) J
  let instGaloisJ : IsGalois (F p) J := hJ.2.1
  let instAbelianJ : IsAbelianGalois (F p) J := { is_comm.comm := hJ.2.2.1 }
  exact finrank_dvd_classNumber_of_everywhereUnramified (F p) J
    ⟨unramifiedAbelianQ_finitePlaces p q J hJ,
      unramifiedAbelianQ_infinitePlaces p q hq J hJ⟩

end Catalan.A3
