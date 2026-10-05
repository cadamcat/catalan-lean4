module

public import Mathlib

/-!
# `Catalan.Density.BoundedSup`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.FieldTower

lemma sSup_mem_of_bounded_finrank
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    (S : Set (IntermediateField F L)) (N : ℕ)
    (hne : S.Nonempty)
    (hfinite : ∀ K ∈ S, FiniteDimensional F K)
    (hbound : ∀ K ∈ S, Module.finrank F K ≤ N)
    (hjoin : ∀ K ∈ S, ∀ J ∈ S, K ⊔ J ∈ S) :
    sSup S ∈ S := by
  classical
  have hdegfin : ((fun K : IntermediateField F L => Module.finrank F K) '' S).Finite := by
    apply (Set.finite_le_nat N).subset
    rintro d ⟨K, hK, rfl⟩
    exact hbound K hK
  obtain ⟨Kmax, hKmax, hmax⟩ :=
    hdegfin.exists_maximalFor' (fun K : IntermediateField F L => Module.finrank F K) S hne
  have hKsup_mem : ∀ J ∈ S, Kmax ⊔ J ∈ S := by
    intro J hJ
    exact hjoin Kmax hKmax J hJ
  have hKsup_le : ∀ J ∈ S,
      Module.finrank F (Kmax ⊔ J : IntermediateField F L) ≤ Module.finrank F Kmax := by
    intro J hJ
    haveI : FiniteDimensional F (Kmax ⊔ J : IntermediateField F L) :=
      hfinite (Kmax ⊔ J : IntermediateField F L) (hKsup_mem J hJ)
    exact hmax (hKsup_mem J hJ)
      (IntermediateField.finrank_le_of_le_right (K := F)
        (F := Kmax) (E := (Kmax ⊔ J : IntermediateField F L)) le_sup_left)
  have hJ_le : ∀ J ∈ S, J ≤ Kmax := by
    intro J hJ
    haveI : FiniteDimensional F (Kmax ⊔ J : IntermediateField F L) :=
      hfinite (Kmax ⊔ J : IntermediateField F L) (hKsup_mem J hJ)
    have heq : Kmax = Kmax ⊔ J :=
      IntermediateField.eq_of_le_of_finrank_le le_sup_left (hKsup_le J hJ)
    calc
      J ≤ Kmax ⊔ J := le_sup_right
      _ = Kmax := heq.symm
  have hsup_le : sSup S ≤ Kmax := sSup_le hJ_le
  have hKmax_le_sup : Kmax ≤ sSup S := le_sSup hKmax
  have heq : sSup S = Kmax := le_antisymm hsup_le hKmax_le_sup
  rw [heq]
  exact hKmax

lemma finiteDimensional_sSup_of_bounded_finrank
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    (S : Set (IntermediateField F L)) (N : ℕ)
    (hfinite : ∀ K ∈ S, FiniteDimensional F K)
    (hbound : ∀ K ∈ S, Module.finrank F K ≤ N)
    (hjoin : ∀ K ∈ S, ∀ J ∈ S, K ⊔ J ∈ S) :
    FiniteDimensional F ↥(sSup S) := by
  classical
  by_cases hS : S.Nonempty
  · exact hfinite (sSup S) (sSup_mem_of_bounded_finrank F L S N hS hfinite hbound hjoin)
  · have hS' : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hS', sSup_empty]
    infer_instance

end Catalan.FieldTower
