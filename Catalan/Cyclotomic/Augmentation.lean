module

public import Catalan.Cyclotomic.GroupRing

/-!
# `Catalan.Cyclotomic.Augmentation`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

private lemma nonneg_size_one_single (A : R p K)
    (hA : ∀ τ, 0 ≤ A.coeff τ) (hs : size p K A = 1) :
    ∃ σ : G p K, A = MonoidAlgebra.single σ 1 := by
  classical
  let : Fintype (G p K) := Fintype.ofFinite _
  have hsum : ∑ τ : G p K, A.coeff τ = 1 := by
    simpa only [size_eq_sum, abs_of_nonneg (hA _)] using hs
  obtain ⟨σ, _, hσpos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun τ (_ : τ ∈ (Finset.univ : Finset (G p K))) => hA τ)).mp
      (show (0 : ℤ) < ∑ τ : G p K, A.coeff τ by omega)
  have hσle : A.coeff σ ≤ 1 := by
    simpa only [hsum] using Finset.single_le_sum (fun τ _ => hA τ) (Finset.mem_univ σ)
  have hσ : A.coeff σ = 1 := by omega
  have herase : ∑ τ ∈ (Finset.univ : Finset (G p K)).erase σ, A.coeff τ = 0 := by
    have := Finset.sum_erase_add (s := (Finset.univ : Finset (G p K)))
      (f := fun τ => A.coeff τ) (Finset.mem_univ σ)
    omega
  refine ⟨σ, ?_⟩
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro τ
  by_cases hτσ : τ = σ
  · subst τ
    simpa using hσ
  · have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => hA τ)).mp herase
      τ (Finset.mem_erase.mpr ⟨hτσ, Finset.mem_univ τ⟩)
    simpa [MonoidAlgebra.coeff_single, Finsupp.single_apply, hτσ, Ne.symm hτσ] using hzero

lemma aug_size_two_shape (Θ : R p K) (hw : weight p K Θ = 0)
    (hs : size p K Θ ≤ 2) (hΘ : Θ ≠ 0) :
    ∃ σ τ : G p K, σ ≠ τ ∧
      Θ = MonoidAlgebra.single σ 1 - MonoidAlgebra.single τ 1 := by
  obtain ⟨hparts, hspl, hwpl⟩ := part_identities p K Θ
  have hp := size_nonneg p K (posPart p K Θ)
  have hn := size_nonneg p K (negPart p K Θ)
  have hsize : size p K Θ ≠ 0 := (size_eq_zero_iff p K Θ).not.mpr hΘ
  have hpone : size p K (posPart p K Θ) = 1 := by omega
  have hnone : size p K (negPart p K Θ) = 1 := by omega
  obtain ⟨σ, hσ⟩ := nonneg_size_one_single p K (posPart p K Θ)
    (fun τ => le_max_right (Θ.coeff τ) 0) hpone
  obtain ⟨τ, hτ⟩ := nonneg_size_one_single p K (negPart p K Θ)
    (fun τ => le_max_right (-Θ.coeff τ) 0) hnone
  refine ⟨σ, τ, ?_, ?_⟩
  · intro heq
    apply hΘ
    rw [hparts, hσ, hτ, heq, sub_self]
  · rw [hparts, hσ, hτ]
end Catalan

