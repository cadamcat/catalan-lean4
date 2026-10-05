module

public import Catalan.Density.FrobeniusStabilizer
public import Catalan.Density.CyclicCentralizer

/-!
# `Catalan.Density.FrobeniusPower`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
open scoped Pointwise
noncomputable section
namespace Catalan.A3

lemma arithmeticFrob_nonzero_power_of_prime_centralizer
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (q : ℕ) (hq : q.Prime) (σ : L ≃ₐ[ℚ] L)
    (hne : σ ≠ 1) (hpow : σ ^ q = 1)
    (hcentral : ∀ τ : L ≃ₐ[ℚ] L, τ * σ = σ * τ → τ ^ q = 1)
    (ell : ℕ) (hell : ell.Prime) (P : Ideal (𝓞 L))
    (hσP : PreservesPrime σ P) (ρ : L ≃ₐ[ℚ] L) (hρ : IsArithmeticFrob ell P ρ) :
    ∃ a : ℕ, 0 < a ∧ a < q ∧ IsArithmeticFrob ell P (σ ^ a) := by
  classical
  let D := MulAction.stabilizer (L ≃ₐ[ℚ] L) P
  have hDρ : D = Subgroup.zpowers ρ := by
    ext τ
    exact (preservesPrime_iff_mem_stabilizer ℚ L τ P).symm.trans
      (preservesPrime_iff_mem_zpowers_of_arithmeticFrob L ell hell P ρ hρ τ)
  let instCyclicD : IsCyclic D := by
    rw [hDρ]
    infer_instance
  have hσD : σ ∈ D := (preservesPrime_iff_mem_stabilizer ℚ L σ P).mp hσP
  have hDσ : D = Subgroup.zpowers σ :=
    Catalan.GroupTheory.cyclic_subgroup_eq_zpowers_of_centralizer_exponent
      (L ≃ₐ[ℚ] L) q hq σ hne hpow hcentral D hσD
  have hρne : ρ ≠ 1 := by
    intro h
    apply hne
    simpa [hDρ, h] using hσD
  have hρD : ρ ∈ D := hDρ.symm ▸ Subgroup.mem_zpowers ρ
  have hρσ : ρ ∈ Subgroup.zpowers σ := hDσ ▸ hρD
  have horder : orderOf σ = q :=
    (hq.eq_one_or_self_of_dvd (orderOf σ) (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
      (fun h => hne (orderOf_eq_one_iff.mp h))
  obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hρσ)
  refine ⟨a, ?_, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    intro ha0
    apply hρne
    rw [← hea, ha0, pow_zero]
  · simpa only [horder] using Finset.mem_range.mp ha
  · simpa only [hea] using hρ

end Catalan.A3
