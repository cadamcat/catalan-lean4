module

public import Catalan.Density.BaseFixing

/-!
# `Catalan.Density.MCentralizer`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma exists_kummer_centralizer_element (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2) :
    ∃ τ : Msub p q ≃ₐ[Bsub p q] Msub p q,
      τ ≠ 1 ∧ τ ^ q = 1 ∧
      ∀ σ : Msub p q ≃ₐ[ℚ] Msub p q,
        σ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ →
          (∀ b : Bsub p q, σ (algebraMap (Bsub p q) (Msub p q) b) =
            algebraMap (Bsub p q) (Msub p q) b) ∧ σ ^ q = 1 := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp2 : p ≠ 2 := by omega
  have instCyclicF : IsCyclic (G p (F p)) := gal_F_cyclic p Fact.out
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G p (F p))
  have horder : orderOf γ = (p - 1) / 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, card_gal_F p Fact.out hp2]
  obtain ⟨f, hf0, _, hrig⟩ := F_unit_dual_projective_generator p q hp7 hq2 hdegree γ hγ
  obtain ⟨τ, hτ⟩ := exists_kummer_aut_of_functional p q f
  refine ⟨τ, ?_, kummerGal_pow_eq_one p q τ, ?_⟩
  · intro heq
    rw [heq, kummerFunctional_one] at hτ
    exact hf0 hτ.symm
  · intro σ hcomm
    obtain ⟨k, hk, hkpow⟩ := Finset.mem_image.mp
      ((mem_zpowers_iff_mem_range_orderOf).mp (hγ (restrictToF p q hp σ)))
    have hkn : k < (p - 1) / 2 := by
      rw [Finset.mem_range, horder] at hk
      exact hk
    have heigen := commuting_kummerFunctional_eigen p q hp σ τ hcomm
    rw [hτ, ← hkpow, map_pow] at heigen
    obtain ⟨hk0, hscalar⟩ := hrig k hkn (cyclotomicScalar p q σ)⁻¹ heigen
    have hF : restrictToF p q hp σ = 1 := by rw [← hkpow, hk0, pow_zero]
    have hχ : cyclotomicScalar p q σ = 1 := inv_eq_one.mp hscalar
    exact ⟨fixes_B_of_restrictToF_eq_one_of_zeta_fixed p q hp σ hF
      ((cyclotomicScalar_eq_one_iff p q σ).mp hχ),
      abs_pow_eq_one_of_restrictToF_eq_one_of_scalar_eq_one p q hp σ hF hχ⟩

end Catalan.A3
