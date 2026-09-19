import Catalan.Density.HDisjoint
import Catalan.Density.FiniteT
import Catalan.Density.TRelative

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma exists_T_lift_H (p q : ℕ) [Fact q.Prime] (hq : Odd q)
    (tau : Hsub p q ≃ₐ[F p] Hsub p q) :
    ∃ sigma : T p q ≃ₐ[Bsub p q] T p q,
      ∀ x : Hsub p q,
        sigma (algebraMap (Hsub p q) (T p q) x) =
          algebraMap (Hsub p q) (T p q) (tau x) := by
  have hHle : Hsub p q ≤ Tsub p q := le_sup_left
  have hBle : Bsub p q ≤ Tsub p q :=
    (show Bsub p q ≤ Msub p q from le_sup_left).trans le_sup_right
  let HT : IntermediateField (F p) (T p q) := IntermediateField.restrict hHle
  let BT : IntermediateField (F p) (T p q) := IntermediateField.restrict hBle
  let eH : Hsub p q ≃ₐ[F p] HT := IntermediateField.restrictAlgEquiv hHle
  let eB : Bsub p q ≃ₐ[F p] BT := IntermediateField.restrictAlgEquiv hBle
  have hHmap (x : Hsub p q) : (eH x : T p q) = algebraMap (Hsub p q) (T p q) x := by
    apply Subtype.ext
    rw [algebraMap_Hsub_T_coe]
    rfl
  have hBmap (x : Bsub p q) : (eB x : T p q) = algebraMap (Bsub p q) (T p q) x := by
    apply Subtype.ext
    rw [algebraMap_Bsub_T_coe]
    rfl
  have instFiniteT : FiniteDimensional (F p) (T p q) := finiteDimensional_T_over_F p q hq
  have instFiniteHT : FiniteDimensional (F p) HT := inferInstance
  have instFiniteBT : FiniteDimensional BT (T p q) :=
    FiniteDimensional.right (F p) BT (T p q)
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  have instGaloisHT : IsGalois (F p) HT := IsGalois.of_algEquiv eH
  have instGaloisT : IsGalois (F p) (T p q) := isGalois_Tsub_over_F p q hq.pos
  have instGaloisBT : IsGalois BT (T p q) :=
    IsGalois.tower_top_of_isGalois (F p) BT (T p q)
  have hinf : HT ⊓ BT = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hHx : (x : Omega) ∈ Hsub p q := (IntermediateField.mem_restrict hHle x).mp hx.1
    have hBx : (x : Omega) ∈ Bsub p q := (IntermediateField.mem_restrict hBle x).mp hx.2
    have hx0 : (x : Omega) ∈ (⊥ : IntermediateField (F p) Omega) := by
      rw [← Hsub_inf_Bsub p q hq]
      exact ⟨hHx, hBx⟩
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hx0
    apply IntermediateField.mem_bot.mpr
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
  let tauH : HT ≃ₐ[F p] HT := eH.symm.trans (tau.trans eH)
  obtain ⟨s, hs⟩ := IntermediateField.restrictRestrictAlgEquivMapHom_surjective HT BT hinf tauH
  have hfixB (b : Bsub p q) : s (algebraMap (Bsub p q) (T p q) b) =
      algebraMap (Bsub p q) (T p q) b := by
    rw [← hBmap]
    exact s.commutes (eB b)
  let sigma : T p q ≃ₐ[Bsub p q] T p q :=
    { toRingEquiv := s.toRingEquiv
      commutes' := hfixB }
  refine ⟨sigma, ?_⟩
  intro x
  change s (algebraMap (Hsub p q) (T p q) x) = algebraMap (Hsub p q) (T p q) (tau x)
  rw [← hHmap, ← hHmap]
  have hx := congrArg (fun u : HT ≃ₐ[F p] HT => ((u (eH x) : HT) : T p q)) hs
  rw [IntermediateField.restrictRestrictAlgEquivMapHom_apply] at hx
  simpa only [tauH, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] using hx

end Catalan.A3
