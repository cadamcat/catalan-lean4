module

public import Catalan.Density.TRelative

/-!
# `Catalan.Density.SelectorLift`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma selector_of_T_lift (p q : ℕ) [Fact q.Prime] (hp : 0 < p)
    (tauM : Msub p q ≃ₐ[Bsub p q] Msub p q) (hne : tauM ≠ 1)
    (hcentral : ∀ rho : Msub p q ≃ₐ[ℚ] Msub p q,
      rho * tauM.restrictScalars ℚ = tauM.restrictScalars ℚ * rho →
        ∀ b : Bsub p q, rho (algebraMap (Bsub p q) (Msub p q) b) =
          algebraMap (Bsub p q) (Msub p q) b)
    (sigmaB : T p q ≃ₐ[Bsub p q] T p q)
    (hlift : ∀ x : Msub p q,
      sigmaB (algebraMap (Msub p q) (T p q) x) =
        algebraMap (Msub p q) (T p q) (tauM x)) :
    Selector p q (sigmaB.restrictScalars ℚ) := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have instGaloisM : IsGalois ℚ (Msub p q) := isGalois_Msub_rat p q hp hq
  let σ : T p q ≃ₐ[ℚ] T p q := sigmaB.restrictScalars ℚ
  let r : (T p q ≃ₐ[ℚ] T p q) →* (Msub p q ≃ₐ[ℚ] Msub p q) :=
    AlgEquiv.restrictNormalHom (Msub p q)
  have hrestrict : r σ = tauM.restrictScalars ℚ := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap (Msub p q) (T p q)).injective
    change algebraMap (Msub p q) (T p q) (σ.restrictNormal (Msub p q) x) =
      algebraMap (Msub p q) (T p q) (tauM x)
    rw [σ.restrictNormal_commutes]
    exact hlift x
  have hrestrict' : r (sigmaB.restrictScalars ℚ) = tauM.restrictScalars ℚ := by
    simpa [σ] using hrestrict
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    let b : Bsub p q := ⟨(x : Omega), hx⟩
    have hb : algebraMap (Bsub p q) (T p q) b = x := by
      apply Subtype.ext
      exact algebraMap_Bsub_T_coe p q b
    rw [← hb]
    exact sigmaB.commutes b
  · intro hσ
    apply hne
    apply AlgEquiv.restrictScalars_injective ℚ
    change tauM.restrictScalars ℚ = 1
    rw [← hrestrict', hσ, map_one]
  · have h := congrArg (AlgEquiv.restrictScalarsHom ℚ) (T_gal_pow_eq_one p q sigmaB)
    simpa only [map_pow, map_one, AlgEquiv.restrictScalarsHom_apply] using h
  · intro γ hcomm
    have hcommM : r γ * tauM.restrictScalars ℚ = tauM.restrictScalars ℚ * r γ := by
      have h := congrArg r hcomm
      simpa only [map_mul, hrestrict'] using h
    have hfixB := hcentral (r γ) hcommM
    have hγB (b : Bsub p q) : γ (algebraMap (Bsub p q) (T p q) b) =
        algebraMap (Bsub p q) (T p q) b := by
      calc
        γ (algebraMap (Bsub p q) (T p q) b) =
            γ (algebraMap (Msub p q) (T p q) (algebraMap (Bsub p q) (Msub p q) b)) :=
          congrArg γ (IsScalarTower.algebraMap_apply (Bsub p q) (Msub p q) (T p q) b)
        _ = algebraMap (Msub p q) (T p q) (r γ (algebraMap (Bsub p q) (Msub p q) b)) :=
          (γ.restrictNormal_commutes (Msub p q) _).symm
        _ = algebraMap (Msub p q) (T p q) (algebraMap (Bsub p q) (Msub p q) b) :=
          congrArg (algebraMap (Msub p q) (T p q)) (hfixB b)
        _ = algebraMap (Bsub p q) (T p q) b :=
          (IsScalarTower.algebraMap_apply (Bsub p q) (Msub p q) (T p q) b).symm
    let γB : T p q ≃ₐ[Bsub p q] T p q :=
      { toRingEquiv := γ.toRingEquiv
        commutes' := hγB }
    have hγ : γB.restrictScalars ℚ = γ := by
      ext x
      rfl
    have h := congrArg (AlgEquiv.restrictScalarsHom ℚ) (T_gal_pow_eq_one p q γB)
    simpa only [map_pow, map_one, AlgEquiv.restrictScalarsHom_apply, hγ] using h

end Catalan.A3
