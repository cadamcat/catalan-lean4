import Catalan.Density.TRelative

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma exists_selector (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2) :
    ∃ σ : T p q ≃ₐ[ℚ] T p q, Selector p q σ := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have instGaloisM : IsGalois ℚ (Msub p q) := isGalois_Msub_rat p q hp hq
  obtain ⟨τM, hτM, _, hcentral⟩ := exists_kummer_centralizer_element p q hp7 hq2 hdegree
  obtain ⟨σB, hlift⟩ := exists_T_lift p q hq τM
  let σ : T p q ≃ₐ[ℚ] T p q := σB.restrictScalars ℚ
  let r : (T p q ≃ₐ[ℚ] T p q) →* (Msub p q ≃ₐ[ℚ] Msub p q) :=
    AlgEquiv.restrictNormalHom (Msub p q)
  have hrestrict : r σ = τM.restrictScalars ℚ := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap (Msub p q) (T p q)).injective
    change algebraMap (Msub p q) (T p q) (σ.restrictNormal (Msub p q) x) =
      algebraMap (Msub p q) (T p q) (τM x)
    rw [σ.restrictNormal_commutes]
    exact hlift x
  refine ⟨σ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    let b : Bsub p q := ⟨(x : Omega), hx⟩
    have hb : algebraMap (Bsub p q) (T p q) b = x := by
      apply Subtype.ext
      exact algebraMap_Bsub_T_coe p q b
    rw [← hb]
    exact σB.commutes b
  · intro hσ
    apply hτM
    apply AlgEquiv.restrictScalars_injective ℚ
    change τM.restrictScalars ℚ = 1
    rw [← hrestrict, hσ, map_one]
  · have h := congrArg (AlgEquiv.restrictScalarsHom ℚ) (T_gal_pow_eq_one p q σB)
    simpa only [map_pow, map_one, AlgEquiv.restrictScalarsHom_apply] using h
  · intro γ hcomm
    have hcommM : r γ * τM.restrictScalars ℚ = τM.restrictScalars ℚ * r γ := by
      have h := congrArg r hcomm
      simpa only [map_mul, hrestrict] using h
    obtain ⟨hfixB, _⟩ := hcentral (r γ) hcommM
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
