module

public import Catalan.Density.TTower
public import Catalan.Density.SupExt

/-!
# `Catalan.Density.TRelative`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

private lemma T_algEquiv_ext (p q : ℕ)
    (σ τ : T p q ≃ₐ[Bsub p q] T p q)
    (hH : ∀ x : Hsub p q, σ (algebraMap (Hsub p q) (T p q) x) =
      τ (algebraMap (Hsub p q) (T p q) x))
    (hM : ∀ x : Msub p q, σ (algebraMap (Msub p q) (T p q) x) =
      τ (algebraMap (Msub p q) (T p q) x)) : σ = τ := by
  have h := FieldTower.sup_algHom_ext (F p) Omega (T p q) (Hsub p q) (Msub p q)
    (σ.toAlgHom.restrictScalars (F p)) (τ.toAlgHom.restrictScalars (F p)) hH hM
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun h x

lemma T_gal_pow_eq_one (p q : ℕ) [Fact q.Prime]
    (σ : T p q ≃ₐ[Bsub p q] T p q) : σ ^ q = 1 := by
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  have instGaloisM : IsGalois (Bsub p q) (Msub p q) :=
    isGalois_Msub_over_B p q (Fact.out : q.Prime).pos
  let rH : (T p q ≃ₐ[Bsub p q] T p q) →* (Hsub p q ≃ₐ[F p] Hsub p q) :=
    (AlgEquiv.restrictNormalHom (Hsub p q)).comp (AlgEquiv.restrictScalarsHom (F p))
  let rM : (T p q ≃ₐ[Bsub p q] T p q) →* (Msub p q ≃ₐ[Bsub p q] Msub p q) :=
    AlgEquiv.restrictNormalHom (Msub p q)
  have hH : rH (σ ^ q) = 1 := by
    rw [map_pow]
    exact Hsub_gal_pow_eq_one p q (rH σ)
  have hM : rM (σ ^ q) = 1 := by
    rw [map_pow]
    exact kummerGal_pow_eq_one p q (rM σ)
  apply T_algEquiv_ext p q (σ ^ q) 1
  · intro x
    have h := ((σ ^ q).restrictScalars (F p)).restrictNormal_commutes (Hsub p q) x
    change algebraMap (Hsub p q) (T p q) (rH (σ ^ q) x) =
      (σ ^ q) (algebraMap (Hsub p q) (T p q) x) at h
    rw [hH] at h
    exact h.symm
  · intro x
    have h := (σ ^ q).restrictNormal_commutes (Msub p q) x
    change algebraMap (Msub p q) (T p q) (rM (σ ^ q) x) =
      (σ ^ q) (algebraMap (Msub p q) (T p q) x) at h
    rw [hM] at h
    exact h.symm

lemma T_gal_mul_comm (p q : ℕ) [Fact q.Prime]
    (σ τ : T p q ≃ₐ[Bsub p q] T p q) : σ * τ = τ * σ := by
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  have instGaloisM : IsGalois (Bsub p q) (Msub p q) :=
    isGalois_Msub_over_B p q (Fact.out : q.Prime).pos
  let instKummerComm : CommGroup (Msub p q ≃ₐ[Bsub p q] Msub p q) :=
    kummerGalCommGroup p q
  let rH : (T p q ≃ₐ[Bsub p q] T p q) →* (Hsub p q ≃ₐ[F p] Hsub p q) :=
    (AlgEquiv.restrictNormalHom (Hsub p q)).comp (AlgEquiv.restrictScalarsHom (F p))
  let rM : (T p q ≃ₐ[Bsub p q] T p q) →* (Msub p q ≃ₐ[Bsub p q] Msub p q) :=
    AlgEquiv.restrictNormalHom (Msub p q)
  have hH : rH (σ * τ) = rH (τ * σ) := by
    rw [map_mul, map_mul]
    exact Hsub_gal_mul_comm p q (rH σ) (rH τ)
  have hM : rM (σ * τ) = rM (τ * σ) := by
    rw [map_mul, map_mul, mul_comm]
  apply T_algEquiv_ext p q (σ * τ) (τ * σ)
  · intro x
    calc
      (σ * τ) (algebraMap (Hsub p q) (T p q) x) =
          algebraMap (Hsub p q) (T p q) (rH (σ * τ) x) :=
        (((σ * τ).restrictScalars (F p)).restrictNormal_commutes (Hsub p q) x).symm
      _ = algebraMap (Hsub p q) (T p q) (rH (τ * σ) x) := by rw [hH]
      _ = (τ * σ) (algebraMap (Hsub p q) (T p q) x) :=
        ((τ * σ).restrictScalars (F p)).restrictNormal_commutes (Hsub p q) x
  · intro x
    calc
      (σ * τ) (algebraMap (Msub p q) (T p q) x) =
          algebraMap (Msub p q) (T p q) (rM (σ * τ) x) :=
        ((σ * τ).restrictNormal_commutes (Msub p q) x).symm
      _ = algebraMap (Msub p q) (T p q) (rM (τ * σ) x) := by rw [hM]
      _ = (τ * σ) (algebraMap (Msub p q) (T p q) x) :=
        (τ * σ).restrictNormal_commutes (Msub p q) x

lemma exists_T_lift (p q : ℕ) (hq : 0 < q)
    (τ : Msub p q ≃ₐ[Bsub p q] Msub p q) :
    ∃ σ : T p q ≃ₐ[Bsub p q] T p q,
      ∀ x : Msub p q,
        σ (algebraMap (Msub p q) (T p q) x) =
          algebraMap (Msub p q) (T p q) (τ x) := by
  have instGaloisM : IsGalois (Bsub p q) (Msub p q) := isGalois_Msub_over_B p q hq
  have instGaloisT : IsGalois (Bsub p q) (T p q) := isGalois_Tsub_over_B p q hq
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := Bsub p q) (K₁ := Msub p q) (E := T p q) τ
  refine ⟨σ, ?_⟩
  intro x
  have h := σ.restrictNormal_commutes (Msub p q) x
  change algebraMap (Msub p q) (T p q) ((AlgEquiv.restrictNormalHom (Msub p q)) σ x) =
    σ (algebraMap (Msub p q) (T p q) x) at h
  rw [hσ] at h
  exact h.symm

end Catalan.A3
