import Catalan.Density.BaseFields

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma isGalois_Hsub (p q : ℕ) : IsGalois (F p) (Hsub p q) := by
  let instNormalFamily : ∀ J : {J : IntermediateField (F p) Omega |
      UnramifiedAbelianQ p q J}, Normal (F p) J.val :=
    fun J => J.property.2.1.to_normal
  let instNormalH : Normal (F p) (Hsub p q) := by
    unfold Hsub
    rw [sSup_eq_iSup']
    infer_instance
  exact {}

private lemma fixes_Hsub_of_fixes_witnesses (p q : ℕ)
    (σ : Omega ≃ₐ[F p] Omega)
    (hσ : ∀ (J : IntermediateField (F p) Omega), UnramifiedAbelianQ p q J →
      ∀ x ∈ J, σ x = x) : ∀ x ∈ Hsub p q, σ x = x := by
  have hle : Hsub p q ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    apply sSup_le
    intro J hJ
    apply (IntermediateField.le_iff_le (Subgroup.zpowers σ) J).mpr
    apply Subgroup.zpowers_le.mpr
    exact (IntermediateField.mem_fixingSubgroup_iff J σ).mpr (hσ J hJ)
  exact (IntermediateField.mem_fixingSubgroup_iff (Hsub p q) σ).mp
    ((IntermediateField.le_iff_le (Subgroup.zpowers σ) (Hsub p q)).mp hle
      (Subgroup.mem_zpowers σ))


lemma Hsub_gal_pow_eq_one (p q : ℕ) (σ : Hsub p q ≃ₐ[F p] Hsub p q) :
    σ ^ q = 1 := by
  let instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  let instAlgebraicFOmega : Algebra.IsAlgebraic (F p) Omega :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (F p)
  let instAlgClosureFOmega : IsAlgClosure (F p) Omega := ⟨inferInstance, inferInstance⟩
  let instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := F p) (E := Omega) (K₁ := Hsub p q) σ
  have hfix : ∀ x ∈ Hsub p q, (s ^ q) x = x := by
    apply fixes_Hsub_of_fixes_witnesses p q
    intro J hJ
    let instGaloisJ : IsGalois (F p) J := hJ.2.1
    apply (AlgEquiv.restrictNormal_eq_one_iff J (s ^ q)).mp
    change (AlgEquiv.restrictNormalHom J) (s ^ q) = 1
    rw [map_pow]
    exact hJ.2.2.2.1 _
  have h := (AlgEquiv.restrictNormal_eq_one_iff (Hsub p q) (s ^ q)).mpr hfix
  change (AlgEquiv.restrictNormalHom (Hsub p q)) (s ^ q) = 1 at h
  rwa [map_pow, hs] at h


lemma Hsub_gal_mul_comm (p q : ℕ) (σ τ : Hsub p q ≃ₐ[F p] Hsub p q) :
    σ * τ = τ * σ := by
  let instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  let instAlgebraicFOmega : Algebra.IsAlgebraic (F p) Omega :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (F p)
  let instAlgClosureFOmega : IsAlgClosure (F p) Omega := ⟨inferInstance, inferInstance⟩
  let instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := F p) (E := Omega) (K₁ := Hsub p q) σ
  obtain ⟨t, ht⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := F p) (E := Omega) (K₁ := Hsub p q) τ
  have hfix : ∀ x ∈ Hsub p q, ((s * t) * (t * s)⁻¹) x = x := by
    apply fixes_Hsub_of_fixes_witnesses p q
    intro J hJ
    let instGaloisJ : IsGalois (F p) J := hJ.2.1
    apply (AlgEquiv.restrictNormal_eq_one_iff J _).mp
    change (AlgEquiv.restrictNormalHom J) ((s * t) * (t * s)⁻¹) = 1
    rw [map_mul, map_inv, map_mul, map_mul]
    exact mul_inv_eq_one.mpr (hJ.2.2.1 _ _)
  have h := (AlgEquiv.restrictNormal_eq_one_iff (Hsub p q) _).mpr hfix
  change (AlgEquiv.restrictNormalHom (Hsub p q)) ((s * t) * (t * s)⁻¹) = 1 at h
  rw [map_mul, map_inv, map_mul, map_mul, hs, ht] at h
  exact mul_inv_eq_one.mp h

end Catalan.A3
