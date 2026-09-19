import Mathlib.FieldTheory.Galois.Basic
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldNormQuotient

set_option autoImplicit false

/-!
# Intrinsic fixed-field specialization

This module specializes the embedded subgroup and inertia comparisons to actual finite fixed fields and packages the intrinsic Frobenius quotient.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- Transport through a separable-closure equivalence identifies membership in
the intrinsic extension subgroup of a finite fixed-field extension with
membership in its ambient extension subgroup. -/
theorem intrinsicExtensionSubgroup_iff_ambientFixedField
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (τ : (intrinsicAbstractBase F).toSubgroup),
    let E := abstractRelativeFixedField K (SeparableClosure K) hJH
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        K (SeparableClosure K) H.field J hJH H.finite hJfinite
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        K (SeparableClosure K) H.field J hJH hJnormal
    let i : E →ₐ[F] SeparableClosure F :=
      e.symm.toAlgHom.comp E.val
    let EI := finiteGaloisAbstractExtensionOfEmbedding F E i
    let φ :
        Gal(SeparableClosure F / F) ≃*
          H.field.toSubgroup :=
      (AlgEquiv.autCongr e).trans
        (abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H.field).symm
    τ ∈ extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below ↔
      φ τ.1 ∈ extensionSubgroup H.field J hJH := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e τ
  let E := abstractRelativeFixedField K (SeparableClosure K) hJH
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field J hJH H.finite hJfinite
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field J hJH hJnormal
  let i : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp E.val
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E i
  let φ :
      Gal(SeparableClosure F / F) ≃*
        H.field.toSubgroup :=
    (AlgEquiv.autCongr e).trans
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H.field).symm
  let qH :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H.field J hJH hJnormal
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E i
  have hcompat :
      qH (QuotientGroup.mk (φ τ.1)) =
        qF (QuotientGroup.mk τ) :=
    fixedFieldQuotientEquiv_mk_compatibility
      K H J hJH e τ
  constructor
  · intro hτ
    have hF : (QuotientGroup.mk τ :
        (intrinsicAbstractBase F).toSubgroup ⧸
          extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hτ
    have hHimage :
        qH (QuotientGroup.mk (φ τ.1)) = 1 := by
      calc
        qH (QuotientGroup.mk (φ τ.1)) =
            qF (QuotientGroup.mk τ) :=
          hcompat
        _ = qF 1 := congrArg qF hF
        _ = 1 := map_one qF
    have hHquotient :
        (QuotientGroup.mk (φ τ.1) :
          H.field.toSubgroup ⧸
            extensionSubgroup H.field J hJH) = 1 := by
      apply qH.injective
      exact hHimage.trans (map_one qH).symm
    exact (QuotientGroup.eq_one_iff (φ τ.1)).1 hHquotient
  · intro hφτ
    have hHquotient :
        (QuotientGroup.mk (φ τ.1) :
          H.field.toSubgroup ⧸
            extensionSubgroup H.field J hJH) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hφτ
    have hFimage :
        qF (QuotientGroup.mk τ) = 1 := by
      calc
        qF (QuotientGroup.mk τ) =
            qH (QuotientGroup.mk (φ τ.1)) :=
          hcompat.symm
        _ = qH 1 := congrArg qH hHquotient
        _ = 1 := map_one qH
    have hFquotient :
        (QuotientGroup.mk τ :
          (intrinsicAbstractBase F).toSubgroup ⧸
            extensionSubgroup
              (intrinsicAbstractBase F) EI.field EI.below) = 1 := by
      apply qF.injective
      exact hFimage.trans (map_one qF).symm
    exact (QuotientGroup.eq_one_iff τ).1 hFquotient

/-- Membership in intrinsic extension inertia is equivalent, under the
fixed-field base equivalence, to membership in the ambient extension inertia. -/
theorem intrinsicExtensionInertia_iff_ambientFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (τ : (intrinsicAbstractBase F).toSubgroup),
    let E := abstractRelativeFixedField K (SeparableClosure K) hJH
    letI : FiniteDimensional K F :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField F :=
      finiteExtensionSpectralNormedField K F
    letI : ValuativeRel F :=
      finiteExtensionSpectralValuativeRel K F
    letI : IsNonarchimedeanLocalField F :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K F
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        K (SeparableClosure K) H.field J hJH H.finite hJfinite
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        K (SeparableClosure K) H.field J hJH hJnormal
    let i : E →ₐ[F] SeparableClosure F :=
      e.symm.toAlgHom.comp E.val
    let EI := finiteGaloisAbstractExtensionOfEmbedding F E i
    let φ :
        Gal(SeparableClosure F / F) ≃*
          H.field.toSubgroup :=
      (AlgEquiv.autCongr e).trans
        (abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H.field).symm
    τ ∈ (localResidueDatum F).extensionInertiaWithin
        (intrinsicAbstractBase F) EI.field EI.below ↔
      φ τ.1 ∈ (localResidueDatum K).extensionInertiaWithin
        H.field J hJH := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e τ
  let E := abstractRelativeFixedField K (SeparableClosure K) hJH
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  let : ValuativeRel F :=
    finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field J hJH H.finite hJfinite
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field J hJH hJnormal
  let i : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp E.val
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E i
  let φ :
      Gal(SeparableClosure F / F) ≃*
        H.field.toSubgroup :=
    (AlgEquiv.autCongr e).trans
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H.field).symm
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let tauRF : RF.field.toSubgroup :=
    ⟨τ.1, τ.2⟩
  let phiTauRH : RH.field.toSubgroup :=
    ⟨(φ τ.1).1, (φ τ.1).2⟩
  have hdegree :
      (localResidueDatum F).normalizedDegree RF tauRF =
        (localResidueDatum K).normalizedDegree RH phiTauRH := by
    simpa [RF, RH, φ, tauRF, phiTauRH] using
      intrinsicBase_normalizedDegree_eq_ambientFixedField K H e τ
  change
    (τ ∈ extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below ∧
      τ ∈ (localResidueDatum F).fieldInertiaWithin
        (intrinsicAbstractBase F)) ↔
    (φ τ.1 ∈ extensionSubgroup H.field J hJH ∧
      φ τ.1 ∈ (localResidueDatum K).fieldInertiaWithin H.field)
  constructor
  · rintro ⟨hτextension, hτinertia⟩
    refine
      ⟨(intrinsicExtensionSubgroup_iff_ambientFixedField
        K H J hJH e τ).1 hτextension, ?_⟩
    have hτRF :
        tauRF ∈
          (localResidueDatum F).fieldInertiaWithin RF.field := by
      exact hτinertia
    have hnormalizedRF :
        (localResidueDatum F).normalizedDegree RF tauRF = 1 := by
      change
        tauRF ∈
          ((localResidueDatum F).normalizedDegree RF).toMonoidHom.ker
      rw [(localResidueDatum F).normalizedDegree_ker RF]
      exact hτRF
    have hnormalizedRH :
        (localResidueDatum K).normalizedDegree RH phiTauRH = 1 :=
      hdegree.symm.trans hnormalizedRF
    change
      phiTauRH ∈
        (localResidueDatum K).fieldInertiaWithin RH.field
    rw [← (localResidueDatum K).normalizedDegree_ker RH]
    exact hnormalizedRH
  · rintro ⟨hφextension, hφinertia⟩
    refine
      ⟨(intrinsicExtensionSubgroup_iff_ambientFixedField
        K H J hJH e τ).2 hφextension, ?_⟩
    have hphiTauRH :
        phiTauRH ∈
          (localResidueDatum K).fieldInertiaWithin RH.field := by
      exact hφinertia
    have hnormalizedRH :
        (localResidueDatum K).normalizedDegree RH phiTauRH = 1 := by
      change
        phiTauRH ∈
          ((localResidueDatum K).normalizedDegree RH).toMonoidHom.ker
      rw [(localResidueDatum K).normalizedDegree_ker RH]
      exact hphiTauRH
    have hnormalizedRF :
        (localResidueDatum F).normalizedDegree RF tauRF = 1 :=
      hdegree.trans hnormalizedRH
    change
      tauRF ∈
        (localResidueDatum F).fieldInertiaWithin RF.field
    rw [← (localResidueDatum F).normalizedDegree_ker RF]
    exact hnormalizedRF

/-- The type of algebra equivalences from the intrinsic separable closure of a
finite fixed field to the ambient separable closure. -/
abbrev intrinsicFixedFieldSeparableClosureEquiv
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K)) :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  @AlgEquiv F (SeparableClosure F) (SeparableClosure K)
    _ _ _
    (separableClosure F (AlgebraicClosure F)).algebra
    F.val.toRingHom.toAlgebra

/-- The intrinsic base subgroup modulo extension inertia for a finite
fixed-field extension, using the chosen separable-closure equivalence. -/
abbrev intrinsicFixedFieldFrobeniusQuotient
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H) :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  letI : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let E := abstractRelativeFixedField K (SeparableClosure K) hJH
  letI : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  letI : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  letI : ValuativeRel F :=
    finiteExtensionSpectralValuativeRel K F
  letI : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field J hJH H.finite hJfinite
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field J hJH hJnormal
  let i : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp E.val
  let EI := finiteGaloisAbstractExtensionOfEmbedding F E i
  (intrinsicAbstractBase F).toSubgroup ⧸
    (localResidueDatum F).extensionInertiaWithin
      (intrinsicAbstractBase F) EI.field EI.below

end LocalClassFieldTheory
