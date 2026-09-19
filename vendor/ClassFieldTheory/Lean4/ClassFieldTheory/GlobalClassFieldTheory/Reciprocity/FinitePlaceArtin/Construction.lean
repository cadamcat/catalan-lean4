import ClassFieldTheory.AlgebraicNumberTheory.Completion.Comparison
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Quotient
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue

set_option autoImplicit false

/-!
# Construction of finite-place Artin homomorphisms

This module constructs the local Artin map for a chosen extension of a finite place and transports it through the actual decomposition group into the global Galois group.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

/-- A completion attached to a nonarchimedean absolute value has an ultrametric distance. -/
theorem finitePlaceArtinCompletionIsUltrametricDist
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    IsUltrametricDist vF.Completion :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
      vF hvF)

/-- The valued-field structure on a finite-place completion induced by its nonarchimedean norm. -/
@[reducible]
noncomputable def finitePlaceArtinCompletionValued
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    Valued vF.Completion ℝ≥0 :=
  letI : IsUltrametricDist vF.Completion :=
    finitePlaceArtinCompletionIsUltrametricDist vF hvF
  NormedField.toValued

/-- The valuation relation on a finite-place completion induced by its canonical valuation. -/
@[reducible]
noncomputable def finitePlaceArtinCompletionValuativeRel
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    ValuativeRel vF.Completion := by
  letI : Valued vF.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vF hvF
  exact ValuativeRel.ofValuation
    (Valued.v : Valuation vF.Completion ℝ≥0)

/-- The canonical valued structure makes a locally compact finite-place completion a nonarchimedean local field. -/
theorem
    finitePlaceArtinCompletionIsNonarchimedeanLocalField
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    [IsUltrametricDist vF.Completion]
    [NontriviallyNormedField vF.Completion]
    [(NormedField.valuation
      (K := vF.Completion)).IsNontrivial]
    [LocallyCompactSpace vF.Completion] :
    letI : Valued vF.Completion ℝ≥0 :=
      finitePlaceArtinCompletionValued vF hvF
    letI : ValuativeRel vF.Completion :=
      finitePlaceArtinCompletionValuativeRel vF hvF
    IsNonarchimedeanLocalField vF.Completion := by
  let : Valued vF.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vF hvF
  let vC : Valuation vF.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vF.Completion)).IsNontrivial)
  let : ValuativeRel vF.Completion :=
    finitePlaceArtinCompletionValuativeRel vF hvF
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vF.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vF.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vF.Completion ℝ≥0
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

/-- The concrete finite-completion ring equivalence agrees with the
relative-completion algebra equivalence on underlying rings. -/
theorem finitePlaceCompletionRingEquiv_eq_relative
    {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    finitePlaceCompletionRingEquiv v =
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv := by
  apply RingEquiv.ext
  intro x
  change
    finitePlaceCompletionRingHom v x =
      relativeFinitePlaceCompletionRingHom v x
  refine UniformSpace.Completion.induction_on
    (α := WithAbs
      (NumberField.HeightOneSpectrum.adicAbv F v)) x ?_ ?_
  · exact isClosed_eq
      (finitePlaceCompletionRingHom_isometry v).continuous
      (relativeFinitePlaceCompletionRingHom_isometry v).continuous
  · intro a
    rw [finitePlaceCompletionRingHom_coe,
      relativeFinitePlaceCompletionRingHom_coe]
    rfl

/-- The finite-place Artin homomorphism associated with a specified
extension of the base adic absolute value to the global extension. -/
noncomputable def finitePlaceArtinMonoidHomOfExtension
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  letI :=
    LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  letI : IsAbelianGalois vK.Completion E :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w
  letI : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  letI : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
  letI : IsUltrametricDist vK.Completion :=
    finitePlaceArtinCompletionIsUltrametricDist vK hvKna
  letI : Valued vK.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vK hvKna
  let vC : Valuation vK.Completion ℝ≥0 :=
    Valued.v
  letI : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  letI : ValuativeRel vK.Completion :=
    finitePlaceArtinCompletionValuativeRel vK hvKna
  letI : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  letI : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  letI : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  letI : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  exact
    (absoluteValueDecompositionGroup K w.1).subtype.comp
      (eD.symm.toMonoidHom.comp
        ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
          vK.Completion E).comp eK.symm.toMonoidHom))

/-- Pointwise formula for the finite-place Artin homomorphism attached
to a specified extension of the base absolute value. -/
theorem finitePlaceArtinMonoidHomOfExtension_apply
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    let vK :=
      NumberField.HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI :=
      LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
    letI :=
      LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
    let E :=
      AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : FiniteDimensional vK.Completion E :=
      AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
    letI : IsAbelianGalois vK.Completion E :=
      LocalClassFieldTheory.localizedCompletion_isAbelianGalois
        vK hvK w
    letI : NontriviallyNormedField vK.Completion :=
      absoluteValueExtension_completionNontriviallyNormedField
        vK hvK
    letI : LocallyCompactSpace vK.Completion :=
      AbsoluteValue.Completion.locallyCompactSpace
        (finitePlaceCompletionBaseMap_isometry v)
    letI : IsUltrametricDist vK.Completion :=
      IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
        (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
          vK
          (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
            K v))
    letI : Valued vK.Completion ℝ≥0 :=
      NormedField.toValued
    let vC : Valuation vK.Completion ℝ≥0 :=
      Valued.v
    letI : vC.IsNontrivial :=
      (inferInstance :
        (NormedField.valuation
          (K := vK.Completion)).IsNontrivial)
    letI : ValuativeRel vK.Completion :=
      ValuativeRel.ofValuation vC
    letI : vC.Compatible :=
      Valuation.Compatible.ofValuation vC
    letI : ValuativeRel.IsNontrivial vK.Completion :=
      (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
        inferInstance
    letI : IsValuativeTopology vK.Completion :=
      isValuativeTopology_of_valued_ofValuation
        vK.Completion ℝ≥0
    letI : IsNonarchimedeanLocalField vK.Completion :=
      { toIsValuativeTopology := inferInstance
        toLocallyCompactSpace := inferInstance
        toIsNontrivial := inferInstance }
    let eD :
        absoluteValueDecompositionGroup K w.1 ≃*
          (E ≃ₐ[vK.Completion] E) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eK :
        vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x =
      (absoluteValueDecompositionGroup K w.1).subtype
        (eD.symm
          (LocalClassFieldTheory.abelianLocalArtinMonoidHom
            vK.Completion E (eK.symm x))) := by
  rfl

/-- The canonical completion input used by the finite-place local Artin map. -/
noncomputable def finitePlaceLocalArtinInputMonoidHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →*
      (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ :=
  (finitePlaceCompletionUnitsContinuousMulEquiv v).symm.toMonoidHom

/-- Evaluation of the canonical completion input for the finite-place local
Artin map. -/
noncomputable def finitePlaceLocalArtinInput
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ :=
  finitePlaceLocalArtinInputMonoidHom v x

/-- The canonical valuation relation used on a finite-place completion by
the local Artin construction. -/
@[reducible]
noncomputable def finitePlaceLocalArtinCompletionValuativeRel
    (v : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel
      (NumberField.HeightOneSpectrum.adicAbv K v).Completion :=
  finitePlaceArtinCompletionValuativeRel
    (NumberField.HeightOneSpectrum.adicAbv K v)
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)

/-- The canonical nonarchimedean-local-field certificate used on a
finite-place completion by the local Artin construction. -/
theorem
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField
    (v : HeightOneSpectrum (𝓞 K)) :
    @IsNonarchimedeanLocalField
      (NumberField.HeightOneSpectrum.adicAbv K v).Completion
      (inferInstance : Field
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
      (finitePlaceLocalArtinCompletionValuativeRel v)
      (inferInstance : TopologicalSpace
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let : IsUltrametricDist vK.Completion :=
    finitePlaceArtinCompletionIsUltrametricDist vK hvKna
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  exact
    finitePlaceArtinCompletionIsNonarchimedeanLocalField
      vK hvKna

/-- The canonical algebra structure on the localized completion used by the
finite-place local Artin map. -/
@[reducible]
noncomputable def finitePlaceLocalArtinLocalizedAlgebra
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    Algebra vK.Completion
      (AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact inferInstance

omit [IsAbelianGalois K L] in
/-- The canonical finite-dimensional certificate for the localized
completion used by the finite-place local Artin map. -/
theorem finitePlaceLocalArtinFiniteDimensional
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    FiniteDimensional vK.Completion E := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  exact
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      vK hvK w

omit hKLfinite in
/-- The canonical abelian-Galois certificate for the localized completion
used by the finite-place local Artin map. -/
theorem finitePlaceLocalArtinIsAbelianGalois
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (_hKLfinite : FiniteDimensional K L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    IsAbelianGalois vK.Completion E := by
  let : FiniteDimensional K L := _hKLfinite
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional vK.Completion E :=
    finitePlaceLocalArtinFiniteDimensional
      (hKLfinite := _hKLfinite) v w
  exact
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w

/-- The local Artin homomorphism on the algebraic localization attached to a chosen extension of a finite place. -/
noncomputable def finitePlaceLocalArtinMonoidHom
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    (v.adicCompletion K)ˣ →* (E ≃ₐ[vK.Completion] E) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  letI : FiniteDimensional vK.Completion E :=
    finitePlaceLocalArtinFiniteDimensional v w
  letI : IsAbelianGalois vK.Completion E :=
    finitePlaceLocalArtinIsAbelianGalois v w hKLfinite
  letI : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom
      vK.Completion E).comp
        (finitePlaceLocalArtinInputMonoidHom v)

/-- Evaluation of the localized finite-place Artin homomorphism through the canonical completion equivalence. -/
theorem finitePlaceLocalArtinMonoidHom_apply
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : FiniteDimensional vK.Completion E :=
      AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
    letI : IsAbelianGalois vK.Completion E :=
      LocalClassFieldTheory.localizedCompletion_isAbelianGalois
        vK hvK w
    letI : NontriviallyNormedField vK.Completion :=
      absoluteValueExtension_completionNontriviallyNormedField
        vK hvK
    letI : LocallyCompactSpace vK.Completion :=
      AbsoluteValue.Completion.locallyCompactSpace
        (finitePlaceCompletionBaseMap_isometry v)
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
    letI : IsUltrametricDist vK.Completion :=
      finitePlaceArtinCompletionIsUltrametricDist vK hvKna
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceArtinCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceArtinCompletionValuativeRel vK hvKna
    letI : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceArtinCompletionIsNonarchimedeanLocalField
        vK hvKna
    let eK :
        vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
      finitePlaceCompletionUnitsContinuousMulEquiv v
    finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom
        vK.Completion E (eK.symm x) := by
  rfl

/-- Evaluation of the localized finite-place Artin homomorphism with all
canonical completion data hidden behind named opaque terms.  This is the
normalization API for clients that must not unfold the construction's
dependent instance tower. -/
theorem finitePlaceLocalArtinMonoidHom_apply_normalized
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x =
      @LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion
          (NumberField.HeightOneSpectrum.adicAbv K v) w)
        (inferInstance : Field
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (inferInstance : Field
          (AlgebraicNumberTheory.Valuations.LocalizedCompletion
            (NumberField.HeightOneSpectrum.adicAbv K v) w))
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (finitePlaceLocalArtinInput v x) := by
  rfl

/-- Elementwise evaluation of the normalized localized finite-place Artin
map.  This form lets clients transport an action without asking the
elaborator to rewrite an equality of automorphisms carrying a dependent
instance tower. -/
theorem finitePlaceLocalArtinMonoidHom_apply_normalized_at
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ)
    (z : AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w) :
    finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x z =
      (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion
          (NumberField.HeightOneSpectrum.adicAbv K v) w)
        (inferInstance : Field
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (inferInstance : Field
          (AlgebraicNumberTheory.Valuations.LocalizedCompletion
            (NumberField.HeightOneSpectrum.adicAbv K v) w))
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (finitePlaceLocalArtinInput v x)) z := by
  exact
    congrArg (fun sigma => sigma z)
      (finitePlaceLocalArtinMonoidHom_apply_normalized
        (K := K) (L := L) v w x)

/-- The decomposition-group inclusion transporting localized automorphisms to the global Galois group. -/
noncomputable def finitePlaceLocalToGlobalMonoidHom
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    (E ≃ₐ[vK.Completion] E) →* (L ≃ₐ[K] L) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  letI : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  exact
    (absoluteValueDecompositionGroup K w.1).subtype.comp
      eD.symm.toMonoidHom

/-- The finite-place Artin map factors through the localized Artin map and the decomposition-group inclusion. -/
theorem finitePlaceArtinMonoidHomOfExtension_factor
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w =
      (finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w).comp
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w) := by
  rfl

/-- Evaluation of the global finite-place Artin homomorphism with the
localized Artin map and its decomposition-group transport expressed through
the canonical named data. -/
theorem finitePlaceArtinMonoidHomOfExtension_apply_normalized
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    letI : Algebra vK.Completion E :=
      finitePlaceLocalArtinLocalizedAlgebra v w
    let eD :
        absoluteValueDecompositionGroup K w.1 ≃*
          (E ≃ₐ[vK.Completion] E) :=
      decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x =
      (absoluteValueDecompositionGroup K w.1).subtype
        (eD.symm
          (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
            vK.Completion E
            (inferInstance : Field vK.Completion)
            (inferInstance : Field E)
            (finitePlaceLocalArtinLocalizedAlgebra v w)
            (finitePlaceLocalArtinCompletionValuativeRel v)
            (inferInstance : TopologicalSpace vK.Completion)
            (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
            (finitePlaceLocalArtinFiniteDimensional v w)
            (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
            (finitePlaceLocalArtinInput v x))) := by
  rw [finitePlaceArtinMonoidHomOfExtension_factor,
    MonoidHom.comp_apply,
    finitePlaceLocalArtinMonoidHom_apply_normalized]
  rfl

/-- The finite-place Artin homomorphism from the concrete adic
completion into the actual global Galois group.  Its image is contained
in the decomposition group at the chosen extension above `v`. -/
noncomputable def chosenFinitePlaceArtinMonoidHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  finitePlaceArtinMonoidHomOfExtension
    (K := K) (L := L) v
    (chosenFinitePlaceExtension (L := L) v)

end Reciprocity
end GlobalClassFieldTheory
