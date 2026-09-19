import Catalan.Density.BaseFields
import Catalan.Density.InertiaBridge
import Catalan.Density.InfiniteUnramified

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma unramifiedAbelianQ_finitePlaces (p q : ℕ)
    (J : IntermediateField (F p) Omega) (hJ : UnramifiedAbelianQ p q J) :
    ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 J),
      Algebra.IsUnramifiedAt (𝓞 (F p)) P.asIdeal := by
  let instFiniteJ : FiniteDimensional (F p) J := hJ.1
  let instNumberFieldJ : NumberField J := NumberField.of_module_finite (F p) J
  let instGaloisJ : IsGalois (F p) J := hJ.2.1
  intro P
  exact (inertiaTrivial_iff_isUnramifiedAt (F p) J P.asIdeal P.ne_bot).mp
    (hJ.2.2.2.2 P.asIdeal P.isMaximal P.ne_bot)


lemma unramifiedAbelianQ_infinitePlaces (p q : ℕ) (hq : Odd q)
    (J : IntermediateField (F p) Omega) (hJ : UnramifiedAbelianQ p q J) :
    IsUnramifiedAtInfinitePlaces (F p) J := by
  let instFiniteJ : FiniteDimensional (F p) J := hJ.1
  let instNumberFieldJ : NumberField J := NumberField.of_module_finite (F p) J
  let instGaloisJ : IsGalois (F p) J := hJ.2.1
  exact isUnramifiedAtInfinitePlaces_of_odd_exponent (F p) J q hq hJ.2.2.2.1


lemma unramifiedAbelianQ_of_unramifiedAtFinitePlaces (p q : ℕ)
    (J : IntermediateField (F p) Omega)
    (hfinite : FiniteDimensional (F p) J) (hgalois : IsGalois (F p) J)
    (hcomm : ∀ σ τ : J ≃ₐ[F p] J, σ * τ = τ * σ)
    (hpow : ∀ σ : J ≃ₐ[F p] J, σ ^ q = 1)
    (hunram : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 J),
      Algebra.IsUnramifiedAt (𝓞 (F p)) P.asIdeal) :
    UnramifiedAbelianQ p q J := by
  let instFiniteJ : FiniteDimensional (F p) J := hfinite
  let instNumberFieldJ : NumberField J := NumberField.of_module_finite (F p) J
  let instGaloisJ : IsGalois (F p) J := hgalois
  refine ⟨hfinite, hgalois, hcomm, hpow, ?_⟩
  intro P hP hPbot
  let instMaximalP : P.IsMaximal := hP
  exact (inertiaTrivial_iff_isUnramifiedAt (F p) J P hPbot).mpr
    (hunram ⟨P, hP.isPrime, hPbot⟩)

end Catalan.A3
