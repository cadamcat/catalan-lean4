import ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
import ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option autoImplicit false

/-!
# Integer rings in the two finite-place completion models

This file restricts the canonical equivalences between the absolute-value and
adic completion models to their valuation rings.  It also identifies the
residue field of a rational finite-place completion.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The canonical equivalence of completion fields identifies their two
valuation rings. -/
theorem finitePlaceCompletionRingEquiv_mem_integers_iff
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (x : ChosenFinitePlaceBaseCompletion (K := K) v) :
    finitePlaceCompletionRingEquiv v x ∈
        v.adicCompletionIntegers K ↔
      x ∈ 𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] := by
  symm
  have hnorm :
      ‖finitePlaceCompletionRingEquiv v x‖ = ‖x‖ :=
    (finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
      (map_zero (finitePlaceCompletionRingHom v)) x
  rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
    (HeightOneSpectrum.adicAbv K v)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K v) x]
  constructor
  · intro hx
    apply mem_adicCompletionIntegers_of_norm_le_one v
    simpa only [hnorm] using hx
  · intro hx
    have hxnorm :=
      norm_le_one_of_mem_adicCompletionIntegers v hx
    simpa only [hnorm] using hxnorm

/-- The canonical equivalence between the valuation ring of the
absolute-value completion and mathlib's adic completion integers. -/
noncomputable def finitePlaceCompletionIntegerRingEquiv
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] ≃+*
      v.adicCompletionIntegers K :=
  RingEquiv.restrict
    (finitePlaceCompletionRingEquiv v)
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
    (v.adicCompletionIntegers K).toSubring
      (fun x =>
        (finitePlaceCompletionRingEquiv_mem_integers_iff v x).symm)

/-- The canonical equivalence between the valuation ring of the chosen
localized completion and the concrete adic completion integers at its
centre. -/
noncomputable def chosenFinitePlaceLocalizedIntegerRingEquiv
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    let W :=
      finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)
    𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v] ≃+*
      W.adicCompletionIntegers L := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  let eField : E ≃+* W.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK (RayClass.adicAbv_isNontrivial v) w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  exact
    RingEquiv.restrict eField 𝒪[E]
      (W.adicCompletionIntegers L).toSubring (by
        intro x
        symm
        change
          eField x ∈ W.adicCompletionIntegers L ↔
            x ∈ 𝒪[E]
        change
          finitePlaceExtensionAdicCompletionRingEquiv
                (K := K) (L := L) v w
                (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
                  vK (RayClass.adicAbv_isNontrivial v) w x) ∈
              W.adicCompletionIntegers L ↔
            x ∈ 𝒪[E]
        rw [
          finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff,
          mem_absoluteValueCompletionIntegers_iff,
          localizedCompletion_mem_integers_iff_norm_le_one
            vK w
            (HeightOneSpectrum.isNonarchimedean_adicAbv K v) x]
        rfl)

/-- The residue field of the absolute-value completion at a rational finite
place has cardinality equal to the natural prime represented by that place. -/
theorem rationalFinitePlaceCompletion_residueField_card
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card
        𝓀[ChosenFinitePlaceBaseCompletion (K := ℚ) v] =
      ((Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ) v : Nat.Primes) : ℕ) := by
  let p : Nat.Primes :=
    Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ) v
  let : Fact p.1.Prime := ⟨p.2⟩
  let eIntegers :
      𝒪[ChosenFinitePlaceBaseCompletion (K := ℚ) v] ≃+*
        v.adicCompletionIntegers ℚ :=
    finitePlaceCompletionIntegerRingEquiv v
  let ePadicIntegers :
      v.adicCompletionIntegers ℚ ≃+* ℤ_[p.1] :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  let eResidue :
      𝓀[ChosenFinitePlaceBaseCompletion (K := ℚ) v] ≃+*
        ZMod p.1 :=
    (IsLocalRing.ResidueField.mapEquiv
      (eIntegers.trans ePadicIntegers)).trans
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntResidueFieldEquivZMod
          p.1)
  change Nat.card
      𝓀[ChosenFinitePlaceBaseCompletion (K := ℚ) v] = p.1
  calc
    Nat.card
          𝓀[ChosenFinitePlaceBaseCompletion (K := ℚ) v] =
        Nat.card (ZMod p.1) :=
      Nat.card_congr eResidue.toEquiv
    _ = p.1 := Nat.card_zmod p.1
