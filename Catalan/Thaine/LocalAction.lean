module

public import Mathlib

/-!
# `Catalan.Thaine.LocalAction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma exists_localized_action_and_residue
    (R k : Type*) [CommRing R] [Field k] (P : Ideal R) [P.IsPrime]
    (tau : R ≃+* R) (hpres : ∀ x : R, tau x ∈ P ↔ x ∈ P)
    (red : R →+* k) (hker : RingHom.ker red = P)
    (hinertia : ∀ x : R, red (tau x) = red x) :
    ∃ (tauLoc : Localization.AtPrime P ≃+* Localization.AtPrime P)
      (redLoc : Localization.AtPrime P →+* k),
      (∀ x : R, tauLoc (algebraMap R (Localization.AtPrime P) x) =
        algebraMap R (Localization.AtPrime P) (tau x)) ∧
      (∀ x : R, redLoc (algebraMap R (Localization.AtPrime P) x) = red x) ∧
      ∀ y : Localization.AtPrime P, redLoc (tauLoc y) = redLoc y := by
  have hPP : P = P.comap tau.toRingHom := by
    ext x
    exact (hpres x).symm
  let tauLoc : Localization.AtPrime P ≃+* Localization.AtPrime P :=
    Localization.localRingEquiv P P tau hPP
  have hden : ∀ y : P.primeCompl, IsUnit (red y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    apply y.property
    exact hker.le (show (y : R) ∈ RingHom.ker red from hy)
  let redLoc : Localization.AtPrime P →+* k :=
    IsLocalization.lift (S := Localization.AtPrime P) hden
  have htau (x : R) : tauLoc (algebraMap R (Localization.AtPrime P) x) =
      algebraMap R (Localization.AtPrime P) (tau x) :=
    Localization.localRingHom_to_map P P tau.toRingHom hPP x
  have hred (x : R) : redLoc (algebraMap R (Localization.AtPrime P) x) = red x :=
    IsLocalization.lift_eq hden x
  have hcomp : redLoc.comp tauLoc.toRingHom = redLoc := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext x
    change redLoc (tauLoc (algebraMap R (Localization.AtPrime P) x)) =
      redLoc (algebraMap R (Localization.AtPrime P) x)
    rw [htau, hred, hred, hinertia]
  refine ⟨tauLoc, redLoc, htau, hred, ?_⟩
  intro y
  exact RingHom.congr_fun hcomp y

end Catalan.Thaine
