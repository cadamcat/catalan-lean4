module

public import Mathlib

/-!
# `Catalan.Thaine.LocalExponent`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma residue_coboundary_of_uniformizer_decomposition
    (R K k : Type*) [CommRing R] [IsDomain R] [Field K] [Field k]
    [Algebra R K] [IsFractionRing R K]
    (tau : R ≃+* R) (sigma : K ≃+* K)
    (hcompat : ∀ x : R, sigma (algebraMap R K x) = algebraMap R K (tau x))
    (red : R →+* k) (hinertia : ∀ x : R, red (tau x) = red x)
    (pi : R) (hpi : pi ≠ 0) (t u eta : Rˣ)
    (hpi_action : tau pi = (t : R) * pi) (alpha : K) (n : ℤ)
    (halpha : alpha = algebraMap R K (u : R) * (algebraMap R K pi) ^ n)
    (heta : sigma alpha = algebraMap R K (eta : R) * alpha) :
    red (eta : R) = (red (t : R)) ^ n := by
  have hpiK : algebraMap R K pi ≠ 0 := by
    intro h
    apply hpi
    apply IsFractionRing.injective R K
    simpa only [map_zero] using h
  have hfield : algebraMap R K (tau (u : R)) * (algebraMap R K (t : R)) ^ n =
      algebraMap R K (eta : R) * algebraMap R K (u : R) := by
    apply mul_right_cancel₀ (zpow_ne_zero n hpiK)
    have h := heta
    simp only [halpha, map_mul, map_zpow₀, hcompat, hpi_action, mul_zpow] at h
    simpa only [mul_assoc] using h
  have htK : algebraMap R K ((t ^ n : Rˣ) : R) = (algebraMap R K (t : R)) ^ n :=
    ((algebraMap R K).toMonoidHom.comp (Units.coeHom R)).map_zpow t n
  have hR : tau (u : R) * ((t ^ n : Rˣ) : R) = (eta : R) * (u : R) := by
    apply IsFractionRing.injective R K
    simpa only [map_mul, htK] using hfield
  have htred : red ((t ^ n : Rˣ) : R) = (red (t : R)) ^ n :=
    (red.toMonoidHom.comp (Units.coeHom R)).map_zpow t n
  have hred : red (u : R) * (red (t : R)) ^ n = red (eta : R) * red (u : R) := by
    simpa only [map_mul, hinertia, htred] using congrArg red hR
  have hune : red (u : R) ≠ 0 := (Units.map red.toMonoidHom u).ne_zero
  apply mul_right_cancel₀ hune
  exact hred.symm.trans (mul_comm _ _)

end Catalan.Thaine
