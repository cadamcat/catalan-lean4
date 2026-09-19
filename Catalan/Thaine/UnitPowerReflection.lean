import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Group.Commute.Units

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma exists_unit_of_power_in_integrally_closed
    (D K : Type*) [CommRing D] [IsDomain D] [IsIntegrallyClosed D]
    [Field K] [Algebra D K] [IsFractionRing D K]
    (q : ℕ) (hq : 0 < q) (b : K) (u : Dˣ)
    (hpower : algebraMap D K (u : D) = b ^ q) :
    ∃ v : Dˣ, algebraMap D K (v : D) = b := by
  have hbpow : IsIntegral D (b ^ q) :=
    IsIntegrallyClosed.isIntegral_iff.mpr ⟨(u : D), hpower⟩
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hq hbpow
  have hpowMap : algebraMap D K (v ^ q) = algebraMap D K (u : D) := by
    calc
      algebraMap D K (v ^ q) = (algebraMap D K v) ^ q := map_pow _ _ _
      _ = b ^ q := by rw [hv]
      _ = algebraMap D K (u : D) := hpower.symm
  have hpowD : v ^ q = (u : D) := IsFractionRing.injective D K hpowMap
  have hvpow : IsUnit (v ^ q) := by
    rw [hpowD]
    exact u.isUnit
  have hvunit : IsUnit v := (isUnit_pow_iff (Nat.ne_of_gt hq)).mp hvpow
  refine ⟨hvunit.unit, ?_⟩
  rw [hvunit.unit_spec]
  exact hv

end Catalan.Thaine
