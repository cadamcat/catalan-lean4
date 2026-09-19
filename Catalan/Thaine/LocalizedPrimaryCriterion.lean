import Catalan.Thaine.UnitPowerReflection
import Catalan.CaseOne.PrimaryUnits

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma primary_of_localized_unit_power
    (A D K : Type*) [CommRing A] [CommRing D] [IsDomain D] [IsIntegrallyClosed D]
    [Field K] [Algebra A D] [Algebra D K] [Algebra A K] [IsScalarTower A D K]
    [IsFractionRing D K] (q : ℕ) (hq : 0 < q)
    (red : D →+* UnitQuotient.ModSquare A q)
    (hred : ∀ a : A, red (algebraMap A D a) =
      Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) a)
    (v : Dˣ) (c : Aˣ) (b : Kˣ)
    (hv : Units.map (algebraMap D K).toMonoidHom v =
      Units.map (algebraMap A K).toMonoidHom c * b ^ q)
    (hvred : Units.map red.toMonoidHom v = 1) :
    c ∈ UnitQuotient.primaryUnits A q := by
  let j : Aˣ →* Dˣ := Units.map (algebraMap A D).toMonoidHom
  let f : Dˣ →* Kˣ := Units.map (algebraMap D K).toMonoidHom
  let r : Dˣ →* (UnitQuotient.ModSquare A q)ˣ := Units.map red.toMonoidHom
  have hcomp : f (j c) = Units.map (algebraMap A K).toMonoidHom c := by
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply A D K (c : A)).symm
  have hd : f ((j c)⁻¹ * v) = b ^ q := by
    rw [map_mul, map_inv, hcomp, hv, inv_mul_cancel_left]
  have hdval : algebraMap D K ((j c)⁻¹ * v : Dˣ) = (b : K) ^ q := by
    exact congrArg (fun z : Kˣ => (z : K)) hd
  obtain ⟨w, hw⟩ := exists_unit_of_power_in_integrally_closed D K q hq (b : K)
    ((j c)⁻¹ * v) hdval
  have hwF : f w = b := by
    apply Units.ext
    exact hw
  have hlocal : v = j c * w ^ q := by
    apply Units.ext
    apply IsFractionRing.injective D K
    change (f v : K) = (f (j c * w ^ q) : K)
    rw [map_mul, map_pow, hcomp, hwF]
    exact congrArg (fun z : Kˣ => (z : K)) hv
  have hrbase : r (j c) = UnitQuotient.modSquareUnit A q c := by
    apply Units.ext
    exact hred (c : A)
  have hres : UnitQuotient.modSquareUnit A q c * (r w) ^ q = 1 := by
    rw [← hrbase, ← map_pow, ← map_mul, ← hlocal]
    exact hvred
  change ∃ z : (UnitQuotient.ModSquare A q)ˣ, z ^ q = UnitQuotient.modSquareUnit A q c
  refine ⟨(r w)⁻¹, ?_⟩
  rw [inv_pow]
  exact (eq_inv_iff_mul_eq_one.mpr hres).symm

end Catalan.Thaine
