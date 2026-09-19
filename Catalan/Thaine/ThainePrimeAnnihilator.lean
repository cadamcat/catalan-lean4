import Catalan.Thaine.RealUnitAnnihilator
import Catalan.Thaine.ClassNorm
import Catalan.Thaine.CoordinateElement
import Catalan.Thaine.CircularCoordinateAnnihilator

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma real_unit_annihilator_kills_prime
    (p q ell : ℕ) [Fact p.Prime] [Fact q.Prime] [Fact ell.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpe : p ≠ ell) (hql : q ∣ ell - 1)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]))
    (v : HeightOneSpectrum (𝓞 (A3.F p)))
    (hcard : Nat.card (𝓞 (A3.F p) ⧸ v.asIdeal) = ell)
    (red : 𝓞 (A3.F p) →+* ZMod ell) (hsurj : Function.Surjective red)
    (hker : RingHom.ker red = v.asIdeal)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (s : (ZMod ell)ˣ) (hs : ∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers s)
    (hse : e (UnitQuotient.powerClass q s) = 1)
    (u : (𝓞 (A3.F p))ˣ) (b : ZMod q)
    (hu : ∀ g : G p (A3.F p),
      A3.unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q u) g =
        (1 : MonoidAlgebra (ZMod q) (G p (A3.F p))).coeff g - b)
    (Theta : R p (A3.F p)) (hTheta : realUnitAnnihilator p q Theta) :
    (classRepresentation (A3.F p) q).asAlgebraHom (Runge.reduceFull p (A3.F p) q Theta)
      (UnitQuotient.powerClass q (ClassGroup.mk (A3.F p) (FractionalIdealGroup.prime v))) = 0 := by
  have realThainePrimeAbelian : IsAbelianGalois ℚ (A3.F p) :=
    A3.isAbelianGalois_F p (Fact.out : p.Prime).pos
  obtain ⟨d, hd, heq⟩ := (realUnitAnnihilator_iff_circular_powerClass p q Theta).mp hTheta u
  have hpoint := circular_coordinates_annihilate_prime p q ell hp2 hq2 hpe hql hell
    v hcard red hsurj hker e s hs hse d hd
  rw [heq, integralUnit_coordinate_element p q ell red e u b hu Theta] at hpoint
  rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    classRepresentation_groupNorm_eq_zero, smul_zero, sub_zero] at hpoint
  exact hpoint

end Catalan.Thaine
