import Catalan.Thaine.CircularOrbitRelation
import Catalan.Thaine.ResidueCoordinateSquare

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators
noncomputable section
namespace Catalan.Thaine

local instance circularCoordinateGalFintype (p : ℕ) : Fintype (G p (A3.F p)) :=
  Fintype.ofFinite _

lemma circular_coordinates_annihilate_prime
    (p q ell : ℕ) [Fact p.Prime] [Fact q.Prime] [Fact ell.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpe : p ≠ ell) (hql : q ∣ ell - 1)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]))
    (v0 : HeightOneSpectrum (𝓞 (A3.F p)))
    (hcard : Nat.card (𝓞 (A3.F p) ⧸ v0.asIdeal) = ell)
    (red : 𝓞 (A3.F p) →+* ZMod ell) (hsurj : Function.Surjective red)
    (hker : RingHom.ker red = v0.asIdeal)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (s : (ZMod ell)ˣ) (hs : ∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers s)
    (hse : e (UnitQuotient.powerClass q s) = 1)
    (d : (𝓞 (A3.F p))ˣ) (hd : d ∈ realCircularUnits p) :
    (classRepresentation (A3.F p) q).asAlgebraHom
      (groupAlgebraOfFunction (ZMod q) (G p (A3.F p))
        (A3.unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q d)))
      (UnitQuotient.powerClass q (ClassGroup.mk (A3.F p) (FractionalIdealGroup.prime v0))) = 0 := by
  obtain ⟨r, hsum, hres⟩ :=
    exists_circular_orbit_relation p q ell hp2 hpe hql hell v0 hcard red hsurj hker d hd s hs
  let c := UnitQuotient.powerClass q
    (ClassGroup.mk (A3.F p) (FractionalIdealGroup.prime v0))
  let f := A3.unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q d)
  have hcoeff (g : G p (A3.F p)) : (2 : ZMod q) * f g = (r g : ZMod q) :=
    twice_unitResidueCoordinate_of_residue_power p q ell red e s hse d g (r g) (hres g)
  have htwosum : (2 : ZMod q) •
      (∑ g : G p (A3.F p), f g • classRepresentation (A3.F p) q g c) = 0 := by
    calc
      _ = ∑ g : G p (A3.F p), ((2 : ZMod q) * f g) • classRepresentation (A3.F p) q g c := by
        rw [Finset.smul_sum]
        simp only [smul_smul]
      _ = ∑ g : G p (A3.F p), (r g : ZMod q) • classRepresentation (A3.F p) q g c := by
        simp_rw [hcoeff]
      _ = ∑ g : G p (A3.F p), r g • classRepresentation (A3.F p) q g c := by
        simp only [Nat.cast_smul_eq_nsmul]
      _ = 0 := by
        rw [← finsum_eq_sum_of_fintype]
        exact hsum
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact (Fact.out : q.Prime).ne_one h1
    · exact hq2 h2
  have hsumzero := (smul_eq_zero.mp htwosum).resolve_left htwo
  simpa only [groupAlgebraOfFunction_action] using hsumzero

end Catalan.Thaine
