import Catalan.Density.UnitResidueCoordinates
import Catalan.Density.RealPrimeCongruence

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
local instance augmentationPrimesGalFintype : Fintype (G p (F p)) := Fintype.ofFinite _

def augmentationPrimeClasses (S : Finset ℕ) :
    Set (UnitQuotient.PowerQuotient (ClassGroup (𝓞 (F p))) q) :=
  {c | ∃ (ell : ℕ) (v : HeightOneSpectrum (𝓞 (F p))) (red : 𝓞 (F p) →+* ZMod ell)
      (s : (ZMod ell)ˣ)
      (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
      (u : (𝓞 (F p))ˣ),
    ell.Prime ∧ ell ∉ S ∧ ell ≠ p ∧ ell ≠ q ∧ q ∣ ell - 1 ∧
    ((ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p])) ∧
    Nat.card (𝓞 (F p) ⧸ v.asIdeal) = ell ∧ Function.Surjective red ∧
    RingHom.ker red = v.asIdeal ∧
    (∀ w : (𝓞 (F p))ˣ,
      (∀ g : G p (F p), ∃ x : (ZMod ell)ˣ,
        x ^ q = Units.map red.toMonoidHom (Circular.unitAction p (F p) g w)) →
      ∃ x : (𝓞 (F p))ˣ, x ^ q = w) ∧
    (∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers s) ∧ e (UnitQuotient.powerClass q s) = 1 ∧
    LinearMap.range (unitResidueCoordinates p q ell red e) =
      Residue.sumZero (ZMod q) (G p (F p)) ∧
    (∀ g : G p (F p),
      unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q u) g =
        (1 : MonoidAlgebra (ZMod q) (G p (F p))).coeff g -
          (Fintype.card (G p (F p)) : ZMod q)⁻¹) ∧
    c = UnitQuotient.powerClass q (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))}

lemma augmentationPrimeClasses_span
    (hp7 : 7 ≤ p) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2) (S : Finset ℕ) :
    Submodule.span (ZMod q) (augmentationPrimeClasses p q S) = ⊤ := by
  have hp2 : p ≠ 2 := by omega
  apply top_unique
  rw [← separatingPrimeClasses_span p q hp7 hq2 hdegree S]
  apply Submodule.span_mono
  intro c hc
  obtain ⟨ell, v, red, hell, havoid, hellp, hellq, hdiv, hnorm, hsurj, hker, hsep, hc⟩ := hc
  have instPrimeEll : Fact ell.Prime := ⟨hell⟩
  obtain ⟨s, hs, e, he⟩ := exists_residue_power_coordinate q ell hdiv
  have hmodp := real_prime_congruence p ell (Fact.out : p.Prime) hell hellp.symm v hnorm
  obtain ⟨u, hu⟩ := exists_unit_augmentation_coordinates p q hp2 hq2 hdegree ell red e hsep
  exact ⟨ell, v, red, s, e, u, hell, havoid, hellp, hellq, hdiv, hmodp, hnorm,
    hsurj, hker, hsep, hs, he, unitResidueCoordinates_range p q hp2 hq2 ell red e hsep,
    hu, hc⟩

end Catalan.A3
