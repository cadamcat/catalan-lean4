module

public import Catalan.Density.CyclicPrimeClasses
public import Catalan.Density.UnitResidueInjective
public import Catalan.Density.ResidueMap
public import Catalan.Density.ResidueKernel
public import Catalan.Density.QPrimeCongruence

/-!
# `Catalan.Density.SeparatingPrimeClasses`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]

def separatingPrimeClasses (S : Finset ℕ) :
    Set (UnitQuotient.PowerQuotient (ClassGroup (𝓞 (F p))) q) :=
  {c | ∃ (ell : ℕ) (v : HeightOneSpectrum (𝓞 (F p))) (red : 𝓞 (F p) →+* ZMod ell),
    ell.Prime ∧ ell ∉ S ∧ ell ≠ p ∧ ell ≠ q ∧ q ∣ ell - 1 ∧
    Nat.card (𝓞 (F p) ⧸ v.asIdeal) = ell ∧ Function.Surjective red ∧
    RingHom.ker red = v.asIdeal ∧
    (∀ u : (𝓞 (F p))ˣ,
      (∀ g : G p (F p), ∃ w : (ZMod ell)ˣ,
        w ^ q = Units.map red.toMonoidHom (Circular.unitAction p (F p) g u)) →
      ∃ w : (𝓞 (F p))ˣ, w ^ q = u) ∧
    c = UnitQuotient.powerClass q (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))}

lemma separatingPrimeClasses_span
    (hp7 : 7 ≤ p) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2) (S : Finset ℕ) :
    Submodule.span (ZMod q) (separatingPrimeClasses p q S) = ⊤ := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hq : Odd q := (Fact.out : q.Prime).odd_of_ne_two hq2
  obtain ⟨gamma, tau, _, _, hcyc, hspan⟩ :=
    exists_cyclic_prime_class_generators p q hp7 hq2 hdegree hq S
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  intro c hc
  obtain ⟨sigmaB, rho, ell, P, a, v, _, hM, hell, havoid, hellp, hellq,
    ha0, haq, hfrob, hv, hnorm, _, hc⟩ := hc
  obtain ⟨red, hsurj, hker⟩ := exists_residueHom_to_zmod (𝓞 (F p)) v.asIdeal ell hell hnorm
  have hfrob' : IsArithmeticFrob ell P ((sigmaB ^ a).restrictScalars ℚ) := by
    have heq : (sigmaB ^ a).restrictScalars ℚ = (sigmaB.restrictScalars ℚ) ^ a :=
      (AlgEquiv.restrictScalarsHom ℚ).map_pow sigmaB a
    rw [heq]
    exact hfrob
  have hqdiv : q ∣ ell - 1 := q_dvd_ell_sub_one_of_B_frobenius p q hq ell hell
    hellq.symm P (sigmaB ^ a) hfrob'
  refine ⟨ell, v, red, hell, havoid, hellp, hellq, hqdiv, hnorm, hsurj, hker, ?_, hc⟩
  intro u hu
  apply unit_qth_power_of_cyclic_prime_residues p q hp hq gamma tau hcyc sigmaB rho hM
    ell hell hellq.symm P a ha0 haq hfrob u
  intro g
  have hg := (Kummer.residue_power_iff_of_surjective (𝓞 (F p)) (ZMod ell) red hsurj
    v.asIdeal hker q (Circular.unitAction p (F p) g u)).mpr (hu g)
  rw [← hv]
  exact hg

end Catalan.A3
