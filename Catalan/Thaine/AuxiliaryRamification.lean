module

public import Catalan.Thaine.RealUnramified
public import Catalan.Thaine.PrimeUniformizer
public import Catalan.Thaine.CyclotomicAway
public import Catalan.Thaine.TotalRamification
public import Catalan.Thaine.TotalInertia
public import Catalan.Thaine.AuxiliaryUniformizer

/-!
# `Catalan.Thaine.AuxiliaryRamification`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma auxiliary_unramified_away
    (p ell : ℕ) [Fact ell.Prime]
    (P : HeightOneSpectrum (𝓞 (A3.Bsub p ell)))
    (haway : (ell : 𝓞 (A3.Bsub p ell)) ∉ P.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 (A3.F p)) P.asIdeal := by
  have actualAwayCyclotomic : IsCyclotomicExtension {ell} (A3.F p) (A3.Bsub p ell) :=
    A3.isCyclotomicExtension_Bsub p ell (Fact.out : ell.Prime).pos
  exact cyclotomic_isUnramifiedAt_away (A3.F p) (A3.Bsub p ell) ell P haway

lemma auxiliary_prime_ramification
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (v : HeightOneSpectrum (𝓞 (A3.F p)))
    (P : HeightOneSpectrum (𝓞 (A3.Bsub p ell))) [P.asIdeal.LiesOver v.asIdeal]
    (hellv : (ell : 𝓞 (A3.F p)) ∈ v.asIdeal) :
    P.asIdeal.ramificationIdx (𝓞 (A3.F p)) = ell - 1 ∧
      emultiplicity P.asIdeal (Ideal.span {auxiliaryUniformizer p ell}) = 1 := by
  have actualRamificationGalois : IsGalois (A3.F p) (A3.Bsub p ell) :=
    A3.isGalois_Bsub p ell (Fact.out : ell.Prime).pos
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := (ZMod ell)ˣ)
  have hdegree := (auxiliary_cyclic_generator p ell hpe s hs).1
  have hw : IsPrimitiveRoot (auxiliaryRoot p ell) ell := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos
  simpa only [auxiliaryUniformizer, auxiliaryIntegerRoot] using
    prime_root_ramification_uniformizer (A3.F p) (A3.Bsub p ell) ell hdegree v P hellv
      (real_prime_ramification_one p ell hpe v hellv) (auxiliaryRoot p ell) hw

lemma auxiliary_prime_fiber
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (v : HeightOneSpectrum (𝓞 (A3.F p)))
    (P : HeightOneSpectrum (𝓞 (A3.Bsub p ell))) [P.asIdeal.LiesOver v.asIdeal]
    (hellv : (ell : 𝓞 (A3.F p)) ∈ v.asIdeal) :
    P.asIdeal.inertiaDeg (𝓞 (A3.F p)) = 1 ∧
      (Nat.card (𝓞 (A3.Bsub p ell) ⧸ P.asIdeal) = Nat.card (𝓞 (A3.F p) ⧸ v.asIdeal)) ∧
      (∀ Q : HeightOneSpectrum (𝓞 (A3.Bsub p ell)), Q.asIdeal.LiesOver v.asIdeal → Q = P) ∧
      ∀ sigma : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell,
        A3.PreservesPrime sigma P.asIdeal ∧
          ∀ x : 𝓞 (A3.Bsub p ell), A3.integralAut sigma x - x ∈ P.asIdeal := by
  have actualFiberGalois : IsGalois (A3.F p) (A3.Bsub p ell) :=
    A3.isGalois_Bsub p ell (Fact.out : ell.Prime).pos
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := (ZMod ell)ˣ)
  have hdegree := (auxiliary_cyclic_generator p ell hpe s hs).1
  have he := (auxiliary_prime_ramification p ell hpe v P hellv).1
  have hedegree : P.asIdeal.ramificationIdx (𝓞 (A3.F p)) =
      Module.finrank (A3.F p) (A3.Bsub p ell) := he.trans hdegree.symm
  obtain ⟨hf, huniq⟩ := inertia_and_unique_prime_of_ramification_degree
    (A3.F p) (A3.Bsub p ell) v P hedegree
  exact ⟨hf, residue_card_eq_of_inertia_one (A3.F p) (A3.Bsub p ell) v P hf, huniq,
    all_integral_automorphisms_trivial_mod_prime (A3.F p) (A3.Bsub p ell) P hedegree⟩

lemma exists_auxiliary_prime_of_norm_eq
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (v : HeightOneSpectrum (𝓞 (A3.F p)))
    (hcard : Nat.card (𝓞 (A3.F p) ⧸ v.asIdeal) = ell) :
    ∃ P : HeightOneSpectrum (𝓞 (A3.Bsub p ell)), P.asIdeal.LiesOver v.asIdeal ∧
      P.asIdeal.ramificationIdx (𝓞 (A3.F p)) = ell - 1 ∧
      P.asIdeal.inertiaDeg (𝓞 (A3.F p)) = 1 ∧
      Nat.card (𝓞 (A3.Bsub p ell) ⧸ P.asIdeal) = ell ∧
      emultiplicity P.asIdeal (Ideal.span {auxiliaryUniformizer p ell}) = 1 ∧
      ∀ Q : HeightOneSpectrum (𝓞 (A3.Bsub p ell)), Q.asIdeal.LiesOver v.asIdeal → Q = P := by
  have hell : ell.Prime := Fact.out
  have hellv : (ell : 𝓞 (A3.F p)) ∈ v.asIdeal := by
    have h := v.asIdeal.absNorm_mem
    change (Nat.card (𝓞 (A3.F p) ⧸ v.asIdeal) : 𝓞 (A3.F p)) ∈ v.asIdeal at h
    rwa [hcard] at h
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (A3.Bsub p ell)) v.asIdeal
  have actualChosenPrimeMax : Q.IsMaximal := hQ
  have actualChosenPrimeOver : Q.LiesOver v.asIdeal := hQv
  have hellQ : (ell : 𝓞 (A3.Bsub p ell)) ∈ Q := by
    simpa only [map_natCast] using (Ideal.mem_of_liesOver Q v.asIdeal _).mp hellv
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at hellQ
    exact (Nat.cast_ne_zero.mpr hell.ne_zero) hellQ
  let P : HeightOneSpectrum (𝓞 (A3.Bsub p ell)) := ⟨Q, inferInstance, hQne⟩
  have actualChosenHeightOver : P.asIdeal.LiesOver v.asIdeal := hQv
  obtain ⟨he, hpi⟩ := auxiliary_prime_ramification p ell hpe v P hellv
  obtain ⟨hf, hc, huniq, _⟩ := auxiliary_prime_fiber p ell hpe v P hellv
  exact ⟨P, hQv, he, hf, hc.trans hcard, hpi, huniq⟩

end Catalan.Thaine
