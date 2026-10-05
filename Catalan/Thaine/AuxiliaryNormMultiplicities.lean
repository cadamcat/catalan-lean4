module

public import Catalan.Thaine.NormFibers
public import Catalan.Thaine.AuxiliaryRamification

/-!
# `Catalan.Thaine.AuxiliaryNormMultiplicities`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma auxiliary_norm_multiplicity_dvd_away
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (I : Ideal (𝓞 (A3.Bsub p ell))) (hI : I ≠ ⊥)
    (hIinv : ∀ sigma : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell,
      Ideal.map (A3.integralAut sigma).toRingHom I = I)
    (v : HeightOneSpectrum (𝓞 (A3.F p)))
    (haway : (ell : 𝓞 (A3.F p)) ∉ v.asIdeal) :
    ell - 1 ∣ multiplicity v.asIdeal (Ideal.relNorm (𝓞 (A3.F p)) I) := by
  have auxiliaryNormAwayGalois : IsGalois (A3.F p) (A3.Bsub p ell) :=
    A3.isGalois_Bsub p ell (Fact.out : ell.Prime).pos
  obtain ⟨J, hJmax, hJover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (A3.Bsub p ell)) v.asIdeal
  have auxiliaryNormAwayMax : J.IsMaximal := hJmax
  have auxiliaryNormAwayOver : J.LiesOver v.asIdeal := hJover
  let P : HeightOneSpectrum (𝓞 (A3.Bsub p ell)) :=
    ⟨J, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot J⟩
  have auxiliaryNormAwayHeightOver : P.asIdeal.LiesOver v.asIdeal := hJover
  have hram (Q : v.asIdeal.primesOver (𝓞 (A3.Bsub p ell))) :
      Q.1.ramificationIdx (𝓞 (A3.F p)) = 1 := by
    let Qh : HeightOneSpectrum (𝓞 (A3.Bsub p ell)) :=
      ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.2⟩
    have hawayQ : (ell : 𝓞 (A3.Bsub p ell)) ∉ Qh.asIdeal := by
      intro h
      apply haway
      apply (Ideal.mem_of_liesOver Q.1 v.asIdeal _).mpr
      simpa only [map_natCast] using h
    have auxiliaryNormAwayUnramified : Algebra.IsUnramifiedAt (𝓞 (A3.F p)) Q.1 :=
      auxiliary_unramified_away p ell Qh hawayQ
    exact Ideal.ramificationIdx_eq_one (R := 𝓞 (A3.F p)) (q := Q.1)
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := (ZMod ell)ˣ)
  have hdegree := (auxiliary_cyclic_generator p ell hpe s hs).1
  have hmult := multiplicity_relNorm_eq_degree_mul_of_unramified
    (A3.F p) (A3.Bsub p ell) I hI hIinv v P hram
  rw [hdegree] at hmult
  exact ⟨multiplicity P.asIdeal I, hmult⟩

lemma auxiliary_norm_multiplicity_at
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (I : Ideal (𝓞 (A3.Bsub p ell))) (hI : I ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 (A3.F p)))
    (P : HeightOneSpectrum (𝓞 (A3.Bsub p ell))) [P.asIdeal.LiesOver v.asIdeal]
    (hellv : (ell : 𝓞 (A3.F p)) ∈ v.asIdeal) :
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 (A3.F p)) I) = multiplicity P.asIdeal I := by
  obtain ⟨hf, _, huniq, _⟩ := auxiliary_prime_fiber p ell hpe v P hellv
  exact multiplicity_relNorm_eq_of_unique_inertia_one
    (A3.F p) (A3.Bsub p ell) I hI v P hf huniq

end Catalan.Thaine
