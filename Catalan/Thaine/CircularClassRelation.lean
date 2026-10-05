module

public import Catalan.Thaine.PrincipalClassRelation
public import Catalan.Thaine.AuxiliaryNormMultiplicities
public import Catalan.Thaine.CircularPrincipalData

/-!
# `Catalan.Thaine.CircularClassRelation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators
noncomputable section
namespace Catalan.Thaine

lemma exists_circular_class_relation
    (p q ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (hql : q ∣ ell - 1)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]))
    (d : (𝓞 (A3.F p))ˣ) (hd : d ∈ realCircularUnits p)
    (s : (ZMod ell)ˣ) (hs : ∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers s) :
    ∃ m : HeightOneSpectrum (𝓞 (A3.F p)) → ℕ,
      Function.HasFiniteSupport m ∧
      (∀ v, (ell : 𝓞 (A3.F p)) ∉ v.asIdeal → m v = 0) ∧
      ((∑ᶠ v : HeightOneSpectrum (𝓞 (A3.F p)),
        m v • UnitQuotient.powerClass q
          (ClassGroup.mk (A3.F p) (FractionalIdealGroup.prime v))) = 0) ∧
      ∀ (v : HeightOneSpectrum (𝓞 (A3.F p)))
        (P : HeightOneSpectrum (𝓞 (A3.Bsub p ell))),
        P.asIdeal.LiesOver v.asIdeal → (ell : 𝓞 (A3.F p)) ∈ v.asIdeal →
        ∀ red : 𝓞 (A3.F p) →+* ZMod ell, Function.Surjective red → RingHom.ker red = v.asIdeal →
          red ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p)) = (s : ZMod ell) ^ m v := by
  classical
  obtain ⟨alpha, halpha, hIinv, hres⟩ :=
    exists_circular_invariant_principal_data p ell hp2 hpe hell d hd s hs
  let I : Ideal (𝓞 (A3.Bsub p ell)) := Ideal.span {alpha}
  have hI : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr halpha
  let J : Ideal (𝓞 (A3.F p)) := Ideal.relNorm (𝓞 (A3.F p)) I
  have hJ : J ≠ ⊥ := Ideal.relNorm_eq_bot_iff.not.mpr hI
  have hJprincipal : J.IsPrincipal := by
    change (Ideal.relNorm (𝓞 (A3.F p)) (Ideal.span {alpha})).IsPrincipal
    rw [Ideal.relNorm_singleton]
    exact ⟨⟨_, rfl⟩⟩
  let m : HeightOneSpectrum (𝓞 (A3.F p)) → ℕ :=
    fun v => if (ell : 𝓞 (A3.F p)) ∈ v.asIdeal then multiplicity v.asIdeal J else 0
  have hmfinite : Function.HasFiniteSupport m := by
    apply (multiplicity_hasFiniteSupport (𝓞 (A3.F p)) J hJ).subset
    intro v hv
    by_cases hellv : (ell : 𝓞 (A3.F p)) ∈ v.asIdeal
    · simpa only [Function.mem_support, m, if_pos hellv] using hv
    · simp only [Function.mem_support, m, if_neg hellv, ne_self_iff_false] at hv
  refine ⟨m, hmfinite, ?_, ?_, ?_⟩
  · intro v haway
    simp only [m, if_neg haway]
  · rw [← principal_class_finsum_eq_zero (A3.F p) q J hJ hJprincipal]
    apply finsum_congr
    intro v
    by_cases hellv : (ell : 𝓞 (A3.F p)) ∈ v.asIdeal
    · simp only [m, if_pos hellv]
    · have hdiv : q ∣ multiplicity v.asIdeal J :=
        hql.trans (auxiliary_norm_multiplicity_dvd_away p ell hpe I hI hIinv v hellv)
      obtain ⟨k, hk⟩ := hdiv
      simp only [m, if_neg hellv, zero_nsmul]
      rw [hk, mul_comm q k, mul_smul, UnitQuotient.powerQuotient_exponent q, nsmul_zero]
  · intro v P hOver hellv red hsurj hker
    have circularNormPrimeOver : P.asIdeal.LiesOver v.asIdeal := hOver
    have hmult : multiplicity v.asIdeal J = multiplicity P.asIdeal I :=
      auxiliary_norm_multiplicity_at p ell hpe I hI v P hellv
    simpa only [m, if_pos hellv, hmult] using hres v P hOver hellv red hsurj hker

end Catalan.Thaine
