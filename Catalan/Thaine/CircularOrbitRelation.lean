module

public import Catalan.Thaine.CircularClassRelation
public import Catalan.Thaine.PrimeOrbit
public import Catalan.Thaine.ClassRepresentation
public import Catalan.Thaine.OrbitReindex

/-!
# `Catalan.Thaine.CircularOrbitRelation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators
noncomputable section
namespace Catalan.Thaine

lemma exists_circular_orbit_relation
    (p q ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (hql : q ∣ ell - 1)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]))
    (v0 : HeightOneSpectrum (𝓞 (A3.F p)))
    (hcard : Nat.card (𝓞 (A3.F p) ⧸ v0.asIdeal) = ell)
    (red : 𝓞 (A3.F p) →+* ZMod ell) (hsurj : Function.Surjective red)
    (hker : RingHom.ker red = v0.asIdeal)
    (d : (𝓞 (A3.F p))ˣ) (hd : d ∈ realCircularUnits p)
    (s : (ZMod ell)ˣ) (hs : ∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers s) :
    ∃ r : (A3.F p ≃ₐ[ℚ] A3.F p) → ℕ,
      ((∑ᶠ g : A3.F p ≃ₐ[ℚ] A3.F p,
        r g • classRepresentation (A3.F p) q g
          (UnitQuotient.powerClass q (ClassGroup.mk (A3.F p) (FractionalIdealGroup.prime v0)))) = 0) ∧
      ∀ g : A3.F p ≃ₐ[ℚ] A3.F p,
        red (A3.integralAut g⁻¹ ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p))) =
          (s : ZMod ell) ^ r g := by
  classical
  let circularOrbitGalFintype : Fintype (A3.F p ≃ₐ[ℚ] A3.F p) := Fintype.ofFinite _
  obtain ⟨m, _, hoff, hsum, hres⟩ := exists_circular_class_relation p q ell hp2 hpe hql hell d hd s hs
  obtain ⟨e, he⟩ := exists_real_prime_orbit_equiv p ell hpe v0 hcard
  let r : (A3.F p ≃ₐ[ℚ] A3.F p) → ℕ := fun g => m (e g).val
  refine ⟨r, ?_, ?_⟩
  · have hindex := finsum_reindex_subtype_equiv
      (HeightOneSpectrum (𝓞 (A3.F p))) (A3.F p ≃ₐ[ℚ] A3.F p)
      (UnitQuotient.PowerQuotient (ClassGroup (𝓞 (A3.F p))) q)
      (fun v => (ell : 𝓞 (A3.F p)) ∈ v.asIdeal) e
      (fun v => m v • UnitQuotient.powerClass q
        (ClassGroup.mk (A3.F p) (FractionalIdealGroup.prime v)))
      (by intro v hv; rw [hoff v hv, zero_nsmul])
    rw [finsum_eq_sum_of_fintype]
    have hterms : (∑ g : A3.F p ≃ₐ[ℚ] A3.F p,
        r g • classRepresentation (A3.F p) q g
          (UnitQuotient.powerClass q (ClassGroup.mk (A3.F p) (FractionalIdealGroup.prime v0)))) =
        ∑ g : A3.F p ≃ₐ[ℚ] A3.F p, m (e g).val • UnitQuotient.powerClass q
          (ClassGroup.mk (A3.F p) (FractionalIdealGroup.prime (e g).val)) := by
      apply Finset.sum_congr rfl
      intro g _
      simp only [r, classRepresentation_prime, he g]
    exact hterms.trans (hindex.symm.trans hsum)
  · intro g
    let v := (e g).val
    let redg : 𝓞 (A3.F p) →+* ZMod ell := red.comp (A3.integralAut g⁻¹).toRingHom
    obtain ⟨hsurjg, hkerg⟩ := residue_map_conjugate (A3.F p) (ZMod ell) v0 g red hsurj hker
    have hkernel : RingHom.ker redg = v.asIdeal := by
      change RingHom.ker redg = (e g).val.asIdeal
      rw [he g]
      exact hkerg
    obtain ⟨J, hJmax, hJover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 (A3.Bsub p ell)) v.asIdeal
    have circularOrbitUpperMax : J.IsMaximal := hJmax
    have circularOrbitUpperOver : J.LiesOver v.asIdeal := hJover
    let P : HeightOneSpectrum (𝓞 (A3.Bsub p ell)) :=
      ⟨J, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot J⟩
    have h := hres v P hJover (e g).property redg hsurjg hkernel
    exact h

end Catalan.Thaine
