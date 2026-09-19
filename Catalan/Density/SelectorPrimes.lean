import Catalan.Density.HPrimeFrobenius
import Catalan.Density.DensityTheorem

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3

private lemma zpowers_pow_eq_of_prime_exponent {G : Type*} [Group G]
    (q : ℕ) (hq : q.Prime) (g : G) (hg : g ^ q = 1)
    (a : ℕ) (ha0 : 0 < a) (haq : a < q) :
    Subgroup.zpowers (g ^ a) = Subgroup.zpowers g := by
  have hcop : a.Coprime q :=
    (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha0 haq)).symm
  have hord : a.Coprime (orderOf g) := Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hg) hcop
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) a)
  · exact Subgroup.zpowers_le.mpr (mem_zpowers_pow_iff.mpr hord)

lemma exists_prime_class_of_selector_avoiding
    (p q : ℕ) [Fact q.Prime] (hp : 0 < p) (hq : Odd q)
    (sigmaB : T p q ≃ₐ[Bsub p q] T p q)
    (hselector : Selector p q (sigmaB.restrictScalars ℚ)) (S : Finset ℕ) :
    ∃ ell : ℕ, ell.Prime ∧ ell ∉ S ∧
      ∃ (P : Ideal (𝓞 (T p q))) (a : ℕ) (v : HeightOneSpectrum (𝓞 (F p))),
        0 < a ∧ a < q ∧ IsArithmeticFrob ell P ((sigmaB.restrictScalars ℚ) ^ a) ∧
        v.asIdeal = P.under (𝓞 (F p)) ∧ Nat.card (𝓞 (F p) ⧸ v.asIdeal) = ell ∧
        Subgroup.zpowers
          (classGroupToHGal p q hq (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))) =
            Subgroup.zpowers (restrictTToH p q sigmaB) := by
  have instNumberFieldT : NumberField (T p q) := numberField_T p q hq
  have instGaloisT : IsGalois ℚ (T p q) := isGalois_T_rat p q hp hq.pos
  obtain ⟨ell, hell, havoid, P, a, ha0, haq, hfrob⟩ :=
    exists_arithmeticFrob_nonzero_power (T p q) q (Fact.out : q.Prime)
      (sigmaB.restrictScalars ℚ) hselector.ne_one hselector.pow_eq_one
      hselector.centralizer_exponent S
  have hfrob' : IsArithmeticFrob ell P ((sigmaB ^ a).restrictScalars ℚ) := by
    have heq : (sigmaB ^ a).restrictScalars ℚ = (sigmaB.restrictScalars ℚ) ^ a :=
      (AlgEquiv.restrictScalarsHom ℚ).map_pow sigmaB a
    rw [heq]
    exact hfrob
  obtain ⟨v, hv, hnorm, hcycle⟩ :=
    exists_H_prime_class_of_rationalFrob p q hq (sigmaB ^ a) ell hell P hfrob'
  refine ⟨ell, hell, havoid, P, a, v, ha0, haq, hfrob, hv, hnorm, ?_⟩
  rw [hcycle, map_pow]
  exact zpowers_pow_eq_of_prime_exponent q (Fact.out : q.Prime)
    (restrictTToH p q sigmaB) (Hsub_gal_pow_eq_one p q _) a ha0 haq

end Catalan.A3
