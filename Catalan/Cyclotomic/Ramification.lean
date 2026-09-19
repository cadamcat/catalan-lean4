import Catalan.Cyclotomic.Elements

/-! The prime above p and differences of conjugate primitive p-th roots. -/
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The same conjugate root, represented in the ring of integers. -/
def zetaConjInt (τ : G p K) : 𝓞 K := ⟨τ (ζ p K), integral_conj_zeta p K τ⟩

/-- The ramified prime in Bilu Proposition 4.6, with generator 1−ζ. -/
def ramifiedPrime : Ideal (𝓞 K) := Ideal.span {1 - zetaConjInt p K 1}

lemma zetaConjInt_one : zetaConjInt p K 1 = (ζ_spec p K).toInteger := by
  apply RingOfIntegers.ext
  rfl

lemma ramifiedPrime_eq_span :
    ramifiedPrime p K = Ideal.span {(ζ_spec p K).toInteger - 1} := by
  rw [ramifiedPrime, zetaConjInt_one, ← neg_sub, Ideal.span_singleton_neg]

lemma ramifiedPrime_facts (_hp2 : p ≠ 2) :
    (ramifiedPrime p K).IsPrime ∧ ramifiedPrime p K ≠ ⊥ ∧
    ramifiedPrime p K ^ (p - 1) = Ideal.span {(p : 𝓞 K)} ∧
    Ideal.absNorm (ramifiedPrime p K) = p := by
  rw [ramifiedPrime_eq_span]
  refine ⟨IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one' p (ζ_spec p K),
    Ideal.span_singleton_eq_bot.not.mpr (ζ_spec p K).zeta_sub_one_prime'.ne_zero, ?_, ?_⟩
  · rw [Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr
      (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p (ζ_spec p K))
  · have hroot : IsPrimitiveRoot (ζ p K) (p ^ (0 + 1)) := by simpa using ζ_spec p K
    let : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using
      (inferInstance : IsCyclotomicExtension {p} ℚ K)
    exact IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one p 0 hroot

lemma difference_ideal (hp2 : p ≠ 2) (s t : G p K) (hst : s ≠ t) :
    Ideal.span {zetaConjInt p K s - zetaConjInt p K t} = ramifiedPrime p K := by
  classical
  let : NeZero p := ⟨hp.out.ne_zero⟩
  have htroot : IsPrimitiveRoot (t (ζ p K)) p := (ζ_spec p K).map_of_injective t.injective
  have ht0 : t (ζ p K) ≠ 0 := htroot.ne_zero hp.out.ne_zero
  let ξ : K := s (ζ p K) / t (ζ p K)
  have hξpow : ξ ^ p = 1 := by
    dsimp [ξ]
    rw [div_pow, ← map_pow, ← map_pow, (ζ_spec p K).pow_eq_one,
      map_one, map_one, div_one]
  have hξne : ξ ≠ 1 := by
    intro he
    apply hst
    apply IsCyclotomicExtension.algEquiv_eq_of_apply_eq {p} ℚ K
    intro n hn _
    have hn' : n = p := Set.mem_singleton_iff.mp hn
    subst n
    exact ⟨ζ p K, ζ_spec p K, (div_eq_one_iff_eq ht0).mp he⟩
  have hξroot : IsPrimitiveRoot ξ p :=
    isPrimitiveRoot_of_mem_nthRootsFinset hp.out
      ((Polynomial.mem_nthRootsFinset hp.out.pos 1).mpr hξpow) hξne
  have hunit : IsUnit (zetaConjInt p K t) := by
    have he : zetaConjInt p K t = htroot.toInteger := by apply RingOfIntegers.ext; rfl
    rw [he]
    exact htroot.toInteger_isPrimitiveRoot.isUnit hp.out.ne_zero
  have hdiff : zetaConjInt p K s - zetaConjInt p K t =
      zetaConjInt p K t * (hξroot.toInteger - 1) := by
    apply RingOfIntegers.ext
    change s (ζ p K) - t (ζ p K) = t (ζ p K) * (ξ - 1)
    dsimp [ξ]
    field_simp
  rw [hdiff, Ideal.span_singleton_mul_left_unit hunit, ramifiedPrime_eq_span]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    (IsCyclotomicExtension.Rat.associated_sub_one_of_isPrimitiveRoot p (ζ_spec p K) hξroot).symm

lemma eq10 (hp2 : p ≠ 2) (x : ℤ) (σ τ : G p K) (hst : σ ≠ τ) :
    ramifiedPrime p K ≤ Ideal.span
      {((x : 𝓞 K) - zetaConjInt p K σ), ((x : 𝓞 K) - zetaConjInt p K τ)} := by
  rw [← difference_ideal p K hp2 σ τ hst]
  apply Ideal.span_le.mpr
  intro a ha
  have ha' : a = zetaConjInt p K σ - zetaConjInt p K τ :=
    Set.mem_singleton_iff.mp ha
  subst a
  let J : Ideal (𝓞 K) := Ideal.span
    {((x : 𝓞 K) - zetaConjInt p K σ), ((x : 𝓞 K) - zetaConjInt p K τ)}
  have hσ : (x : 𝓞 K) - zetaConjInt p K σ ∈ J :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hτ : (x : 𝓞 K) - zetaConjInt p K τ ∈ J :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hsub : ((x : 𝓞 K) - zetaConjInt p K τ) -
      ((x : 𝓞 K) - zetaConjInt p K σ) =
        zetaConjInt p K σ - zetaConjInt p K τ := by ring
  change zetaConjInt p K σ - zetaConjInt p K τ ∈ J
  rw [← hsub]
  exact J.sub_mem hτ hσ

end Catalan
