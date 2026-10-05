module

public import Catalan.Cyclotomic.NormSubZeta
public import Catalan.IdealAction
public import Catalan.Cyclotomic.ValueBound

/-!
# `Catalan.Cyclotomic.OtherPrime`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
noncomputable section
namespace Catalan

lemma ideal_eq_prime_pow_of_prime_divisors {A : Type*} [CommRing A] [IsDedekindDomain A]
    (P I : Ideal A) (hI : I ≠ ⊥)
    (honly : ∀ Q : Ideal A, Prime Q → Q ∣ I → Q = P) :
    ∃ n : ℕ, I = P ^ n := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hI rfl).elim
  | h₂ I hu =>
    exact ⟨0, by simpa only [pow_zero] using isUnit_iff_eq_one.mp hu⟩
  | h₃ I Q hI0 hQ ih =>
    have hQP : Q = P := honly Q hQ (dvd_mul_right Q I)
    obtain ⟨n, hn⟩ := ih hI0 (fun Q' hQ' hQI => honly Q' hQ' (hQI.trans (dvd_mul_left I Q)))
    exact ⟨n + 1, by rw [hQP, hn, pow_succ, mul_comm]⟩

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma map_ramifiedPrime (s : G p K) :
    Ideal.map (integerAut K s).toRingHom (ramifiedPrime p K) = ramifiedPrime p K := by
  let : NeZero p := ⟨hp.out.ne_zero⟩
  have hsroot : IsPrimitiveRoot (s (ζ p K)) p := (ζ_spec p K).map_of_injective s.injective
  rw [ramifiedPrime_eq_span, Ideal.map_span, Set.image_singleton]
  have he : integerAut K s ((ζ_spec p K).toInteger - 1) = hsroot.toInteger - 1 := by
    apply RingOfIntegers.ext
    simp only [map_sub, map_one]
    rfl
  change Ideal.span {integerAut K s ((ζ_spec p K).toInteger - 1)} = _
  rw [he]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    (IsCyclotomicExtension.Rat.associated_sub_one_of_isPrimitiveRoot p (ζ_spec p K) hsroot).symm

lemma exists_other_prime_divisor_of_absNorm_gt (hp2 : p ≠ 2) (x : ℤ)
    (hnorm : p < Ideal.absNorm (Ideal.span {(x : 𝓞 K) - zetaConjInt p K 1})) :
    ∃ Q : Ideal (𝓞 K), Q.IsPrime ∧ Q ≠ ⊥ ∧ Q ≠ ramifiedPrime p K ∧
      (x : 𝓞 K) - zetaConjInt p K 1 ∈ Q := by
  classical
  let I : Ideal (𝓞 K) := Ideal.span {(x : 𝓞 K) - zetaConjInt p K 1}
  have hI0 : I ≠ ⊥ := by
    apply Ideal.span_singleton_eq_bot.not.mpr
    intro he
    apply x_sub_ζ_ne_zero p K x hp2
    have hc := congrArg (fun a : 𝓞 K => (a : K)) he
    change (x : K) - ζ p K = 0 at hc
    exact hc
  by_contra hno
  have honly (Q : Ideal (𝓞 K)) (hQ : Prime Q) (hQI : Q ∣ I) : Q = ramifiedPrime p K := by
    by_contra hne
    apply hno
    exact ⟨Q, Ideal.isPrime_of_prime hQ, hQ.ne_zero, hne,
      (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp hQI)⟩
  obtain ⟨n, hn⟩ := ideal_eq_prime_pow_of_prime_divisors (ramifiedPrime p K) I hI0 honly
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  let : Fintype (G p K) := Fintype.ofFinite _
  have hcard : 1 < Fintype.card (G p K) := by
    rw [Fintype.card_eq_nat_card]
    change 1 < Nat.card (K ≃ₐ[ℚ] K)
    rw [IsGalois.card_aut_eq_finrank, cyclotomic_degree p K]
    have := hp.out.two_le
    omega
  let : Nontrivial (G p K) := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨s, hs⟩ := exists_ne (1 : G p K)
  have hxI : (x : 𝓞 K) - zetaConjInt p K 1 ∈ I := Ideal.subset_span (Set.mem_singleton _)
  have helem : integerAut K s ((x : 𝓞 K) - zetaConjInt p K 1) =
      (x : 𝓞 K) - zetaConjInt p K s := by
    apply RingOfIntegers.ext
    change s ((x : K) - ζ p K) = (x : K) - s (ζ p K)
    simp only [map_sub, map_intCast]
  have hxmap : (x : 𝓞 K) - zetaConjInt p K s ∈
      Ideal.map (integerAut K s).toRingHom I := by
    rw [← helem]
    exact Ideal.mem_map_of_mem _ hxI
  rw [hn, Ideal.map_pow, map_ramifiedPrime] at hxmap
  have hle : ramifiedPrime p K ≤ ramifiedPrime p K ^ n := by
    apply (eq10 p K hp2 x 1 s hs.symm).trans
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change (x : 𝓞 K) - zetaConjInt p K 1 ∈ ramifiedPrime p K ^ n
      rw [← hn]
      exact hxI
    · exact hxmap
  have hdiv : Ideal.absNorm I ∣ p := by
    rw [hn]
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rwa [(ramifiedPrime_facts p K hp2).2.2.2] at hd
  exact (not_lt_of_ge (Nat.le_of_dvd hp.out.pos hdiv)) hnorm

/-- Bilu Proposition 4.6: a conjugate factor has a prime divisor other than (1−ζ). -/
lemma exists_other_prime_divisor (hp2 : p ≠ 2) (x : ℤ)
    (hx : 2 ≤ |x|) (hexc : p = 3 → x ≠ -2) :
    ∃ Q : Ideal (𝓞 K), Q.IsPrime ∧ Q ≠ ⊥ ∧ Q ≠ ramifiedPrime p K ∧
      (x : 𝓞 K) - zetaConjInt p K 1 ∈ Q := by
  apply exists_other_prime_divisor_of_absNorm_gt p K hp2 x
  rw [absNorm_span_x_sub_zeta]
  have h := cyclotomic_value_large p hp2 x hx hexc
  have h' : (p : ℤ) < ((∑ i ∈ Finset.range p, x ^ i).natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using h
  exact_mod_cast h'

end Catalan
