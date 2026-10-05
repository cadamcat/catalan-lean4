module

public import Catalan.Wieferich.Core
public import Catalan.Wieferich.Action
public import Catalan.Wieferich.Conjugation
public import Catalan.Wieferich.IdealGenerator

/-!
# `Catalan.Wieferich.Minus`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open NumberField
namespace Catalan.A1e
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The needed Kummer quotient assertion for the frozen conjugation. -/
lemma kummer_unit_quotient (hp2 : p ≠ 2) (u : (𝓞 K)ˣ) :
    ∃ n : ℕ, 0 < n ∧
      ((u : K) / ι p K (u : K)) ^ n = 1 := by
  let f : (𝓞 K) →+* (𝓞 K) :=
    RingOfIntegers.mapRingHom (ι p K).toRingEquiv.toRingHom
  let v : (𝓞 K)ˣ := Units.map f.toMonoidHom u
  have hv : (v : K) = ι p K (u : K) := rfl
  have hc : ∀ φ : K →+* ℂ, φ (v : K) = conj (φ (u : K)) := by
    intro φ
    rw [hv]
    exact iota_on_embeddings p K hp2 φ (u : K)
  simpa only [hv] using kronecker_unit_pair u v hc


lemma minus_stick_qth
    (q : ℕ) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1)
    (T : R p K) (hT : T ∈ stickSpan p K) :
    ∃ b : Kˣ, upow p K (xmζ p K x hp2) (minusPart p K T) = b ^ q := by
  obtain ⟨e, a, hgen⟩ := lambda_stick_generator p K q hq hp2 hq2 x y hx hy h T hT
  let d : Kˣ := Units.mk0 (1 - ζ p K)
    (sub_ne_zero.mpr ((ζ_spec p K).ne_one hp.out.one_lt).symm)
  let r₀ : Kˣ := d / actUnit p K (ι p K) d
  have hr₀ : r₀ ^ (2 * p) = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [minus_root_quotient p K d rfl]
    rw [(even_two_mul p).neg_pow, mul_comm 2 p, pow_mul, (ζ_spec p K).pow_eq_one, one_pow]
  let eK : Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom e
  let E : Kˣ := eK / actUnit p K (ι p K) eK
  have hEfin : ∃ n : ℕ, 0 < n ∧ E ^ n = 1 := by
    obtain ⟨n, hn, he⟩ := kummer_unit_quotient p K hp2 e
    refine ⟨n, hn, ?_⟩
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    dsimp only [E]
    rw [Units.val_div_eq_div_val]
    change ((e : K) / ι p K (e : K)) ^ n = 1
    exact he
  have hE : E ^ (2 * p) = 1 := torsion_order_bound p K hp2 E hEfin
  let r : Kˣ := upow p K r₀ T * E
  have hr : r ^ (2 * p) = 1 := by
    dsimp only [r]
    rw [mul_pow, upow_pow_eq_one p K r₀ T (2 * p) hr₀, hE, one_mul]
  have hcop : q.Coprime (2 * p) :=
    ((Nat.coprime_primes hq Nat.prime_two).mpr hq2).mul_right
      ((Nat.coprime_primes hq hp.out).mpr hpq.symm)
  obtain ⟨c, hc⟩ := qth_root_of_coprime r (2 * p) q hr hcop
  have hxunit : xmζ p K x hp2 = lambdaUnit p K x hp2 * d := by
    change xmζ p K x hp2 = (xmζ p K x hp2 / d) * d
    simp
  have hLambdaMinus : upow p K (lambdaUnit p K x hp2) (minusPart p K T) =
      E * (a / actUnit p K (ι p K) a) ^ q := by
    rw [upow_minusPart_eq, hgen, map_mul, map_pow]
    change (eK * a ^ q) / (actUnit p K (ι p K) eK * (actUnit p K (ι p K) a) ^ q) = _
    rw [mul_div_mul_comm, ← div_pow]
  refine ⟨c * (a / actUnit p K (ι p K) a), ?_⟩
  rw [hxunit, upow_base_mul, hLambdaMinus, upow_minusPart_base, mul_pow, hc]
  change E * (a / actUnit p K (ι p K) a) ^ q * upow p K r₀ T =
    (upow p K r₀ T * E) * (a / actUnit p K (ι p K) a) ^ q
  ac_rfl

end Catalan.A1e
