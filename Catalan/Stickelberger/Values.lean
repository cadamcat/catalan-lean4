module

public import Catalan.Stickelberger.ValuesBridge
public import Catalan.Stickelberger.DigitValuation
public import Catalan.Stickelberger.Local

/-! # The Gauss-family ideal valuation is the base-`ell` digit sum -/

/-!
# `Catalan.Stickelberger.Values`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

open Ideal

/-- The ideal valuation of the Gauss family at `I` is the base-`ell`
digit sum of the index. -/
theorem gaussFamily_emultiplicity_eq_digitSum
    {ell : ℕ} [hp : Fact ell.Prime]
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I.IsPrime) (hI0 : I ≠ ⊥)
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (π : A →+* F) (d : ℕ) (hcard : Fintype.card F = ell ^ d) (hell : 2 < ell)
    (τ : MulChar F A) {ζ : A} (hζ : IsPrimitiveRoot ζ ell)
    (hpow : ∀ x : F, (τ x) ^ Fintype.card F = τ x)
    (hred : ∀ x : F, π (τ x) = x⁻¹)
    (hone : emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one 1}) = 1)
    (hram : emultiplicity I (Ideal.span {(ell : A)}) = ((ell - 1 : ℕ) : ℕ∞))
    (a : ℕ) (ha : a < ell ^ d - 1) :
    emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one a})
      = ((ell.digits a).sum : ℕ∞) := by
  classical
  have hIprime : Prime I := Ideal.prime_of_isPrime hI0 hI
  have hsplit : ∀ x y : A, emultiplicity I (Ideal.span {x * y})
      = emultiplicity I (Ideal.span {x}) + emultiplicity I (Ideal.span {y}) := by
    intro x y
    rw [← Ideal.span_singleton_mul_span_singleton, emultiplicity_mul hIprime]
  have hunit : ∀ x : A, IsUnit x → emultiplicity I (Ideal.span {x}) = 0 := by
    intro x hx
    rw [Ideal.span_singleton_eq_top.mpr hx]
    simpa using emultiplicity_of_one_right hIprime.not_isUnit
  have hdegen : ∀ k : ℕ, τ ^ k = 1 → gaussFamily τ hζ.pow_eq_one k = -1 := by
    intro k hk
    rw [gaussFamily, hk]
    exact integralTraceGaussSum_one hζ
  have hzero : emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one 0}) = 0 := by
    rw [gaussFamily_zero τ hζ]
    exact hunit _ isUnit_one.neg
  have hadd : ∀ b c : ℕ,
      emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one (b + c)})
        ≤ emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one b})
          + emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one c}) := by
    intro b c
    by_cases hbc : τ ^ (b + c) = 1
    · rw [hdegen _ hbc, hunit _ isUnit_one.neg]
      exact zero_le
    · have hidvd : (Ideal.span {gaussFamily τ hζ.pow_eq_one (b + c)} : Ideal A) ∣
          Ideal.span {gaussFamily τ hζ.pow_eq_one b * gaussFamily τ hζ.pow_eq_one c} := by
        rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.mem_span_singleton.mpr (gaussFamily_dvd_mul τ hζ.pow_eq_one b c hbc)
      calc emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one (b + c)})
          ≤ emultiplicity I
              (Ideal.span {gaussFamily τ hζ.pow_eq_one b * gaussFamily τ hζ.pow_eq_one c}) :=
            emultiplicity_le_emultiplicity_of_dvd_right hidvd
        _ = _ := hsplit _ _
  have hfrob : ∀ k : ℕ,
      emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one (ell * k)})
        = emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one k}) := by
    intro k
    rw [gaussFamily_natCast_mul τ hζ.pow_eq_one k]
  have hord : orderOf τ = Fintype.card F - 1 :=
    orderOf_eq_card_sub_one_of_inv_reduction π τ hpow hred
  have hpair : ∀ k : ℕ, 0 < k → k < ell ^ d - 1 →
      emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one k})
        + emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one (ell ^ d - 1 - k)})
        = ((d * (ell - 1) : ℕ) : ℕ∞) := by
    intro k hk0 hkd
    have hk' : k < Fintype.card F - 1 := by rw [hcard]; exact hkd
    have hsub : Fintype.card F - 1 - k = ell ^ d - 1 - k := by rw [hcard]
    have hprod := gaussFamily_mul_complement τ hζ hord k hk0 hk'
    rw [hsub] at hprod
    have hunitval : IsUnit ((τ ^ k) (-1) : A) := by
      refine isUnit_iff_exists_inv.mpr ⟨(τ ^ k) (-1), ?_⟩
      rw [← map_mul]
      simp
    have hcardpow : ((Fintype.card F : ℕ) : A) = (ell : A) ^ d := by
      rw [hcard, Nat.cast_pow]
    rw [← hsplit, hprod, hsplit, hunit _ hunitval, zero_add, hcardpow,
      ← Ideal.span_singleton_pow, emultiplicity_pow hIprime, hram, Nat.cast_mul]
  exact enatValuation_eq_digitSum
    (fun k => emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one k})) ell d
    (by omega) hzero (le_of_eq hone) hadd hfrob hpair a ha


section Compose
open NumberField
attribute [local instance] Ideal.Quotient.field Fintype.ofFinite

/-- At an actual prime `P` of the cyclotomic field of conductor
`n = ell * (ell ^ f - 1)`, the ideal valuation of the Gauss family is the
base-`ell` digit sum of the index, for every index below
`ell ^ f - 1`.

This strengthens `exists_cyclotomic_gaussFamily_emultiplicity_one` from the single
index `1` to the whole family.  No hypothesis is added. -/
theorem exists_cyclotomic_gaussFamily_emultiplicity_eq_digitSum
    (ell f m n : ℕ) [hp : Fact ell.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span {(ell : ℤ)})]
    [Algebra (ZMod ell) (𝓞 K ⧸ P)]
    (hell : 2 < ell) (hf : 0 < f) (hm : m = ell ^ f - 1) (hn : n = ell * m) :
    ∃ (ζ : 𝓞 K) (hζ : IsPrimitiveRoot ζ ell) (τ : MulChar (𝓞 K ⧸ P) (𝓞 K)),
      (∀ x : 𝓞 K ⧸ P, Ideal.Quotient.mk P (τ x) = x⁻¹) ∧
      ∀ a : ℕ, a < ell ^ f - 1 →
        emultiplicity P (Ideal.span {gaussFamily τ hζ.pow_eq_one a})
          = ((ell.digits a).sum : ℕ∞) := by
  obtain ⟨hcard, hmemP, hdvd, μ, ζ, hμ, hζ, huni, hnot⟩ :=
    cyclotomic_route_inputs ell f m n K P hell hf hm hn
  have : CharP (𝓞 K ⧸ P) ell :=
    charP_quotient_of_mem P ell hp.out (Ideal.IsPrime.ne_top inferInstance) hmemP
  have hcard' : Fintype.card (𝓞 K ⧸ P) = ell ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hsub : Fintype.card (𝓞 K ⧸ P) - 1 = m := by rw [hcard', hm]
  have hF : 2 < Fintype.card (𝓞 K ⧸ P) := by
    rw [hcard']
    exact lt_of_lt_of_le (by omega) (le_trans (by omega : 3 ≤ ell) (Nat.le_self_pow hf.ne' ell))
  have hker : ∀ a : 𝓞 K, Ideal.Quotient.mk P a = 0 ↔ a ∈ P := fun a =>
    Ideal.Quotient.eq_zero_iff_mem
  have hfμ : IsPrimitiveRoot (Ideal.Quotient.mk P μ) m := by
    have : NeZero m := ⟨by rw [hm]; have := Nat.le_self_pow hf.ne' ell; omega⟩
    exact isPrimitiveRoot_quotient_of_not_dvd P m ell hp.out hmemP hdvd hμ
  obtain ⟨τ, hpow, hred, -, hval⟩ :=
    exists_gaussFamily_emultiplicity_one_of_uniformizer_ideal P
      (Ideal.IsPrime.ne_top inferInstance) (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective hker hF hell (hsub ▸ hμ) (hsub ▸ hfμ) hζ hnot
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h] at hmemP
    have : (ell : 𝓞 K) = 0 := (Ideal.mem_bot).mp hmemP
    have hz : ((ell : ℕ) : 𝓞 K) = ((0 : ℕ) : 𝓞 K) := by simpa using this
    exact hp.out.ne_zero (Nat.cast_injective hz)
  have hram : emultiplicity P (Ideal.span {(ell : 𝓞 K)}) = ((ell - 1 : ℕ) : ℕ∞) :=
    emultiplicity_span_natCast_eq ell f m n K P hell hf hm hn
  refine ⟨ζ, hζ, τ, hred, fun a ha => ?_⟩
  exact gaussFamily_emultiplicity_eq_digitSum P inferInstance hP0
    (Ideal.Quotient.mk P) f hcard' hell τ hζ hpow hred hval hram a ha

end Compose

end Catalan.Stickelberger
