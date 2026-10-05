module

public import Catalan.Stickelberger.Factor
public import Catalan.FactorBridge

/-! # Descent from prime-by-prime valuations to `J ^ (pθ) = (Γ)` -/

/-!
# `Catalan.FactorDescent`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
namespace Catalan

open NumberField Catalan.Stickelberger

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The conjugate `σ_a⁻¹ P` of an integral ideal, as an integral ideal. -/
def conjIdeal (P : Ideal (𝓞 K)) (a : (ZMod p)ˣ) : Ideal (𝓞 K) :=
  Ideal.map (integerAut K (σ p K a)⁻¹).toRingHom P

/-- Stated as a theorem rather than an instance: the head symbol would be
`Ideal.map`, so a global instance here would fire on unrelated primality goals. -/
theorem conjIdeal_isPrime (P : Ideal (𝓞 K)) [P.IsPrime] (a : (ZMod p)ˣ) :
    (conjIdeal p K P a).IsPrime :=
  Ideal.map_isPrime_of_equiv (integerAut K (σ p K a)⁻¹)

theorem conjIdeal_ne_bot (P : Ideal (𝓞 K)) (hP0 : P ≠ ⊥) (a : (ZMod p)ˣ) :
    conjIdeal p K P a ≠ ⊥ := by
  intro h
  refine hP0 (le_bot_iff.mp fun x hx => ?_)
  have hmem : (integerAut K (σ p K a)⁻¹) x ∈ conjIdeal p K P a :=
    Ideal.mem_map_of_mem _ hx
  rw [h, Ideal.mem_bot] at hmem
  have := (integerAut K (σ p K a)⁻¹).injective (by simpa using hmem)
  simpa using this

open scoped Classical in
/-- **Descent step (general form).**  If `Γ`'s multiplicity at every prime is
the sum of `a` over the fiber `{a | σ_a⁻¹ P = Q}`, then `P ^ (pθ) = (Γ)` in the group of
fractional-ideal units — which is exactly the hypothesis `hΓ` of
`theta_principal_of_gauss_quotient`.

The single hypothesis `hall` replaces the earlier three (`hinj`, `hat`, `hout`).  That matters
mathematically, not just cosmetically: `hinj` said the conjugates `σ_a⁻¹ P` are pairwise
distinct, which holds **only** when the decomposition group of `P` is trivial, i.e. when `ell`
splits completely in `ℚ(ζ_p)`.  In general the conjugates repeat along the decomposition group,
and the exponent at each prime is the orbit sum that `hall` records.

`hall` is an input, not a theorem: it is what the Gauss-sum valuation has to supply, after the
valuation is transported from the conductor-`ell*(ell^f-1)` tower back to `ℚ(ζ_p)`.  That
transport is not done. -/
theorem ipow_pθ_eq_principalIdeal_of_emultiplicity_fiber
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥)
    (γ : 𝓞 K) (hγ : γ ≠ 0) (u : Kˣ) (hu : (u : K) = algebraMap (𝓞 K) K γ)
    (hall : ∀ Q : Ideal (𝓞 K), Q.IsPrime → Q ≠ ⊥ →
      emultiplicity Q (Ideal.span {γ})
        = ∑ a ∈ Finset.univ.filter (fun a : (ZMod p)ˣ => conjIdeal p K P a = Q),
            (((a : ZMod p).val : ℕ) : ℕ∞)) :
    ipow p K (idealUnit K P hP0) (pθ p K) = principalIdeal K u := by
  have hspan : (Ideal.span {γ} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hγ
  have hfac : Ideal.span {γ}
      = ∏ a : (ZMod p)ˣ, conjIdeal p K P a ^ ((a : ZMod p).val : ℕ) :=
    span_eq_prod_pow_of_emultiplicity_fiber Finset.univ (conjIdeal p K P)
      (fun a => ((a : ZMod p).val : ℕ)) hγ
      (fun a _ => conjIdeal_isPrime p K P a) (fun a _ => conjIdeal_ne_bot p K P hP0 a)
      (fun Q hQ hQ0 => hall Q hQ hQ0)
  have hJ : ∀ a : (ZMod p)ˣ, a ∈ (Finset.univ : Finset (ZMod p)ˣ) →
      ((idealAct K (σ p K a)⁻¹ (idealUnit K P hP0) : FracIdeal K))
        = ((conjIdeal p K P a : Ideal (𝓞 K)) : FracIdeal K) :=
    fun a _ => idealAct_idealUnit K (σ p K a)⁻¹ P hP0
  have hunits : idealUnit K (Ideal.span {γ}) hspan
      = ∏ a : (ZMod p)ˣ, (idealAct K (σ p K a)⁻¹ (idealUnit K P hP0))
          ^ ((a : ZMod p).val : ℕ) :=
    idealUnit_eq_prod_pow Finset.univ (conjIdeal p K P)
      (fun a => ((a : ZMod p).val : ℕ)) (Ideal.span {γ}) hspan hfac
      (fun a => idealAct K (σ p K a)⁻¹ (idealUnit K P hP0)) hJ
  rw [ipow_pθ_eq_prod p K (idealUnit K P hP0)]
  simp only [zpow_natCast]
  rw [← hunits, idealUnit_span_eq_principalIdeal γ u hu hspan]

/-- The totally-split special case. It is *derived* from the fiber form rather than proved
separately, so there is a single proof. `hinj` is false in general — prefer
`ipow_pθ_eq_principalIdeal_of_emultiplicity_fiber`. -/
theorem ipow_pθ_eq_principalIdeal_of_emultiplicity
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥)
    (γ : 𝓞 K) (hγ : γ ≠ 0) (u : Kˣ) (hu : (u : K) = algebraMap (𝓞 K) K γ)
    (hinj : ∀ a b : (ZMod p)ˣ, conjIdeal p K P a = conjIdeal p K P b → a = b)
    (hat : ∀ a : (ZMod p)ˣ, emultiplicity (conjIdeal p K P a) (Ideal.span {γ})
      = (((a : ZMod p).val : ℕ) : ℕ∞))
    (hout : ∀ Q : Ideal (𝓞 K), Q.IsPrime → Q ≠ ⊥ →
      (∀ a : (ZMod p)ˣ, Q ≠ conjIdeal p K P a) →
      emultiplicity Q (Ideal.span {γ}) = 0) :
    ipow p K (idealUnit K P hP0) (pθ p K) = principalIdeal K u := by
  classical
  refine ipow_pθ_eq_principalIdeal_of_emultiplicity_fiber p K P hP0 γ hγ u hu
    fun Q hQ hQ0 => ?_
  by_cases hmem : ∃ b : (ZMod p)ˣ, conjIdeal p K P b = Q
  · obtain ⟨b, hb⟩ := hmem
    have hfilter :
        (Finset.univ.filter (fun a : (ZMod p)ˣ => conjIdeal p K P a = Q)) = {b} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hinj a b (h.trans hb.symm), fun h => h ▸ hb⟩
    rw [hfilter, Finset.sum_singleton, ← hb]
    exact hat b
  · have hne : ∀ a : (ZMod p)ˣ, Q ≠ conjIdeal p K P a :=
      fun a h => hmem ⟨a, h.symm⟩
    have hfilter :
        (Finset.univ.filter (fun a : (ZMod p)ˣ => conjIdeal p K P a = Q)) = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hne a h.symm
    rw [hfilter, Finset.sum_empty]
    exact hout Q hQ hQ0 hne

end Catalan
