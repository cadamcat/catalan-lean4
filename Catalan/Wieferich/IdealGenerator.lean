module

public import Catalan.Wieferich.Defs
public import Catalan.FactorBridge
public import Catalan.Cassels.LambdaIdeal
public import Catalan.Stickelberger.Annihilation

/-!
# `Catalan.Wieferich.IdealGenerator`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
namespace Catalan.A1e

lemma exists_unit_mul_of_principalIdeal_eq
    (K : Type*) [Field K] [NumberField K] (x y : Kˣ)
    (h : principalIdeal K x = principalIdeal K y) :
    ∃ e : (𝓞 K)ˣ, x = Units.map (algebraMap (𝓞 K) K).toMonoidHom e * y := by
  have hf : FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) := by
    simpa only [principalIdeal, coe_toPrincipalIdeal] using
      congrArg (fun I : FracIdealUnit K => (I : FracIdeal K)) h.symm
  obtain ⟨e, he⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hf
  refine ⟨e, ?_⟩
  apply Units.ext
  change (x : K) = algebraMap (𝓞 K) K (e : 𝓞 K) * (y : K)
  change (e : 𝓞 K) • (y : K) = (x : K) at he
  rw [Algebra.smul_def] at he
  exact he.symm

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma lambda_stick_generator
    (q : ℕ) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1)
    (T : R p K) (hT : T ∈ stickSpan p K) :
    ∃ (e : (𝓞 K)ˣ) (a : Kˣ),
      upow p K (lambdaUnit p K x hp2) T =
        Units.map (algebraMap (𝓞 K) K).toMonoidHom e * a ^ q := by
  obtain ⟨l, I, hl, hI⟩ := lambda_ideal_pow p q hp.out hq hp2 hq2 x y hx hy h K
  have hlunit : (lambdaUnit p K x hp2 : K) = (l : K) := by
    simpa only [lambdaUnit, Units.val_div_eq_div_val, xmζ, Units.val_mk0] using hl.symm
  have hl0 : l ≠ 0 := by
    intro hzero
    apply (lambdaUnit p K x hp2).ne_zero
    rw [hlunit, hzero]
    rfl
  have hspan0 : (Ideal.span {l} : Ideal (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hI0 : I ≠ ⊥ := by
    intro hzero
    apply hspan0
    rw [hI, hzero, ← Ideal.zero_eq_bot, zero_pow hq.ne_zero]
  let J := idealUnit K I hI0
  have hLambda : principalIdeal K (lambdaUnit p K x hp2) = J ^ q := by
    rw [← idealUnit_span_eq_principalIdeal l (lambdaUnit p K x hp2) hlunit hspan0]
    apply Units.ext
    simp only [coe_idealUnit, Units.val_pow_eq_pow_val, J]
    rw [hI]
    exact (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K).map_pow I q
  obtain ⟨a, ha⟩ := stickelberger_annihilates p K T hT J
  have heq : principalIdeal K (upow p K (lambdaUnit p K x hp2) T) =
      principalIdeal K (a ^ q) := by
    have hcompat : ipow p K (principalIdeal K (lambdaUnit p K x hp2)) T =
        principalIdeal K (upow p K (lambdaUnit p K x hp2) T) :=
      ipow_principalIdeal p K (lambdaUnit p K x hp2) T
    rw [← hcompat, hLambda, ← zpow_natCast J q, ipow_zpow, ha]
    simp only [zpow_natCast, map_pow]
  obtain ⟨e, he⟩ := exists_unit_mul_of_principalIdeal_eq K _ _ heq
  exact ⟨e, a, he⟩

end Catalan.A1e
