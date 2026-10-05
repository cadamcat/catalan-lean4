module

public import Catalan.Mihailescu.LinearLog

/-!
# `Catalan.Mihailescu.PhaseCore`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField

section Phase
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ) (φ : K →+* ℂ)

/-- Bilu (2005), section 4.2: alpha restricted to the augmented ideal. -/
def augAlpha (hp2 : p ≠ 2) (Θ : mihAug p K q x hp2) : Kˣ :=
  alpha p K q x hp2 ⟨Θ.val, Θ.property.1⟩

/-- Bilu (2005), section 4.2: alpha viewed through the ONE fixed complex embedding. -/
def alphaC (hp2 : p ≠ 2) (Θ : mihAug p K q x hp2) : ℂ :=
  φ ((augAlpha p K q x hp2 Θ : Kˣ) : K)

lemma alphaC_zero (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2) :
    alphaC p K q x φ hp2 0 = 1 := by
  change φ ((alpha p K q x hp2 0 : Kˣ) : K) = 1
  rw [alpha_zero p K q x hp2 hpq hq2]
  exact map_one φ

lemma alphaC_add (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (Θ Ψ : mihAug p K q x hp2) :
    alphaC p K q x φ hp2 (Θ + Ψ) =
      alphaC p K q x φ hp2 Θ * alphaC p K q x φ hp2 Ψ := by
  change φ ((alpha p K q x hp2
      (⟨Θ.val, Θ.property.1⟩ + ⟨Ψ.val, Ψ.property.1⟩) : Kˣ) : K) = _
  rw [alpha_add p K q x hp2 hpq hq2]
  exact map_mul φ _ _

lemma alphaC_pow (hp2 : p ≠ 2) (hx : 1 < (|x| : ℝ))
    (Θ : mihAug p K q x hp2) :
    alphaC p K q x φ hp2 Θ ^ q = Complex.exp (linearLog p K φ x Θ.val) := by
  rw [exp_linearLog p K φ x hp2 hx Θ.val Θ.property.2]
  have h := congrArg (fun a : Kˣ => φ (a : K))
    (alpha_pow p K q x hp2 ⟨Θ.val, Θ.property.1⟩)
  simpa only [alphaC, augAlpha, Units.val_pow_eq_pow_val, map_pow] using h

/-- Bilu (2005), Proposition 4.8, explicit branch-safe construction:
xi_phi(Theta)=phi(alpha(Theta))*exp(-L_phi(Theta)/q). -/
def phaseValue (hp2 : p ≠ 2) (Θ : mihAug p K q x hp2) : ℂ :=
  alphaC p K q x φ hp2 Θ * Complex.exp (-linearLog p K φ x Θ.val / (q : ℂ))

-- candidate for Mathlib upstream
lemma exp_nat_mul_manual (z : ℂ) (n : ℕ) :
    Complex.exp ((n : ℂ) * z) = Complex.exp z ^ n := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, Complex.exp_zero, pow_zero]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Complex.exp_add, ih, pow_succ]

lemma phaseValue_pow (hp2 : p ≠ 2) (hx : 1 < (|x| : ℝ))
    (Θ : mihAug p K q x hp2) : phaseValue p K q x φ hp2 Θ ^ q = 1 := by
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  rw [phaseValue, mul_pow, alphaC_pow p K q x φ hp2 hx,
    ← exp_nat_mul_manual, ← Complex.exp_add]
  have hz : linearLog p K φ x Θ.val +
      (q : ℂ) * (-linearLog p K φ x Θ.val / (q : ℂ)) = 0 := by
    field_simp [hq]
    ring
  rw [hz, Complex.exp_zero]

/-- Bilu (2005), Proposition 4.8: the phase, as an actual element of mu_q(C).
It is defined on the entire augmented group; the stated uniqueness is local. -/
def xi (hp2 : p ≠ 2) (hx : 1 < (|x| : ℝ))
    (Θ : mihAug p K q x hp2) : rootsOfUnity q ℂ :=
  rootsOfUnity.mkOfPowEq (phaseValue p K q x φ hp2 Θ)
    (phaseValue_pow p K q x φ hp2 hx Θ)

lemma xi_val (hp2 : p ≠ 2) (hx : 1 < (|x| : ℝ))
    (Θ : mihAug p K q x hp2) :
    (((xi p K q x φ hp2 hx Θ : rootsOfUnity q ℂ) : ℂˣ) : ℂ) =
      phaseValue p K q x φ hp2 Θ := by
  rfl

lemma xi_zero (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hx : 1 < (|x| : ℝ)) : xi p K q x φ hp2 hx 0 = 1 := by
  apply rootsOfUnity.coe_injective
  simp only [xi_val, phaseValue, alphaC_zero p K q x φ hp2 hpq hq2,
    AddSubgroup.coe_zero, linearLog_zero, neg_zero, zero_div, Complex.exp_zero, mul_one,
    OneMemClass.coe_one, Units.val_one]

lemma xi_add (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hx : 1 < (|x| : ℝ)) (Θ Ψ : mihAug p K q x hp2) :
    xi p K q x φ hp2 hx (Θ + Ψ) =
      xi p K q x φ hp2 hx Θ * xi p K q x φ hp2 hx Ψ := by
  apply rootsOfUnity.coe_injective
  change phaseValue p K q x φ hp2 (Θ + Ψ) =
    phaseValue p K q x φ hp2 Θ * phaseValue p K q x φ hp2 Ψ
  simp only [phaseValue, alphaC_add p K q x φ hp2 hpq hq2, AddSubgroup.coe_add, linearLog_add]
  rw [neg_add, add_div, Complex.exp_add]
  ring

/-- Bilu (2005), Proposition 4.8: the linear lift produces a global character;
on the small balls this is Bilu's uniquely specified local homomorphism. -/
def xiHom (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hx : 1 < (|x| : ℝ)) :
    mihAug p K q x hp2 →+ Additive (rootsOfUnity q ℂ) where
  toFun Θ := Additive.ofMul (xi p K q x φ hp2 hx Θ)
  map_zero' := xi_zero p K q x φ hp2 hpq hq2 hx
  map_add' := xi_add p K q x φ hp2 hpq hq2 hx

lemma xi_neg (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hx : 1 < (|x| : ℝ)) (Θ : mihAug p K q x hp2) :
    xi p K q x φ hp2 hx (-Θ) = (xi p K q x φ hp2 hx Θ)⁻¹ := by
  exact (xiHom p K q x φ hp2 hpq hq2 hx).map_neg Θ

lemma xi_sub (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hx : 1 < (|x| : ℝ)) (Θ Ψ : mihAug p K q x hp2) :
    xi p K q x φ hp2 hx (Θ - Ψ) =
      xi p K q x φ hp2 hx Θ / xi p K q x φ hp2 hx Ψ := by
  exact (xiHom p K q x φ hp2 hpq hq2 hx).map_sub Θ Ψ


end Phase
end Catalan
