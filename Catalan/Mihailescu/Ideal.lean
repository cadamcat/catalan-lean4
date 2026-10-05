module

public import Catalan.Cyclotomic.Elements
public import Catalan.Cyclotomic.UnitPowers

/-! The Mihăilescu ideal and its augmentation subgroup, without height assumptions. -/
/-!
# `Catalan.Mihailescu.Ideal`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
section BaseElement
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The nonzero field element x−ζ, represented as a unit. -/
def xmζ (x : ℤ) (hp2 : p ≠ 2) : Kˣ :=
  Units.mk0 _ (x_sub_ζ_ne_zero p K x hp2)
end BaseElement

section MihIdeal
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ)

/-- Bilu (2005), section 4, Definition: I_M={Theta : (x-zeta)^Theta is a q-th power}. -/
def mihIdeal (hp2 : p ≠ 2) : Ideal (R p K) where
  carrier := {Θ | ∃ b : Kˣ, upow p K (xmζ p K x hp2) Θ = b ^ q}
  zero_mem' := by
    refine ⟨1, ?_⟩
    rw [upow_zero, one_pow]
  add_mem' := by
    rintro Θ Ψ ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [upow_add, ha, hb, mul_pow]
  smul_mem' := by
    rintro A Θ ⟨b, hb⟩
    change ∃ c : Kˣ, upow p K (xmζ p K x hp2) (A * Θ) = c ^ q
    refine ⟨upow p K b A, ?_⟩
    rw [upow_mul, hb, upow_pow]

/-- Bilu (2005), section 2 and section 4: I_M^aug, as an additive subgroup. -/
def mihAug (hp2 : p ≠ 2) : AddSubgroup (R p K) where
  carrier := {Θ | Θ ∈ mihIdeal p K q x hp2 ∧ weight p K Θ = 0}
  zero_mem' := ⟨(mihIdeal p K q x hp2).zero_mem, weight_zero p K⟩
  add_mem' := by
    rintro Θ Ψ ⟨hΘ, hwΘ⟩ ⟨hΨ, hwΨ⟩
    exact ⟨(mihIdeal p K q x hp2).add_mem hΘ hΨ,
      by rw [weight_add, hwΘ, hwΨ, add_zero]⟩
  neg_mem' := by
    rintro Θ ⟨hΘ, hwΘ⟩
    exact ⟨(mihIdeal p K q x hp2).neg_mem hΘ,
      by rw [weight_neg, hwΘ, neg_zero]⟩

/-- Bilu (2005), section 4: the real-radius augmented ball, using an integer size. -/
def augBall (hp2 : p ≠ 2) (r : ℝ) : Set (R p K) :=
  {Θ ∈ mihIdeal p K q x hp2 | weight p K Θ = 0 ∧ (size p K Θ : ℝ) ≤ r}

lemma finite_aug_ball (hp2 : p ≠ 2) (r : ℝ) :
    (augBall p K q x hp2 r).Finite := by
  exact (finite_size_ball p K r).subset (fun _ h => h.2.2)

/-- Bilu (2005), section 4.2: a chosen q-th root; uniqueness is proved separately. -/
def alpha (hp2 : p ≠ 2) (Θ : mihIdeal p K q x hp2) : Kˣ :=
  Classical.choose Θ.property

lemma alpha_pow (hp2 : p ≠ 2) (Θ : mihIdeal p K q x hp2) :
    alpha p K q x hp2 Θ ^ q = upow p K (xmζ p K x hp2) Θ.val := by
  exact (Classical.choose_spec Θ.property).symm

lemma alpha_zero (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2) :
    alpha p K q x hp2 0 = 1 := by
  apply unit_pow_injective p K q hpq hq2
  dsimp only
  rw [alpha_pow, one_pow]
  exact upow_zero p K _

lemma alpha_add (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (Θ Ψ : mihIdeal p K q x hp2) :
    alpha p K q x hp2 (Θ + Ψ) = alpha p K q x hp2 Θ * alpha p K q x hp2 Ψ := by
  apply unit_pow_injective p K q hpq hq2
  dsimp only
  rw [alpha_pow, mul_pow, alpha_pow, alpha_pow]
  exact upow_add p K _ Θ.val Ψ.val

/-- Bilu (2005), section 4.2: alpha is an additive-to-multiplicative group homomorphism. -/
def alphaHom (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2) :
    (mihIdeal p K q x hp2) →+ Additive Kˣ where
  toFun Θ := Additive.ofMul (alpha p K q x hp2 Θ)
  map_zero' := alpha_zero p K q x hp2 hpq hq2
  map_add' := alpha_add p K q x hp2 hpq hq2

lemma alpha_neg (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (Θ : mihIdeal p K q x hp2) :
    alpha p K q x hp2 (-Θ) = (alpha p K q x hp2 Θ)⁻¹ := by
  exact (alphaHom p K q x hp2 hpq hq2).map_neg Θ

end MihIdeal

section Embedding
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance mihIdealFintypeG : Fintype (G p K) := Fintype.ofFinite _

lemma map_upow_xmζ (φ : K →+* ℂ) (x : ℤ) (hp2 : p ≠ 2) (Θ : R p K) :
    φ ((upow p K (xmζ p K x hp2) Θ : Kˣ) : K) =
      ∏ τ : G p K, ((x : ℂ) - φ (τ (ζ p K))) ^ (Θ.coeff τ) := by
  rw [map_upow]
  apply Finset.prod_congr rfl
  intro τ _
  congr 1
  change φ (τ ((x : K) - ζ p K)) = (x : ℂ) - φ (τ (ζ p K))
  simp only [map_sub, map_intCast]

end Embedding
end Catalan
