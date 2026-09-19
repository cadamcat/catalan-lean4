import Catalan.Cyclotomic.Basic

/-! Integral group-ring weight, size and exponentiation on field units. -/

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
section Definitions
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

/-- Bilu (2005), equation (1): w(Theta) = sum of its integer coefficients. -/
def weight (Θ : R p K) : ℤ := Θ.coeff.sum fun _ m => m

/-- Bilu (2005), section 2 following (1): size(Theta) = sum |m_sigma|. -/
def size (Θ : R p K) : ℤ := Θ.coeff.sum fun _ m => |m|

/-- Bilu (2005), section 2: the action of an automorphism on K^*. -/
def actUnit (τ : G p K) : Kˣ →* Kˣ :=
  Units.map τ.toRingEquiv.toRingHom.toMonoidHom

/-- Bilu (2005), section 4: a^Theta = product sigma(a)^(m_sigma). -/
def upow (a : Kˣ) (Θ : R p K) : Kˣ :=
  Θ.coeff.prod fun τ m => (actUnit p K τ a) ^ m

end Definitions

section Algebra
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

local instance : Fintype (G p K) := Fintype.ofFinite _

lemma weight_eq_sum (Θ : R p K) :
    weight p K Θ = ∑ τ : G p K, Θ.coeff τ := by
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

lemma size_eq_sum (Θ : R p K) :
    size p K Θ = ∑ τ : G p K, |Θ.coeff τ| := by
  exact Finsupp.sum_fintype _ _ (fun _ => abs_zero)

lemma weight_zero : weight p K (0 : R p K) = 0 := by
  simp only [weight, MonoidAlgebra.coeff_zero, Finsupp.sum_zero_index]

lemma size_zero : size p K (0 : R p K) = 0 := by
  simp only [size, MonoidAlgebra.coeff_zero, Finsupp.sum_zero_index]

lemma weight_add (Θ Ψ : R p K) :
    weight p K (Θ + Ψ) = weight p K Θ + weight p K Ψ := by
  simp only [weight_eq_sum, MonoidAlgebra.coeff_add, Finsupp.add_apply,
    Finset.sum_add_distrib]

lemma weight_neg (Θ : R p K) : weight p K (-Θ) = -weight p K Θ := by
  simp only [weight_eq_sum, MonoidAlgebra.coeff_neg, Finsupp.neg_apply,
    Finset.sum_neg_distrib]

lemma weight_sub (Θ Ψ : R p K) :
    weight p K (Θ - Ψ) = weight p K Θ - weight p K Ψ := by
  rw [sub_eq_add_neg, weight_add, weight_neg, sub_eq_add_neg]

lemma size_nonneg (Θ : R p K) : 0 ≤ size p K Θ := by
  rw [size_eq_sum]
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma size_neg (Θ : R p K) : size p K (-Θ) = size p K Θ := by
  simp only [size_eq_sum, MonoidAlgebra.coeff_neg, Finsupp.neg_apply, abs_neg]

lemma size_add_le (Θ Ψ : R p K) :
    size p K (Θ + Ψ) ≤ size p K Θ + size p K Ψ := by
  simp only [size_eq_sum, MonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_add_le _ _)

lemma size_sub_le (Θ Ψ : R p K) :
    size p K (Θ - Ψ) ≤ size p K Θ + size p K Ψ := by
  simpa only [sub_eq_add_neg, size_neg] using size_add_le p K Θ (-Ψ)

lemma abs_coeff_le_size (Θ : R p K) (τ : G p K) :
    |Θ.coeff τ| ≤ size p K Θ := by
  rw [size_eq_sum]
  exact Finset.single_le_sum (f := fun τ : G p K => |Θ.coeff τ|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)

lemma size_eq_zero_iff (Θ : R p K) : size p K Θ = 0 ↔ Θ = 0 := by
  constructor
  · intro h
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro τ
    have ht := abs_coeff_le_size p K Θ τ
    rw [h] at ht
    have hz : |Θ.coeff τ| = 0 := le_antisymm ht (abs_nonneg _)
    simpa only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using abs_eq_zero.mp hz
  · rintro rfl
    exact size_zero p K

/-- Bilu (2005), section 2: Theta^+ has coefficients max(m_sigma,0). -/
def posPart (Θ : R p K) : R p K :=
  MonoidAlgebra.ofCoeff (Θ.coeff.mapRange (fun m : ℤ => max m 0) (by norm_num))

/-- Bilu (2005), section 2: Theta^- has coefficients max(-m_sigma,0). -/
def negPart (Θ : R p K) : R p K :=
  MonoidAlgebra.ofCoeff (Θ.coeff.mapRange (fun m : ℤ => max (-m) 0) (by norm_num))

lemma part_identities (Θ : R p K) :
    Θ = posPart p K Θ - negPart p K Θ ∧
    size p K Θ = size p K (posPart p K Θ) + size p K (negPart p K Θ) ∧
    weight p K Θ = size p K (posPart p K Θ) - size p K (negPart p K Θ) := by
  have hp (τ : G p K) : (posPart p K Θ).coeff τ = max (Θ.coeff τ) 0 := rfl
  have hn (τ : G p K) : (negPart p K Θ).coeff τ = max (-Θ.coeff τ) 0 := rfl
  have hpoint (τ : G p K) :
      |Θ.coeff τ| = |max (Θ.coeff τ) 0| + |max (-Θ.coeff τ) 0| ∧
      Θ.coeff τ = |max (Θ.coeff τ) 0| - |max (-Θ.coeff τ) 0| := by
    rw [abs_of_nonneg (le_max_right (Θ.coeff τ) 0),
      abs_of_nonneg (le_max_right (-Θ.coeff τ) 0)]
    rcases le_total 0 (Θ.coeff τ) with h | h
    · rw [abs_of_nonneg h]; constructor <;> omega
    · rw [abs_of_nonpos h]; constructor <;> omega
  refine ⟨?_, ?_, ?_⟩
  · apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro τ
    change Θ.coeff τ = max (Θ.coeff τ) 0 - max (-Θ.coeff τ) 0
    omega
  · rw [size_eq_sum, size_eq_sum, size_eq_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro τ _
    rw [hp, hn]
    exact (hpoint τ).1
  · rw [weight_eq_sum, size_eq_sum, size_eq_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro τ _
    rw [hp, hn]
    exact (hpoint τ).2

lemma max_part_size (Θ : R p K) :
    (max (size p K (posPart p K Θ)) (size p K (negPart p K Θ)) : ℝ) =
      ((size p K Θ : ℝ) + |(weight p K Θ : ℝ)|) / 2 := by
  obtain ⟨_, hs, hw⟩ := part_identities p K Θ
  have hs' : (size p K Θ : ℝ) =
      (size p K (posPart p K Θ) : ℝ) + (size p K (negPart p K Θ) : ℝ) := by
    exact_mod_cast hs
  have hw' : (weight p K Θ : ℝ) =
      (size p K (posPart p K Θ) : ℝ) - (size p K (negPart p K Θ) : ℝ) := by
    exact_mod_cast hw
  rcases le_total (size p K (posPart p K Θ)) (size p K (negPart p K Θ)) with h | h
  · rw [max_eq_right (show (size p K (posPart p K Θ) : ℝ) ≤ size p K (negPart p K Θ) by exact_mod_cast h)]
    have hn : (weight p K Θ : ℝ) ≤ 0 := by
      exact_mod_cast (show weight p K Θ ≤ 0 by omega)
    rw [abs_of_nonpos hn]
    linarith
  · rw [max_eq_left (show (size p K (negPart p K Θ) : ℝ) ≤ size p K (posPart p K Θ) by exact_mod_cast h)]
    have hn : (0 : ℝ) ≤ weight p K Θ := by
      exact_mod_cast (show 0 ≤ weight p K Θ by omega)
    rw [abs_of_nonneg hn]
    linarith

lemma aug_size_lt_two (Θ : R p K) (hw : weight p K Θ = 0)
    (hs : (size p K Θ : ℝ) < 2) : Θ = 0 := by
  rcases part_identities p K Θ with ⟨_, hspl, hwpl⟩
  have hp := size_nonneg p K (posPart p K Θ)
  have hn := size_nonneg p K (negPart p K Θ)
  have hs' : size p K Θ < 2 := by exact_mod_cast hs
  apply (size_eq_zero_iff p K Θ).mp
  omega

-- candidate for Mathlib upstream
lemma finite_size_ball (r : ℝ) :
    Set.Finite {Θ : R p K | (size p K Θ : ℝ) ≤ r} := by
  classical
  let N : ℤ := ⌊r⌋
  let B := {m : ℤ // m ∈ Set.Icc (-N) N}
  let : Fintype B := (Set.finite_Icc (-N) N).fintype
  let S := {Θ : R p K | (size p K Θ : ℝ) ≤ r}
  have hb (Θ : S) (τ : G p K) : |Θ.val.coeff τ| ≤ N := by
    apply le_trans (abs_coeff_le_size p K Θ.val τ)
    exact Int.le_floor.mpr Θ.property
  let f : S → (G p K → B) := fun Θ τ =>
    ⟨Θ.val.coeff τ, (abs_le.mp (hb Θ τ))⟩
  have hf : Function.Injective f := by
    intro Θ Ψ h
    apply Subtype.ext
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro τ
    exact congrArg Subtype.val (congrFun h τ)
  let : Finite S := Finite.of_injective f hf
  exact Set.toFinite S

lemma upow_fintype (a : Kˣ) (Θ : R p K) :
    upow p K a Θ = ∏ τ : G p K, (actUnit p K τ a) ^ (Θ.coeff τ) := by
  exact Finsupp.prod_fintype _ _ (fun _ => zpow_zero _)

lemma upow_zero (a : Kˣ) : upow p K a (0 : R p K) = 1 := by
  simp only [upow, MonoidAlgebra.coeff_zero, Finsupp.prod_zero_index]

lemma upow_add (a : Kˣ) (Θ Ψ : R p K) :
    upow p K a (Θ + Ψ) = upow p K a Θ * upow p K a Ψ := by
  unfold upow
  rw [MonoidAlgebra.coeff_add]
  exact Finsupp.prod_add_index' (fun _ => zpow_zero _)
    (fun _ _ _ => zpow_add _ _ _)

/-- Bilu (2005), section 4: the group-ring exponent is additive-to-multiplicative. -/
def upowAddHom (a : Kˣ) : R p K →+ Additive Kˣ where
  toFun Θ := Additive.ofMul (upow p K a Θ)
  map_zero' := upow_zero p K a
  map_add' := upow_add p K a

lemma upow_neg (a : Kˣ) (Θ : R p K) :
    upow p K a (-Θ) = (upow p K a Θ)⁻¹ := by
  exact (upowAddHom p K a).map_neg Θ

lemma upow_single (a : Kˣ) (τ : G p K) (m : ℤ) :
    upow p K a (MonoidAlgebra.single τ m) = (actUnit p K τ a) ^ m := by
  exact Finsupp.prod_single_index (zpow_zero _)

lemma actUnit_mul (σ τ : G p K) (a : Kˣ) :
    actUnit p K (σ * τ) a = actUnit p K σ (actUnit p K τ a) := by
  apply Units.ext
  rfl

lemma upow_base_one (Θ : R p K) : upow p K (1 : Kˣ) Θ = 1 := by
  simp only [upow_fintype, map_one, one_zpow, Finset.prod_const_one]

lemma upow_base_mul (a b : Kˣ) (Θ : R p K) :
    upow p K (a * b) Θ = upow p K a Θ * upow p K b Θ := by
  simp only [upow_fintype, map_mul, mul_zpow, Finset.prod_mul_distrib]

lemma upow_pow (a : Kˣ) (Θ : R p K) (n : ℕ) :
    upow p K (a ^ n) Θ = upow p K a Θ ^ n := by
  induction n with
  | zero => simp only [pow_zero, upow_base_one]
  | succ n ih => rw [pow_succ, upow_base_mul, ih, pow_succ]

lemma upow_mul_single_int (a : Kˣ) (σ : G p K) (m : ℤ) (Θ : R p K) :
    upow p K a (MonoidAlgebra.single σ m * Θ) =
      (actUnit p K σ (upow p K a Θ)) ^ m := by
  refine MonoidAlgebra.induction_linear Θ ?_ ?_ ?_
  · simp only [mul_zero, upow_zero, map_one, one_zpow]
  · intro Θ Ψ hΘ hΨ
    rw [mul_add, upow_add, hΘ, hΨ, upow_add, map_mul, mul_zpow]
  · intro τ n
    rw [MonoidAlgebra.single_mul_single, upow_single, upow_single, map_zpow,
      ← actUnit_mul, mul_comm m n, zpow_mul]

lemma upow_mul_single (a : Kˣ) (τ : G p K) (Θ : R p K) :
    upow p K a (MonoidAlgebra.single τ 1 * Θ) =
      actUnit p K τ (upow p K a Θ) := by
  simpa only [zpow_one] using upow_mul_single_int p K a τ 1 Θ

lemma upow_mul (a : Kˣ) (A Θ : R p K) :
    upow p K a (A * Θ) = upow p K (upow p K a Θ) A := by
  refine MonoidAlgebra.induction_linear A ?_ ?_ ?_
  · simp only [zero_mul, upow_zero]
  · intro A B hA hB
    rw [add_mul, upow_add, hA, hB, upow_add]
  · intro τ m
    rw [upow_mul_single_int, upow_single]

end Algebra


end Catalan
