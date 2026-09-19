import Catalan.Stickelberger.GaussFamily
import Catalan.Stickelberger.GaussIdentities
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

/-- 积分迹 Gauss 和的 Jacobi 关系。 -/
theorem integralTraceGaussSum_mul_jacobiSum {ell : ℕ} [Fact ell.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [IsDomain A] (χ φ : MulChar F A) (hχφ : χ * φ ≠ 1)
    {ζ : A} (hζ : ζ ^ ell = 1) :
    integralTraceGaussSum (χ * φ) hζ * jacobiSum χ φ
      = integralTraceGaussSum χ hζ * integralTraceGaussSum φ hζ := by
  change gaussSum (χ * φ) _ * jacobiSum χ φ = gaussSum χ _ * gaussSum φ _
  exact jacobiSum_mul_nontrivial hχφ _

/-- Gauss 家族的整除形式次可加性。 -/
theorem gaussFamily_dvd_mul {ell : ℕ} [Fact ell.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [IsDomain A] (τ : MulChar F A) {ζ : A} (hζ : ζ ^ ell = 1)
    (a c : ℕ) (h : τ ^ (a + c) ≠ 1) :
    gaussFamily τ hζ (a + c) ∣ gaussFamily τ hζ a * gaussFamily τ hζ c := by
  have hne : τ ^ a * τ ^ c ≠ 1 := by
    simpa [pow_add] using h
  have hrel := integralTraceGaussSum_mul_jacobiSum (τ ^ a) (τ ^ c) hne hζ
  refine ⟨jacobiSum (τ ^ a) (τ ^ c), ?_⟩
  simpa [gaussFamily, pow_add] using hrel.symm

/-- 零指标：家族第 0 项是 −1。 -/
theorem gaussFamily_zero {ell : ℕ} [Fact ell.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [IsDomain A] (τ : MulChar F A) {ζ : A} (hζ : IsPrimitiveRoot ζ ell) :
    gaussFamily τ hζ.pow_eq_one 0 = -1 := by
  simp only [gaussFamily, pow_zero]
  exact integralTraceGaussSum_one hζ

/-- Frobenius 不变性：指标乘 ell 不改变家族成员。 -/
theorem gaussFamily_natCast_mul {ell : ℕ} [Fact ell.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    [CommRing A] (τ : MulChar F A) {ζ : A} (hζ : ζ ^ ell = 1) (a : ℕ) :
    gaussFamily τ hζ (ell * a) = gaussFamily τ hζ a := by
  change integralTraceGaussSum (τ ^ (ell * a)) hζ =
    integralTraceGaussSum (τ ^ a) hζ
  rw [Nat.mul_comm, pow_mul]
  exact integralTraceGaussSum_pow_char (τ ^ a) hζ

/-- 以 `x⁻¹` 为约化的特征，其阶恰为 `#F − 1`。 -/
theorem orderOf_eq_card_sub_one_of_inv_reduction
    {F A : Type*} [Field F] [Fintype F] [CommRing A] [IsDomain A]
    (f : A →+* F) (τ : MulChar F A)
    (hpow : ∀ x : F, (τ x) ^ Fintype.card F = τ x)
    (hred : ∀ x : F, f (τ x) = x⁻¹) :
    orderOf τ = Fintype.card F - 1 := by
  have hτne (x : F) (hx : x ≠ 0) : τ x ≠ 0 := by
    intro h
    have hz : x⁻¹ = 0 := by
      rw [← hred x, h, map_zero]
    exact (inv_ne_zero hx) hz
  have hpow_sub (x : F) (hx : x ≠ 0) :
      (τ x) ^ (Fintype.card F - 1) = 1 := by
    apply mul_right_cancel₀ (hτne x hx)
    rw [one_mul, ← pow_succ,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero)]
    exact hpow x
  have hτorder : τ ^ (Fintype.card F - 1) = 1 := by
    apply MulChar.ext
    intro x
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    exact hpow_sub (x : F) (Units.ne_zero x)
  have hupper : orderOf τ ∣ Fintype.card F - 1 :=
    orderOf_dvd_of_pow_eq_one hτorder
  have hunitpow : ∀ x : Fˣ, x ^ orderOf τ = 1 := by
    intro x
    have hτval : (τ (x : F)) ^ orderOf τ = 1 := by
      simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using
        congrArg (fun χ : MulChar F A => χ (x : F)) (pow_orderOf_eq_one τ)
    have hinv : ((x : F)⁻¹) ^ orderOf τ = 1 := by
      simpa only [map_pow, hred, map_one] using congrArg f hτval
    have hxpow : (x : F) ^ orderOf τ = 1 := by
      simpa only [inv_pow, inv_inv, inv_one] using congrArg Inv.inv hinv
    exact Units.ext hxpow
  have hlower : Fintype.card F - 1 ∣ orderOf τ :=
    (FiniteField.forall_pow_eq_one_iff F (orderOf τ)).mp hunitpow
  exact Nat.dvd_antisymm hupper hlower

/-- 互补配对的元素形式。 -/
theorem gaussFamily_mul_complement {ell : ℕ} [Fact ell.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [IsDomain A] (τ : MulChar F A) {ζ : A} (hζ : IsPrimitiveRoot ζ ell)
    (hord : orderOf τ = Fintype.card F - 1)
    (a : ℕ) (ha : 0 < a) (ha' : a < Fintype.card F - 1) :
    gaussFamily τ hζ.pow_eq_one a * gaussFamily τ hζ.pow_eq_one (Fintype.card F - 1 - a)
      = (τ ^ a) (-1) * (Fintype.card F : A) := by
  have hτorder : τ ^ (Fintype.card F - 1) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one τ
  have hchar_ne : τ ^ a ≠ 1 := by
    intro hchar
    have hdvd : orderOf τ ∣ a := orderOf_dvd_of_pow_eq_one hchar
    rw [hord] at hdvd
    exact (Nat.not_dvd_of_pos_of_lt ha ha') hdvd
  have hprod : τ ^ a * τ ^ (Fintype.card F - 1 - a) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' ha'.le, hτorder]
  have hinv : τ ^ (Fintype.card F - 1 - a) = (τ ^ a)⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  unfold gaussFamily
  rw [hinv]
  exact integralTraceGaussSum_mul_inv (τ ^ a) hchar_ne hζ

end Catalan.Stickelberger
