import Catalan.Stickelberger.GaussFamily
import Mathlib

/-! # Galois action on the integral trace Gauss sum

If a ring endomorphism `σ` of the coefficient ring fixes the character values and sends the
`ell`-th root of unity `ζ` to `ζ ^ j`, then it multiplies the Gauss sum by `χ(j)⁻¹`.  The
identity is stated multiplicatively, so no inverse and no invertibility of `χ(j)` is needed.

Consequence: if `χ ^ p = 1` then `σ` fixes the `p`-th power of the Gauss sum.  That is the
mechanism by which `g ^ p` descends from `ℚ(ζ_p, ζ_ell)` to `ℚ(ζ_p)`.
-/

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

section Twist

variable {ell : ℕ} [NeZero ell] {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
  [CommRing A]

omit [Fintype F] in
/-- 把 `ζ` 换成 `ζ ^ j` 后的迹加性特征，就是原特征的 `mulShift`（位移量是 `j` 在 `F` 中的像）。 -/
lemma integralTraceAddChar_pow {ζ : A} (hζ : ζ ^ ell = 1) (j : ℕ) :
    (AddChar.zmodChar ell (show (ζ ^ j) ^ ell = 1 by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow])).compAddMonoidHom
          (Algebra.trace (ZMod ell) F).toAddMonoidHom
      = ((AddChar.zmodChar ell hζ).compAddMonoidHom
          (Algebra.trace (ZMod ell) F).toAddMonoidHom).mulShift ((j : ℕ) : F) := by
  refine AddChar.ext _ _ fun x => ?_
  rw [AddChar.compAddMonoidHom_apply, AddChar.mulShift_apply,
    AddChar.compAddMonoidHom_apply, AddChar.zmodChar_apply, AddChar.zmodChar_apply]
  simp only [LinearMap.toAddMonoidHom_coe]
  -- the two traces differ by the scalar `j`
  have hcast : ((j : ℕ) : F) = algebraMap (ZMod ell) F ((j : ℕ) : ZMod ell) := by
    rw [map_natCast]
  have htrace : Algebra.trace (ZMod ell) F (((j : ℕ) : F) * x)
      = ((j : ℕ) : ZMod ell) * Algebra.trace (ZMod ell) F x := by
    rw [hcast, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [htrace]
  set t : ZMod ell := Algebra.trace (ZMod ell) F x with ht
  -- reduce both sides to the additive character `zmodChar`, where scaling is a power
  have h1 : (ζ ^ j) ^ t.val = (ζ ^ t.val) ^ j := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have h2 : ((j : ℕ) : ZMod ell) * t = j • t := by rw [nsmul_eq_mul]
  have h3 : ζ ^ ((j • t : ZMod ell)).val = (ζ ^ t.val) ^ j := by
    have := AddChar.map_nsmul_eq_pow (AddChar.zmodChar ell hζ) j t
    rwa [AddChar.zmodChar_apply, AddChar.zmodChar_apply] at this
  rw [h1, h2, h3]

end Twist

section Galois

variable {ell : ℕ} [hp : Fact ell.Prime] {F A : Type*} [Field F] [Fintype F]
  [Algebra (ZMod ell) F] [CharP F ell] [CommRing A]

/-- **Galois 扭转恒等式。**  `σ` 固定特征值并把 `ζ` 送到 `ζ ^ j`（`ell ∤ j`），
则它把 Gauss 和乘上 `χ(j)⁻¹`。这里写成乘法形式，故不需要 `χ(j)` 可逆。 -/
theorem integralTraceGaussSum_galois_twist
    (χ : MulChar F A) {ζ : A} (hζ : ζ ^ ell = 1)
    (σ : A →+* A) (j : ℕ) (hj : ¬ ell ∣ j)
    (hχ : ∀ x : F, σ (χ x) = χ x) (hσζ : σ ζ = ζ ^ j) :
    χ ((j : ℕ) : F) * σ (integralTraceGaussSum χ hζ) = integralTraceGaussSum χ hζ := by
  classical
  have hjF : ((j : ℕ) : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F ell j]
    exact hj
  -- σ pushed through the sum gives the Gauss sum with base `ζ ^ j`
  have hpush : σ (integralTraceGaussSum χ hζ)
      = integralTraceGaussSum χ (show (ζ ^ j) ^ ell = 1 by
          rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]) := by
    simp only [integralTraceGaussSum, gaussSum, map_sum, map_mul, map_pow,
      AddChar.compAddMonoidHom_apply, AddChar.zmodChar_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hχ x, hσζ]
  rw [hpush]
  -- and that Gauss sum is the mulShift one
  have hshift : integralTraceGaussSum χ (show (ζ ^ j) ^ ell = 1 by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow])
      = gaussSum χ (((AddChar.zmodChar ell hζ).compAddMonoidHom
          (Algebra.trace (ZMod ell) F).toAddMonoidHom).mulShift ((j : ℕ) : F)) := by
    rw [integralTraceGaussSum, integralTraceAddChar_pow hζ j]
  rw [hshift]
  have := gaussSum_mulShift χ ((AddChar.zmodChar ell hζ).compAddMonoidHom
    (Algebra.trace (ZMod ell) F).toAddMonoidHom) (Units.mk0 ((j : ℕ) : F) hjF)
  simpa only [Units.val_mk0, integralTraceGaussSum] using this

/-- **`p` 次幂被固定。**  若 `χ ^ p = 1`，则扭转因子的 `p` 次幂是 1，于是 `σ` 固定 `g ^ p`。
这正是 `g ^ p` 从 `ℚ(ζ_p, ζ_ell)` 降到 `ℚ(ζ_p)` 的机制。 -/
theorem integralTraceGaussSum_pow_fixed
    (χ : MulChar F A) {ζ : A} (hζ : ζ ^ ell = 1)
    (σ : A →+* A) (j : ℕ) (hj : ¬ ell ∣ j) (P : ℕ)
    (hχP : ∀ x : F, x ≠ 0 → (χ x) ^ P = 1)
    (hχ : ∀ x : F, σ (χ x) = χ x) (hσζ : σ ζ = ζ ^ j) :
    σ ((integralTraceGaussSum χ hζ) ^ P) = (integralTraceGaussSum χ hζ) ^ P := by
  have hjF : ((j : ℕ) : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F ell j]
    exact hj
  have htwist := integralTraceGaussSum_galois_twist χ hζ σ j hj hχ hσζ
  have hpow : (χ ((j : ℕ) : F)) ^ P * (σ (integralTraceGaussSum χ hζ)) ^ P
      = (integralTraceGaussSum χ hζ) ^ P := by
    rw [← mul_pow, htwist]
  rw [map_pow]
  rwa [hχP _ hjF, one_mul] at hpow

end Galois

end Catalan.Stickelberger
