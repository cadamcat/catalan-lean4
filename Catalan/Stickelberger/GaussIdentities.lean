import Catalan.Stickelberger.LocalGauss

noncomputable section
open scoped BigOperators

namespace Catalan.Stickelberger

private lemma integralTraceAddChar_primitive {ell : ℕ} [Fact ell.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] {ζ : A} (hζ : IsPrimitiveRoot ζ ell) :
    ((AddChar.zmodChar ell hζ.pow_eq_one).compAddMonoidHom
      (Algebra.trace (ZMod ell) F).toAddMonoidHom).IsPrimitive := by
  letI : CharP F ell := (Algebra.charP_iff (ZMod ell) F ell).mp inferInstance
  have hchar : ringChar F = ell := ringChar.eq F ell
  subst ell
  apply AddChar.IsPrimitive.of_ne_one
  obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
  rw [one_mul] at ha
  apply AddChar.ne_one_iff.mpr
  refine ⟨a, fun hf => ha ?_⟩
  exact (AddChar.zmodChar_primitive_of_primitive_root (ringChar F) hζ).zmod_char_eq_one_iff
    (ringChar F) (Algebra.trace (ZMod (ringChar F)) F a) |>.mp hf

/-- The prime-field trace is Frobenius invariant. -/
lemma integralTraceGaussSum_trace_frobenius {ell : ℕ} [Fact ell.Prime]
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (x : F) :
    Algebra.trace (ZMod ell) F (x ^ ell) = Algebra.trace (ZMod ell) F x := by
  simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using
    (Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod ell) F) x)

/-- Raising to the residue characteristic is bijective on a finite field. -/
lemma integralTraceGaussSum_pow_bijective {ell : ℕ} [Fact ell.Prime]
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell] :
    Function.Bijective (fun x : F => x ^ ell) := by
  simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod ell) F).bijective

/-- 零指标：平凡乘性特征的 Gauss 和等于 −1。 -/
theorem integralTraceGaussSum_one {ell : ℕ} [Fact ell.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [IsDomain A] {ζ : A} (hζ : IsPrimitiveRoot ζ ell) :
    integralTraceGaussSum (1 : MulChar F A) hζ.pow_eq_one = -1 := by
  let ψ : AddChar F A :=
    (AddChar.zmodChar ell hζ.pow_eq_one).compAddMonoidHom
      (Algebra.trace (ZMod ell) F).toAddMonoidHom
  have hp : ψ.IsPrimitive := integralTraceAddChar_primitive hζ
  have hψ : ψ ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hp one_ne_zero
  change gaussSum (1 : MulChar F A) ψ = -1
  exact gaussSum_one_left hψ

/-- Frobenius 不变性：ell 次特征幂的 Gauss 和与原特征的相同。 -/
theorem integralTraceGaussSum_pow_char {ell : ℕ} [Fact ell.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    [CommRing A] (χ : MulChar F A) {ζ : A} (hζ : ζ ^ ell = 1) :
    integralTraceGaussSum (χ ^ ell) hζ = integralTraceGaussSum χ hζ := by
  classical
  let ψ : AddChar F A :=
    (AddChar.zmodChar ell hζ).compAddMonoidHom
      (Algebra.trace (ZMod ell) F).toAddMonoidHom
  have hχpow (x : F) : (χ ^ ell) x = χ (x ^ ell) := by
    rw [χ.pow_apply' (Fact.out : ell.Prime).ne_zero, ← map_pow]
  have hψpow (x : F) : ψ (x ^ ell) = ψ x := by
    change ζ ^ (Algebra.trace (ZMod ell) F (x ^ ell)).val =
      ζ ^ (Algebra.trace (ZMod ell) F x).val
    rw [integralTraceGaussSum_trace_frobenius]
  have hbij : Function.Bijective (fun x : F => x ^ ell) :=
    integralTraceGaussSum_pow_bijective
  change (∑ x : F, (χ ^ ell) x * ψ x) = ∑ x : F, χ x * ψ x
  calc
    (∑ x : F, (χ ^ ell) x * ψ x) =
        ∑ x : F, χ (x ^ ell) * ψ (x ^ ell) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hχpow x, ← hψpow x]
    _ = ∑ x : F, χ x * ψ x :=
      Fintype.sum_bijective _ hbij _ _ (fun x => rfl)

/-- 互补配对：非平凡特征与其逆的 Gauss 和之积为 χ(−1)·#F。 -/
theorem integralTraceGaussSum_mul_inv {ell : ℕ} [Fact ell.Prime]
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [IsDomain A] (χ : MulChar F A) (hχ : χ ≠ 1)
    {ζ : A} (hζ : IsPrimitiveRoot ζ ell) :
    integralTraceGaussSum χ hζ.pow_eq_one * integralTraceGaussSum χ⁻¹ hζ.pow_eq_one
      = χ (-1) * Fintype.card F := by
  let ψ : AddChar F A :=
    (AddChar.zmodChar ell hζ.pow_eq_one).compAddMonoidHom
      (Algebra.trace (ZMod ell) F).toAddMonoidHom
  have hp : ψ.IsPrimitive := integralTraceAddChar_primitive hζ
  have hcore : gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * Fintype.card F := by
    rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹ ψ, mul_left_comm,
      gaussSum_mul_gaussSum_eq_card hχ hp, MulChar.inv_apply', inv_neg_one]
  simpa only [integralTraceGaussSum, ψ] using hcore

/-- Gauss 和的 `p` 次幂与互补者的 `p` 次幂之积是 `ell ^ (f * p)`。
这给出理想分解所需的范数条件：只有 `ell` 上方的素理想能整除。
-/
theorem integralTraceGaussSum_pow_mul_inv_pow
    {ell : ℕ} [Fact ell.Prime] {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [IsDomain A] (χ : MulChar F A) (hχ : χ ≠ 1)
    {ζ : A} (hζ : IsPrimitiveRoot ζ ell)
    (p f : ℕ) (hcard : Fintype.card F = ell ^ f) (hχp : (χ (-1)) ^ p = 1) :
    (integralTraceGaussSum χ hζ.pow_eq_one) ^ p
        * (integralTraceGaussSum χ⁻¹ hζ.pow_eq_one) ^ p
      = (ell : A) ^ (f * p) := by
  have hcardpow : ((Fintype.card F : ℕ) : A) = (ell : A) ^ f := by
    rw [hcard, Nat.cast_pow]
  calc
    (integralTraceGaussSum χ hζ.pow_eq_one) ^ p
        * (integralTraceGaussSum χ⁻¹ hζ.pow_eq_one) ^ p =
        (integralTraceGaussSum χ hζ.pow_eq_one *
          integralTraceGaussSum χ⁻¹ hζ.pow_eq_one) ^ p := by
            rw [mul_pow]
    _ = (χ (-1) * Fintype.card F) ^ p := by
      rw [integralTraceGaussSum_mul_inv χ hχ hζ]
    _ = (χ (-1)) ^ p * ((Fintype.card F : ℕ) : A) ^ p := by
      rw [mul_pow]
    _ = ((Fintype.card F : ℕ) : A) ^ p := by
      rw [hχp, one_mul]
    _ = ((ell : A) ^ f) ^ p := by
      rw [hcardpow]
    _ = (ell : A) ^ (f * p) := by
      rw [pow_mul]

end Catalan.Stickelberger
