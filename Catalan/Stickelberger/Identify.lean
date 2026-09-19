import Catalan.Stickelberger.Equivariance
import Catalan.Stickelberger.Transfer
import Catalan.Stickelberger.DigitResidue
import Mathlib

/-! # Galois action on an order-dividing-`p` character

The final step in the valuation argument. A ring endomorphism that raises one
primitive `p`-th root of unity to the `b`-th power does the same to every `p`-th root of unity,
hence acts on a character whose values are `p`-th roots of unity by `χ ↦ χ ^ b`.

Also: the ℕ∞ cancellation that turns the ramification-scaled valuation equation into the value
of the multiplicity downstairs.
-/

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

/-- 在一个 `p` 次本原单位根上是 `b` 次幂的环同态，在所有 `p` 次单位根上都是 `b` 次幂。 -/
theorem ringHom_apply_eq_pow_of_pow_eq_one {A : Type*} [CommRing A] [IsDomain A]
    {p : ℕ} [NeZero p] {ζ : A} (hζ : IsPrimitiveRoot ζ p)
    (σ : A →+* A) {b : ℕ} (hσζ : σ ζ = ζ ^ b)
    {x : A} (hx : x ^ p = 1) : σ x = x ^ b := by
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [← hi, map_pow, hσζ, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **辨识。**  值为 `p` 次单位根的特征，在这样的环同态下正好被抬成 `b` 次幂。
这一步把特征 `χ` 换成 `χ ^ b`。 -/
theorem ringHomComp_eq_pow_of_pow_eq_one
    {F A : Type*} [Field F] [Fintype F] [CommRing A] [IsDomain A]
    {p : ℕ} [NeZero p] {ζ : A} (hζ : IsPrimitiveRoot ζ p)
    (χ : MulChar F A) (hχp : ∀ u : Fˣ, (χ (u : F)) ^ p = 1)
    (σ : A →+* A) {b : ℕ} (hσζ : σ ζ = ζ ^ b) :
    χ.ringHomComp σ = χ ^ b := by
  ext u
  rw [MulChar.ringHomComp_apply, MulChar.pow_apply_coe]
  exact ringHom_apply_eq_pow_of_pow_eq_one hζ σ hσζ (hχp u)

/-- ℕ∞ 中消去一个非零自然数因子：这把「分歧指数放大后的赋值方程」解成下层的重数。 -/
theorem enat_eq_natCast_of_natCast_mul_eq {e k : ℕ} (he : e ≠ 0) {x : ℕ∞}
    (h : (e : ℕ∞) * x = ((e * k : ℕ) : ℕ∞)) : x = (k : ℕ∞) := by
  induction x using ENat.recTopCoe with
  | top =>
      rw [ENat.mul_top (by exact_mod_cast he)] at h
      exact absurd h.symm (ENat.natCast_ne_top (e * k))
  | coe n =>
      rw [← Nat.cast_mul] at h
      have hnat : e * n = e * k := by exact_mod_cast h
      rw [Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) hnat]


/-- **赋值公式的算术核心。** 上层的重数是 `p · s_ell(d·b)`（数字和恒等式取 `p` 次幂后的形状），
分歧指数是 `ell − 1`，则下层的重数恰是分解群轨道和 `∑_{i<f} (b·ell^i mod p)`。

指数恒等式由引理 `mul_digitSum_eq_mul_sum_mod`
取 `m := p`，再配 `emultiplicity_map_eq_ramificationIdx_mul` 与 ℕ∞ 的消去。 -/
theorem emultiplicity_eq_orbit_sum
    {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] (q : Ideal A) (P : Ideal B) [q.IsMaximal] [P.IsMaximal] [P.LiesOver q]
    (hmap : Ideal.map (algebraMap A B) q ≠ ⊥)
    (ell p f d b : ℕ) (hell : 1 < ell) (hp : 1 < p) (hf : 0 < f)
    (hdm : d * p = ell ^ f - 1) (hb : b < p)
    (hram : P.ramificationIdx A = ell - 1)
    (γ : A) (hγ : Ideal.span {γ} ≠ ⊥)
    (hup : emultiplicity P (Ideal.map (algebraMap A B) (Ideal.span {γ}))
        = ((p * (ell.digits (d * b)).sum : ℕ) : ℕ∞)) :
    emultiplicity q (Ideal.span {γ})
      = ((∑ i ∈ Finset.range f, (b * ell ^ i) % p : ℕ) : ℕ∞) := by
  -- the ramification scaling
  have hscale := emultiplicity_map_eq_ramificationIdx_mul q P hmap (Ideal.span {γ}) hγ
  rw [hup, hram] at hscale
  -- the digit identity, already proved in the main library
  have hdigit := mul_digitSum_eq_mul_sum_mod ell f p d b hell hf hp hdm hb
  rw [hdigit] at hscale
  -- cancel the ramification index
  exact enat_eq_natCast_of_natCast_mul_eq (by omega) hscale.symm

end Catalan.Stickelberger
