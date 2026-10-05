module

public import Catalan.Stickelberger.GaussGalois
public import Catalan.Stickelberger.Descent
public import Mathlib

/-! # Root-of-unity facts for Galois descent

* `exists_algebraMap_eq_of_pow_eq_one`: if the base field already contains a primitive `p`-th
  root of unity, every `p`-th root of unity upstairs comes from the base.  This is what makes
  the order-`p` character values fixed by `Gal(L/K)`.
* `exists_pow_eq_of_isPrimitiveRoot`: a ring endomorphism that is injective sends a primitive
  `ell`-th root of unity to `ζ ^ j` with `ell ∤ j`.  This supplies the hypothesis `hσζ` of
  `integralTraceGaussSum_galois_twist`.
-/

/-!
# `Catalan.Stickelberger.RootDescent`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

/-- 若基域已含 `p` 次本原单位根，则上层的每个 `p` 次单位根都来自基域。 -/
theorem exists_algebraMap_eq_of_pow_eq_one
    (p : ℕ) [NeZero p] (K L : Type*) [Field K] [Field L] [Algebra K L]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (x : L) (hx : x ^ p = 1) :
    ∃ y : K, algebraMap K L y = x := by
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) p :=
    hζ.map_of_injective (algebraMap K L).injective
  obtain ⟨i, -, hi⟩ := hζL.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

/-- 单射环同态把 `ell` 次本原单位根送到 `ζ ^ j`，且 `ell ∤ j`。 -/
theorem exists_pow_eq_of_isPrimitiveRoot
    {ell : ℕ} (hell : 1 < ell) {A : Type*} [CommRing A] [IsDomain A]
    {ζ : A} (hζ : IsPrimitiveRoot ζ ell)
    (σ : A →+* A) (hσ : Function.Injective σ) :
    ∃ j : ℕ, ¬ ell ∣ j ∧ σ ζ = ζ ^ j := by
  have : NeZero ell := ⟨by omega⟩
  have hpow : (σ ζ) ^ ell = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨j, hjlt, hj⟩ := hζ.eq_pow_of_pow_eq_one hpow
  refine ⟨j, ?_, hj.symm⟩
  intro hdvd
  -- `ell ∣ j` together with `j < ell` forces `j = 0`, i.e. `σ ζ = 1 = σ 1`
  have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hjlt
  rw [hj0, pow_zero] at hj
  have h1 : σ ζ = σ 1 := by rw [← hj, map_one]
  exact hζ.ne_one hell (hσ h1)


section Combine

open NumberField

variable (p ell : ℕ) [hp : Fact ell.Prime]
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsScalarTower ℚ K L]

omit [IsScalarTower ℚ K L] in
/-- **Gauss 和的 `p` 次幂被 `Gal(L/K)` 的每个元素固定。**

两个假设都是在调用处兑现的：`hχp` 说特征的值是 `p` 次单位根（阶 `p` 特征自动满足），
`hχK` 说这些值来自 `𝓞 K`（由 `exists_algebraMap_eq_of_pow_eq_one` 给出，因为 `K ⊇ μ_p`）。 -/
theorem gaussSum_pow_fixed_of_algEquiv
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (χ : MulChar F (𝓞 L)) {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ ell) (hell : 1 < ell)
    (hχp : ∀ x : F, x ≠ 0 → (χ x) ^ p = 1)
    (hχK : ∀ x : F, ∃ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 L) y = χ x)
    (σ : L ≃ₐ[K] L) :
    (galRestrict (𝓞 K) K L (𝓞 L) σ) ((integralTraceGaussSum χ hζ.pow_eq_one) ^ p)
      = (integralTraceGaussSum χ hζ.pow_eq_one) ^ p := by
  set s := galRestrict (𝓞 K) K L (𝓞 L) σ with hs
  have hinj : Function.Injective (s : 𝓞 L → 𝓞 L) := s.injective
  -- `s` sends the root of unity to a power with exponent prime to `ell`
  obtain ⟨j, hj, hsz⟩ :=
    exists_pow_eq_of_isPrimitiveRoot hell hζ (s : 𝓞 L →+* 𝓞 L) hinj
  -- `s` fixes the character values, because they come from `𝓞 K`
  have hfix : ∀ x : F, (s : 𝓞 L →+* 𝓞 L) (χ x) = χ x := by
    intro x
    obtain ⟨y, hy⟩ := hχK x
    rw [← hy]
    exact s.commutes y
  exact integralTraceGaussSum_pow_fixed χ hζ.pow_eq_one (s : 𝓞 L →+* 𝓞 L) j hj p hχp hfix hsz

/-- **Gauss 和的 Galois 下降。** 阶 `p` 特征的 Gauss 和，其 `p` 次幂来自 `𝓞 K`。

这把 `integralTraceGaussSum_pow_fixed`（每个 `σ` 固定 `g ^ p`）与 Galois 下降
（被全体固定 ⟹ 来自 `𝓞 K`）接了起来。两个假设在调用处兑现：`hχp` 对阶 `p` 特征自动成立，
`hχK` 由 `exists_algebraMap_eq_of_pow_eq_one` 给出（因为 `K` 含 `μ_p`）。 -/
theorem exists_ringOfIntegers_gaussSum_pow [IsGalois K L]
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (χ : MulChar F (𝓞 L)) {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ ell) (hell : 1 < ell)
    (hχp : ∀ x : F, x ≠ 0 → (χ x) ^ p = 1)
    (hχK : ∀ x : F, ∃ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 L) y = χ x) :
    ∃ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 L) y
      = (integralTraceGaussSum χ hζ.pow_eq_one) ^ p := by
  refine exists_ringOfIntegers_of_forall_fixed K L _ fun σ => ?_
  have hfix := gaussSum_pow_fixed_of_algEquiv p ell K L χ hζ hell hχp hχK σ
  have := congrArg (algebraMap (𝓞 L) L) hfix
  rwa [algebraMap_galRestrict_apply] at this

omit [NumberField K] [NumberField L] [IsScalarTower ℚ K L] in
/-- `𝓞 L` 中的 `p` 次单位根来自 `𝓞 K`（只要 `K` 含 `p` 次本原单位根）。
这正是上一条定理 `hχK` 假设的兑现方式。 -/
theorem exists_ringOfIntegers_of_pow_eq_one [NeZero p]
    {ζK : K} (hζK : IsPrimitiveRoot ζK p)
    (x : 𝓞 L) (hx : x ^ p = 1) :
    ∃ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 L) y = x := by
  have hxL : (x : L) ^ p = 1 := by
    rw [← map_pow, hx, map_one]
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_of_pow_eq_one p K L hζK (x : L) hxL
  have hy_int : IsIntegral ℤ y :=
    isIntegral_of_algebraMap_isIntegral K L y (by rw [hy]; exact RingOfIntegers.isIntegral_coe x)
  refine ⟨⟨y, hy_int⟩, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap K L y = (x : L)
  exact hy

end Combine

end Catalan.Stickelberger
