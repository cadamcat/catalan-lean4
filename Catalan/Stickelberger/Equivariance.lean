import Catalan.Stickelberger.GaussGalois
import Mathlib

/-! # Galois and multiplicity equivariance

* Gauss sums are natural in the coefficient ring when the root of unity is fixed:
  `σ (g χ) = g (χ ∘ σ)`.  This is the Galois action that turns `χ` into `χ ^ b`.
* Multiplicity is invariant under a multiplicative equivalence, hence under transporting both
  the prime and the ideal along a ring automorphism.  This is what relates the multiplicity at a
  conjugate prime `σ_b⁻¹ P` to the multiplicity at `P` of the conjugated element.
-/

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

/-- 固定 `ζ` 的环同态把 Gauss 和送到「特征复合 `σ`」的 Gauss 和。 -/
theorem integralTraceGaussSum_ringHom_of_fixed_root
    {ell : ℕ} [Fact ell.Prime] {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] (χ : MulChar F A) {ζ : A} (hζ : ζ ^ ell = 1)
    (σ : A →+* A) (hσζ : σ ζ = ζ) :
    σ (integralTraceGaussSum χ hζ) = integralTraceGaussSum (χ.ringHomComp σ) hζ := by
  simp only [integralTraceGaussSum, gaussSum, map_sum, map_mul, map_pow,
    AddChar.compAddMonoidHom_apply, AddChar.zmodChar_apply, MulChar.ringHomComp_apply]
  exact Finset.sum_congr rfl fun x _ => by rw [hσζ]

/-- 重数在乘法同构下不变。 -/
theorem emultiplicity_mulEquiv {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) (a b : M) :
    emultiplicity (e a) (e b) = emultiplicity a b := by
  refine ENat.eq_of_forall_natCast_le_iff fun k => ?_
  rw [← pow_dvd_iff_le_emultiplicity, ← pow_dvd_iff_le_emultiplicity, ← map_pow]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨e.symm c, by simpa using congrArg e.symm hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨e c, by rw [← map_mul, ← hc]⟩

/-- 环自同构在理想上诱导的乘法同构。 -/
def idealMapMulEquiv {A : Type*} [CommRing A] (e : A ≃+* A) : Ideal A ≃* Ideal A where
  toFun I := Ideal.map (e : A →+* A) I
  invFun I := Ideal.map (e.symm : A →+* A) I
  left_inv I := by
    show Ideal.map (e.symm : A →+* A) (Ideal.map (e : A →+* A) I) = I
    rw [Ideal.map_map]
    simp
  right_inv I := by
    show Ideal.map (e : A →+* A) (Ideal.map (e.symm : A →+* A) I) = I
    rw [Ideal.map_map]
    simp
  map_mul' I J := Ideal.map_mul _ _ _

@[simp] lemma idealMapMulEquiv_apply {A : Type*} [CommRing A] (e : A ≃+* A) (I : Ideal A) :
    idealMapMulEquiv e I = Ideal.map (e : A →+* A) I := rfl

/-- **重数的 Galois 等变性。**  把素理想与理想同时沿环自同构搬运，重数不变。 -/
theorem emultiplicity_ideal_map {A : Type*} [CommRing A] (e : A ≃+* A) (Q I : Ideal A) :
    emultiplicity (Ideal.map (e : A →+* A) Q) (Ideal.map (e : A →+* A) I)
      = emultiplicity Q I := by
  simpa only [idealMapMulEquiv_apply] using emultiplicity_mulEquiv (idealMapMulEquiv e) Q I

/-- 主理想版本：搬运素理想等于反向搬运生成元。 -/
theorem emultiplicity_ideal_map_span {A : Type*} [CommRing A] (e : A ≃+* A) (Q : Ideal A) (x : A) :
    emultiplicity (Ideal.map (e : A →+* A) Q) (Ideal.span {e x}) = emultiplicity Q (Ideal.span {x}) := by
  rw [← emultiplicity_ideal_map e Q (Ideal.span {x}), Ideal.map_span]
  congr 2
  simp

end Catalan.Stickelberger
