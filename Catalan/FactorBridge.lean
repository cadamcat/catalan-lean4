import Catalan.IdealAction.Composition
import Catalan.Cyclotomic.Basic
import Mathlib

set_option autoImplicit false

noncomputable section
namespace Catalan
open NumberField
open scoped BigOperators nonZeroDivisors Pointwise

/-- `pθ` 的理想幂展开成共轭理想幂之积。 -/
theorem ipow_pθ_eq_prod (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (J : FracIdealUnit K) :
    ipow p K J (pθ p K)
      = ∏ a : (ZMod p)ˣ, (idealAct K (σ p K a)⁻¹ J) ^ (((a : ZMod p).val : ℕ) : ℤ) := by
  simpa only [pθ, ipow_single] using
    (ipow_sum p K (Finset.univ : Finset (ZMod p)ˣ) J
      (fun a => MonoidAlgebra.single (σ p K a)⁻¹
        (((a : ZMod p).val : ℕ) : ℤ)))

/-- 整理想的有限幂积搬到分式理想单位群。 -/
theorem idealUnit_eq_prod_pow {K : Type*} [Field K] [NumberField K]
    {iota : Type*} (s : Finset iota) (Q : iota → Ideal (𝓞 K)) (e : iota → ℕ)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hIeq : I = ∏ i ∈ s, Q i ^ e i)
    (J : iota → FracIdealUnit K)
    (hJ : ∀ i ∈ s, ((J i : FracIdeal K)) = ((Q i : Ideal (𝓞 K)) : FracIdeal K)) :
    idealUnit K I hI = ∏ i ∈ s, (J i) ^ e i := by
  apply Units.ext
  rw [coe_idealUnit, Units.coe_prod]
  simp only [Units.val_pow_eq_pow_val]
  rw [hIeq]
  change (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) (∏ i ∈ s, Q i ^ e i) =
    ∏ i ∈ s, (J i : FracIdeal K) ^ e i
  rw [map_prod]
  simp only [map_pow]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun A : FracIdeal K => A ^ e i) (hJ i hi).symm

/-- 整元素的主理想就是 `principalIdeal`。 -/
theorem idealUnit_span_eq_principalIdeal {K : Type*} [Field K] [NumberField K]
    (γ : 𝓞 K) (u : Kˣ) (hu : (u : K) = algebraMap (𝓞 K) K γ)
    (hspan : Ideal.span {γ} ≠ ⊥) :
    idealUnit K (Ideal.span {γ}) hspan = principalIdeal K u := by
  apply Units.ext
  rw [coe_idealUnit, coe_toPrincipalIdeal,
    FractionalIdeal.coeIdeal_span_singleton, hu]

end Catalan
