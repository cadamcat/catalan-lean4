module

public import Catalan.Stickelberger.CharacterDefs

/-!
# `Catalan.Stickelberger.CharacterHalfBasis`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.MinusIndependence
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

private lemma halfUnit_val (i : Fin ((p - 1) / 2)) :
    (halfUnit p i : ZMod p).val = i.val + 1 := by
  simp only [halfUnit, ZMod.coe_unitOfCoprime]
  apply ZMod.val_natCast_of_lt
  have := i.isLt
  omega

private lemma halfUnit_injective : Function.Injective (halfUnit p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun a : (ZMod p)ˣ => (a : ZMod p).val) h
  simpa only [halfUnit_val, Nat.add_left_inj] using hv

private lemma halfUnit_ne_neg (i j : Fin ((p - 1) / 2)) :
    halfUnit p i ≠ -halfUnit p j := by
  have instHalfNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro h
  have hv := congrArg (fun a : (ZMod p)ˣ => (a : ZMod p).val) h
  simp only [Units.val_neg, ZMod.neg_val, Units.ne_zero, if_false, halfUnit_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  omega

lemma halfVector_coeff (i j : Fin ((p - 1) / 2)) :
    (halfVector p K i).coeff ((σ p K (halfUnit p j))⁻¹) = if i = j then 1 else 0 := by
  classical
  have hiota : (ι p K)⁻¹ = ι p K := by
    dsimp [ι, σ]
    rw [← map_inv]
    simp
  have hnegIndex : (σ p K (-halfUnit p i))⁻¹ =
      (σ p K (halfUnit p i))⁻¹ * ι p K := by
    rw [show -halfUnit p i = (-1) * halfUnit p i by simp, σ_mul, mul_inv_rev]
    exact congrArg ((σ p K (halfUnit p i))⁻¹ * ·) hiota
  have hneg : (σ p K (halfUnit p i))⁻¹ * ι p K ≠
      (σ p K (halfUnit p j))⁻¹ := by
    rw [← hnegIndex]
    intro h
    have hu := (σ_bijective p K).injective (inv_inj.mp h)
    exact halfUnit_ne_neg p j i hu.symm
  have heq : (σ p K (halfUnit p i))⁻¹ = (σ p K (halfUnit p j))⁻¹ ↔ i = j := by
    constructor
    · intro h
      exact halfUnit_injective p ((σ_bijective p K).injective (inv_inj.mp h))
    · rintro rfl
      rfl
  simp only [halfVector, complexMinus, map_sub, coeffCast_single, Int.cast_one,
    mul_sub, MonoidAlgebra.single_mul_single, mul_one,
    MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, hneg, if_false, sub_zero, heq]

lemma halfVector_linearIndependent :
    LinearIndependent ℂ (halfVector p K) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he := congrArg (fun T : ComplexRing p K =>
    T.coeff ((σ p K (halfUnit p i))⁻¹)) hc
  simpa [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, halfVector_coeff,
    Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul] using he

lemma halfVector_mem_minusRange (i : Fin ((p - 1) / 2)) :
    halfVector p K i ∈ minusRange p K := by
  exact ⟨MonoidAlgebra.single (σ p K (halfUnit p i))⁻¹ 1, rfl⟩


end Catalan.MinusIndependence
