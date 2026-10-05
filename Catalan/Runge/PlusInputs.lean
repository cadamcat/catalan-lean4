module

public import Catalan.CaseOne.PlusAugmentation
public import Catalan.Runge.Reduction

/-!
# `Catalan.Runge.PlusInputs`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.Runge
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance plusInputsGalComm : CommGroup (G p K) := UnitModule.cyclotomicGalCommGroup p K

lemma even_weight_of_mem_plusAugIdeal (q : ℕ) (Theta : R p K)
    (hTheta : reduceFull p K q Theta ∈ UnitModule.plusAugIdeal p K q) :
    (∀ g : G p K,
      (Theta.coeff (ι p K * g) : ZMod q) = (Theta.coeff g : ZMod q)) ∧
      (weight p K Theta : ZMod q) = 0 := by
  classical
  let U : MonoidAlgebra (ZMod q) (G p K) := reduceFull p K q Theta
  let t : MonoidAlgebra (ZMod q) (G p K) := MonoidAlgebra.single (ι p K) 1
  let N : MonoidAlgebra (ZMod q) (G p K) := UnitReduction.groupNorm (ZMod q) (G p K)
  have hU : U ∈ Ideal.span ({1 + t} : Set _) * (Ideal.span ({N} : Set _)).annihilator :=
    hTheta
  obtain ⟨B, hB, hBU⟩ := Ideal.mem_span_singleton_mul.mp hU
  let plusInputsGalFintype : Fintype (G p K) := Fintype.ofFinite _
  have ht : t ^ 2 = 1 := by
    dsimp only [t]
    rw [MonoidAlgebra.single_pow, UnitModule.iota_square, one_pow,
      ← MonoidAlgebra.one_def]
  have htU : t * U = U := by
    rw [← hBU, ← mul_assoc, mul_add, mul_one, ← pow_two, ht, add_comm]
  have hBN : B * N = 0 := by
    simpa only [smul_eq_mul] using (Submodule.mem_annihilator_span_singleton N B).mp hB
  have hUN : U * N = 0 := by
    rw [← hBU, mul_assoc, hBN, mul_zero]
  have hNcoeff (g : G p K) : N.coeff g = 1 := by
    simp [N, UnitReduction.groupNorm, MonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
  constructor
  · intro g
    have hc := congrArg
      (fun V : MonoidAlgebra (ZMod q) (G p K) => V.coeff (ι p K * g)) htU
    dsimp only [t] at hc
    simp only [MonoidAlgebra.coeff_single_mul_mul, one_mul] at hc
    simpa only [U, reduceFull, MonoidAlgebra.coeff_mapRingHom, Int.coe_castRingHom] using hc.symm
  · have hc := congrArg
      (fun V : MonoidAlgebra (ZMod q) (G p K) => V.coeff 1) hUN
    rw [MonoidAlgebra.coeff_mul_apply_left] at hc
    simp only [hNcoeff, mul_one, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    have hs : (∑ g : G p K, U.coeff g) = 0 := by
      exact (Finsupp.sum_fintype U.coeff (fun _ r => r) (fun _ => rfl)).symm.trans hc
    rw [weight_eq_sum, Int.cast_sum]
    simpa only [U, reduceFull, MonoidAlgebra.coeff_mapRingHom, Int.coe_castRingHom] using hs

end Catalan.Runge
