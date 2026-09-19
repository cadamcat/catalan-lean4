import Catalan.FactorDescent
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField
open scoped BigOperators Pointwise

open scoped Classical in
theorem conjIdeal_fiber_sum_eq_orbit_sum
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span {(ell : ℤ)})]
    (hcop : ell.Coprime p) (b : (ZMod p)ˣ) :
    (∑ a ∈ Finset.univ.filter (fun a : (ZMod p)ˣ =>
      conjIdeal p K P a = conjIdeal p K P b), (a : ZMod p).val) =
      ∑ i ∈ Finset.range (orderOf (ell : ZMod p)),
        ((b : ZMod p).val * ell ^ i) % p := by
  classical
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime ell hcop
  have hu : orderOf u = orderOf (ell : ZMod p) := by
    rw [← orderOf_units, ZMod.coe_unitOfCoprime]
  have hfiber (a : (ZMod p)ˣ) :
      conjIdeal p K P a = conjIdeal p K P b ↔ a * b⁻¹ ∈ Subgroup.zpowers u := by
    rw [← IsCyclotomicExtension.Rat.galEquivZMod_stabilizer p K ell P hcop]
    rw [MulEquiv.mapSubgroup_apply]
    change _ ↔ a * b⁻¹ ∈ (MulAction.stabilizer (K ≃ₐ[ℚ] K) P).map
      (IsCyclotomicExtension.Rat.galEquivZMod p K).toMonoidHom
    rw [Subgroup.mem_map_equiv, MulAction.mem_stabilizer_iff]
    change conjIdeal p K P a = conjIdeal p K P b ↔ σ p K (a * b⁻¹) • P = P
    rw [conjIdeal, conjIdeal, ← ideal_pointwise_smul_eq_map,
      ← ideal_pointwise_smul_eq_map, inv_smul_eq_iff, ← mul_smul]
    change P = (σ p K a * (σ p K b)⁻¹) • P ↔ σ p K (a * b⁻¹) • P = P
    have hinv : σ p K (b⁻¹) = (σ p K b)⁻¹ := by
      exact (IsCyclotomicExtension.Rat.galEquivZMod p K).symm.map_inv b
    rw [σ_mul, hinv]
    exact eq_comm
  symm
  refine Finset.sum_bij (fun i _ => b * u ^ i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfiber]
    simp [mul_comm, mul_left_comm]
  · intro i hi j hj hij
    apply pow_injOn_Iio_orderOf (x := u)
    · simpa only [Set.mem_Iio, hu] using Finset.mem_range.mp hi
    · simpa only [Set.mem_Iio, hu] using Finset.mem_range.mp hj
    · exact mul_left_cancel hij
  · intro a ha
    have ha' := (hfiber a).mp (Finset.mem_filter.mp ha).2
    rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at ha'
    obtain ⟨i, hi, hai⟩ := ha'
    refine ⟨i, ?_, ?_⟩
    · simpa only [hu] using hi
    · rw [hai]
      simp
  · intro i hi
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
      ← Nat.cast_pow, ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod_mod, u]

end Catalan

