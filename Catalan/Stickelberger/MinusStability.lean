module

public import Catalan.Stickelberger.MinusDefs
public import Catalan.Stickelberger.Reduction

/-!
# `Catalan.Stickelberger.MinusStability`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma ΘS_mul_single (k : ℕ) (b : (ZMod p)ˣ) :
    ΘS p K k * MonoidAlgebra.single (σ p K b) 1 =
      ΘS p K ((b : ZMod p).val * k) - (k : ℤ) • ΘS p K (b : ZMod p).val
 := by
  classical
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro τ
  obtain ⟨a, rfl⟩ := ((Equiv.inv (G p K)).bijective.comp (σ_bijective p K)).surjective τ
  change (ΘS p K k * MonoidAlgebra.single (σ p K b) 1).coeff ((σ p K a)⁻¹) =
    (ΘS p K ((b : ZMod p).val * k) - (k : ℤ) • ΘS p K (b : ZMod p).val).coeff ((σ p K a)⁻¹)
  have hindex : (σ p K a)⁻¹ * (σ p K b)⁻¹ = (σ p K (b * a))⁻¹ := by
    rw [← mul_inv_rev, ← σ_mul]
  have hrem : ((b * a : (ZMod p)ˣ) : ZMod p).val =
      ((a : ZMod p).val * (b : ZMod p).val) % p := by
    rw [Units.val_mul, ZMod.val_mul, Nat.mul_comm]
  have hdiv : (a : ZMod p).val * ((b : ZMod p).val * k) / p =
      k * ((a : ZMod p).val * (b : ZMod p).val / p) +
        (((a : ZMod p).val * (b : ZMod p).val) % p) * k / p := by
    calc
      (a : ZMod p).val * ((b : ZMod p).val * k) / p =
          ((((a : ZMod p).val * (b : ZMod p).val) % p) * k +
            p * (((a : ZMod p).val * (b : ZMod p).val / p) * k)) / p := by
        congr 1
        calc
          (a : ZMod p).val * ((b : ZMod p).val * k) =
              ((a : ZMod p).val * (b : ZMod p).val) * k := by ring
          _ = ((((a : ZMod p).val * (b : ZMod p).val) % p) +
                p * (((a : ZMod p).val * (b : ZMod p).val) / p)) * k :=
            congrArg (fun t : ℕ => t * k)
              (Nat.mod_add_div ((a : ZMod p).val * (b : ZMod p).val) p).symm
          _ = _ := by ring
      _ = ((((a : ZMod p).val * (b : ZMod p).val) % p) * k) / p +
          ((a : ZMod p).val * (b : ZMod p).val / p) * k :=
        Nat.add_mul_div_left _ _ (Fact.out : p.Prime).pos
      _ = _ := by ac_rfl
  simp only [MonoidAlgebra.coeff_mul_single_apply, mul_one, hindex,
    MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.coeff_smul,
    Finsupp.smul_apply, smul_eq_mul, ΘS_coeff, hrem]
  have hz := congrArg (fun t : ℕ => (t : ℤ)) hdiv
  simp only [Nat.cast_add, Nat.cast_mul] at hz
  omega

lemma pθ_mul_single (b : (ZMod p)ˣ) :
    pθ p K * MonoidAlgebra.single (σ p K b) 1 =
      ((b : ZMod p).val : ℤ) • pθ p K - (p : ℤ) • ΘS p K (b : ZMod p).val
 := by
  calc
    pθ p K * MonoidAlgebra.single (σ p K b) 1 =
        ΘS p K p * MonoidAlgebra.single (σ p K b) 1 := by rw [ΘS_p]
    _ = ΘS p K ((b : ZMod p).val * p) - (p : ℤ) • ΘS p K (b : ZMod p).val :=
      ΘS_mul_single p K p b
    _ = _ := by
      rw [ΘS_mod_decomposition, Nat.mul_div_cancel _ (Fact.out : p.Prime).pos]
      simp only [Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod, ΘS_zero, add_zero]

lemma stickSpan_mul_single (T : R p K) (hT : T ∈ stickSpan p K) (τ : G p K) :
    T * MonoidAlgebra.single τ 1 ∈ stickSpan p K
 := by
  obtain ⟨b, rfl⟩ := (σ_bijective p K).surjective τ
  have hgen (k : ℕ) : ΘS p K k ∈ stickSpan p K :=
    Submodule.subset_span (Or.inl ⟨k, rfl⟩)
  have hpθ : pθ p K ∈ stickSpan p K :=
    Submodule.subset_span (Or.inr (Set.mem_singleton _))
  let U : Submodule ℤ (R p K) := (stickSpan p K).comap
    (LinearMap.mulRight ℤ (MonoidAlgebra.single (σ p K b) 1))
  have hle : stickSpan p K ≤ U := by
    apply Submodule.span_le.mpr
    intro A hA
    change A * MonoidAlgebra.single (σ p K b) 1 ∈ stickSpan p K
    rcases hA with ⟨k, rfl⟩ | hA
    · rw [ΘS_mul_single]
      exact (stickSpan p K).sub_mem (hgen _) ((stickSpan p K).smul_mem (k : ℤ) (hgen _))
    · have he : A = pθ p K := Set.mem_singleton_iff.mp hA
      rw [he, pθ_mul_single]
      exact (stickSpan p K).sub_mem
        ((stickSpan p K).smul_mem ((b : ZMod p).val : ℤ) hpθ)
        ((stickSpan p K).smul_mem (p : ℤ) (hgen _))
  exact hle hT

theorem θminus_mem (k : ℕ) : θminus p K k ∈ stickSpan p K
 := by
  have hgen (j : ℕ) : ΘS p K j ∈ stickSpan p K :=
    Submodule.subset_span (Or.inl ⟨j, rfl⟩)
  have hD : ΘS p K (k + 1) - ΘS p K k ∈ stickSpan p K :=
    (stickSpan p K).sub_mem (hgen _) (hgen _)
  rw [θminus, mul_sub]
  exact (stickSpan p K).sub_mem
    (stickSpan_mul_single p K _ hD 1) (stickSpan_mul_single p K _ hD (ι p K))

end Catalan
