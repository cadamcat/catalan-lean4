import Catalan.Stickelberger.CharacterDefs

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.MinusIndependence
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma coeffCast_mem_theta_span (T : R p K) (hT : T ∈ minusGeneratorSpan p K) :
    coeffCast p K T ∈ Submodule.span ℂ (Set.range (thetaVector p K)) := by
  change T ∈ Submodule.span ℤ
    (Set.range (fun i : Fin ((p - 1) / 2) => θminus p K (i.val + 1))) at hT
  refine Submodule.span_induction (p := fun T _ =>
    coeffCast p K T ∈ Submodule.span ℂ (Set.range (thetaVector p K)))
    ?_ ?_ ?_ ?_ hT
  · intro T hT
    obtain ⟨i, rfl⟩ := hT
    exact Submodule.subset_span (Set.mem_range_self i)
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro T U hT hU hT' hU'
    simpa only [map_add] using (Submodule.add_mem _ hT' hU')
  · intro n T hT hT'
    rw [map_zsmul]
    have hs := Submodule.smul_mem (Submodule.span ℂ (Set.range (thetaVector p K)))
      (n : ℂ) hT'
    simpa only [Int.cast_smul_eq_zsmul] using hs

lemma complexPTheta_mul_halfVector_mem_span (i : Fin ((p - 1) / 2)) :
    complexPTheta p K * halfVector p K i ∈
      Submodule.span ℂ (Set.range (thetaVector p K)) := by
  have hpθ : pθ p K ∈ stickSpan p K :=
    Submodule.subset_span (Or.inr rfl)
  have hsingle := stickSpan_mul_single p K (pθ p K) hpθ
    ((σ p K (halfUnit p i))⁻¹)
  have hminus : minusLinearMap p K
      (pθ p K * MonoidAlgebra.single ((σ p K (halfUnit p i))⁻¹) 1) ∈
      minusGeneratorSpan p K := by
    rw [← theta_minus_spans p K]
    exact Submodule.mem_map.mpr ⟨pθ p K *
      MonoidAlgebra.single ((σ p K (halfUnit p i))⁻¹) 1, hsingle, rfl⟩
  have hcast := coeffCast_mem_theta_span p K
    (minusLinearMap p K (pθ p K *
      MonoidAlgebra.single ((σ p K (halfUnit p i))⁻¹) 1)) hminus
  rw [show complexPTheta p K * halfVector p K i =
      coeffCast p K (minusLinearMap p K
        (pθ p K * MonoidAlgebra.single ((σ p K (halfUnit p i))⁻¹) 1)) by
    simp only [complexPTheta, halfVector, complexMinus, coeffCast_single,
      map_mul, minusLinearMap, LinearMap.mulRight_apply]
    norm_num
    rw [mul_assoc]]
  exact hcast

end Catalan.MinusIndependence
