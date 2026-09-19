import Catalan.Cyclotomic.Elements

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Circular
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma exists_ratio_unit (a b : (ZMod p)ˣ) :
    ∃ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) =
      (1 - ζ p K ^ (a : ZMod p).val) / (1 - ζ p K ^ (b : ZMod p).val) := by
  let instRatioNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have ha : IsPrimitiveRoot (σ p K a (ζ p K)) p :=
    (ζ_spec p K).map_of_injective (σ p K a).injective
  have hb : IsPrimitiveRoot (σ p K b (ζ p K)) p :=
    (ζ_spec p K).map_of_injective (σ p K b).injective
  obtain ⟨u, hu⟩ :=
    IsCyclotomicExtension.Rat.associated_sub_one_of_isPrimitiveRoot p hb ha
  have hmul := congrArg (fun z : 𝓞 K => (z : K)) hu
  change (σ p K b (ζ p K) - 1) * ((u : 𝓞 K) : K) = σ p K a (ζ p K) - 1 at hmul
  rw [σ_apply_ζ, σ_apply_ζ] at hmul
  have hbne : ζ p K ^ (b : ZMod p).val ≠ 1 := by
    rw [← σ_apply_ζ]
    exact hb.ne_one (Fact.out : p.Prime).one_lt
  refine ⟨u, (eq_div_iff (sub_ne_zero.mpr hbne.symm)).mpr ?_⟩
  linear_combination -hmul

end Catalan.Circular

