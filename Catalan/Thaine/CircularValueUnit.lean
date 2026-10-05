module

public import Catalan.Thaine.Normalization

/-!
# `Catalan.Thaine.CircularValueUnit`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma exists_normalized_circular_unit
    (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (z : K) (hz : IsPrimitiveRoot z p) (a : (ZMod p)ˣ) :
    ∃ c : (𝓞 K)ˣ, ((c : 𝓞 K) : K) = normalizedCircularValue p a z := by
  have hp : p.Prime := Fact.out
  have circularValueNeZeroP : NeZero p := ⟨hp.ne_zero⟩
  have hroot : IsUnit hz.toInteger := hz.toInteger_isPrimitiveRoot.isUnit hp.ne_zero
  have hsum : IsUnit ((Finset.range (a : ZMod p).val).sum
      fun i => hz.toInteger ^ i) :=
    hz.toInteger_isPrimitiveRoot.geom_sum_isUnit hp.two_le (ZMod.val_coe_unit_coprime a)
  obtain ⟨c, hc⟩ := (hroot.pow (normalizedHalf p a)).mul hsum
  refine ⟨c, ?_⟩
  have hvalue : ((c : 𝓞 K) : K) =
      z ^ normalizedHalf p a * (Finset.range (a : ZMod p).val).sum (fun i => z ^ i) := by
    rw [hc]
    simp only [map_mul, map_pow, map_sum]
    rfl
  rw [hvalue]
  unfold normalizedCircularValue normalizedEpsilon
  apply (eq_div_iff (sub_ne_zero.mpr (hz.ne_one hp.one_lt))).mpr
  rw [mul_assoc, geom_sum_mul]

end Catalan.Thaine
