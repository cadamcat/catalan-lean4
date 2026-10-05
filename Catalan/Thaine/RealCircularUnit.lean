module

public import Catalan.Thaine.CircularValueUnit
public import Catalan.Thaine.NormalizedPair

/-!
# `Catalan.Thaine.RealCircularUnit`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

private lemma realCircular_eq_or_inv_of_trace_eq
    {K : Type*} [Field K] (x y : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x + x⁻¹ = y + y⁻¹) : x = y ∨ x = y⁻¹ := by
  have hfactor : (x - y) * (x - y⁻¹) = 0 := by
    calc
      _ = x * (x + x⁻¹ - (y + y⁻¹)) := by field_simp; ring
      _ = 0 := by rw [h, sub_self, mul_zero]
  exact (mul_eq_zero.mp hfactor).imp sub_eq_zero.mp sub_eq_zero.mp

lemma exists_real_circular_unit
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : (ZMod p)ˣ) :
    ∃ c : (𝓞 (A3.F p))ˣ,
      algebraMap (A3.F p) A3.Omega ((c : 𝓞 (A3.F p)) : A3.F p) =
        normalizedCircularValue p a (A3.primitiveRoot p) := by
  have hp : p.Prime := Fact.out
  have realCircularGaloisB : IsGalois (A3.F p) (A3.Bsub p p) :=
    A3.isGalois_Bsub p p hp.pos
  have hz : IsPrimitiveRoot (auxiliaryRoot p p) p := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact A3.primitiveRoot_spec p hp.pos
  have hz0 : auxiliaryRoot p p ≠ 0 := hz.ne_zero hp.ne_zero
  obtain ⟨u, hu⟩ := exists_normalized_circular_unit (A3.Bsub p p) p (auxiliaryRoot p p) hz a
  have hfixed : ∀ sigma : A3.Bsub p p ≃ₐ[A3.F p] A3.Bsub p p,
      sigma ((u : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) =
        ((u : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) := by
    intro sigma
    let t : A3.F p :=
      ⟨A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹,
        IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    have ht : algebraMap (A3.F p) (A3.Bsub p p) t =
        auxiliaryRoot p p + (auxiliaryRoot p p)⁻¹ := by
      apply Subtype.ext
      rfl
    have htrace : sigma (auxiliaryRoot p p) + (sigma (auxiliaryRoot p p))⁻¹ =
        auxiliaryRoot p p + (auxiliaryRoot p p)⁻¹ := by
      calc
        _ = sigma (auxiliaryRoot p p + (auxiliaryRoot p p)⁻¹) := by rw [map_add, map_inv₀]
        _ = _ := by rw [← ht, sigma.commutes]
    have hmap : sigma (normalizedCircularValue p a (auxiliaryRoot p p)) =
        normalizedCircularValue p a (sigma (auxiliaryRoot p p)) := by
      simp only [normalizedCircularValue, normalizedEpsilon, map_div₀, map_mul,
        map_sub, map_pow, map_one]
    rw [hu, hmap]
    rcases realCircular_eq_or_inv_of_trace_eq (sigma (auxiliaryRoot p p)) (auxiliaryRoot p p)
        ((map_ne_zero sigma).mpr hz0) hz0 htrace with hsigma | hsigma
    · rw [hsigma]
    · rw [hsigma, normalizedCircularValue_inverse_root p hp2 a (auxiliaryRoot p p) hz]
  obtain ⟨x, hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := A3.F p)
    (((u : 𝓞 (A3.Bsub p p)) : A3.Bsub p p))).mpr hfixed
  obtain ⟨c, hc, _⟩ := exists_integral_unit_of_field_image
    (A3.F p) (A3.Bsub p p) u x hx
  refine ⟨c, ?_⟩
  rw [hc]
  calc
    algebraMap (A3.F p) A3.Omega x =
        algebraMap (A3.Bsub p p) A3.Omega (algebraMap (A3.F p) (A3.Bsub p p) x) :=
      (IsScalarTower.algebraMap_apply (A3.F p) (A3.Bsub p p) A3.Omega x).symm
    _ = algebraMap (A3.Bsub p p) A3.Omega
        (normalizedCircularValue p a (auxiliaryRoot p p)) := by rw [hx, hu]
    _ = normalizedCircularValue p a (A3.primitiveRoot p) := by
      simp only [normalizedCircularValue, normalizedEpsilon, map_div₀, map_mul,
        map_sub, map_pow, map_one]
      rfl

end Catalan.Thaine
