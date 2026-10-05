module

public import Catalan.Thaine.Normalization
public import Catalan.Thaine.EpsilonInversion
public import Catalan.Thaine.MixedDescent
public import Catalan.Thaine.IntegralUnitDescent

/-!
# `Catalan.Thaine.NormalizedPair`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

def normalizedPair {K : Type*} [Field K]
    (p : ℕ) (a : (ZMod p)ˣ) (z w : K) : K :=
  normalizedEpsilon p a z w * normalizedEpsilon p a z w⁻¹

lemma normalizedEpsilon_map {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (p : ℕ) (a : (ZMod p)ˣ) (z w : K) :
    f (normalizedEpsilon p a z w) = normalizedEpsilon p a (f z) (f w) := by
  simp only [normalizedEpsilon, map_div₀, map_mul, map_sub, map_pow]

lemma normalizedPair_map {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (p : ℕ) (a : (ZMod p)ˣ) (z w : K) :
    f (normalizedPair p a z w) = normalizedPair p a (f z) (f w) := by
  simp only [normalizedPair, map_mul, normalizedEpsilon_map, map_inv₀]

lemma normalizedPair_inverse_root {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : (ZMod p)ˣ)
    (z w : K) (hz : IsPrimitiveRoot z p) (hw : w ≠ 0) :
    normalizedPair p a z⁻¹ w = normalizedPair p a z w := by
  simpa only [normalizedPair, normalizedEpsilon, zpow_natCast] using
    epsilon_pair_inverse_root z w (hz.ne_zero (Fact.out : p.Prime).ne_zero) hw
      (a : ZMod p).val (normalizedHalf p a : ℤ) (normalizedHalf_root p hp2 a z hz)

lemma normalizedCircularValue_inverse_root {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : (ZMod p)ˣ)
    (z : K) (hz : IsPrimitiveRoot z p) :
    normalizedCircularValue p a z⁻¹ = normalizedCircularValue p a z := by
  simpa only [normalizedCircularValue, normalizedEpsilon, zpow_natCast, inv_one] using
    epsilon_inverse_root z 1 (hz.ne_zero (Fact.out : p.Prime).ne_zero) one_ne_zero
      (a : ZMod p).val (normalizedHalf p a : ℤ) (normalizedHalf_root p hp2 a z hz)

lemma normalizedPair_fixed {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : (ZMod p)ˣ)
    (z w : K) (hz : IsPrimitiveRoot z p) (hw : w ≠ 0)
    (sigma : K →+* K) (hzsigma : sigma z = z⁻¹) (hwsigma : sigma w = w) :
    sigma (normalizedPair p a z w) = normalizedPair p a z w := by
  rw [normalizedPair_map, hzsigma, hwsigma, normalizedPair_inverse_root p hp2 a z w hz hw]

lemma exists_normalized_pair_unit
    (K : Type*) [Field K] [NumberField K]
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (z w : K) (hz : IsPrimitiveRoot z p) (hw : IsPrimitiveRoot w ell)
    (a : (ZMod p)ˣ) :
    ∃ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) = normalizedPair p a z w := by
  obtain ⟨u, hu⟩ := exists_normalized_epsilon_unit K p ell hpe z w hz hw a
  obtain ⟨v, hv⟩ := exists_normalized_epsilon_unit K p ell hpe z w⁻¹ hz hw.inv a
  refine ⟨u * v, ?_⟩
  change ((u : 𝓞 K) : K) * ((v : 𝓞 K) : K) = _
  rw [hu, hv]
  rfl

lemma exists_auxiliary_normalized_unit
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (a : (ZMod p)ˣ) :
    ∃ eta : (𝓞 (A3.Bsub p ell))ˣ,
      algebraMap (A3.Bsub p ell) (mixedExtension p ell)
          ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) =
        normalizedPair p a (mixedPRoot p ell) (mixedEllRoot p ell) := by
  have hp : p.Prime := Fact.out
  have hell : ell.Prime := Fact.out
  have hz : IsPrimitiveRoot (mixedPRoot p ell) p := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact A3.primitiveRoot_spec p hp.pos
  have hwb : IsPrimitiveRoot (auxiliaryRoot p ell) ell := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact A3.primitiveRoot_spec ell hell.pos
  have hw : IsPrimitiveRoot (mixedEllRoot p ell) ell :=
    hwb.map_of_injective (algebraMap (A3.Bsub p ell) (mixedExtension p ell)).injective
  obtain ⟨u, hu⟩ := exists_normalized_pair_unit (mixedExtension p ell) p ell hpe
    (mixedPRoot p ell) (mixedEllRoot p ell) hz hw a
  obtain ⟨tau, htau, _, hfixed⟩ := exists_mixed_involution p ell hp2 hpe
  have hwtau : tau (mixedEllRoot p ell) = mixedEllRoot p ell :=
    tau.commutes (auxiliaryRoot p ell)
  have hufixed : tau ((u : 𝓞 (mixedExtension p ell)) : mixedExtension p ell) =
      ((u : 𝓞 (mixedExtension p ell)) : mixedExtension p ell) := by
    rw [hu]
    exact normalizedPair_fixed p hp2 a (mixedPRoot p ell) (mixedEllRoot p ell)
      hz (hw.ne_zero hell.ne_zero) tau.toRingEquiv.toRingHom htau hwtau
  obtain ⟨x, hx⟩ := (hfixed _).mp hufixed
  obtain ⟨eta, heta, _⟩ := exists_integral_unit_of_field_image
    (A3.Bsub p ell) (mixedExtension p ell) u x hx
  exact ⟨eta, (congrArg (algebraMap (A3.Bsub p ell) (mixedExtension p ell)) heta).trans
    (hx.trans hu)⟩

end Catalan.Thaine
