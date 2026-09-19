import Catalan.Thaine.NormalizedPair

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma normalized_epsilon_residue
    (K k : Type*) [Field K] [NumberField K] [Field k]
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] [CharP k ell] (hpe : p ≠ ell)
    (f : 𝓞 K →+* k) (z w : K) (hz : IsPrimitiveRoot z p) (hw : IsPrimitiveRoot w ell)
    (a : (ZMod p)ˣ) (u c : (𝓞 K)ˣ)
    (hu : ((u : 𝓞 K) : K) = normalizedEpsilon p a z w)
    (hc : ((c : 𝓞 K) : K) = normalizedCircularValue p a z) :
    f (u : 𝓞 K) = f (c : 𝓞 K) := by
  let hpow : ℕ := normalizedHalf p a
  let aval : ℕ := (a : ZMod p).val
  have hzw : z - w ≠ 0 := by
    intro h
    apply hpe
    have hzw' : z = w := sub_eq_zero.mp h
    calc
      p = orderOf z := (IsPrimitiveRoot.iff_orderOf.mp hz).symm
      _ = orderOf w := by rw [hzw']
      _ = ell := IsPrimitiveRoot.iff_orderOf.mp hw
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (hz.ne_one (Fact.out : p.Prime).one_lt)
  have huf : ((u : 𝓞 K) : K) * (z - w) =
      z ^ hpow * (z ^ aval - w) := by
    have hu' : ((u : 𝓞 K) : K) =
        z ^ hpow * (z ^ aval - w) / (z - w) := by
      simpa [normalizedEpsilon, hpow, aval] using hu
    exact (eq_div_iff hzw).mp hu'
  have hcf : ((c : 𝓞 K) : K) * (z - 1) =
      z ^ hpow * (z ^ aval - 1) := by
    have hc' : ((c : 𝓞 K) : K) =
        z ^ hpow * (z ^ aval - 1) / (z - 1) := by
      simpa [normalizedCircularValue, normalizedEpsilon, hpow, aval] using hc
    exact (eq_div_iff hz1).mp hc'
  have hzi : IsPrimitiveRoot hz.toInteger p := hz.toInteger_isPrimitiveRoot
  have hwi : IsPrimitiveRoot hw.toInteger ell := hw.toInteger_isPrimitiveRoot
  have hzbar : f hz.toInteger ≠ 1 := by
    intro hred
    have hsum : ∑ i ∈ Finset.range p, hz.toInteger ^ i = 0 := by
      have h := geom_sum_mul hz.toInteger p
      rw [hzi.pow_eq_one, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right
        (sub_ne_zero.mpr (hzi.ne_one (Fact.out : p.Prime).one_lt))
    have h := congrArg f hsum
    apply CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : p.Prime) hpe.symm
    simpa only [map_sum, map_pow, hred, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
  have hwbar : f hw.toInteger = 1 := by
    have hpowbar : f hw.toInteger ^ ell = 1 := by
      have h := congrArg f hwi.pow_eq_one
      simpa only [map_pow, map_one] using h
    have hzero : (f hw.toInteger - 1) ^ ell = 0 := by
      rw [sub_pow_char, hpowbar]
      simp
    exact sub_eq_zero.mp ((pow_eq_zero_iff (Fact.out : ell.Prime).ne_zero).mp hzero)
  have hufO : (u : 𝓞 K) * (hz.toInteger - hw.toInteger) =
      hz.toInteger ^ hpow * (hz.toInteger ^ aval - hw.toInteger) := by
    apply RingOfIntegers.coe_injective
    change ((u : 𝓞 K) : K) * (z - w) = z ^ hpow * (z ^ aval - w)
    exact huf
  have hcfO : (c : 𝓞 K) * (hz.toInteger - 1) =
      hz.toInteger ^ hpow * (hz.toInteger ^ aval - 1) := by
    apply RingOfIntegers.coe_injective
    change ((c : 𝓞 K) : K) * (z - 1) = z ^ hpow * (z ^ aval - 1)
    exact hcf
  have hufk := congrArg f hufO
  have hcfk := congrArg f hcfO
  have hufk' : f (u : 𝓞 K) * (f hz.toInteger - f hw.toInteger) =
      f hz.toInteger ^ hpow * (f hz.toInteger ^ aval - f hw.toInteger) := by
    simpa only [map_mul, map_sub, map_pow] using hufk
  have hcfk' : f (c : 𝓞 K) * (f hz.toInteger - 1) =
      f hz.toInteger ^ hpow * (f hz.toInteger ^ aval - 1) := by
    simpa only [map_mul, map_sub, map_pow, map_one] using hcfk
  have hufk'' : f (u : 𝓞 K) * (f hz.toInteger - 1) =
      f hz.toInteger ^ hpow * (f hz.toInteger ^ aval - 1) := by
    simpa only [hwbar] using hufk'
  have hEq : f (u : 𝓞 K) * (f hz.toInteger - 1) =
      f (c : 𝓞 K) * (f hz.toInteger - 1) := by
    calc
      _ = f hz.toInteger ^ hpow * (f hz.toInteger ^ aval - 1) := hufk''
      _ = _ := hcfk'.symm
  exact (mul_right_cancel₀ (sub_ne_zero.mpr hzbar)) hEq

lemma normalized_pair_residue
    (K k : Type*) [Field K] [NumberField K] [Field k]
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] [CharP k ell] (hpe : p ≠ ell)
    (f : 𝓞 K →+* k) (z w : K) (hz : IsPrimitiveRoot z p) (hw : IsPrimitiveRoot w ell)
    (a : (ZMod p)ˣ) (u c : (𝓞 K)ˣ)
    (hu : ((u : 𝓞 K) : K) = normalizedPair p a z w)
    (hc : ((c : 𝓞 K) : K) = normalizedCircularValue p a z) :
    f (u : 𝓞 K) = f (c : 𝓞 K) ^ 2 := by
  obtain ⟨u₁, hu₁⟩ := exists_normalized_epsilon_unit K p ell hpe z w hz hw a
  obtain ⟨u₂, hu₂⟩ := exists_normalized_epsilon_unit K p ell hpe z w⁻¹ hz hw.inv a
  have hc' : ((c : 𝓞 K) : K) = normalizedEpsilon p a z 1 := by
    simpa only [normalizedCircularValue] using hc
  have h₁ := normalized_epsilon_residue K k p ell hpe f z w hz hw a u₁ c hu₁ hc'
  have h₂ := normalized_epsilon_residue K k p ell hpe f z w⁻¹ hz hw.inv a u₂ c hu₂ hc'
  have huu : u = u₁ * u₂ := by
    apply Units.ext
    apply RingOfIntegers.coe_injective
    change ((u : 𝓞 K) : K) = ((u₁ * u₂ : (𝓞 K)ˣ) : 𝓞 K)
    change ((u : 𝓞 K) : K) = ((u₁ : 𝓞 K) : K) * ((u₂ : 𝓞 K) : K)
    rw [hu, hu₁, hu₂]
    rfl
  rw [huu]
  change f ((u₁ : 𝓞 K) * (u₂ : 𝓞 K)) = f (c : 𝓞 K) ^ 2
  rw [map_mul, h₁, h₂]
  ring

end Catalan.Thaine
