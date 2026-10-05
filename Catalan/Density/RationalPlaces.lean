module

public import Catalan.Density.Definitions
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational

/-!
# `Catalan.Density.RationalPlaces`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3

lemma rational_natGenerator_below_mem
    (L : Type) [Field L] [NumberField L]
    (W : HeightOneSpectrum (𝓞 L)) :
    (Rat.HeightOneSpectrum.natGenerator (finitePlaceBelow (K := ℚ) W) : 𝓞 L) ∈ W.asIdeal := by
  let v₀ := finitePlaceBelow (K := ℚ) W
  let n := Rat.HeightOneSpectrum.natGenerator v₀
  have hmap := Rat.HeightOneSpectrum.span_natGenerator v₀
  have hzOQ : (n : 𝓞 ℚ) ∈ v₀.asIdeal := by
    have hcomp :
        (v₀.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).comap
            (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) = v₀.asIdeal :=
      Ideal.comap_map_of_bijective
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective
        (I := v₀.asIdeal)
    rw [← hcomp]
    change Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) (n : 𝓞 ℚ) ∈
      v₀.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
    rw [← hmap]
    simpa only [map_natCast] using Ideal.mem_span_singleton_self (n : ℤ)
  have hzunder : (n : 𝓞 ℚ) ∈ W.asIdeal.under (𝓞 ℚ) := by
    simpa only [v₀, finitePlaceBelow_asIdeal] using hzOQ
  have hzL : algebraMap (𝓞 ℚ) (𝓞 L) (n : 𝓞 ℚ) ∈ W.asIdeal :=
    (Ideal.mem_under (𝓞 ℚ) W.asIdeal).mp hzunder
  simpa only [v₀, n, map_natCast] using hzL

lemma finite_places_above_natSet
    (K : Type) [Field K] [NumberField K] (S : Finset ℕ) :
    {v : HeightOneSpectrum (𝓞 K) |
      Rat.HeightOneSpectrum.natGenerator (finitePlaceBelow (K := ℚ) v) ∈ S}.Finite := by
  let B : Set (HeightOneSpectrum (𝓞 ℚ)) :=
    {v | Rat.HeightOneSpectrum.natGenerator v ∈ (S : Set ℕ)}
  have hB : B.Finite := by
    apply (S.finite_toSet.preimage (f := Rat.HeightOneSpectrum.natGenerator))
    intro v hv w hw h
    exact RayClass.rational_natGenerator_injective h
  have hpre := Set.Finite.preimage_finitePlaceBelow
    (K := ℚ) (L := K) hB
  simpa only [B, Set.mem_ofPred_eq, Finset.mem_coe] using hpre

end Catalan.A3
