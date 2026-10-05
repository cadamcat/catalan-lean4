module

public import Catalan.Thaine.MixedNormBase
public import Catalan.Thaine.NormalizedNorm

/-!
# `Catalan.Thaine.AuxiliaryNormOne`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma auxiliary_normalized_unit_norm_one
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p])) (a : (ZMod p)ˣ)
    (eta : (𝓞 (A3.Bsub p ell))ˣ)
    (heta : algebraMap (A3.Bsub p ell) (mixedExtension p ell)
        ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) =
      normalizedPair p a (mixedPRoot p ell) (mixedEllRoot p ell)) :
    Algebra.norm (A3.F p) ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) = 1 := by
  have actualNormCyclotomic : IsCyclotomicExtension {ell}
      (mixedPrimeField p ell) (mixedExtension p ell) :=
    mixedExtension_overPrime_isCyclotomic p ell hp2 hpe
  have actualNormFinite : FiniteDimensional (mixedPrimeField p ell) (mixedExtension p ell) :=
    IsCyclotomicExtension.finiteDimensional {ell} (mixedPrimeField p ell) (mixedExtension p ell)
  have hzE : IsPrimitiveRoot (mixedPRoot p ell) p := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact A3.primitiveRoot_spec p (Fact.out : p.Prime).pos
  have hz : IsPrimitiveRoot (mixedPrimeGenerator p ell) p := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact hzE
  have hwB : IsPrimitiveRoot (auxiliaryRoot p ell) ell := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos
  have hw : IsPrimitiveRoot (mixedEllRoot p ell) ell :=
    hwB.map_of_injective (algebraMap (A3.Bsub p ell) (mixedExtension p ell)).injective
  apply (algebraMap (A3.F p) (mixedPrimeField p ell)).injective
  rw [map_one, ← mixedPrime_norm_compat p ell hp2 hpe, heta]
  exact normalizedPair_norm_one (mixedPrimeField p ell) (mixedExtension p ell) p ell
    (mixedExtension_overPrime_finrank p ell hp2 hpe) hp2 hell
    (mixedPrimeGenerator p ell) hz a (mixedEllRoot p ell) hw

lemma exists_auxiliary_norm_one_unit
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (hell : (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p])) (a : (ZMod p)ˣ) :
    ∃ eta : (𝓞 (A3.Bsub p ell))ˣ,
      algebraMap (A3.Bsub p ell) (mixedExtension p ell)
          ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) =
        normalizedPair p a (mixedPRoot p ell) (mixedEllRoot p ell) ∧
      Algebra.norm (A3.F p) ((eta : 𝓞 (A3.Bsub p ell)) : A3.Bsub p ell) = 1 := by
  obtain ⟨eta, heta⟩ := exists_auxiliary_normalized_unit p ell hp2 hpe a
  exact ⟨eta, heta, auxiliary_normalized_unit_norm_one p ell hp2 hpe hell a eta heta⟩

end Catalan.Thaine
