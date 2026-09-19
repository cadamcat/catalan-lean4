import Catalan.Thaine.PrimaryLocalization
import Catalan.IdealAction
import Catalan.Cyclotomic.GroupRing

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine
attribute [local instance] primaryLocalizationIsLocalization

lemma exists_primary_localized_upow
    (p q : ℕ) (K : Type*) [Field K] [NumberField K]
    (a : Kˣ) (s : 𝓞 K) (hs : (s : K) = (a : K))
    (hsmod : ∀ g : G p K, (q : 𝓞 K) ^ 2 ∣ integerAut K g s - 1)
    (Theta : R p K) :
    ∃ v : (primaryLocalization (𝓞 K) K q)ˣ,
      Units.map (algebraMap (primaryLocalization (𝓞 K) K q) K).toMonoidHom v = upow p K a Theta ∧
      Units.map (primaryLocalizationResidue (𝓞 K) K q).toMonoidHom v = 1 := by
  let L := primaryLocalization (𝓞 K) K q
  let j := Units.map (algebraMap L K).toMonoidHom
  let r := Units.map (primaryLocalizationResidue (𝓞 K) K q).toMonoidHom
  have hs0 : s ≠ 0 := by
    intro hzero
    apply a.ne_zero
    rw [← hs, hzero]
    rfl
  have hgen (g : G p K) : ∃ v : Lˣ, j v = actUnit p K g a ∧ r v = 1 := by
    have hg0 : integerAut K g s ≠ 0 := by
      intro hz
      apply hs0
      apply (integerAut K g).injective
      simpa only [map_zero] using hz
    have hgmod : Ideal.Quotient.mk (Ideal.span ({(q : 𝓞 K) ^ 2} : Set (𝓞 K)))
        (integerAut K g s) = 1 := by
      have heq := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (integerAut K g s) (1 : 𝓞 K)).mpr
        (Ideal.mem_span_singleton.mpr (hsmod g))
      simpa only [map_one] using heq
    have hgS : integerAut K g s ∈ primaryDenominators (𝓞 K) q := by
      constructor
      · change IsUnit (Ideal.Quotient.mk
          (Ideal.span ({(q : 𝓞 K) ^ 2} : Set (𝓞 K))) (integerAut K g s))
        rw [hgmod]
        exact isUnit_one
      · exact mem_nonZeroDivisors_iff_ne_zero.mpr hg0
    have hunit := IsLocalization.map_units L ⟨integerAut K g s, hgS⟩
    refine ⟨hunit.unit, ?_, ?_⟩
    · apply Units.ext
      change algebraMap L K (hunit.unit : L) = g (a : K)
      rw [hunit.unit_spec, ← IsScalarTower.algebraMap_apply (𝓞 K) L K]
      change g (s : K) = g (a : K)
      rw [hs]
    · apply Units.ext
      change primaryLocalizationResidue (𝓞 K) K q (hunit.unit : L) = 1
      rw [hunit.unit_spec, primaryLocalizationResidue_algebraMap, hgmod]
  change ∃ v : Lˣ, j v = upow p K a Theta ∧ r v = 1
  refine MonoidAlgebra.induction_linear Theta ?_ ?_ ?_
  · refine ⟨1, ?_, ?_⟩
    · rw [map_one, upow_zero]
    · exact map_one r
  · intro A B hA hB
    obtain ⟨vA, hAj, hAr⟩ := hA
    obtain ⟨vB, hBj, hBr⟩ := hB
    refine ⟨vA * vB, ?_, ?_⟩
    · rw [map_mul, hAj, hBj, upow_add]
    · rw [map_mul, hAr, hBr, one_mul]
  · intro g m
    obtain ⟨v, hvj, hvr⟩ := hgen g
    refine ⟨v ^ m, ?_, ?_⟩
    · rw [map_zpow, hvj, upow_single]
    · rw [map_zpow, hvr, one_zpow]

end Catalan.Thaine
