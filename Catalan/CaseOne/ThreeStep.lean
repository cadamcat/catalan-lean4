module

public import Catalan.CaseOne.Filtration

/-!
# `Catalan.CaseOne.ThreeStep`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitReduction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsSemisimpleModule R M]

lemma three_step_annihilator_pairwise
    (hcyc : ∃ v : M, Function.Surjective (LinearMap.toSpanSingleton R M v))
    (P W : Submodule R M) (hPW : P ≤ W) :
    (Module.annihilator R (M ⧸ W) ⊔ Module.annihilator R (W ⧸ P.comap W.subtype) = ⊤) ∧
    (Module.annihilator R (M ⧸ W) ⊔ Module.annihilator R P = ⊤) ∧
    (Module.annihilator R (W ⧸ P.comap W.subtype) ⊔ Module.annihilator R P = ⊤) := by
  have hWcyc := submodule_cyclic_of_semisimple hcyc W
  have hPann : Module.annihilator R (P.comap W.subtype) = Module.annihilator R P :=
    (Submodule.comapSubtypeEquivOfLe hPW).annihilator_eq
  have hinner := annihilator_eq_mul_quotient_of_cyclic_semisimple hWcyc (P.comap W.subtype)
  rw [hPann] at hinner
  have houter := annihilator_quotient_sup_of_cyclic_semisimple hcyc W
  rw [hinner] at houter
  refine ⟨?_, ?_, ?_⟩
  · exact top_unique (houter.symm.trans_le (sup_le_sup_left Ideal.mul_le_left _))
  · exact top_unique (houter.symm.trans_le (sup_le_sup_left Ideal.mul_le_right _))
  · simpa only [hPann] using
      annihilator_quotient_sup_of_cyclic_semisimple hWcyc (P.comap W.subtype)

lemma three_step_annihilator_product
    (hcyc : ∃ v : M, Function.Surjective (LinearMap.toSpanSingleton R M v))
    (P W : Submodule R M) (hPW : P ≤ W) :
    Module.annihilator R M =
      Module.annihilator R (M ⧸ W) * Module.annihilator R (W ⧸ P.comap W.subtype) *
        Module.annihilator R P := by
  have hWcyc := submodule_cyclic_of_semisimple hcyc W
  have hPann : Module.annihilator R (P.comap W.subtype) = Module.annihilator R P :=
    (Submodule.comapSubtypeEquivOfLe hPW).annihilator_eq
  rw [annihilator_eq_mul_quotient_of_cyclic_semisimple hcyc W,
    annihilator_eq_mul_quotient_of_cyclic_semisimple hWcyc (P.comap W.subtype),
    hPann, mul_assoc]

end Catalan.UnitReduction
