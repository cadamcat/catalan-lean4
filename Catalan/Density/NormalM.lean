module

public import Catalan.Density.BaseFields

/-!
# `Catalan.Density.NormalM`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

local instance instNormalMAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega :=
  AlgebraicClosure.isAlgebraic ℚ

local instance instAlgebraicFOmega (p : ℕ) : Algebra.IsAlgebraic (F p) Omega :=
  Algebra.IsAlgebraic.tower_top (K := ℚ) (F p)

local instance instAlgClosureFOmega (p : ℕ) : IsAlgClosure (F p) Omega :=
  ⟨inferInstance, inferInstance⟩

lemma isCyclotomicExtension_Bsub (p q : ℕ) (hq : 0 < q) :
    IsCyclotomicExtension {q} (F p) (Bsub p q) := by
  let instNeZeroQ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  exact (primitiveRoot_spec q hq).intermediateField_adjoin_isCyclotomicExtension (F p)

lemma isGalois_Bsub (p q : ℕ) (hq : 0 < q) :
    IsGalois (F p) (Bsub p q) := by
  let instCyclotomicB : IsCyclotomicExtension {q} (F p) (Bsub p q) :=
    isCyclotomicExtension_Bsub p q hq
  exact IsCyclotomicExtension.isGalois {q} (F p) (Bsub p q)

lemma isGalois_Msub (p q : ℕ) (hq : 0 < q) :
    IsGalois (F p) (Msub p q) := by
  let instGaloisB : IsGalois (F p) (Bsub p q) := isGalois_Bsub p q hq
  let instNormalRadicals :
      Normal (F p) (IntermediateField.adjoin (F p) (unitRadicals p q)) := by
    rw [IntermediateField.normal_iff_forall_map_le]
    intro σ
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨a, ⟨u, hu⟩, rfl⟩
    apply IntermediateField.subset_adjoin
    refine ⟨u, ?_⟩
    rw [← map_pow, hu, σ.commutes]
  let instNormalM : Normal (F p) (Msub p q) := by
    unfold Msub
    infer_instance
  exact isGalois_iff.mpr ⟨inferInstance, instNormalM⟩

end Catalan.A3

