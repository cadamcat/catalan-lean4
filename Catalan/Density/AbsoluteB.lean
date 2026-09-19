import Catalan.Density.NormalM
import Catalan.Density.FStructure

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma isGalois_Bsub_rat (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    IsGalois ℚ (Bsub p q) := by
  have instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  have instNeZeroQ : NeZero q := ⟨hq.ne'⟩
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp
  have instNormalF : Normal ℚ (Fsub p) := by
    change Normal ℚ (F p)
    exact instAbelianF.toIsGalois.to_normal
  let C : IntermediateField ℚ Omega := IntermediateField.adjoin ℚ {primitiveRoot q}
  have instCyclotomicC : IsCyclotomicExtension {q} ℚ C :=
    (primitiveRoot_spec q hq).intermediateField_adjoin_isCyclotomicExtension ℚ
  have instGaloisC : IsGalois ℚ C := IsCyclotomicExtension.isGalois {q} ℚ C
  have hB : (Bsub p q).restrictScalars ℚ = Fsub p ⊔ C :=
    IntermediateField.restrictScalars_adjoin_eq_sup ℚ (Fsub p) {primitiveRoot q}
  have instNormalB : Normal ℚ (Bsub p q) := by
    change Normal ℚ ((Bsub p q).restrictScalars ℚ)
    rw [hB]
    exact @IntermediateField.normal_sup ℚ Omega _ _ _ (Fsub p) C instNormalF instGaloisC.to_normal
  exact isGalois_iff.mpr ⟨inferInstance, instNormalB⟩

end Catalan.A3
