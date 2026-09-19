import Catalan.Density.ClassGroupArtin

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma classGroupArtinOfEverywhereUnramified_idele
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (hunram : IsEverywhereUnramified K L) (a : IdeleGroup K) :
    classGroupArtinOfEverywhereUnramified K L hunram (IdeleGroup.idealClass a) =
      GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom K L a := by
  let instIdeleClassComm : IsMulCommutative (IdeleClassGroup K) :=
    ⟨⟨fun x y => mul_comm x y⟩⟩
  let instInfiniteUnramified : IsUnramifiedAtInfinitePlaces K L := hunram.infinitePlaces
  let E := GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup
    (K := K)
  have hclass : E.symm (IdeleGroup.idealClass a) =
      QuotientGroup.mk'
        (GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroup (K := K))
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) := by
    apply E.injective
    rw [E.apply_symm_apply]
    rfl
  dsimp only [classGroupArtinOfEverywhereUnramified,
    GlobalClassFieldTheory.GlobalClassFields.classGroupToIdeleClassNormQuotient,
    MonoidHom.comp_apply]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [hclass,
    GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk]
  change (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv K L).symm
    ((QuotientGroup.mk' (ideleClassNorm K L).range)
      ((QuotientGroup.mk' (IdeleGroup.principalSubgroup K)) a)) = _
  rw [GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk]
  exact DFunLike.congr_fun
    (GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_comp_ideleClassQuotient_eq_globalArtin
      K L) a

end Catalan.A3
