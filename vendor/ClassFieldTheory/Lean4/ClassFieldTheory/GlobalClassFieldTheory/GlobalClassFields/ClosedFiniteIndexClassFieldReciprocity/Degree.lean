import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldOriginalField
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue

set_option autoImplicit false

/-!
# Degree of a closed finite-index class field

This leaf derives the degree of the selected class field from its exact
idèle-class norm range.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The degree of the selected class field over the original number
field is the index of its defining idèle-class subgroup. -/
theorem closedFiniteIndexClassField_finrank_eq_index
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Module.finrank K
        (closedFiniteIndexClassField
          (K := K) H hclosed) =
      H.index := by
  calc
    Module.finrank K
        (closedFiniteIndexClassField
          (K := K) H hclosed) =
        (_root_.ideleClassNorm K
          (closedFiniteIndexClassField
            (K := K) H hclosed)).range.index :=
      (ideleClassNorm_index_eq_finrank_abelian K
        (closedFiniteIndexClassField
          (K := K) H hclosed)).symm
    _ = H.index :=
      congrArg Subgroup.index
        (closedFiniteIndexClassField_ideleClassNorm_range
          (K := K) H hclosed)

end GlobalClassFields
end GlobalClassFieldTheory
