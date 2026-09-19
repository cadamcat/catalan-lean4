import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport

set_option autoImplicit false

/-!
# Continuous closed finite-index class-field reciprocity

The final equivalence composes finite global reciprocity with the generic
continuous transport induced by the exact norm-range equality.  Equality
elimination preserves the native quotient topology, so no discrete topology
instances are reconstructed here.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

/-- Canonical class-group commutativity supplies normality for the two quotients. -/
private theorem closedFiniteIndexTopologicalClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexTopologicalClassGroupIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

/-- Global reciprocity for the selected class field as a homeomorphic
multiplicative equivalence `Gal(L / K) ≃ₜ* C_K / H`. -/
noncomputable def
    closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Gal((closedFiniteIndexClassField
          (K := K) H hclosed) / K) ≃ₜ*
      IdeleClassGroup K ⧸ H :=
  (globalReciprocityContinuousMulEquiv K
    (closedFiniteIndexClassField
      (K := K) H hclosed)).trans
      (QuotientGroup.quotientContinuousMulEquivOfEq
        (closedFiniteIndexClassField_ideleClassNorm_range
          (K := K) H hclosed))

end GlobalClassFields
end GlobalClassFieldTheory
