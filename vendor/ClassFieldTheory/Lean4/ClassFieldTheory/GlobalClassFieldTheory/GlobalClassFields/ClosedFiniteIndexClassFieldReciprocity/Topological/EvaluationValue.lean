/-
MODIFIED FROM UPSTREAM:
n-yamaguchi-0729/ClassFieldTheory commit 7713795234690681b4406ae198b07aa95e82716a.
Added Lean module-system visibility declarations and ported this file to Mathlib/Lean v4.35.0-rc3.
-/
module

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction


/-!
# `ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue`

Part of the vendored ClassFieldTheory source bundle.
-/

@[expose] public section

set_option autoImplicit false

/-!
# Named value of closed finite-index reciprocity

The expanded inverse norm-residue expression is kept behind one reducible
value provider.  Public evaluation statements can therefore mention the
selected class-field instance tower once while remaining definitionally
equivalent to the historical formula.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

/-- Canonical class-group commutativity supplies normality for norm-range transport. -/
private theorem closedFiniteIndexEvaluationValueClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexEvaluationValueClassGroupIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

/-- The quotient value prescribed by inverse global norm-residue reciprocity
for a Galois element of the selected closed finite-index class field. -/
noncomputable abbrev closedFiniteIndexClassFieldReciprocityValue
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (σ : Gal((closedFiniteIndexClassField
      (K := K) H hclosed) / K)) :
    IdeleClassGroup K ⧸ H :=
  QuotientGroup.quotientMulEquivOfEq
      (closedFiniteIndexClassField_ideleClassNorm_range
        (K := K) H hclosed)
    (Additive.toMul
      ((globalNormResidueEquiv K
          (closedFiniteIndexClassField
            (K := K) H hclosed)).symm
        (Additive.ofMul σ)))

end GlobalClassFields
end GlobalClassFieldTheory
