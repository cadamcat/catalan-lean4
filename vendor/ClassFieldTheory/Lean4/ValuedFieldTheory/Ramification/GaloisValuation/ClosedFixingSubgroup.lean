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

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite


@[expose] public section

set_option autoImplicit false

/-!
# Closed fixing subgroups

This module packages the closed subgroup attached to an intermediate field in
the Krull topology.
-/

noncomputable section

namespace RamificationTheory

/-- The closed fixing subgroup attached to an intermediate field. -/
@[implicit_reducible]
noncomputable def closedFixingSubgroup
    (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) : ClosedSubgroup Gal(Ω/k) :=
  ⟨K.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed K⟩

end RamificationTheory
