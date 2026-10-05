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

public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Field norms on unit groups

This file provides the common algebraic norm map on unit groups.  It is
independent of any valuation or local-field structure, so valued-field and
discrete-valuation APIs can share the same definition.
-/


/-!
# `ValuedFieldTheory.LocalField.NormUnits`

Part of the vendored ClassFieldTheory source bundle.
-/

@[expose] public section

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u v w

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- The algebra norm, restricted to unit groups. -/
def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- The underlying field element of a unit norm is the algebra norm. -/
@[simp]
theorem normUnits_apply_coe (x : Lˣ) :
    ((normUnits K L x : Kˣ) : K) = Algebra.norm K (x : L) :=
  rfl

/-- Field norms on unit groups are transitive in a tower. -/
theorem normUnits_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [Module.Free M L] (x : Lˣ) :
    normUnits K M (normUnits M L x) = normUnits K L x := by
  apply Units.ext
  exact Algebra.norm_norm

end

end LocalFieldTheory
