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

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.UniformSpace.AbsoluteValue


/-!
# `ValuedFieldTheory.Valuation.AbsoluteValue.Extension`

Part of the vendored ClassFieldTheory source bundle.
-/

@[expose] public section

set_option autoImplicit false

/-!
# Extensions of absolute values

A reusable predicate for exact extension along an algebra map.
-/
namespace AbsoluteValue
/-- The target absolute value agrees with the base absolute value along the algebra map. -/
def Extends {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) : Prop :=
  ∀ x : K, w (algebraMap K L x) = v x

end AbsoluteValue
