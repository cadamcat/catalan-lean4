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

public import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather


/-!
# `GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Decomposition`

Part of the vendored ClassFieldTheory source bundle.
-/

@[expose] public section

set_option autoImplicit false

/-!
# The profinite-unit product decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- Topological decomposition
`ℤ̂ˣ ≃ Multiplicative ℤ̂ × finite-product` used in the rational cyclotomic
calculation. -/
noncomputable def zHatUnitsDecomposition :
    ZHatˣ ≃ₜ* Multiplicative ZHat × CyclotomicFinitePart :=
  zHatUnitsContinuousMulEquivPrimeProduct.trans <|
    ProfiniteUnitDecomposition.Internal.localDecomposition.symm.trans <|
      ProfiniteUnitDecomposition.Internal.finiteFreeSplit.trans <|
        continuousMulEquivProdCongr
          ProfiniteUnitDecomposition.Internal.gatherFree
          (ContinuousMulEquiv.refl CyclotomicFinitePart)

end KummerTheory
