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
# `GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Swap`

Part of the vendored ClassFieldTheory source bundle.
-/

@[expose] public section

set_option autoImplicit false

/-!
# Compiled final swap stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation

/-- Swap the collected free and finite coordinates. -/
noncomputable def freeFiniteSwap :
    CyclotomicFinitePart × Multiplicative ZHat ≃ₜ*
      Multiplicative ZHat × CyclotomicFinitePart :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivProdComm
    CyclotomicFinitePart (Multiplicative ZHat)

end KummerTheory.ProfiniteUnitDecomposition.Internal
