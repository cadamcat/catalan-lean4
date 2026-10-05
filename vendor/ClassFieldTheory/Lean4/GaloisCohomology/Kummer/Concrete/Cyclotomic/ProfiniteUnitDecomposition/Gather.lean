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

public import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteFree


@[expose] public section

set_option autoImplicit false

/-!
# Compiled free-coordinate gathering stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation
open LocalFieldTheory.Padic

/-- Reassemble the family of local additive coordinates into `ℤ̂`. -/
noncomputable def gatherFree :
    ((p : Nat.Primes) → Multiplicative ℤ_[p.1]) ≃ₜ*
      Multiplicative ZHat :=
  (continuousPiMultiplicative
      (fun p : Nat.Primes => ℤ_[p.1])).symm.trans
    (continuousMultiplicativeEquivOfAddEquiv
      zHatContinuousAddEquivPrimeProduct).symm

end KummerTheory.ProfiniteUnitDecomposition.Internal
