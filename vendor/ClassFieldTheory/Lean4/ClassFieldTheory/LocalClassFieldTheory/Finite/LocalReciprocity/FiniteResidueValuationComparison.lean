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

public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence


@[expose] public section

set_option autoImplicit false

namespace LocalClassFieldTheory

open ValuationTheory RamificationTheory

/-!
# Finite-separable comparison of restricted valuation rings

The valuation on an algebraic ambient field can be restricted to a finite
intermediate field.  Over a complete discrete valuation field this
restriction is the unique extension valuation ring, so it agrees with any
other extension valuation ring on the finite field.  This is the
valuation-ring comparison used in the finite local reciprocity construction before comparing residue
degrees.
-/

noncomputable section

universe u v w

open DiscreteValuationField

/-- Over a complete discrete valuation field, restricting an ambient
extension valuation ring to a finite separable intermediate field gives the
same valuation ring as any independently constructed extension valuation on
that intermediate field. -/
theorem ValuationSubring.restrictIntermediateField_eq_of_finite_separable
    {K : Type u} {Omega : Type v} [Field K] [Field Omega] [Algebra K Omega]
    (base : CompleteDVF K)
    (A : ValuationSubring Omega) [base.valuation.HasExtension A.valuation]
    (E : IntermediateField K Omega) [FiniteDimensional K E]
    [Algebra.IsSeparable K E]
    (C : ValuationSubring E) [base.valuation.HasExtension C.valuation] :
    A.restrictIntermediateField E = C := by
  let B := A.restrictIntermediateField E
  let : base.valuation.HasExtension B.valuation :=
    RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension
      base.valuation A E
  obtain ⟨target, hExt, _hIntegralClosure, _hFundamental⟩ :=
    DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_fundamental_identity
      (K := K) (L := E) base
  let : base.valuation.HasExtension target.valuation := hExt
  have hB : target.valuation.valuationSubring = B :=
    DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      base target B
  have hC : target.valuation.valuationSubring = C :=
    DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      base target C
  exact hB.symm.trans hC

end
end LocalClassFieldTheory
