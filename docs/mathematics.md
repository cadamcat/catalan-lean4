# Statement and proof guide

[JSP-000035](https://github.com/TheJustinSunPrize/awards/blob/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/problems/catalog-0001-0100.md#JSP-000035) asks whether 8 and 9 are the only consecutive positive integers that are both proper perfect powers. That catalog version provides a natural-language statement, not a maintainer-approved Lean declaration.

## Direct problem statement

[`Catalan.JSP.statement`](../Catalan/JSP.lean) proves both existence and unrestricted uniqueness:

```lean
(IsProperPerfectPower 8 ∧ IsProperPerfectPower 9) ∧
  ∀ n : ℕ, 0 < n → IsProperPerfectPower n →
    IsProperPerfectPower (n + 1) → n = 8
```

Here `IsProperPerfectPower n` means `∃ m k : ℕ, 2 ≤ m ∧ 2 ≤ k ∧ m ^ k = n`. The uniqueness statement has no numerical cutoff. Its proof applies `Catalan.catalans_conjecture` to the two power representations. This is a submitter-proposed formal statement for review against the original problem.

## Equation classifications

[Final/Assembly.lean](../Catalan/Final/Assembly.lean) proves the natural-number classification, the positive-base integer classification, and the impossibility of a solution with two odd prime exponents. [Final/Signed.lean](../Catalan/Final/Signed.lean) extends the classification to nonzero integer bases and arbitrary natural exponents at least 2. The negative square base is retained: `(-3)^2 - 2^3 = 1`.

The proof develops Cassels' divisibility results, the required height and counting estimates, Stickelberger annihilation, unit-module and class-field-theoretic arguments, and the Runge contradiction. The classical exponent-2 cases and reduction to prime exponents complete the classification. Definitions and intermediate results are exposed by [Interface.lean](../Catalan/Interface.lean).

The compatibility theorem `q_lt_three_sq` is a downstream consequence of odd-prime impossibility. It is not used as an independent numerical bound in the proof.

## Attribution

Preda Mihăilescu proved the mathematical theorem. This project is a Lean formalization, with mathematical references and third-party source acknowledgments listed in [THIRD_PARTY.md](../THIRD_PARTY.md).
