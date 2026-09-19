import Catalan.Mihailescu.Ideal

open scoped BigOperators ComplexConjugate
open NumberField
noncomputable section
namespace Catalan.A1e

section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The minus operator `(1-iota)T`; Bilu, Proposition 3.1.1. -/
def minusPart (T : R p K) : R p K :=
  (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (ι p K) 1) * T

/-- The single test exponent `(1-iota)Theta_2`; Bilu, p. 6.
The inverses in the frozen definition of `ThetaS` are retained. -/
noncomputable def testTheta : R p K := minusPart p K (ΘS p K 2)

/-- Cassels' lambda as a field unit: `(x-zeta)/(1-zeta)`.
Bilu, Section 3.1, immediately before equation (10). -/
noncomputable def lambdaUnit (x : ℤ) (hp2 : p ≠ 2) : Kˣ :=
  xmζ p K x hp2 /
    Units.mk0 (1 - ζ p K) (by
      simpa only [Int.cast_one] using
        (x_sub_ζ_ne_zero p K (1 : ℤ) hp2))

/-- The integral primitive root; no new mathematical normalization. -/
noncomputable def zetaInteger : 𝓞 K := (ζ_spec p K).toInteger

/-- The integral basis vector `sigma_a^{-1}(zeta^{-1})`, written with
`zeta^(p-1)` so the definition uses no inverse in the integer ring. -/
noncomputable def inverseConjugate (a : (ZMod p)ˣ) : 𝓞 K :=
  RingOfIntegers.mapRingHom
    ((σ p K a)⁻¹).toRingEquiv.toRingHom
    ((zetaInteger p K) ^ (p - 1))

/-- Nonnegative coefficient lift (F1), introduced here:
`m_a=q^2-1` for `2a<p`, and `m_a=1` for `2a>p`.
It is congruent modulo q^2 to the coefficient of `testTheta`. -/
def liftCoefficient (q : ℕ) (a : (ZMod p)ˣ) : ℕ :=
  if 2 * (a : ZMod p).val < p then q ^ 2 - 1 else 1

/-- Integral version of the normalized group-ring power (F2):
`A=prod_a (1-x*sigma_a^{-1}(zeta^{-1}))^m_a`.
This replaces semilocal denominators in Bilu's first-order expansion. -/
noncomputable def liftProduct (q : ℕ) (x : ℤ) : 𝓞 K :=
  ∏ a : (ZMod p)ˣ,
    (1 - (x : 𝓞 K) * inverseConjugate p K a) ^ liftCoefficient p q a

/-- The first-order coefficient (F3):
`L=sum_a m_a*sigma_a^{-1}(zeta^{-1})`. -/
noncomputable def liftLinear (q : ℕ) : 𝓞 K :=
  ∑ a : (ZMod p)ˣ,
    (liftCoefficient p q a : 𝓞 K) * inverseConjugate p K a

lemma theta_two_mem : ΘS p K 2 ∈ stickSpan p K := by
  exact Submodule.subset_span (Or.inl ⟨2, rfl⟩)


end Cyclotomic
end Catalan.A1e
