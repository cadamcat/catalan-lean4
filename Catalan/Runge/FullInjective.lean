module

public import Catalan.Runge.BoundedLift
public import Catalan.Runge.PowerTransport
public import Catalan.Runge.Growth
public import Catalan.Runge.Normalized

/-!
# `Catalan.Runge.FullInjective`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Runge
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma normalize_full_relation (q : ℕ) (hq : q.Prime) (hp2 : p ≠ 2) (x : ℤ)
    (Theta : R p K)
    (he : ∀ g : G p K,
      (Theta.coeff (ι p K * g) : ZMod q) = (Theta.coeff g : ZMod q))
    (hw : (weight p K Theta : ZMod q) = 0) (hne : reduceFull p K q Theta ≠ 0)
    (hu : ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K)) :
    ∃ (Psi : R p K) (m : ℕ),
      (∀ g, 0 ≤ Psi.coeff g) ∧ EvenCoefficients p K Psi ∧
      0 < m ∧ 2 * m ≤ p - 1 ∧ weight p K Psi = (m * q : ℕ) ∧
      reduceFull p K q Psi ≠ 0 ∧
      ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Psi : Kˣ) : K) := by
  obtain ⟨Psi, m, hn, he', hm, hmp, hw', hne', heq⟩ :=
    exists_bounded_even_lift p K q hq Theta he hw hne
  exact ⟨Psi, m, hn, he', hm, hmp, hw', hne',
    root_of_reduceFull_eq_or_neg p K q hp2 x Psi Theta heq hu⟩

lemma runge_full_injective (q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q)
    (hp2 : p ≠ 2) (hpq : p ≠ q) (x : ℤ)
    (hx : (q : ℝ) ^ (p - 1) < (|x| : ℝ)) (Theta : R p K)
    (he : ∀ g : G p K,
      (Theta.coeff (ι p K * g) : ZMod q) = (Theta.coeff g : ZMod q))
    (hw : (weight p K Theta : ZMod q) = 0)
    (hu : ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K)) :
    reduceFull p K q Theta = 0 := by
  by_contra hne
  obtain ⟨Psi, m, hn, he', hm, hmp, hw', hne', hu'⟩ :=
    normalize_full_relation p K q hq hp2 x Theta he hw hne hu
  exact hne' (runge_normalized p K q hq hq7 hp2 hpq x hx Psi hn he' m hm hmp hw' hu')

lemma runge_full_injective_of_solution (q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q)
    (hqp : q < p) (hp2 : p ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (Theta : R p K)
    (he : ∀ g : G p K,
      (Theta.coeff (ι p K * g) : ZMod q) = (Theta.coeff g : ZMod q))
    (hw : (weight p K Theta : ZMod q) = 0)
    (hu : ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K)) :
    reduceFull p K q Theta = 0 :=
  runge_full_injective p K q hq hq7 hp2 (ne_of_gt hqp) x
    (cassels_growth p q Fact.out hq hq7 hqp x y hx hy h) Theta he hw hu

end Catalan.Runge
