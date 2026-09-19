import Catalan.Runge.Definitions
import Catalan.Wieferich.Conjugation

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open NumberField
noncomputable section
namespace Catalan.Runge

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance realityGalFintype : Fintype (G p K) := Fintype.ofFinite _

lemma field_pow_injective (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2) :
    Function.Injective (fun a : K => a ^ q) := by
  intro a b hab
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  by_cases ha : a = 0
  · subst a
    have hb : b = 0 := eq_zero_of_pow_eq_zero (by simpa only [zero_pow hq] using hab.symm)
    exact hb.symm
  · have hb : b ≠ 0 := by
      intro hb
      apply ha
      apply eq_zero_of_pow_eq_zero
      simpa only [hb, zero_pow hq] using hab
    have heq : (Units.mk0 a ha) ^ q = (Units.mk0 b hb) ^ q := Units.ext hab
    exact congrArg (fun u : Kˣ => (u : K)) ((unit_pow_injective p K q hpq hq2) heq)

lemma iota_upow_eq_self_of_even (a : Kˣ) (Theta : R p K) (he : EvenCoefficients p K Theta) :
    ι p K ((upow p K a Theta : Kˣ) : K) = ((upow p K a Theta : Kˣ) : K) := by
  classical
  have hprod : ((upow p K a Theta : Kˣ) : K) = ∏ g : G p K, (g (a : K)) ^ Theta.coeff g := by
    rw [upow_fintype]
    change (Units.coeHom K) (∏ g : G p K, actUnit p K g a ^ Theta.coeff g) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro g _
    change ((actUnit p K g a ^ Theta.coeff g : Kˣ) : K) = (g (a : K)) ^ Theta.coeff g
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  rw [hprod, map_prod]
  simp only [map_zpow₀]
  have hcoef (g : G p K) : Theta.coeff (ι p K * g) = Theta.coeff g := he g
  have hperm := Equiv.prod_comp (Equiv.mulLeft (ι p K))
    (fun g : G p K => (g (a : K)) ^ Theta.coeff g)
  change (∏ g : G p K, (ι p K * g) (a : K) ^ Theta.coeff (ι p K * g)) =
    ∏ g : G p K, (g (a : K)) ^ Theta.coeff g at hperm
  simpa only [AlgEquiv.mul_apply, hcoef] using hperm

lemma root_im_eq_zero_of_even (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (x : ℤ) (Theta : R p K) (he : EvenCoefficients p K Theta) (u : K)
    (hu : u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K))
    (τ : K →+* ℂ) : (τ u).im = 0 := by
  have hi : ι p K u = u := by
    apply field_pow_injective p K q hpq hq2
    change (ι p K u) ^ q = u ^ q
    rw [← map_pow, hu]
    exact iota_upow_eq_self_of_even p K (xmζ p K x hp2) Theta he
  apply Complex.conj_eq_iff_im.mp
  rw [← A1e.iota_on_embeddings p K hp2 τ u, hi]

end Catalan.Runge
