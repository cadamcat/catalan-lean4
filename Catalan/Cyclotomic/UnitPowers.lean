module

public import Catalan.Cyclotomic.GroupRing

/-! Prime-power injectivity for units in a prime cyclotomic field. -/
/-!
# `Catalan.Cyclotomic.UnitPowers`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma qtorsion_trivial (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2)
    (a : Kˣ) (ha : a ^ q = 1) : a = 1 := by
  have hq : q.Prime := Fact.out
  have hpow : (a : K) ^ q = 1 := by
    exact congrArg (fun u : Kˣ => (u : K)) ha
  have hdiv : orderOf (a : K) ∣ q := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime hq).mp hdiv with horder | horder
  · apply Units.ext
    have h := pow_orderOf_eq_one (a : K)
    simpa only [horder, pow_one, Units.val_one] using h
  · have hroot : IsPrimitiveRoot (a : K) q := by
      rw [← horder]
      exact IsPrimitiveRoot.orderOf (a : K)
    have hd : q ∣ 2 * p := hroot.dvd_of_isCyclotomicExtension p hq.ne_zero
    exfalso
    rcases hq.dvd_mul.mp hd with htwo | hp
    · rcases (Nat.dvd_prime Nat.prime_two).mp htwo with h | h
      · exact hq.ne_one h
      · exact hq2 h
    · rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hp with h | h
      · exact hq.ne_one h
      · exact hpq h.symm

lemma unit_pow_injective (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2) :
    Function.Injective (fun a : Kˣ => a ^ q) := by
  intro a b hab
  change a ^ q = b ^ q at hab
  have h : (a / b) ^ q = 1 := by rw [div_pow, hab, div_self']
  exact div_eq_one.mp (qtorsion_trivial p K q hpq hq2 (a / b) h)


local instance unitPowersFintypeG : Fintype (G p K) := Fintype.ofFinite _

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
lemma map_upow (φ : K →+* ℂ) (a : Kˣ) (Θ : R p K) :
    φ ((upow p K a Θ : Kˣ) : K) =
      ∏ τ : G p K, (φ (τ (a : K))) ^ (Θ.coeff τ) := by
  classical
  rw [upow_fintype]
  change φ ((Units.coeHom K) (∏ τ : G p K, actUnit p K τ a ^ Θ.coeff τ)) = _
  rw [map_prod]
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro τ _
  change φ ((actUnit p K τ a ^ Θ.coeff τ : Kˣ) : K) = _
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  rfl

end Catalan
