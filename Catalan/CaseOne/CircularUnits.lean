import Catalan.CaseOne.RatioUnits
import Catalan.CaseOne.PrimaryUnits
import Catalan.CaseOne.PrimaryObstruction

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Circular
section Action
variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

def unitAction (τ : G p K) : (𝓞 K)ˣ →* (𝓞 K)ˣ :=
  Units.map (RingOfIntegers.mapRingHom τ.toRingEquiv.toRingHom).toMonoidHom

lemma unitAction_coe (τ : G p K) (u : (𝓞 K)ˣ) :
    ((unitAction p K τ u : 𝓞 K) : K) = τ ((u : 𝓞 K) : K) := rfl

end Action
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The full cyclotomic-field circular units. -/
def circularUnits : Subgroup (𝓞 K)ˣ :=
  Subgroup.closure {u | u ∈ NumberField.Units.torsion K ∨
    ∃ a b : (ZMod p)ˣ, ((u : 𝓞 K) : K) =
      (1 - ζ p K ^ (a : ZMod p).val) / (1 - ζ p K ^ (b : ZMod p).val)}

def primaryCircularUnits (q : ℕ) : Subgroup (𝓞 K)ˣ :=
  circularUnits p K ⊓ UnitQuotient.primaryUnits (𝓞 K) q

lemma exists_zeta_sum_circular (q : ℕ) (hq : q.Prime) (hqp : q < p) :
    ∃ u : (𝓞 K)ˣ, u ∈ circularUnits p K ∧
      (u : 𝓞 K) = 1 + (ζ_spec p K).toInteger ^ q := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hq.two_le; omega
  have hqcp : q.Coprime p := (Nat.coprime_primes hq hp).mpr (Nat.ne_of_lt hqp)
  have h2cp : Nat.Coprime 2 p :=
    (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  let a : (ZMod p)ˣ := ZMod.unitOfCoprime (2 * q) (h2cp.mul_left hqcp)
  let b : (ZMod p)ˣ := ZMod.unitOfCoprime q hqcp
  have ha : ζ p K ^ (a : ZMod p).val = ζ p K ^ (2 * q) := by
    simp only [a, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact (pow_eq_pow_mod (2 * q) (ζ_spec p K).pow_eq_one).symm
  have hb : ζ p K ^ (b : ZMod p).val = ζ p K ^ q := by
    simp only [b, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact (pow_eq_pow_mod q (ζ_spec p K).pow_eq_one).symm
  obtain ⟨u, hu⟩ := exists_ratio_unit p K a b
  refine ⟨u, Subgroup.subset_closure (Or.inr ⟨a, b, hu⟩), ?_⟩
  have hroot : IsPrimitiveRoot (ζ p K ^ q) p := by
    simpa only [σ_apply_ζ, hb] using
      (ζ_spec p K).map_of_injective (σ p K b).injective
  have hden : 1 - ζ p K ^ q ≠ 0 := sub_ne_zero.mpr (hroot.ne_one hp.one_lt).symm
  have hvalue : ((u : 𝓞 K) : K) = 1 + ζ p K ^ q := by
    rw [hu, ha, hb, mul_comm 2 q, pow_mul]
    field_simp [hden]
    ring
  apply RingOfIntegers.ext
  change ((u : 𝓞 K) : K) = 1 + ζ p K ^ q
  exact hvalue

lemma primaryCircularUnits_ne (q : ℕ) (hq : q.Prime) (hqp : q < p) :
    primaryCircularUnits p K q ≠ circularUnits p K := by
  intro heq
  obtain ⟨u, huC, hu⟩ := exists_zeta_sum_circular p K q hq hqp
  have hprim : u ∈ UnitQuotient.primaryUnits (𝓞 K) q := by
    have hh : u ∈ primaryCircularUnits p K q := heq.symm ▸ huC
    exact hh.2
  obtain ⟨ν, hν⟩ := (UnitQuotient.mem_primaryUnits_iff (𝓞 K) q hq.pos u).mp hprim
  rw [hu] at hν
  exact Primary.zeta_sum_not_qth_mod_square p K q hq hqp ⟨ν, hν⟩

end Catalan.Circular
