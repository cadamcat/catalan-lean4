module

public import Catalan.CaseOne.CyclotomicPlaces
public import Catalan.CaseTwo.Assembly

/-!
# `Catalan.CaseOne.GaloisRing`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The usual Galois group operations, with commutativity witnessed cyclotomically. -/
@[instance_reducible]
def cyclotomicGalCommGroup : CommGroup (G p K) := by
  let instNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact { (inferInstance : Group (G p K)) with
    mul_comm := fun σ τ => (IsCyclotomicExtension.Rat.galEquivZMod p K).injective
      (by rw [map_mul, map_mul, mul_comm]) }

lemma cyclotomicGal_card : Nat.card (G p K) = p - 1 := by
  let instNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Nat.card_congr (IsCyclotomicExtension.Rat.galEquivZMod p K).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)]

lemma not_dvd_gal_card_of_solution (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : ¬ q ∣ Nat.card (G p K) := by
  rw [cyclotomicGal_card]
  intro hd
  exact (case_two p q Fact.out Fact.out hp2 hq2 x y hx hy h).2
    ((Nat.modEq_iff_dvd' (Fact.out : p.Prime).one_le).mpr hd).symm

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
lemma unitPower_semisimple (q : ℕ) [Fact q.Prime] (hcard : ¬ q ∣ Nat.card (G p K)) :
    IsSemisimpleModule (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) := by
  have hc : (Nat.card (G p K) : ZMod q) ≠ 0 := by
    intro hz
    exact hcard ((ZMod.natCast_eq_zero_iff (Nat.card (G p K)) q).mp hz)
  let instCard : NeZero (Nat.card (G p K) : ZMod q) := ⟨hc⟩
  infer_instance

end Catalan.UnitModule
