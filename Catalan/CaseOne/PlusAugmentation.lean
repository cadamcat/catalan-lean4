module

public import Catalan.CaseOne.UnitNorm
public import Catalan.CaseOne.AnnihilatorDuality
public import Catalan.CaseOne.Involution

/-!
# `Catalan.CaseOne.PlusAugmentation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance plusAugGalComm : CommGroup (G p K) := cyclotomicGalCommGroup p K

lemma iota_square : (ι p K) ^ 2 = 1 := by
  let instNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let e := IsCyclotomicExtension.Rat.galEquivZMod p K
  have he : e (ι p K) = (-1 : (ZMod p)ˣ) := by
    change e (e.symm (-1)) = -1
    exact e.apply_symm_apply _
  apply e.injective
  rw [map_pow, he, map_one]
  apply Units.ext
  simp

/-- The plus ideal (1+iota) times the annihilator of the norm. -/
def plusAugIdeal (q : ℕ) : Ideal (MonoidAlgebra (ZMod q) (G p K)) :=
  Ideal.span ({1 + MonoidAlgebra.single (ι p K) (1 : ZMod q)} : Set _) *
    (Ideal.span ({UnitReduction.groupNorm (ZMod q) (G p K)} : Set _)).annihilator

lemma plusAugIdeal_annihilator (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) (hcard : ¬ q ∣ Nat.card (G p K)) :
    (plusAugIdeal p K q).annihilator = normPlusIdeal p K q := by
  have hc : (Nat.card (G p K) : ZMod q) ≠ 0 := by
    intro hz
    exact hcard ((ZMod.natCast_eq_zero_iff (Nat.card (G p K)) q).mp hz)
  let instCard : NeZero (Nat.card (G p K) : ZMod q) := ⟨hc⟩
  have instRingSemi : IsSemisimpleRing (MonoidAlgebra (ZMod q) (G p K)) := inferInstance
  have h2q : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (Fact.out : q.Prime).ne_one h1
    · exact hq2 h2
  have h2 : IsUnit (2 : MonoidAlgebra (ZMod q) (G p K)) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr h2q).map
      (algebraMap (ZMod q) (MonoidAlgebra (ZMod q) (G p K)))
  have hz : (MonoidAlgebra.single (ι p K) (1 : ZMod q)) ^ 2 = 1 := by
    rw [MonoidAlgebra.single_pow, iota_square, one_pow, ← MonoidAlgebra.one_def]
  rw [plusAugIdeal, UnitReduction.semisimple_ideal_annihilator_mul,
    UnitReduction.annihilator_span_one_add_involution _ hz h2,
    UnitReduction.semisimple_ideal_double_annihilator, normPlusIdeal, Ideal.span_insert]
  exact sup_comm _ _

lemma plusAugIdeal_annihilator_of_solution (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    (plusAugIdeal p K q).annihilator = normPlusIdeal p K q :=
  plusAugIdeal_annihilator p K q hq2 (not_dvd_gal_card_of_solution p K q hp2 hq2 x y hx hy h)

lemma plusAug_unit_annihilator_of_solution (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    (plusAugIdeal p K q).annihilator =
      Module.annihilator (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) := by
  rw [plusAugIdeal_annihilator_of_solution p K q hp2 hq2 x y hx hy h,
    unit_annihilator_eq_normPlus_of_solution p K q hp2 hq2 x y hx hy h]

end Catalan.UnitModule
