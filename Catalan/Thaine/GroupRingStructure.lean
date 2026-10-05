module

public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod

/-!
# `Catalan.Thaine.GroupRingStructure`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

local instance primaryGroupRingFinite
    (G : Type*) [Group G] [Finite G] (q : ℕ) [Fact q.Prime] :
    Finite (MonoidAlgebra (ZMod q) G) := by
  classical
  let instFiniteG : Fintype G := Fintype.ofFinite G
  exact Finite.of_injective (fun x : MonoidAlgebra (ZMod q) G => x.coeff)
    MonoidAlgebra.coeff_injective

local instance primaryGroupRingCharP
    (G : Type*) [Group G] (q : ℕ) [Fact q.Prime] :
    CharP (MonoidAlgebra (ZMod q) G) q :=
  charP_of_injective_algebraMap
    (algebraMap (ZMod q) (MonoidAlgebra (ZMod q) G)).injective q

lemma groupRing_isReduced
    (G : Type*) [CommGroup G] [Finite G] (q : ℕ) [Fact q.Prime]
    (hcard : ¬ q ∣ Nat.card G) : IsReduced (MonoidAlgebra (ZMod q) G) := by
  have hc : (Nat.card G : ZMod q) ≠ 0 := by
    intro hz
    exact hcard ((ZMod.natCast_eq_zero_iff (Nat.card G) q).mp hz)
  let instCard : NeZero (Nat.card G : ZMod q) := ⟨hc⟩
  infer_instance

end Catalan.Thaine
