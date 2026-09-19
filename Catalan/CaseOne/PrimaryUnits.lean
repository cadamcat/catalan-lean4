import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.UnitQuotient

def qPowers (B : Type*) [CommGroup B] (q : ℕ) : Subgroup B where
  carrier := {b | ∃ a : B, a ^ q = b}
  one_mem' := ⟨1, one_pow q⟩
  mul_mem' := by
    rintro a b ⟨a', rfl⟩ ⟨b', rfl⟩
    exact ⟨a' * b', mul_pow a' b' q⟩
  inv_mem' := by
    rintro a ⟨a', rfl⟩
    exact ⟨a'⁻¹, inv_pow a' q⟩

abbrev ModSquare (A : Type*) [CommRing A] (q : ℕ) :=
  A ⧸ Ideal.span ({(q : A) ^ 2} : Set A)

def modSquareUnit (A : Type*) [CommRing A] (q : ℕ) : Aˣ →* (ModSquare A q)ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A))).toMonoidHom

def primaryUnits (A : Type*) [CommRing A] (q : ℕ) : Subgroup Aˣ :=
  (qPowers (ModSquare A q)ˣ q).comap (modSquareUnit A q)

lemma mem_primaryUnits_iff (A : Type*) [CommRing A] (q : ℕ) (hq : 0 < q) (u : Aˣ) :
    u ∈ primaryUnits A q ↔ ∃ v : A, (q : A) ^ 2 ∣ (u : A) - v ^ q := by
  constructor
  · intro hu
    change modSquareUnit A q u ∈ qPowers (ModSquare A q)ˣ q at hu
    change ∃ w : (ModSquare A q)ˣ, w ^ q = modSquareUnit A q u at hu
    obtain ⟨w, hw⟩ := hu
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (w : ModSquare A q)
    have hval : (w : ModSquare A q) ^ q =
        Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) (u : A) := by
      have hval := congrArg (fun z : (ModSquare A q)ˣ => (z : ModSquare A q)) hw
      change (w : ModSquare A q) ^ q =
        Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) (u : A) at hval
      exact hval
    have hqeq : (Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A))) (v ^ q) =
        Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) (u : A) := by
      calc
        Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) (v ^ q) =
            (Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) v) ^ q := by
              rw [map_pow]
        _ = (w : ModSquare A q) ^ q := by rw [hv]
        _ = Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) (u : A) := hval
    have hmem : (u : A) - v ^ q ∈ Ideal.span ({(q : A) ^ 2} : Set A) := by
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (u : A) (v ^ q)).mp hqeq.symm
    exact ⟨v, Ideal.mem_span_singleton.mp hmem⟩
  · rintro ⟨v, hv⟩
    change modSquareUnit A q u ∈ qPowers (ModSquare A q)ˣ q
    change ∃ w : (ModSquare A q)ˣ, w ^ q = modSquareUnit A q u
    have hmem : (u : A) - v ^ q ∈ Ideal.span ({(q : A) ^ 2} : Set A) :=
      Ideal.mem_span_singleton.mpr hv
    have hqeq : Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) (u : A) =
        Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) (v ^ q) :=
      Ideal.Quotient.mk_eq_mk_iff_sub_mem (u : A) (v ^ q) |>.mpr hmem
    have hunitpow : IsUnit ((Ideal.Quotient.mk
        (Ideal.span ({(q : A) ^ 2} : Set A))) v ^ q) := by
      rw [← map_pow, ← hqeq]
      exact IsUnit.map _ u.isUnit
    have hunit : IsUnit (Ideal.Quotient.mk
        (Ideal.span ({(q : A) ^ 2} : Set A)) v) :=
      (isUnit_pow_iff hq.ne').mp hunitpow
    let w : (ModSquare A q)ˣ := hunit.unit
    refine ⟨w, ?_⟩
    apply Units.ext
    have hw : (w : ModSquare A q) =
        Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) v :=
      hunit.unit_spec
    change (w : ModSquare A q) ^ q =
      Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) (u : A)
    rw [hw, ← map_pow]
    exact hqeq.symm

lemma qPowers_le_primaryUnits (A : Type*) [CommRing A] (q : ℕ) :
    qPowers Aˣ q ≤ primaryUnits A q := by
  intro u hu
  change modSquareUnit A q u ∈ qPowers (ModSquare A q)ˣ q
  change ∃ w : (ModSquare A q)ˣ, w ^ q = modSquareUnit A q u
  change ∃ v : Aˣ, v ^ q = u at hu
  obtain ⟨v, rfl⟩ := hu
  exact ⟨modSquareUnit A q v, by rw [map_pow]⟩

end Catalan.UnitQuotient
