module

public import Catalan.Stickelberger.GaussFamily
public import Catalan.Stickelberger.TowerArith
public import Catalan.Stickelberger.WittTower
public import Mathlib.RingTheory.Henselian

/-! # Lifting roots of unity by Hensel's lemma

The Teichmüller family of `Catalan/Stickelberger/Teichmuller.lean` needs a
primitive `(#F - 1)`-th root of unity in the coefficient ring `A`, together with
the fact that it stays primitive after reduction.  Both are produced here for any
henselian local ring with finite residue field, which avoids computing residue
degrees in a cyclotomic tower.
-/

/-!
# `Catalan.Stickelberger.Tower`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

open Polynomial

/-- A generator of the unit group of a finite field is a primitive
`(#F - 1)`-th root of unity. -/
theorem exists_isPrimitiveRoot_card_sub_one (F : Type*) [Field F] [Fintype F] :
    ∃ g : F, IsPrimitiveRoot g (Fintype.card F - 1) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hg' : orderOf g = Fintype.card F - 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using hg
  refine ⟨(g : F), ?_, ?_⟩
  · have h1 : g ^ (Fintype.card F - 1) = 1 := by rw [← hg']; exact pow_orderOf_eq_one g
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val h1
  · intro l hl
    rw [← hg']
    apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hl

/-- **Hensel lifting of the full group of roots of unity.**  In a henselian local
ring whose residue field is finite, a generator of the residue unit group lifts to
a primitive `(#F - 1)`-th root of unity.  This supplies both primitive-root
premises of the Teichmüller family. -/
theorem exists_primitiveRoot_of_henselian
    {A : Type*} [CommRing A] [HenselianLocalRing A]
    {F : Type*} [Field F] [Fintype F]
    (π : A →+* F) (hπ : Function.Surjective π)
    (hker : ∀ a : A, π a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A) :
    ∃ μ : A, IsPrimitiveRoot μ (Fintype.card F - 1) ∧
      IsPrimitiveRoot (π μ) (Fintype.card F - 1) := by
  classical
  obtain ⟨g, hg⟩ := exists_isPrimitiveRoot_card_sub_one F
  obtain ⟨a₀, ha₀⟩ := hπ g
  have hcard : 1 < Fintype.card F := Fintype.one_lt_card
  have hn : Fintype.card F - 1 ≠ 0 := by omega
  -- the residue of the derivative is `-1` times a unit, hence nonzero
  have hgne : g ≠ 0 := hg.ne_zero hn
  have hcast : ((Fintype.card F - 1 : ℕ) : F) = -1 := by
    rw [Nat.cast_sub hcard.le, Nat.cast_one, Nat.cast_card_eq_zero, zero_sub]
  set n := Fintype.card F - 1 with hndef
  set f : A[X] := X ^ n - 1 with hfdef
  have hmonic : f.Monic := by
    have : f = X ^ n - C (1 : A) := by rw [hfdef, map_one]
    rw [this]; exact monic_X_pow_sub_C 1 hn
  have heval : f.eval a₀ ∈ IsLocalRing.maximalIdeal A := by
    apply (hker _).mp
    rw [hfdef]
    simp only [eval_sub, eval_pow, eval_X, eval_one, map_sub, map_pow, map_one, ha₀]
    rw [hg.pow_eq_one, sub_self]
  have hderiv : f.derivative.eval a₀ = (n : A) * a₀ ^ (n - 1) := by
    rw [hfdef]
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul,
      eval_C, eval_pow, eval_X]
  have hunit : IsUnit (f.derivative.eval a₀) := by
    rw [hderiv, ← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have h0 := (hker _).mpr hmem
    rw [map_mul, map_pow, ha₀, map_natCast, hndef, hcast] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact one_ne_zero (neg_eq_zero.mp h)
    · exact hgne (pow_eq_zero_iff'.mp h).1
  obtain ⟨μ, hroot, hclose⟩ := HenselianLocalRing.is_henselian f hmonic a₀ heval hunit
  have hμpow : μ ^ n = 1 := by
    have := hroot
    rw [IsRoot, hfdef] at this
    simp only [eval_sub, eval_pow, eval_X, eval_one] at this
    exact sub_eq_zero.mp this
  have hπμ : π μ = g := by
    have h0 := (hker _).mpr hclose
    rw [map_sub, ha₀, sub_eq_zero] at h0
    exact h0
  refine ⟨μ, ⟨hμpow, ?_⟩, ?_⟩
  · intro l hl
    apply hg.dvd_of_pow_eq_one
    rw [← hπμ, ← map_pow, hl, map_one]
  · rw [hπμ]; exact hg

/-- **Gauss-sum valuation theorem.** For a henselian local Dedekind domain with finite
residue field, the base Gauss sum of the inverse Teichmüller character has ideal
valuation one.  Compared with `exists_invTeichmuller_gaussFamily_emultiplicity_one`
the two primitive-root premises are gone: only the ramification data of the tower
(`CharP (A ⧸ I ^ 2) ell`, `ζ - 1 ∈ I`, `ζ - 1 ∉ I ^ 2`) and `2 < #F` remain. -/
theorem exists_gaussFamily_emultiplicity_one_of_henselian
    {ell : ℕ} [Fact ell.Prime]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [HenselianLocalRing A]
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    [CharP (A ⧸ (IsLocalRing.maximalIdeal A) ^ 2) ell]
    (π : A →+* F) (hπ : Function.Surjective π)
    (hker : ∀ a : A, π a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (hF : 2 < Fintype.card F)
    {ζ : A} (hζ : ζ ^ ell = 1)
    (hmem : ζ - 1 ∈ IsLocalRing.maximalIdeal A)
    (hnot : ζ - 1 ∉ (IsLocalRing.maximalIdeal A) ^ 2) :
    ∃ τ : MulChar F A,
      (∀ x : F, (τ x) ^ Fintype.card F = τ x) ∧
      (∀ x : F, π (τ x) = x⁻¹) ∧ τ ≠ 1 ∧
      emultiplicity (IsLocalRing.maximalIdeal A)
        (Ideal.span {gaussFamily τ hζ 1}) = 1 := by
  obtain ⟨μ, hμ, hfμ⟩ := exists_primitiveRoot_of_henselian π hπ hker
  exact exists_invTeichmuller_gaussFamily_emultiplicity_one
    (IsLocalRing.maximalIdeal A) π hπ hker hF hμ hfμ hζ hmem hnot

/-- In a domain, a primitive `ell`-th root of unity with `ζ - 1 ∈ I` forces
`ell ∈ I ^ 2` as soon as `2 < ell`.  This is the cyclotomic ramification identity
`ell = unit * (ζ - 1) ^ (ell - 1)` in the divisibility form Mathlib supplies. -/
theorem natCast_mem_sq_of_primitiveRoot {A : Type*} [CommRing A] [IsDomain A]
    (I : Ideal A) {ell : ℕ} (hell : 2 < ell) {ζ : A} (hζ : IsPrimitiveRoot ζ ell)
    (hmem : ζ - 1 ∈ I) : (ell : A) ∈ I ^ 2 := by
  obtain ⟨z, -, hz⟩ := hζ.self_sub_one_pow_dvd_order hell
  rw [hz]
  exact Ideal.mul_mem_left _ z (Ideal.pow_mem_pow hmem 2)

/-- **Reduced form.** The equal-characteristic premise on `A ⧸ I ^ 2` is
gone: for an odd residue characteristic it follows from the uniformizer condition.
What remains are exactly the uniformizer facts `ζ - 1 ∈ I`, `ζ - 1 ∉ I ^ 2` for a
primitive `ell`-th root of unity, plus `2 < #F`. -/
theorem exists_gaussFamily_emultiplicity_one_of_primitiveRoot
    {ell : ℕ} [hp : Fact ell.Prime]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [HenselianLocalRing A]
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (π : A →+* F) (hπ : Function.Surjective π)
    (hker : ∀ a : A, π a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (hF : 2 < Fintype.card F) (hell : 2 < ell)
    {ζ : A} (hζ : IsPrimitiveRoot ζ ell)
    (hmem : ζ - 1 ∈ IsLocalRing.maximalIdeal A)
    (hnot : ζ - 1 ∉ (IsLocalRing.maximalIdeal A) ^ 2) :
    ∃ τ : MulChar F A,
      (∀ x : F, (τ x) ^ Fintype.card F = τ x) ∧
      (∀ x : F, π (τ x) = x⁻¹) ∧ τ ≠ 1 ∧
      emultiplicity (IsLocalRing.maximalIdeal A)
        (Ideal.span {gaussFamily τ hζ.pow_eq_one 1}) = 1 := by
  have hItop : IsLocalRing.maximalIdeal A ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have hsqtop : (IsLocalRing.maximalIdeal A) ^ 2 ≠ ⊤ := fun h =>
    hItop (top_le_iff.mp (h.ge.trans (Ideal.pow_le_self two_ne_zero)))
  have : CharP (A ⧸ (IsLocalRing.maximalIdeal A) ^ 2) ell :=
    charP_quotient_pow_of_mem _ ell hp.out 2 hsqtop
      (natCast_mem_sq_of_primitiveRoot _ hell hζ hmem)
  exact exists_gaussFamily_emultiplicity_one_of_henselian π hπ hker hF hζ.pow_eq_one hmem hnot

/-- The uniformizer membership `ζ - 1 ∈ I` is automatic: in residue characteristic
`ell` the only `ell`-th root of unity is `1`. -/
theorem sub_one_mem_of_pow_eq_one
    {A : Type*} [CommRing A] (I : Ideal A)
    {F : Type*} [Field F] {ell : ℕ} [Fact ell.Prime] [CharP F ell]
    (π : A →+* F) (hker : ∀ a : A, π a = 0 ↔ a ∈ I)
    {ζ : A} (hζ : ζ ^ ell = 1) : ζ - 1 ∈ I := by
  apply (hker _).mp
  rw [map_sub, map_one]
  have h : (π ζ - 1) ^ ell = 0 := by
    rw [sub_pow_char, one_pow, ← map_pow, hζ, map_one, sub_self]
  exact pow_eq_zero_iff (Fact.out : ell.Prime).ne_zero |>.mp h

/-- **Uniformizer form.** Only one ramification input remains: the primitive
`ell`-th root of unity must not be congruent to `1` modulo `I ^ 2`, i.e. `ζ - 1`
is an actual uniformizer.  Everything else is either general structure of a
henselian local Dedekind domain or arithmetic of the residue field. -/
theorem exists_gaussFamily_emultiplicity_one_of_uniformizer
    {ell : ℕ} [hp : Fact ell.Prime]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [HenselianLocalRing A]
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (π : A →+* F) (hπ : Function.Surjective π)
    (hker : ∀ a : A, π a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (hF : 2 < Fintype.card F) (hell : 2 < ell)
    {ζ : A} (hζ : IsPrimitiveRoot ζ ell)
    (hnot : ζ - 1 ∉ (IsLocalRing.maximalIdeal A) ^ 2) :
    ∃ τ : MulChar F A,
      (∀ x : F, (τ x) ^ Fintype.card F = τ x) ∧
      (∀ x : F, π (τ x) = x⁻¹) ∧ τ ≠ 1 ∧
      emultiplicity (IsLocalRing.maximalIdeal A)
        (Ideal.span {gaussFamily τ hζ.pow_eq_one 1}) = 1 :=
  exists_gaussFamily_emultiplicity_one_of_primitiveRoot π hπ hker hF hell hζ
    (sub_one_mem_of_pow_eq_one _ π hker hζ.pow_eq_one) hnot


/-! ### A concrete instance: Witt vectors over the residue field

`WittVector ell F` is a henselian local Dedekind domain with residue field `F`
(`Catalan/Stickelberger/WittTower.lean`), so the Hensel lift above applies to it
verbatim.  This exhibits the full group of `(#F - 1)`-th roots of unity in an
actual ring, with no cyclotomic residue-degree computation.

It does **not** carry the Gauss sum: the maximal ideal of `WittVector ell F` is
generated by `ell`, so `ell ∉ I ^ 2` and there is no primitive `ell`-th root of
unity in it.  The ramified extension adjoining `ζ_ell` is still required, and is
the remaining input for the cyclotomic valuation argument.
-/

namespace Witt

open WittVector

/-- The full group of `(#F - 1)`-th roots of unity lives in `WittVector ell F`,
and reduces isomorphically onto the residue unit group. -/
theorem exists_primitiveRoot_wittVector (ell : ℕ) [Fact ell.Prime]
    (F : Type*) [Field F] [Fintype F] [CharP F ell] :
    ∃ μ : WittVector ell F, IsPrimitiveRoot μ (Fintype.card F - 1) ∧
      IsPrimitiveRoot (WittVector.constantCoeff μ) (Fintype.card F - 1) := by
  have := wittVector_henselianLocalRing ell F
  have hpi : Function.Surjective (WittVector.constantCoeff : WittVector ell F →+* F) :=
    WittVector.constantCoeff_surjective ell
  have hker : ∀ a : WittVector ell F,
      WittVector.constantCoeff a = 0 ↔ a ∈ IsLocalRing.maximalIdeal (WittVector ell F) := by
    intro a
    rw [← RingHom.mem_ker, WittVector.ker_constantCoeff,
      wittVector_span_eq_maximalIdeal ell F]
  exact exists_primitiveRoot_of_henselian _ hpi hker

end Witt

end Catalan.Stickelberger
