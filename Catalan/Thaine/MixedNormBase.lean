module

public import Catalan.Thaine.MixedDescent

/-!
# `Catalan.Thaine.MixedNormBase`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

def mixedPrimeField (p ell : ℕ) : IntermediateField (A3.F p) (mixedExtension p ell) :=
  IntermediateField.adjoin (A3.F p) {mixedPRoot p ell}

def mixedPrimeGenerator (p ell : ℕ) : mixedPrimeField p ell :=
  ⟨mixedPRoot p ell, IntermediateField.subset_adjoin (A3.F p) _ (by simp)⟩

local instance mixedNormCachedFieldF (p : ℕ) : Field (A3.F p) := inferInstance
local instance mixedNormCachedFieldB (p ell : ℕ) : Field (A3.Bsub p ell) := inferInstance
local instance mixedNormCachedFieldE (p ell : ℕ) : Field (mixedExtension p ell) := inferInstance
local instance mixedNormCachedAlgebraFB (p ell : ℕ) : Algebra (A3.F p) (A3.Bsub p ell) := inferInstance
local instance mixedNormCachedAlgebraBE (p ell : ℕ) : Algebra (A3.Bsub p ell) (mixedExtension p ell) := inferInstance
local instance mixedNormCachedAlgebraFE (p ell : ℕ) : Algebra (A3.F p) (mixedExtension p ell) := inferInstance
local instance mixedNormCachedFieldK (p ell : ℕ) : Field (mixedPrimeField p ell) := inferInstance
local instance mixedNormCachedAlgebraFK (p ell : ℕ) : Algebra (A3.F p) (mixedPrimeField p ell) :=
  IntermediateField.algebra' (mixedPrimeField p ell)
local instance mixedNormCachedAlgebraKE (p ell : ℕ) : Algebra (mixedPrimeField p ell) (mixedExtension p ell) := inferInstance

local instance mixedNormCachedModuleFB (p ell : ℕ) : Module (A3.F p) (A3.Bsub p ell) := Algebra.toModule
local instance mixedNormCachedFreeFB (p ell : ℕ) : Module.Free (A3.F p) (A3.Bsub p ell) := Module.Free.of_divisionRing (A3.F p) (A3.Bsub p ell)
local instance mixedNormCachedModuleBE (p ell : ℕ) : Module (A3.Bsub p ell) (mixedExtension p ell) := Algebra.toModule
local instance mixedNormCachedFreeBE (p ell : ℕ) : Module.Free (A3.Bsub p ell) (mixedExtension p ell) := Module.Free.of_divisionRing (A3.Bsub p ell) (mixedExtension p ell)
local instance mixedNormCachedModuleFE (p ell : ℕ) : Module (A3.F p) (mixedExtension p ell) := Algebra.toModule
local instance mixedNormCachedModuleFK (p ell : ℕ) : Module (A3.F p) (mixedPrimeField p ell) := Algebra.toModule

lemma mixedFiniteOverF (p ell : ℕ) :
    FiniteDimensional (A3.F p) (mixedExtension p ell) :=
  FiniteDimensional.trans (A3.F p) (A3.Bsub p ell) (mixedExtension p ell)

def mixedBaseRange (p ell : ℕ) : IntermediateField (A3.F p) (mixedExtension p ell) :=
  (IsScalarTower.toAlgHom (A3.F p) (A3.Bsub p ell) (mixedExtension p ell)).fieldRange

local instance mixedNormCachedFieldRange (p ell : ℕ) : Field (mixedBaseRange p ell) := inferInstance
local instance mixedNormCachedAlgebraFRange (p ell : ℕ) : Algebra (A3.F p) (mixedBaseRange p ell) :=
  IntermediateField.algebra' (mixedBaseRange p ell)

local instance mixedNormCachedModuleFRange (p ell : ℕ) : Module (A3.F p) (mixedBaseRange p ell) := Algebra.toModule

lemma mixedBaseRange_finrank (p ell : ℕ) :
    Module.finrank (A3.F p) (mixedBaseRange p ell) =
      Module.finrank (A3.F p) (A3.Bsub p ell) := by
  let f := IsScalarTower.toAlgHom (A3.F p) (A3.Bsub p ell) (mixedExtension p ell)
  let instMixedRangeLocalAlgebra : Algebra (A3.F p) f.fieldRange := IntermediateField.algebra' f.fieldRange
  let instMixedRangeLocalModule : Module (A3.F p) f.fieldRange := Algebra.toModule
  exact f.equivFieldRange.toLinearEquiv.finrank_eq.symm

lemma mixedPrime_sup_base (p ell : ℕ) (hp : 0 < p) :
    mixedPrimeField p ell ⊔ mixedBaseRange p ell = ⊤ := by
  have instMixedSupNeP : NeZero p := ⟨hp.ne'⟩
  have instMixedSupCyclo : IsCyclotomicExtension {p} (A3.Bsub p ell) (mixedExtension p ell) :=
    mixedExtension_isCyclotomic p ell hp
  have hr : IsPrimitiveRoot (mixedPRoot p ell) p :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (A3.primitiveRoot_spec p hp)
  have hgen : IntermediateField.adjoin (A3.Bsub p ell) {mixedPRoot p ell} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra (A3.Bsub p ell) _
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hr)
  let S := mixedPrimeField p ell ⊔ mixedBaseRange p ell
  change S = ⊤
  apply top_unique
  intro x hx
  have hxgen : x ∈ IntermediateField.adjoin (A3.Bsub p ell) {mixedPRoot p ell} := by
    rw [hgen]
    trivial
  clear hx
  induction hxgen using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain rfl : y = mixedPRoot p ell := by simpa using hy
    exact (show mixedPrimeField p ell ≤ S from le_sup_left)
      (IntermediateField.subset_adjoin (A3.F p) _ (by simp))
  | algebraMap y =>
    exact (show mixedBaseRange p ell ≤ S from le_sup_right) ⟨y, rfl⟩
  | add a b ha hb hsa hsb => exact S.add_mem hsa hsb
  | inv a ha hsa => exact S.inv_mem hsa
  | mul a b ha hb hsa hsb => exact S.mul_mem hsa hsb

lemma mixedPrimeField_finrank
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell) :
    Module.finrank (A3.F p) (mixedPrimeField p ell) = 2 := by
  have hp := (Fact.out : p.Prime)
  have instMixedPrimeFinite : FiniteDimensional (A3.F p) (mixedExtension p ell) := mixedFiniteOverF p ell
  have hr : IsPrimitiveRoot (mixedPRoot p ell) p :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (A3.primitiveRoot_spec p hp.pos)
  let t : A3.F p := ⟨A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let P : Polynomial (A3.F p) := Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1
  have htrace : algebraMap (A3.F p) (mixedExtension p ell) t =
      mixedPRoot p ell + (mixedPRoot p ell)⁻¹ := by
    apply Subtype.ext
    rfl
  have hP2 : P.coeff 2 = 1 := by norm_num [P, Polynomial.coeff_one]
  have hPne : P ≠ 0 := by intro h; rw [h, Polynomial.coeff_zero] at hP2; exact zero_ne_one hP2
  have hPdeg : P.natDegree ≤ 2 := by dsimp [P]; compute_degree
  have hPzero : Polynomial.aeval (mixedPRoot p ell) P = 0 := by
    simp only [P, map_add, map_sub, map_pow, map_mul, map_one, Polynomial.aeval_X,
      Polynomial.aeval_C, htrace]
    field_simp [hr.ne_zero hp.ne_zero]
    ring
  have hzint : IsIntegral (A3.F p) (mixedPRoot p ell) := IsIntegral.of_finite _ _
  have hle : Module.finrank (A3.F p) (mixedPrimeField p ell) ≤ 2 := by
    have hdim : Module.finrank (A3.F p) (mixedPrimeField p ell) =
        (minpoly (A3.F p) (mixedPRoot p ell)).natDegree := IntermediateField.adjoin.finrank hzint
    rw [hdim]
    exact (Polynomial.natDegree_le_of_dvd
      (minpoly.dvd (A3.F p) (mixedPRoot p ell) hPzero) hPne).trans hPdeg
  have hne : Module.finrank (A3.F p) (mixedPrimeField p ell) ≠ 1 := by
    intro h1
    have hbot : mixedPRoot p ell ∈ (⊥ : IntermediateField (A3.F p) (mixedExtension p ell)) :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h1
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hbot
    obtain ⟨tau, htau, _, _⟩ := exists_mixed_involution p ell hp2 hpe
    have hfix : tau (mixedPRoot p ell) = mixedPRoot p ell := by
      rw [← hy]
      exact (tau.restrictScalars (A3.F p)).commutes y
    have hinv : mixedPRoot p ell = (mixedPRoot p ell)⁻¹ := hfix.symm.trans htau
    have hpow : mixedPRoot p ell ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hinv]
      exact inv_mul_cancel₀ (hr.ne_zero hp.ne_zero)
    exact hp2 (Nat.le_antisymm
      (Nat.le_of_dvd (by decide : 0 < 2) (hr.dvd_of_pow_eq_one 2 hpow)) hp.two_le)
  have hpos := (Module.finrank_pos : 0 < Module.finrank (A3.F p) (mixedPrimeField p ell))
  omega

lemma mixedExtension_overPrime_isCyclotomic
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell) :
    IsCyclotomicExtension {ell} (mixedPrimeField p ell) (mixedExtension p ell) := by
  have instMixedOverPrimeNeEll : NeZero ell := ⟨(Fact.out : ell.Prime).ne_zero⟩
  have instMixedOverPrimeFinite : FiniteDimensional (A3.F p) (mixedExtension p ell) := mixedFiniteOverF p ell
  have instMixedOverPrimeFiniteBaseK : FiniteDimensional (A3.F p) (mixedPrimeField p ell) :=
    FiniteDimensional.of_finrank_pos (by rw [mixedPrimeField_finrank p ell hp2 hpe]; decide)
  have instMixedOverPrimeFiniteK : FiniteDimensional (mixedPrimeField p ell) (mixedExtension p ell) :=
    FiniteDimensional.right (A3.F p) (mixedPrimeField p ell) (mixedExtension p ell)
  have instMixedOverPrimeCycloB : IsCyclotomicExtension {ell} (A3.F p) (A3.Bsub p ell) :=
    A3.isCyclotomicExtension_Bsub p ell (Fact.out : ell.Prime).pos
  have hbroot : IsPrimitiveRoot (auxiliaryRoot p ell) ell :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos)
  have hw : IsPrimitiveRoot (mixedEllRoot p ell) ell :=
    hbroot.map_of_injective (algebraMap (A3.Bsub p ell) (mixedExtension p ell)).injective
  have hBgen : IntermediateField.adjoin (A3.F p) {auxiliaryRoot p ell} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra (A3.F p) _
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top hbroot)
  have hBrange : mixedBaseRange p ell = IntermediateField.adjoin (A3.F p) {mixedEllRoot p ell} := by
    rw [mixedBaseRange, AlgHom.fieldRange_eq_map, ← hBgen, IntermediateField.adjoin_map]
    simp only [Set.image_singleton]
    rfl
  have hKgen : IntermediateField.adjoin (mixedPrimeField p ell) {mixedEllRoot p ell} = ⊤ := by
    apply IntermediateField.restrictScalars_injective (A3.F p)
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, ← hBrange,
      mixedPrime_sup_base p ell (Fact.out : p.Prime).pos]
    rfl
  have instMixedOverPrimeCycloAdjoin : IsCyclotomicExtension {ell} (mixedPrimeField p ell)
      (IntermediateField.adjoin (mixedPrimeField p ell) {mixedEllRoot p ell}) :=
    hw.intermediateField_adjoin_isCyclotomicExtension (mixedPrimeField p ell)
  exact IsCyclotomicExtension.equiv {ell} (mixedPrimeField p ell) _
    ((IntermediateField.equivOfEq hKgen).trans IntermediateField.topEquiv)


lemma mixedPrime_linearDisjoint
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell) :
    (mixedPrimeField p ell).LinearDisjoint (mixedBaseRange p ell) := by
  have instMixedLinearFinite : FiniteDimensional (A3.F p) (mixedExtension p ell) := mixedFiniteOverF p ell
  apply IntermediateField.LinearDisjoint.of_finrank_sup
  rw [mixedPrime_sup_base p ell (Fact.out : p.Prime).pos, IntermediateField.finrank_top',
    mixedPrimeField_finrank p ell hp2 hpe, mixedBaseRange_finrank]
  have h := Module.finrank_mul_finrank (A3.F p) (A3.Bsub p ell) (mixedExtension p ell)
  rw [mixedExtension_finrank p ell hp2 hpe] at h
  exact h.symm.trans (mul_comm _ _)


lemma mixedExtension_overPrime_finrank
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell) :
    Module.finrank (mixedPrimeField p ell) (mixedExtension p ell) = ell - 1 := by
  have instMixedDegreeFinite : FiniteDimensional (A3.F p) (mixedExtension p ell) := mixedFiniteOverF p ell
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := (ZMod ell)ˣ)
  calc
    Module.finrank (mixedPrimeField p ell) (mixedExtension p ell) =
        Module.finrank (A3.F p) (mixedBaseRange p ell) :=
      (mixedPrime_linearDisjoint p ell hp2 hpe).finrank_left_eq_finrank
        (mixedPrime_sup_base p ell (Fact.out : p.Prime).pos)
    _ = Module.finrank (A3.F p) (A3.Bsub p ell) := mixedBaseRange_finrank p ell
    _ = ell - 1 := (auxiliary_cyclic_generator p ell hpe s hs).1

lemma mixedPrime_norm_compat
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hp2 : p ≠ 2) (hpe : p ≠ ell)
    (x : A3.Bsub p ell) :
    Algebra.norm (mixedPrimeField p ell)
        (algebraMap (A3.Bsub p ell) (mixedExtension p ell) x) =
      algebraMap (A3.F p) (mixedPrimeField p ell) (Algebra.norm (A3.F p) x) := by
  have instMixedNormFinite : FiniteDimensional (A3.F p) (mixedExtension p ell) := mixedFiniteOverF p ell
  let e : A3.Bsub p ell ≃ₐ[A3.F p] mixedBaseRange p ell :=
    (IsScalarTower.toAlgHom (A3.F p) (A3.Bsub p ell) (mixedExtension p ell)).equivFieldRange
  have h := (mixedPrime_linearDisjoint p ell hp2 hpe).norm_algebraMap
    (mixedPrime_sup_base p ell (Fact.out : p.Prime).pos) (e x)
  rw [Algebra.norm_eq_of_algEquiv e] at h
  exact h

end Catalan.Thaine
