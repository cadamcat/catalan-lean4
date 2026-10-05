module

public import Catalan.Stickelberger.LocalGauss
public import Catalan.Stickelberger.Teichmuller
public import Catalan.Stickelberger.SectionBridge

/-! # The integral Gauss family of the inverse Teichmüller character

`gaussFamily τ hζ a` is `g_a = g(τ ^ a)`, the integral trace Gauss sum of the
`a`-th power of the integral inverse Teichmüller character `τ`.

Three things are proved here.

* `invTeichmuller_pow_normalization`: the `d`-th member of the family, with
  `d = (#F - 1)/p`, carries exactly the `p`-torsion and the reduction `(x ^ d)⁻¹`
  fixed by `Catalan.exists_inverse_normalized_primeResidueChar`.  This is the
  link between the full family and the already proved order-`p` character.
* `integralTraceGaussSum_map`: the Gauss sum is natural in the coefficient ring,
  which is how an ideal valuation computed in the tower transfers.
* `integralTraceGaussSum_emultiplicity_one_of_teichmuller` and its existential
  form: the base member `g_1` has ideal valuation one.  Compared with
  `Catalan.Stickelberger.integralTraceGaussSum_emultiplicity_one` this no longer
  takes the coefficient-field section or the reduction identity modulo `I ^ 2` as
  premises; both are constructed.  What remains are premises about the tower
  itself: the equal characteristic of `A ⧸ I ^ 2`, a primitive `(#F - 1)`-th root
  of unity in `A`, and the uniformizer conditions `ζ - 1 ∈ I`, `ζ - 1 ∉ I ^ 2`.
-/

/-!
# `Catalan.Stickelberger.GaussFamily`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
open scoped BigOperators
namespace Catalan.Stickelberger

variable {ell : ℕ} [Fact ell.Prime]

/-- The Gauss family `g_a = g(τ ^ a)`. -/
def gaussFamily {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] (τ : MulChar F A) {ζ : A} (hζ : ζ ^ ell = 1) (a : ℕ) : A :=
  integralTraceGaussSum (τ ^ a) hζ

@[simp] lemma gaussFamily_one {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] (τ : MulChar F A) {ζ : A} (hζ : ζ ^ ell = 1) :
    gaussFamily τ hζ 1 = integralTraceGaussSum τ hζ := by
  rw [gaussFamily, pow_one]

/-- The `d`-th power of the inverse Teichmüller character has `p`-torsion and
reduces to `(x ^ d)⁻¹`: the normalization of the order-`p` residue character. -/
theorem invTeichmuller_pow_normalization
    {F : Type*} [Field F] [Fintype F] {R : Type*} [CommRing R] [IsDomain R]
    (f : R →+* F) (τ : MulChar F R) (hred : ∀ x : F, f (τ x) = x⁻¹)
    (p : ℕ) (hdvd : p ∣ Fintype.card F - 1) :
    (τ ^ ((Fintype.card F - 1) / p)) ^ p = 1 ∧
      ∀ x : Fˣ, f ((τ ^ ((Fintype.card F - 1) / p)) x)
        = ((x : F) ^ ((Fintype.card F - 1) / p))⁻¹ := by
  classical
  refine ⟨?_, ?_⟩
  · rw [← pow_mul, Nat.div_mul_cancel hdvd, ← Fintype.card_units]
    exact τ.pow_card_eq_one
  · intro x
    rw [MulChar.pow_apply_coe, map_pow, hred, inv_pow]

/-- The integral trace Gauss sum is natural in the coefficient ring. -/
theorem integralTraceGaussSum_map
    {F A B : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [CommRing B] (g : A →+* B)
    (χ : MulChar F A) {ζ : A} (hζ : ζ ^ ell = 1) :
    g (integralTraceGaussSum χ hζ) =
      integralTraceGaussSum (χ.ringHomComp g)
        (show (g ζ) ^ ell = 1 by rw [← map_pow, hζ, map_one]) := by
  change g (∑ x : F, χ x * ζ ^ (Algebra.trace (ZMod ell) F x).val) =
    ∑ x : F, (χ.ringHomComp g) x * (g ζ) ^ (Algebra.trace (ZMod ell) F x).val
  simp only [map_sum, map_mul, map_pow, MulChar.ringHomComp_apply]

/-- Valuation one for the base Gauss sum of an integral character with
Teichmüller reduction.  The coefficient-field section and the identity modulo
`I ^ 2` are constructed, not assumed. -/
theorem integralTraceGaussSum_emultiplicity_one_of_teichmuller
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [IsDedekindDomain A] (I : Ideal A)
    [CharP F ell] [CharP (A ⧸ I ^ 2) ell]
    (π : A →+* F) (hπ : Function.Surjective π) (hker : ∀ a : A, π a = 0 ↔ a ∈ I)
    (τ : MulChar F A) (hne : τ ≠ 1)
    (hpow : ∀ x : F, (τ x) ^ Fintype.card F = τ x)
    (hred : ∀ x : F, π (τ x) = x⁻¹)
    {ζ : A} (hζ : ζ ^ ell = 1) (hmem : ζ - 1 ∈ I) (hnot : ζ - 1 ∉ I ^ 2) :
    emultiplicity I (Ideal.span {integralTraceGaussSum τ hζ}) = 1 := by
  have hle : ∀ a ∈ I ^ 2, π a = 0 := fun a ha =>
    (hker a).mpr (Ideal.pow_le_self two_ne_zero ha)
  let f : A ⧸ I ^ 2 →+* F := Ideal.Quotient.lift (I ^ 2) π hle
  have hfmk : ∀ a : A, f (Ideal.Quotient.mk (I ^ 2) a) = π a := fun a =>
    Ideal.Quotient.lift_mk (I ^ 2) π hle
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := hπ y
    exact ⟨Ideal.Quotient.mk (I ^ 2) a, hfmk a⟩
  have hfker : ∀ z : A ⧸ I ^ 2, f z = 0 → z ^ 2 = 0 := by
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hfmk a] at hz
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ((hker a).mp hz) 2)
  have hredI : ∀ x : F, f (Ideal.Quotient.mk (I ^ 2) (τ x)) = x⁻¹ := fun x => by
    rw [hfmk, hred]
  obtain ⟨ι, hι⟩ := exists_residue_section_sq I ell f hfsurj hfker τ hpow hredI
  exact integralTraceGaussSum_emultiplicity_one τ hne hζ I ι hι hmem hnot

/-- Existential form: the inverse Teichmüller character itself is constructed from
a primitive `(#F - 1)`-th root of unity in the coefficient ring. -/
theorem exists_invTeichmuller_gaussFamily_emultiplicity_one
    {F A : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F]
    [CommRing A] [IsDedekindDomain A] (I : Ideal A)
    [CharP F ell] [CharP (A ⧸ I ^ 2) ell]
    (π : A →+* F) (hπ : Function.Surjective π) (hker : ∀ a : A, π a = 0 ↔ a ∈ I)
    (hF : 2 < Fintype.card F)
    {μ : A} (hμ : IsPrimitiveRoot μ (Fintype.card F - 1))
    (hfμ : IsPrimitiveRoot (π μ) (Fintype.card F - 1))
    {ζ : A} (hζ : ζ ^ ell = 1) (hmem : ζ - 1 ∈ I) (hnot : ζ - 1 ∉ I ^ 2) :
    ∃ τ : MulChar F A,
      (∀ x : F, (τ x) ^ Fintype.card F = τ x) ∧
      (∀ x : F, π (τ x) = x⁻¹) ∧ τ ≠ 1 ∧
      emultiplicity I (Ideal.span {gaussFamily τ hζ 1}) = 1 := by
  obtain ⟨τ, hpow, hred, hne⟩ := exists_invTeichmullerChar F A hF π hμ hfμ
  refine ⟨τ, hpow, hred, hne, ?_⟩
  rw [gaussFamily_one]
  exact integralTraceGaussSum_emultiplicity_one_of_teichmuller I π hπ hker τ hne hpow hred
    hζ hmem hnot

end Catalan.Stickelberger
