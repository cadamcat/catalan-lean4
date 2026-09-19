import Catalan.Stickelberger.Tower
import Catalan.Stickelberger.Uniformizer
import Catalan.Stickelberger.LocalArith

/-! # Gauss valuations for arbitrary ideals in Dedekind domains

`Catalan/Stickelberger/Tower.lean` states the Gauss valuation theorem for a
henselian local ring, because there the primitive `(#F - 1)`-th root of unity is
produced by Hensel's lemma.  The cyclotomic instantiation does not go that way:
in `𝓞 K` for `K` of conductor `ell * (ell ^ f - 1)` the root of unity is already
present, and `𝓞 K` is a Dedekind domain but not local.

So this file restates the theorem for an arbitrary ideal `I` of a Dedekind
domain, with the root of unity supplied as data.  The premise reductions of
`Tower.lean` (`ell ∈ I ^ 2` and `ζ - 1 ∈ I` from the root-of-unity condition) are
reused verbatim; they never used locality.
-/

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

/-- **General-ideal form of the Gauss valuation theorem.** `I` is an arbitrary proper
ideal of a Dedekind domain and the primitive `(#F - 1)`-th root of unity is data.
Only `ζ - 1 ∉ I ^ 2` remains as a ramification input. -/
theorem exists_gaussFamily_emultiplicity_one_of_uniformizer_ideal
    {ell : ℕ} [hp : Fact ell.Prime]
    {A : Type*} [CommRing A] [IsDedekindDomain A] (I : Ideal A) (hItop : I ≠ ⊤)
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod ell) F] [CharP F ell]
    (π : A →+* F) (hπ : Function.Surjective π) (hker : ∀ a : A, π a = 0 ↔ a ∈ I)
    (hF : 2 < Fintype.card F) (hell : 2 < ell)
    {μ : A} (hμ : IsPrimitiveRoot μ (Fintype.card F - 1))
    (hfμ : IsPrimitiveRoot (π μ) (Fintype.card F - 1))
    {ζ : A} (hζ : IsPrimitiveRoot ζ ell) (hnot : ζ - 1 ∉ I ^ 2) :
    ∃ τ : MulChar F A,
      (∀ x : F, (τ x) ^ Fintype.card F = τ x) ∧
      (∀ x : F, π (τ x) = x⁻¹) ∧ τ ≠ 1 ∧
      emultiplicity I (Ideal.span {gaussFamily τ hζ.pow_eq_one 1}) = 1 := by
  have hmem : ζ - 1 ∈ I := sub_one_mem_of_pow_eq_one I π hker hζ.pow_eq_one
  have hsqtop : I ^ 2 ≠ ⊤ := fun h =>
    hItop (top_le_iff.mp (h.ge.trans (Ideal.pow_le_self two_ne_zero)))
  have : CharP (A ⧸ I ^ 2) ell :=
    charP_quotient_pow_of_mem I ell hp.out 2 hsqtop
      (natCast_mem_sq_of_primitiveRoot I hell hζ hmem)
  exact exists_invTeichmuller_gaussFamily_emultiplicity_one I π hπ hker hF hμ hfμ
    hζ.pow_eq_one hmem hnot

/-! ### Cyclotomic field of conductor `ell * (ell ^ f - 1)`

Every input of `exists_gaussFamily_emultiplicity_one_of_uniformizer_ideal` is now
produced from the cyclotomic field itself, with no localization and no Hensel
lift: the residue cardinality comes from the inertia degree, and both roots of
unity are powers of the canonical root of conductor `n`.

The conclusion is stated as the list of inputs rather than as the Gauss valuation
itself, because `Ideal.Quotient.field` and `ZMod.algebra` are not global
instances in Mathlib (it uses `attribute [local instance]` for the former), so a
statement mentioning `MulChar (𝓞 K ⧸ P) (𝓞 K)` would need instance arguments.
A caller introduces those three instances with `letI` and composes in three lines.
-/

open NumberField in
/-- The cyclotomic field supplies every input of the Gauss valuation theorem. -/
theorem cyclotomic_route_inputs
    (ell f m n : ℕ) [hp : Fact ell.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(ell : ℤ)})]
    (hell : 2 < ell) (hf : 0 < f) (hm : m = ell ^ f - 1) (hn : n = ell * m) :
    Nat.card (𝓞 K ⧸ P) = ell ^ f ∧ (ell : 𝓞 K) ∈ P ∧ ¬ ell ∣ m ∧
      ∃ μ ζ : 𝓞 K, IsPrimitiveRoot μ m ∧ IsPrimitiveRoot ζ ell ∧
        ζ - 1 ∈ P ∧ ζ - 1 ∉ P ^ 2 := by
  have h3 : 3 ≤ ell ^ f := le_trans (by omega : 3 ≤ ell) (Nat.le_self_pow hf.ne' ell)
  have hm0 : 0 < m := by rw [hm]; omega
  have hn0 : 0 < n := by rw [hn]; positivity
  have : NeZero n := ⟨hn0.ne'⟩
  have : NeZero m := ⟨hm0.ne'⟩
  have : NeZero ell := ⟨hp.out.ne_zero⟩
  -- the two roots of unity are powers of the canonical root of conductor `n`
  have hζn := IsCyclotomicExtension.zeta_spec n ℚ K
  have hμ : IsPrimitiveRoot ((IsCyclotomicExtension.zeta n ℚ K) ^ ell) m := hζn.pow hn0 hn
  have hζ : IsPrimitiveRoot ((IsCyclotomicExtension.zeta n ℚ K) ^ m) ell :=
    hζn.pow hn0 (by rw [hn]; ring)
  obtain ⟨huni, hnot⟩ := zeta_sub_one_mem_not_mem_sq ell f m n K P hell hf hm hn hζ
  exact ⟨card_residue_of_cyclotomic ell f m n K P hell hf hm hn,
    natCast_mem_of_liesOver ell K P, not_dvd_of_eq_pow_sub_one hell hf hm,
    hμ.toInteger, hζ.toInteger, hμ.toInteger_isPrimitiveRoot,
    hζ.toInteger_isPrimitiveRoot, huni, hnot⟩

section Compose
open NumberField
attribute [local instance] Ideal.Quotient.field Fintype.ofFinite

/-- The base Gauss sum has ideal valuation one at an actual
prime ideal of an actual cyclotomic field.  Every hypothesis is either a property
of the conductor (`n = ell * (ell ^ f - 1)`, `2 < ell`, `0 < f`) or the standard
data of the prime.  The `Algebra (ZMod ell) (𝓞 K ⧸ P)` instance is the canonical
one from `ZMod.algebra`; it appears because `gaussFamily` mentions it.

No ramification input remains: `ζ - 1 ∉ P ^ 2` is proved from the cyclotomic
ramification index, and the primitive `(#F - 1)`-th root of unity comes from the
conductor rather than from a Hensel lift. -/
theorem exists_cyclotomic_gaussFamily_emultiplicity_one
    (ell f m n : ℕ) [hp : Fact ell.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span {(ell : ℤ)})]
    [Algebra (ZMod ell) (𝓞 K ⧸ P)]
    (hell : 2 < ell) (hf : 0 < f) (hm : m = ell ^ f - 1) (hn : n = ell * m) :
    ∃ (ζ : 𝓞 K) (hζ : ζ ^ ell = 1) (τ : MulChar (𝓞 K ⧸ P) (𝓞 K)),
      (∀ x : 𝓞 K ⧸ P, Ideal.Quotient.mk P (τ x) = x⁻¹) ∧
      emultiplicity P (Ideal.span {gaussFamily τ hζ 1}) = 1 := by
  obtain ⟨hcard, hmemP, hdvd, μ, ζ, hμ, hζ, huni, hnot⟩ :=
    cyclotomic_route_inputs ell f m n K P hell hf hm hn
  have : CharP (𝓞 K ⧸ P) ell :=
    charP_quotient_of_mem P ell hp.out (Ideal.IsPrime.ne_top inferInstance) hmemP
  have hcard' : Fintype.card (𝓞 K ⧸ P) = ell ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hsub : Fintype.card (𝓞 K ⧸ P) - 1 = m := by rw [hcard', hm]
  have hF : 2 < Fintype.card (𝓞 K ⧸ P) := by
    rw [hcard']
    exact lt_of_lt_of_le (by omega) (le_trans (by omega : 3 ≤ ell) (Nat.le_self_pow hf.ne' ell))
  have hker : ∀ a : 𝓞 K, Ideal.Quotient.mk P a = 0 ↔ a ∈ P := fun a =>
    Ideal.Quotient.eq_zero_iff_mem
  have hfμ : IsPrimitiveRoot (Ideal.Quotient.mk P μ) m := by
    have : NeZero m := ⟨by rw [hm]; have := Nat.le_self_pow hf.ne' ell; omega⟩
    exact isPrimitiveRoot_quotient_of_not_dvd P m ell hp.out hmemP hdvd hμ
  obtain ⟨τ, -, hred, -, hval⟩ :=
    exists_gaussFamily_emultiplicity_one_of_uniformizer_ideal P
      (Ideal.IsPrime.ne_top inferInstance) (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective hker hF hell (hsub ▸ hμ) (hsub ▸ hfμ) hζ hnot
  exact ⟨ζ, hζ.pow_eq_one, τ, hred, hval⟩

end Compose

end Catalan.Stickelberger
