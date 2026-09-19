import Mathlib

/-!
Prime selection for the mod-q Thaine argument.
Target: Lean / Mathlib v4.33.1.

The Hilbert q-field is an actual supremum of subfields. Finiteness, Artin
reciprocity, and the class-group interpretation remain separate obligations.
This file states the prime-selection input; it does not prove all of Thaine's
theorem.
-/

open NumberField
open Filter Topology

noncomputable section

namespace Catalan
namespace A3

/-- A fixed algebraic closure of Q. -/
abbrev Omega := AlgebraicClosure ℚ

/-- A chosen primitive n-th root, provided one exists.
Positive-n existence is established by a separate theorem. -/
def primitiveRoot (n : ℕ) : Omega :=
  Classical.epsilon (fun z : Omega => IsPrimitiveRoot z n)

/-- The subfield Q(zeta_p + zeta_p^(-1)). -/
def Fsub (p : ℕ) : IntermediateField ℚ Omega :=
  IntermediateField.adjoin ℚ
    ({primitiveRoot p + (primitiveRoot p)⁻¹} : Set Omega)

/-- The real prime-conductor cyclotomic field, as a type. -/
abbrev F (p : ℕ) := ↥(Fsub p)

/-- B = F(zeta_q), inside the fixed algebraic closure. -/
def Bsub (p q : ℕ) : IntermediateField (F p) Omega :=
  IntermediateField.adjoin (F p) ({primitiveRoot q} : Set Omega)

/-- The set of all q-th roots of all global units of F. -/
def unitRadicals (p q : ℕ) : Set Omega :=
  {r | ∃ u : (𝓞 (F p))ˣ,
    r ^ q = algebraMap (F p) Omega (((u : 𝓞 (F p)) : F p))}

/-- M = F(zeta_q, E^(1/q)); the multi-unit Kummer field. -/
def Msub (p q : ℕ) : IntermediateField (F p) Omega :=
  Bsub p q ⊔ IntermediateField.adjoin (F p) (unitRadicals p q)

/-- Restriction of a field automorphism to algebraic integers. -/
def integralAut {k L : Type*} [Field k] [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) : 𝓞 L ≃+* 𝓞 L :=
  NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv

/-- The decomposition-group membership condition at P. -/
def PreservesPrime {k L : Type*} [Field k] [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) (P : Ideal (𝓞 L)) : Prop :=
  ∀ x : 𝓞 L, integralAut σ x ∈ P ↔ x ∈ P

/-- Triviality of the inertia group at P.
For finite Galois number-field extensions this is unramifiedness at P. -/
def InertiaTrivial (k L : Type*) [Field k] [Field L] [Algebra k L]
    (P : Ideal (𝓞 L)) : Prop :=
  ∀ σ : L ≃ₐ[k] L, PreservesPrime σ P →
    (∀ x : 𝓞 L, integralAut σ x - x ∈ P) → σ = 1

/-- Finite abelian Galois exponent-q extensions of F, unramified
at finite primes. For odd q there is no ramification at infinity either. -/
def UnramifiedAbelianQ (p q : ℕ)
    (J : IntermediateField (F p) Omega) : Prop :=
  FiniteDimensional (F p) J ∧
  IsGalois (F p) J ∧
  (∀ σ τ : J ≃ₐ[F p] J, σ * τ = τ * σ) ∧
  (∀ σ : J ≃ₐ[F p] J, σ ^ q = 1) ∧
  ∀ P : Ideal (𝓞 J), P.IsMaximal → P ≠ ⊥ →
    InertiaTrivial (F p) J P

/-- H is the compositum of all unramified abelian exponent-q
extensions of F. Neither finiteness nor Artin reciprocity is assumed here. -/
def Hsub (p q : ℕ) : IntermediateField (F p) Omega :=
  sSup {J | UnramifiedAbelianQ p q J}

/-- T = H M = H F(zeta_q, E^(1/q)). -/
def Tsub (p q : ℕ) : IntermediateField (F p) Omega :=
  Hsub p q ⊔ Msub p q

/-- The Thaine prime-selection field, as a type. -/
abbrev T (p q : ℕ) := ↥(Tsub p q)

/-- Arithmetic rational Frobenius: x maps to x^ell modulo P.
The selector also requires ell.Prime. The exponent is ell, NOT N(P).
This definition avoids assuming an unavailable bundled Artin-symbol API. -/
def IsArithmeticFrob {L : Type*} [Field L] [CharZero L]
    (ell : ℕ) (P : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L) : Prop :=
  P.IsMaximal ∧ P ≠ ⊥ ∧ (ell : 𝓞 L) ∈ P ∧
  Finite (𝓞 L ⧸ P) ∧
  InertiaTrivial ℚ L P ∧ PreservesPrime σ P ∧
  ∀ x : 𝓞 L, integralAut σ x - x ^ ell ∈ P

/-- The prime-conductor, odd-q hypotheses. -/
structure Admissible (p q : ℕ) : Prop where
  hp : p.Prime
  hq : q.Prime
  hp2 : p ≠ 2
  hq2 : q ≠ 2
  hpq : p ≠ q
  hdegree : ¬ q ∣ (p - 1) / 2

/-- The selectors used by the mod-q proof.
The centralizer restriction weakens the usual all-elements input and
permits the arbitrary-number-field local-global-power argument. -/
structure Selector (p q : ℕ) (σ : T p q ≃ₐ[ℚ] T p q) : Prop where
  fixesBase : ∀ x : T p q, (x : Omega) ∈ Bsub p q → σ x = x
  ne_one : σ ≠ 1
  pow_eq_one : σ ^ q = 1
  centralizer_exponent :
    ∀ τ : T p q ≃ₐ[ℚ] T p q, τ * σ = σ * τ → τ ^ q = 1

end A3

/-- Prime-selection hypothesis: one rational prime per needed selector,
with Frobenius a nonzero power. No density, infinitude, arbitrary finite
avoidance set, or specified generator of the order-q subgroup is required. -/
def DensityInput (p q : ℕ) : Prop :=
  A3.Admissible p q →
  ∀ σ : A3.T p q ≃ₐ[ℚ] A3.T p q, A3.Selector p q σ →
    ∃ ell : ℕ, ell.Prime ∧ ell ≠ p ∧ ell ≠ q ∧
      ∃ P : Ideal (𝓞 (A3.T p q)), ∃ a : ℕ,
        0 < a ∧ a < q ∧ A3.IsArithmeticFrob ell P (σ ^ a)

namespace A3

/-- The choice specification, assuming the standard root-existence fact. -/
theorem primitiveRoot_spec_of_exists (n : ℕ)
    (h : ∃ z : Omega, IsPrimitiveRoot z n) :
    IsPrimitiveRoot (primitiveRoot n) n := by
  exact Classical.epsilon_spec h

/-- Primitive roots exist in the algebraic closure in characteristic zero. -/
theorem primitiveRoot_spec (n : ℕ) (hn : 0 < n) :
    IsPrimitiveRoot (primitiveRoot n) n := by
  apply primitiveRoot_spec_of_exists n
  haveI : NeZero (n : ℚ) := ⟨by exact_mod_cast (Nat.ne_of_gt hn)⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Omega n

/-- Positive residue: this theorem is already in Mathlib v4.33.1. -/
theorem zeta_residue_pos (K : Type*) [Field K] [NumberField K] :
    0 < NumberField.dedekindZeta_residue K := by
  exact NumberField.dedekindZeta_residue_pos K

/-- The required one-sided pole, not global meromorphic continuation. -/
theorem zeta_right_pole (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) * NumberField.dedekindZeta K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (NumberField.dedekindZeta_residue K : ℂ)) := by
  exact NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K

end A3

end Catalan
