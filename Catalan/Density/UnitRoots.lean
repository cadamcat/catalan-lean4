module

public import Catalan.Density.NormalM
public import Catalan.Density.FiniteM

/-!
# `Catalan.Density.UnitRoots`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

/-- The chosen cyclotomic root in the literal Kummer base field. -/
def kummerZeta (p q : ℕ) : Bsub p q :=
  ⟨primitiveRoot q, IntermediateField.subset_adjoin (F p) _ (by simp)⟩

lemma kummerZeta_spec (p q : ℕ) (hq : 0 < q) : IsPrimitiveRoot (kummerZeta p q) q := by
  apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
  exact primitiveRoot_spec q hq

/-- The same chosen root in the literal multi-unit extension. -/
def kummerZetaM (p q : ℕ) : Msub p q :=
  ⟨primitiveRoot q, (show Bsub p q ≤ Msub p q from le_sup_left)
    (IntermediateField.subset_adjoin (F p) _ (by simp))⟩

lemma kummerZetaM_spec (p q : ℕ) (hq : 0 < q) :
    IsPrimitiveRoot (kummerZetaM p q) q := by
  apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
  exact primitiveRoot_spec q hq

lemma exists_unitRoot_M (p q : ℕ) (hq : 0 < q) (u : (NumberField.RingOfIntegers (F p))ˣ) :
    ∃ r : Msub p q, r ^ q = algebraMap (F p) (Msub p q)
      (((u : NumberField.RingOfIntegers (F p)) : F p)) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (F p) Omega (((u : NumberField.RingOfIntegers (F p)) : F p))) hq
  have hrmem : r ∈ Msub p q :=
    (show IntermediateField.adjoin (F p) (unitRadicals p q) ≤ Msub p q from le_sup_right)
      (IntermediateField.subset_adjoin (F p) _ ⟨u, hr⟩)
  refine ⟨⟨r, hrmem⟩, ?_⟩
  exact Subtype.ext hr

/-- A root of each actual integral unit, chosen inside the literal field M. -/
def unitRoot (p q : ℕ) (hq : 0 < q) (u : (NumberField.RingOfIntegers (F p))ˣ) : Msub p q :=
  Classical.choose (exists_unitRoot_M p q hq u)

lemma unitRoot_pow (p q : ℕ) (hq : 0 < q) (u : (NumberField.RingOfIntegers (F p))ˣ) :
    unitRoot p q hq u ^ q = algebraMap (F p) (Msub p q)
      (((u : NumberField.RingOfIntegers (F p)) : F p)) :=
  Classical.choose_spec (exists_unitRoot_M p q hq u)

lemma unitRoot_ne_zero (p q : ℕ) (hq : 0 < q) (u : (NumberField.RingOfIntegers (F p))ˣ) :
    unitRoot p q hq u ≠ 0 := by
  intro hz
  have h := unitRoot_pow p q hq u
  rw [hz, zero_pow hq.ne'] at h
  have hF : ((u : NumberField.RingOfIntegers (F p)) : F p) = 0 :=
    (algebraMap (F p) (Msub p q)).injective (by simpa using h.symm)
  exact Units.ne_zero u (NumberField.RingOfIntegers.coe_injective hF)

end Catalan.A3
