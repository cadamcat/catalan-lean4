module

public import Catalan.Density.FiniteH
public import Catalan.Density.TTower

/-!
# `Catalan.Density.FiniteT`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma finiteDimensional_T_over_F (p q : ℕ) (hq : Odd q) :
    FiniteDimensional (F p) (T p q) := by
  have instFiniteH : FiniteDimensional (F p) (Hsub p q) := finiteDimensional_Hsub p q hq
  have instFiniteM : FiniteDimensional (F p) (Msub p q) := finiteDimensional_Msub p q hq.pos
  exact IntermediateField.finiteDimensional_sup (Hsub p q) (Msub p q)

lemma finiteDimensional_T_over_B (p q : ℕ) (hq : Odd q) :
    FiniteDimensional (Bsub p q) (T p q) := by
  have instFiniteT : FiniteDimensional (F p) (T p q) := finiteDimensional_T_over_F p q hq
  exact FiniteDimensional.right (F p) (Bsub p q) (T p q)

lemma numberField_T (p q : ℕ) (hq : Odd q) : NumberField (T p q) := by
  have instFiniteT : FiniteDimensional (F p) (T p q) := finiteDimensional_T_over_F p q hq
  exact NumberField.of_module_finite (F p) (T p q)

end Catalan.A3
