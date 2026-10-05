module

public import Catalan.CaseOne.CyclicVector
public import Catalan.CaseOne.RepresentationCyclic
public import Catalan.CaseOne.GeometricUnits

/-!
# `Catalan.CaseOne.UnitCyclic`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma unit_module_cyclic (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hqn : ¬ q ∣ Fintype.card (InfinitePlace K)) :
    ∃ v : UnitPowerModule p K q, Function.Surjective
      (LinearMap.toSpanSingleton (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) v) := by
  obtain ⟨τ, hτ⟩ := exists_cyclotomic_generator p K
  apply UnitReduction.representation_cyclic_of_polynomial_cyclic (unitRepresentation p K q) τ
  exact UnitReduction.exists_cyclic_vector_of_squarefree_charpoly (unitRepresentation p K q τ)
    (unit_generator_charpoly_squarefree p K q hpq hq2 τ hτ hqn)

lemma unit_module_cyclic_of_solution (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    ∃ v : UnitPowerModule p K q, Function.Surjective
      (LinearMap.toSpanSingleton (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) v) := by
  obtain ⟨τ, hτ⟩ := exists_cyclotomic_generator p K
  apply UnitReduction.representation_cyclic_of_polynomial_cyclic (unitRepresentation p K q) τ
  exact UnitReduction.exists_cyclic_vector_of_squarefree_charpoly (unitRepresentation p K q τ)
    (unit_generator_charpoly_squarefree_of_solution p K q hp2 hq2 x y hx hy h τ hτ)

end Catalan.UnitModule
