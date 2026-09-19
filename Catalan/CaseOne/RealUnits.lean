import Catalan.CaseOne.RealTorsion
import Catalan.CaseOne.PlaceCharpoly
import Catalan.CaseOne.GeometricSquarefree
import Catalan.CaseOne.CyclicVector
import Catalan.CaseOne.MinpolyCyclic

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
variable (p : ℕ) (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

lemma real_unitReductionMap_bijective (q : ℕ) (hq : Odd q) :
    Function.Bijective (unitReductionMap K q) :=
  unitReductionMap_bijective_of_torsion_le K q
    (UnitQuotient.real_torsion_le_qPowers K q hq)

lemma real_unitRepresentation_charpoly (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (τ : G p K) :
    (unitRepresentation p K q τ).charpoly =
      (integralUnitRepresentation p K τ).charpoly.map (Int.castRingHom (ZMod q)) :=
  unitRepresentation_charpoly_of_torsion_le p K q
    (UnitQuotient.real_torsion_le_qPowers K q hq) τ

lemma real_unit_charpoly_of_generator [IsGalois ℚ K]
    (q : ℕ) [Fact q.Prime] (hq : Odd q) (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ) :
    (unitRepresentation p K q τ).charpoly =
      ∑ i ∈ Finset.range (Fintype.card (InfinitePlace K)),
        (Polynomial.X : Polynomial (ZMod q)) ^ i := by
  rw [real_unitRepresentation_charpoly p K q hq τ,
    integralUnit_charpoly_of_generator p K τ hτ]
  simp only [Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X]

lemma real_unit_minpoly_of_generator [IsGalois ℚ K]
    (q : ℕ) [Fact q.Prime] (hq : Odd q) (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ)
    (hqn : ¬ q ∣ Fintype.card (InfinitePlace K)) :
    minpoly (ZMod q) (unitRepresentation p K q τ) =
      ∑ i ∈ Finset.range (Fintype.card (InfinitePlace K)),
        (Polynomial.X : Polynomial (ZMod q)) ^ i := by
  have hchar := real_unit_charpoly_of_generator p K q hq τ hτ
  have hsf : Squarefree (unitRepresentation p K q τ).charpoly := by
    rw [hchar]
    exact UnitReduction.geometricSum_squarefree q _ hqn
  rw [UnitReduction.minpoly_eq_charpoly_of_polynomial_cyclic _
    (UnitReduction.exists_cyclic_vector_of_squarefree_charpoly _ hsf), hchar]

end Catalan.UnitModule
