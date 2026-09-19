import Catalan.CaseOne.PlaceCharpoly
import Catalan.CaseOne.CyclotomicPlaces
import Catalan.CaseOne.GeometricSquarefree
import Catalan.CaseOne.CaseTwoCard
import Catalan.Wieferich.Arithmetic

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma unit_charpoly_of_generator (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2)
    (τ : G p K) (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ) :
    (unitRepresentation p K q τ).charpoly =
      ∑ i ∈ Finset.range (Fintype.card (InfinitePlace K)),
        (Polynomial.X : Polynomial (ZMod q)) ^ i := by
  have instGalois : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  rw [unitRepresentation_charpoly p K q hpq hq2 τ, integralUnit_charpoly_of_generator p K τ hτ]
  simp only [Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X]

lemma unit_charpoly_halfdegree (hp2 : 2 < p) (q : ℕ) [Fact q.Prime]
    (hpq : p ≠ q) (hq2 : q ≠ 2) (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ) :
    (unitRepresentation p K q τ).charpoly =
      ∑ i ∈ Finset.range ((p - 1) / 2), (Polynomial.X : Polynomial (ZMod q)) ^ i := by
  rw [unit_charpoly_of_generator p K q hpq hq2 τ hτ, cyclotomicPlace_card p K hp2]

lemma unit_generator_charpoly_squarefree (q : ℕ) [Fact q.Prime]
    (hpq : p ≠ q) (hq2 : q ≠ 2) (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ)
    (hqn : ¬ q ∣ Fintype.card (InfinitePlace K)) :
    Squarefree (unitRepresentation p K q τ).charpoly := by
  rw [unit_charpoly_of_generator p K q hpq hq2 τ hτ]
  exact UnitReduction.geometricSum_squarefree q _ hqn

lemma unit_generator_isSemisimple (q : ℕ) [Fact q.Prime]
    (hpq : p ≠ q) (hq2 : q ≠ 2) (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ)
    (hqn : ¬ q ∣ Fintype.card (InfinitePlace K)) :
    Module.End.IsSemisimple (unitRepresentation p K q τ) := by
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (unit_generator_charpoly_squarefree p K q hpq hq2 τ hτ hqn)
    (LinearMap.aeval_self_charpoly _)

lemma unit_generator_charpoly_squarefree_of_solution (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ) :
    Squarefree (unitRepresentation p K q τ).charpoly := by
  have hpq := A1e.solution_primes_ne p q Fact.out Fact.out hp2 hq2 x y hx hy h
  exact unit_generator_charpoly_squarefree p K q hpq hq2 τ hτ
    (not_dvd_place_card_of_solution p q K hp2 hq2 x y hx hy h)

lemma unit_generator_isSemisimple_of_solution (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ) :
    Module.End.IsSemisimple (unitRepresentation p K q τ) := by
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (unit_generator_charpoly_squarefree_of_solution p K q hp2 hq2 x y hx hy h τ hτ)
    (LinearMap.aeval_self_charpoly _)

end Catalan.UnitModule
