module

public import Catalan.CaseOne.RepresentationAnnihilator
public import Catalan.CaseOne.MinpolyCyclic
public import Catalan.CaseOne.GeneratorConjugation
public import Catalan.CaseOne.NormSum
public import Catalan.CaseOne.NormIdeal
public import Catalan.CaseOne.GaloisRing
public import Catalan.CaseOne.GeometricUnits
public import Catalan.CaseOne.CyclicVector

/-!
# `Catalan.CaseOne.UnitNorm`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance instGalComm : CommGroup (G p K) := cyclotomicGalCommGroup p K

/-- The actual full-field norm/complex-conjugation ideal over ZMod q. -/
def normPlusIdeal (q : ℕ) : Ideal (MonoidAlgebra (ZMod q) (G p K)) :=
  Ideal.span {UnitReduction.groupNorm (ZMod q) (G p K),
    1 - MonoidAlgebra.single (ι p K) (1 : ZMod q)}

lemma unit_generator_minpoly (q : ℕ) [Fact q.Prime] (hpq : p ≠ q) (hq2 : q ≠ 2)
    (τ : G p K) (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ)
    (hqn : ¬ q ∣ Fintype.card (InfinitePlace K)) :
    minpoly (ZMod q) (unitRepresentation p K q τ) =
      ∑ i ∈ Finset.range (Fintype.card (InfinitePlace K)),
        (Polynomial.X : Polynomial (ZMod q)) ^ i := by
  rw [UnitReduction.minpoly_eq_charpoly_of_polynomial_cyclic (unitRepresentation p K q τ)
    (UnitReduction.exists_cyclic_vector_of_squarefree_charpoly _
      (unit_generator_charpoly_squarefree p K q hpq hq2 τ hτ hqn))]
  exact unit_charpoly_of_generator p K q hpq hq2 τ hτ

lemma unit_annihilator_eq_normPlus (hp2 : 2 < p) (q : ℕ) [Fact q.Prime]
    (hpq : p ≠ q) (hq2 : q ≠ 2) (hqn : ¬ q ∣ Fintype.card (InfinitePlace K)) :
    Module.annihilator (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) =
      normPlusIdeal p K q := by
  classical
  obtain ⟨τ, hτ⟩ := exists_cyclotomic_generator p K
  have h2q : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (Fact.out : q.Prime).ne_one h1
    · exact hq2 h2
  have h2 : IsUnit (2 : MonoidAlgebra (ZMod q) (G p K)) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr h2q).map
      (algebraMap (ZMod q) (MonoidAlgebra (ZMod q) (G p K)))
  have hcard : Nat.card (G p K) = 2 * ((p - 1) / 2) := by
    rw [cyclotomicGal_card]
    obtain ⟨r, hr⟩ := (Fact.out : p.Prime).even_sub_one (by omega)
    omega
  have hnorm : UnitReduction.groupNorm (ZMod q) (G p K) =
      ∑ i ∈ Finset.range (2 * ((p - 1) / 2)), (MonoidAlgebra.single τ (1 : ZMod q)) ^ i := by
    rw [UnitReduction.groupNorm_eq_sum_powers (ZMod q) (G p K) τ hτ, hcard]
  have hiota : (MonoidAlgebra.single τ (1 : ZMod q)) ^ ((p - 1) / 2) =
      MonoidAlgebra.single (ι p K) (1 : ZMod q) := by
    rw [MonoidAlgebra.single_pow, one_pow, generator_half_eq_iota p K hp2 τ hτ]
  rw [UnitReduction.representation_annihilator_eq_span_minpoly (unitRepresentation p K q) τ hτ,
    unit_generator_minpoly p K q hpq hq2 τ hτ hqn, cyclotomicPlace_card p K hp2]
  simp only [map_sum, map_pow, Polynomial.aeval_X]
  rw [UnitReduction.span_geometric_eq_norm_pair _ _ h2, ← hnorm, hiota]
  rfl

lemma unit_annihilator_eq_normPlus_of_solution (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    Module.annihilator (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) =
      normPlusIdeal p K q := by
  have hpq := A1e.solution_primes_ne p q Fact.out Fact.out hp2 hq2 x y hx hy h
  exact unit_annihilator_eq_normPlus p K (by have := (Fact.out : p.Prime).two_le; omega)
    q hpq hq2 (not_dvd_place_card_of_solution p q K hp2 hq2 x y hx hy h)

end Catalan.UnitModule
