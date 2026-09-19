import Catalan.CaseOne.UnitCharpoly

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma cyclotomicGal_cyclic : IsCyclic (G p K) := by
  have hp : p.Prime := Fact.out
  let instNeZeroP : NeZero p := ⟨hp.ne_zero⟩
  exact (IsCyclotomicExtension.Rat.galEquivZMod p K).isCyclic.mpr inferInstance

lemma exists_cyclotomic_generator : ∃ τ : G p K, ∀ σ : G p K, σ ∈ Subgroup.zpowers τ := by
  have instCyclic : IsCyclic (G p K) := cyclotomicGal_cyclic p K
  exact IsCyclic.exists_generator

lemma cyclotomicPlace_card (hp2 : 2 < p) :
    Fintype.card (InfinitePlace K) = (p - 1) / 2 := by
  have hp : p.Prime := Fact.out
  let instNeZeroP : NeZero p := ⟨hp.ne_zero⟩
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K hp2,
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two p K,
    zero_add, Nat.totient_prime hp]

end Catalan.UnitModule
