module

public import Catalan.CaseOne.CyclotomicPlaces

/-!
# `Catalan.CaseOne.GeneratorConjugation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma gal_generator_order (τ : G p K) (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ) :
    orderOf τ = p - 1 := by
  let instGalois : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  rw [orderOf_eq_card_of_forall_mem_zpowers hτ, IsGalois.card_aut_eq_finrank,
    cyclotomic_degree p K]

lemma generator_half_eq_iota (hp2 : 2 < p) (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ) :
    τ ^ ((p - 1) / 2) = ι p K := by
  let instNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let e := IsCyclotomicExtension.Rat.galEquivZMod p K
  have hne : τ ^ ((p - 1) / 2) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · omega
    · rw [gal_generator_order p K τ hτ]
      omega
  have hvalne : ((e τ : (ZMod p)ˣ) : ZMod p) ^ ((p - 1) / 2) ≠ 1 := by
    intro hval
    apply hne
    apply e.injective
    rw [map_pow, map_one]
    exact Units.ext hval
  have hodd : p % 2 = 1 :=
    (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)
  have hhalf : p / 2 = (p - 1) / 2 := by omega
  have hval : ((e τ : (ZMod p)ˣ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have h := ZMod.pow_div_two_eq_neg_one_or_one p (Units.ne_zero (e τ))
    rw [hhalf] at h
    exact h.resolve_left hvalne
  have hiota : e (ι p K) = (-1 : (ZMod p)ˣ) := by
    change e (e.symm (-1)) = -1
    exact e.apply_symm_apply _
  apply e.injective
  rw [map_pow, hiota]
  exact Units.ext hval

end Catalan.UnitModule
