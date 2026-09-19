import Catalan.Runge.BinomialSeries

set_option autoImplicit false
open scoped BigOperators Classical
open NumberField
noncomputable section
namespace Catalan.Runge

lemma sum_bounded_eq_piAntidiag
    {ι R : Type*} [Fintype ι] [AddCommMonoid R] (k : ℕ) (F : (ι → ℕ) → R) :
    (∑ f : ι → Fin (k + 1), if (∑ i, (f i).val) = k then F (fun i => (f i).val) else 0) =
      ∑ f ∈ Finset.piAntidiag Finset.univ k, F f := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun f _ i => (f i).val)
  · intro f hf
    rw [Finset.mem_filter] at hf
    exact Finset.mem_piAntidiag.mpr ⟨hf.2, fun _ _ => Finset.mem_univ _⟩
  · intro f hf g hg h
    funext i
    apply Fin.ext
    exact congr_fun h i
  · intro f hf
    have hsum := (Finset.mem_piAntidiag.mp hf).1
    have hle (i : ι) : f i ≤ k := by
      calc
        f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = k := hsum
    let b : ι → Fin (k + 1) := fun i => ⟨f i, Nat.lt_succ_of_le (hle i)⟩
    refine ⟨b, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsum⟩
  · intro f hf
    rfl

def binomialProductCoeff (ι : Type*) [Fintype ι] (a : ι → ℚ) (w : ι → ℂ) (k : ℕ) : ℂ :=
  ∑ f : ι → Fin (k + 1),
    if (∑ i, (f i).val) = k then
      ∏ i, ((binomRat (a i) (f i).val : ℂ) * w i ^ (f i).val)
    else 0

section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance productCoefficientsGalFintype : Fintype (G p K) := Fintype.ofFinite _

lemma map_rungeCoeff_eq_binomialProductCoeff (q : ℕ) (Theta : R p K) (τ : K →+* ℂ) (k : ℕ) :
    τ (rungeCoeff p K q Theta k) =
      binomialProductCoeff (G p K) (fun g => (Theta.coeff g : ℚ) / (q : ℚ))
        (fun g => -τ (g (ζ p K))) k := by
  simp only [rungeCoeff, binomialProductCoeff, map_sum, apply_ite, map_zero, map_prod, map_mul,
    map_pow, map_neg, RingHom.map_rat_algebraMap]
  rfl

end Cyclotomic
end Catalan.Runge
