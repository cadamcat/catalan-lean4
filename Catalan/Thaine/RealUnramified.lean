module

public import Catalan.Thaine.AuxiliaryGenerator
public import Catalan.Density.FStructure

/-!
# `Catalan.Thaine.RealUnramified`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma isCyclotomicExtension_Bsub_self_rat (p : ℕ) (hp : 0 < p) :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := by
  have realUnramifiedNeZeroP : NeZero p := ⟨hp.ne'⟩
  have realUnramifiedOmegaAlgebraic : Algebra.IsAlgebraic ℚ A3.Omega :=
    AlgebraicClosure.isAlgebraic ℚ
  let C : IntermediateField ℚ A3.Omega := IntermediateField.adjoin ℚ {A3.primitiveRoot p}
  have hFC : A3.Fsub p ≤ C := by
    rw [A3.Fsub, IntermediateField.adjoin_le_iff]
    rintro x (rfl : x = _)
    have hz : A3.primitiveRoot p ∈ C := IntermediateField.subset_adjoin ℚ _ (by simp)
    exact C.add_mem hz (C.inv_mem hz)
  have hBC : (A3.Bsub p p).restrictScalars ℚ = C := by
    calc
      (A3.Bsub p p).restrictScalars ℚ = A3.Fsub p ⊔ C :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ (A3.Fsub p) {A3.primitiveRoot p}
      _ = C := sup_eq_right.mpr hFC
  have hC : IsCyclotomicExtension {p} ℚ C :=
    (A3.primitiveRoot_spec p hp).intermediateField_adjoin_isCyclotomicExtension ℚ
  change IsCyclotomicExtension {p} ℚ ((A3.Bsub p p).restrictScalars ℚ)
  rw [hBC]
  exact hC

lemma real_prime_ramification_one
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (v : HeightOneSpectrum (𝓞 (A3.F p))) (hellv : (ell : 𝓞 (A3.F p)) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 := by
  have hp : p.Prime := Fact.out
  have hell : ell.Prime := Fact.out
  have realPrimeUnramifiedNeZeroP : NeZero p := ⟨hp.ne_zero⟩
  have realPrimeUnramifiedCycloB : IsCyclotomicExtension {p} ℚ (A3.Bsub p p) :=
    isCyclotomicExtension_Bsub_self_rat p hp.pos
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (A3.Bsub p p)) v.asIdeal
  have realPrimeUnramifiedMaxP : P.IsMaximal := hP
  have realPrimeUnramifiedOverV : P.LiesOver v.asIdeal := hPv
  have hellP : (ell : 𝓞 (A3.Bsub p p)) ∈ P := by
    simpa only [map_natCast] using (Ideal.mem_of_liesOver P v.asIdeal _).mp hellv
  have realPrimeUnramifiedOverEll : P.LiesOver (Ideal.span {(ell : ℤ)}) := by
    apply (Ideal.liesOver_span_iff hP.ne_top (Nat.prime_iff_prime_int.mp hell)).mpr
    simpa only [map_natCast] using hellP
  have hnot : ¬ ell ∣ p := by
    intro hdiv
    exact hpe ((Nat.prime_dvd_prime_iff_eq hell hp).mp hdiv).symm
  have hPindex : P.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd ell (A3.Bsub p p) P hnot
  have hdiv : v.asIdeal.ramificationIdx ℤ ∣ P.ramificationIdx ℤ :=
    Ideal.ramificationIdx_below_dvd (R := ℤ) v.asIdeal P
  rw [hPindex] at hdiv
  exact Nat.dvd_one.mp hdiv

end Catalan.Thaine
