module

public import Mathlib

/-!
# `Catalan.Thaine.TotalRamification`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma inertia_and_unique_prime_of_ramification_degree
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsGalois F L]
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver v.asIdeal]
    (he : P.asIdeal.ramificationIdx (𝓞 F) = Module.finrank F L) :
    P.asIdeal.inertiaDeg (𝓞 F) = 1 ∧
      ∀ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal.LiesOver v.asIdeal → Q = P := by
  have htotal := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    v.asIdeal (𝓞 L) (L ≃ₐ[F] L)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.asIdeal (L ≃ₐ[F] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.asIdeal (L ≃ₐ[F] L),
    IsGalois.card_aut_eq_finrank, he] at htotal
  have hdegree : 0 < Module.finrank F L := Module.finrank_pos
  have hcancel : (v.asIdeal.primesOver (𝓞 L)).ncard * P.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    apply mul_right_cancel₀ hdegree.ne'
    calc
      ((v.asIdeal.primesOver (𝓞 L)).ncard * P.asIdeal.inertiaDeg (𝓞 F)) *
          Module.finrank F L =
        (v.asIdeal.primesOver (𝓞 L)).ncard *
          (Module.finrank F L * P.asIdeal.inertiaDeg (𝓞 F)) := by ring
      _ = Module.finrank F L := htotal
      _ = 1 * Module.finrank F L := by rw [one_mul]
  have hcard : (v.asIdeal.primesOver (𝓞 L)).ncard = 1 :=
    Nat.dvd_one.mp ⟨P.asIdeal.inertiaDeg (𝓞 F), hcancel.symm⟩
  have hf : P.asIdeal.inertiaDeg (𝓞 F) = 1 := by simpa only [hcard, one_mul] using hcancel
  refine ⟨hf, ?_⟩
  intro Q hQ
  obtain ⟨J, hJ⟩ := Set.ncard_eq_one.mp hcard
  have hPmem : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) := ⟨P.isPrime, inferInstance⟩
  have hQmem : Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) := ⟨Q.isPrime, hQ⟩
  rw [hJ, Set.mem_singleton_iff] at hPmem hQmem
  exact HeightOneSpectrum.ext (hQmem.trans hPmem.symm)

lemma residue_card_eq_of_inertia_one
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver v.asIdeal] (hf : P.asIdeal.inertiaDeg (𝓞 F) = 1) :
    Nat.card (𝓞 L ⧸ P.asIdeal) = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  let totalResidueFieldBase : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let totalResidueFieldTop : Field (𝓞 L ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  have hdim : Module.finrank (𝓞 F ⧸ v.asIdeal) (𝓞 L ⧸ P.asIdeal) = 1 := by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal P.asIdeal]
    exact hf
  have hbij : Function.Bijective (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 L ⧸ P.asIdeal)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdim
  exact (Nat.card_congr (Equiv.ofBijective
    (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 L ⧸ P.asIdeal)) hbij)).symm

end Catalan.Thaine
