import Catalan.Density.Definitions

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma all_integral_automorphisms_trivial_mod_prime
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsGalois F L]
    (P : HeightOneSpectrum (𝓞 L))
    (he : P.asIdeal.ramificationIdx (𝓞 F) = Module.finrank F L) :
    ∀ sigma : L ≃ₐ[F] L, A3.PreservesPrime sigma P.asIdeal ∧
      ∀ x : 𝓞 L, A3.integralAut sigma x - x ∈ P.asIdeal := by
  have hcard : Nat.card (P.asIdeal.inertia (L ≃ₐ[F] L)) = Nat.card (L ≃ₐ[F] L) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[F] L)
        (P.asIdeal.under (𝓞 F)) P.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.asIdeal.under (𝓞 F)) P.asIdeal (L ≃ₐ[F] L),
      he, IsGalois.card_aut_eq_finrank]
  have htop : P.asIdeal.inertia (L ≃ₐ[F] L) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ hcard
  intro sigma
  have hmem : sigma ∈ P.asIdeal.inertia (L ≃ₐ[F] L) := by rw [htop]; trivial
  change ∀ x : 𝓞 L, A3.integralAut sigma x - x ∈ P.asIdeal at hmem
  refine ⟨?_, hmem⟩
  intro x
  constructor
  · intro hx
    simpa only [sub_sub_cancel] using P.asIdeal.sub_mem hx (hmem x)
  · intro hx
    simpa only [sub_add_cancel] using P.asIdeal.add_mem (hmem x) hx

end Catalan.Thaine
