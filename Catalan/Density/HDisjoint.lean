import Catalan.Density.FiniteH
import Catalan.Density.HRelative
import Catalan.Density.Bdegree

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma Hsub_finrank_prime_pow (p q : ℕ) [Fact q.Prime] (hq : Odd q) :
    ∃ n : ℕ, Module.finrank (F p) (Hsub p q) = q ^ n := by
  let instFiniteH : FiniteDimensional (F p) (Hsub p q) := finiteDimensional_Hsub p q hq
  let instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  let instFiniteGal : Finite (Hsub p q ≃ₐ[F p] Hsub p q) :=
    @Fintype.finite _ (AlgEquiv.fintype (F p) (Hsub p q))
  have hP : IsPGroup q (Hsub p q ≃ₐ[F p] Hsub p q) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro σ
    refine ⟨1, ?_⟩
    simpa using Hsub_gal_pow_eq_one p q σ
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  refine ⟨n, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank]
  exact hn

lemma Hsub_Bsub_linearDisjoint (p q : ℕ) [Fact q.Prime] (hq : Odd q) :
    (Hsub p q).LinearDisjoint (Bsub p q) := by
  obtain ⟨n, hn⟩ := Hsub_finrank_prime_pow p q hq
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  rw [hn]
  exact (coprime_q_finrank_B p q Fact.out).pow_left n

lemma Hsub_inf_Bsub (p q : ℕ) [Fact q.Prime] (hq : Odd q) :
    Hsub p q ⊓ Bsub p q = ⊥ := by
  exact (Hsub_Bsub_linearDisjoint p q hq).inf_eq_bot

end Catalan.A3
