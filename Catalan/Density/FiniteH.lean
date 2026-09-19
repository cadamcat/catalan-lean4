import Catalan.Density.DegreeBound
import Catalan.Density.UnramifiedSup
import Catalan.Density.BoundedSup

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma unramifiedAbelianQ_bot (p q : ℕ) :
    UnramifiedAbelianQ p q (⊥ : IntermediateField (F p) Omega) := by
  have hgal : Subsingleton ((⊥ : IntermediateField (F p) Omega) ≃ₐ[F p]
      (⊥ : IntermediateField (F p) Omega)) := by
    refine ⟨fun σ τ => AlgEquiv.ext fun x => ?_⟩
    obtain ⟨a, rfl⟩ := (IntermediateField.botEquiv (F p) Omega).symm.surjective x
    exact (σ.commutes a).trans (τ.commutes a).symm
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro σ τ
    exact Subsingleton.elim _ _
  · intro σ
    exact Subsingleton.elim _ _
  · intro P hP hPbot σ hpres hinertia
    exact Subsingleton.elim _ _

lemma unramifiedAbelianQ_Hsub (p q : ℕ) (hq : Odd q) :
    UnramifiedAbelianQ p q (Hsub p q) := by
  exact Catalan.FieldTower.sSup_mem_of_bounded_finrank (F p) Omega
    {J | UnramifiedAbelianQ p q J} (NumberField.classNumber (F p))
    ⟨⊥, unramifiedAbelianQ_bot p q⟩
    (fun _ hJ => hJ.1)
    (fun J hJ => Nat.le_of_dvd (NumberField.classNumber_pos (F p))
      (unramifiedAbelianQ_finrank_dvd_classNumber p q hq J hJ))
    (fun A hA B hB => unramifiedAbelianQ_sup p q A B hA hB)

lemma finiteDimensional_Hsub (p q : ℕ) (hq : Odd q) :
    FiniteDimensional (F p) (Hsub p q) :=
  (unramifiedAbelianQ_Hsub p q hq).1

lemma numberField_Hsub (p q : ℕ) (hq : Odd q) : NumberField (Hsub p q) := by
  have instFiniteH : FiniteDimensional (F p) (Hsub p q) := finiteDimensional_Hsub p q hq
  exact NumberField.of_module_finite (F p) (Hsub p q)

lemma Hsub_finrank_dvd_classNumber (p q : ℕ) (hq : Odd q) :
    Module.finrank (F p) (Hsub p q) ∣ NumberField.classNumber (F p) :=
  unramifiedAbelianQ_finrank_dvd_classNumber p q hq (Hsub p q)
    (unramifiedAbelianQ_Hsub p q hq)

end Catalan.A3
