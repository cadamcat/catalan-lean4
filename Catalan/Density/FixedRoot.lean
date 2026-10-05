module

public import Catalan.Density.KummerTower
public import Catalan.Density.UnitFieldInjection

/-!
# `Catalan.Density.FixedRoot`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma unit_qth_root_of_all_aut_fix_unitRoot (p q : ℕ) [Fact q.Prime]
    (u : (𝓞 (F p))ˣ)
    (hfix : ∀ σ : Msub p q ≃ₐ[Bsub p q] Msub p q,
      σ (unitRoot p q (Fact.out : q.Prime).pos u) =
        unitRoot p q (Fact.out : q.Prime).pos u) :
    ∃ v : (𝓞 (F p))ˣ, v ^ q = u := by
  have hq : q.Prime := Fact.out
  have instFiniteMB : FiniteDimensional (Bsub p q) (Msub p q) :=
    finiteDimensional_Msub_over_B p q hq.pos
  have instGaloisMB : IsGalois (Bsub p q) (Msub p q) :=
    isGalois_Msub_over_B p q hq.pos
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := Bsub p q) (E := Msub p q) (unitRoot p q hq.pos u)).mpr hfix
  have hbq : b ^ q = algebraMap (F p) (Bsub p q) (((u : 𝓞 (F p)) : F p)) := by
    apply (algebraMap (Bsub p q) (Msub p q)).injective
    rw [map_pow, hb, unitRoot_pow]
    exact IsScalarTower.algebraMap_apply (F p) (Bsub p q) (Msub p q) _
  exact UnitQuotient.unit_qth_root_of_field_qth_root (F p) q hq.pos u
    (UnitQuotient.field_qth_root_of_coprime_degree (F p) (Bsub p q) q
      (coprime_q_finrank_B p q hq) _ ⟨b, hbq⟩)

end Catalan.A3
