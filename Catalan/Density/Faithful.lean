module

public import Catalan.Density.PairingValues
public import Catalan.Density.UnitRootExt

/-!
# `Catalan.Density.Faithful`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma kummerPairingHom_injective (p q : ℕ) [Fact q.Prime] :
    Function.Injective (kummerPairingHom p q) := by
  apply (injective_iff_map_eq_one (kummerPairingHom p q)).mpr
  intro σ hσ
  have hζmap : algebraMap (Bsub p q) (Msub p q) (kummerZeta p q) =
      kummerZetaM p q := by
    apply Subtype.ext
    exact algebraMap_Bsub_Msub_coe p q (kummerZeta p q)
  have hζ : σ (kummerZetaM p q) = kummerZetaM p q := by
    rw [← hζmap, σ.commutes]
  have hroots : ∀ u : (NumberField.RingOfIntegers (F p))ˣ,
      σ (unitRoot p q (Fact.out : q.Prime).pos u) =
        unitRoot p q (Fact.out : q.Prime).pos u := by
    intro u
    apply (kummerValue_eq_one_iff p q σ u).mp
    exact DFunLike.congr_fun hσ u
  have heq := unitRoots_algHom_ext p q (Fact.out : q.Prime).pos (Msub p q)
    (σ.toAlgHom.restrictScalars (F p)) (AlgHom.id (F p) (Msub p q)) hζ hroots
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun heq x

end Catalan.A3
