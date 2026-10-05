module

public import Catalan.Density.PairingDual
public import Catalan.Density.Faithful

/-!
# `Catalan.Density.DualLeft`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma kummerDualHom_injective (p q : ℕ) [Fact q.Prime] :
    Function.Injective (kummerDualHom p q) := by
  apply (injective_iff_map_eq_one (kummerDualHom p q)).mpr
  intro σ hσ
  have hzero : kummerFunctional p q σ = 0 := hσ
  apply kummerPairingHom_injective p q
  rw [map_one]
  apply MonoidHom.ext
  intro u
  change kummerValue p q σ u = 1
  apply (kummerFunctional_apply_eq_zero_iff p q σ u).mp
  exact DFunLike.congr_fun hzero (UnitQuotient.powerClass q u)

end Catalan.A3
