module

public import Catalan.CaseOne.CircularUnits
public import Catalan.Runge.PowerTransport

/-!
# `Catalan.Thaine.CircularPowerTransport`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma circular_power_of_reduceFull_eq
    (p q : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (a : Kˣ) (Theta Psi : R p K)
    (heq : Runge.reduceFull p K q Theta = Runge.reduceFull p K q Psi)
    (hPsi : ∃ c : (𝓞 K)ˣ, c ∈ Circular.circularUnits p K ∧ ∃ b : Kˣ,
      upow p K a Psi = Units.map (algebraMap (𝓞 K) K).toMonoidHom c * b ^ q) :
    ∃ c : (𝓞 K)ˣ, c ∈ Circular.circularUnits p K ∧ ∃ b : Kˣ,
      upow p K a Theta = Units.map (algebraMap (𝓞 K) K).toMonoidHom c * b ^ q := by
  obtain ⟨U, hU⟩ := (Runge.reduceFull_eq_iff_exists_nsmul p K q Theta Psi).mp heq
  obtain ⟨c, hc, b, hb⟩ := hPsi
  refine ⟨c, hc, b * upow p K a U, ?_⟩
  rw [hU, upow_add, Runge.upow_nsmul, hb, mul_pow, mul_assoc]

end Catalan.Thaine
