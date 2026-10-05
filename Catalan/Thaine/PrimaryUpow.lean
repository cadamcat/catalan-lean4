module

public import Catalan.Thaine.PrimaryLocalizedPowers
public import Catalan.Thaine.LocalizedPrimaryCriterion

/-!
# `Catalan.Thaine.PrimaryUpow`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma primary_of_upow_eq_unit_mul_pow
    (p q : ℕ) (hq : 0 < q) (K : Type*) [Field K] [NumberField K]
    (a : Kˣ) (s : 𝓞 K) (hs : (s : K) = (a : K))
    (hsmod : ∀ g : G p K, (q : 𝓞 K) ^ 2 ∣ integerAut K g s - 1)
    (Theta : R p K) (c : (𝓞 K)ˣ) (b : Kˣ)
    (hpower : upow p K a Theta = Units.map (algebraMap (𝓞 K) K).toMonoidHom c * b ^ q) :
    c ∈ UnitQuotient.primaryUnits (𝓞 K) q := by
  have primaryUpowClosed : IsIntegrallyClosed (primaryLocalization (𝓞 K) K q) :=
    primaryLocalizationClosed (𝓞 K) K q
  have primaryUpowFractionRing : IsFractionRing (primaryLocalization (𝓞 K) K q) K :=
    Localization.subalgebra.isFractionRing_ofField K (primaryDenominators (𝓞 K) q) inf_le_right
  obtain ⟨v, hv, hres⟩ := exists_primary_localized_upow p q K a s hs hsmod Theta
  exact primary_of_localized_unit_power (𝓞 K) (primaryLocalization (𝓞 K) K q) K q hq
    (primaryLocalizationResidue (𝓞 K) K q) (primaryLocalizationResidue_algebraMap (𝓞 K) K q)
    v c b (hv.trans hpower) hres

end Catalan.Thaine
