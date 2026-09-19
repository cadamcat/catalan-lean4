import Catalan.Thaine.ThainePrimeAnnihilator
import Catalan.Density.AugmentationPrimeClasses

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma real_unit_annihilator_kills_class_quotient
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (Theta : R p (A3.F p)) (hTheta : realUnitAnnihilator p q Theta)
    (z : UnitQuotient.PowerQuotient (ClassGroup (𝓞 (A3.F p))) q) :
    (classRepresentation (A3.F p) q).asAlgebraHom (Runge.reduceFull p (A3.F p) q Theta) z = 0 := by
  let T := (classRepresentation (A3.F p) q).asAlgebraHom (Runge.reduceFull p (A3.F p) q Theta)
  have hker : ⊤ ≤ LinearMap.ker T := by
    rw [← A3.augmentationPrimeClasses_span p q hp7 hq2 hdegree (∅ : Finset ℕ)]
    apply Submodule.span_le.mpr
    intro c hc
    obtain ⟨ell, v, red, s, e, u, hell, _, hpe, _, hql, hmod, hcard, hsurj, hred,
      _, hs, hse, _, hu, hc⟩ := hc
    have thaineClassEllPrime : Fact ell.Prime := ⟨hell⟩
    subst c
    exact real_unit_annihilator_kills_prime p q ell (by omega) hq2 hpe.symm hql hmod
      v hcard red hsurj hred e s hs hse u _ hu Theta hTheta
  exact hker (Submodule.mem_top : z ∈ (⊤ : Submodule (ZMod q) _))

end Catalan.Thaine
