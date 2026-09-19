import Catalan.Runge.Definitions

set_option autoImplicit false
noncomputable section
namespace Catalan.Runge

variable (p : ℕ) (K : Type*) [Field K] [NumberField K]

def reduceFull (q : ℕ) : R p K →+* MonoidAlgebra (ZMod q) (G p K) :=
  MonoidAlgebra.mapRingHom (G p K) (Int.castRingHom (ZMod q))

lemma reduceFull_eq_zero_iff (q : ℕ) (Theta : R p K) :
    reduceFull p K q Theta = 0 ↔ ∀ g : G p K, (q : ℤ) ∣ Theta.coeff g := by
  constructor
  · intro h g
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (Theta.coeff g) q).mp
    have hc := congrArg (fun A : MonoidAlgebra (ZMod q) (G p K) => A.coeff g) h
    simpa only [reduceFull, MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_zero,
      Int.coe_castRingHom, Finsupp.zero_apply] using hc
  · intro h
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro g
    simpa only [reduceFull, MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_zero,
      Int.coe_castRingHom, Finsupp.zero_apply] using (ZMod.intCast_zmod_eq_zero_iff_dvd (Theta.coeff g) q).mpr (h g)

end Catalan.Runge
