import Catalan.Density.PrimeArtinDecomposition
import Catalan.Density.RelativeFrobenius
import Catalan.Density.InertiaBridge

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3
attribute [local instance] integerAutSMulCommClass

lemma zpowers_nativeFrob_eq_zpowers_primeArtin
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (hunram : IsUnramifiedAtFinitePlaces K L) (P : HeightOneSpectrum (𝓞 L))
    (rho : L ≃ₐ[K] L) (hfrob : IsArithFrobAt (𝓞 K) rho P.asIdeal) :
    Subgroup.zpowers rho = Subgroup.zpowers
      (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
        (K := K) (L := L) (finitePlaceBelow (K := K) P)) := by
  have hinertia : InertiaTrivial K L P.asIdeal :=
    (inertiaTrivial_iff_isUnramifiedAt K L P.asIdeal P.ne_bot).mpr (hunram P)
  ext sigma
  exact (preservesPrime_iff_mem_zpowers_of_nativeFrob K L P.asIdeal P.isMaximal P.ne_bot
    rho hinertia hfrob sigma).symm.trans
      (preservesPrime_iff_mem_zpowers_primeArtin K L hunram P sigma)

end Catalan.A3
