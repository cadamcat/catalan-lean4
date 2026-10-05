module

public import Catalan.Density.ArtinIdele
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin

/-!
# `Catalan.Density.PrimeArtinFormula`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3

lemma classGroupArtinOfEverywhereUnramified_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (hunram : IsEverywhereUnramified K L)
    (v : HeightOneSpectrum (𝓞 K)) :
    classGroupArtinOfEverywhereUnramified K L hunram
      (ClassGroup.mk K (FractionalIdealGroup.prime v)) =
        GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v := by
  rw [← IdeleGroup.idealClass_finitePrimeIdele]
  simpa only [GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin] using
    (classGroupArtinOfEverywhereUnramified_idele K L hunram
      (IdeleGroup.finitePrimeIdele v))

end Catalan.A3
