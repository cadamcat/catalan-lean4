import Catalan.Density.AbsoluteH
import Catalan.Density.AbsoluteM

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma isGalois_T_rat (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    IsGalois ℚ (T p q) := by
  have instGaloisH : IsGalois ℚ (Hsub p q) := isGalois_Hsub_rat p q hp
  have instGaloisM : IsGalois ℚ (Msub p q) := isGalois_Msub_rat p q hp hq
  have instNormalH : Normal ℚ ((Hsub p q).restrictScalars ℚ) := instGaloisH.to_normal
  have instNormalM : Normal ℚ ((Msub p q).restrictScalars ℚ) := instGaloisM.to_normal
  have instNormalT : Normal ℚ (T p q) := by
    change Normal ℚ ((Tsub p q).restrictScalars ℚ)
    rw [Tsub, ← IntermediateField.restrictScalars_sup]
    exact @IntermediateField.normal_sup ℚ Omega _ _ _
      ((Hsub p q).restrictScalars ℚ) ((Msub p q).restrictScalars ℚ) instNormalH instNormalM
  exact {}

end Catalan.A3
