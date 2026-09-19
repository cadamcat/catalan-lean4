import Catalan.Density.KummerCovariance
import Catalan.Density.ScalarFixed

set_option autoImplicit false
noncomputable section
namespace Catalan.A3
variable (p q : ℕ)

lemma fixes_B_of_restrictToF_eq_one_of_zeta_fixed (hp : 0 < p)
    (σ : Msub p q ≃ₐ[ℚ] Msub p q)
    (hF : restrictToF p q hp σ = 1)
    (hζ : σ (kummerZetaM p q) = kummerZetaM p q) :
    ∀ b : Bsub p q, σ (algebraMap (Bsub p q) (Msub p q) b) =
      algebraMap (Bsub p q) (Msub p q) b := by
  have hFmap (a : F p) : σ (algebraMap (F p) (Msub p q) a) =
      algebraMap (F p) (Msub p q) a := by
    rw [← restrictToF_commutes p q hp σ a, hF]
    rfl
  let φ : Bsub p q →ₐ[F p] Msub p q :=
    { toRingHom := σ.toRingHom.comp (algebraMap (Bsub p q) (Msub p q))
      commutes' a := by
        change σ (algebraMap (Bsub p q) (Msub p q)
          (algebraMap (F p) (Bsub p q) a)) = algebraMap (F p) (Msub p q) a
        rw [← IsScalarTower.algebraMap_apply, hFmap] }
  let ψ : Bsub p q →ₐ[F p] Msub p q :=
    IsScalarTower.toAlgHom (F p) (Bsub p q) (Msub p q)
  have hζmap : algebraMap (Bsub p q) (Msub p q) (kummerZeta p q) =
      kummerZetaM p q := by
    apply Subtype.ext
    exact algebraMap_Bsub_Msub_coe p q (kummerZeta p q)
  have hφ : φ = ψ := by
    apply IntermediateField.adjoin_algHom_ext (F p)
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change σ (algebraMap (Bsub p q) (Msub p q) (kummerZeta p q)) =
      algebraMap (Bsub p q) (Msub p q) (kummerZeta p q)
    rw [hζmap]
    exact hζ
  intro b
  exact DFunLike.congr_fun hφ b

variable [Fact q.Prime]

lemma cyclotomicScalar_eq_one_iff (σ : Msub p q ≃ₐ[ℚ] Msub p q) :
    cyclotomicScalar p q σ = 1 ↔ σ (kummerZetaM p q) = kummerZetaM p q := by
  exact Kummer.rootCoordinateScalar_eq_one_iff (Msub p q) q (kummerZetaUnitM p q)
    (kummerZetaUnitM_spec p q) σ.toRingEquiv

lemma abs_pow_eq_one_of_restrictToF_eq_one_of_scalar_eq_one (hp : 0 < p)
    (σ : Msub p q ≃ₐ[ℚ] Msub p q) (hF : restrictToF p q hp σ = 1)
    (hχ : cyclotomicScalar p q σ = 1) : σ ^ q = 1 := by
  let τ : Msub p q ≃ₐ[Bsub p q] Msub p q :=
    { toRingEquiv := σ.toRingEquiv
      commutes' := fixes_B_of_restrictToF_eq_one_of_zeta_fixed p q hp σ hF
        ((cyclotomicScalar_eq_one_iff p q σ).mp hχ) }
  have hτ : τ.restrictScalars ℚ = σ := by
    ext x
    rfl
  have h := congrArg (AlgEquiv.restrictScalarsHom ℚ) (kummerGal_pow_eq_one p q τ)
  simpa only [map_pow, map_one, AlgEquiv.restrictScalarsHom_apply, hτ] using h

end Catalan.A3
