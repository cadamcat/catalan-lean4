import Catalan.Thaine.AuxiliaryIntegerData
import Catalan.Stickelberger.Equivariance

set_option autoImplicit false
open NumberField
open scoped Pointwise
noncomputable section
namespace Catalan.Thaine

lemma principal_ideal_fixed_of_integral_coboundary
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (tau : L ≃ₐ[F] L) (eta : (𝓞 L)ˣ) (alpha : 𝓞 L)
    (heq : A3.integralAut tau alpha = (eta : 𝓞 L) * alpha) :
    Ideal.map (A3.integralAut tau).toRingHom (Ideal.span {alpha}) = Ideal.span {alpha} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {A3.integralAut tau alpha} = Ideal.span {alpha}
  rw [heq, Ideal.span_singleton_mul_left_unit eta.isUnit]

lemma principal_ideal_fixed_of_cyclic_coboundary
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (tau : L ≃ₐ[F] L) (hgen : ∀ sigma : L ≃ₐ[F] L, sigma ∈ Subgroup.zpowers tau)
    (eta : (𝓞 L)ˣ) (alpha : 𝓞 L)
    (heq : A3.integralAut tau alpha = (eta : 𝓞 L) * alpha)
    (sigma : L ≃ₐ[F] L) :
    Ideal.map (A3.integralAut sigma).toRingHom (Ideal.span {alpha}) = Ideal.span {alpha} := by
  let S := MulAction.stabilizer (L ≃ₐ[F] L) (Ideal.span {alpha})
  have htau : tau ∈ S := by
    change Ideal.map (A3.integralAut tau).toRingHom (Ideal.span {alpha}) = Ideal.span {alpha}
    exact principal_ideal_fixed_of_integral_coboundary F L tau eta alpha heq
  have hsigma : sigma ∈ S := (Subgroup.zpowers_le.mpr htau) (hgen sigma)
  exact hsigma

lemma principal_multiplicity_constant_of_cyclic_coboundary
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (tau : L ≃ₐ[F] L) (hgen : ∀ sigma : L ≃ₐ[F] L, sigma ∈ Subgroup.zpowers tau)
    (eta : (𝓞 L)ˣ) (alpha : 𝓞 L)
    (heq : A3.integralAut tau alpha = (eta : 𝓞 L) * alpha)
    (sigma : L ≃ₐ[F] L) (P : Ideal (𝓞 L)) :
    emultiplicity (Ideal.map (A3.integralAut sigma).toRingHom P) (Ideal.span {alpha}) =
      emultiplicity P (Ideal.span {alpha}) := by
  have h := Stickelberger.emultiplicity_ideal_map (A3.integralAut sigma) P (Ideal.span {alpha})
  change emultiplicity (Ideal.map (A3.integralAut sigma).toRingHom P)
      (Ideal.map (A3.integralAut sigma).toRingHom (Ideal.span {alpha})) =
        emultiplicity P (Ideal.span {alpha}) at h
  rw [principal_ideal_fixed_of_cyclic_coboundary F L tau hgen eta alpha heq sigma] at h
  exact h

end Catalan.Thaine
