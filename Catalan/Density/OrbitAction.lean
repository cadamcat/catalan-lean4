import Catalan.Density.OrbitCoordinates

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Catalan.Residue
variable {k G V : Type*} [Field k] [Group G] [Fintype G]
  [AddCommGroup V] [Module k V]

lemma inverseOrbitMap_algebra_action (pi : Representation k G V) (f : V →ₗ[k] k)
    (Theta : MonoidAlgebra k G) (z : V) (g : G) :
    inverseOrbitMap pi f (pi.asAlgebraHom Theta z) g =
      ∑ h : G, Theta.coeff h * inverseOrbitMap pi f z (h⁻¹ * g) := by
  classical
  refine MonoidAlgebra.induction_linear Theta ?_ ?_ ?_
  · simp [inverseOrbitMap_apply]
  · intro Theta Psi hTheta hPsi
    calc
      inverseOrbitMap pi f (pi.asAlgebraHom (Theta + Psi) z) g =
          inverseOrbitMap pi f ((pi.asAlgebraHom Theta) z +
            (pi.asAlgebraHom Psi) z) g := by
          rw [map_add]
          rfl
      _ = inverseOrbitMap pi f ((pi.asAlgebraHom Theta) z) g +
          inverseOrbitMap pi f ((pi.asAlgebraHom Psi) z) g := by
        rw [LinearMap.map_add]
        rfl
      _ = (∑ h : G, Theta.coeff h * inverseOrbitMap pi f z (h⁻¹ * g)) +
          ∑ h : G, Psi.coeff h * inverseOrbitMap pi f z (h⁻¹ * g) := by
        rw [hTheta, hPsi]
      _ = ∑ h : G, (Theta + Psi).coeff h *
          inverseOrbitMap pi f z (h⁻¹ * g) := by
        rw [MonoidAlgebra.coeff_add]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro h hh
        simp only [Finsupp.add_apply]
        ring
  · intro h m
    rw [Representation.asAlgebraHom_single]
    simp [inverseOrbitMap_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]

lemma inverseOrbitMap_canonical_action (pi : Representation k G V) (f : V →ₗ[k] k)
    (z : V) (b : k)
    (hz : ∀ g : G, inverseOrbitMap pi f z g = (1 : MonoidAlgebra k G).coeff g - b)
    (Theta : MonoidAlgebra k G) (g : G) :
    inverseOrbitMap pi f (pi.asAlgebraHom Theta z) g =
      Theta.coeff g - (∑ h : G, Theta.coeff h) * b := by
  classical
  rw [inverseOrbitMap_algebra_action pi f Theta z g]
  simp_rw [hz]
  have hdelta (x : G) :
      (1 : MonoidAlgebra k G).coeff (x⁻¹ * g) = if x = g then 1 else 0 := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single]
    by_cases hx : x = g
    · subst x
      simp
    · have hneq : ¬ (1 : G) = x⁻¹ * g := by
        intro h
        apply hx
        have h' := congrArg (fun y : G => x * y) h
        simpa [mul_assoc] using h'
      rw [Finsupp.single_apply, if_neg hneq, if_neg hx]
  simp_rw [mul_sub, Finset.sum_sub_distrib, hdelta]
  simp_rw [mul_ite]
  simp [Finset.sum_mul]

end Catalan.Residue
