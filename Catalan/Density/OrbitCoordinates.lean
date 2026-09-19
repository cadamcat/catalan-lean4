import Mathlib

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Catalan.Residue

variable (k G : Type*) [Field k] [Group G] [Fintype G]

def sumZero : Submodule k (G → k) :=
  LinearMap.ker (∑ g : G, (LinearMap.proj g : (G → k) →ₗ[k] k))

variable {k G} {V : Type*} [AddCommGroup V] [Module k V]

def inverseOrbitMap (pi : Representation k G V) (f : V →ₗ[k] k) :
    V →ₗ[k] (G → k) := LinearMap.pi (fun g => f.comp (pi g⁻¹))

lemma mem_sumZero (z : G → k) : z ∈ sumZero k G ↔ ∑ g : G, z g = 0 := by
  simp only [sumZero, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply]

lemma inverseOrbitMap_apply (pi : Representation k G V) (f : V →ₗ[k] k)
    (z : V) (g : G) : inverseOrbitMap pi f z g = f (pi g⁻¹ z) := rfl

lemma inverseOrbitMap_equivariant (pi : Representation k G V) (f : V →ₗ[k] k)
    (sigma : G) (z : V) (g : G) :
    inverseOrbitMap pi f (pi sigma z) g = inverseOrbitMap pi f z (sigma⁻¹ * g) := by
  simp only [inverseOrbitMap_apply, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

lemma inverseOrbitMap_range_eq_sumZero [FiniteDimensional k V]
    (pi : Representation k G V) (f : V →ₗ[k] k)
    (hinj : Function.Injective (inverseOrbitMap pi f))
    (hnorm : ∀ z : V, ∑ g : G, pi g z = 0)
    (hdim : Module.finrank k V + 1 = Fintype.card G) :
    LinearMap.range (inverseOrbitMap pi f) = sumZero k G := by
  classical
  have hle : LinearMap.range (inverseOrbitMap pi f) ≤ sumZero k G := by
    rintro _ ⟨z, rfl⟩
    rw [mem_sumZero]
    simp only [inverseOrbitMap_apply]
    rw [← map_sum]
    have hinv : (∑ g : G, pi g⁻¹ z) = ∑ g : G, pi g z :=
      Equiv.sum_comp (Equiv.inv G) (fun g : G => pi g z)
    rw [hinv, hnorm, map_zero]
  let sumMap : (G → k) →ₗ[k] k := ∑ g : G, (LinearMap.proj g : (G → k) →ₗ[k] k)
  have hsurj : Function.Surjective sumMap := by
    intro a
    refine ⟨fun g : G => if g = 1 then a else 0, ?_⟩
    simp [sumMap, LinearMap.sum_apply, LinearMap.proj_apply]
  have hrank := sumMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, CommSemiring.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hrank
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj hinj]
  change Module.finrank k V = Module.finrank k (LinearMap.ker sumMap)
  omega

end Catalan.Residue
