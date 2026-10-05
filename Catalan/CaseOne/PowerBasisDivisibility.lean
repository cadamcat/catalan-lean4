module

public import Mathlib

/-!
# `Catalan.CaseOne.PowerBasisDivisibility`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open Polynomial
noncomputable section
namespace Catalan.Primary

lemma powerBasis_dvd_aeval_coeff
    (A : Type*) [CommRing A] [Algebra ℤ A] (pb : PowerBasis ℤ A)
    (f : ℤ[X]) (hf : f.natDegree < pb.dim) (n : ℤ)
    (hdiv : (n : A) ∣ aeval pb.gen f) (i : Fin pb.dim) : n ∣ f.coeff i := by
  cases Subsingleton.elim ‹Algebra ℤ A› (Ring.toIntAlgebra A)
  classical
  obtain ⟨d, hd⟩ := hdiv
  rw [aeval_eq_sum_range' hf, Finset.sum_range] at hd
  have he : (∑ j : Fin pb.dim, f.coeff j • pb.basis j) = n • d := by
    simpa only [pb.basis_eq_pow, zsmul_eq_mul] using hd
  refine ⟨pb.basis.repr d i, ?_⟩
  have hcoord := congrArg (fun t : A => pb.basis.repr t i) he
  simpa only [pb.basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul]
    using hcoord

end Catalan.Primary

