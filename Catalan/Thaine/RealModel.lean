module

public import Catalan.Density.BaseFields
public import Catalan.Cyclotomic.Basic

/-!
# `Catalan.Thaine.RealModel`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

lemma real_model_transport
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] :
    let R := IntermediateField.adjoin ℚ ({ζ p K + (ζ p K)⁻¹} : Set K)
    ∃ (j : K →ₐ[ℚ] A3.Omega) (e : R ≃ₐ[ℚ] A3.F p),
      j (ζ p K) = A3.primitiveRoot p ∧
      ∀ x : R, algebraMap (A3.F p) A3.Omega (e x) = j (x : K) := by
  classical
  have hp : p.Prime := Fact.out
  have instNeZeroP : NeZero p := ⟨hp.ne_zero⟩
  let R := IntermediateField.adjoin ℚ ({ζ p K + (ζ p K)⁻¹} : Set K)
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) := Polynomial.cyclotomic.irreducible_rat hp.pos
  let E : (K →ₐ[ℚ] A3.Omega) ≃ primitiveRoots p A3.Omega :=
    (ζ_spec p K).embeddingsEquivPrimitiveRoots A3.Omega hirr
  let r : primitiveRoots p A3.Omega :=
    ⟨A3.primitiveRoot p, (mem_primitiveRoots hp.pos).mpr (A3.primitiveRoot_spec p hp.pos)⟩
  let j : K →ₐ[ℚ] A3.Omega := E.symm r
  have hj : j (ζ p K) = A3.primitiveRoot p := by
    have hroot := congrArg (fun z : primitiveRoots p A3.Omega => (z : A3.Omega))
      (E.apply_symm_apply r)
    change (E j : A3.Omega) = A3.primitiveRoot p at hroot
    exact ((ζ_spec p K).embeddingsEquivPrimitiveRoots_apply_coe A3.Omega hirr j).symm.trans hroot
  have hR : R.map j = A3.Fsub p := by
    dsimp only [R, A3.Fsub]
    rw [IntermediateField.adjoin_map]
    simp only [Set.image_singleton, map_add, map_inv₀, hj]
  let e : R ≃ₐ[ℚ] A3.F p :=
    (R.equivMap j).trans (IntermediateField.equivOfEq hR)
  refine ⟨j, e, hj, ?_⟩
  intro x
  change ((R.equivMap j x : R.map j) : A3.Omega) = j (x : K)
  exact IntermediateField.coe_equivMap_apply R j x

end Catalan.Thaine
