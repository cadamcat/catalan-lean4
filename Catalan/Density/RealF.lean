module

public import Catalan.Density.BaseFields

/-!
# `Catalan.Density.RealF`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

local instance instRealFAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega :=
  AlgebraicClosure.isAlgebraic ℚ

lemma isTotallyReal_F (p : ℕ) (hp : 0 < p) : NumberField.IsTotallyReal (F p) := by
  apply (NumberField.isTotallyReal_iff_le_maximalRealSubfield
    (E := (Fsub p).toSubfield)).mpr
  let E : IntermediateField ℚ Omega :=
    (NumberField.maximalRealSubfield Omega).toIntermediateField (fun r => by simp)
  change Fsub p ≤ E
  rw [Fsub, IntermediateField.adjoin_le_iff]
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  change ∀ φ : Omega →+* ℂ,
    star (φ (primitiveRoot p + (primitiveRoot p)⁻¹)) =
      φ (primitiveRoot p + (primitiveRoot p)⁻¹)
  intro φ
  have hpow : (φ (primitiveRoot p)) ^ p = 1 := by
    rw [← map_pow, (primitiveRoot_spec p hp).pow_eq_one, map_one]
  have hnorm : ‖φ (primitiveRoot p)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow (Nat.ne_of_gt hp)
  have hstar : star (φ (primitiveRoot p)) = (φ (primitiveRoot p))⁻¹ :=
    (Complex.inv_eq_conj hnorm).symm
  simp only [map_add, map_inv₀, star_add, star_inv₀, hstar, inv_inv, add_comm]

end Catalan.A3

