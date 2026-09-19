import Catalan.Density.UnitRoots

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma unitRoots_algHom_ext (p q : ℕ) (hq : 0 < q)
    (L : Type*) [Field L] [Algebra (F p) L]
    (φ ψ : Msub p q →ₐ[F p] L)
    (hζ : φ (kummerZetaM p q) = ψ (kummerZetaM p q))
    (hroots : ∀ u : (NumberField.RingOfIntegers (F p))ˣ,
      φ (unitRoot p q hq u) = ψ (unitRoot p q hq u)) :
    φ = ψ := by
  have instNeZeroQ : NeZero q := ⟨hq.ne'⟩
  have hM : Msub p q = IntermediateField.adjoin (F p)
      ({primitiveRoot q} ∪ unitRadicals p q) := by
    rw [Msub, Bsub, IntermediateField.adjoin_union]
  apply IntermediateField.algHom_ext_of_eq_adjoin (F p) hM
  intro r hr
  rcases hr with hr | hr
  · obtain rfl := Set.mem_singleton_iff.mp hr
    exact hζ
  · obtain ⟨u, hu⟩ := hr
    have hrmem : r ∈ Msub p q :=
      (show IntermediateField.adjoin (F p) (unitRadicals p q) ≤ Msub p q from le_sup_right)
        (IntermediateField.subset_adjoin (F p) _ ⟨u, hu⟩)
    let rM : Msub p q := ⟨r, hrmem⟩
    change φ rM = ψ rM
    have hrPow : rM ^ q = algebraMap (F p) (Msub p q)
        (((u : NumberField.RingOfIntegers (F p)) : F p)) := Subtype.ext hu
    have hratio : (rM / unitRoot p q hq u) ^ q = 1 := by
      rw [div_pow, hrPow, ← unitRoot_pow p q hq u,
        div_self (pow_ne_zero q (unitRoot_ne_zero p q hq u))]
    obtain ⟨i, _, hi⟩ := (kummerZetaM_spec p q hq).eq_pow_of_pow_eq_one hratio
    have hrEq : rM = kummerZetaM p q ^ i * unitRoot p q hq u := by
      rw [hi, div_mul_cancel₀ _ (unitRoot_ne_zero p q hq u)]
    simp only [hrEq, map_mul, map_pow, hζ, hroots u]

end Catalan.A3
