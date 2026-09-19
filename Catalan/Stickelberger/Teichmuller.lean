import Catalan.Stickelberger.NormalizedCharacter

/-!
# Teichmüller characters: the prime-free generalization

This file generalizes the order-`p` normalized power-residue character of
`Catalan/Stickelberger/NormalizedCharacter.lean` from a prime exponent `p` to an
arbitrary exponent `n` with `[NeZero n]`, and specializes it at
`n = Fintype.card F - 1` to obtain the Teichmüller character and its inverse.

The auxiliary declarations `Catalan.restrictRootsOfUnity_bijective_of_primitive`
and `Catalan.residuePowerHom` of that file already assume only `[NeZero n]`, so
they are reused unchanged.
-/

noncomputable section

namespace Catalan.Stickelberger

/-- A normalized `n`-th power-residue character, with the orientation fixed by `f`. -/
theorem exists_normalized_residueChar
    (F : Type*) [Field F] [Fintype F] (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) [NeZero n] (hdiv : n ∣ Fintype.card F - 1)
    (f : R →+* F) {μ : R} (hμ : IsPrimitiveRoot μ n) (hfμ : IsPrimitiveRoot (f μ) n) :
    ∃ χ : MulChar F R, χ ^ n = 1 ∧ (∀ x : Fˣ, (χ x) ^ n = 1) ∧
      (∀ x : Fˣ, f (χ x) = (x : F) ^ ((Fintype.card F - 1) / n)) := by
  classical
  let e : rootsOfUnity n R ≃* rootsOfUnity n F :=
    MulEquiv.ofBijective (restrictRootsOfUnity f n)
      (restrictRootsOfUnity_bijective_of_primitive f hμ hfμ)
  let h : Fˣ →* Rˣ := (rootsOfUnity n R).subtype.comp
    (e.symm.toMonoidHom.comp (residuePowerHom F n hdiv))
  let χ := MulChar.ofUnitHom h
  have hnorm (x : Fˣ) : f (χ x) = (x : F) ^ ((Fintype.card F - 1) / n) := by
    have hh := e.apply_symm_apply (residuePowerHom F n hdiv x)
    have hh' := congrArg (fun z : rootsOfUnity n F => ((z : Fˣ) : F)) hh
    change f ((e.symm (residuePowerHom F n hdiv x) : Rˣ) : R) = _ at hh'
    change f (MulChar.ofUnitHom h (x : F)) = _
    rw [MulChar.ofUnitHom_coe]
    exact hh'
  have hptwise (x : Fˣ) : (χ x) ^ n = 1 := by
    change (MulChar.ofUnitHom h (x : F)) ^ n = 1
    rw [MulChar.ofUnitHom_coe]
    exact (mem_rootsOfUnity' n _).mp (e.symm (residuePowerHom F n hdiv x)).prop
  have hpow : χ ^ n = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    exact hptwise u
  exact ⟨χ, hpow, hptwise, hnorm⟩

/-- The Teichmüller character: a multiplicative character `F → R` that is a section of `f`
and whose values are `(#F - 1)`-th roots of unity (equivalently, fixed by `x ↦ x ^ #F`). -/
theorem exists_teichmullerChar
    (F : Type*) [Field F] [Fintype F] (R : Type*) [CommRing R] [IsDomain R]
    (f : R →+* F) {μ : R} (hμ : IsPrimitiveRoot μ (Fintype.card F - 1))
    (hfμ : IsPrimitiveRoot (f μ) (Fintype.card F - 1)) :
    ∃ τ : MulChar F R, (∀ x : F, (τ x) ^ Fintype.card F = τ x) ∧
      (∀ x : F, f (τ x) = x) := by
  classical
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  have : NeZero (Fintype.card F - 1) := ⟨by omega⟩
  obtain ⟨τ, -, hptwise, hnorm⟩ :=
    exists_normalized_residueChar F R (Fintype.card F - 1) dvd_rfl f hμ hfμ
  refine ⟨τ, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst hx
      rw [MulChar.map_zero, zero_pow (by omega)]
    · have hu : (τ x) ^ (Fintype.card F - 1) = 1 := by
        simpa only [Units.val_mk0] using hptwise (Units.mk0 x hx)
      have hcard : Fintype.card F = (Fintype.card F - 1) + 1 := by omega
      rw [hcard, pow_succ, hu, one_mul]
  · intro x
    by_cases hx : x = 0
    · subst hx
      rw [MulChar.map_zero, map_zero]
    · have hd : (Fintype.card F - 1) / (Fintype.card F - 1) = 1 :=
        Nat.div_self (by omega)
      simpa only [Units.val_mk0, hd, pow_one] using hnorm (Units.mk0 x hx)

/-- The inverse Teichmüller character: same root-of-unity property, but reducing to `x⁻¹`.
It is nontrivial as soon as `#F > 2`. -/
theorem exists_invTeichmullerChar
    (F : Type*) [Field F] [Fintype F] (R : Type*) [CommRing R] [IsDomain R]
    (hF : 2 < Fintype.card F)
    (f : R →+* F) {μ : R} (hμ : IsPrimitiveRoot μ (Fintype.card F - 1))
    (hfμ : IsPrimitiveRoot (f μ) (Fintype.card F - 1)) :
    ∃ τ : MulChar F R, (∀ x : F, (τ x) ^ Fintype.card F = τ x) ∧
      (∀ x : F, f (τ x) = x⁻¹) ∧ τ ≠ 1 := by
  classical
  obtain ⟨τ, hpow, hnorm⟩ := exists_teichmullerChar F R f hμ hfμ
  have hinvpow : ∀ x : F, (τ⁻¹ x) ^ Fintype.card F = τ⁻¹ x := by
    intro x
    rw [MulChar.inv_apply']
    exact hpow _
  have hinvnorm : ∀ x : F, f (τ⁻¹ x) = x⁻¹ := by
    intro x
    rw [MulChar.inv_apply']
    exact hnorm _
  refine ⟨τ⁻¹, hinvpow, hinvnorm, ?_⟩
  intro hc
  have hcard : 1 < Fintype.card Fˣ := by
    rw [Fintype.card_units]; omega
  have : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  have h1 : ((u : F))⁻¹ = 1 := by
    rw [← hinvnorm, hc, MulChar.one_apply_coe, map_one]
  exact hu (Units.ext (by rw [Units.val_one, ← inv_inv (u : F), h1, inv_one]))

end Catalan.Stickelberger
