import Catalan.Density.NormalM
import Catalan.Stickelberger.TowerLift

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

def auxiliaryRoot (p ell : ℕ) : A3.Bsub p ell :=
  ⟨A3.primitiveRoot ell, IntermediateField.subset_adjoin (A3.F p) _ (by simp)⟩

private lemma exists_ambient_auxiliary_action
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (s : (ZMod ell)ˣ) :
    ∃ sigma : A3.Omega ≃ₐ[ℚ] A3.Omega,
      sigma (A3.primitiveRoot p) = A3.primitiveRoot p ∧
      sigma (A3.primitiveRoot ell) = A3.primitiveRoot ell ^ (s : ZMod ell).val := by
  have instAuxAmbientNeP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have instAuxAmbientNeEll : NeZero ell := ⟨(Fact.out : ell.Prime).ne_zero⟩
  have instAuxAmbientNeMul : NeZero (p * ell) := ⟨mul_ne_zero (NeZero.ne p) (NeZero.ne ell)⟩
  have instAuxAmbientAlgebraic : Algebra.IsAlgebraic ℚ A3.Omega := AlgebraicClosure.isAlgebraic ℚ
  have instAuxAmbientAlgClosure : IsAlgClosure ℚ A3.Omega := ⟨inferInstance, instAuxAmbientAlgebraic⟩
  have instAuxAmbientNormal : Normal ℚ A3.Omega := IsAlgClosure.normal ℚ A3.Omega
  let Cp : IntermediateField ℚ A3.Omega := IntermediateField.adjoin ℚ {A3.primitiveRoot p}
  let Ce : IntermediateField ℚ A3.Omega := IntermediateField.adjoin ℚ {A3.primitiveRoot ell}
  let M : IntermediateField ℚ A3.Omega := Cp ⊔ Ce
  have hcop : p.Coprime ell := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : ell.Prime)).mpr hpe
  have instAuxAmbientCycloM : IsCyclotomicExtension {p * ell} ℚ M := by
    let instAuxAmbientAlgebraCp : Algebra ℚ Cp := IntermediateField.algebra' Cp
    let instAuxAmbientAlgebraCe : Algebra ℚ Ce := IntermediateField.algebra' Ce
    let instAuxAmbientAlgebraM : Algebra ℚ M := IntermediateField.algebra' M
    have instAuxAmbientCycloP : IsCyclotomicExtension {p} ℚ Cp :=
      (A3.primitiveRoot_spec p (Fact.out : p.Prime).pos).intermediateField_adjoin_isCyclotomicExtension ℚ
    have instAuxAmbientCycloEll : IsCyclotomicExtension {ell} ℚ Ce :=
      (A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos).intermediateField_adjoin_isCyclotomicExtension ℚ
    have h := IntermediateField.isCyclotomicExtension_lcm_sup ℚ A3.Omega p ell Cp Ce
    rw [hcop.lcm_eq_mul] at h
    convert h using 1
    · rfl
    · exact Subsingleton.elim _ _
  have instAuxAmbientNumberM : NumberField M := IsCyclotomicExtension.numberField {p * ell} ℚ M
  have hpM : A3.primitiveRoot p ∈ M :=
    (show Cp ≤ M from le_sup_left) (IntermediateField.subset_adjoin ℚ _ (by simp))
  have heM : A3.primitiveRoot ell ∈ M :=
    (show Ce ≤ M from le_sup_right) (IntermediateField.subset_adjoin ℚ _ (by simp))
  let b := Nat.chineseRemainder hcop 1 (s : ZMod ell).val
  have hbp : b.val.Coprime p := by
    rw [← ZMod.coprime_mod_iff_coprime, b.prop.1, ZMod.coprime_mod_iff_coprime]
    exact Nat.coprime_one_left p
  have hbe : b.val.Coprime ell := by
    rw [← ZMod.coprime_mod_iff_coprime, b.prop.2, ZMod.coprime_mod_iff_coprime]
    exact ZMod.val_coe_unit_coprime s
  let t : (ZMod (p * ell))ˣ := ZMod.unitOfCoprime b.val (hbp.mul_right hbe)
  let sigmaM := (IsCyclotomicExtension.Rat.galEquivZMod (p * ell) M).symm t
  have hsigmaM (x : M) (hx : x ^ (p * ell) = 1) : sigmaM x = x ^ b.val := by
    have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (p * ell) M sigmaM hx
    simp only [sigmaM, MulEquiv.apply_symm_apply, t, ZMod.coe_unitOfCoprime,
      ZMod.val_natCast] at h
    exact h.trans (pow_eq_pow_mod b.val hx).symm
  let sigma := sigmaM.liftNormal A3.Omega
  have hlift (x : A3.Omega) (hx : x ∈ M) (hxN : x ^ (p * ell) = 1) :
      sigma x = x ^ b.val := by
    let y : M := ⟨x, hx⟩
    have hy : y ^ (p * ell) = 1 := Subtype.ext hxN
    calc
      sigma x = algebraMap M A3.Omega (sigmaM y) := sigmaM.liftNormal_commutes A3.Omega y
      _ = x ^ b.val := by rw [hsigmaM y hy, map_pow]; rfl
  refine ⟨sigma, ?_, ?_⟩
  · have hpz := (A3.primitiveRoot_spec p (Fact.out : p.Prime).pos).pow_eq_one
    rw [hlift _ hpM (by rw [pow_mul, hpz, one_pow]), pow_eq_pow_mod b.val hpz,
      b.prop.1, ← pow_eq_pow_mod 1 hpz, pow_one]
  · have hez := (A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos).pow_eq_one
    rw [hlift _ heM (by rw [mul_comm p ell, pow_mul, hez, one_pow]),
      pow_eq_pow_mod b.val hez, b.prop.2, ← pow_eq_pow_mod (s : ZMod ell).val hez]

lemma auxiliary_cyclic_generator
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (s : (ZMod ell)ˣ) (hs : ∀ x : (ZMod ell)ˣ, x ∈ Subgroup.zpowers s) :
    Module.finrank (A3.F p) (A3.Bsub p ell) = ell - 1 ∧
    ∃ tau : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell,
      tau (auxiliaryRoot p ell) = auxiliaryRoot p ell ^ (s : ZMod ell).val ∧
      orderOf tau = ell - 1 ∧
      ∀ sigma : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell,
        sigma ∈ Subgroup.zpowers tau := by
  have instAuxNeEll : NeZero ell := ⟨(Fact.out : ell.Prime).ne_zero⟩
  have instAuxCycloB : IsCyclotomicExtension {ell} (A3.F p) (A3.Bsub p ell) :=
    A3.isCyclotomicExtension_Bsub p ell (Fact.out : ell.Prime).pos
  have instAuxGaloisB : IsGalois (A3.F p) (A3.Bsub p ell) :=
    A3.isGalois_Bsub p ell (Fact.out : ell.Prime).pos
  obtain ⟨sigma, hsigp, hsige⟩ := exists_ambient_auxiliary_action p ell hpe s
  have hfix (x : A3.F p) : sigma (x : A3.Omega) = (x : A3.Omega) := by
    have heq : sigma.toAlgHom.comp (A3.Fsub p).val = (A3.Fsub p).val := by
      apply IntermediateField.adjoin_algHom_ext
      intro y hy
      obtain rfl : y = A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹ := by simpa using hy
      change sigma (A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹) =
        A3.primitiveRoot p + (A3.primitiveRoot p)⁻¹
      rw [map_add, map_inv₀, hsigp]
    exact DFunLike.congr_fun heq x
  let sigmaF : A3.Omega ≃ₐ[A3.F p] A3.Omega :=
    AlgEquiv.ofRingEquiv (f := sigma.toRingEquiv) hfix
  let tau : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell :=
    sigmaF.restrictNormal (A3.Bsub p ell)
  have htau : tau (auxiliaryRoot p ell) = auxiliaryRoot p ell ^ (s : ZMod ell).val := by
    apply Subtype.ext
    have h := sigmaF.restrictNormal_commutes (A3.Bsub p ell) (auxiliaryRoot p ell)
    change ((tau (auxiliaryRoot p ell) : A3.Bsub p ell) : A3.Omega) =
      sigma (A3.primitiveRoot ell) at h
    exact h.trans hsige
  have hroot : IsPrimitiveRoot (auxiliaryRoot p ell) ell := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos
  let phi := hroot.autToPow (A3.F p)
  have hphi : Function.Injective phi := hroot.autToPow_injective (A3.F p)
  have hphitau : phi tau = s := by
    apply Units.ext
    apply ZMod.val_injective
    apply hroot.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    exact (hroot.autToPow_spec (A3.F p) tau).trans htau
  have hgen : ∀ rho : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell,
      rho ∈ Subgroup.zpowers tau := by
    intro rho
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp (hs (phi rho))
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨k, hphi ?_⟩
    rw [map_zpow, hphitau]
    exact hk
  have horder : orderOf tau = ell - 1 := by
    rw [← orderOf_injective phi hphi tau, hphitau,
      orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card,
      Fintype.card_units, ZMod.card]
  refine ⟨?_, tau, htau, horder, hgen⟩
  rw [← IsGalois.card_aut_eq_finrank, ← orderOf_eq_card_of_forall_mem_zpowers hgen, horder]

end Catalan.Thaine
