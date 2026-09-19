import Catalan.Runge.Reduction

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Runge

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma reduceFull_eq_iff_exists_nsmul (q : ℕ) (Theta Psi : R p K) :
    reduceFull p K q Theta = reduceFull p K q Psi ↔
      ∃ U : R p K, Theta = Psi + q • U := by
  constructor
  · intro heq
    have hzero : reduceFull p K q (Theta - Psi) = 0 := by
      rw [map_sub, heq, sub_self]
    have hdiv : ∀ g : G p K, (q : ℤ) ∣ (Theta - Psi).coeff g :=
      (reduceFull_eq_zero_iff p K q (Theta - Psi)).mp hzero
    let f : ℤ → ℤ := fun z => z / (q : ℤ)
    have hfzero : f 0 = 0 := by simp [f]
    let U : R p K := MonoidAlgebra.ofCoeff
      ((Theta - Psi).coeff.mapRange f hfzero)
    have hqU : q • U = Theta - Psi := by
      apply MonoidAlgebra.coeff_injective
      apply Finsupp.ext
      intro g
      have hg := hdiv g
      have hg' : (q : ℤ) ∣ Theta.coeff g - Psi.coeff g := by
        simpa only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply] using hg
      have hqg : (q : ℤ) * f ((Theta - Psi).coeff g) =
          (Theta - Psi).coeff g := by
        dsimp [f]
        simpa only [Int.mul_comm] using Int.ediv_mul_cancel hg'
      rw [MonoidAlgebra.coeff_smul]
      change q • f ((Theta - Psi).coeff g) = (Theta - Psi).coeff g
      rw [show q • f ((Theta - Psi).coeff g) =
        (q : ℤ) * f ((Theta - Psi).coeff g) by simp [nsmul_eq_mul], hqg]
    refine ⟨U, ?_⟩
    rw [hqU]
    abel
  · rintro ⟨U, hU⟩
    rw [hU, map_add, map_nsmul]
    have hzero : q • reduceFull p K q U = 0 := by
      apply MonoidAlgebra.coeff_injective
      apply Finsupp.ext
      intro g
      rw [MonoidAlgebra.coeff_smul]
      simp
    rw [hzero, add_zero]

lemma upow_nsmul (a : Kˣ) (Theta : R p K) (q : ℕ) :
    upow p K a (q • Theta) = upow p K a Theta ^ q := by
  have h := (upowAddHom p K a).map_nsmul q Theta
  change Additive.ofMul (upow p K a (q • Theta)) =
    q • Additive.ofMul (upow p K a Theta) at h
  simpa only [toMul_ofMul, toMul_nsmul] using congrArg Additive.toMul h

lemma root_of_reduceFull_eq (q : ℕ) (hp2 : p ≠ 2) (x : ℤ) (Theta Psi : R p K)
    (heq : reduceFull p K q Theta = reduceFull p K q Psi)
    (hu : ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Psi : Kˣ) : K)) :
    ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K) := by
  obtain ⟨U, hU⟩ := (reduceFull_eq_iff_exists_nsmul p K q Theta Psi).mp heq
  let a : Kˣ := xmζ p K x hp2
  obtain ⟨u, hu0⟩ := hu
  have hu : u ^ q = ((upow p K a Psi : Kˣ) : K) := by
    simpa [a] using hu0
  have hpow : upow p K a Theta =
      upow p K a Psi * upow p K a U ^ q := by
    rw [hU, upow_add, upow_nsmul]
  refine ⟨u * ((upow p K a U : Kˣ) : K), ?_⟩
  rw [mul_pow, hu]
  simpa only [Units.val_pow_eq_pow_val, Units.val_mul] using
    (congrArg Units.val hpow).symm

lemma root_of_reduceFull_eq_or_neg (q : ℕ) (hp2 : p ≠ 2) (x : ℤ) (Theta Psi : R p K)
    (heq : reduceFull p K q Theta = reduceFull p K q Psi ∨
      reduceFull p K q Theta = -reduceFull p K q Psi)
    (hu : ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Psi : Kˣ) : K)) :
    ∃ u : K, u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K) := by
  rcases heq with heq | heq
  · exact root_of_reduceFull_eq p K q hp2 x Theta Psi heq hu
  · have hneg : reduceFull p K q Theta = reduceFull p K q (-Psi) := by
      rw [map_neg]
      simpa only [heq]
    obtain ⟨U, hU⟩ :=
      (reduceFull_eq_iff_exists_nsmul p K q Theta (-Psi)).mp hneg
    let a : Kˣ := xmζ p K x hp2
    obtain ⟨u, hu0⟩ := hu
    have hu : u ^ q = ((upow p K a Psi : Kˣ) : K) := by
      simpa [a] using hu0
    have hpow : upow p K a Theta =
        upow p K a (-Psi) * upow p K a U ^ q := by
      rw [hU, upow_add, upow_nsmul]
    refine ⟨((upow p K a U : Kˣ) : K) / u, ?_⟩
    rw [div_pow, hu, hpow, upow_neg]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end Catalan.Runge
