module

public import Catalan.IdealHelpers

/-!
# `Catalan.Stickelberger.ClassReduction`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Pointwise
open NumberField
noncomputable section
namespace Catalan

/-- Construction by adjoining one generator modulo the excluded ideal.
The proof follows the standard Dedekind argument also used in
xroblot/SKW, SKW/Prereqs/ClassGroupCoprime.lean, revision
4db8676808a63d892a8f36ead11308ca8dd58520. No SKW dependency is imported. -/
lemma exists_coprime_integralRepresentative
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (C : ClassGroup R) (B : Ideal R) (hB : B ≠ ⊥) :
    ∃ I : (Ideal R)⁰, ClassGroup.mk0 I = C ∧ IsCoprime (I : Ideal R) B := by
  by_cases htop : B = ⊤
  · obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective C
    exact ⟨I, hI, by simp [Ideal.isCoprime_iff_sup_eq, htop]⟩
  obtain ⟨A, hA⟩ := ClassGroup.mk0_surjective C⁻¹
  have hA0 : (A : Ideal R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp A.property
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (Ideal.mul_le_left : (A : Ideal R) * B ≤ A) (mul_ne_zero hA0 hB)
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr
    (show Ideal.span {a} ≤ (A : Ideal R) from ha ▸ le_sup_right)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_zero, sup_bot_eq] at ha
    apply htop
    exact mul_left_cancel₀ hA0 (ha.trans (Ideal.mul_top _).symm)
  have hI0 : I ≠ 0 := by
    intro h
    rw [h, mul_zero] at hI
    exact ha0 (Ideal.span_singleton_eq_bot.mp hI)
  let U : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩
  let V : (Ideal R)⁰ := ⟨Ideal.span {a},
    mem_nonZeroDivisors_iff_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr ha0)⟩
  have hprod : A * U = V := Subtype.ext hI.symm
  have hclass : ClassGroup.mk0 V = 1 :=
    (ClassGroup.mk0_eq_one_iff V.property).mpr ⟨⟨a, rfl⟩⟩
  refine ⟨U, ?_, ?_⟩
  · have h := congrArg ClassGroup.mk0 hprod
    rw [map_mul, hA, hclass] at h
    exact (inv_mul_eq_one.mp h).symm
  · rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
    apply mul_left_cancel₀ hA0
    change (A : Ideal R) * (B ⊔ I) = (A : Ideal R) * ⊤
    rw [Ideal.mul_sup, Ideal.mul_top, ← hI, ha]

lemma principalIdeal_of_class_eq_one
    (K : Type*) [Field K] [NumberField K]
    (J : FracIdealUnit K) (h : ClassGroup.mk K J = 1) :
    ∃ γ : Kˣ, J = principalIdeal K γ := by
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff (J : FracIdeal K)).mp
    (ClassGroup.mk_eq_one_iff.mp h)
  have hx0 : x ≠ 0 := by
    intro hzero
    apply Units.ne_zero J
    exact hx.trans (by simp [hzero])
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  simpa only [coe_toPrincipalIdeal, Units.val_mk0] using hx

lemma ipow_principal_of_class_eq
    (p : ℕ) (K : Type*) [Field K] [NumberField K]
    (Θ : R p K) (I J : FracIdealUnit K)
    (hclass : ClassGroup.mk K I = ClassGroup.mk K J)
    (hI : ∃ γ : Kˣ, ipow p K I Θ = principalIdeal K γ) :
    ∃ γ : Kˣ, ipow p K J Θ = principalIdeal K γ := by
  have hquot : ClassGroup.mk K (J / I) = 1 := by
    rw [map_div, ← hclass, div_self']
  obtain ⟨δ, hδ⟩ := principalIdeal_of_class_eq_one K (J / I) hquot
  have hJ : J = principalIdeal K δ * I := (div_eq_iff_eq_mul).mp hδ
  obtain ⟨γ, hγ⟩ := hI
  refine ⟨Θ.coeff.prod (fun τ m => (elementAct K τ δ) ^ m) * γ, ?_⟩
  rw [hJ, ipow_mul, ipow_principalIdeal, hγ, map_mul]

lemma fractional_generator_of_coprime_integral
    (p : ℕ) (K : Type*) [Field K] [NumberField K]
    (Θ : R p K) (B : Ideal (𝓞 K)) (hB : B ≠ ⊥)
    (hgen : ∀ (I : Ideal (𝓞 K)) (hI0 : I ≠ ⊥), IsCoprime I B →
      ∃ γ : Kˣ, ipow p K (idealUnit K I hI0) Θ = principalIdeal K γ)
    (J : FracIdealUnit K) :
    ∃ γ : Kˣ, ipow p K J Θ = principalIdeal K γ := by
  obtain ⟨I, hI, hcop⟩ := exists_coprime_integralRepresentative (ClassGroup.mk K J) B hB
  have hI0 : (I : Ideal (𝓞 K)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  apply ipow_principal_of_class_eq p K Θ (idealUnit K I hI0) J
  · change ClassGroup.mk K (FractionalIdeal.mk0 K I) = _
    rwa [ClassGroup.mk_mk0]
  · exact hgen I hI0 hcop

lemma fractional_generator_of_coprime_primes
    (p : ℕ) (K : Type*) [Field K] [NumberField K]
    (Θ : R p K) (B : Ideal (𝓞 K)) (hB : B ≠ ⊥)
    (hgen : ∀ (I : Ideal (𝓞 K)) (_hI : I.IsPrime) (hI0 : I ≠ ⊥),
      IsCoprime I B →
      ∃ γ : Kˣ, ipow p K (idealUnit K I hI0) Θ = principalIdeal K γ)
    (J : FracIdealUnit K) :
    ∃ γ : Kˣ, ipow p K J Θ = principalIdeal K γ := by
  apply fractional_generator_of_coprime_integral p K Θ B hB _ J
  intro I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro hI; exact (hI rfl).elim
  | h₂ I hI =>
    intro hI0 _
    have hI1 : I = 1 := isUnit_iff_eq_one.mp hI
    subst I
    have heq : idealUnit K 1 hI0 = 1 := by
      apply Units.ext
      simp [coe_idealUnit]
    exact ⟨1, by rw [heq, ipow_one, map_one]⟩
  | h₃ I Q hI hQ ih =>
    intro hQI hcop
    have hQ0 : Q ≠ ⊥ := hQ.ne_zero
    have hI0 : I ≠ ⊥ := hI
    have heq : idealUnit K (Q * I) hQI = idealUnit K Q hQ0 * idealUnit K I hI0 := by
      apply Units.ext
      exact map_mul (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) Q I
    obtain ⟨α, hα⟩ := hgen Q (Ideal.isPrime_of_prime hQ) hQ0 hcop.of_mul_left_left
    obtain ⟨β, hβ⟩ := ih hI0 hcop.of_mul_left_right
    exact ⟨α * β, by rw [heq, ipow_mul, hα, hβ, map_mul]⟩

/-- Prime witnesses outside 2p suffice for every fractional ideal, including
    prime ideals above 2 and p. The witnesses are an explicit premise. -/
lemma fractional_generator_of_primes_away_two_mul
    (p : ℕ) (hp : p ≠ 0) (K : Type*) [Field K] [NumberField K]
    (Θ : R p K)
    (hgen : ∀ (I : Ideal (𝓞 K)) (_hI : I.IsPrime) (hI0 : I ≠ ⊥),
      (2 * p : 𝓞 K) ∉ I →
      ∃ γ : Kˣ, ipow p K (idealUnit K I hI0) Θ = principalIdeal K γ)
    (J : FracIdealUnit K) :
    ∃ γ : Kˣ, ipow p K J Θ = principalIdeal K γ := by
  have hB : Ideal.span {(2 * p : 𝓞 K)} ≠ ⊥ := by
    apply Ideal.span_singleton_eq_bot.not.mpr
    exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hp)
  apply fractional_generator_of_coprime_primes p K Θ _ hB _ J
  intro I hI hI0 hcop
  apply hgen I hI hI0
  intro hmem
  have hle : Ideal.span {(2 * p : 𝓞 K)} ≤ I := (Ideal.span_singleton_le_iff_mem _).mpr hmem
  apply hI.ne_top
  calc
    I = I ⊔ Ideal.span {(2 * p : 𝓞 K)} := (sup_eq_left.mpr hle).symm
    _ = ⊤ := hcop.sup_eq

end Catalan
