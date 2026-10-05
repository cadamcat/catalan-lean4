module

public import Catalan.IdealAction

/-!
# `Catalan.IdealHelpers`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors Pointwise
open NumberField
noncomputable section
namespace Catalan

section
variable (K : Type*) [Field K] [NumberField K]

lemma fractionalIdeal_prime_induction
    (P : FracIdealUnit K → Prop)
    (h_one : P 1)
    (h_mul : ∀ I J, P I → P J → P (I * J))
    (h_inv : ∀ I, P I → P I⁻¹)
    (h_prime : ∀ (I : Ideal (𝓞 K)) (_hI : I.IsPrime) (hI0 : I ≠ ⊥),
      P (idealUnit K I hI0)) :
    ∀ J : FracIdealUnit K, P J := by
  have h_integral : ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥), P (idealUnit K I hI) := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact (h rfl).elim
    | h₂ I hI =>
      intro hI0
      have hI1 : I = 1 := isUnit_iff_eq_one.mp hI
      subst I
      convert h_one using 1
      apply Units.ext
      simp [coe_idealUnit]
    | h₃ I Q hI hQ ih =>
      intro hIQ
      have hQ0 : Q ≠ ⊥ := hQ.ne_zero
      have hI0 : I ≠ ⊥ := hI
      have heq : idealUnit K (Q * I) hIQ = idealUnit K Q hQ0 * idealUnit K I hI0 := by
        apply Units.ext
        exact map_mul (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) Q I
      rw [heq]
      exact h_mul _ _ (h_prime Q (Ideal.isPrime_of_prime hQ) hQ0) (ih hI0)
  intro J
  obtain ⟨a, B, ha, hB⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (J : FracIdeal K)
  have hB0 : B ≠ ⊥ := FractionalIdeal.ideal_factor_ne_zero (Units.ne_zero J) hB
  have ha0 : Ideal.span {a} ≠ (⊥ : Ideal (𝓞 K)) := by
    exact Ideal.span_singleton_eq_bot.not.mpr ha
  have hJa : J = (idealUnit K (Ideal.span {a}) ha0)⁻¹ * idealUnit K B hB0 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val, coe_idealUnit, coe_idealUnit,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv]
    exact hB
  rw [hJa]
  exact h_mul _ _ (h_inv _ (h_integral _ ha0)) (h_integral B hB0)

end

section
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [hcycl : IsCyclotomicExtension {p} ℚ K]

include hp hcycl in
lemma prime_over_p_principal (I : Ideal (𝓞 K))
    (hI : I.IsPrime) (hI0 : I ≠ ⊥) (hpI : (p : 𝓞 K) ∈ I) :
    ∃ γ : Kˣ, idealUnit K I hI0 = principalIdeal K γ := by
  let : NeZero p := ⟨hp.out.ne_zero⟩
  let : I.IsPrime := hI
  let : I.LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    apply Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p)
      Ideal.IsPrime.ne_top'
    simpa only [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq,
      map_natCast] using hpI
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have heq : I = Ideal.span {hζ.toInteger - 1} :=
    IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p K hζ I
  have hgen : ((hζ.toInteger - 1 : 𝓞 K) : K) ≠ 0 := by
    exact_mod_cast hζ.zeta_sub_one_prime'.ne_zero
  refine ⟨Units.mk0 ((hζ.toInteger - 1 : 𝓞 K) : K) hgen, ?_⟩
  apply Units.ext
  rw [coe_idealUnit, heq, coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
  rfl

end
end Catalan
