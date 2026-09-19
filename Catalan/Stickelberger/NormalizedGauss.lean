import Catalan.Stickelberger.NormalizedCharacter
import Catalan.Stickelberger.ResidueQuotient

/-! A single normalized residue character supplies the Gauss power and all quotients. -/
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

theorem primeResidueGaussSum_data_of_pow_eq_one (I : Ideal (𝓞 K)) [I.IsMaximal]
    (haway : (p : 𝓞 K) ∉ I) (χ : MulChar (𝓞 K ⧸ I) K) (hχ : χ ^ p = 1) :
    primeResidueGaussSum K I χ ≠ 0 ∧
      ∃ Γ : Kˣ, algebraMap K (CyclotomicField (ringChar (𝓞 K ⧸ I)) K) (Γ : K) =
          primeResidueGaussSum K I χ ^ p ∧
        ∀ a : (ZMod p)ˣ, ∃ δ : Kˣ,
          δ ^ p = Γ ^ (a : ZMod p).val / elementAct K (σ p K a) Γ := by
  let : Field (𝓞 K ⧸ I) := Ideal.Quotient.field I
  let : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  let : Algebra (ZMod (ringChar (𝓞 K ⧸ I))) (𝓞 K ⧸ I) := ZMod.algebra _ _
  let : Fact (ringChar (𝓞 K ⧸ I)).Prime := ⟨CharP.char_is_prime (𝓞 K ⧸ I) _⟩
  let E := CyclotomicField (ringChar (𝓞 K ⧸ I)) K
  let : IsGalois K E := IsCyclotomicExtension.isGalois {ringChar (𝓞 K ⧸ I)} K E
  let : FiniteDimensional K E :=
    IsCyclotomicExtension.finite_of_singleton (ringChar (𝓞 K ⧸ I)) K E
  have hζ := IsCyclotomicExtension.zeta_spec (ringChar (𝓞 K ⧸ I)) K E
  have hg : primeResidueGaussSum K I χ ≠ 0 := traceGaussSum_ne_zero_any χ hζ
  have hfixed (τ : E ≃ₐ[K] E) :
      τ (primeResidueGaussSum K I χ ^ p) = primeResidueGaussSum K I χ ^ p :=
    traceGaussSum_aut_pow χ p hχ hζ τ
  obtain ⟨Γ, hΓ⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := K) (E := E) _).mpr hfixed
  have hΓ0 : Γ ≠ 0 := by
    intro h
    apply pow_ne_zero p hg
    rw [← hΓ, h, map_zero]
  refine ⟨hg, Units.mk0 Γ hΓ0, hΓ, ?_⟩
  intro a
  obtain ⟨δ, hδ⟩ := exists_cyclotomicTraceGaussSum_quotient_power p K (𝓞 K ⧸ I)
    (prime_ne_residue_characteristic p K I haway) χ hχ a Γ hΓ.symm
  refine ⟨δ, ?_⟩
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_mk0]
  change (δ : K) ^ p = Γ ^ (a : ZMod p).val / σ p K a Γ
  exact hδ

/-- Inverse power-residue normalization, nonzero Gauss sum and all descended
quotients hold for the same character. The ideal factorization remains separate. -/
theorem exists_inverse_normalized_primeResidueGaussSum (I : Ideal (𝓞 K)) [I.IsMaximal]
    (haway : (p : 𝓞 K) ∉ I) :
    ∃ χ : MulChar (𝓞 K ⧸ I) K, orderOf χ = p ∧
      (∀ x : (𝓞 K ⧸ I)ˣ, ∃ z : 𝓞 K, (z : K) = χ x ∧
        Ideal.Quotient.mk I z =
          (((x ^ ((Nat.card (𝓞 K ⧸ I) - 1) / p))⁻¹ : (𝓞 K ⧸ I)ˣ) : 𝓞 K ⧸ I)) ∧
      primeResidueGaussSum K I χ ≠ 0 ∧
      ∃ Γ : Kˣ, algebraMap K (CyclotomicField (ringChar (𝓞 K ⧸ I)) K) (Γ : K) =
          primeResidueGaussSum K I χ ^ p ∧
        ∀ a : (ZMod p)ˣ, ∃ δ : Kˣ,
          δ ^ p = Γ ^ (a : ZMod p).val / elementAct K (σ p K a) Γ := by
  obtain ⟨χ, hχ, hnorm⟩ := exists_inverse_normalized_primeResidueChar p K I haway
  have hd := primeResidueGaussSum_data_of_pow_eq_one p K I haway χ (hχ ▸ pow_orderOf_eq_one χ)
  exact ⟨χ, hχ, hnorm, hd⟩

end Catalan
