module

public import Catalan.Stickelberger.ResidueGauss
public import Catalan.Stickelberger.CyclotomicLift
public import Catalan.Stickelberger.GammaAssembly

/-! Actual prime-residue Gauss sums have all the descended quotients required by Θ_k. -/
/-!
# `Catalan.Stickelberger.ResidueQuotient`

Part of the Catalan formalization.
-/

@[expose] public section

open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma prime_ne_residue_characteristic (I : Ideal (𝓞 K)) [I.IsMaximal]
    (haway : (p : 𝓞 K) ∉ I) : p ≠ ringChar (𝓞 K ⧸ I) := by
  intro h
  apply haway
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_natCast, h]
  exact CharP.cast_eq_zero (𝓞 K ⧸ I) (ringChar (𝓞 K ⧸ I))

/-- One actual residue Gauss sum supplies Γ and all the quotient-power witnesses.
No ideal-factorization assertion is included here. -/
theorem exists_primeResidueGaussSum_quotients (I : Ideal (𝓞 K)) [I.IsMaximal]
    (haway : (p : 𝓞 K) ∉ I) :
    ∃ χ : MulChar (𝓞 K ⧸ I) K, orderOf χ = p ∧
      primeResidueGaussSum K I χ ≠ 0 ∧
      ∃ Γ : Kˣ, algebraMap K (CyclotomicField (ringChar (𝓞 K ⧸ I)) K) (Γ : K) =
          primeResidueGaussSum K I χ ^ p ∧
        ∀ a : (ZMod p)ˣ, ∃ δ : Kˣ,
          δ ^ p = Γ ^ (a : ZMod p).val / elementAct K (σ p K a) Γ := by
  let : Field (𝓞 K ⧸ I) := Ideal.Quotient.field I
  let : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  let : Algebra (ZMod (ringChar (𝓞 K ⧸ I))) (𝓞 K ⧸ I) := ZMod.algebra _ _
  obtain ⟨χ, hχ, hg, Γ, hΓ⟩ := exists_primeResidueGaussSum_descended_power p K I haway
  refine ⟨χ, hχ, hg, Γ, hΓ, ?_⟩
  intro a
  have hχpow : χ ^ p = 1 := hχ ▸ pow_orderOf_eq_one χ
  obtain ⟨δ, hδ⟩ := exists_cyclotomicTraceGaussSum_quotient_power p K (𝓞 K ⧸ I)
    (prime_ne_residue_characteristic p K I haway) χ hχpow a (Γ : K) hΓ.symm
  refine ⟨δ, ?_⟩
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]
  change (δ : K) ^ p = (Γ : K) ^ (a : ZMod p).val / σ p K a (Γ : K)
  exact hδ

end Catalan
