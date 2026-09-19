import Catalan.Density.Definitions

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma card_quotient_under_of_arithmeticFrob_fixes
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (ell : ℕ) (hell : ell.Prime) (P : Ideal (𝓞 L))
    (sigma : L ≃ₐ[ℚ] L) (hfrob : IsArithmeticFrob ell P sigma)
    (hfix : ∀ x : K, sigma (algebraMap K L x) = algebraMap K L x) :
    Nat.card (𝓞 K ⧸ P.under (𝓞 K)) = ell := by
  rcases hfrob with ⟨hPmax, _, hellP, _, _, _, hcong⟩
  let fixedResiduePMaximal : P.IsMaximal := hPmax
  let I : Ideal (𝓞 K) := P.under (𝓞 K)
  let fixedResidueUnderMaximal : I.IsMaximal := inferInstance
  let F := 𝓞 K ⧸ I
  let fixedResidueField : Field F := Ideal.Quotient.field I
  let fixedResiduePrime : Fact ell.Prime := ⟨hell⟩
  have hellI : (ell : 𝓞 K) ∈ I := by
    change algebraMap (𝓞 K) (𝓞 L) (ell : 𝓞 K) ∈ P
    simpa only [map_natCast] using hellP
  have hellZero : (ell : F) = 0 := by
    change (ell : 𝓞 K ⧸ I) = 0
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hellI
  let fixedResidueCharP : CharP F ell := (CharP.charP_iff_prime_eq_zero hell).mpr hellZero
  have hfixed (x : 𝓞 K) :
      integralAut sigma (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap (𝓞 K) (𝓞 L) x := by
    apply RingOfIntegers.coe_injective
    change sigma (algebraMap K L (x : K)) = algebraMap K L (x : K)
    exact hfix (x : K)
  have hdiff (x : 𝓞 K) : x - x ^ ell ∈ I := by
    change algebraMap (𝓞 K) (𝓞 L) (x - x ^ ell) ∈ P
    rw [map_sub, map_pow]
    simpa only [hfixed] using hcong (algebraMap (𝓞 K) (𝓞 L) x)
  have hpower (z : F) : z ^ ell = z := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hquot := (Ideal.Quotient.eq (I := I)).mpr (hdiff x)
    simpa only [map_pow] using hquot.symm
  have hbot : (⊥ : Subfield F) = ⊤ := by
    apply top_unique
    intro z _
    exact (Subfield.mem_bot_iff_pow_eq_self F ell).mpr (hpower z)
  change Nat.card F = ell
  calc
    Nat.card F = Nat.card (⊤ : Subfield F) :=
      (Nat.card_congr (Subfield.topEquiv (K := F)).toEquiv).symm
    _ = Nat.card (⊥ : Subfield F) := by rw [hbot]
    _ = ell := Subfield.card_bot F ell

end Catalan.A3
