module

public import Catalan.Stickelberger.PrimeGauss
public import Catalan.Stickelberger.Reduction
public import Catalan.Stickelberger.GammaAssembly

/-!
# `Catalan.Stickelberger.Annihilation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField
open scoped nonZeroDivisors

/-- Gauss witnesses make every small Stickelberger generator principal at primes outside 2p. -/
theorem prime_stickelberger_generator
    (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (I : Ideal (𝓞 K)) (hI : I.IsPrime) (hI0 : I ≠ ⊥)
    (haway : (2 * p : 𝓞 K) ∉ I) (k : ℕ) (hk : 0 < k) (hkp : k ≤ p) :
    ∃ δ : Kˣ, ipow p K (idealUnit K I hI0) (ΘS p K k) = principalIdeal K δ := by
  classical
  have hIprime : I.IsPrime := hI
  have hImax : I.IsMaximal := hI.isMaximal hI0
  obtain ⟨ell, n, hn, hmem, hell, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow I
  have hellPrime : Fact ell.Prime := ⟨hell⟩
  have hne2 : ell ≠ 2 := by
    intro h
    rw [h, Nat.cast_ofNat] at hmem
    exact haway (I.mul_mem_right (p : 𝓞 K) hmem)
  have hne : ell ≠ p := by
    intro h
    rw [h] at hmem
    exact haway (I.mul_mem_left 2 hmem)
  have hgt : 2 < ell := lt_of_le_of_ne hell.two_le (Ne.symm hne2)
  have hOver : I.LiesOver (Ideal.span {(ell : ℤ)}) := by
    apply (Ideal.liesOver_span_iff hI.ne_top (Nat.prime_iff_prime_int.mp hell)).mpr
    simpa only [map_natCast] using hmem
  obtain ⟨Γ, hΓ, hquot⟩ := Stickelberger.exists_prime_gauss_witnesses p ell K I hgt hne hI0
  by_cases hkeq : k = p
  · exact ⟨Γ, by simpa only [hkeq, ΘS_p] using hΓ⟩
  · have hklt : k < p := lt_of_le_of_ne hkp hkeq
    have hcop : k.Coprime p := (hp.out.coprime_iff_not_dvd).mpr
      (Nat.not_dvd_of_pos_of_lt hk hklt) |>.symm
    let a : (ZMod p)ˣ := ZMod.unitOfCoprime k hcop
    have ha : (a : ZMod p).val = k := by simp [a, ZMod.val_natCast_of_lt hklt]
    obtain ⟨δ, hδ⟩ := hquot a
    exact ⟨δ, by simpa only [ha] using
      theta_principal_of_gauss_quotient p K (idealUnit K I hI0) a Γ δ hΓ hδ⟩

/-- Every element of the integral Stickelberger span annihilates every fractional ideal class. -/
theorem stickelberger_annihilates
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (Θ : R p K) (hΘ : Θ ∈ stickSpan p K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ γ : Kˣ, ipow p K J Θ = toPrincipalIdeal (𝓞 K) K γ := by
  exact stickelberger_from_primes_away_two_mul p K
    (fun I hI hI0 haway k hk hkp => prime_stickelberger_generator p K I hI hI0 haway k hk hkp)
    Θ hΘ J

end Catalan

