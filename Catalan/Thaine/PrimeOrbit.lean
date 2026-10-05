module

public import Catalan.Thaine.RealUnramified

/-!
# `Catalan.Thaine.PrimeOrbit`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
namespace Catalan.Thaine

private lemma nat_mem_of_card
    (F : Type*) [Field F] [NumberField F] (ell : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = ell) : (ell : 𝓞 F) ∈ v.asIdeal := by
  have h := v.asIdeal.absNorm_mem
  change (Nat.card (𝓞 F ⧸ v.asIdeal) : 𝓞 F) ∈ v.asIdeal at h
  rwa [hcard] at h

private lemma liesOver_int_of_nat_mem
    (F : Type*) [Field F] [NumberField F] (ell : ℕ) [Fact ell.Prime]
    (v : HeightOneSpectrum (𝓞 F)) (hmem : (ell : 𝓞 F) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(ell : ℤ)}) := by
  apply (Ideal.liesOver_span_iff v.isPrime.ne_top
    (Nat.prime_iff_prime_int.mp (Fact.out : ell.Prime))).mpr
  simpa only [map_natCast] using hmem

private lemma prime_equiv_asIdeal
    (F : Type*) [Field F] [NumberField F] (g : F ≃ₐ[ℚ] F) (v : HeightOneSpectrum (𝓞 F)) :
    (HeightOneSpectrum.equivOfRingEquiv (A3.integralAut g) v).asIdeal = g • v.asIdeal := by
  change v.asIdeal.comap (A3.integralAut g).symm.toRingHom = g • v.asIdeal
  calc
    v.asIdeal.comap (A3.integralAut g).symm.toRingHom =
        Ideal.map (A3.integralAut g).toRingHom v.asIdeal :=
      (Ideal.map_comap_of_equiv (I := v.asIdeal) (A3.integralAut g)).symm
    _ = g • v.asIdeal := by
      rw [Ideal.pointwise_smul_def]
      rfl

lemma inertiaDeg_int_eq_one_of_card
    (F : Type*) [Field F] [NumberField F]
    (ell : ℕ) [Fact ell.Prime]
    (v : HeightOneSpectrum (𝓞 F))
    (hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = ell) :
    v.asIdeal.inertiaDeg ℤ = 1 := by
  have instPrimeOrbitInertiaOver : v.asIdeal.LiesOver (Ideal.span {(ell : ℤ)}) :=
    liesOver_int_of_nat_mem F ell v (nat_mem_of_card F ell v hcard)
  have h := Ideal.cardQuot_pow_inertiaDeg (Ideal.span {(ell : ℤ)}) v.asIdeal
  change Nat.card (ℤ ⧸ Ideal.span {(ell : ℤ)}) ^ v.asIdeal.inertiaDeg ℤ =
    Nat.card (𝓞 F ⧸ v.asIdeal) at h
  rw [Int.card_ideal_quot, hcard] at h
  apply Nat.pow_right_injective (Fact.out : ell.Prime).two_le
  simpa only [pow_one] using h

lemma real_prime_stabilizer_eq_bot
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (v0 : HeightOneSpectrum (𝓞 (A3.F p)))
    (hcard : Nat.card (𝓞 (A3.F p) ⧸ v0.asIdeal) = ell) :
    MulAction.stabilizer (A3.F p ≃ₐ[ℚ] A3.F p) v0.asIdeal = ⊥ := by
  have instPrimeOrbitStabAbelian : IsAbelianGalois ℚ (A3.F p) :=
    A3.isAbelianGalois_F p (Fact.out : p.Prime).pos
  have hellv : (ell : 𝓞 (A3.F p)) ∈ v0.asIdeal := nat_mem_of_card (A3.F p) ell v0 hcard
  have instPrimeOrbitStabOver : v0.asIdeal.LiesOver (Ideal.span {(ell : ℤ)}) :=
    liesOver_int_of_nat_mem (A3.F p) ell v0 hellv
  apply Subgroup.eq_bot_of_card_eq
  rw [Ideal.card_stabilizer_eq (G := A3.F p ≃ₐ[ℚ] A3.F p)
      (Ideal.span {(ell : ℤ)}) v0.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(ell : ℤ)}) v0.asIdeal
      (A3.F p ≃ₐ[ℚ] A3.F p),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(ell : ℤ)}) v0.asIdeal
      (A3.F p ≃ₐ[ℚ] A3.F p),
    real_prime_ramification_one p ell hpe v0 hellv,
    inertiaDeg_int_eq_one_of_card (A3.F p) ell v0 hcard, one_mul]

lemma exists_real_prime_orbit_equiv
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (v0 : HeightOneSpectrum (𝓞 (A3.F p)))
    (hcard : Nat.card (𝓞 (A3.F p) ⧸ v0.asIdeal) = ell) :
    ∃ e : (A3.F p ≃ₐ[ℚ] A3.F p) ≃
        {v : HeightOneSpectrum (𝓞 (A3.F p)) // (ell : 𝓞 (A3.F p)) ∈ v.asIdeal},
      ∀ g, (e g).val = HeightOneSpectrum.equivOfRingEquiv (A3.integralAut g) v0 := by
  have instPrimeOrbitEquivAbelian : IsAbelianGalois ℚ (A3.F p) :=
    A3.isAbelianGalois_F p (Fact.out : p.Prime).pos
  have hellv0 : (ell : 𝓞 (A3.F p)) ∈ v0.asIdeal := nat_mem_of_card (A3.F p) ell v0 hcard
  have instPrimeOrbitEquivOver0 : v0.asIdeal.LiesOver (Ideal.span {(ell : ℤ)}) :=
    liesOver_int_of_nat_mem (A3.F p) ell v0 hellv0
  let f : (A3.F p ≃ₐ[ℚ] A3.F p) →
      {v : HeightOneSpectrum (𝓞 (A3.F p)) // (ell : 𝓞 (A3.F p)) ∈ v.asIdeal} :=
    fun g => ⟨HeightOneSpectrum.equivOfRingEquiv (A3.integralAut g) v0, by
      change (A3.integralAut g).symm (ell : 𝓞 (A3.F p)) ∈ v0.asIdeal
      simpa only [map_natCast] using hellv0⟩
  have hinj : Function.Injective f := by
    intro g h hfg
    have hI : g • v0.asIdeal = h • v0.asIdeal := by
      have heq := congrArg (fun v => v.val.asIdeal) hfg
      simpa only [f, prime_equiv_asIdeal] using heq
    have hmem : g⁻¹ * h ∈ MulAction.stabilizer (A3.F p ≃ₐ[ℚ] A3.F p) v0.asIdeal := by
      apply MulAction.mem_stabilizer_iff.mpr
      rw [mul_smul, ← hI, inv_smul_smul]
    have hidentity : g⁻¹ * h = 1 := by
      simpa only [real_prime_stabilizer_eq_bot p ell hpe v0 hcard, Subgroup.mem_bot] using hmem
    exact inv_mul_eq_one.mp hidentity
  have hsurj : Function.Surjective f := by
    intro v
    have instPrimeOrbitTargetOver : v.val.asIdeal.LiesOver (Ideal.span {(ell : ℤ)}) :=
      liesOver_int_of_nat_mem (A3.F p) ell v.val v.property
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      (Ideal.span {(ell : ℤ)}) v0.asIdeal v.val.asIdeal (A3.F p ≃ₐ[ℚ] A3.F p)
    refine ⟨g, Subtype.ext ?_⟩
    apply HeightOneSpectrum.ext
    exact (prime_equiv_asIdeal (A3.F p) g v0).trans hg
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro g
  rfl

end Catalan.Thaine
