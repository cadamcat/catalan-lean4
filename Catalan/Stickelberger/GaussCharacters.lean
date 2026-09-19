import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.FieldTheory.Galois.Basic

/-! Concrete finite-field trace Gauss sums, relative Galois action, and descent.
The construction uses Mathlib character and Gauss-sum APIs only. No SKW source
or project-specific Gauss-eigenvector assumption is used. -/

noncomputable section
open scoped BigOperators
namespace Catalan

variable {F K E : Type*} [Field F] [Fintype F] [Field K] [Field E]

local instance gaussCharactersCharPrime : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩

/-- The additive character obtained from the prime-field trace and a root of unity. -/
def traceAddChar [Algebra (ZMod (ringChar F)) F] {ζ : E}
    (hζ : ζ ^ ringChar F = 1) : AddChar F E :=
  (AddChar.zmodChar (ringChar F) hζ).compAddMonoidHom
    (Algebra.trace (ZMod (ringChar F)) F).toAddMonoidHom

lemma traceAddChar_primitive [Algebra (ZMod (ringChar F)) F] {ζ : E}
    (hζ : IsPrimitiveRoot ζ (ringChar F)) :
    (traceAddChar (F := F) hζ.pow_eq_one).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
  rw [one_mul] at ha
  apply AddChar.ne_one_iff.mpr
  refine ⟨a, fun hf => ha ?_⟩
  exact (AddChar.zmodChar_primitive_of_primitive_root (ringChar F) hζ).zmod_char_eq_one_iff
    (ringChar F) (Algebra.trace (ZMod (ringChar F)) F a) |>.mp hf

/-- Reindexing the actual finite sum gives the automorphism eigenvalue. -/
lemma gaussSum_aut_eq_mul {χ : MulChar F E} {ψ : AddChar F E}
    (τ : E ≃+* E) (a : Fˣ)
    (hχ : ∀ x, τ (χ x) = χ x) (hψ : ∀ x, τ (ψ x) = ψ (a * x)) :
    τ (gaussSum χ ψ) = χ⁻¹ a * gaussSum χ ψ := by
  calc
    τ (gaussSum χ ψ) = gaussSum χ (ψ.mulShift a) := by
      simp only [gaussSum, map_sum, map_mul, hχ, hψ, AddChar.mulShift_apply]
    _ = _ := gaussSum_mulShift_eq χ ψ a

lemma traceAddChar_aut [Algebra (ZMod (ringChar F)) F] {ζ : E}
    (hζ : ζ ^ ringChar F = 1) (τ : E ≃+* E) (a : ZMod (ringChar F))
    (hτ : τ ζ = ζ ^ a.val) (x : F) :
    τ (traceAddChar (F := F) hζ x) =
      traceAddChar (F := F) hζ (algebraMap (ZMod (ringChar F)) F a * x) := by
  change τ (ζ ^ (Algebra.trace (ZMod (ringChar F)) F x).val) =
    ζ ^ (Algebra.trace (ZMod (ringChar F)) F
      (algebraMap (ZMod (ringChar F)) F a * x)).val
  rw [map_pow, hτ, ← Algebra.smul_def, map_smul, smul_eq_mul, ZMod.val_mul]
  rw [← pow_mul, pow_eq_pow_mod _ hζ]

lemma gaussSum_trace_ne_zero [Algebra (ZMod (ringChar F)) F] [CharZero E]
    {χ : MulChar F E} (hχ : χ ≠ 1) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (ringChar F)) :
    gaussSum χ (traceAddChar (F := F) hζ.pow_eq_one) ≠ 0 := by
  exact gaussSum_ne_zero_of_nontrivial (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    hχ (traceAddChar_primitive hζ)

/-- Every automorphism acts on the primitive prime-order root by a nonzero exponent. -/
lemma exists_prime_root_aut_exponent {ζ : E}
    (hζ : IsPrimitiveRoot ζ (ringChar F)) (τ : E ≃+* E) :
    ∃ a : (ZMod (ringChar F))ˣ, τ ζ = ζ ^ (a : ZMod (ringChar F)).val := by
  obtain ⟨n, hn, he⟩ := hζ.eq_pow_of_pow_eq_one
    (show (τ ζ) ^ ringChar F = 1 by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hn0 : (n : ZMod (ringChar F)) ≠ 0 := by
    intro hz
    have hn0 : n = 0 := by
      have := congrArg ZMod.val hz
      simpa only [ZMod.val_natCast_of_lt hn, ZMod.val_zero] using this
    have hzeta : τ ζ = 1 := by simpa [hn0] using he.symm
    exact hζ.ne_one (CharP.char_is_prime F _).one_lt
      (τ.injective (hzeta.trans τ.map_one.symm))
  refine ⟨Units.mk0 _ hn0, ?_⟩
  simpa only [Units.val_mk0, ZMod.val_natCast_of_lt hn] using he.symm

/-- The finite-field trace Gauss sum, with multiplicative values in the base field. -/
def traceGaussSum [Algebra K E] [Algebra (ZMod (ringChar F)) F]
    (χ : MulChar F K) {ζ : E} (hζ : ζ ^ ringChar F = 1) : E :=
  gaussSum (χ.ringHomComp (algebraMap K E)) (traceAddChar (F := F) hζ)

lemma traceGaussSum_ne_zero [Algebra K E] [Algebra (ZMod (ringChar F)) F] [CharZero E]
    {χ : MulChar F K} (hχ : χ ≠ 1) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (ringChar F)) :
    traceGaussSum χ hζ.pow_eq_one ≠ 0 := by
  apply gaussSum_trace_ne_zero _ hζ
  intro h
  apply hχ
  apply MulChar.injective_ringHomComp (algebraMap K E).injective
  simpa using h

/-- The relative Galois eigencharacter is the inverse multiplicative character
of the prime-field exponent describing the action on the additive root. -/
lemma traceGaussSum_aut [Algebra K E] [Algebra (ZMod (ringChar F)) F]
    (χ : MulChar F K) {ζ : E} (hζ : ζ ^ ringChar F = 1)
    (τ : E ≃ₐ[K] E) (a : (ZMod (ringChar F))ˣ)
    (hτ : τ ζ = ζ ^ (a : ZMod (ringChar F)).val) :
    τ (traceGaussSum χ hζ) =
      algebraMap K E (χ⁻¹ (algebraMap (ZMod (ringChar F)) F a)) *
        traceGaussSum χ hζ := by
  have h := gaussSum_aut_eq_mul (χ := χ.ringHomComp (algebraMap K E))
    (ψ := traceAddChar (F := F) hζ) τ.toRingEquiv
    (Units.map (algebraMap (ZMod (ringChar F)) F).toMonoidHom a)
    (fun x => τ.commutes (χ x))
    (fun x => traceAddChar_aut hζ τ.toRingEquiv a hτ x)
  simpa [MulChar.ringHomComp_inv, traceGaussSum] using h

lemma traceGaussSum_aut_pow [Algebra K E] [Algebra (ZMod (ringChar F)) F]
    (χ : MulChar F K) (p : ℕ) (hχ : χ ^ p = 1) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (ringChar F)) (τ : E ≃ₐ[K] E) :
    τ (traceGaussSum χ hζ.pow_eq_one ^ p) = traceGaussSum χ hζ.pow_eq_one ^ p := by
  obtain ⟨a, ha⟩ := exists_prime_root_aut_exponent (F := F) hζ τ.toRingEquiv
  rw [map_pow, traceGaussSum_aut χ hζ.pow_eq_one τ a ha, mul_pow,
    ← map_pow]
  have hv : χ⁻¹ (algebraMap (ZMod (ringChar F)) F a) ^ p = 1 := by
    let b : Fˣ := Units.map (algebraMap (ZMod (ringChar F)) F).toMonoidHom a
    change χ⁻¹ (b : F) ^ p = 1
    rw [← MulChar.pow_apply_coe, inv_pow, hχ, inv_one, MulChar.one_apply_coe]
  rw [hv, map_one, one_mul]

/-- A genuine nonzero Gauss sum of an exact-order character has its p-th power
in the base field. The character and additive trace character are constructed here. -/
theorem exists_traceGaussSum_descended_power [Algebra K E]
    [Algebra (ZMod (ringChar F)) F] [CharZero E]
    [IsGalois K E] [FiniteDimensional K E]
    (p : ℕ) (hp : 1 < p) (hcard : p ∣ Fintype.card F - 1)
    {μ : K} (hμ : IsPrimitiveRoot μ p) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (ringChar F)) :
    ∃ χ : MulChar F K, orderOf χ = p ∧
      traceGaussSum χ hζ.pow_eq_one ≠ 0 ∧
      ∃ Γ : Kˣ, algebraMap K E (Γ : K) = traceGaussSum χ hζ.pow_eq_one ^ p := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf F hcard hμ
  have hχ1 : χ ≠ 1 := by
    intro h
    have : p = 1 := by simpa [h] using hχ.symm
    omega
  have hg := traceGaussSum_ne_zero hχ1 hζ
  refine ⟨χ, hχ, hg, ?_⟩
  obtain ⟨Γ, hΓ⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := K) (E := E) (traceGaussSum χ hζ.pow_eq_one ^ p)).mpr
      (traceGaussSum_aut_pow χ p (hχ ▸ pow_orderOf_eq_one χ) hζ)
  have hΓ0 : Γ ≠ 0 := by
    intro h
    apply pow_ne_zero p hg
    rw [← hΓ, h, map_zero]
  exact ⟨Units.mk0 Γ hΓ0, hΓ⟩

/-- A primitive trace Gauss sum is nonzero also for the trivial multiplicative
character, when its value is minus one. -/
lemma traceGaussSum_ne_zero_any [Algebra K E] [Algebra (ZMod (ringChar F)) F]
    [CharZero E] (χ : MulChar F K) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (ringChar F)) :
    traceGaussSum χ hζ.pow_eq_one ≠ 0 := by
  by_cases hχ : χ = 1
  · have hp := traceAddChar_primitive (F := F) hζ
    have hψ : traceAddChar (F := F) hζ.pow_eq_one ≠ 1 := by
      simpa only [AddChar.mulShift_one] using hp one_ne_zero
    simpa only [traceGaussSum, hχ, MulChar.ringHomComp_one,
      gaussSum_one_left hψ, ne_eq, neg_eq_zero] using (one_ne_zero : (1 : E) ≠ 0)
  · exact traceGaussSum_ne_zero hχ hζ

lemma traceGaussSum_powChar_aut [Algebra K E] [Algebra (ZMod (ringChar F)) F]
    (χ : MulChar F K) {ζ : E} (hζ : ζ ^ ringChar F = 1)
    (τ : E ≃ₐ[K] E) (a : (ZMod (ringChar F))ˣ) (k : ℕ)
    (hτ : τ ζ = ζ ^ (a : ZMod (ringChar F)).val) :
    τ (traceGaussSum (χ ^ k) hζ) =
      (algebraMap K E (χ⁻¹ (algebraMap (ZMod (ringChar F)) F a))) ^ k *
        traceGaussSum (χ ^ k) hζ := by
  rw [traceGaussSum_aut (χ ^ k) hζ τ a hτ, ← inv_pow, ← map_pow]
  congr 2
  let b : Fˣ := Units.map (algebraMap (ZMod (ringChar F)) F).toMonoidHom a
  change (χ⁻¹ ^ k) (b : F) = χ⁻¹ (b : F) ^ k
  exact MulChar.pow_apply_coe _ _ _

/-- The quotient formed with the k-th character power descends directly from
its two finite-sum transformation formulas. -/
theorem exists_traceGaussSum_descended_quotient [Algebra K E]
    [Algebra (ZMod (ringChar F)) F] [CharZero E]
    [IsGalois K E] [FiniteDimensional K E]
    (χ : MulChar F K) {ζ : E} (hζ : IsPrimitiveRoot ζ (ringChar F)) (k : ℕ) :
    ∃ δ : Kˣ, algebraMap K E (δ : K) =
      traceGaussSum χ hζ.pow_eq_one ^ k / traceGaussSum (χ ^ k) hζ.pow_eq_one := by
  have hfixed (τ : E ≃ₐ[K] E) :
      τ (traceGaussSum χ hζ.pow_eq_one ^ k / traceGaussSum (χ ^ k) hζ.pow_eq_one) =
      traceGaussSum χ hζ.pow_eq_one ^ k / traceGaussSum (χ ^ k) hζ.pow_eq_one := by
    obtain ⟨a, ha⟩ := exists_prime_root_aut_exponent (F := F) hζ τ.toRingEquiv
    rw [map_div₀, map_pow, traceGaussSum_aut χ hζ.pow_eq_one τ a ha,
      traceGaussSum_powChar_aut χ hζ.pow_eq_one τ a k ha, mul_pow]
    apply mul_div_mul_left
    apply pow_ne_zero
    exact (((a.isUnit.map (algebraMap (ZMod (ringChar F)) F)).map χ⁻¹).map
      (algebraMap K E)).ne_zero
  obtain ⟨δ, hδ⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := K) (E := E) _).mpr hfixed
  have hδ0 : δ ≠ 0 := by
    intro h
    have hn := div_ne_zero (pow_ne_zero k (traceGaussSum_ne_zero_any χ hζ))
      (traceGaussSum_ne_zero_any (χ ^ k) hζ)
    apply hn
    rw [← hδ, h, map_zero]
  exact ⟨Units.mk0 δ hδ0, hδ⟩

/-- A base-field automorphism acting on the primitive p-th root by k acts on
any p-torsion multiplicative character by its k-th character power. -/
lemma mulChar_aut_eq_pow (χ : MulChar F K) {p : ℕ} [NeZero p]
    (hχ : χ ^ p = 1) {μ : K} (hμ : IsPrimitiveRoot μ p)
    (σ : K ≃+* K) (k : ℕ) (hσ : σ μ = μ ^ k) (x : F) :
    σ (χ x) = (χ ^ k) x := by
  by_cases hx : x = 0
  · simp only [hx, MulChar.map_zero, map_zero]
  · obtain ⟨j, _, hj⟩ := MulChar.exists_apply_eq_pow hχ hμ hx
    have hp : (χ ^ k) x = χ x ^ k := by
      simpa using MulChar.pow_apply_coe χ k (Units.mk0 x hx)
    rw [hp, hj, map_pow, hσ, ← pow_mul, ← pow_mul, Nat.mul_comm k j]

/-- A lift fixing the additive root sends the Gauss sum to that of the
corresponding power of the multiplicative character. -/
lemma traceGaussSum_lift [Algebra K E] [Algebra (ZMod (ringChar F)) F]
    (χ : MulChar F K) {p : ℕ} [NeZero p] (hχ : χ ^ p = 1)
    {μ : K} (hμ : IsPrimitiveRoot μ p) {ζ : E} (hζ : ζ ^ ringChar F = 1)
    (σ : K ≃+* K) (s : E ≃+* E) (k : ℕ)
    (hσ : σ μ = μ ^ k) (hsζ : s ζ = ζ)
    (hlift : ∀ x : K, s (algebraMap K E x) = algebraMap K E (σ x)) :
    s (traceGaussSum χ hζ) = traceGaussSum (χ ^ k) hζ := by
  have hψ (x : F) : s (traceAddChar (F := F) hζ x) = traceAddChar hζ x := by
    change s (ζ ^ (Algebra.trace (ZMod (ringChar F)) F x).val) =
      ζ ^ (Algebra.trace (ZMod (ringChar F)) F x).val
    rw [map_pow, hsζ]
  simp only [traceGaussSum, gaussSum, map_sum, map_mul, MulChar.ringHomComp_apply,
    hlift, mulChar_aut_eq_pow χ hχ hμ σ k hσ, hψ]

/-- The descended quotient supplies the precise p-th-power identity required
for ideal cancellation. Its automorphism hypotheses are only concrete lift data. -/
theorem exists_traceGaussSum_quotient_power [Algebra K E]
    [Algebra (ZMod (ringChar F)) F] [CharZero E]
    [IsGalois K E] [FiniteDimensional K E]
    (χ : MulChar F K) {p : ℕ} [NeZero p] (hχ : χ ^ p = 1)
    {μ : K} (hμ : IsPrimitiveRoot μ p) {ζ : E}
    (hζ : IsPrimitiveRoot ζ (ringChar F))
    (σ : K ≃+* K) (s : E ≃+* E) (k : ℕ)
    (hσ : σ μ = μ ^ k) (hsζ : s ζ = ζ)
    (hlift : ∀ x : K, s (algebraMap K E x) = algebraMap K E (σ x))
    (Γ : K) (hΓ : traceGaussSum χ hζ.pow_eq_one ^ p = algebraMap K E Γ) :
    ∃ δ : Kˣ, algebraMap K E (δ : K) =
      traceGaussSum χ hζ.pow_eq_one ^ k / s (traceGaussSum χ hζ.pow_eq_one) ∧
      (δ : K) ^ p = Γ ^ k / σ Γ := by
  obtain ⟨δ, hδ⟩ := exists_traceGaussSum_descended_quotient χ hζ k
  have hs := traceGaussSum_lift χ hχ hμ hζ.pow_eq_one σ s k hσ hsζ hlift
  rw [← hs] at hδ
  refine ⟨δ, hδ, ?_⟩
  apply (algebraMap K E).injective
  change algebraMap K E ((δ : K) ^ p) = _
  rw [map_pow, hδ, div_pow, ← map_pow, ← pow_mul, Nat.mul_comm k p,
    pow_mul, hΓ, hlift, map_div₀, map_pow]

/-- The Gauss sum in the concrete extension K(ζ_ell), where ell is the residue
characteristic. -/
def cyclotomicTraceGaussSum [CharZero K] [Algebra (ZMod (ringChar F)) F]
    (χ : MulChar F K) : CyclotomicField (ringChar F) K :=
  traceGaussSum χ (IsCyclotomicExtension.zeta_pow (ringChar F) K
    (CyclotomicField (ringChar F) K))

/-- No extension or additive-character existence premise remains: the extension
is the cyclotomic field over K and the additive root is its canonical root. -/
theorem exists_cyclotomicTraceGaussSum_descended_power [CharZero K]
    [Algebra (ZMod (ringChar F)) F]
    (p : ℕ) (hp : 1 < p) (hcard : p ∣ Fintype.card F - 1)
    {μ : K} (hμ : IsPrimitiveRoot μ p) :
    ∃ χ : MulChar F K, orderOf χ = p ∧
      cyclotomicTraceGaussSum χ ≠ 0 ∧
      ∃ Γ : Kˣ, algebraMap K (CyclotomicField (ringChar F) K) (Γ : K) =
        cyclotomicTraceGaussSum χ ^ p := by
  let := IsCyclotomicExtension.isGalois {ringChar F} K (CyclotomicField (ringChar F) K)
  let := IsCyclotomicExtension.finite_of_singleton (ringChar F) K
    (CyclotomicField (ringChar F) K)
  exact exists_traceGaussSum_descended_power p hp hcard hμ
    (IsCyclotomicExtension.zeta_spec (ringChar F) K (CyclotomicField (ringChar F) K))

end Catalan

