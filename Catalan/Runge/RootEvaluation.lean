import Catalan.Runge.RootReality
import Catalan.Runge.ProductReality

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open NumberField
noncomputable section
namespace Catalan.Runge

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance rootEvaluationGalFintype : Fintype (G p K) := Fintype.ofFinite _

def rungeFunction (q : ℕ) (Theta : R p K) (τ : K →+* ℂ) (z : ℂ) : ℂ :=
  ∏ g : G p K, (1 + (-τ (g (ζ p K))) * z) ^ (((Theta.coeff g : ℚ) / q : ℚ) : ℂ)

lemma norm_embedding_zeta_conj (τ : K →+* ℂ) (g : G p K) : ‖τ (g (ζ p K))‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := p) _ (Fact.out : p.Prime).ne_zero
  rw [← map_pow, ← map_pow, (ζ_spec p K).pow_eq_one, map_one, map_one]

lemma rungeFunction_positive_real (q : ℕ) (Theta : R p K) (hp2 : p ≠ 2)
    (he : EvenCoefficients p K Theta) (τ : K →+* ℂ) (t : ℝ) (ht : |t| < 1) :
    ∃ r : ℝ, 0 < r ∧ rungeFunction p K q Theta τ (t : ℂ) = (r : ℂ) := by
  apply binomialProduct_positive_real (G p K)
    (fun g => (Theta.coeff g : ℚ) / q) (fun g => -τ (g (ζ p K)))
    (Equiv.mulLeft (ι p K))
  · intro g
    change (Theta.coeff (ι p K * g) : ℚ) / q = (Theta.coeff g : ℚ) / q
    rw [he g]
  · intro g
    change -τ ((ι p K * g) (ζ p K)) = conj (-τ (g (ζ p K)))
    rw [AlgEquiv.mul_apply, A1e.iota_on_embeddings p K hp2 τ, map_neg]
  · intro g
    rw [norm_neg, norm_embedding_zeta_conj p K τ g]
  · exact ht

lemma rungeFunction_pow (q : ℕ) (hq : q ≠ 0) (Theta : R p K) (τ : K →+* ℂ) (z : ℂ) :
    rungeFunction p K q Theta τ z ^ q =
      ∏ g : G p K, (1 + (-τ (g (ζ p K))) * z) ^ Theta.coeff g := by
  classical
  rw [rungeFunction, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro g _
  rw [← Complex.cpow_mul_nat]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have heq : (((Theta.coeff g : ℚ) / q : ℚ) : ℂ) * (q : ℂ) = (Theta.coeff g : ℂ) := by
    push_cast
    field_simp
  rw [heq, Complex.cpow_intCast]

lemma root_pow_eq_scaled_rungeFunction_pow (q : ℕ) (hq : q ≠ 0) (hp2 : p ≠ 2)
    (x : ℤ) (hx : x ≠ 0) (Theta : R p K) (hn : ∀ g, 0 ≤ Theta.coeff g)
    (m : ℕ) (hw : weight p K Theta = (m * q : ℕ)) (u : K)
    (hu : u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K))
    (τ : K →+* ℂ) :
    (τ u) ^ q = ((x : ℂ) ^ m * rungeFunction p K q Theta τ ((x : ℂ)⁻¹)) ^ q := by
  classical
  let n : G p K → ℕ := fun g => (Theta.coeff g).toNat
  have hncast (g : G p K) : (n g : ℤ) = Theta.coeff g := Int.toNat_of_nonneg (hn g)
  have hsum : (∑ g : G p K, n g) = m * q := by
    have hs : (∑ g : G p K, (n g : ℤ)) = ((m * q : ℕ) : ℤ) := by
      simpa only [hncast, ← weight_eq_sum] using hw
    exact_mod_cast hs
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hval : τ ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K) =
      ∏ g : G p K, ((x : ℂ) - τ (g (ζ p K))) ^ n g := by
    rw [map_upow]
    apply Finset.prod_congr rfl
    intro g _
    rw [← hncast g, zpow_natCast]
    congr 1
    change τ (g ((x : K) - ζ p K)) = _
    rw [map_sub, map_sub, map_intCast, map_intCast]
  have hfun : rungeFunction p K q Theta τ ((x : ℂ)⁻¹) ^ q =
      ∏ g : G p K, (1 + (-τ (g (ζ p K))) * (x : ℂ)⁻¹) ^ n g := by
    rw [rungeFunction_pow p K q hq]
    apply Finset.prod_congr rfl
    intro g _
    rw [← hncast g, zpow_natCast]
  calc
    (τ u) ^ q = τ ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K) := by rw [← map_pow, hu]
    _ = ∏ g : G p K, ((x : ℂ) - τ (g (ζ p K))) ^ n g := hval
    _ = ∏ g : G p K, ((x : ℂ) * (1 + (-τ (g (ζ p K))) * (x : ℂ)⁻¹)) ^ n g := by
      apply Finset.prod_congr rfl
      intro g _
      congr 1
      field_simp
      ring
    _ = (x : ℂ) ^ (∑ g : G p K, n g) *
        ∏ g : G p K, (1 + (-τ (g (ζ p K))) * (x : ℂ)⁻¹) ^ n g := by
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    _ = (x : ℂ) ^ (m * q) * rungeFunction p K q Theta τ ((x : ℂ)⁻¹) ^ q := by rw [hsum, hfun]
    _ = ((x : ℂ) ^ m * rungeFunction p K q Theta τ ((x : ℂ)⁻¹)) ^ q := by rw [mul_pow, pow_mul]

lemma root_eq_scaled_rungeFunction (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (x : ℤ) (hx : 1 < (|x| : ℝ)) (Theta : R p K)
    (hn : ∀ g, 0 ≤ Theta.coeff g) (he : EvenCoefficients p K Theta)
    (m : ℕ) (hw : weight p K Theta = (m * q : ℕ)) (u : K)
    (hu : u ^ q = ((upow p K (xmζ p K x hp2) Theta : Kˣ) : K))
    (τ : K →+* ℂ) :
    τ u = (x : ℂ) ^ m * rungeFunction p K q Theta τ ((x : ℂ)⁻¹) := by
  have hq : q.Prime := Fact.out
  have hx0 : x ≠ 0 := by intro hx0; subst x; norm_num at hx
  have hxR : 1 < |(x : ℝ)| := by exact_mod_cast hx
  have ht : |(x : ℝ)⁻¹| < 1 := by
    rw [abs_inv]
    exact (inv_lt_one₀ (by linarith : 0 < |(x : ℝ)|)).mpr hxR
  obtain ⟨r, hr, hfun⟩ := rungeFunction_positive_real p K q Theta hp2 he τ ((x : ℝ)⁻¹) ht
  have hfunC : rungeFunction p K q Theta τ ((x : ℂ)⁻¹) = (r : ℂ) := by simpa using hfun
  have huReal : (((τ u).re : ℝ) : ℂ) = τ u :=
    Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr
      (root_im_eq_zero_of_even p K q hp2 hpq hq2 x Theta he u hu τ))
  have hpower := root_pow_eq_scaled_rungeFunction_pow p K q hq.ne_zero hp2 x hx0 Theta hn m hw u hu τ
  rw [hfunC] at hpower
  have hpowerR : (τ u).re ^ q = ((x : ℝ) ^ m * r) ^ q := by
    apply Complex.ofReal_injective
    push_cast
    rw [huReal]
    exact hpower
  have hroot := (hq.odd_of_ne_two hq2).pow_injective hpowerR
  calc
    τ u = (((τ u).re : ℝ) : ℂ) := huReal.symm
    _ = (((x : ℝ) ^ m * r : ℝ) : ℂ) := congrArg Complex.ofReal hroot
    _ = (x : ℂ) ^ m * rungeFunction p K q Theta τ ((x : ℂ)⁻¹) := by rw [hfunC]; push_cast; rfl

end Catalan.Runge
