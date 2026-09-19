import Catalan.Thaine.LiteralNorms
import Catalan.Cassels.LambdaIdeal
import Catalan.FactorBridge

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance normLambdaCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

lemma literal_lambda_norm_ideal
    (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    ∃ l : 𝓞 (A3.F p), ∃ I : Ideal (𝓞 (A3.F p)),
      (l : A3.F p) = (literalLambdaNorm p x hp2 : A3.F p) ∧ Ideal.span {l} = I ^ q := by
  obtain ⟨l, I, hl, hI⟩ :=
    Catalan.lambda_ideal_pow p q (Fact.out : p.Prime) hq hp2 hq2 x y hx hy h
      (A3.Bsub p p)
  let lnorm : 𝓞 (A3.F p) :=
    Algebra.intNorm (𝓞 (A3.F p)) (𝓞 (A3.Bsub p p)) l
  have hnorm_value : (lnorm : A3.F p) =
      (literalLambdaNorm p x hp2 : A3.F p) := by
    change algebraMap (𝓞 (A3.F p)) (A3.F p)
      (Algebra.intNorm (𝓞 (A3.F p)) (𝓞 (A3.Bsub p p)) l) = _
    rw [Algebra.algebraMap_intNorm (A := 𝓞 (A3.F p)) (B := 𝓞 (A3.Bsub p p))
      (K := A3.F p) (L := A3.Bsub p p), literalLambdaNorm_apply]
    congr 1
  have hnorm_span : Ideal.relNorm (𝓞 (A3.F p)) (Ideal.span {l}) =
      Ideal.span {lnorm} := by
    rw [Ideal.relNorm_singleton]
  refine ⟨lnorm, Ideal.relNorm (𝓞 (A3.F p)) I, hnorm_value, ?_⟩
  calc
    Ideal.span {lnorm} = Ideal.relNorm (𝓞 (A3.F p)) (Ideal.span {l}) := hnorm_span.symm
    _ = (Ideal.relNorm (𝓞 (A3.F p)) I) ^ q := by rw [hI, map_pow]

lemma literal_lambda_norm_principal_power
    (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    ∃ J : FracIdealUnit (A3.F p),
      principalIdeal (A3.F p) (literalLambdaNorm p x hp2) = J ^ q := by
  obtain ⟨l, I, hcoe, hI⟩ := literal_lambda_norm_ideal p q hq hp2 hq2 x y hx hy h
  have hl0 : l ≠ 0 := by
    intro hz
    have hzero : (literalLambdaNorm p x hp2 : A3.F p) = 0 := by
      rw [← hcoe, hz]
      rfl
    exact (literalLambdaNorm p x hp2).ne_zero hzero
  have hspan0 : Ideal.span {l} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hI0 : I ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.bot_pow hq.ne_zero] at hI
    exact hspan0 hI
  let J : FracIdealUnit (A3.F p) := idealUnit (A3.F p) I hI0
  have hspan_principal :
      idealUnit (A3.F p) (Ideal.span {l}) hspan0 =
        principalIdeal (A3.F p) (literalLambdaNorm p x hp2) :=
    idealUnit_span_eq_principalIdeal l (literalLambdaNorm p x hp2) hcoe.symm hspan0
  refine ⟨J, ?_⟩
  rw [← hspan_principal]
  apply Units.ext
  simp only [coe_idealUnit, Units.val_pow_eq_pow_val, J]
  rw [hI]
  exact (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 (A3.F p))) (A3.F p)).map_pow I q

end Catalan.Thaine
