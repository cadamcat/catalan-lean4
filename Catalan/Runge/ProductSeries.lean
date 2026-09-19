import Catalan.Runge.ProductCoefficients

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
namespace Catalan.Runge

private lemma complex_hasSum_mul {α β : Type*} (f : α → ℂ) (g : β → ℂ)
    (a b : ℂ) (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun x : α × β => f x.1 * g x.2) (a * b) := by
  have hn1 : Summable (fun x => ‖f x‖) := summable_norm_iff.mpr hf.summable
  have hn2 : Summable (fun x => ‖g x‖) := summable_norm_iff.mpr hg.summable
  exact hf.mul hg (summable_mul_of_summable_norm hn1 hn2)

private lemma fin_product_hasSum
    (n : ℕ) (f : Fin n → ℕ → ℂ) (b : Fin n → ℂ)
    (hf : ∀ i, HasSum (f i) (b i)) :
    HasSum (fun m : Fin n → ℕ => ∏ i, f i (m i)) (∏ i, b i) := by
  classical
  revert f b
  induction n with
  | zero =>
    intro f b hf
    simpa using (hasSum_unique (fun m : Fin 0 → ℕ => ∏ i, f i (m i)))
  | succ n ih =>
    intro f b hf
    have ht : HasSum (fun m : Fin n → ℕ => ∏ i : Fin n, f i.succ (m i)) (∏ i : Fin n, b i.succ) :=
      ih (fun i : Fin n => f i.succ) (fun i : Fin n => b i.succ) (fun i : Fin n => hf i.succ)
    have hp := complex_hasSum_mul (f 0) (fun m : Fin n → ℕ => ∏ i : Fin n, f i.succ (m i))
      (b 0) (∏ i : Fin n, b i.succ) (hf 0) ht
    have h := (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).symm.hasSum_iff.mpr hp
    simpa [Function.comp_def, Fin.consEquiv, Fin.tail, Fin.prod_univ_succ] using h

private lemma finite_product_hasSum
    (ι : Type*) [Fintype ι] (f : ι → ℕ → ℂ) (b : ι → ℂ)
    (hf : ∀ i, HasSum (f i) (b i)) :
    HasSum (fun m : ι → ℕ => ∏ i, f i (m i)) (∏ i, b i) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h : HasSum (fun m : Fin (Fintype.card ι) → ℕ => ∏ i, f (e.symm i) (m i))
      (∏ i : Fin (Fintype.card ι), b (e.symm i)) := fin_product_hasSum (Fintype.card ι)
        (fun i : Fin (Fintype.card ι) => f (e.symm i)) (fun i : Fin (Fintype.card ι) => b (e.symm i)) (fun i : Fin (Fintype.card ι) => hf (e.symm i))
  let E : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) := Equiv.arrowCongr e (Equiv.refl ℕ)
  have h' : HasSum (fun m : ι → ℕ => ∏ i : Fin (Fintype.card ι), f (e.symm i) (m (e.symm i)))
      (∏ i : Fin (Fintype.card ι), b (e.symm i)) := by
    simpa [Function.comp_def, E, Equiv.arrowCongr] using E.hasSum_iff.mpr h
  have hb : (∏ i : Fin (Fintype.card ι), b (e.symm i)) = ∏ i : ι, b i :=
    Fintype.prod_equiv e.symm (fun i : Fin (Fintype.card ι) => b (e.symm i)) b (fun _ => rfl)
  rw [hb] at h'
  apply h'.congr_fun
  intro m
  exact (Fintype.prod_equiv e.symm (fun i => f (e.symm i) (m (e.symm i)))
    (fun i => f i (m i)) (fun _ => rfl)).symm

private lemma hasSum_by_total
    (ι : Type*) [Fintype ι] (f : (ι → ℕ) → ℂ) (b : ℂ) (hf : HasSum f b) :
    HasSum (fun k : ℕ => ∑ m ∈ Finset.piAntidiag Finset.univ k, f m) b := by
  have h := hf.tsum_fiberwise (fun m : ι → ℕ => ∑ i, m i)
  apply h.congr_fun
  intro k
  let e : ↑((fun m : ι → ℕ => ∑ i, m i) ⁻¹' {k}) ≃
      ↥(Finset.piAntidiag (Finset.univ : Finset ι) k) :=
    Equiv.subtypeEquivRight (fun m => by simp [Finset.mem_piAntidiag])
  have he := e.tsum_eq (fun m => f m.val)
  change (∑' m : ↑((fun m : ι → ℕ => ∑ i, m i) ⁻¹' {k}), f m.val) =
    ∑' m : ↥(Finset.piAntidiag (Finset.univ : Finset ι) k), f m.val at he
  simpa only [tsum_fintype, Finset.sum_coe_sort] using he.symm

private lemma total_degree_term
    (ι : Type*) [Fintype ι] (a : ι → ℚ) (w : ι → ℂ) (z : ℂ) (k : ℕ) :
    (∑ m ∈ Finset.piAntidiag (Finset.univ : Finset ι) k,
      ∏ i, ((binomRat (a i) (m i) : ℂ) * (w i * z) ^ m i)) =
      binomialProductCoeff ι a w k * z ^ k := by
  rw [binomialProductCoeff,
    sum_bounded_eq_piAntidiag k
      (fun m : ι → ℕ => ∏ i, ((binomRat (a i) (m i) : ℂ) * w i ^ m i)),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hsum : (∑ i, m i) = k := (Finset.mem_piAntidiag.mp hm).1
  calc
    (∏ i, ((binomRat (a i) (m i) : ℂ) * (w i * z) ^ m i)) =
        ∏ i, (((binomRat (a i) (m i) : ℂ) * w i ^ m i) * z ^ m i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [mul_pow, mul_assoc]
    _ = (∏ i, ((binomRat (a i) (m i) : ℂ) * w i ^ m i)) * z ^ k := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]


lemma hasSum_binomialProductCoeff
    (ι : Type*) [Fintype ι] (a : ι → ℚ) (w : ι → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1)
    (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => binomialProductCoeff ι a w k * z ^ k)
      (∏ i, (1 + w i * z) ^ (a i : ℂ)) := by
  have hsingle (i : ι) :
      HasSum (fun n : ℕ => (binomRat (a i) n : ℂ) * (w i * z) ^ n)
        ((1 + w i * z) ^ (a i : ℂ)) := by
    apply hasSum_binomRat_mul_pow
    calc
      ‖w i * z‖ = ‖w i‖ * ‖z‖ := norm_mul _ _
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right (hw i) (norm_nonneg z)
      _ < 1 := by simpa only [one_mul] using hz
  have h := finite_product_hasSum ι
    (fun i n => (binomRat (a i) n : ℂ) * (w i * z) ^ n)
    (fun i => (1 + w i * z) ^ (a i : ℂ)) hsingle
  have ht := hasSum_by_total ι
    (fun m : ι → ℕ => ∏ i, ((binomRat (a i) (m i) : ℂ) * (w i * z) ^ m i))
    (∏ i, (1 + w i * z) ^ (a i : ℂ)) h
  apply ht.congr_fun
  intro k
  exact (total_degree_term ι a w z k).symm

end Catalan.Runge
