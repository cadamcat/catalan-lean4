module

public import Catalan.Cassels.Elementary

/-!
# `Catalan.Cassels.Relations`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

lemma cassels_partial_q_relations (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (hqx : (q : ℤ) ∣ x) :
    ∃ b u : ℤ, b ≠ 0 ∧ 0 < u ∧
      y + 1 = (q : ℤ) ^ (p - 1) * b ^ p ∧
      casselsCyclo q (-y) = (q : ℤ) * u ^ p ∧
      x = (q : ℤ) * b * u := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hqo : Odd q := hq.odd_of_ne_two hq2
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqA : (q : ℤ) ∣ y + 1 := by
    have hqpow : (q : ℤ) ∣ x ^ p := dvd_pow hqx hp.ne_zero
    have hF := Int.prime_dvd_pow_self_sub hq y
    have he : x ^ p - (y ^ q - y) = y + 1 := by rw [h]; ring
    simpa only [he] using dvd_sub hqpow hF
  have hnegA : -y - 1 = -(y + 1) := by ring
  have hqnegA : (q : ℤ) ∣ -y - 1 := by
    rw [hnegA]
    exact dvd_neg.mpr hqA
  have hprod : (y + 1) * casselsCyclo q (-y) = x ^ p := by
    have hf := int_pow_sub_one_factor q (-y)
    rw [hqo.neg_pow, hnegA] at hf
    rw [h]
    linear_combination hf
  have hA : y + 1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact (pow_ne_zero p hx) hprod.symm
  have hSpos : 0 < casselsCyclo q (-y) := by
    exact hqo.geom_sum_pos
  have hS : casselsCyclo q (-y) ≠ 0 := ne_of_gt hSpos
  have hv := cassels_cyclo_exact_valuation q hq hq2 (-y) hqnegA
  have hqS : (q : ℤ) ∣ casselsCyclo q (-y) := by
    simpa only [hv, pow_one] using (padicValInt_dvd (p := q) (casselsCyclo q (-y)))
  obtain ⟨D, hD⟩ := hqS
  have hnqD : ¬ (q : ℤ) ∣ D := by
    intro hdiv
    have hsq : (q : ℤ) ^ 2 ∣ casselsCyclo q (-y) := by
      rw [hD, pow_two]
      exact mul_dvd_mul_left (q : ℤ) hdiv
    have hval := (padicValInt_dvd_iff_of_ne_one hq.ne_one 2
      (casselsCyclo q (-y))).mp hsq
    simp only [hS, hv, false_or] at hval
    omega
  have hD0 : D ≠ 0 := by
    intro h0
    apply hS
    simp only [hD, h0, mul_zero]
  obtain ⟨c, hc⟩ := hqx
  have hpstep : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.one_le).symm
  have hqpowstep : (q : ℤ) ^ p = (q : ℤ) * (q : ℤ) ^ (p - 1) := by
    nth_rw 1 [hpstep]
    rw [pow_succ']
  have hprod' : (y + 1) * D = (q : ℤ) ^ (p - 1) * c ^ p := by
    apply mul_left_cancel₀ hqZ.ne_zero
    calc
      (q : ℤ) * ((y + 1) * D) = (y + 1) * casselsCyclo q (-y) := by rw [hD]; ring
      _ = x ^ p := hprod
      _ = (q : ℤ) ^ p * c ^ p := by rw [hc, mul_pow]
      _ = (q : ℤ) * ((q : ℤ) ^ (p - 1) * c ^ p) := by
        rw [hqpowstep]
        ring
  have hqpA : (q : ℤ) ^ (p - 1) ∣ y + 1 := by
    apply hqZ.pow_dvd_of_dvd_mul_right (p - 1) hnqD
    rw [hprod']
    exact dvd_mul_right _ _
  obtain ⟨E, hE⟩ := hqpA
  have hE0 : E ≠ 0 := by
    intro h0
    apply hA
    simp only [hE, h0, mul_zero]
  have hED : E * D = c ^ p := by
    apply mul_left_cancel₀ (pow_ne_zero (p - 1) hqZ.ne_zero)
    calc
      (q : ℤ) ^ (p - 1) * (E * D) = (y + 1) * D := by rw [hE]; ring
      _ = (q : ℤ) ^ (p - 1) * c ^ p := hprod'
  have hAS : y + 1 ∣ casselsCyclo q (-y) - (q : ℤ) := by
    simpa only [hnegA, neg_dvd] using cassels_cyclo_sub_dvd q (-y)
  have hg : Int.gcd E D = 1 := by
    let g : ℕ := Int.gcd E D
    have hgE : (g : ℤ) ∣ E := Int.gcd_dvd_left E D
    have hgD : (g : ℤ) ∣ D := Int.gcd_dvd_right E D
    have hgA : (g : ℤ) ∣ y + 1 := by
      rw [hE]
      exact dvd_mul_of_dvd_right hgE _
    have hgS : (g : ℤ) ∣ casselsCyclo q (-y) := by
      rw [hD]
      exact dvd_mul_of_dvd_right hgD _
    have hgd : (g : ℤ) ∣ casselsCyclo q (-y) - (q : ℤ) := dvd_trans hgA hAS
    have hgq : (g : ℤ) ∣ (q : ℤ) := by
      have he : casselsCyclo q (-y) - (casselsCyclo q (-y) - (q : ℤ)) = q := by ring
      simpa only [he] using dvd_sub hgS hgd
    have hgqN : g ∣ q := by exact_mod_cast hgq
    rcases (Nat.dvd_prime hq).mp hgqN with hg1 | hgq
    · exact hg1
    · exfalso
      apply hnqD
      simpa only [hgq] using hgD
  obtain ⟨b, u, hb, hu⟩ := cassels_coprime_power_factors p hpo E D c hE0 hD0 hg hED
  have hb0 : b ≠ 0 := by
    intro h0
    apply hE0
    simp only [hb, h0, zero_pow hp.ne_zero]
  have hyb : y + 1 = (q : ℤ) ^ (p - 1) * b ^ p := by rw [hE, hb]
  have hSu : casselsCyclo q (-y) = (q : ℤ) * u ^ p := by rw [hD, hu]
  have hu0 : 0 < u := by
    apply hpo.pow_pos_iff.mp
    have hqpos : 0 < (q : ℤ) := by exact_mod_cast hq.pos
    rw [hSu] at hSpos
    exact (mul_pos_iff_of_pos_left hqpos).mp hSpos
  have hxu : x = (q : ℤ) * b * u := by
    apply hpo.pow_injective
    calc
      x ^ p = (y + 1) * casselsCyclo q (-y) := hprod.symm
      _ = ((q : ℤ) ^ (p - 1) * b ^ p) * ((q : ℤ) * u ^ p) := by rw [hyb, hSu]
      _ = ((q : ℤ) * b * u) ^ p := by
        rw [mul_pow, mul_pow, hqpowstep]
        ring
  exact ⟨b, u, hb0, hu0, hyb, hSu, hxu⟩

#print axioms cassels_partial_q_relations

end Catalan
