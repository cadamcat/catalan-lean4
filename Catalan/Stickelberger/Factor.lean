import Catalan.Stickelberger.GaussFamily
import Catalan.IdealAction.Composition
import Mathlib

/-!
# Ideal identities from prime-by-prime multiplicities

The Stickelberger step needs `J ^ (pθ) = (Γ)`.  This file supplies the *descent
apparatus*: the general Dedekind-domain facts that turn a statement about
`emultiplicity` at each prime into an identity of ideals, and then into an
identity of fractional-ideal units of the shape `ipow`/`principalIdeal` used by
`theta_principal_of_gauss_quotient`.

Nothing here computes a Gauss-sum valuation; that input stays explicit.
-/

noncomputable section

namespace Catalan.Stickelberger

open Ideal

/-- 在 Dedekind 整环里，两个非零理想在每个非零素理想处重数相同就相等。 -/
theorem ideal_eq_of_emultiplicity_eq {A : Type*} [CommRing A] [IsDedekindDomain A]
    {I J : Ideal A} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ P : Ideal A, P.IsPrime → P ≠ ⊥ → emultiplicity P I = emultiplicity P J) :
    I = J := by
  have key : ∀ Q : Ideal A, Prime Q → emultiplicity Q I = emultiplicity Q J := fun Q hQ =>
    h Q (Ideal.isPrime_of_prime hQ) hQ.ne_zero
  have h1 : I ∣ J := (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hI).mpr
    fun Q hQ => le_of_eq (key Q hQ)
  have h2 : J ∣ I := (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hJ).mpr
    fun Q hQ => le_of_eq (key Q hQ).symm
  exact le_antisymm (Ideal.dvd_iff_le.mp h2) (Ideal.dvd_iff_le.mp h1)

/-- 若 `Γ` 乘上某个元素等于单位乘 `ell ^ f`，则不在 `ell` 上方的素理想不整除 `(Γ)`。 -/
theorem emultiplicity_span_eq_zero_of_notMem
    {A : Type*} [CommRing A] [IsDomain A] {Γ Γ' u : A} {ell f : ℕ}
    (hu : IsUnit u) (hprod : Γ * Γ' = u * (ell : A) ^ f)
    (P : Ideal A) (hP : P.IsPrime) (hell : (ell : A) ∉ P) :
    emultiplicity P (Ideal.span {Γ}) = 0 := by
  rw [emultiplicity_eq_zero]
  intro hdvd
  have hmem : Γ ∈ P := by
    obtain ⟨X, hX⟩ := hdvd
    have hle : Ideal.span {Γ} ≤ P := by
      rw [hX]; exact Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self Γ)
  have hprodmem : u * (ell : A) ^ f ∈ P := hprod ▸ Ideal.mul_mem_right _ _ hmem
  have hupow : (ell : A) ^ f ∈ P := by
    obtain ⟨v, hv⟩ := hu
    have : (v⁻¹ : Aˣ) * (u * (ell : A) ^ f) ∈ P := Ideal.mul_mem_left _ _ hprodmem
    rwa [← hv, ← mul_assoc, Units.inv_mul, one_mul] at this
  exact hell (hP.mem_of_pow_mem f hupow)


/-- 素理想幂之有限积在给定素理想处的重数。 -/
theorem emultiplicity_prod_pow {A : Type*} [CommRing A] [IsDedekindDomain A]
    {iota : Type*} (s : Finset iota) (Q : iota -> Ideal A) (e : iota -> Nat)
    (P : Ideal A) (hP : Prime P) :
    emultiplicity P (∏ i ∈ s, Q i ^ e i)
      = ∑ i ∈ s, (e i : ℕ∞) * emultiplicity P (Q i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using emultiplicity_of_one_right hP.not_isUnit
  | cons a s ha ih =>
      rw [Finset.prod_cons, emultiplicity_mul hP, emultiplicity_pow hP,
        Finset.sum_cons, ih]

/-- 不同的非零素理想互不整除，故重数为零。 -/
theorem emultiplicity_eq_zero_of_ne {A : Type*} [CommRing A] [IsDedekindDomain A]
    {P Q : Ideal A} (hP : P.IsPrime) (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    (hne : P ≠ Q) : emultiplicity P Q = 0 := by
  rw [emultiplicity_eq_zero]
  intro hdvd
  exact hne (((hQ.isMaximal hQ0).eq_of_le hP.ne_top (Ideal.dvd_iff_le.mp hdvd)).symm)

/-- **从逐素理想重数恢复理想分解。**  `Q` 在 `s` 上取值为互不相同的非零素理想，
`(Γ)` 在 `Q i` 处的重数是 `e i`、在其它素理想处为零，则 `(Γ) = ∏ Q i ^ e i`。

该引理将证明理想等式的目标化约为逐素理想的重数计算。 -/
theorem span_eq_prod_pow_of_emultiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    {iota : Type*} (s : Finset iota) (Q : iota -> Ideal A) (e : iota -> Nat)
    {Γ : A} (hΓ : Γ ≠ 0)
    (hQ : ∀ i ∈ s, (Q i).IsPrime) (hQ0 : ∀ i ∈ s, Q i ≠ ⊥)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, Q i = Q j -> i = j)
    (hat : ∀ i ∈ s, emultiplicity (Q i) (Ideal.span {Γ}) = (e i : ℕ∞))
    (hout : ∀ P : Ideal A, P.IsPrime -> P ≠ ⊥ -> (∀ i ∈ s, P ≠ Q i) ->
      emultiplicity P (Ideal.span {Γ}) = 0) :
    Ideal.span {Γ} = ∏ i ∈ s, Q i ^ e i := by
  classical
  have hspan : (Ideal.span {Γ} : Ideal A) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hΓ
  have hprod0 : (∏ i ∈ s, Q i ^ e i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ ?_
    simpa only [Ideal.zero_eq_bot] using hQ0 i hi
  refine ideal_eq_of_emultiplicity_eq hspan hprod0 fun P hP hP0 => ?_
  have hPprime : Prime P := Ideal.prime_of_isPrime hP0 hP
  rw [emultiplicity_prod_pow s Q e P hPprime]
  by_cases hmem : ∃ j ∈ s, P = Q j
  · obtain ⟨j, hj, hPj⟩ := hmem
    have hterm : ∀ i ∈ s, (e i : ℕ∞) * emultiplicity P (Q i)
        = if i = j then (e j : ℕ∞) else 0 := by
      intro i hi
      by_cases hij : i = j
      · have hQij : Q i = P := by rw [hij, hPj]
        have h1 : emultiplicity P (Q i) = 1 := by
          rw [hQij]
          simpa using emultiplicity_pow_self_of_prime hPprime 1
        rw [h1, mul_one, if_pos hij, hij]
      · have hne : P ≠ Q i := fun h => hij (hinj i hi j hj (h.symm.trans hPj))
        rw [emultiplicity_eq_zero_of_ne hP (hQ i hi) (hQ0 i hi) hne, mul_zero,
          if_neg hij]
    rw [Finset.sum_congr rfl hterm,
      Finset.sum_ite_eq' s j (fun _ => (e j : ℕ∞)), if_pos hj, hPj]
    exact hat j hj
  · have hout' : ∀ i ∈ s, P ≠ Q i := fun i hi h => hmem ⟨i, hi, h⟩
    have hzero : ∀ i ∈ s, (e i : ℕ∞) * emultiplicity P (Q i) = 0 := fun i hi => by
      rw [emultiplicity_eq_zero_of_ne hP (hQ i hi) (hQ0 i hi) (hout' i hi), mul_zero]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact hout P hP hP0 hout'


open scoped Classical in
/-- **由逐素理想重数恢复理想分解（纤维和形式）。**  这是
`span_eq_prod_pow_of_emultiplicity` 去掉单射假设后的版本：`Q` 在 `s` 上**允许重复**，
每个素理想处的指数是落在它上面的那一纤维的 `e` 之和。

去掉单射是必要的，不是方便：在 `ℚ(ζ_p)` 里共轭 `σ_a⁻¹ 𝔮` 只有当 `𝔮` 的分解群平凡
（即 `ell` 在 `ℚ(ζ_p)` 中完全分裂）才两两不同，一般情形它们按分解群的轨道重复。 -/
theorem span_eq_prod_pow_of_emultiplicity_fiber {A : Type*} [CommRing A] [IsDedekindDomain A]
    {iota : Type*} (s : Finset iota) (Q : iota → Ideal A) (e : iota → ℕ)
    {Γ : A} (hΓ : Γ ≠ 0)
    (hQ : ∀ i ∈ s, (Q i).IsPrime) (hQ0 : ∀ i ∈ s, Q i ≠ ⊥)
    (hall : ∀ P : Ideal A, P.IsPrime → P ≠ ⊥ →
      emultiplicity P (Ideal.span {Γ})
        = ∑ i ∈ s.filter (fun i => Q i = P), (e i : ℕ∞)) :
    Ideal.span {Γ} = ∏ i ∈ s, Q i ^ e i := by
  have hspan : (Ideal.span {Γ} : Ideal A) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hΓ
  have hprod0 : (∏ i ∈ s, Q i ^ e i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ ?_
    simpa only [Ideal.zero_eq_bot] using hQ0 i hi
  refine ideal_eq_of_emultiplicity_eq hspan hprod0 fun P hP hP0 => ?_
  have hPprime : Prime P := Ideal.prime_of_isPrime hP0 hP
  rw [emultiplicity_prod_pow s Q e P hPprime, hall P hP hP0, Finset.sum_filter]
  refine (Finset.sum_congr rfl fun i hi => ?_).symm
  by_cases h : Q i = P
  · have h1 : emultiplicity P (Q i) = 1 := by
      rw [h]
      simpa using emultiplicity_pow_self_of_prime hPprime 1
    rw [if_pos h, h1, mul_one]
  · rw [if_neg h,
      emultiplicity_eq_zero_of_ne hP (hQ i hi) (hQ0 i hi) (Ne.symm h), mul_zero]

end Catalan.Stickelberger
