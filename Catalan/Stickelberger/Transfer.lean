import Catalan.Stickelberger.Factor
import Catalan.Stickelberger.Uniformizer
import Mathlib

/-! # Cyclotomic tower and valuation transfer

Two independent ingredients of the transfer of a Gauss-sum valuation from the big
cyclotomic tower of conductor `ell * (ell ^ f - 1)` down to `ℚ(ζ_p)`:

* `isCyclotomicExtension_tower`: the intermediate field `ℚ(ζ_p)` really sits inside the
  big cyclotomic field whenever `p ∣ N`, with the cyclotomic structure on both steps;
* `emultiplicity_map_eq_ramificationIdx_mul`: multiplicities upstairs are multiplicities
  downstairs scaled by the ramification index.

Neither computes a Gauss-sum valuation; the transfer itself is not assembled here.
-/

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger

open Ideal UniqueFactorizationMonoid IsCyclotomicExtension

/-- 记号：`L` 中由 `p` 次单位根生成的子代数，即 `ℚ(ζ_p)` 在 `L` 里的实现。 -/
abbrev cycloSub (p : ℕ) (L : Type*) [Field L] [Algebra ℚ L] :=
  Algebra.adjoin ℚ {b : L | ∃ a ∈ ({p} : Set ℕ), a ≠ 0 ∧ b ^ a = 1}

/-- **圆分赋值转移所需的圆分塔存在。** 若 `p ∣ N` 且 `L` 是导子 `N` 的圆分域，
则 `L` 内部就有一个中间域 `ℚ(ζ_p)`：它对 `ℚ` 是导子 `p` 的圆分扩张，而 `L` 对它是导子 `N` 的圆分扩张。

这正是把赋值从大塔搬回 `ℚ(ζ_p)` 所需的塔结构。注意 `p ∣ ell^f − 1 ∣ N`（`N = ell·(ell^f−1)`），
所以这个可除性条件在 Stickelberger 的设定下自动成立。 -/
theorem isCyclotomicExtension_tower (N p : ℕ) [NeZero p] (hN : N ≠ 0) (hdvd : p ∣ N)
    (L : Type*) [Field L] [CharZero L] [Algebra ℚ L] [IsCyclotomicExtension {N} ℚ L] :
    IsCyclotomicExtension {p} ℚ (cycloSub p L) ∧
      IsCyclotomicExtension {N} (cycloSub p L) L := by
  have hbig : IsCyclotomicExtension ({N} ∪ {p}) ℚ L :=
    of_union_of_dvd (n := p) ℚ L ⟨N, rfl, hN, hdvd⟩
  have hbig' : IsCyclotomicExtension (({p} : Set ℕ) ∪ {N}) ℚ L := by
    rwa [Set.union_comm]
  refine ⟨union_left ({p} : Set ℕ) (({p} : Set ℕ) ∪ {N}) ℚ L Set.subset_union_left, ?_⟩
  exact union_right ({p} : Set ℕ) ({N} : Set ℕ) ℚ L


/-- `P` 位于 `q` 上方时，`q` 推到 `B` 后落在 `P` 之内。 -/
theorem ramTransfer_map_le {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal A) (P : Ideal B) [P.LiesOver q] :
    Ideal.map (algebraMap A B) q ≤ P :=
  Ideal.map_le_of_le_comap (P.over_def q).le

/-- **分歧指数就是 `q` 推上去之后在 `P` 处的重数**（`emultiplicity` 版本）。 -/
theorem ramTransfer_emultiplicity_map_self {A B : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] (q : Ideal A) (P : Ideal B)
    [P.IsPrime] [P.LiesOver q] (hmap : Ideal.map (algebraMap A B) q ≠ ⊥) :
    emultiplicity P (Ideal.map (algebraMap A B) q) = (P.ramificationIdx A : ℕ∞) := by
  have hP0 : P ≠ ⊥ := fun h => hmap (le_bot_iff.mp (h ▸ ramTransfer_map_le q P))
  have hmap0 : Ideal.map (algebraMap A B) q ≠ 0 := by
    simpa only [Ideal.zero_eq_bot] using hmap
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count q P hmap,
    emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime hP0 inferInstance).irreducible hmap0, normalize_eq]

/-- 不位于 `P` 下方的素理想推上去之后不被 `P` 整除。 -/
theorem ramTransfer_emultiplicity_map_eq_zero {A B : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] (q : Ideal A) (P : Ideal B)
    [hq : q.IsMaximal] [P.IsPrime] [P.LiesOver q] {q' : Ideal A} (hq' : q'.IsPrime)
    (hq'0 : q' ≠ ⊥) (hne : q' ≠ q) :
    emultiplicity P (Ideal.map (algebraMap A B) q') = 0 := by
  rw [emultiplicity_eq_zero]
  intro hdvd
  have hle : Ideal.map (algebraMap A B) q' ≤ P := Ideal.dvd_iff_le.mp hdvd
  have hsub : q' ≤ q := by
    rw [P.over_def q]
    intro x hx
    rw [Ideal.mem_under]
    exact hle (Ideal.mem_map_of_mem _ hx)
  exact hne ((hq'.isMaximal hq'0).eq_of_le hq.ne_top hsub)

/-- 赋值随分歧指数放大：`A ⊆ B` 都是 Dedekind 整环，`P` 是 `B` 的极大理想、位于 `A` 的极大理想 `q`
上方，则 `A` 的任意非零理想 `I` 推到 `B` 后在 `P` 处的重数，等于它在 `q` 处的重数乘 `e(P/q)`。 -/
theorem emultiplicity_map_eq_ramificationIdx_mul
    {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] (q : Ideal A) (P : Ideal B) [q.IsMaximal] [P.IsMaximal] [P.LiesOver q]
    (hmap : Ideal.map (algebraMap A B) q ≠ ⊥)
    (I : Ideal A) (hI : I ≠ ⊥) :
    emultiplicity P (Ideal.map (algebraMap A B) I)
      = (P.ramificationIdx A : ℕ∞) * emultiplicity q I := by
  classical
  have hq0 : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmap
    exact hmap rfl
  have hP0 : P ≠ ⊥ := fun h => hmap (le_bot_iff.mp (h ▸ ramTransfer_map_le q P))
  have hqprime : Prime q := Ideal.prime_of_isPrime hq0 inferInstance
  have hPprime : Prime P := Ideal.prime_of_isPrime hP0 inferInstance
  have hram : emultiplicity P (Ideal.map (algebraMap A B) q) = (P.ramificationIdx A : ℕ∞) :=
    ramTransfer_emultiplicity_map_self q P hmap
  -- 素理想情形
  have hprime_case : ∀ p : Ideal A, Prime p →
      emultiplicity P (Ideal.map (algebraMap A B) p)
        = (P.ramificationIdx A : ℕ∞) * emultiplicity q p := by
    intro p hp
    by_cases hpq : p = q
    · subst hpq
      have h1 : emultiplicity p p = 1 := by
        simpa using emultiplicity_pow_self_of_prime hp 1
      rw [hram, h1, mul_one]
    · have hp0 : p ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hp.ne_zero
      rw [ramTransfer_emultiplicity_map_eq_zero q P (Ideal.isPrime_of_prime hp) hp0 hpq,
        emultiplicity_eq_zero_of_ne inferInstance (Ideal.isPrime_of_prime hp) hp0
          (Ne.symm hpq), mul_zero]
  -- 对 `I` 的素分解归纳
  have key : ∀ J : Ideal A, J ≠ 0 →
      emultiplicity P (Ideal.map (algebraMap A B) J)
        = (P.ramificationIdx A : ℕ∞) * emultiplicity q J := by
    intro J
    induction J using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => exact fun h => absurd rfl h
    | h₂ x hx =>
        intro _
        rw [Ideal.isUnit_iff] at hx
        subst hx
        rw [Ideal.map_top]
        simp only [← Ideal.one_eq_top, emultiplicity_of_one_right hPprime.not_isUnit,
          emultiplicity_of_one_right hqprime.not_isUnit, mul_zero]
    | h₃ a p ha hp ih =>
        intro _
        rw [Ideal.map_mul, emultiplicity_mul hPprime, emultiplicity_mul hqprime, mul_add,
          ih ha, hprime_case p hp]
  exact key I (by simpa only [Ideal.zero_eq_bot] using hI)

/-! ### 塔中的分歧指数

⚠ 下面这条把三个塔实例（`Algebra (𝓞 K) (𝓞 L)`、`IsScalarTower`、`Module.Flat`）当作**假设**；
此处没有为实际的 `ℚ(ζ_p) ⊆ ℚ(ζ_N)` 构造这些实例。 -/

open NumberField in
/-- 塔中分歧指数的商：`ell` 在大圆分域 `L`（导子 `N = ell·(ell^f−1)`）中全分歧、指数 `ell−1`，
在 `K = ℚ(ζ_p)` 中不分歧、指数 `1`，故 `P` 对 `𝓞 K` 的分歧指数是 `ell−1`。 -/
theorem ramificationIdx_tower_eq (ell p f m N : ℕ) [Fact ell.Prime] [Fact p.Prime]
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [IsCyclotomicExtension {p} ℚ K] [IsCyclotomicExtension {N} ℚ L]
    [Algebra (𝓞 K) (𝓞 L)] [IsScalarTower ℤ (𝓞 K) (𝓞 L)] [Module.Flat (𝓞 K) (𝓞 L)]
    (q : Ideal (𝓞 K)) [q.IsPrime] [q.LiesOver (Ideal.span {(ell : ℤ)})]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(ell : ℤ)})] [P.LiesOver q]
    (hell : 2 < ell) (hne : ell ≠ p) (hf : 0 < f)
    (hm : m = ell ^ f - 1) (hN : N = ell * m) :
    P.ramificationIdx (𝓞 K) = ell - 1 := by
  have hEllNotDvdP : ¬ell ∣ p := by
    intro hdiv
    apply hne
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime ell)
      (Fact.out : Nat.Prime p)).mp hdiv
  have hmNotDvd : ¬ell ∣ m := not_dvd_of_eq_pow_sub_one hell hf hm
  have hPZ : P.ramificationIdx ℤ = ell - 1 := by
    have h := IsCyclotomicExtension.Rat.ramificationIdx_eq (p := ell) (k := 0) (m := m)
      N L P (by rw [hN, pow_one]) hmNotDvd
    simpa using h
  have hqZ : q.ramificationIdx ℤ = 1 := by
    exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd ell K q hEllNotDvdP
  have htower : P.ramificationIdx ℤ =
      q.ramificationIdx ℤ * P.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower q P
  rw [hPZ, hqZ] at htower
  simpa using htower.symm

/-- 中间域形式的圆分塔：`p ∣ N` 时，`ℚ(ζ_N)` 内由 `p` 次单位根生成的**中间域**
对 `ℚ` 是导子 `p` 的圆分扩张。子代数形式合不出 `Field` 实例，中间域形式可以。 -/
theorem isCyclotomicExtension_intermediateField (N p : ℕ) [NeZero p] (hN : N ≠ 0) (hdvd : p ∣ N)
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] :
    IsCyclotomicExtension {p} ℚ
      (IntermediateField.adjoin ℚ {b : L | ∃ a ∈ ({p} : Set ℕ), a ≠ 0 ∧ b ^ a = 1}) := by
  have hcyclo :
      IsCyclotomicExtension {p} ℚ
        (Algebra.adjoin ℚ {b : L | ∃ a ∈ ({p} : Set ℕ), a ≠ 0 ∧ b ^ a = 1}) :=
    (isCyclotomicExtension_tower N p hN hdvd L).1
  have hadjoin :
      (IntermediateField.adjoin ℚ {b : L | ∃ a ∈ ({p} : Set ℕ), a ≠ 0 ∧ b ^ a = 1}).toSubalgebra =
        Algebra.adjoin ℚ {b : L | ∃ a ∈ ({p} : Set ℕ), a ≠ 0 ∧ b ^ a = 1} :=
    IntermediateField.adjoin_toSubalgebra _
  exact IsCyclotomicExtension.equiv ({p} : Set ℕ) ℚ _ (h := hcyclo)
    (Subalgebra.equivOfEq _ _ hadjoin.symm)

end Catalan.Stickelberger
