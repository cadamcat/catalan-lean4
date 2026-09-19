import Catalan.Wieferich.DoubleWieferich
import Catalan.Wieferich.Action
import Catalan.IdealAction

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

def symmetrizedRootFactor
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (x : ℤ) : 𝓞 K :=
  ((x : 𝓞 K) - A1e.zetaInteger p K) *
    integerAut K (ι p K) ((x : 𝓞 K) - A1e.zetaInteger p K)

lemma symmetrizedRootFactor_coe
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (x : ℤ) (hp2 : p ≠ 2) :
    (symmetrizedRootFactor p K x : K) =
      (upow p K (xmζ p K x hp2) (1 + MonoidAlgebra.single (ι p K) 1) : K) := by
  let u : Kˣ := xmζ p K x hp2
  have hu : (u : K) = (x : K) - ζ p K := rfl
  have hzcoe : algebraMap (𝓞 K) K (A1e.zetaInteger p K) = ζ p K := rfl
  have hfield : (symmetrizedRootFactor p K x : K) =
      (u : K) * ι p K (u : K) := by
    simp [symmetrizedRootFactor, Catalan.integerAut,
      RingOfIntegers.mapRingEquiv_apply, u, xmζ, map_sub, map_intCast,
      hzcoe, A1e.iota_apply_zeta]
  have hupow_one : upow p K u (1 : R p K) = u := by
    change upow p K u (MonoidAlgebra.single (1 : G p K) (1 : ℤ)) = u
    simp only [upow_single, A1e.actUnit_one, zpow_one]
  have hupow : upow p K u (1 + MonoidAlgebra.single (ι p K) 1) =
      u * actUnit p K (ι p K) u := by
    rw [upow_add, hupow_one, upow_single, zpow_one]
  calc
    (symmetrizedRootFactor p K x : K) =
        ((u * actUnit p K (ι p K) u : Kˣ) : K) := by
      rw [hfield]
      rfl
    _ = (upow p K u (1 + MonoidAlgebra.single (ι p K) 1) : K) := by
      rw [hupow]
    _ = _ := rfl

lemma symmetrizedRootFactor_congruent_one
    (p q : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (x : ℤ) (hx : (q : ℤ) ^ 2 ∣ x) (g : G p K) :
    (q : 𝓞 K) ^ 2 ∣ integerAut K g (symmetrizedRootFactor p K x) - 1 := by
  let z : 𝓞 K := A1e.zetaInteger p K
  let zbar : 𝓞 K := integerAut K (ι p K) z
  have hzK : (z : K) = ζ p K := rfl
  have hzbarK : (zbar : K) = ι p K (z : K) := by
    simp [zbar, Catalan.integerAut, RingOfIntegers.mapRingEquiv_apply]
  have htrans : integerAut K (ι p K) ((x : 𝓞 K) - z) =
      (x : 𝓞 K) - zbar := by
    apply RingOfIntegers.coe_injective
    change ι p K ((x : K) - (z : K)) = (x : K) - (zbar : K)
    simp only [map_sub, map_intCast, hzbarK]
  have hzprod : z * zbar = 1 := by
    apply RingOfIntegers.coe_injective
    change (z : K) * (zbar : K) = 1
    rw [hzbarK, hzK, A1e.iota_apply_zeta]
    exact mul_inv_cancel₀ ((ζ_spec p K).ne_zero (Fact.out : p.Prime).ne_zero)
  have hfactor : symmetrizedRootFactor p K x - 1 =
      (x : 𝓞 K) * ((x : 𝓞 K) - z - zbar) := by
    change ((x : 𝓞 K) - z) * integerAut K (ι p K) ((x : 𝓞 K) - z) - 1 = _
    rw [htrans]
    calc
      _ = ((x : 𝓞 K) - z) * ((x : 𝓞 K) - zbar) - z * zbar := by rw [hzprod]
      _ = (x : 𝓞 K) * ((x : 𝓞 K) - z - zbar) := by ring
  have hxO : (q : 𝓞 K) ^ 2 ∣ (x : 𝓞 K) :=
    by simpa using map_dvd (Int.castRingHom (𝓞 K)) hx
  have hbase : (q : 𝓞 K) ^ 2 ∣ symmetrizedRootFactor p K x - 1 := by
    rw [hfactor]
    exact dvd_mul_of_dvd_left hxO _
  have hmap := map_dvd (integerAut K g).toRingHom hbase
  change integerAut K g ((q : 𝓞 K) ^ 2) ∣
    integerAut K g (symmetrizedRootFactor p K x - 1) at hmap
  simpa only [map_pow, map_natCast, map_sub, map_one] using hmap

lemma symmetrizedRootFactor_congruent_one_of_solution
    (p q : ℕ) [Fact p.Prime] (hq : q.Prime)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) (g : G p K) :
    (q : 𝓞 K) ^ 2 ∣ integerAut K g (symmetrizedRootFactor p K x) - 1 := by
  have hsq : (q : ℤ) ^ 2 ∣ x :=
    A1e.super_cassels p q (Fact.out : p.Prime) hq hp2 hq2 x y hx hy h
  exact symmetrizedRootFactor_congruent_one p q K x hsq g

end Catalan.Thaine
