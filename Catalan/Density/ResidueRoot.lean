module

public import Catalan.Density.Definitions

/-!
# `Catalan.Density.ResidueRoot`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Kummer

private lemma root_eq_one_of_reduction_eq_one
    (R E : Type*) [CommRing R] [IsDomain R] [Field E]
    (f : R →+* E) (q : ℕ) (hq : (q : E) ≠ 0)
    (x : R) (hpow : x ^ q = 1) (hred : f x = 1) : x = 1 := by
  by_contra hne
  have hsum : (Finset.range q).sum (fun i => x ^ i) = 0 := by
    have h := geom_sum_mul x q
    rw [hpow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have h := congrArg f hsum
  have hqzero : (q : E) = 0 := by
    simpa only [map_sum, map_pow, hred, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
  exact hq hqzero

lemma integral_root_fixed_of_residue_power
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (q ell : ℕ) (hq : q.Prime) (hell : ell.Prime) (hqell : q ≠ ell)
    (P : Ideal (𝓞 L)) (hPmax : P.IsMaximal) (hellP : (ell : 𝓞 L) ∈ P)
    (hcard : Nat.card (𝓞 K ⧸ P.under (𝓞 K)) = ell)
    (sigma : L ≃ₐ[K] L)
    (hfrob : ∀ x : 𝓞 L, Catalan.A3.integralAut sigma x - x ^ ell ∈ P)
    (zeta : (𝓞 K)ˣ) (hzeta : IsPrimitiveRoot (zeta : 𝓞 K) q)
    (u : (𝓞 K)ˣ) (r : (𝓞 L)ˣ)
    (hr : r ^ q = Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom u)
    (hres : ∃ v : (𝓞 K ⧸ P.under (𝓞 K))ˣ,
      v ^ q = Units.map (Ideal.Quotient.mk (P.under (𝓞 K))).toMonoidHom u) :
    Catalan.A3.integralAut sigma (r : 𝓞 L) = (r : 𝓞 L) := by
  classical
  let residueRootPMaximal : P.IsMaximal := hPmax
  let I : Ideal (𝓞 K) := P.under (𝓞 K)
  let residueRootIMaximal : I.IsMaximal := inferInstance
  let F := 𝓞 K ⧸ I
  let E := 𝓞 L ⧸ P
  let residueRootBaseField : Field F := Ideal.Quotient.field I
  let residueRootTopField : Field E := Ideal.Quotient.field P
  let residueRootLiesOver : P.LiesOver I := inferInstance
  let residueRootAlgebra : Algebra F E := inferInstance
  let red : 𝓞 L →+* E := Ideal.Quotient.mk P
  have hellZero : (ell : E) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact hellP
  let residueRootCharP : CharP E ell := (CharP.charP_iff_prime_eq_zero hell).mpr hellZero
  have hqE : (q : E) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime E hq hqell.symm
  let residueRootQNeZero : NeZero q := ⟨hq.ne_zero⟩
  let residueRootFiniteBase : Finite F := Nat.finite_of_card_ne_zero (hcard ▸ hell.ne_zero)
  let residueRootFintypeBase : Fintype F := Fintype.ofFinite F
  have hbase (x : 𝓞 K) :
      Catalan.A3.integralAut sigma (algebraMap (𝓞 K) (𝓞 L) x) =
        algebraMap (𝓞 K) (𝓞 L) x := by
    apply RingOfIntegers.coe_injective
    change sigma (algebraMap K L (x : K)) = algebraMap K L (x : K)
    exact sigma.commutes (x : K)
  have hredFrob (x : 𝓞 L) :
      red (Catalan.A3.integralAut sigma x) = (red x) ^ ell := by
    rw [← map_pow]
    exact (Ideal.Quotient.eq (I := P)).mpr (hfrob x)
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) := by
    intro a b hab
    apply RingOfIntegers.coe_injective
    apply (algebraMap K L).injective
    exact congrArg (fun x : 𝓞 L => (x : L)) hab
  let z : 𝓞 L := algebraMap (𝓞 K) (𝓞 L) (zeta : 𝓞 K)
  have hzpow : z ^ q = 1 := by
    dsimp only [z]
    rw [← map_pow, hzeta.pow_eq_one, map_one]
  have hzbarne : red z ≠ 1 := by
    intro hzred
    have hz1 := root_eq_one_of_reduction_eq_one (𝓞 L) E red q hqE z hzpow hzred
    apply hzeta.ne_one hq.one_lt
    apply hinj
    simpa only [z, map_one] using hz1
  have hzbarpow : (red z) ^ q = 1 := by rw [← map_pow, hzpow, map_one]
  have hzbar : IsPrimitiveRoot (red z) q :=
    isPrimitiveRoot_of_mem_nthRootsFinset hq
      ((Polynomial.mem_nthRootsFinset hq.pos (1 : E)).mpr hzbarpow) hzbarne
  have hzbarEll : (red z) ^ ell = red z := by
    have hh := hredFrob z
    have hzfix : Catalan.A3.integralAut sigma z = z := hbase (zeta : 𝓞 K)
    rw [hzfix] at hh
    exact hh.symm
  obtain ⟨v, hv⟩ := hres
  let vb : E := algebraMap F E (v : F)
  let rb : E := red (r : 𝓞 L)
  have hv0 : vb ≠ 0 := (Units.map (algebraMap F E).toMonoidHom v).ne_zero
  have hr0 : rb ≠ 0 := (Units.map red.toMonoidHom r).ne_zero
  have hrval : (r : 𝓞 L) ^ q = algebraMap (𝓞 K) (𝓞 L) (u : 𝓞 K) :=
    congrArg (fun a : (𝓞 L)ˣ => (a : 𝓞 L)) hr
  have hvval : (v : F) ^ q = Ideal.Quotient.mk I (u : 𝓞 K) :=
    congrArg (fun a : Fˣ => (a : F)) hv
  have hrbpow : rb ^ q = red (algebraMap (𝓞 K) (𝓞 L) (u : 𝓞 K)) := by
    dsimp only [rb]
    rw [← map_pow, hrval]
  have hvbpow : vb ^ q = red (algebraMap (𝓞 K) (𝓞 L) (u : 𝓞 K)) := by
    dsimp only [vb]
    rw [← map_pow, hvval]
    exact Ideal.Quotient.algebraMap_mk_of_liesOver P I (u : 𝓞 K)
  have hratio : (rb / vb) ^ q = 1 := by
    rw [div_pow, hrbpow, ← hvbpow, div_self (pow_ne_zero q hv0)]
  obtain ⟨j, _, hj⟩ := hzbar.eq_pow_of_pow_eq_one hratio
  have hrdecomp : rb = red z ^ j * vb := (div_eq_iff hv0).mp hj.symm
  have hvEll : (v : F) ^ ell = (v : F) := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card (v : F)
  have hvbEll : vb ^ ell = vb := by
    simpa only [map_pow, vb] using congrArg (algebraMap F E) hvEll
  have hrbEll : rb ^ ell = rb := by
    rw [hrdecomp, mul_pow, pow_right_comm, hzbarEll, hvbEll]
  have hredfixed : red (Catalan.A3.integralAut sigma (r : 𝓞 L)) = red (r : 𝓞 L) :=
    (hredFrob (r : 𝓞 L)).trans hrbEll
  let t : (𝓞 L)ˣ := Units.map (Catalan.A3.integralAut sigma).toMonoidHom r / r
  have hsigmapow : (Units.map (Catalan.A3.integralAut sigma).toMonoidHom r) ^ q = r ^ q := by
    rw [← map_pow, hr]
    apply Units.ext
    exact hbase (u : 𝓞 K)
  have htunit : t ^ q = 1 := by
    dsimp only [t]
    rw [div_pow, hsigmapow, div_self']
  have htval : (t : 𝓞 L) ^ q = 1 := congrArg (fun a : (𝓞 L)ˣ => (a : 𝓞 L)) htunit
  have htred : red (t : 𝓞 L) = 1 := by
    change ((Units.map red.toMonoidHom t : Eˣ) : E) = 1
    simp only [t, map_div, Units.val_div_eq_div_val, Units.coe_map]
    change red (Catalan.A3.integralAut sigma (r : 𝓞 L)) / red (r : 𝓞 L) = 1
    rw [hredfixed, div_self hr0]
  have htone : t = 1 := Units.ext
    (root_eq_one_of_reduction_eq_one (𝓞 L) E red q hqE (t : 𝓞 L) htval htred)
  have heq : Units.map (Catalan.A3.integralAut sigma).toMonoidHom r = r := div_eq_one.mp htone
  exact congrArg (fun a : (𝓞 L)ˣ => (a : 𝓞 L)) heq

end Catalan.Kummer
