/-
# Wolstenholme's theorem over Gaussian integers: the higher-power conjecture fails

## Source

Nikita Kalinin, *Wolstenholme's theorem over Gaussian integers*,
arXiv:2504.07978, Section 3 ("Higher powers"), Conjecture `conj:main`
("Wolstenholme's Higher-Power Congruences for Gaussian Integers").
Verbatim (LaTeX):

```
For any integer $k \geq 1$ and prime $p > 17$,
the sum $S_p^{(k)}$ satisfies:
S_p^{(k)}=\sum_{\substack{1\leq n,m\leq p-1\\(p,n^2+m^2)=1}}\frac{1}{(mi+n)^{k}}
  \equiv 0 \pmod{p^{m(k)}},
m(k) = 4, 3, 2, 1 if k \equiv 1, 2, 3, 0 \pmod 4.
One can write $m(k)$ as $m(k)=4-(k-1)\pmod 4.$
```

The paper's Motivation section fixes the meaning of `≡ 0 (mod p^e)` for a
Gaussian rational: it is `p^e` times a number whose denominator is prime to `p`.

## Status (recorded 2026-10-21)

The paper states this as an open conjecture (supported by computations with
`k ≤ 12`, `p < 1000`).  It is **false as printed**.  This module proves:

* `kalininConjecture_false`: the conjecture fails at `p = 29`, `k = 28`
  (`m(28) = 1`, but `S_{29}^{(28)} ≢ 0 (mod 29)`);
* `not_gaussCongZero_conjExponent_of_mod_four_eq_one`: it fails for every
  prime `p ≡ 1 (mod 4)` and every positive multiple `k` of `p - 1`.

Argument: clear denominators by `Q = ∏ (n²+m²)^k`, reduce modulo `p` along
`ℤ[i] → ZMod p`, `i ↦ c` with `c² = -1`; by Fermat every term becomes `1`,
so `S ≡ #pairs = (p-1)(p-3) ≡ 3 (mod p)`.  The refutation is proved even for
Gaussian-integer denominators not divisible by `p` (`mul_S_ne_of_not_dvd_card`),
so it does not depend on how "denominator prime to `p`" is read.
-/
import Mathlib

set_option autoImplicit false

namespace WolstenholmeGaussianRefutation

open Complex GaussianInt

/-- The index set of the sums `S_p^{(k)}`: pairs `(n, m)` with `1 ≤ n, m ≤ p - 1`
and `p ∤ n² + m²`. -/
def pairs (p : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 (p - 1) ×ˢ Finset.Icc 1 (p - 1)).filter (fun x => ¬ p ∣ x.1 ^ 2 + x.2 ^ 2)

/-- Kalinin's sum `S_p^{(k)} = ∑_{1 ≤ n, m ≤ p-1, (p, n²+m²) = 1} 1 / (n + m i)^k`. -/
noncomputable def S (p k : ℕ) : ℂ :=
  ∑ x ∈ pairs p, 1 / ((x.1 : ℂ) + (x.2 : ℂ) * I) ^ k

/-! Ground truth: for `p = 3` and `p = 7` (both `≡ 3 mod 4`) no pair is excluded; for
`p = 5, 13` (`≡ 1 mod 4`) exactly `2 (p - 1)` pairs are excluded. -/
example : (pairs 3).card = 4 := by decide
example : (pairs 5).card = 8 := by decide
example : (pairs 7).card = 36 := by decide +kernel
example : (pairs 13).card = 120 := by decide +kernel

/-- The index set for `p = 3`. -/
theorem pairs_three : pairs 3 = {(1, 1), (1, 2), (2, 1), (2, 2)} := by decide

/-- Ground truth: `S_3^{(1)} = 1/(1+i) + 1/(1+2i) + 1/(2+i) + 1/(2+2i) = 27/20 · (1 - i)`. -/
theorem S_three_one : S 3 1 = 27 / 20 * (1 - I) := by
  rw [S, pairs_three]
  apply Complex.ext
  · norm_num [Finset.sum_insert, Complex.div_re, Complex.normSq]
  · norm_num [Finset.sum_insert, Complex.div_im, Complex.normSq]

/-- The conjugate Gaussian integer `n - m i` attached to a pair. -/
def gzc (x : ℕ × ℕ) : GaussianInt := ⟨x.1, -(x.2 : ℤ)⟩

/-- The integer norm `n² + m²` of a pair. -/
def nrm (x : ℕ × ℕ) : ℤ := (x.1 : ℤ) ^ 2 + (x.2 : ℤ) ^ 2

/-- Clearing denominators: with `Q = ∏ (n²+m²)^k`, `Q · S_p^{(k)}` is the image of an
explicit Gaussian integer. -/
theorem clear_denominators (p k : ℕ) :
    ((∏ x ∈ pairs p, nrm x ^ k : ℤ) : ℂ) * S p k =
      toComplex (∑ x ∈ pairs p,
        ((∏ y ∈ (pairs p).erase x, nrm y ^ k : ℤ) : GaussianInt) * gzc x ^ k) := by
  classical
  rw [S, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hn : 1 ≤ x.1 := by
    simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
    exact hx.1.1.1
  have hz : (x.1 : ℂ) + (x.2 : ℂ) * I ≠ 0 := by
    intro h0
    have hre : (x.1 : ℝ) = 0 := by simpa using congrArg Complex.re h0
    have hx0 : x.1 = 0 := by exact_mod_cast hre
    omega
  have hQ : (∏ y ∈ pairs p, nrm y ^ k : ℤ) = nrm x ^ k * ∏ y ∈ (pairs p).erase x, nrm y ^ k :=
    (Finset.mul_prod_erase _ _ hx).symm
  have hnorm : ((nrm x : ℤ) : ℂ) = ((x.1 : ℂ) + (x.2 : ℂ) * I) * ((x.1 : ℂ) - (x.2 : ℂ) * I) := by
    simp only [nrm]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [hQ]
  simp only [map_mul, map_pow, map_intCast, gzc, toComplex_def']
  push_cast
  rw [hnorm]
  field_simp
  rw [mul_assoc _ (_ ^ k), ← mul_pow]
  ring

/-- For an index pair, `n² + m²` is a unit modulo `p`. -/
theorem nrm_ne_zero {p : ℕ} {x : ℕ × ℕ} (hx : x ∈ pairs p) : (nrm x : ZMod p) ≠ 0 := by
  have hndvd : ¬ p ∣ x.1 ^ 2 + x.2 ^ 2 := (Finset.mem_filter.mp hx).2
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hcast : nrm x = ((x.1 ^ 2 + x.2 ^ 2 : ℕ) : ℤ) := by
    simp only [nrm]
    push_cast
    ring
  rw [hcast, Int.natCast_dvd_natCast]
  exact hndvd

/-- Fermat in the form needed: a nonzero residue raised to a multiple of `p - 1` is `1`. -/
theorem pow_eq_one_of_dvd {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) {k : ℕ}
    (hk : p - 1 ∣ k) : a ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_mul, ZMod.pow_card_sub_one_eq_one ha, one_pow]

/-- The square root of `-1` packaged for `Zsqrtd.lift`. -/
def sqrtNegOne {p : ℕ} (c : ZMod p) (hc : c * c = -1) : {r : ZMod p // r * r = ((-1 : ℤ) : ZMod p)} :=
  ⟨c, by rw [hc]; push_cast; rfl⟩

/-- Reduction modulo the prime above `p` determined by `c`: if `d · S_p^{(k)} = p · w`
with Gaussian integers `d, w` and `p - 1 ∣ k`, then `φ(d) · #pairs = 0` in `ZMod p`, where
`φ : ℤ[i] → ZMod p` sends `i ↦ c`. -/
theorem lift_mul_card_eq_zero (p : ℕ) [Fact p.Prime] (c : ZMod p) (hc : c * c = -1) {k : ℕ}
    (hk : p - 1 ∣ k) (d w : GaussianInt) (h : toComplex d * S p k = (p : ℂ) * toComplex w) :
    Zsqrtd.lift (sqrtNegOne c hc) d * ((pairs p).card : ZMod p) = 0 := by
  classical
  set φ := Zsqrtd.lift (sqrtNegOne c hc) with hφ
  set Q : ℤ := ∏ x ∈ pairs p, nrm x ^ k with hQ
  set A : GaussianInt := ∑ x ∈ pairs p,
    ((∏ y ∈ (pairs p).erase x, nrm y ^ k : ℤ) : GaussianInt) * gzc x ^ k with hAdef
  have hA : (Q : ℂ) * S p k = toComplex A := clear_denominators p k
  have hkey : d * A = (p : GaussianInt) * ((Q : GaussianInt) * w) := by
    apply toComplex_injective
    rw [map_mul, ← hA, map_mul, map_mul, map_natCast, map_intCast]
    linear_combination (Q : ℂ) * h
  have hφA : φ A = ((pairs p).card : ZMod p) := by
    rw [hAdef, map_sum, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hprod : φ ((∏ y ∈ (pairs p).erase x, nrm y ^ k : ℤ) : GaussianInt) = 1 := by
      rw [map_intCast]
      push_cast
      refine Finset.prod_eq_one fun y hy => ?_
      exact pow_eq_one_of_dvd (nrm_ne_zero (Finset.mem_of_mem_erase hy)) hk
    have hconj : φ (gzc x) ≠ 0 := by
      intro h0
      apply nrm_ne_zero hx
      rw [hφ, Zsqrtd.lift_apply_apply] at h0
      have hfac : (nrm x : ZMod p) =
          ((x.1 : ZMod p) + (-(x.2 : ℤ) : ZMod p) * c) * ((x.1 : ZMod p) + (x.2 : ZMod p) * c) := by
        simp only [nrm]
        push_cast
        linear_combination ((x.2 : ZMod p) ^ 2) * hc
      rw [hfac]
      simp only [gzc, sqrtNegOne] at h0
      push_cast at h0 ⊢
      rw [h0, zero_mul]
    rw [map_mul, map_pow, hprod, pow_eq_one_of_dvd hconj hk, one_mul, Nat.cast_one]
  have hzero : φ (d * A) = 0 := by
    rw [hkey, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  rw [map_mul, hφA] at hzero
  exact hzero

/-- Core non-divisibility: for an odd prime `p` with a square root `c` of `-1` modulo `p`,
`p - 1 ∣ k` and `p ∤ #pairs`, no Gaussian integer `d` not divisible by `p` makes
`d · S_p^{(k)}` equal to `p` times a Gaussian integer. -/
theorem mul_S_ne_of_not_dvd_card (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (c : ZMod p)
    (hc : c * c = -1) {k : ℕ} (hk : p - 1 ∣ k) (hcard : ¬ p ∣ (pairs p).card)
    (d w : GaussianInt) (hd : ¬ (p : GaussianInt) ∣ d) :
    toComplex d * S p k ≠ (p : ℂ) * toComplex w := by
  intro h
  have hcard0 : ((pairs p).card : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hc' : (-c) * (-c) = -1 := by rw [neg_mul_neg, hc]
  have h1 := lift_mul_card_eq_zero p c hc hk d w h
  have h2 := lift_mul_card_eq_zero p (-c) hc' hk d w h
  rw [mul_eq_zero, or_iff_left hcard0, Zsqrtd.lift_apply_apply] at h1 h2
  simp only [sqrtNegOne] at h1 h2
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h20
    have h2dvd : p ∣ 2 := by exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h20)
    have hp : p.Prime := Fact.out
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd)
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero] at hc
    exact one_ne_zero (neg_eq_zero.mp hc.symm)
  have hre : (d.re : ZMod p) = 0 := by
    have h2re : (2 : ZMod p) * d.re = 0 := by linear_combination h1 + h2
    exact (mul_eq_zero.mp h2re).resolve_left htwo
  have him : (d.im : ZMod p) = 0 := by
    rw [hre, zero_add] at h1
    exact (mul_eq_zero.mp h1).resolve_right hc0
  apply hd
  rw [← Int.cast_natCast, Zsqrtd.intCast_dvd]
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hre,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp him⟩

/-! ## Counting the index set when `p ≡ 1 (mod 4)` -/

/-- For `p` prime with `c² = -1` and `1 ≤ m ≤ p - 1`, the `n ∈ [1, p-1]` with
`p ∣ n² + m²` are exactly the two residues `± c m`. -/
theorem fiber_eq (p : ℕ) [Fact p.Prime] (c : ZMod p) (hc : c * c = -1) {m : ℕ}
    (hm : m ∈ Finset.Icc 1 (p - 1)) :
    (Finset.Icc 1 (p - 1)).filter (fun n => p ∣ n ^ 2 + m ^ 2) =
      {(c * m).val, (-(c * m)).val} := by
  have hp : p.Prime := Fact.out
  have hp1 := hp.one_lt
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  have hm0 : (m : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn1, hn2⟩, hdvd⟩
    have hz : ((n : ZMod p) - c * m) * ((n : ZMod p) + c * m) = 0 := by
      have h0 : ((n ^ 2 + m ^ 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      push_cast at h0
      linear_combination h0 - (m : ZMod p) ^ 2 * hc
    have hnval : ((n : ZMod p)).val = n := ZMod.val_natCast_of_lt (by omega)
    rcases mul_eq_zero.mp hz with h | h
    · left
      rw [← hnval, sub_eq_zero.mp h]
    · right
      rw [← hnval, eq_neg_of_add_eq_zero_left h]
  · have hcm : c * m ≠ 0 := by
      refine mul_ne_zero ?_ hm0
      rintro rfl
      rw [mul_zero] at hc
      exact one_ne_zero (neg_eq_zero.mp hc.symm)
    have key : ∀ u : ZMod p, u ≠ 0 → u * u = -((m : ZMod p) ^ 2) →
        (1 ≤ u.val ∧ u.val ≤ p - 1) ∧ p ∣ u.val ^ 2 + m ^ 2 := by
      intro u hu huu
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero u).mpr hu), ?_⟩, ?_⟩
      · have := ZMod.val_lt u
        omega
      · rw [← ZMod.natCast_eq_zero_iff]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination huu
    rintro (rfl | rfl)
    · exact key _ hcm (by linear_combination (m : ZMod p) ^ 2 * hc)
    · exact key _ (neg_ne_zero.mpr hcm) (by linear_combination (m : ZMod p) ^ 2 * hc)

/-- For an odd prime `p` with a square root of `-1`, exactly `2 (p - 1)` pairs in
`[1, p-1]²` have `p ∣ n² + m²`. -/
theorem card_bad (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (c : ZMod p) (hc : c * c = -1) :
    ((Finset.Icc 1 (p - 1) ×ˢ Finset.Icc 1 (p - 1)).filter
      (fun x => p ∣ x.1 ^ 2 + x.2 ^ 2)).card = 2 * (p - 1) := by
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h20
    have h2dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h20)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd)
  rw [Finset.card_filter, Finset.sum_product_right]
  have hfib : ∀ m ∈ Finset.Icc 1 (p - 1),
      (∑ n ∈ Finset.Icc 1 (p - 1), if p ∣ (n, m).1 ^ 2 + (n, m).2 ^ 2 then 1 else 0) = 2 := by
    intro m hm
    rw [← Finset.card_filter, fiber_eq p c hc hm]
    refine Finset.card_pair fun hval => ?_
    have heq : c * m = -(c * m) := ZMod.val_injective p hval
    have hm0 : (m : ZMod p) ≠ 0 := by
      obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      have := hp.one_lt
      omega
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact one_ne_zero (neg_eq_zero.mp hc.symm)
    have h2cm : (2 : ZMod p) * (c * m) = 0 := by linear_combination heq
    exact mul_ne_zero htwo (mul_ne_zero hc0 hm0) h2cm
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
  omega

/-- For an odd prime `p` with a square root of `-1` (i.e. `p ≡ 1 mod 4`),
`#pairs = (p-1)² - 2(p-1) ≡ 3 (mod p)`. -/
theorem card_pairs_cast (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (c : ZMod p) (hc : c * c = -1) :
    ((pairs p).card : ZMod p) = 3 := by
  have hp : p.Prime := Fact.out
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 (p - 1) ×ˢ Finset.Icc 1 (p - 1))
    (fun x : ℕ × ℕ => p ∣ x.1 ^ 2 + x.2 ^ 2)
  rw [card_bad p hp2 c hc, Finset.card_product, Nat.card_Icc] at hsplit
  have hcast := congrArg (fun t : ℕ => (t : ZMod p)) hsplit
  simp only [Nat.cast_add, Nat.cast_mul] at hcast
  have hpm : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hpm' : ((p - 1 + 1 - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.add_sub_cancel, hpm]
  rw [hpm, hpm'] at hcast
  have hpairs : pairs p = (Finset.Icc 1 (p - 1) ×ˢ Finset.Icc 1 (p - 1)).filter
      (fun x => ¬ p ∣ x.1 ^ 2 + x.2 ^ 2) := rfl
  rw [← hpairs, Nat.cast_ofNat] at hcast
  linear_combination hcast

/-- `z ≡ 0 (mod p^e)` in the sense of the paper: `z = p^e · (a + b i) / D` with integers
`D, a, b` and `p ∤ D` (the denominator is prime to `p`). -/
def GaussCongZero (p e : ℕ) (z : ℂ) : Prop :=
  ∃ D a b : ℤ, ¬ (p : ℤ) ∣ D ∧ (D : ℂ) * z = (p : ℂ) ^ e * ((a : ℂ) + (b : ℂ) * I)

/-- Non-vacuity of the predicate: `20 · S_3^{(1)} = 3³ · (1 - i)`, so
`S_3^{(1)} ≡ 0 (mod 3³)`. -/
example : GaussCongZero 3 3 (S 3 1) :=
  ⟨20, 1, -1, by decide, by rw [S_three_one]; push_cast; ring⟩

/-- The conjectured exponent `m(k) = 4 - ((k - 1) mod 4)`: `4, 3, 2, 1` for
`k ≡ 1, 2, 3, 0 (mod 4)`, `k ≥ 1`. -/
def conjExponent (k : ℕ) : ℕ := 4 - (k - 1) % 4

example : conjExponent 1 = 4 := rfl
example : conjExponent 2 = 3 := rfl
example : conjExponent 3 = 2 := rfl
example : conjExponent 4 = 1 := rfl
example : conjExponent 5 = 4 := rfl
example : conjExponent 28 = 1 := rfl

/-- Kalinin's Conjecture `conj:main` (arXiv:2504.07978, Section 3) as printed: for every
integer `k ≥ 1` and every prime `p > 17`, `S_p^{(k)} ≡ 0 (mod p^{m(k)})`. -/
def KalininConjecture : Prop :=
  ∀ k p : ℕ, 1 ≤ k → p.Prime → 17 < p → GaussCongZero p (conjExponent k) (S p k)

/-- Under the hypotheses of `mul_S_ne_of_not_dvd_card`, `S_p^{(k)}` is not `≡ 0 (mod p^e)`
for any `e ≥ 1`. -/
theorem not_gaussCongZero_of_not_dvd_card (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (c : ZMod p)
    (hc : c * c = -1) {k : ℕ} (hk : p - 1 ∣ k) (hcard : ¬ p ∣ (pairs p).card) {e : ℕ}
    (he : 1 ≤ e) : ¬ GaussCongZero p e (S p k) := by
  rintro ⟨D, a, b, hD, h⟩
  refine mul_S_ne_of_not_dvd_card p hp2 c hc hk hcard (D : GaussianInt)
    ((p : GaussianInt) ^ (e - 1) * ⟨a, b⟩) ?_ ?_
  · rw [← Int.cast_natCast, Zsqrtd.intCast_dvd]
    rintro ⟨hre, -⟩
    exact hD (by simpa using hre)
  · rw [map_intCast, h, map_mul, map_pow, map_natCast, toComplex_def', ← mul_assoc, ← pow_succ',
      Nat.sub_add_cancel he]

/-- For `p = 29` there are `28² - 2·28 = 728 ≡ 3 (mod 29)` index pairs. -/
theorem card_pairs_29 : (pairs 29).card = 728 := by
  decide +kernel

/-- `12² = 144 ≡ -1 (mod 29)`. -/
theorem sqrt_neg_one_29 : (12 : ZMod 29) * 12 = -1 := by
  decide

/-- The concrete counterexample: `S_{29}^{(28)}` is not `≡ 0 (mod 29)`, although `m(28) = 1`. -/
theorem not_gaussCongZero_29_28 : ¬ GaussCongZero 29 (conjExponent 28) (S 29 28) := by
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  refine not_gaussCongZero_of_not_dvd_card 29 (by norm_num) 12 sqrt_neg_one_29
    (dvd_refl 28) ?_ (le_refl 1)
  rw [card_pairs_29]
  norm_num

/-- **Refutation of Kalinin's Conjecture `conj:main`** (arXiv:2504.07978, Section 3):
the higher-power Wolstenholme congruence fails as printed, already at `p = 29`, `k = 28`. -/
theorem kalininConjecture_false : ¬ KalininConjecture := fun h =>
  not_gaussCongZero_29_28 (h 28 29 (by norm_num) (by norm_num) (by norm_num))

/-- **General family.** For every prime `p ≡ 1 (mod 4)` and every multiple `k` of `p - 1`,
`S_p^{(k)} ≢ 0 (mod p^e)` for all `e ≥ 1`; indeed `S_p^{(k)} ≡ 3 (mod p)`. -/
theorem not_gaussCongZero_of_mod_four_eq_one {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    {k : ℕ} (hk : p - 1 ∣ k) {e : ℕ} (he : 1 ≤ e) : ¬ GaussCongZero p e (S p k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨c, hc⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  have hc' : c * c = -1 := hc.symm
  refine not_gaussCongZero_of_not_dvd_card p hp2 c hc' hk ?_ he
  intro hdvd
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by
    rw [← (ZMod.natCast_eq_zero_iff _ _).mpr hdvd, card_pairs_cast p hp2 c hc', Nat.cast_ofNat]
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff _ _).mp h3))

/-- **The conjecture fails on an infinite family.** For every prime `p ≡ 1 (mod 4)` and every
`k ≥ 1` with `p - 1 ∣ k`, the conjectured congruence `S_p^{(k)} ≡ 0 (mod p^{m(k)})` is false
(here `m(k) = 1`). This covers all such `p > 17`, e.g. `p = 29, 37, 41, ...`. -/
theorem not_gaussCongZero_conjExponent_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) {k : ℕ} (hk0 : 1 ≤ k) (hk : p - 1 ∣ k) :
    ¬ GaussCongZero p (conjExponent k) (S p k) := by
  have h4p : 4 ∣ p - 1 := ⟨p / 4, by omega⟩
  have h4 : 4 ∣ k := h4p.trans hk
  have hm : conjExponent k = 1 := by
    obtain ⟨j, rfl⟩ := h4
    simp only [conjExponent]
    omega
  rw [hm]
  exact not_gaussCongZero_of_mod_four_eq_one hp hp4 hk le_rfl

end WolstenholmeGaussianRefutation
