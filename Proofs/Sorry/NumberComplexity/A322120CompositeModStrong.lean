/-
# A322120 — Ordowski: composites with `b^(m-1) ≡ 1 (mod (b^2-1) m)` are strong pseudoprimes

## OEIS source (retrieved with `oeis show A322120`, live entry checked, 2026-10-21)

```
NAME:     a(n) is the smallest composite k such that n^(k-1) == 1 (mod (n^2-1)*k).
OFFSET:   2
TERMS:    341,91,91,217,481,25,65,91,91,133,133,85,781,341,91,91,25,49,671,221,...
COMMENT:  a(n) >= A271801(n). All terms are odd and indivisible by 3.
COMMENT (the conjecture):
  Conjecture: if m is a composite number such that b^(m-1) == 1 (mod (b^2-1)m)
  for some b, then m is a strong pseudoprime to some base a in the range
  2 <= a <= m-2. Thus, probably every term a(n) is in A181782.
AUTHOR:   Thomas Ordowski, Nov 27 2018 (the conjecture line is unsigned; it is
          part of the original submission).
```

A181782: "Odd composite numbers n that are strong pseudoprimes to some base a,
2 <= a <= n-2."  The PARI program there (Arndt, Hasler) is the Miller–Rabin
test: write `n - 1 = 2^t q` with `q` odd; accept iff `a^q ≡ 1 (mod n)` or
`a^(2^e q) ≡ -1 (mod n)` for some `e < t`.

## Status

Open in the entry (no proof given).  Triage (2026-10) found no proof in the
literature and sketched an elementary one.  This file proves the conjecture
(`a322120_conjecture`, sorry-free) by a variant of that argument; the variant
needs no element of odd prime order, only the image of `b` itself.
The base `b` in the conjecture is read as `b ≥ 2`: for `b = 1` the modulus
`(b^2-1) m` is `0` and the congruence `1 ≡ 1` holds for every `m`, which would
make the statement false (e.g. `m = 9` is not in A181782).

## Proof (formalized below)

Write `B = b mod m`, `m - 1 = 2^s d` with `d` odd.
* `m` is odd: for even `m`, `b^(m-1) ≡ b (mod b^2-1)`, forcing `b^2-1 ∣ b-1`.
* Key lemma: no prime `p ∣ m` has `b^2 ≡ 1 (mod p)`.  Otherwise
  `b^(m-1) - 1 = (b^2-1) S` with `S = Σ_{i<(m-1)/2} b^(2i) ≡ (m-1)/2 (mod p)`,
  and `(b^2-1) m ∣ (b^2-1) S` gives `p ∣ m ∣ S`, so `p ∣ (m-1)/2`, `p ∣ 1`.
* Case A, `B^(2^s) ≠ 1`: `a = B^(2^s)` has `a^d = B^(m-1) = 1` and
  `a ≠ 0, ±1`, so `a` is a strong liar.
* Case B, `B^(2^s) = 1`: for every prime power `p^n ∣ m` the image of `b` has
  2-power order `≥ 4` in `ZMod (p^n)`, and `±1` are the only square roots of
  `1` there (`p` odd), so `-1` is a square mod `p^n`; by CRT `-1 = z^2` in
  `ZMod m`.  Since `s ≥ 2`, `a = z` satisfies `a^(2d) = -1`, and `a ≠ 0, ±1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A322120CompositeModStrong

/-! ## Definition layer -/

/-- `IsStrongProbablePrime m a`: `m` passes the Miller–Rabin test to base `a`.
Writing `m - 1 = 2^s * d` with `d` odd, either `a^d ≡ 1 (mod m)` or
`a^(2^r d) ≡ m - 1 ≡ -1 (mod m)` for some `r < s`.  The decomposition is
unique, and for `2 ≤ m` it automatically has `s < m` and `d < m`; the bounds
are stated only to make the predicate decidable. -/
def IsStrongProbablePrime (m a : ℕ) : Prop :=
  ∃ s < m, ∃ d < m, m - 1 = 2 ^ s * d ∧ Odd d ∧
    (a ^ d ≡ 1 [MOD m] ∨ ∃ r < s, a ^ (2 ^ r * d) ≡ m - 1 [MOD m])

instance (m a : ℕ) : Decidable (IsStrongProbablePrime m a) := by
  unfold IsStrongProbablePrime; infer_instance

/-- Membership in A181782: `n` is an odd composite number that is a strong
pseudoprime to some base `a` with `2 ≤ a ≤ n - 2`. -/
def InA181782 (n : ℕ) : Prop :=
  Odd n ∧ 1 < n ∧ ¬ n.Prime ∧ ∃ a, 2 ≤ a ∧ a ≤ n - 2 ∧ IsStrongProbablePrime n a

/-- The defining property of A322120 at index `n`: `k` is composite and
`n^(k-1) ≡ 1 (mod (n^2-1) k)`.  The term `a(n)` is the least such `k`. -/
def A322120Prop (n k : ℕ) : Prop :=
  1 < k ∧ ¬ k.Prime ∧ n ^ (k - 1) ≡ 1 [MOD (n ^ 2 - 1) * k]

instance (n k : ℕ) : Decidable (A322120Prop n k) := by
  unfold A322120Prop; infer_instance

/-! ## Fidelity: the decomposition `m - 1 = 2^s d` is unique

So the existential over `(s, d)` in `IsStrongProbablePrime` is the Miller–Rabin
test with the canonical `s = ν₂(m - 1)`, `d = (m - 1) / 2^s` (as in the PARI
program of A181782). -/

/-- `ν₂(2^s d) = s` for odd `d`. -/
theorem factorization_two_pow_mul_odd (s d : ℕ) (hd : Odd d) :
    (2 ^ s * d).factorization 2 = s := by
  have hd0 : d ≠ 0 := hd.pos.ne'
  have hnd : ¬ 2 ∣ d := by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]
  rw [Nat.factorization_mul (pow_ne_zero s two_ne_zero) hd0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hnd,
    add_zero]

/-- Uniqueness of the decomposition `2^s d` with `d` odd. -/
theorem two_pow_mul_odd_inj {s d s' d' : ℕ} (hd : Odd d) (hd' : Odd d')
    (h : 2 ^ s * d = 2 ^ s' * d') : s = s' ∧ d = d' := by
  have hs : s = s' := by
    rw [← factorization_two_pow_mul_odd s d hd, h, factorization_two_pow_mul_odd s' d' hd']
  subst hs
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos s) h⟩

/-! ## Ground truth -/

/-- `a(7) = 25` (the sixth listed term). -/
example : IsLeast {k | A322120Prop 7 k} 25 := by
  refine ⟨by decide, fun k hk => ?_⟩
  have hsmall : ∀ k < 25, ¬ A322120Prop 7 k := by decide
  by_contra hlt
  exact hsmall k (Nat.lt_of_not_le hlt) hk

set_option exponentiation.threshold 400 in
/-- `a(3) = 91` and `a(2) = 341` satisfy the defining property. -/
example : A322120Prop 3 91 ∧ A322120Prop 2 341 := by
  exact ⟨⟨by norm_num, by norm_num, by decide⟩, ⟨by norm_num, by norm_num, by decide⟩⟩

/-- `25` (base `7`), `49` (base `18`), `91` (base `9`) and `341` (base `4`)
are in A181782, with the Miller–Rabin data `m - 1 = 2^s d` displayed. -/
example : InA181782 25 ∧ InA181782 49 ∧ InA181782 91 ∧ InA181782 341 := by
  refine ⟨⟨by decide, by norm_num, by norm_num, 7, by norm_num, by norm_num,
      3, by norm_num, 3, by norm_num, by norm_num, by decide, Or.inr ⟨1, by norm_num, by decide⟩⟩,
    ⟨by decide, by norm_num, by norm_num, 18, by norm_num, by norm_num,
      4, by norm_num, 3, by norm_num, by norm_num, by decide, Or.inl (by decide)⟩,
    ⟨by decide, by norm_num, by norm_num, 9, by norm_num, by norm_num,
      1, by norm_num, 45, by norm_num, by norm_num, by decide, Or.inl (by decide)⟩,
    ⟨by decide, by norm_num, by norm_num, 4, by norm_num, by norm_num,
      2, by norm_num, 85, by norm_num, by norm_num, by decide, Or.inl (by decide)⟩⟩

/-- The odd composites `9`, `15`, `21` are not in A181782. -/
example : ¬ InA181782 9 ∧ ¬ InA181782 15 ∧ ¬ InA181782 21 := by
  have h9 : ∀ a < 8, 2 ≤ a → ¬ IsStrongProbablePrime 9 a := by decide
  have h15 : ∀ a < 14, 2 ≤ a → ¬ IsStrongProbablePrime 15 a := by decide
  have h21 : ∀ a < 20, 2 ≤ a → ¬ IsStrongProbablePrime 21 a := by decide
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, -, -, a, ha2, ha, hsp⟩
    exact h9 a (by omega) ha2 hsp
  · rintro ⟨-, -, -, a, ha2, ha, hsp⟩
    exact h15 a (by omega) ha2 hsp
  · rintro ⟨-, -, -, a, ha2, ha, hsp⟩
    exact h21 a (by omega) ha2 hsp

/-! ## Helper lemmas -/

/-- Under the hypothesis, `m` is odd: for even `m ≥ 2`, `b^(m-1) ≡ b (mod b^2-1)`,
which would force `b^2 - 1 ∣ b - 1`. -/
theorem odd_of_modEq {m b : ℕ} (hm : 1 < m) (hb : 2 ≤ b)
    (h : b ^ (m - 1) ≡ 1 [MOD (b ^ 2 - 1) * m]) : Odd m := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨t, ht⟩ := hev
  have hmt : m - 1 = 2 * (t - 1) + 1 := by omega
  have h1 : b ^ (m - 1) ≡ 1 [MOD b ^ 2 - 1] := Nat.ModEq.of_mul_right m h
  have hb1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsq : ((b : ZMod (b ^ 2 - 1))) ^ 2 = 1 := by
    have : ((b ^ 2 - 1 + 1 : ℕ) : ZMod (b ^ 2 - 1)) = 1 := by
      rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    rw [Nat.sub_add_cancel hb1, Nat.cast_pow] at this
    exact this
  have hbmod : ((b : ZMod (b ^ 2 - 1))) = 1 := by
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    have hexp : ((b : ZMod (b ^ 2 - 1))) ^ (m - 1) = ((b : ZMod (b ^ 2 - 1)) ^ 2) ^ (t - 1) * b := by
      rw [hmt]; ring
    rw [Nat.cast_pow, hexp, hsq, one_pow, one_mul, Nat.cast_one] at h2
    exact h2
  have h3 : b ≡ 1 [MOD b ^ 2 - 1] := by
    rw [← ZMod.natCast_eq_natCast_iff, hbmod, Nat.cast_one]
  have h4 : b ^ 2 - 1 ∣ b - 1 := (Nat.modEq_iff_dvd' (by omega)).mp h3.symm
  have h5 : b ^ 2 - 1 ≤ b - 1 := Nat.le_of_dvd (by omega) h4
  have h6 : b < b ^ 2 := by nlinarith
  omega

/-- Key lemma: under the hypothesis (with `m` odd), no prime `p ∣ m` has
`b^2 ≡ 1 (mod p)`.  Otherwise `b^(m-1) - 1 = (b^2-1) S` with
`S = Σ_{i<(m-1)/2} b^(2i) ≡ (m-1)/2 (mod p)` and `m ∣ S`, so `p ∣ 1`. -/
theorem sq_ne_one_of_prime_dvd {m b p : ℕ} (hm : 1 < m) (hodd : Odd m) (hb : 2 ≤ b)
    (h : b ^ (m - 1) ≡ 1 [MOD (b ^ 2 - 1) * m]) (hp : p.Prime) (hpm : p ∣ m) :
    ((b : ZMod p)) ^ 2 ≠ 1 := by
  intro hb2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := hodd
  have hmt : m - 1 = 2 * t := by omega
  have hb1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ (by omega)
  -- `(b^2 - 1) m ∣ (b^2)^t - 1` in `ℤ`
  have hdvd : ((b : ℤ) ^ 2 - 1) * (m : ℤ) ∣ ((b : ℤ) ^ 2) ^ t - 1 := by
    have h1 := (Nat.ModEq.dvd h.symm)
    rw [← pow_mul, ← hmt]
    push_cast [Nat.cast_sub hb1] at h1
    exact h1
  set S : ℤ := ∑ i ∈ Finset.range t, ((b : ℤ) ^ 2) ^ i with hS
  have hgeom : ((b : ℤ) ^ 2 - 1) * S = ((b : ℤ) ^ 2) ^ t - 1 := mul_geom_sum _ _
  have hne : ((b : ℤ) ^ 2 - 1) ≠ 0 := by
    have h4 : (4 : ℤ) ≤ (b : ℤ) ^ 2 := by
      have h2 : (2 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    linarith
  -- cancel `b^2 - 1`: `m ∣ S`
  have hmS : (m : ℤ) ∣ S := by
    rw [← hgeom] at hdvd
    exact (mul_dvd_mul_iff_left hne).mp hdvd
  have hpS : (p : ℤ) ∣ S := (Int.natCast_dvd_natCast.mpr hpm).trans hmS
  have hS0 : (S : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd S p).mpr hpS
  -- `S ≡ t (mod p)` because `b^2 ≡ 1 (mod p)`
  have hSt : (S : ZMod p) = (t : ZMod p) := by
    rw [hS]
    push_cast
    simp [hb2]
  have hm0 : (m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr hpm
  have h10 : (1 : ZMod p) = 0 := by
    have hm2 : (m : ZMod p) = 2 * (t : ZMod p) + 1 := by rw [ht]; push_cast; ring
    rw [hm0, ← hSt, hS0] at hm2
    simpa using hm2.symm
  exact one_ne_zero h10

/-- In `ZMod (p^n)` with `p` an odd prime, the only square roots of `1` are `±1`. -/
theorem eq_neg_one_of_sq_eq_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (y : ZMod (p ^ n))
    (hy : y ^ 2 = 1) (hy1 : y ≠ 1) : y = -1 := by
  obtain ⟨Y, rfl⟩ := ZMod.intCast_surjective y
  have hprod : ((p ^ n : ℕ) : ℤ) ∣ (Y - 1) * (Y + 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination hy
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  push_cast at hprod
  by_cases hd : (p : ℤ) ∣ Y + 1
  · have hnd : ¬ (p : ℤ) ∣ Y - 1 := by
      intro hd'
      have h2 : (p : ℤ) ∣ 2 := by
        have := dvd_sub hd hd'
        ring_nf at this
        exact this
      have : p ∣ 2 := by exact_mod_cast h2
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
      exact hp2 this
    have hcop : IsCoprime ((p : ℤ) ^ n) (Y - 1) :=
      ((Prime.coprime_iff_not_dvd hpZ).mpr hnd).pow_left
    have h' : (p : ℤ) ^ n ∣ Y + 1 := hcop.dvd_of_dvd_mul_left hprod
    have h'' : ((Y + 1 : ℤ) : ZMod (p ^ n)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (Y + 1) (p ^ n)).mpr (by exact_mod_cast h')
    push_cast at h''
    linear_combination h''
  · have hcop : IsCoprime ((p : ℤ) ^ n) (Y + 1) :=
      ((Prime.coprime_iff_not_dvd hpZ).mpr hd).pow_left
    have h' : (p : ℤ) ^ n ∣ Y - 1 := hcop.dvd_of_dvd_mul_right hprod
    have h'' : ((Y - 1 : ℤ) : ZMod (p ^ n)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (Y - 1) (p ^ n)).mpr (by exact_mod_cast h')
    push_cast at h''
    exact absurd (by linear_combination h'') hy1

/-- In a commutative ring whose only square roots of `1` are `±1`, an element `x`
with `x^(2^s) = 1` but `x^2 ≠ 1` yields a square root of `-1`. -/
theorem isSquare_neg_one_of_pow_two_pow_eq_one {R : Type*} [CommRing R]
    (hR : ∀ y : R, y ^ 2 = 1 → y ≠ 1 → y = -1) {x : R} {s : ℕ}
    (hx : x ^ 2 ^ s = 1) (hx2 : x ^ 2 ≠ 1) : IsSquare (-1 : R) := by
  have key : ∀ j : ℕ, x ^ 2 ^ (j + 2) = 1 → IsSquare (-1 : R) := by
    intro j
    induction j with
    | zero =>
      intro h4
      have hy : (x ^ 2) ^ 2 = 1 := by rw [← pow_mul]; simpa using h4
      exact ⟨x, by rw [← hR _ hy hx2]; ring⟩
    | succ j ih =>
      intro hj
      by_cases hy1 : x ^ 2 ^ (j + 2) = 1
      · exact ih hy1
      · have hy : (x ^ 2 ^ (j + 2)) ^ 2 = 1 := by
          rw [← pow_mul, ← pow_succ]; exact hj
        refine ⟨x ^ 2 ^ (j + 1), ?_⟩
        rw [← hR _ hy hy1, ← pow_add, ← two_mul, ← pow_succ']
  obtain _ | _ | j := s
  · exact absurd (by simpa using hx : x = 1) (fun h => hx2 (by rw [h, one_pow]))
  · exact absurd (by simpa using hx) hx2
  · exact key j hx

/-- CRT: if `-1` is a square modulo every prime power dividing `m ≠ 0`, it is a square
modulo `m`. -/
theorem isSquare_neg_one_of_forall_primePow {m : ℕ} (hm : m ≠ 0)
    (H : ∀ p n : ℕ, p.Prime → 0 < n → p ^ n ∣ m → IsSquare (-1 : ZMod (p ^ n))) :
    IsSquare (-1 : ZMod m) := by
  suffices key : ∀ k : ℕ, k ∣ m → IsSquare (-1 : ZMod k) from key m dvd_rfl
  intro k
  induction k using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => exact fun hdvd => H p n hp hn hdvd
  | zero => intro h0; exact absurd (Nat.eq_zero_of_zero_dvd h0) hm
  | one => intro _; exact ⟨0, Subsingleton.elim _ _⟩
  | coprime a c _ _ hcop iha ihc =>
    intro hdvd
    obtain ⟨x, hx⟩ := iha (dvd_of_mul_right_dvd hdvd)
    obtain ⟨y, hy⟩ := ihc (dvd_of_mul_left_dvd hdvd)
    let e := ZMod.chineseRemainder hcop
    refine ⟨e.symm (x, y), ?_⟩
    rw [← map_mul, Prod.mk_mul_mk, ← hx, ← hy]
    apply e.injective
    ext <;> simp

/-- For `2 < m`, `1 ≠ -1` in `ZMod m`. -/
theorem one_ne_neg_one_zmod {m : ℕ} (hm : 2 < m) : (1 : ZMod m) ≠ -1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod m) = 0 := by
    push_cast
    linear_combination h
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 m).mp h2)
  omega

/-- A residue `z ∈ ZMod m` other than `0, ±1` satisfying the Miller–Rabin
condition for the decomposition `m - 1 = 2^s d` gives a strong liar
`a = z.val` with `2 ≤ a ≤ m - 2`. -/
theorem exists_liar_of_zmod {m s d : ℕ} (hm : 2 < m) (hmd : m - 1 = 2 ^ s * d) (hd : Odd d)
    (z : ZMod m) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hzn : z ≠ -1)
    (hz : z ^ d = 1 ∨ ∃ r < s, z ^ (2 ^ r * d) = -1) :
    ∃ a, 2 ≤ a ∧ a ≤ m - 2 ∧ IsStrongProbablePrime m a := by
  haveI : NeZero m := ⟨by omega⟩
  have hcast : ((z.val : ℕ) : ZMod m) = z := ZMod.natCast_zmod_val z
  have hm1 : ((m - 1 : ℕ) : ZMod m) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hv0 : z.val ≠ 0 := fun h => hz0 ((ZMod.val_eq_zero z).mp h)
  have hv1 : z.val ≠ 1 := fun h => hz1 (by rw [← hcast, h, Nat.cast_one])
  have hvn : z.val ≠ m - 1 := fun h => hzn (by rw [← hcast, h, hm1])
  have hvlt : z.val < m := ZMod.val_lt z
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hdlt : d < m := by
    have : d ≤ 2 ^ s * d := Nat.le_mul_of_pos_left d hpos
    omega
  have hslt : s < m := by
    have h1 : s < 2 ^ s := Nat.lt_two_pow_self
    have h2 : 2 ^ s ≤ 2 ^ s * d := Nat.le_mul_of_pos_right _ hd.pos
    omega
  refine ⟨z.val, by omega, by omega, s, hslt, d, hdlt, hmd, hd, ?_⟩
  rcases hz with h1 | ⟨r, hr, hr1⟩
  · left
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, hcast, h1, Nat.cast_one]
  · right
    refine ⟨r, hr, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, hcast, hr1, hm1]

/-! ## The conjecture -/

/-- **Ordowski's conjecture (A322120, Thomas Ordowski, Nov 27 2018).**

Verbatim: "Conjecture: if m is a composite number such that b^(m-1) == 1
(mod (b^2-1)m) for some b, then m is a strong pseudoprime to some base a in the
range 2 <= a <= m-2. Thus, probably every term a(n) is in A181782."

Formal reading: for composite `m` (`1 < m`, not prime) and a base `b ≥ 2` with
`b^(m-1) ≡ 1 (mod (b^2-1) m)`, `m` lies in A181782 (odd composite with a strong
liar `a`, `2 ≤ a ≤ m - 2`).  The guard `2 ≤ b` keeps `(b^2-1) m` nonzero; for
`b = 1` the claim is false. -/
theorem a322120_conjecture {m b : ℕ} (hm : 1 < m) (hmc : ¬ m.Prime) (hb : 2 ≤ b)
    (h : b ^ (m - 1) ≡ 1 [MOD (b ^ 2 - 1) * m]) : InA181782 m := by
  have hodd : Odd m := odd_of_modEq hm hb h
  have hm2 : 2 < m := by
    by_contra hle
    have hm2' : m = 2 := by omega
    exact hmc (hm2' ▸ Nat.prime_two)
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨hm⟩
  refine ⟨hodd, hm, hmc, ?_⟩
  obtain ⟨s, d, hd, hmd⟩ := Nat.exists_eq_two_pow_mul_odd (n := m - 1) (by omega)
  have hkey : ∀ p : ℕ, p.Prime → p ∣ m → ((b : ZMod p)) ^ 2 ≠ 1 :=
    fun p hp hpm => sq_ne_one_of_prime_dvd hm hodd hb h hp hpm
  have h1ne : (1 : ZMod m) ≠ -1 := one_ne_neg_one_zmod hm2
  set B : ZMod m := (b : ZMod m) with hBdef
  have hB : B ^ (m - 1) = 1 := by
    have hmod : b ^ (m - 1) ≡ 1 [MOD m] := Nat.ModEq.of_mul_left (b ^ 2 - 1) h
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one] at hmod
    exact hmod
  by_cases hA : B ^ 2 ^ s = 1
  · -- Case B: `-1` is a square mod `m`, and `s ≥ 2`.
    have hsq : IsSquare (-1 : ZMod m) := by
      refine isSquare_neg_one_of_forall_primePow (by omega) fun p n hp hn hpn => ?_
      have hpm : p ∣ m := (dvd_pow_self p hn.ne').trans hpn
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpm)
      refine isSquare_neg_one_of_pow_two_pow_eq_one
        (eq_neg_one_of_sq_eq_one hp hp2) (x := (b : ZMod (p ^ n))) (s := s) ?_ ?_
      · have hmap := congrArg (ZMod.castHom hpn (ZMod (p ^ n))) hA
        rw [map_pow, map_one, hBdef, map_natCast] at hmap
        exact hmap
      · intro hx
        have hmap := congrArg (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) hx
        rw [map_pow, map_one, map_natCast] at hmap
        exact hkey p hp hpm hmap
    obtain ⟨z, hz⟩ := hsq
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (n := m) (by omega)
    have hB2 : B ^ 2 ≠ 1 := by
      intro hx
      have hmap := congrArg (ZMod.castHom hpm (ZMod p)) hx
      rw [map_pow, map_one, hBdef, map_natCast] at hmap
      exact hkey p hp hpm hmap
    obtain _ | _ | s := s
    · have hB1 : B = 1 := by simpa using hA
      exact (hB2 (by rw [hB1, one_pow])).elim
    · exact absurd (by simpa using hA) hB2
    · refine exists_liar_of_zmod hm2 hmd hd z ?_ ?_ ?_ (Or.inr ⟨1, by omega, ?_⟩)
      · rintro rfl
        exact one_ne_zero (by linear_combination -hz)
      · rintro rfl
        exact h1ne (by linear_combination -hz)
      · rintro rfl
        exact h1ne (by linear_combination -hz)
      · rw [pow_mul, pow_one, sq, ← hz, Odd.neg_one_pow hd]
  · -- Case A: `B^(2^s)` is a liar with `(B^(2^s))^d = 1`.
    have hzd : (B ^ 2 ^ s) ^ d = 1 := by rw [← pow_mul, ← hmd, hB]
    refine exists_liar_of_zmod hm2 hmd hd (B ^ 2 ^ s) ?_ hA ?_ (Or.inl hzd)
    · intro h0
      rw [h0, zero_pow hd.pos.ne'] at hzd
      exact zero_ne_one hzd
    · intro hn
      rw [hn, Odd.neg_one_pow hd] at hzd
      exact h1ne hzd.symm

/-- Corollary in the entry: every term of A322120 lies in A181782.  For `n ≥ 2`,
if `k` is the least composite with `n^(k-1) ≡ 1 (mod (n^2-1) k)`, then `k` is in
A181782. -/
theorem a322120_term_mem_A181782 {n k : ℕ} (hn : 2 ≤ n)
    (hk : IsLeast {j | A322120Prop n j} k) : InA181782 k :=
  a322120_conjecture hk.1.1 hk.1.2.1 hn hk.1.2.2

set_option exponentiation.threshold 400 in
/-- Non-vacuity: the hypotheses of `a322120_conjecture` hold jointly at
`m = 341`, `b = 2` (the term `a(2)`). -/
example : 1 < 341 ∧ ¬ (341).Prime ∧ 2 ≤ 2 ∧ 2 ^ (341 - 1) ≡ 1 [MOD (2 ^ 2 - 1) * 341] :=
  ⟨by norm_num, by norm_num, le_rfl, by decide⟩

end Candidates.A322120CompositeModStrong
