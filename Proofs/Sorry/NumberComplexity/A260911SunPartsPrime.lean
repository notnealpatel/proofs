/-
# A260911 — Sun: Pythagorean triples of residues / nonresidues modulo a prime

## OEIS source (retrieved with `oeis show A260911` and the live `%A` line, 2026-10-21)

```
NAME:     Least positive integer k < prime(n) such that there are 0 < i < j < k
          for which i^2 + j^2 = k^2 and i,j,k are all quadratic residues modulo
          prime(n), or 0 if no such k exists.
TERMS:    0,0,0,0,5,0,0,0,0,25,0,34,0,41,25,25,5,5,26,5,37,0,41,0,0,65,17,34,
          5,61,17,5,17,25,25,29,37,26,25,41,5,5,5,25,25,53,34,17,34,5,109,5,5
COMMENT:  Conjecture: (i) a(n) > 0 for all n > 25. In other words, for any prime
          p > 100, we have a^2 + b^2 = c^2 for some a,b,c in the set
          R(p) = {0<r<p: r is a quadratic residue mod p}.
          (ii) For any prime p > 50, we have a^2 + b^2 = c^2 for some a,b,c in
          the set N(p) = {0<n<p: n is a quadratic nonresidue mod p}.
          (iii) For any prime p > 32, we have a^2 + b^2 = c^2 for some a,b in
          the set R(p) and c in the set N(p).
          (iv) For any prime p > 72, we have a^2 + b^2 = c^2 for some a,b in the
          set N(p) and c in the set R(p).
          I have verified the conjecture for primes p < 1.5*10^7.
AUTHOR:   Zhi-Wei Sun, Aug 03 2015
```

This module treats parts (i) and (ii).  Parts (iii) and (iv) are not stated
here.

## Status

Triage: open for all `p` past the stated thresholds.  Xi and Zheng (Acta
Math. Sinica Chinese Ser. 67 (2024) 220-226) proved the sign-pattern version
for all sufficiently large `p`, using a higher-dimensional Burgess bound
(as reported in Wu-Ni, arXiv:2608.04391).  The triage found no proof for
every `p > 100` (resp. `p > 50`).  The triage's search was limited, so
this is no claim of novelty.

## Proof used here (elementary, finite certificate)

Let `S = {2, 3, 5, ..., 43}` (14 primes).  For `p > 43` the residue status
of an `S`-smooth number is determined by the 14 Legendre symbols
`(q / p)`, `q ∈ S`, through multiplicativity.

* (i), `p > 1690`.  A list of 19 `S`-smooth Pythagorean triples with
  hypotenuse `≤ 1690` contains, for every one of the `2^14` sign patterns,
  a triple whose three entries are all residues (`coverI_all`).  The
  `2^14` patterns are certified by a prefix decision trie with 275 leaves
  (`trieI_check`, a kernel `decide`).
* (ii), `p > 1850`.  A list of 30 `S`-smooth triples with hypotenuse
  `≤ 1850` handles every sign pattern except "all of `S` are residues"
  (`coverII_all`, certified by a 417-leaf trie, `trieII_check`).  In that pattern, let `q` be the least nonresidue.  Every
  `0 < n ≤ 46` is `S`-smooth, so `q ≥ 47`.  For `m = ⌊p/q⌋ + 1` the number
  `mq - p` lies in `(0, q)` and is a residue, so `m` is a nonresidue, so
  `m ≥ q`.  Hence `p ≥ q(q - 1) > 5q`, and `(3q, 4q, 5q)` works.
* Small primes `101 ≤ p ≤ 1690` (resp. `51 ≤ p ≤ 1850`) are handled by a
  witness table checked in the kernel with Euler's criterion
  `a^((p-1)/2) ≡ ±1 (mod p)` (`witI_check`, `witII_check`).  Composite
  numbers in these ranges are skipped through a factor `≤ 43`.

All finite checks use `decide +kernel` (no `native_decide`).  The module
elaborates in about 15 seconds.

## Result

`sun_A260911_i` and `sun_A260911_ii` prove parts (i) and (ii) for every
prime past the stated thresholds, with no `sorry`; `a260911_pos` restates
(i) in the entry's form `a(n) > 0` for `n > 25`.
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Parity
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

namespace Candidates.A260911SunPartsPrime

/-! ## Definition layer -/

/-- `r ∈ R(p)`: `0 < r < p` and `r` is a quadratic residue modulo `p`. -/
def InR (p r : ℕ) : Prop := 0 < r ∧ r < p ∧ IsSquare (r : ZMod p)

/-- `r ∈ N(p)`: `0 < r < p` and `r` is a quadratic nonresidue modulo `p`. -/
def InN (p r : ℕ) : Prop := 0 < r ∧ r < p ∧ ¬IsSquare (r : ZMod p)

/-- `k` is admissible for the prime `p` in the sense of the entry's name:
`k < p` and there are `0 < i < j < k` with `i^2 + j^2 = k^2` and `i, j, k`
all quadratic residues modulo `p` (they are nonzero residues since they lie
in `(0, p)`). -/
def Admissible (p k : ℕ) : Prop :=
  k < p ∧ ∃ i j : ℕ, i < j ∧ j < k ∧ i ^ 2 + j ^ 2 = k ^ 2 ∧ InR p i ∧ InR p j ∧ InR p k

open Classical in
/-- `A260911(n)`: the least admissible `k` for `p = prime(n)`, or `0` if
there is none.  Here `prime(n) = Nat.nth Nat.Prime (n - 1)` (1-indexed, so
`prime(1) = 2`). -/
noncomputable def a260911 (n : ℕ) : ℕ :=
  if h : ∃ k, Admissible (Nat.nth Nat.Prime (n - 1)) k then Nat.find h else 0

/-- The only Pythagorean triples with hypotenuse below `13` are `(3,4,5)` and
`(6,8,10)`. -/
theorem pythagorean_lt_thirteen (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < 13)
    (h : i ^ 2 + j ^ 2 = k ^ 2) (hi : 0 < i) :
    (i = 3 ∧ j = 4 ∧ k = 5) ∨ (i = 6 ∧ j = 8 ∧ k = 10) := by
  interval_cases k <;> interval_cases j <;> interval_cases i <;> omega

/-- No `k` is admissible for a prime `p ≤ 13` other than `11`: below `13`
only `(3,4,5)` and `(6,8,10)` are Pythagorean, and `3`, `5`, `6` are
nonresidues where needed. -/
theorem not_admissible_of_small (p : ℕ) (hp : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13)
    (k : ℕ) : ¬Admissible p k := by
  rintro ⟨hkp, i, j, hij, hjk, heq, hRi, hRj, hRk⟩
  have hk13 : k < 13 := by omega
  rcases pythagorean_lt_thirteen i j k hij hjk hk13 heq hRi.1 with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact absurd hRk.2.1 (by norm_num)
    · exact absurd hRk.2.1 (by norm_num)
    · exact absurd hRk.2.1 (by norm_num)
    · exact absurd hRi.2.2 (by decide)
    · exact absurd hRk.2.2 (by decide)
  · rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact absurd hRk.2.1 (by norm_num)
    · exact absurd hRk.2.1 (by norm_num)
    · exact absurd hRk.2.1 (by norm_num)
    · exact absurd hRk.2.1 (by norm_num)
    · exact absurd hRi.2.2 (by decide)

open Classical in
/-- Ground truth: `a(1) = a(2) = a(3) = a(4) = 0`, `a(5) = 5`, `a(6) = 0`,
matching the first six listed terms `0, 0, 0, 0, 5, 0`. -/
theorem a260911_first_terms :
    a260911 1 = 0 ∧ a260911 2 = 0 ∧ a260911 3 = 0 ∧ a260911 4 = 0 ∧
      a260911 5 = 5 ∧ a260911 6 = 0 := by
  have hc13 : Nat.count Nat.Prime 13 = 5 := by decide
  have h13 : Nat.nth Nat.Prime 5 = 13 :=
    hc13 ▸ Nat.nth_count (p := Nat.Prime) (by norm_num : Nat.Prime 13)
  have hzero : ∀ n p, Nat.nth Nat.Prime (n - 1) = p →
      (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13) → a260911 n = 0 := by
    intro n p hnp hp
    rw [a260911, dif_neg]
    rintro ⟨k, hk⟩
    exact not_admissible_of_small p hp k (hnp ▸ hk)
  refine ⟨hzero 1 2 Nat.nth_prime_zero_eq_two (by norm_num),
    hzero 2 3 Nat.nth_prime_one_eq_three (by norm_num),
    hzero 3 5 Nat.nth_prime_two_eq_five (by norm_num),
    hzero 4 7 Nat.nth_prime_three_eq_seven (by norm_num), ?_,
    hzero 6 13 h13 (by norm_num)⟩
  have hadm : Admissible 11 5 := by
    refine ⟨by norm_num, 3, 4, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · exact ⟨by norm_num, by norm_num, by decide⟩
    · exact ⟨by norm_num, by norm_num, by decide⟩
    · exact ⟨by norm_num, by norm_num, by decide⟩
  have hex : ∃ k, Admissible (Nat.nth Nat.Prime (5 - 1)) k :=
    ⟨5, by simpa [Nat.nth_prime_four_eq_eleven] using hadm⟩
  rw [a260911, dif_pos hex, Nat.find_eq_iff]
  refine ⟨by simpa [Nat.nth_prime_four_eq_eleven] using hadm, ?_⟩
  rintro k hk ⟨-, i, j, hij, hjk, heq, hRi, -, -⟩
  have h5 : k < 13 := by omega
  rcases pythagorean_lt_thirteen i j k hij hjk h5 heq hRi.1 with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
    omega

/-! ## Residues through Euler's criterion and Legendre symbols -/

/-- Boolean Euler test: `r^(p/2) mod p = 1`. -/
def isQRb (p r : ℕ) : Bool := r ^ (p / 2) % p == 1

/-- Euler's criterion in Boolean form: for a prime `p` and `r` nonzero mod
`p`, `r` is a square mod `p` iff `r^(p/2) mod p = 1`. -/
theorem isSquare_iff_isQRb (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : (r : ZMod p) ≠ 0) :
    IsSquare (r : ZMod p) ↔ isQRb p r = true := by
  rw [ZMod.euler_criterion p hr, isQRb, beq_iff_eq]
  have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', h1]

/-- A number strictly between `0` and `p` is nonzero in `ZMod p`. -/
theorem natCast_ne_zero_of_pos_of_lt (p r : ℕ) (h0 : 0 < r) (hr : r < p) :
    (r : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd h0 h) (not_le.mpr hr)

/-- The sign `±1` attached to a residue bit. -/
def sgn : Bool → ℤ
  | true => 1
  | false => -1

/-- `prodRes β ps` is `true` iff the product of the signs `β q` over `q ∈ ps`
is `+1` (an even number of `false` bits). -/
def prodRes (β : ℕ → Bool) : List ℕ → Bool
  | [] => true
  | q :: qs => (β q == prodRes β qs)

/-- Signs multiply like `xnor`. -/
theorem sgn_mul_sgn (x y : Bool) : sgn x * sgn y = sgn (x == y) := by
  cases x <;> cases y <;> rfl

/-- The residue bit of `q` modulo `p` (classically decided). -/
noncomputable def resBit (p q : ℕ) : Bool := by
  classical exact decide (IsSquare (q : ZMod p))

/-- The residue bit is `true` exactly for squares. -/
theorem resBit_eq_true_iff (p q : ℕ) : resBit p q = true ↔ IsSquare (q : ZMod p) := by
  simp [resBit]

/-- For `q` nonzero mod `p`, the Legendre symbol `(q / p)` is the sign of the
residue bit. -/
theorem legendreSym_eq_sgn (p : ℕ) [Fact p.Prime] (q : ℕ) (hq : (q : ZMod p) ≠ 0) :
    legendreSym p q = sgn (resBit p q) := by
  have hq' : ((q : ℤ) : ZMod p) ≠ 0 := by exact_mod_cast hq
  by_cases h : IsSquare (q : ZMod p)
  · have h' : IsSquare ((q : ℤ) : ZMod p) := by exact_mod_cast h
    simp [resBit, h, sgn, (legendreSym.eq_one_iff p hq').mpr h']
  · have h' : ¬IsSquare ((q : ℤ) : ZMod p) := by exact_mod_cast h
    simp [resBit, h, sgn, legendreSym.eq_neg_one_iff p |>.mpr h']

/-- Multiplicativity of the Legendre symbol over a list of factors. -/
theorem legendreSym_prod (p : ℕ) [Fact p.Prime] (ps : List ℕ)
    (hps : ∀ q ∈ ps, (q : ZMod p) ≠ 0) :
    legendreSym p (ps.prod : ℕ) = sgn (prodRes (resBit p) ps) := by
  induction ps with
  | nil => simp [prodRes, sgn]
  | cons q qs ih =>
    rw [List.prod_cons, Nat.cast_mul, legendreSym.mul,
      legendreSym_eq_sgn p q (hps q List.mem_cons_self),
      ih (fun r hr => hps r (List.mem_cons_of_mem q hr)), sgn_mul_sgn, prodRes]

/-- If `n = (∏ ps) · m²` is nonzero mod `p`, then `n` is a square mod `p` iff
the residue bits of `ps` have product `+1`. -/
theorem isSquare_iff_prodRes (p : ℕ) [Fact p.Prime] (n m : ℕ) (ps : List ℕ)
    (hn : n = ps.prod * m ^ 2) (hn0 : (n : ZMod p) ≠ 0) :
    IsSquare (n : ZMod p) ↔ prodRes (resBit p) ps = true := by
  have hps0 : (ps.prod : ZMod p) ≠ 0 := by
    intro h; apply hn0; rw [hn, Nat.cast_mul, h, zero_mul]
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro h; apply hn0; rw [hn, Nat.cast_mul, Nat.cast_pow, h]; ring
  have hps : ∀ q ∈ ps, (q : ZMod p) ≠ 0 := by
    intro q hq h
    apply hps0
    rw [Nat.cast_list_prod]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨q, hq, h⟩)
  have hleg : legendreSym p (n : ℤ) = sgn (prodRes (resBit p) ps) := by
    have hm0' : ((m : ℤ) : ZMod p) ≠ 0 := by exact_mod_cast hm0
    rw [hn, Nat.cast_mul, Nat.cast_pow, legendreSym.mul, legendreSym.sq_one' p hm0',
      mul_one, legendreSym_prod p ps hps]
  have hn0' : ((n : ℤ) : ZMod p) ≠ 0 := by exact_mod_cast hn0
  rw [← Int.cast_natCast, ← legendreSym.eq_one_iff p hn0', hleg]
  cases prodRes (resBit p) ps <;> simp [sgn]

/-- In a field, if `x ≠ 0` and `x`, `x * y` are squares, then `y` is a square. -/
theorem isSquare_of_isSquare_mul {F : Type*} [Field F] {x y : F} (hx : IsSquare x)
    (hx0 : x ≠ 0) (hxy : IsSquare (x * y)) : IsSquare y := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hxy
  refine ⟨t * s⁻¹, ?_⟩
  have hy : y = (x * y) * x⁻¹ := by field_simp
  rw [hy, ht, hs, mul_inv]
  ring

/-! ## The sign-pattern covers (kernel `decide`) -/

/-- The primes `S = {2, 3, 5, ..., 43}`. -/
def primesS : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

/-- The sublist of `qs` selected by the binary digits of `mask` (least
significant digit first). -/
def maskPrimes : List ℕ → ℕ → List ℕ
  | [], _ => []
  | q :: qs, mask => cond (mask % 2 == 1) (q :: maskPrimes qs (mask / 2)) (maskPrimes qs (mask / 2))

/-- `prodRes` evaluated on a bit list `bs` (bit `i` is the residue bit of the
`i`-th prime) and the primes selected by `mask`. -/
def maskRes : List Bool → ℕ → Bool
  | [], _ => true
  | b :: bs, mask => cond (mask % 2 == 1) (b == maskRes bs (mask / 2)) (maskRes bs (mask / 2))

/-- `maskRes` on the bits of `β` computes `prodRes β` of the selected primes. -/
theorem maskRes_map (β : ℕ → Bool) (qs : List ℕ) (mask : ℕ) :
    maskRes (qs.map β) mask = prodRes β (maskPrimes qs mask) := by
  induction qs generalizing mask with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons, maskRes, maskPrimes]
    cases mask % 2 == 1
    · exact ih (mask / 2)
    · rw [cond_true, cond_true, prodRes, ih]

/-- An `S`-smooth number `n` recorded as `n = (∏ ps) · m²`, where `ps` (the
primes of `S` with odd exponent in `n`) is encoded by the bitmask `mask`. -/
structure Entry where
  /-- The number. -/
  n : ℕ
  /-- The bitmask over `primesS` of the primes with odd exponent in `n`. -/
  mask : ℕ
  /-- The square root of the square part. -/
  m : ℕ

/-- 19 `S`-smooth Pythagorean triples covering all sign patterns for part (i). -/
def triplesI : List (Entry × Entry × Entry) :=
  [(⟨3, 2, 1⟩, ⟨4, 0, 2⟩, ⟨5, 4, 1⟩),
   (⟨7, 8, 1⟩, ⟨24, 3, 2⟩, ⟨25, 0, 5⟩),
   (⟨16, 0, 4⟩, ⟨30, 7, 1⟩, ⟨34, 65, 1⟩),
   (⟨9, 0, 3⟩, ⟨40, 5, 2⟩, ⟨41, 4096, 1⟩),
   (⟨36, 0, 6⟩, ⟨77, 24, 1⟩, ⟨85, 68, 1⟩),
   (⟨36, 0, 6⟩, ⟨105, 14, 1⟩, ⟨111, 2050, 1⟩),
   (⟨17, 64, 1⟩, ⟨144, 0, 12⟩, ⟨145, 516, 1⟩),
   (⟨169, 0, 13⟩, ⟨1092, 42, 2⟩, ⟨1105, 100, 1⟩),
   (⟨15, 6, 1⟩, ⟨36, 0, 6⟩, ⟨39, 34, 1⟩),
   (⟨36, 0, 6⟩, ⟨323, 192, 1⟩, ⟨325, 32, 5⟩),
   (⟨246, 4099, 1⟩, ⟨1672, 145, 2⟩, ⟨1690, 5, 13⟩),
   (⟨342, 129, 3⟩, ⟨1056, 19, 4⟩, ⟨1110, 2055, 1⟩),
   (⟨87, 514, 1⟩, ⟨416, 33, 4⟩, ⟨425, 64, 5⟩),
   (⟨370, 2053, 1⟩, ⟨1344, 10, 8⟩, ⟨1394, 4161, 1⟩),
   (⟨63, 8, 3⟩, ⟨660, 22, 2⟩, ⟨663, 98, 1⟩),
   (⟨100, 0, 10⟩, ⟨621, 258, 3⟩, ⟨629, 2112, 1⟩),
   (⟨1020, 70, 2⟩, ⟨1265, 276, 1⟩, ⟨1625, 36, 5⟩),
   (⟨144, 0, 12⟩, ⟨858, 51, 1⟩, ⟨870, 519, 1⟩),
   (⟨21, 10, 1⟩, ⟨220, 20, 2⟩, ⟨221, 96, 1⟩)]
/-- 30 `S`-smooth Pythagorean triples covering the non-all-residue sign patterns for part (ii). -/
def triplesII : List (Entry × Entry × Entry) :=
  [(⟨6, 3, 1⟩, ⟨8, 1, 2⟩, ⟨10, 5, 1⟩),
   (⟨5, 4, 1⟩, ⟨12, 2, 2⟩, ⟨13, 32, 1⟩),
   (⟨8, 1, 2⟩, ⟨15, 6, 1⟩, ⟨17, 64, 1⟩),
   (⟨39, 34, 1⟩, ⟨252, 8, 6⟩, ⟨255, 70, 1⟩),
   (⟨182, 41, 1⟩, ⟨624, 34, 4⟩, ⟨650, 33, 5⟩),
   (⟨54, 3, 3⟩, ⟨240, 6, 4⟩, ⟨246, 4099, 1⟩),
   (⟨180, 4, 6⟩, ⟨1615, 196, 1⟩, ⟨1625, 36, 5⟩),
   (⟨168, 11, 2⟩, ⟨374, 81, 1⟩, ⟨410, 4101, 1⟩),
   (⟨540, 6, 6⟩, ⟨1155, 30, 1⟩, ⟨1275, 66, 5⟩),
   (⟨357, 74, 1⟩, ⟨476, 72, 2⟩, ⟨595, 76, 1⟩),
   (⟨105, 14, 1⟩, ⟨1100, 16, 10⟩, ⟨1105, 100, 1⟩),
   (⟨660, 22, 2⟩, ⟨693, 24, 3⟩, ⟨957, 530, 1⟩),
   (⟨123, 4098, 1⟩, ⟨836, 144, 2⟩, ⟨845, 4, 13⟩),
   (⟨60, 6, 2⟩, ⟨175, 8, 5⟩, ⟨185, 2052, 1⟩),
   (⟨152, 129, 2⟩, ⟨285, 134, 1⟩, ⟨323, 192, 1⟩),
   (⟨308, 24, 2⟩, ⟨819, 40, 3⟩, ⟨875, 12, 5⟩),
   (⟨65, 36, 1⟩, ⟨420, 14, 2⟩, ⟨425, 64, 5⟩),
   (⟨203, 520, 1⟩, ⟨696, 515, 2⟩, ⟨725, 512, 5⟩),
   (⟨24, 3, 2⟩, ⟨143, 48, 1⟩, ⟨145, 516, 1⟩),
   (⟨280, 13, 2⟩, ⟨294, 3, 7⟩, ⟨406, 521, 1⟩),
   (⟨1040, 36, 4⟩, ⟨1530, 69, 3⟩, ⟨1850, 2049, 5⟩),
   (⟨21, 10, 1⟩, ⟨220, 20, 2⟩, ⟨221, 96, 1⟩),
   (⟨161, 264, 1⟩, ⟨552, 259, 2⟩, ⟨575, 256, 5⟩),
   (⟨924, 26, 2⟩, ⟨1305, 516, 3⟩, ⟨1599, 4130, 1⟩),
   (⟨217, 1032, 1⟩, ⟨744, 1027, 2⟩, ⟨775, 1024, 5⟩),
   (⟨285, 134, 1⟩, ⟨880, 20, 4⟩, ⟨925, 2048, 5⟩),
   (⟨301, 8200, 1⟩, ⟨1032, 8195, 2⟩, ⟨1075, 8192, 5⟩),
   (⟨111, 2050, 1⟩, ⟨148, 2048, 2⟩, ⟨185, 2052, 1⟩),
   (⟨35, 12, 1⟩, ⟨120, 7, 2⟩, ⟨125, 4, 5⟩),
   (⟨123, 4098, 1⟩, ⟨164, 4096, 2⟩, ⟨205, 4100, 1⟩)]

/-- Validity of an entry: `n = (∏ ps) · m²`. -/
def entryOK (e : Entry) : Bool := e.n == (maskPrimes primesS e.mask).prod * e.m ^ 2

/-- Validity of a triple: valid entries, `0 < a < b < c ≤ bound`, `a² + b² = c²`. -/
def tripleOK (bound : ℕ) (t : Entry × Entry × Entry) : Bool :=
  entryOK t.1 && entryOK t.2.1 && entryOK t.2.2 && 0 < t.1.n && t.1.n < t.2.1.n &&
    t.2.1.n < t.2.2.n && t.2.2.n ≤ bound && t.1.n ^ 2 + t.2.1.n ^ 2 == t.2.2.n ^ 2

/-- Every triple of `triplesI` is valid with hypotenuse `≤ 1690`. -/
theorem triplesI_ok : triplesI.all (tripleOK 1690) = true := by decide +kernel

/-- Every triple of `triplesII` is valid with hypotenuse `≤ 1850`. -/
theorem triplesII_ok : triplesII.all (tripleOK 1850) = true := by decide +kernel

/-- For a bit list `l` (bit `i` = residue bit of the `i`-th prime of `S`),
some triple of `T` has all three entries with residue bit `want`, or `top`
holds and all bits are `true`. -/
def coverF (T : List (Entry × Entry × Entry)) (want top : Bool) (l : List Bool) : Bool :=
  (T.any fun t => (maskRes l t.1.mask == want) && (maskRes l t.2.1.mask == want) &&
    (maskRes l t.2.2.mask == want)) || (top && l.all id)

/-- `maskRes` vanishes on the empty mask. -/
theorem maskRes_zero (l : List Bool) : maskRes l 0 = true := by
  induction l with
  | nil => rfl
  | cons b bs ih => simpa [maskRes] using ih

/-- `maskRes` only reads the first `k` bits when `mask < 2^k`. -/
theorem maskRes_append (pre rest : List Bool) (mask : ℕ) (h : mask < 2 ^ pre.length) :
    maskRes (pre ++ rest) mask = maskRes pre mask := by
  induction pre generalizing mask with
  | nil =>
    have h0 : mask = 0 := by simpa using h
    rw [h0, List.nil_append, maskRes_zero, maskRes_zero]
  | cons b pre ih =>
    have h2 : mask / 2 < 2 ^ pre.length := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]
      simpa using h
    simp only [List.cons_append, maskRes, ih (mask / 2) h2]

/-- A prefix trie on bit lists; a leaf names a triple index. -/
inductive Trie where
  /-- A leaf certifying the triple with the given index. -/
  | leaf (i : ℕ)
  /-- Branch on the next bit (`false` subtrie first). -/
  | node (f t : Trie)

/-- Check a trie below the prefix `pre`, with leaf test `ok`; the bit lists
have length `14`. -/
def checkT (ok : List Bool → ℕ → Bool) : List Bool → Trie → Bool
  | pre, .leaf i => ok pre i
  | pre, .node f t =>
    decide (pre.length < 14) && checkT ok (pre ++ [false]) f && checkT ok (pre ++ [true]) t

/-- Soundness of `checkT`. -/
theorem checkT_sound (ok : List Bool → ℕ → Bool) (F : List Bool → Bool)
    (hok : ∀ pre i rest, ok pre i = true → (pre ++ rest).length = 14 → F (pre ++ rest) = true)
    (t : Trie) : ∀ pre, checkT ok pre t = true →
      ∀ rest, (pre ++ rest).length = 14 → F (pre ++ rest) = true := by
  induction t with
  | leaf i => exact fun pre h rest hl => hok pre i rest h hl
  | node f t ihf iht =>
    intro pre h rest hl
    simp only [checkT, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlen, hf⟩, ht⟩ := h
    match rest, hl with
    | [], hl' => rw [List.append_nil] at hl'; omega
    | false :: rest', hl' =>
      have e : pre ++ false :: rest' = (pre ++ [false]) ++ rest' := by simp
      rw [e] at hl' ⊢
      exact ihf _ hf rest' hl'
    | true :: rest', hl' =>
      have e : pre ++ true :: rest' = (pre ++ [true]) ++ rest' := by simp
      rw [e] at hl' ⊢
      exact iht _ ht rest' hl'

/-- One entry is decided by the prefix `pre` with residue bit `want`. -/
def entDecided (want : Bool) (pre : List Bool) (mask : ℕ) : Bool :=
  decide (mask < 2 ^ pre.length) && (maskRes pre mask == want)

/-- Leaf test: the triple `T[i]` is decided by `pre` with residue bit `want`;
an out-of-range index is the "all bits `true`" leaf, allowed only when `top`. -/
def okLeaf (T : List (Entry × Entry × Entry)) (want top : Bool) (pre : List Bool) (i : ℕ) :
    Bool :=
  match T[i]? with
  | some t => entDecided want pre t.1.mask && entDecided want pre t.2.1.mask &&
      entDecided want pre t.2.2.mask
  | none => top && decide (pre.length = 14) && pre.all id

/-- Soundness of the leaf test. -/
theorem okLeaf_sound (T : List (Entry × Entry × Entry)) (want top : Bool) (pre : List Bool)
    (i : ℕ) (rest : List Bool) (h : okLeaf T want top pre i = true)
    (hl : (pre ++ rest).length = 14) : coverF T want top (pre ++ rest) = true := by
  unfold okLeaf at h
  rcases hti : T[i]? with _ | t
  · rw [hti] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨htop, hlen⟩, hall⟩ := h
    have hrest : rest = [] := by
      rw [List.length_append] at hl
      exact List.length_eq_zero_iff.mp (by omega)
    subst hrest
    simp [coverF, htop, List.append_nil, hall]
  · rw [hti] at h
    simp only [entDecided, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, e1⟩, ⟨h2, e2⟩⟩, ⟨h3, e3⟩⟩ := h
    have hmem : t ∈ T := List.mem_of_getElem? hti
    simp only [coverF, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inl ⟨t, hmem, ⟨⟨by rw [maskRes_append _ _ _ h1]; exact e1,
      by rw [maskRes_append _ _ _ h2]; exact e2⟩, by rw [maskRes_append _ _ _ h3]; exact e3⟩⟩

/-- Decision trie certifying the cover lemma (i) (275 leaves). -/
def trieI : Trie :=
  .node (.node (.node (.node (.node (.node (.leaf 8) (.node (.leaf 4) (.leaf 18))) (.node (.leaf
  8) (.node (.leaf 7) (.node (.node (.node (.leaf 6) (.node (.node (.leaf 11) (.leaf 15)) (.node
  (.leaf 11) (.leaf 15)))) (.node (.leaf 6) (.node (.node (.leaf 11) (.node (.leaf 13) (.leaf
  3))) (.node (.leaf 11) (.node (.leaf 13) (.leaf 3)))))) (.leaf 9))))) (.leaf 1)) (.node (.node
  (.node (.node (.leaf 2) (.leaf 4)) (.node (.leaf 2) (.leaf 4))) (.node (.node (.leaf 2) (.node
  (.node (.node (.leaf 12) (.leaf 6)) (.node (.leaf 12) (.leaf 6))) (.node (.node (.leaf 12)
  (.leaf 6)) (.node (.leaf 12) (.leaf 6))))) (.node (.leaf 2) (.leaf 7)))) (.leaf 1))) (.node
  (.node (.node (.node (.node (.leaf 2) (.leaf 7)) (.node (.leaf 2) (.node (.node (.node (.leaf
  6) (.leaf 17)) (.node (.leaf 6) (.leaf 17))) (.leaf 9)))) (.node (.node (.leaf 2) (.leaf 7))
  (.node (.leaf 2) (.node (.node (.node (.leaf 6) (.node (.node (.node (.leaf 10) (.leaf 3))
  (.leaf 5)) (.node (.node (.leaf 10) (.leaf 3)) (.leaf 5)))) (.node (.leaf 6) (.node (.node
  (.node (.leaf 10) (.leaf 3)) (.leaf 5)) (.node (.node (.leaf 10) (.leaf 3)) (.leaf 5)))))
  (.leaf 9))))) (.node (.node (.node (.leaf 2) (.node (.node (.node (.leaf 6) (.leaf 12)) (.node
  (.leaf 6) (.leaf 12))) (.node (.node (.leaf 6) (.leaf 12)) (.node (.leaf 6) (.leaf 12)))))
  (.node (.leaf 2) (.leaf 14))) (.node (.node (.leaf 2) (.node (.node (.node (.leaf 6) (.leaf
  12)) (.node (.leaf 6) (.leaf 12))) (.node (.node (.leaf 6) (.leaf 12)) (.node (.leaf 6) (.leaf
  12))))) (.node (.leaf 2) (.node (.node (.node (.leaf 6) (.node (.node (.node (.leaf 10) (.leaf
  3)) (.node (.leaf 10) (.leaf 3))) (.node (.node (.leaf 10) (.leaf 3)) (.node (.leaf 10) (.leaf
  3))))) (.node (.leaf 6) (.node (.node (.node (.leaf 10) (.leaf 3)) (.leaf 15)) (.node (.node
  (.leaf 10) (.leaf 3)) (.leaf 15))))) (.leaf 9)))))) (.leaf 0))) (.node (.node (.node (.node
  (.node (.leaf 8) (.node (.leaf 4) (.leaf 2))) (.node (.leaf 8) (.node (.leaf 7) (.leaf 2))))
  (.node (.node (.leaf 8) (.node (.node (.leaf 9) (.node (.node (.node (.node (.leaf 5) (.leaf
  11)) (.node (.leaf 5) (.leaf 11))) (.leaf 17)) (.node (.node (.node (.leaf 5) (.leaf 11))
  (.node (.leaf 5) (.leaf 11))) (.leaf 17)))) (.leaf 2))) (.node (.leaf 8) (.node (.leaf 4)
  (.leaf 2))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 5) (.node
  (.leaf 10) (.leaf 3))) (.node (.leaf 5) (.node (.leaf 10) (.leaf 3)))) (.node (.node (.leaf 5)
  (.node (.leaf 10) (.leaf 3))) (.node (.leaf 5) (.node (.leaf 10) (.leaf 3))))) (.node (.node
  (.node (.leaf 5) (.node (.leaf 10) (.leaf 3))) (.node (.leaf 5) (.node (.leaf 10) (.leaf 3))))
  (.node (.node (.leaf 5) (.node (.leaf 10) (.leaf 3))) (.node (.leaf 5) (.node (.leaf 10) (.leaf
  3)))))) (.node (.node (.node (.node (.leaf 5) (.node (.leaf 13) (.leaf 3))) (.node (.leaf 5)
  (.node (.leaf 13) (.leaf 3)))) (.node (.node (.leaf 5) (.node (.leaf 13) (.leaf 3))) (.node
  (.leaf 5) (.node (.leaf 13) (.leaf 3))))) (.node (.node (.node (.leaf 5) (.node (.leaf 13)
  (.leaf 3))) (.node (.leaf 5) (.node (.leaf 13) (.leaf 3)))) (.node (.node (.leaf 5) (.node
  (.leaf 13) (.leaf 3))) (.node (.leaf 5) (.node (.leaf 13) (.leaf 3))))))) (.leaf 4)) (.node
  (.node (.leaf 9) (.node (.leaf 16) (.node (.leaf 17) (.node (.node (.leaf 5) (.node (.leaf 13)
  (.leaf 3))) (.node (.leaf 5) (.node (.leaf 13) (.leaf 3))))))) (.leaf 4))) (.node (.node (.leaf
  18) (.node (.node (.node (.leaf 17) (.leaf 6)) (.node (.leaf 17) (.leaf 6))) (.node (.node
  (.leaf 17) (.leaf 6)) (.node (.leaf 17) (.leaf 6))))) (.node (.node (.leaf 9) (.node (.node
  (.node (.node (.leaf 5) (.node (.leaf 10) (.leaf 3))) (.node (.leaf 5) (.node (.leaf 10) (.leaf
  3)))) (.node (.node (.leaf 5) (.node (.leaf 10) (.leaf 3))) (.node (.leaf 5) (.node (.leaf 10)
  (.leaf 3))))) (.leaf 16))) (.leaf 7)))) (.node (.node (.node (.leaf 7) (.leaf 14)) (.node
  (.leaf 14) (.node (.node (.node (.leaf 12) (.leaf 6)) (.node (.leaf 12) (.leaf 6))) (.leaf
  9)))) (.node (.node (.leaf 7) (.leaf 4)) (.node (.node (.leaf 9) (.node (.node (.node (.node
  (.leaf 15) (.node (.leaf 10) (.leaf 3))) (.node (.leaf 15) (.node (.leaf 10) (.leaf 3))))
  (.node (.node (.leaf 15) (.node (.leaf 10) (.leaf 3))) (.node (.leaf 15) (.node (.leaf 10)
  (.leaf 3))))) (.leaf 16))) (.leaf 4)))))) (.node (.node (.node (.node (.node (.leaf 4) (.leaf
  7)) (.node (.leaf 4) (.node (.node (.node (.leaf 6) (.leaf 12)) (.node (.leaf 6) (.leaf 12)))
  (.leaf 9)))) (.node (.node (.node (.node (.leaf 16) (.node (.node (.node (.leaf 15) (.leaf 5))
  (.node (.leaf 15) (.leaf 5))) (.node (.node (.leaf 15) (.leaf 5)) (.node (.leaf 15) (.leaf
  5))))) (.node (.leaf 16) (.node (.node (.node (.leaf 11) (.leaf 5)) (.node (.leaf 11) (.leaf
  5))) (.node (.node (.leaf 11) (.leaf 5)) (.node (.leaf 11) (.leaf 5)))))) (.leaf 7)) (.node
  (.node (.leaf 9) (.node (.node (.leaf 17) (.node (.node (.leaf 11) (.leaf 5)) (.node (.leaf 11)
  (.leaf 5)))) (.node (.leaf 17) (.node (.node (.leaf 11) (.leaf 5)) (.node (.leaf 11) (.leaf
  5)))))) (.node (.node (.node (.leaf 6) (.leaf 12)) (.node (.leaf 6) (.leaf 12))) (.leaf 9)))))
  (.leaf 1)) (.leaf 0)))

/-- Decision trie certifying the cover lemma (ii) (417 leaves). -/
def trieII : Trie :=
  .node (.node (.node (.node (.node (.node (.leaf 1) (.node (.leaf 3) (.leaf 10))) (.node (.leaf
  1) (.node (.leaf 3) (.node (.node (.node (.node (.node (.leaf 25) (.node (.leaf 7) (.leaf 12)))
  (.node (.leaf 25) (.node (.leaf 7) (.leaf 12)))) (.node (.node (.leaf 25) (.node (.leaf 7)
  (.leaf 12))) (.node (.leaf 25) (.node (.leaf 7) (.leaf 12))))) (.node (.node (.node (.leaf 25)
  (.node (.leaf 7) (.leaf 12))) (.node (.leaf 25) (.node (.leaf 7) (.leaf 12)))) (.node (.node
  (.leaf 25) (.node (.leaf 7) (.leaf 12))) (.node (.leaf 25) (.node (.leaf 7) (.leaf 12))))))
  (.leaf 6))))) (.leaf 28)) (.node (.node (.node (.node (.leaf 2) (.leaf 8)) (.node (.leaf 2)
  (.leaf 3))) (.node (.node (.leaf 2) (.node (.node (.node (.node (.node (.leaf 13) (.leaf 20))
  (.node (.leaf 13) (.leaf 20))) (.leaf 11)) (.node (.node (.node (.leaf 13) (.leaf 20)) (.node
  (.leaf 13) (.leaf 20))) (.leaf 11))) (.node (.node (.node (.node (.leaf 13) (.leaf 20)) (.node
  (.leaf 13) (.leaf 20))) (.leaf 11)) (.node (.node (.node (.leaf 13) (.leaf 20)) (.node (.leaf
  13) (.leaf 20))) (.leaf 11))))) (.leaf 15))) (.node (.node (.node (.leaf 2) (.leaf 10)) (.leaf
  4)) (.node (.node (.leaf 2) (.leaf 8)) (.leaf 4))))) (.node (.node (.node (.node (.node (.leaf
  2) (.leaf 3)) (.node (.leaf 2) (.node (.node (.node (.leaf 19) (.leaf 18)) (.node (.leaf 19)
  (.leaf 18))) (.leaf 6)))) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 2) (.node (.node
  (.node (.leaf 11) (.node (.node (.node (.leaf 12) (.leaf 5)) (.leaf 13)) (.node (.node (.leaf
  12) (.leaf 5)) (.leaf 13)))) (.node (.leaf 11) (.node (.node (.node (.leaf 12) (.leaf 5))
  (.leaf 13)) (.node (.node (.leaf 12) (.leaf 5)) (.leaf 13))))) (.leaf 6))))) (.node (.node
  (.leaf 15) (.node (.leaf 2) (.leaf 10))) (.node (.node (.leaf 2) (.node (.node (.node (.node
  (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 7) (.leaf
  5)) (.node (.leaf 7) (.leaf 5)))) (.leaf 18)) (.node (.node (.node (.node (.leaf 7) (.leaf 5))
  (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))))
  (.leaf 18))) (.node (.node (.node (.node (.leaf 25) (.node (.leaf 7) (.leaf 5))) (.node (.leaf
  25) (.node (.leaf 7) (.leaf 5)))) (.leaf 18)) (.node (.node (.node (.leaf 25) (.node (.leaf 7)
  (.leaf 5))) (.node (.leaf 25) (.node (.leaf 7) (.leaf 5)))) (.leaf 18))))) (.node (.leaf 2)
  (.node (.node (.node (.node (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5)))
  (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5)))) (.node (.node (.node (.leaf 7)
  (.leaf 5)) (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7)
  (.leaf 5))))) (.node (.node (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5)))
  (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5)))) (.node (.node (.node (.leaf 7)
  (.leaf 5)) (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7)
  (.leaf 5)))))) (.leaf 6)))))) (.leaf 0))) (.node (.node (.node (.node (.node (.leaf 1) (.node
  (.leaf 3) (.leaf 10))) (.node (.leaf 1) (.node (.leaf 3) (.node (.leaf 14) (.leaf 6))))) (.node
  (.node (.leaf 1) (.node (.node (.leaf 6) (.node (.node (.leaf 11) (.leaf 18)) (.node (.leaf 11)
  (.leaf 18)))) (.node (.leaf 14) (.leaf 6)))) (.node (.leaf 1) (.node (.leaf 21) (.node (.leaf
  14) (.leaf 6)))))) (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 13)
  (.node (.leaf 23) (.leaf 5))) (.node (.leaf 13) (.node (.leaf 23) (.leaf 5)))) (.leaf 19))
  (.node (.node (.node (.leaf 13) (.node (.leaf 23) (.leaf 5))) (.node (.leaf 13) (.node (.leaf
  23) (.leaf 5)))) (.leaf 19))) (.node (.node (.node (.node (.leaf 13) (.node (.leaf 23) (.leaf
  5))) (.node (.leaf 13) (.node (.leaf 23) (.leaf 5)))) (.leaf 19)) (.node (.node (.node (.leaf
  13) (.node (.leaf 23) (.leaf 5))) (.node (.leaf 13) (.node (.leaf 23) (.leaf 5)))) (.leaf
  19)))) (.leaf 8)) (.node (.node (.node (.node (.leaf 18) (.leaf 19)) (.node (.leaf 18) (.leaf
  19))) (.node (.node (.leaf 18) (.leaf 19)) (.node (.leaf 18) (.leaf 19)))) (.leaf 3))) (.node
  (.node (.node (.node (.node (.leaf 18) (.leaf 11)) (.node (.leaf 18) (.leaf 11))) (.node (.node
  (.leaf 18) (.leaf 11)) (.node (.leaf 18) (.leaf 11)))) (.node (.node (.node (.leaf 18) (.leaf
  11)) (.node (.leaf 18) (.leaf 11))) (.node (.node (.leaf 18) (.leaf 11)) (.node (.leaf 18)
  (.leaf 11))))) (.leaf 15))) (.node (.node (.node (.leaf 16) (.leaf 10)) (.node (.leaf 10)
  (.node (.node (.node (.leaf 18) (.node (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7)
  (.leaf 5))) (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))))) (.node (.leaf 18)
  (.node (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 7)
  (.leaf 5)) (.node (.leaf 7) (.leaf 5)))))) (.node (.node (.leaf 18) (.node (.node (.leaf 25)
  (.node (.leaf 7) (.leaf 5))) (.node (.leaf 25) (.node (.leaf 7) (.leaf 5))))) (.node (.leaf 18)
  (.node (.node (.leaf 25) (.node (.leaf 7) (.leaf 5))) (.node (.leaf 25) (.node (.leaf 7) (.leaf
  5))))))))) (.node (.node (.leaf 16) (.leaf 8)) (.node (.node (.node (.node (.node (.node (.node
  (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 7) (.leaf 5)) (.node
  (.leaf 7) (.leaf 5)))) (.node (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5)))
  (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))))) (.node (.node (.node (.node
  (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 7) (.leaf 5)) (.node
  (.leaf 7) (.leaf 5)))) (.node (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5)))
  (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5)))))) (.node (.node (.node (.node
  (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 7) (.leaf 5))
  (.node (.leaf 7) (.leaf 5)))) (.node (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf
  5))) (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))))) (.node (.node (.node
  (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))) (.node (.node (.leaf 7) (.leaf 5))
  (.node (.leaf 7) (.leaf 5)))) (.node (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf
  5))) (.node (.node (.leaf 7) (.leaf 5)) (.node (.leaf 7) (.leaf 5))))))) (.leaf 8)))))) (.node
  (.node (.node (.node (.node (.leaf 8) (.leaf 3)) (.node (.leaf 8) (.node (.node (.node (.node
  (.node (.leaf 20) (.leaf 13)) (.node (.leaf 20) (.leaf 13))) (.node (.node (.leaf 20) (.leaf
  13)) (.node (.leaf 20) (.leaf 13)))) (.node (.node (.node (.leaf 20) (.leaf 13)) (.node (.leaf
  20) (.leaf 13))) (.node (.node (.leaf 20) (.leaf 13)) (.node (.leaf 20) (.leaf 13))))) (.leaf
  6)))) (.node (.node (.node (.node (.node (.leaf 11) (.node (.node (.node (.leaf 12) (.leaf 7))
  (.leaf 13)) (.node (.node (.leaf 12) (.leaf 7)) (.leaf 13)))) (.node (.leaf 11) (.node (.node
  (.node (.leaf 12) (.leaf 7)) (.leaf 13)) (.node (.node (.leaf 12) (.leaf 7)) (.leaf 13)))))
  (.node (.node (.leaf 11) (.node (.node (.leaf 25) (.leaf 13)) (.node (.leaf 25) (.leaf 13))))
  (.node (.leaf 11) (.node (.node (.leaf 25) (.leaf 13)) (.node (.leaf 25) (.leaf 13)))))) (.leaf
  3)) (.node (.leaf 21) (.node (.node (.node (.leaf 11) (.node (.node (.leaf 20) (.leaf 13))
  (.node (.leaf 20) (.leaf 13)))) (.node (.leaf 11) (.node (.node (.leaf 20) (.leaf 13)) (.node
  (.leaf 20) (.leaf 13))))) (.leaf 6))))) (.leaf 28)) (.node (.node (.node (.node (.leaf 3)
  (.leaf 9)) (.node (.leaf 10) (.leaf 9))) (.node (.node (.leaf 3) (.leaf 9)) (.leaf 15))) (.node
  (.node (.leaf 4) (.node (.leaf 9) (.node (.leaf 14) (.node (.leaf 22) (.node (.leaf 17) (.leaf
  11)))))) (.node (.leaf 4) (.node (.leaf 9) (.node (.leaf 14) (.node (.leaf 22) (.node (.leaf
  17) (.node (.leaf 24) (.node (.leaf 27) (.node (.leaf 29) (.node (.leaf 26) (.leaf
  30))))))))))))))

/-- Kernel check of the trie for part (i). -/
theorem trieI_check : checkT (okLeaf triplesI true false) [] trieI = true := by decide +kernel

/-- Kernel check of the trie for part (ii). -/
theorem trieII_check : checkT (okLeaf triplesII false true) [] trieII = true := by
  decide +kernel

/-- **Cover lemma (i)**: for each of the `2^14` sign patterns on `2, ..., 43`,
some triple of `triplesI` consists of residues. -/
theorem coverI_all (l : List Bool) (hl : l.length = 14) : coverF triplesI true false l = true :=
  checkT_sound _ _ (okLeaf_sound triplesI true false) trieI [] trieI_check l hl

/-- **Cover lemma (ii)**: for each sign pattern on `2, ..., 43` other than
all-residue, some triple of `triplesII` consists of nonresidues. -/
theorem coverII_all (l : List Bool) (hl : l.length = 14) : coverF triplesII false true l = true :=
  checkT_sound _ _ (okLeaf_sound triplesII false true) trieII [] trieII_check l hl

/-! ## Small primes: witness tables (kernel `decide`) -/

/-- A witness `(p, a, b, c)`. -/
structure Wit where
  /-- The prime. -/
  p : ℕ
  /-- The shortest leg. -/
  a : ℕ
  /-- The longer leg. -/
  b : ℕ
  /-- The hypotenuse. -/
  c : ℕ

/-- `w` is a Pythagorean triple `0 < a < b < c < p` whose entries all have
Euler bit `res` modulo `p`. -/
def witOK (res : Bool) (w : Wit) : Bool :=
  0 < w.a && w.a < w.b && w.b < w.c && w.c < w.p && w.a ^ 2 + w.b ^ 2 == w.c ^ 2 &&
    (isQRb w.p w.a == res) && (isQRb w.p w.b == res) && (isQRb w.p w.c == res)

/-- `n` has a divisor `d` with `2 ≤ d ≤ 43`. -/
def hasSmallFactor (n : ℕ) : Bool := (List.range' 2 42).any fun d => n % d == 0

/-- Walk `n, n+1, ..., n+k-1`; skip numbers with a small factor; otherwise the
next witness must be for `n` and valid. -/
def checkRange (res : Bool) : ℕ → ℕ → List Wit → Bool
  | _, 0, _ => true
  | n, k + 1, ws =>
    if hasSmallFactor n then checkRange res (n + 1) k ws else
      match ws with
      | [] => false
      | w :: ws' => (w.p == n) && witOK res w && checkRange res (n + 1) k ws'

/-- Witness table for part (i): one triple for each prime in `[101, 1690]`. -/
def witI : List Wit :=
  [⟨101, 33, 56, 65⟩, ⟨103, 8, 15, 17⟩, ⟨107, 16, 30, 34⟩, ⟨109, 3, 4, 5⟩,
   ⟨113, 11, 60, 61⟩, ⟨127, 8, 15, 17⟩, ⟨131, 3, 4, 5⟩, ⟨137, 8, 15, 17⟩,
   ⟨139, 7, 24, 25⟩, ⟨149, 7, 24, 25⟩, ⟨151, 20, 21, 29⟩, ⟨157, 12, 35, 37⟩,
   ⟨163, 10, 24, 26⟩, ⟨167, 7, 24, 25⟩, ⟨173, 9, 40, 41⟩, ⟨179, 3, 4, 5⟩,
   ⟨181, 3, 4, 5⟩, ⟨191, 3, 4, 5⟩, ⟨193, 7, 24, 25⟩, ⟨197, 7, 24, 25⟩,
   ⟨199, 28, 45, 53⟩, ⟨211, 16, 30, 34⟩, ⟨223, 8, 15, 17⟩, ⟨227, 16, 30, 34⟩,
   ⟨229, 3, 4, 5⟩, ⟨233, 60, 91, 109⟩, ⟨239, 3, 4, 5⟩, ⟨241, 3, 4, 5⟩,
   ⟨251, 3, 4, 5⟩, ⟨257, 8, 15, 17⟩, ⟨263, 12, 35, 37⟩, ⟨269, 16, 30, 34⟩,
   ⟨271, 9, 40, 41⟩, ⟨277, 16, 30, 34⟩, ⟨281, 28, 45, 53⟩, ⟨283, 7, 24, 25⟩,
   ⟨293, 10, 24, 26⟩, ⟨307, 7, 24, 25⟩, ⟨311, 3, 4, 5⟩, ⟨313, 88, 105, 137⟩,
   ⟨317, 7, 24, 25⟩, ⟨331, 24, 70, 74⟩, ⟨337, 7, 24, 25⟩, ⟨347, 16, 30, 34⟩,
   ⟨349, 3, 4, 5⟩, ⟨353, 8, 15, 17⟩, ⟨359, 3, 4, 5⟩, ⟨367, 60, 63, 87⟩,
   ⟨373, 9, 40, 41⟩, ⟨379, 16, 30, 34⟩, ⟨383, 7, 24, 25⟩, ⟨389, 7, 24, 25⟩,
   ⟨397, 16, 30, 34⟩, ⟨401, 9, 40, 41⟩, ⟨409, 3, 4, 5⟩, ⟨419, 3, 4, 5⟩,
   ⟨421, 3, 4, 5⟩, ⟨431, 3, 4, 5⟩, ⟨433, 12, 35, 37⟩, ⟨439, 28, 45, 53⟩,
   ⟨443, 12, 35, 37⟩, ⟨449, 9, 40, 41⟩, ⟨457, 7, 24, 25⟩, ⟨461, 24, 70, 74⟩,
   ⟨463, 8, 15, 17⟩, ⟨467, 9, 40, 41⟩, ⟨479, 3, 4, 5⟩, ⟨487, 15, 36, 39⟩,
   ⟨491, 3, 4, 5⟩, ⟨499, 20, 21, 29⟩, ⟨503, 7, 24, 25⟩, ⟨509, 20, 21, 29⟩,
   ⟨521, 20, 21, 29⟩, ⟨523, 7, 24, 25⟩, ⟨541, 3, 4, 5⟩, ⟨547, 13, 84, 85⟩,
   ⟨557, 7, 24, 25⟩, ⟨563, 17, 144, 145⟩, ⟨569, 9, 40, 41⟩, ⟨571, 20, 21, 29⟩,
   ⟨577, 17, 144, 145⟩, ⟨587, 16, 63, 65⟩, ⟨593, 8, 15, 17⟩, ⟨599, 3, 4, 5⟩,
   ⟨601, 3, 4, 5⟩, ⟨607, 11, 60, 61⟩, ⟨613, 9, 40, 41⟩, ⟨617, 15, 36, 39⟩,
   ⟨619, 7, 24, 25⟩, ⟨631, 20, 21, 29⟩, ⟨641, 16, 63, 65⟩, ⟨643, 7, 24, 25⟩,
   ⟨647, 7, 24, 25⟩, ⟨653, 7, 24, 25⟩, ⟨659, 3, 4, 5⟩, ⟨661, 3, 4, 5⟩,
   ⟨673, 7, 24, 25⟩, ⟨677, 9, 40, 41⟩, ⟨683, 16, 30, 34⟩, ⟨691, 7, 24, 25⟩,
   ⟨701, 7, 24, 25⟩, ⟨709, 3, 4, 5⟩, ⟨719, 3, 4, 5⟩, ⟨727, 8, 15, 17⟩,
   ⟨733, 12, 35, 37⟩, ⟨739, 57, 176, 185⟩, ⟨743, 12, 35, 37⟩, ⟨751, 65, 72, 97⟩,
   ⟨757, 17, 144, 145⟩, ⟨761, 20, 21, 29⟩, ⟨769, 3, 4, 5⟩, ⟨773, 10, 24, 26⟩,
   ⟨787, 7, 24, 25⟩, ⟨797, 9, 40, 41⟩, ⟨809, 16, 63, 65⟩, ⟨811, 7, 24, 25⟩,
   ⟨821, 7, 24, 25⟩, ⟨823, 13, 84, 85⟩, ⟨827, 16, 30, 34⟩, ⟨829, 3, 4, 5⟩,
   ⟨839, 3, 4, 5⟩, ⟨853, 16, 30, 34⟩, ⟨857, 13, 84, 85⟩, ⟨859, 7, 24, 25⟩,
   ⟨863, 12, 35, 37⟩, ⟨877, 16, 30, 34⟩, ⟨881, 9, 40, 41⟩, ⟨883, 56, 90, 106⟩,
   ⟨887, 7, 24, 25⟩, ⟨907, 9, 40, 41⟩, ⟨911, 3, 4, 5⟩, ⟨919, 20, 21, 29⟩,
   ⟨929, 20, 21, 29⟩, ⟨937, 12, 35, 37⟩, ⟨941, 20, 21, 29⟩, ⟨947, 16, 30, 34⟩,
   ⟨953, 8, 15, 17⟩, ⟨967, 8, 15, 17⟩, ⟨971, 3, 4, 5⟩, ⟨977, 8, 15, 17⟩,
   ⟨983, 7, 24, 25⟩, ⟨991, 20, 21, 29⟩, ⟨997, 16, 30, 34⟩, ⟨1009, 3, 4, 5⟩,
   ⟨1013, 13, 84, 85⟩, ⟨1019, 3, 4, 5⟩, ⟨1021, 3, 4, 5⟩, ⟨1031, 3, 4, 5⟩,
   ⟨1033, 7, 24, 25⟩, ⟨1039, 16, 63, 65⟩, ⟨1049, 20, 21, 29⟩, ⟨1051, 20, 21, 29⟩,
   ⟨1061, 7, 24, 25⟩, ⟨1063, 8, 15, 17⟩, ⟨1069, 3, 4, 5⟩, ⟨1087, 8, 15, 17⟩,
   ⟨1091, 3, 4, 5⟩, ⟨1093, 16, 30, 34⟩, ⟨1097, 8, 15, 17⟩, ⟨1103, 12, 35, 37⟩,
   ⟨1109, 20, 21, 29⟩, ⟨1117, 16, 30, 34⟩, ⟨1123, 7, 24, 25⟩, ⟨1129, 3, 4, 5⟩,
   ⟨1151, 3, 4, 5⟩, ⟨1153, 25, 312, 313⟩, ⟨1163, 16, 30, 34⟩, ⟨1171, 33, 56, 65⟩,
   ⟨1181, 20, 99, 101⟩, ⟨1187, 16, 30, 34⟩, ⟨1193, 11, 60, 61⟩, ⟨1201, 3, 4, 5⟩,
   ⟨1213, 16, 30, 34⟩, ⟨1217, 15, 36, 39⟩, ⟨1223, 7, 24, 25⟩, ⟨1229, 7, 24, 25⟩,
   ⟨1231, 9, 40, 41⟩, ⟨1237, 12, 35, 37⟩, ⟨1249, 3, 4, 5⟩, ⟨1259, 3, 4, 5⟩,
   ⟨1277, 11, 60, 61⟩, ⟨1279, 9, 40, 41⟩, ⟨1283, 12, 35, 37⟩, ⟨1289, 9, 40, 41⟩,
   ⟨1291, 7, 24, 25⟩, ⟨1297, 7, 24, 25⟩, ⟨1301, 20, 21, 29⟩, ⟨1303, 13, 84, 85⟩,
   ⟨1307, 9, 40, 41⟩, ⟨1319, 3, 4, 5⟩, ⟨1321, 3, 4, 5⟩, ⟨1327, 8, 15, 17⟩,
   ⟨1361, 9, 40, 41⟩, ⟨1367, 36, 77, 85⟩, ⟨1373, 7, 24, 25⟩, ⟨1381, 3, 4, 5⟩,
   ⟨1399, 9, 40, 41⟩, ⟨1409, 36, 77, 85⟩, ⟨1423, 15, 36, 39⟩, ⟨1427, 9, 40, 41⟩,
   ⟨1429, 3, 4, 5⟩, ⟨1433, 13, 84, 85⟩, ⟨1439, 3, 4, 5⟩, ⟨1447, 8, 15, 17⟩,
   ⟨1451, 3, 4, 5⟩, ⟨1453, 9, 40, 41⟩, ⟨1459, 7, 24, 25⟩, ⟨1471, 9, 40, 41⟩,
   ⟨1481, 9, 40, 41⟩, ⟨1483, 7, 24, 25⟩, ⟨1487, 7, 24, 25⟩, ⟨1489, 3, 4, 5⟩,
   ⟨1493, 7, 24, 25⟩, ⟨1499, 3, 4, 5⟩, ⟨1511, 3, 4, 5⟩, ⟨1523, 16, 30, 34⟩,
   ⟨1531, 7, 24, 25⟩, ⟨1543, 8, 15, 17⟩, ⟨1549, 3, 4, 5⟩, ⟨1553, 15, 36, 39⟩,
   ⟨1559, 3, 4, 5⟩, ⟨1567, 15, 36, 39⟩, ⟨1571, 3, 4, 5⟩, ⟨1579, 20, 21, 29⟩,
   ⟨1583, 88, 105, 137⟩, ⟨1597, 9, 40, 41⟩, ⟨1601, 20, 21, 29⟩, ⟨1607, 12, 35, 37⟩,
   ⟨1609, 3, 4, 5⟩, ⟨1613, 56, 90, 106⟩, ⟨1619, 3, 4, 5⟩, ⟨1621, 3, 4, 5⟩,
   ⟨1627, 7, 24, 25⟩, ⟨1637, 13, 84, 85⟩, ⟨1657, 65, 72, 97⟩, ⟨1663, 11, 60, 61⟩,
   ⟨1667, 40, 42, 58⟩, ⟨1669, 3, 4, 5⟩]

/-- Witness table for part (ii): one triple for each prime in `[51, 1850]`. -/
def witII : List Wit :=
  [⟨53, 14, 48, 50⟩, ⟨59, 6, 8, 10⟩, ⟨61, 6, 8, 10⟩, ⟨67, 5, 12, 13⟩,
   ⟨71, 21, 28, 35⟩, ⟨73, 20, 21, 29⟩, ⟨79, 12, 35, 37⟩, ⟨83, 18, 80, 82⟩,
   ⟨89, 12, 35, 37⟩, ⟨97, 20, 21, 29⟩, ⟨101, 11, 60, 61⟩, ⟨103, 12, 35, 37⟩,
   ⟨107, 8, 15, 17⟩, ⟨109, 6, 8, 10⟩, ⟨113, 20, 21, 29⟩, ⟨127, 24, 45, 51⟩,
   ⟨131, 6, 8, 10⟩, ⟨137, 5, 12, 13⟩, ⟨139, 8, 15, 17⟩, ⟨149, 14, 48, 50⟩,
   ⟨151, 33, 56, 65⟩, ⟨157, 20, 21, 29⟩, ⟨163, 5, 12, 13⟩, ⟨167, 60, 91, 109⟩,
   ⟨173, 28, 45, 53⟩, ⟨179, 6, 8, 10⟩, ⟨181, 6, 8, 10⟩, ⟨191, 21, 28, 35⟩,
   ⟨193, 11, 60, 61⟩, ⟨197, 5, 12, 13⟩, ⟨199, 48, 55, 73⟩, ⟨211, 8, 15, 17⟩,
   ⟨223, 5, 12, 13⟩, ⟨227, 8, 15, 17⟩, ⟨229, 6, 8, 10⟩, ⟨233, 24, 143, 145⟩,
   ⟨239, 21, 28, 35⟩, ⟨241, 21, 28, 35⟩, ⟨251, 6, 8, 10⟩, ⟨257, 24, 45, 51⟩,
   ⟨263, 20, 21, 29⟩, ⟨269, 8, 15, 17⟩, ⟨271, 60, 91, 109⟩, ⟨277, 8, 15, 17⟩,
   ⟨281, 11, 60, 61⟩, ⟨283, 12, 35, 37⟩, ⟨293, 5, 12, 13⟩, ⟨307, 5, 12, 13⟩,
   ⟨311, 33, 44, 55⟩, ⟨313, 28, 45, 53⟩, ⟨317, 5, 12, 13⟩, ⟨331, 12, 35, 37⟩,
   ⟨337, 11, 60, 61⟩, ⟨347, 8, 15, 17⟩, ⟨349, 6, 8, 10⟩, ⟨353, 5, 12, 13⟩,
   ⟨359, 21, 28, 35⟩, ⟨367, 20, 21, 29⟩, ⟨373, 11, 60, 61⟩, ⟨379, 8, 15, 17⟩,
   ⟨383, 11, 60, 61⟩, ⟨389, 14, 48, 50⟩, ⟨397, 8, 15, 17⟩, ⟨401, 13, 84, 85⟩,
   ⟨409, 21, 28, 35⟩, ⟨419, 6, 8, 10⟩, ⟨421, 6, 8, 10⟩, ⟨431, 21, 28, 35⟩,
   ⟨433, 20, 21, 29⟩, ⟨439, 85, 132, 157⟩, ⟨443, 20, 21, 29⟩, ⟨449, 13, 84, 85⟩,
   ⟨457, 11, 60, 61⟩, ⟨461, 12, 35, 37⟩, ⟨463, 5, 12, 13⟩, ⟨467, 11, 60, 61⟩,
   ⟨479, 39, 52, 65⟩, ⟨487, 5, 12, 13⟩, ⟨491, 6, 8, 10⟩, ⟨499, 8, 15, 17⟩,
   ⟨503, 35, 120, 125⟩, ⟨509, 40, 42, 58⟩, ⟨521, 60, 63, 87⟩, ⟨523, 12, 35, 37⟩,
   ⟨541, 6, 8, 10⟩, ⟨547, 39, 80, 89⟩, ⟨557, 5, 12, 13⟩, ⟨563, 65, 72, 97⟩,
   ⟨569, 48, 55, 73⟩, ⟨571, 8, 15, 17⟩, ⟨577, 20, 21, 29⟩, ⟨587, 11, 60, 61⟩,
   ⟨593, 5, 12, 13⟩, ⟨599, 21, 28, 35⟩, ⟨601, 21, 28, 35⟩, ⟨607, 20, 21, 29⟩,
   ⟨613, 18, 80, 82⟩, ⟨617, 5, 12, 13⟩, ⟨619, 8, 15, 17⟩, ⟨631, 12, 35, 37⟩,
   ⟨641, 48, 189, 195⟩, ⟨643, 5, 12, 13⟩, ⟨647, 11, 60, 61⟩, ⟨653, 20, 21, 29⟩,
   ⟨659, 6, 8, 10⟩, ⟨661, 6, 8, 10⟩, ⟨673, 11, 60, 61⟩, ⟨677, 28, 45, 53⟩,
   ⟨683, 8, 15, 17⟩, ⟨691, 8, 15, 17⟩, ⟨701, 14, 48, 50⟩, ⟨709, 6, 8, 10⟩,
   ⟨719, 33, 44, 55⟩, ⟨727, 20, 21, 29⟩, ⟨733, 20, 21, 29⟩, ⟨739, 65, 72, 97⟩,
   ⟨743, 20, 21, 29⟩, ⟨751, 48, 55, 73⟩, ⟨757, 65, 72, 97⟩, ⟨761, 11, 60, 61⟩,
   ⟨769, 21, 28, 35⟩, ⟨773, 5, 12, 13⟩, ⟨787, 5, 12, 13⟩, ⟨797, 28, 45, 53⟩,
   ⟨809, 88, 105, 137⟩, ⟨811, 8, 15, 17⟩, ⟨821, 8, 15, 17⟩, ⟨823, 20, 99, 101⟩,
   ⟨827, 8, 15, 17⟩, ⟨829, 6, 8, 10⟩, ⟨839, 33, 44, 55⟩, ⟨853, 8, 15, 17⟩,
   ⟨857, 39, 80, 89⟩, ⟨859, 14, 48, 50⟩, ⟨863, 13, 84, 85⟩, ⟨877, 8, 15, 17⟩,
   ⟨881, 15, 112, 113⟩, ⟨883, 28, 45, 53⟩, ⟨887, 35, 120, 125⟩, ⟨907, 18, 80, 82⟩,
   ⟨911, 21, 28, 35⟩, ⟨919, 12, 35, 37⟩, ⟨929, 33, 56, 65⟩, ⟨937, 33, 56, 65⟩,
   ⟨941, 8, 15, 17⟩, ⟨947, 8, 15, 17⟩, ⟨953, 24, 45, 51⟩, ⟨967, 5, 12, 13⟩,
   ⟨971, 6, 8, 10⟩, ⟨977, 5, 12, 13⟩, ⟨983, 11, 60, 61⟩, ⟨991, 12, 35, 37⟩,
   ⟨997, 8, 15, 17⟩, ⟨1009, 33, 44, 55⟩, ⟨1013, 88, 105, 137⟩, ⟨1019, 6, 8, 10⟩,
   ⟨1021, 6, 8, 10⟩, ⟨1031, 21, 28, 35⟩, ⟨1033, 39, 80, 89⟩, ⟨1039, 11, 60, 61⟩,
   ⟨1049, 12, 35, 37⟩, ⟨1051, 8, 15, 17⟩, ⟨1061, 8, 15, 17⟩, ⟨1063, 20, 21, 29⟩,
   ⟨1069, 6, 8, 10⟩, ⟨1087, 5, 12, 13⟩, ⟨1091, 6, 8, 10⟩, ⟨1093, 8, 15, 17⟩,
   ⟨1097, 5, 12, 13⟩, ⟨1103, 13, 84, 85⟩, ⟨1109, 40, 42, 58⟩, ⟨1117, 8, 15, 17⟩,
   ⟨1123, 5, 12, 13⟩, ⟨1129, 33, 44, 55⟩, ⟨1151, 39, 52, 65⟩, ⟨1153, 15, 112, 113⟩,
   ⟨1163, 8, 15, 17⟩, ⟨1171, 12, 35, 37⟩, ⟨1181, 65, 72, 97⟩, ⟨1187, 8, 15, 17⟩,
   ⟨1193, 28, 45, 53⟩, ⟨1201, 33, 44, 55⟩, ⟨1213, 8, 15, 17⟩, ⟨1217, 5, 12, 13⟩,
   ⟨1223, 35, 120, 125⟩, ⟨1229, 8, 15, 17⟩, ⟨1231, 27, 120, 123⟩, ⟨1237, 20, 21, 29⟩,
   ⟨1249, 21, 28, 35⟩, ⟨1259, 6, 8, 10⟩, ⟨1277, 28, 45, 53⟩, ⟨1279, 11, 60, 61⟩,
   ⟨1283, 24, 70, 74⟩, ⟨1289, 11, 60, 61⟩, ⟨1291, 14, 48, 50⟩, ⟨1297, 35, 120, 125⟩,
   ⟨1301, 12, 35, 37⟩, ⟨1303, 28, 45, 53⟩, ⟨1307, 11, 60, 61⟩, ⟨1319, 39, 52, 65⟩,
   ⟨1321, 21, 28, 35⟩, ⟨1327, 24, 45, 51⟩, ⟨1361, 12, 35, 37⟩, ⟨1367, 44, 117, 125⟩,
   ⟨1373, 5, 12, 13⟩, ⟨1381, 6, 8, 10⟩, ⟨1399, 13, 84, 85⟩, ⟨1409, 60, 91, 109⟩,
   ⟨1423, 5, 12, 13⟩, ⟨1427, 18, 80, 82⟩, ⟨1429, 6, 8, 10⟩, ⟨1433, 28, 45, 53⟩,
   ⟨1439, 21, 28, 35⟩, ⟨1447, 20, 21, 29⟩, ⟨1451, 6, 8, 10⟩, ⟨1453, 18, 80, 82⟩,
   ⟨1459, 8, 15, 17⟩, ⟨1471, 33, 56, 65⟩, ⟨1481, 11, 60, 61⟩, ⟨1483, 14, 48, 50⟩,
   ⟨1487, 39, 80, 89⟩, ⟨1489, 21, 28, 35⟩, ⟨1493, 5, 12, 13⟩, ⟨1499, 6, 8, 10⟩,
   ⟨1511, 33, 44, 55⟩, ⟨1523, 8, 15, 17⟩, ⟨1531, 14, 48, 50⟩, ⟨1543, 24, 45, 51⟩,
   ⟨1549, 6, 8, 10⟩, ⟨1553, 5, 12, 13⟩, ⟨1559, 51, 68, 85⟩, ⟨1567, 5, 12, 13⟩,
   ⟨1571, 6, 8, 10⟩, ⟨1579, 40, 42, 58⟩, ⟨1583, 20, 21, 29⟩, ⟨1597, 11, 60, 61⟩,
   ⟨1601, 48, 55, 73⟩, ⟨1607, 20, 21, 29⟩, ⟨1609, 21, 28, 35⟩, ⟨1613, 28, 45, 53⟩,
   ⟨1619, 6, 8, 10⟩, ⟨1621, 6, 8, 10⟩, ⟨1627, 5, 12, 13⟩, ⟨1637, 48, 55, 73⟩,
   ⟨1657, 28, 45, 53⟩, ⟨1663, 28, 45, 53⟩, ⟨1667, 20, 21, 29⟩, ⟨1669, 6, 8, 10⟩,
   ⟨1693, 8, 15, 17⟩, ⟨1697, 5, 12, 13⟩, ⟨1699, 14, 48, 50⟩, ⟨1709, 14, 48, 50⟩,
   ⟨1721, 12, 35, 37⟩, ⟨1723, 5, 12, 13⟩, ⟨1733, 12, 35, 37⟩, ⟨1741, 6, 8, 10⟩,
   ⟨1747, 5, 12, 13⟩, ⟨1753, 13, 84, 85⟩, ⟨1759, 12, 35, 37⟩, ⟨1777, 20, 21, 29⟩,
   ⟨1783, 5, 12, 13⟩, ⟨1787, 20, 21, 29⟩, ⟨1789, 6, 8, 10⟩, ⟨1801, 33, 44, 55⟩,
   ⟨1811, 6, 8, 10⟩, ⟨1823, 35, 120, 125⟩, ⟨1831, 12, 35, 37⟩, ⟨1847, 35, 120, 125⟩]

/-- Kernel check of the witness table for part (i). -/
theorem witI_check : checkRange true 101 1590 witI = true := by decide +kernel

/-- Kernel check of the witness table for part (ii). -/
theorem witII_check : checkRange false 51 1800 witII = true := by decide +kernel

/-- Soundness of `checkRange`: every `p` in the window without a small factor
has a valid witness in the list. -/
theorem checkRange_sound (res : Bool) (k : ℕ) : ∀ (n : ℕ) (ws : List Wit),
    checkRange res n k ws = true → ∀ p, n ≤ p → p < n + k → hasSmallFactor p = false →
      ∃ w ∈ ws, w.p = p ∧ witOK res w = true := by
  induction k with
  | zero => intro n ws _ p h1 h2 _; omega
  | succ k ih =>
    intro n ws h p h1 h2 hsf
    by_cases hn : hasSmallFactor n = true
    · simp only [checkRange, hn, ↓reduceIte] at h
      have h1' : n + 1 ≤ p := by
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · rw [hsf] at hn; exact absurd hn (by decide)
        · exact hlt
      exact ih (n + 1) ws h p h1' (by omega) hsf
    · simp only [checkRange, hn, Bool.false_eq_true, ↓reduceIte] at h
      cases ws with
      | nil => simp at h
      | cons w ws' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨hwp, hw⟩, hrest⟩ := h
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact ⟨w, List.mem_cons_self, hwp, hw⟩
        · obtain ⟨w', hw'mem, hw'p, hw'ok⟩ := ih (n + 1) ws' hrest p hlt (by omega) hsf
          exact ⟨w', List.mem_cons_of_mem w hw'mem, hw'p, hw'ok⟩

/-- A prime `p > 43` has no divisor in `[2, 43]`. -/
theorem hasSmallFactor_eq_false (p : ℕ) (hp : p.Prime) (h : 43 < p) :
    hasSmallFactor p = false := by
  rw [Bool.eq_false_iff]
  intro hs
  simp only [hasSmallFactor, List.any_eq_true, List.mem_range'_1, beq_iff_eq] at hs
  obtain ⟨d, ⟨hd2, hd43⟩, hd⟩ := hs
  rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hd) with h1 | h1 <;> omega

/-- Reading a residue status off a passed Euler bit. -/
theorem isSquare_iff_of_isQRb (p r : ℕ) [Fact p.Prime] (res : Bool) (h0 : 0 < r) (hr : r < p)
    (hb : isQRb p r = res) : IsSquare (r : ZMod p) ↔ res = true := by
  rw [isSquare_iff_isQRb p r (natCast_ne_zero_of_pos_of_lt p r h0 hr), hb]

/-- Small primes for part (i): `101 ≤ p ≤ 1690`, from the witness table. -/
theorem exists_inR_of_le_1690 (p : ℕ) (hp : p.Prime) (h1 : 100 < p) (h2 : p ≤ 1690) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ InR p a ∧ InR p b ∧ InR p c := by
  obtain ⟨w, -, hwp, hw⟩ := checkRange_sound true 1590 101 witI witI_check p (by omega)
    (by omega) (hasSmallFactor_eq_false p hp (by omega))
  subst hwp
  haveI := Fact.mk hp
  simp only [witOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨ha0, hab⟩, hbc⟩, hcp⟩, hpy⟩, hA⟩, hB⟩, hC⟩ := hw
  refine ⟨w.a, w.b, w.c, hab, hbc, hpy, ⟨ha0, by omega, ?_⟩, ⟨by omega, by omega, ?_⟩,
    ⟨by omega, hcp, ?_⟩⟩
  · exact (isSquare_iff_of_isQRb w.p w.a true ha0 (by omega) hA).mpr rfl
  · exact (isSquare_iff_of_isQRb w.p w.b true (by omega) (by omega) hB).mpr rfl
  · exact (isSquare_iff_of_isQRb w.p w.c true (by omega) hcp hC).mpr rfl

/-- Small primes for part (ii): `51 ≤ p ≤ 1850`, from the witness table. -/
theorem exists_inN_of_le_1850 (p : ℕ) (hp : p.Prime) (h1 : 50 < p) (h2 : p ≤ 1850) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ InN p a ∧ InN p b ∧ InN p c := by
  obtain ⟨w, -, hwp, hw⟩ := checkRange_sound false 1800 51 witII witII_check p (by omega)
    (by omega) (hasSmallFactor_eq_false p hp (by omega))
  subst hwp
  haveI := Fact.mk hp
  simp only [witOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨ha0, hab⟩, hbc⟩, hcp⟩, hpy⟩, hA⟩, hB⟩, hC⟩ := hw
  refine ⟨w.a, w.b, w.c, hab, hbc, hpy, ⟨ha0, by omega, ?_⟩, ⟨by omega, by omega, ?_⟩,
    ⟨by omega, hcp, ?_⟩⟩
  · exact fun hsq => absurd ((isSquare_iff_of_isQRb w.p w.a false ha0 (by omega) hA).mp hsq)
      (by decide)
  · exact fun hsq => absurd ((isSquare_iff_of_isQRb w.p w.b false (by omega) (by omega) hB).mp
      hsq) (by decide)
  · exact fun hsq => absurd ((isSquare_iff_of_isQRb w.p w.c false (by omega) hcp hC).mp hsq)
      (by decide)

/-! ## Large primes -/

/-- Residue status of a valid entry, read off the residue bits of `S`. -/
theorem isSquare_iff_maskRes (p : ℕ) [Fact p.Prime] (e : Entry) (he : entryOK e = true)
    (h0 : 0 < e.n) (hp : e.n < p) :
    IsSquare (e.n : ZMod p) ↔ maskRes (primesS.map (resBit p)) e.mask = true := by
  rw [maskRes_map]
  exact isSquare_iff_prodRes p e.n e.m _ (beq_iff_eq.mp he)
    (natCast_ne_zero_of_pos_of_lt p e.n h0 hp)

/-- Large primes for part (i): `p > 1690`, from the cover lemma. -/
theorem exists_inR_of_1690_lt (p : ℕ) [Fact p.Prime] (hp : 1690 < p) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ InR p a ∧ InR p b ∧ InR p c := by
  have hcov := coverI_all (primesS.map (resBit p)) (by simp [primesS])
  simp only [coverF, Bool.false_and, Bool.or_false, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hcov
  obtain ⟨t, ht, ⟨rA, rB⟩, rC⟩ := hcov
  have hok := List.all_eq_true.mp triplesI_ok t ht
  simp only [tripleOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, ha0⟩, hab⟩, hbc⟩, hc⟩, hpy⟩ := hok
  refine ⟨t.1.n, t.2.1.n, t.2.2.n, hab, hbc, hpy,
    ⟨ha0, by omega, (isSquare_iff_maskRes p _ hA ha0 (by omega)).mpr rA⟩,
    ⟨by omega, by omega, (isSquare_iff_maskRes p _ hB (by omega) (by omega)).mpr rB⟩,
    ⟨by omega, by omega, (isSquare_iff_maskRes p _ hC (by omega) (by omega)).mpr rC⟩⟩

/-- An odd prime has a nonresidue in `(0, p)`. -/
theorem exists_nonsquare_lt (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ n : ℕ, 0 < n ∧ n < p ∧ ¬IsSquare (n : ZMod p) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare hchar
  refine ⟨x.val, ?_, ZMod.val_lt x, by rwa [ZMod.natCast_zmod_val]⟩
  rw [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
  rintro rfl
  exact hx ⟨0, by simp⟩

/-- If every prime `q ≤ 43` is a residue mod `p`, then so is every
`0 < n ≤ 46` (all such `n` are `43`-smooth). -/
theorem isSquare_of_le_46 (p : ℕ) (hS : ∀ q : ℕ, q.Prime → q ≤ 43 → IsSquare (q : ZMod p)) :
    ∀ n : ℕ, 0 < n → n ≤ 46 → IsSquare (n : ZMod p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h0 h46
    by_cases h1 : n = 1
    · subst h1; exact ⟨1, by simp⟩
    by_cases hpr : n.Prime
    · apply hS n hpr
      by_contra hc
      interval_cases n <;> norm_num at hpr
    · have h2 : 2 ≤ n := by omega
      have hlt : n.minFac < n := (Nat.not_prime_iff_minFac_lt h2).mp hpr
      have hpos : 0 < n.minFac := Nat.minFac_pos n
      have hk : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
      have hkpos : 0 < n / n.minFac := Nat.div_pos (Nat.minFac_le (by omega)) hpos
      have hklt : n / n.minFac < n :=
        Nat.div_lt_self (by omega) (Nat.minFac_prime (by omega)).one_lt
      rw [hk, Nat.cast_mul]
      exact (ih _ hlt hpos (by omega)).mul (ih _ hklt hkpos (by omega))

/-- **Least-nonresidue step.** If every prime `q ≤ 43` is a residue mod a
prime `p > 50`, there is a nonresidue `q` with `46 < q` and `5q < p`
(classically `q (q - 1) < p` for the least nonresidue `q`). -/
theorem exists_nonsquare_five_mul_lt (p : ℕ) [Fact p.Prime] (hp : 50 < p)
    (hS : ∀ q : ℕ, q.Prime → q ≤ 43 → IsSquare (q : ZMod p)) :
    ∃ q : ℕ, 46 < q ∧ 5 * q < p ∧ ¬IsSquare (q : ZMod p) := by
  classical
  have hsmooth := isSquare_of_le_46 p hS
  have hex : ∃ n : ℕ, 0 < n ∧ n < p ∧ ¬IsSquare (n : ZMod p) :=
    exists_nonsquare_lt p (by omega)
  have hex' : ∃ n : ℕ, 0 < n ∧ ¬IsSquare (n : ZMod p) :=
    hex.imp fun n hn => ⟨hn.1, hn.2.2⟩
  obtain ⟨n0, hn0, hn0p, hn0s⟩ := hex
  set q := Nat.find hex' with hqdef
  have hq : 0 < q ∧ ¬IsSquare (q : ZMod p) := Nat.find_spec hex'
  have hmin : ∀ n : ℕ, 0 < n → n < q → IsSquare (n : ZMod p) := fun n h0 hn => by
    by_contra hns
    exact Nat.find_min hex' hn ⟨h0, hns⟩
  have hqn0 : q ≤ n0 := Nat.find_min' hex' ⟨hn0, hn0s⟩
  have hq46 : 46 < q := by
    by_contra hc
    exact hq.2 (hsmooth q hq.1 (by omega))
  have hqp : q < p := by omega
  have hmod : 0 < p % q := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero h) with h1 | h1
      <;> omega
  have hmodlt : p % q < q := Nat.mod_lt p (by omega)
  have hdecomp : q * (p / q) + p % q = p := Nat.div_add_mod p q
  set s := p / q with hs
  set m := s + 1 with hm
  have hmq : m * q = q * s + q := by rw [hm]; ring
  set r := q - p % q with hr
  have hr0 : 0 < r := by omega
  have hrq : r < q := by omega
  have hrp : r + p = m * q := by
    generalize q * s = u at hdecomp hmq
    omega
  have hcast : (r : ZMod p) = (m : ZMod p) * (q : ZMod p) := by
    have h' : ((r + p : ℕ) : ZMod p) = ((m * q : ℕ) : ZMod p) := by rw [hrp]
    rw [Nat.cast_add, ZMod.natCast_self, add_zero, Nat.cast_mul] at h'
    exact h'
  have hqm : q ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    have hm0 : 0 < m := Nat.succ_pos s
    have hm0' : (m : ZMod p) ≠ 0 := natCast_ne_zero_of_pos_of_lt p m hm0 (lt_trans hlt hqp)
    exact hq.2 (isSquare_of_isSquare_mul (hmin m hm0 hlt) hm0' (hcast ▸ hmin r hr0 hrq))
  have h46s : 46 ≤ s := by omega
  have hle : q * 46 ≤ q * s := Nat.mul_le_mul_left q h46s
  refine ⟨q, hq46, ?_, hq.2⟩
  generalize q * s = u at hdecomp hle
  omega

/-- Large primes for part (ii) in the all-residue pattern, via
`(3q, 4q, 5q)` for a nonresidue `q` with `5q < p`. -/
theorem exists_inN_of_allRes (p : ℕ) [Fact p.Prime] (hp : 50 < p)
    (hS : ∀ q : ℕ, q.Prime → q ≤ 43 → IsSquare (q : ZMod p)) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ InN p a ∧ InN p b ∧ InN p c := by
  obtain ⟨q, hq46, h5q, hqs⟩ := exists_nonsquare_five_mul_lt p hp hS
  have hnon : ∀ k : ℕ, 0 < k → k ≤ 5 → IsSquare (k : ZMod p) → InN p (k * q) := by
    intro k hk0 hk5 hksq
    refine ⟨by positivity, by nlinarith, fun hsq => hqs ?_⟩
    rw [Nat.cast_mul] at hsq
    exact isSquare_of_isSquare_mul hksq (natCast_ne_zero_of_pos_of_lt p k hk0 (by omega)) hsq
  have h3 : IsSquare ((3 : ℕ) : ZMod p) := hS 3 (by norm_num) (by norm_num)
  have h4 : IsSquare ((4 : ℕ) : ZMod p) := ⟨2, by norm_num⟩
  have h5 : IsSquare ((5 : ℕ) : ZMod p) := hS 5 (by norm_num) (by norm_num)
  exact ⟨3 * q, 4 * q, 5 * q, by omega, by omega, by ring, hnon 3 (by norm_num) (by norm_num) h3,
    hnon 4 (by norm_num) (by norm_num) h4, hnon 5 (by norm_num) (by norm_num) h5⟩

/-- Large primes for part (ii): `p > 1850`, from the cover lemma and the
least-nonresidue step. -/
theorem exists_inN_of_1850_lt (p : ℕ) [Fact p.Prime] (hp : 1850 < p) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ InN p a ∧ InN p b ∧ InN p c := by
  have hcov := coverII_all (primesS.map (resBit p)) (by simp [primesS])
  simp only [coverF, Bool.true_and, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hcov
  rcases hcov with ⟨t, ht, ⟨rA, rB⟩, rC⟩ | hall
  · have hok := List.all_eq_true.mp triplesII_ok t ht
    simp only [tripleOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, ha0⟩, hab⟩, hbc⟩, hc⟩, hpy⟩ := hok
    refine ⟨t.1.n, t.2.1.n, t.2.2.n, hab, hbc, hpy, ⟨ha0, by omega, fun hsq => ?_⟩,
      ⟨by omega, by omega, fun hsq => ?_⟩, ⟨by omega, by omega, fun hsq => ?_⟩⟩
    · have h := (isSquare_iff_maskRes p _ hA ha0 (by omega)).mp hsq
      rw [rA] at h; exact Bool.false_ne_true h
    · have h := (isSquare_iff_maskRes p _ hB (by omega) (by omega)).mp hsq
      rw [rB] at h; exact Bool.false_ne_true h
    · have h := (isSquare_iff_maskRes p _ hC (by omega) (by omega)).mp hsq
      rw [rC] at h; exact Bool.false_ne_true h
  · refine exists_inN_of_allRes p (by omega) fun q hq hq43 => ?_
    have hmem : q ∈ primesS := by
      interval_cases q <;> first | decide | (exfalso; norm_num at hq)
    have hbit := List.all_eq_true.mp hall (resBit p q) (List.mem_map_of_mem hmem)
    exact (resBit_eq_true_iff p q).mp hbit

/-! ## The conjecture, parts (i) and (ii) -/

/-- **Sun's conjecture A260911 (i)** (Zhi-Wei Sun, Aug 03 2015), proved
here.  Verbatim: "for any prime p > 100, we have a^2 + b^2 = c^2 for some
a,b,c in the set R(p) = {0<r<p: r is a quadratic residue mod p}."  The
ordering `a < b` is no restriction: `a = b` is impossible for positive
`a^2 + b^2 = c^2`. -/
theorem sun_A260911_i (p : ℕ) (hp : p.Prime) (h : 100 < p) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ InR p a ∧ InR p b ∧ InR p c := by
  by_cases hlarge : 1690 < p
  · haveI := Fact.mk hp
    exact exists_inR_of_1690_lt p hlarge
  · exact exists_inR_of_le_1690 p hp h (by omega)

/-- **Sun's conjecture A260911 (ii)** (Zhi-Wei Sun, Aug 03 2015), proved
here.  Verbatim: "For any prime p > 50, we have a^2 + b^2 = c^2 for some
a,b,c in the set N(p) = {0<n<p: n is a quadratic nonresidue mod p}." -/
theorem sun_A260911_ii (p : ℕ) (hp : p.Prime) (h : 50 < p) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ InN p a ∧ InN p b ∧ InN p c := by
  by_cases hlarge : 1850 < p
  · haveI := Fact.mk hp
    exact exists_inN_of_1850_lt p hlarge
  · exact exists_inN_of_le_1850 p hp h (by omega)

open Classical in
/-- **A260911 (i) in the entry's own form**: `a(n) > 0` for all `n > 25`
(`prime(26) = 101`). -/
theorem a260911_pos (n : ℕ) (hn : 25 < n) : 0 < a260911 n := by
  have hc : Nat.count Nat.Prime 101 = 25 := by decide +kernel
  have h101 : Nat.nth Nat.Prime 25 = 101 :=
    hc ▸ Nat.nth_count (p := Nat.Prime) (by norm_num : Nat.Prime 101)
  have hmono : Nat.nth Nat.Prime 25 ≤ Nat.nth Nat.Prime (n - 1) :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
  have hpr : (Nat.nth Nat.Prime (n - 1)).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n - 1)
  obtain ⟨a, b, c, hab, hbc, hpy, ha, hb, hc⟩ :=
    sun_A260911_i (Nat.nth Nat.Prime (n - 1)) hpr (by omega)
  have hex : ∃ k, Admissible (Nat.nth Nat.Prime (n - 1)) k :=
    ⟨c, hc.2.1, a, b, hab, hbc, hpy, ha, hb, hc⟩
  rw [a260911, dif_pos hex]
  obtain ⟨-, i, j, hij, hjk, -⟩ := Nat.find_spec hex
  omega

/-- Satisfiability of the hypotheses at the thresholds' first primes. -/
example : Nat.Prime 101 ∧ 100 < 101 ∧ Nat.Prime 53 ∧ 50 < 53 := by norm_num


end Candidates.A260911SunPartsPrime
