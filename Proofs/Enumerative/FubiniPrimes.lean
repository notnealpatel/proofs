import Mathlib
import Enumerative.FubiniMod

/-!
# Fubini primes and Muljadi's `4n+1` observation (OEIS A000670)

## Source, pinned verbatim

Re-pulled with `goof oeis show A000670` on 2026-08-05.

Sequence name (verbatim):

> Fubini numbers: number of preferential arrangements of n labeled elements;
> or number of weak orders on n labeled elements; or number of ordered
> partitions of [n].

Keywords (verbatim): `nonn,core,nice,easy`

Terms (verbatim, first 22):

> 1, 1, 3, 13, 75, 541, 4683, 47293, 545835, 7087261, 102247563, 1622632573,
> 28091567595, 526858348381, 10641342970443, 230283190977853,
> 5315654681981355, 130370767029135901, 3385534663256845323,
> 92801587319328411133, 2677687796244384203115, 81124824998504073881821

The archived comment (verbatim, the whole line, from the `comments` field):

> It appears that the prime numbers greater than 3 in this sequence
> (13, 541, 47293, ...) are of the form 4n+1. - _Paul Muljadi_, Jan 28 2011

## Status: proved, not archived as a conjecture

The dispatching brief asked for this claim to be *archived* with one intended
`sorry`.  It is not a conjecture: it is an elementary consequence of two
congruences, one of which is already proved in `Enumerative/FubiniMod.lean`.
This file therefore carries **no `sorry`** — see the deviation note at the end
of this docstring.

## The proof

Write `f n = A051293.fubini n`.  Two residue facts pin the claim.

* **Odd indices, modulo 4.**  `f n ≡ 1 (mod 4)` whenever `n` is odd.  This is
  the mod-4 half of Bala's periodicity, already available as
  `A000670.fubini_add_two_modEq_four` (`Enumerative/FubiniMod.lean`): the
  residues run `1, 3, 1, 3, …` from `n = 1`, and `f 1 = 1`.

* **Even indices, modulo 3.**  `3 ∣ f n` whenever `n` is even and `2 ≤ n`.
  This file proves the closed form `(f m : ZMod 3) = 2 ^ m - 1` for `1 ≤ m`
  (`fubini_zmod3`), by the same strong induction on the Fubini recurrence
  `f (n+1) = ∑_{j ≤ n} C(n+1,j) · f j` used for the moduli `2` and `16` in
  `Enumerative/FubiniMod.lean`.  Splitting the recurrence row at `j = 1` and
  evaluating the two binomial row sums `∑_j C(N,j) 2^j = 3^N ≡ 0 (mod 3)` and
  `∑_j C(N,j) = 2^N` collapses the step to `f (n+1) ≡ 2 - 2·2^{n+1}`, which is
  `2^{n+1} - 1` because `3 ≡ 0`.  Since `2 ≡ -1 (mod 3)`, the closed form gives
  `f m ≡ 0 (mod 3)` for even `m` and `f m ≡ 1 (mod 3)` for odd `m`.

Muljadi's claim follows.  Let `p = f n` be prime with `3 < p`.

* `n = 0` is impossible: `f 0 = 1` is not `> 3`.
* `n` even with `2 ≤ n` is impossible: `3 ∣ p` and `p` prime force `p = 3`,
  contradicting `3 < p`.
* `n` odd gives `p ≡ 1 (mod 4)`, i.e. `p = 4m + 1`.

The qualifier "greater than 3" is exactly what excludes `f 2 = 3`, the one
prime term of the sequence that is `≡ 3 (mod 4)`; the sharpness `example`
below records this.  The primes `13 = f 3`, `541 = f 5`, `47293 = f 7` that
Muljadi lists are certified prime and `≡ 1 (mod 4)` below.

## Attribution

The mod-3 pattern `1, 1, 0, 1, 0, 1, 0, …` is not new: it is the `k = 3`
instance of the eventual periodicity of `A000670` modulo `k` with period
dividing `φ(k)` (B. Poonen, *Periodicity of a combinatorial sequence*,
Fibonacci Quarterly 26 (1988), 70–76; conjectured on the OEIS page by Peter
Bala, Jul 08 2022; formalized in `Enumerative/FubiniMod.lean`).  The A000670
FORMULA section also records the direct statement: "For odd prime p and n >= 1,
a((p-1)*n) = 0 (mod p). - Peter Bala, Sep 18 2013" — at p = 3 this is
`three_dvd_fubini_of_even`.  Equivalently it follows from
`f n = ∑_k k! · S(n,k)` by discarding the `k ≥ 3` terms.  No OEIS comment on
A000670 records the reduction of Muljadi's observation to the mod-3/mod-4
pair; that reduction is the only content this file adds.

## Deviations from the brief

* **No `sorry`.**  The brief budgeted one intended `sorry` for the Muljadi
  claim.  The claim is provable in roughly a page, so it is proved here.  The
  archived-conjecture shape is not available without deliberately hiding a
  finished proof.
* `Proofs/Enumerative.lean` is *not* edited by this file's lane; the module
  must be added there (`import Enumerative.FubiniPrimes`) to enter the
  `Enumerative` default target.

No `native_decide` is used; every ground value is kernel-checked through the
equation lemma `A051293.fubini_succ_eq_sum_range`.
-/

set_option autoImplicit false

open Finset

namespace A000670

open A051293

/-! ## Ground values beyond `Enumerative/Fubini.lean`

`Enumerative/Fubini.lean` stops at `fubini 5 = 541`; Muljadi's third listed
prime is `fubini 7 = 47293`, so two more kernel-checked values are needed. -/

/-- `fubini 6 = 4683` (OEIS A000670). -/
private lemma fubini_six : fubini 6 = 4683 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, fubini_succ_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fubini_zero, fubini_one,
    fubini_two, fubini_three, fubini_four, fubini_five]
  decide

/-- `fubini 7 = 47293` (OEIS A000670). -/
private lemma fubini_seven : fubini 7 = 47293 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, fubini_succ_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fubini_zero, fubini_one,
    fubini_two, fubini_three, fubini_four, fubini_five, fubini_six]
  decide

/-- Ground check against the live OEIS A000670 terms. -/
example : (fubini 0, fubini 1, fubini 2, fubini 3, fubini 4, fubini 5, fubini 6, fubini 7)
    = (1, 1, 3, 13, 75, 541, 4683, 47293) := by
  rw [fubini_zero, fubini_one, fubini_two, fubini_three, fubini_four, fubini_five,
    fubini_six, fubini_seven]

/-! ## The Fubini numbers modulo 3 -/

/-- The `2`-weighted binomial row sum `∑_{j ≤ N} C(N,j) · 2^j = 3^N` vanishes
in `ZMod 3` as soon as `1 ≤ N`. -/
private lemma choose_two_pow_row_sum {N : ℕ} (hN : 1 ≤ N) :
    ∑ j ∈ Finset.range (N + 1), (N.choose j : ZMod 3) * (2 : ZMod 3) ^ j = 0 := by
  have hadd := add_pow (2 : ZMod 3) 1 N
  simp only [one_pow, mul_one] at hadd
  have h0 : (2 : ZMod 3) + 1 = 0 := by decide
  rw [h0, zero_pow (by omega : N ≠ 0)] at hadd
  calc ∑ j ∈ Finset.range (N + 1), (N.choose j : ZMod 3) * (2 : ZMod 3) ^ j
      = ∑ j ∈ Finset.range (N + 1), (2 : ZMod 3) ^ j * (N.choose j : ZMod 3) :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = 0 := hadd.symm

/-- **The Fubini numbers modulo 3**: `(fubini m : ZMod 3) = 2 ^ m - 1` for
`1 ≤ m`, i.e. the residues run `1, 0, 1, 0, …` from `m = 1` on.

Strong induction on the recurrence `fubini (n+1) = ∑_{j ≤ n} C(n+1,j)·fubini j`.
Split the row at `j = 1`: the boundary term is `C(n+1,0)·fubini 0 = 1`, the tail
is rewritten by the induction hypothesis into `∑ C(n+1,j)·(2^j - 1)`, and the
two tail row sums evaluate to `-1 - 2^{n+1}` (weighted) and `2^{n+1} - 2`
(plain).  The total is `2 - 2·2^{n+1}`, which equals `2^{n+1} - 1` because
`3 = 0` in `ZMod 3`. -/
private lemma fubini_zmod3 : ∀ m : ℕ, 1 ≤ m → (fubini m : ZMod 3) = (2 : ZMod 3) ^ m - 1 := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · -- base case `m = 1`: `fubini 1 = 1 = 2^1 - 1` in `ZMod 3`
      have hm1 : m = 1 := by omega
      subst hm1
      rw [fubini_one]
      decide
    · -- step case `m = n + 1` with `1 ≤ n`
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hn1 : 1 ≤ n := by omega
      -- the recurrence, cast into `ZMod 3`
      have hrec : (fubini (n + 1) : ZMod 3)
          = ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 3) * (fubini j : ZMod 3) := by
        rw [fubini_succ_eq_sum_range, Nat.cast_sum]
        exact Finset.sum_congr rfl fun j _ => Nat.cast_mul _ _
      -- split the row at `j = 1`
      have hsplit : ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 3) * (fubini j : ZMod 3)
          = (∑ j ∈ Finset.range 1, ((n + 1).choose j : ZMod 3) * (fubini j : ZMod 3))
            + ∑ j ∈ Finset.Ico 1 (n + 1), ((n + 1).choose j : ZMod 3) * (fubini j : ZMod 3) :=
        (Finset.sum_range_add_sum_Ico _ (by omega)).symm
      -- boundary `j = 0` with `fubini 0 = 1`
      have hbase : ∑ j ∈ Finset.range 1, ((n + 1).choose j : ZMod 3) * (fubini j : ZMod 3)
          = 1 := by
        simp only [Finset.sum_range_one, Nat.choose_zero_right, fubini_zero, Nat.cast_one,
          mul_one]
      -- rewrite the tail by the induction hypothesis
      have hIH : ∑ j ∈ Finset.Ico 1 (n + 1), ((n + 1).choose j : ZMod 3) * (fubini j : ZMod 3)
          = ∑ j ∈ Finset.Ico 1 (n + 1),
              ((n + 1).choose j : ZMod 3) * ((2 : ZMod 3) ^ j - 1) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨hj1, hjn⟩ := Finset.mem_Ico.mp hj
        rw [ih j hjn hj1]
      -- expand the pattern sum into the two tail row sums
      have hexpand : ∑ j ∈ Finset.Ico 1 (n + 1),
            ((n + 1).choose j : ZMod 3) * ((2 : ZMod 3) ^ j - 1)
          = (∑ j ∈ Finset.Ico 1 (n + 1), ((n + 1).choose j : ZMod 3) * (2 : ZMod 3) ^ j)
            - ∑ j ∈ Finset.Ico 1 (n + 1), ((n + 1).choose j : ZMod 3) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      have echoose : ((n + 1).choose (n + 1) : ZMod 3) = 1 := by
        rw [Nat.choose_self, Nat.cast_one]
      -- tail of the `2`-weighted row sum
      have hwt : ∑ j ∈ Finset.Ico 1 (n + 1), ((n + 1).choose j : ZMod 3) * (2 : ZMod 3) ^ j
          = -1 - (2 : ZMod 3) ^ (n + 1) := by
        have e1 : (∑ j ∈ Finset.range 1, ((n + 1).choose j : ZMod 3) * (2 : ZMod 3) ^ j)
            + ∑ j ∈ Finset.Ico 1 (n + 1), ((n + 1).choose j : ZMod 3) * (2 : ZMod 3) ^ j
            = ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 3) * (2 : ZMod 3) ^ j :=
          Finset.sum_range_add_sum_Ico _ (by omega)
        have e2 : ∑ j ∈ Finset.range (n + 1 + 1), ((n + 1).choose j : ZMod 3) * (2 : ZMod 3) ^ j
            = (∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 3) * (2 : ZMod 3) ^ j)
              + ((n + 1).choose (n + 1) : ZMod 3) * (2 : ZMod 3) ^ (n + 1) :=
          Finset.sum_range_succ _ _
        have e3 : ∑ j ∈ Finset.range 1, ((n + 1).choose j : ZMod 3) * (2 : ZMod 3) ^ j = 1 := by
          simp only [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, pow_zero,
            mul_one]
        have e4 := choose_two_pow_row_sum (N := n + 1) (by omega)
        linear_combination e1 - e2 + e4 - e3 - (2 : ZMod 3) ^ (n + 1) * echoose
      -- tail of the plain row sum
      have hpl : ∑ j ∈ Finset.Ico 1 (n + 1), ((n + 1).choose j : ZMod 3)
          = (2 : ZMod 3) ^ (n + 1) - 2 := by
        have e1 : (∑ j ∈ Finset.range 1, ((n + 1).choose j : ZMod 3))
            + ∑ j ∈ Finset.Ico 1 (n + 1), ((n + 1).choose j : ZMod 3)
            = ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 3) :=
          Finset.sum_range_add_sum_Ico _ (by omega)
        have e2 : ∑ j ∈ Finset.range (n + 1 + 1), ((n + 1).choose j : ZMod 3)
            = (∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 3))
              + ((n + 1).choose (n + 1) : ZMod 3) :=
          Finset.sum_range_succ _ _
        have e3 : ∑ j ∈ Finset.range 1, ((n + 1).choose j : ZMod 3) = 1 := by
          simp only [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one]
        have e4 : ∑ j ∈ Finset.range (n + 1 + 1), ((n + 1).choose j : ZMod 3)
            = (2 : ZMod 3) ^ (n + 1) := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring
        linear_combination e1 - e2 + e4 - e3 - echoose
      -- collapse the recurrence to a closed expression
      have hmain : (fubini (n + 1) : ZMod 3) = 2 - 2 * (2 : ZMod 3) ^ (n + 1) := by
        linear_combination hrec + hsplit + hbase + hIH + hexpand + hwt - hpl
      have h30 : (3 : ZMod 3) = 0 := by decide
      rw [hmain]
      linear_combination (1 - (2 : ZMod 3) ^ (n + 1)) * h30

/-- Every Fubini number of even index `2 ≤ n` is divisible by `3`.

`2 = -1` in `ZMod 3`, so the closed form `(fubini n : ZMod 3) = 2 ^ n - 1` of
`fubini_zmod3` reads `(-1)^n - 1`, which vanishes for even `n`. -/
theorem three_dvd_fubini_of_even (n : ℕ) (hn : 2 ≤ n) (hev : Even n) : 3 ∣ fubini n := by
  refine (ZMod.natCast_eq_zero_iff (fubini n) 3).mp ?_
  rw [fubini_zmod3 n (by omega)]
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [h2, hev.neg_one_pow, sub_self]

/-! ## The Fubini numbers of odd index, modulo 4 -/

/-- `fubini (2t+1) % 4 = 1`, by induction on `t` along the mod-4 period-2
congruence `A000670.fubini_add_two_modEq_four`, based at `fubini 1 = 1`. -/
private lemma fubini_two_mul_add_one_mod_four (t : ℕ) : fubini (2 * t + 1) % 4 = 1 := by
  induction t with
  | zero =>
    have h1 : fubini (2 * 0 + 1) = 1 := fubini_one
    rw [h1]
  | succ t iht =>
    have hstep : fubini (2 * t + 1 + 2) % 4 = fubini (2 * t + 1) % 4 :=
      fubini_add_two_modEq_four (2 * t + 1) (by omega)
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 2 by ring, hstep, iht]

/-- Every Fubini number of odd index is `≡ 1 (mod 4)`. -/
theorem fubini_mod_four_eq_one_of_odd (n : ℕ) (hn : Odd n) : fubini n % 4 = 1 := by
  obtain ⟨t, rfl⟩ := hn
  exact fubini_two_mul_add_one_mod_four t

/-! ## Muljadi's observation -/

/-- **Muljadi's observation** (OEIS A000670 comments, Paul Muljadi, Jan 28
2011), index form: if `fubini n` is a prime greater than `3`, then
`fubini n ≡ 1 (mod 4)`.

Even indices are eliminated rather than computed: `fubini 0 = 1` is not `> 3`,
and for even `n ≥ 2` the term is divisible by `3`
(`three_dvd_fubini_of_even`), hence prime only if it *equals* `3`.  Odd indices
are handled by `fubini_mod_four_eq_one_of_odd`. -/
theorem fubini_mod_four_eq_one_of_prime (n : ℕ) (hp : (fubini n).Prime)
    (hgt : 3 < fubini n) : fubini n % 4 = 1 := by
  rcases Nat.even_or_odd n with hev | hodd
  · exfalso
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [fubini_zero] at hgt
      omega
    · have hn2 : 2 ≤ n := by
        obtain ⟨r, hr⟩ := hev
        omega
      have hdvd : (3 : ℕ) ∣ fubini n := three_dvd_fubini_of_even n hn2 hev
      have heq : (3 : ℕ) = fubini n :=
        (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
      omega
  · exact fubini_mod_four_eq_one_of_odd n hodd

/-- **Muljadi's observation**, in the shape he wrote it: every prime `p > 3`
that occurs in A000670 is "of the form `4n+1`". -/
theorem muljadi_fubini_prime_four_mul_add_one {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (hmem : ∃ n : ℕ, fubini n = p) : ∃ m : ℕ, p = 4 * m + 1 := by
  obtain ⟨n, rfl⟩ := hmem
  refine ⟨fubini n / 4, ?_⟩
  have hmod : fubini n % 4 = 1 := fubini_mod_four_eq_one_of_prime n hp hgt
  omega

/-! ## Ground certificates for the three primes Muljadi lists -/

/-- `fubini 3 = 13` is prime. -/
theorem fubini_three_prime : Nat.Prime (fubini 3) := by
  rw [fubini_three]
  norm_num

/-- `fubini 5 = 541` is prime. -/
theorem fubini_five_prime : Nat.Prime (fubini 5) := by
  rw [fubini_five]
  norm_num

/-- `fubini 7 = 47293` is prime. -/
theorem fubini_seven_prime : Nat.Prime (fubini 7) := by
  rw [fubini_seven]
  norm_num

-- the three listed primes, in Muljadi's `4n+1` shape
example : fubini 3 = 4 * 3 + 1 := fubini_three
example : fubini 5 = 4 * 135 + 1 := fubini_five
example : fubini 7 = 4 * 11823 + 1 := fubini_seven

-- and via the theorem itself, at `p = 13`
example : ∃ m : ℕ, (13 : ℕ) = 4 * m + 1 :=
  muljadi_fubini_prime_four_mul_add_one (by norm_num) (by norm_num) ⟨3, fubini_three⟩

-- and at `p = 541`
example : ∃ m : ℕ, (541 : ℕ) = 4 * m + 1 :=
  muljadi_fubini_prime_four_mul_add_one (by norm_num) (by norm_num) ⟨5, fubini_five⟩

/-! ## Satisfiability and sharpness

Every hypothesis of `muljadi_fubini_prime_four_mul_add_one` is instantiated
jointly at `p = 13` below, so the theorem is not vacuous; the `3 < p`
hypothesis is then shown to be load-bearing rather than decorative. -/

-- joint satisfiability of all three hypotheses at `p = 13 = fubini 3`
example : Nat.Prime 13 ∧ 3 < 13 ∧ ∃ n : ℕ, fubini n = 13 :=
  ⟨by norm_num, by norm_num, ⟨3, fubini_three⟩⟩

-- joint satisfiability of the index-form hypotheses at `n = 5`
example : (fubini 5).Prime ∧ 3 < fubini 5 :=
  ⟨fubini_five_prime, by rw [fubini_five]; norm_num⟩

-- sharpness: `fubini 2 = 3` is a prime term of A000670 with `3 % 4 = 3`, so
-- Muljadi's "greater than 3" qualifier cannot be dropped
example : (fubini 2).Prime ∧ fubini 2 % 4 = 3 := by
  rw [fubini_two]
  exact ⟨Nat.prime_three, rfl⟩

-- nonvacuity of `three_dvd_fubini_of_even`, at `n = 4` and `n = 6`
example : 3 ∣ fubini 4 ∧ 3 ∣ fubini 6 :=
  ⟨three_dvd_fubini_of_even 4 (by norm_num) ⟨2, rfl⟩,
   three_dvd_fubini_of_even 6 (by norm_num) ⟨3, rfl⟩⟩

-- the same two divisibilities, read off the ground values `75 = 3·25` and
-- `4683 = 3·1561`
example : fubini 4 = 3 * 25 ∧ fubini 6 = 3 * 1561 := ⟨fubini_four, fubini_six⟩

-- consequently the even-index terms beyond `fubini 2` are composite
example : ¬ (fubini 4).Prime := by
  rw [fubini_four]
  norm_num

example : ¬ (fubini 6).Prime := by
  rw [fubini_six]
  norm_num

-- nonvacuity of `fubini_mod_four_eq_one_of_odd`, at `n = 7`
example : fubini 7 % 4 = 1 := fubini_mod_four_eq_one_of_odd 7 ⟨3, rfl⟩

-- residues mod 3 from `n = 0`: `1, 1, 0, 1, 0, 1, 0, 1` (OEIS terms
-- `1, 1, 3, 13, 75, 541, 4683, 47293`)
example : (fubini 0 % 3, fubini 1 % 3, fubini 2 % 3, fubini 3 % 3,
    fubini 4 % 3, fubini 5 % 3, fubini 6 % 3, fubini 7 % 3) = (1, 1, 0, 1, 0, 1, 0, 1) := by
  rw [fubini_zero, fubini_one, fubini_two, fubini_three, fubini_four, fubini_five,
    fubini_six, fubini_seven]

-- residues mod 4 from `n = 0`: `1, 1, 3, 1, 3, 1, 3, 1`
example : (fubini 0 % 4, fubini 1 % 4, fubini 2 % 4, fubini 3 % 4,
    fubini 4 % 4, fubini 5 % 4, fubini 6 % 4, fubini 7 % 4) = (1, 1, 3, 1, 3, 1, 3, 1) := by
  rw [fubini_zero, fubini_one, fubini_two, fubini_three, fubini_four, fubini_five,
    fubini_six, fubini_seven]

/-! ## Signature audit -/

#check @three_dvd_fubini_of_even
#check @fubini_mod_four_eq_one_of_odd
#check @fubini_mod_four_eq_one_of_prime
#check @muljadi_fubini_prime_four_mul_add_one
#check @fubini_three_prime
#check @fubini_five_prime
#check @fubini_seven_prime

/-! ## Axiom audit -/

#print axioms fubini_zmod3
#print axioms three_dvd_fubini_of_even
#print axioms fubini_mod_four_eq_one_of_odd
#print axioms fubini_mod_four_eq_one_of_prime
#print axioms muljadi_fubini_prime_four_mul_add_one
#print axioms fubini_three_prime
#print axioms fubini_five_prime
#print axioms fubini_seven_prime

end A000670
