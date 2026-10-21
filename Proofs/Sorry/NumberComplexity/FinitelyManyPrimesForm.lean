/-
# Finitely many primes of the form `∑_{k ≤ n} (1 + d k)!` when `d + 2` is prime

## Source

arXiv:2609.28805, Tomoki Mihara, "Parallel Searching Method for Verifying
Finiteness of Prime Numbers Presented as Specific Linear Combinations of
Factorials".  Retrieved 2026-10-21.

* Theorem 1.1 (`\label{main}`), verbatim: "There are only finitely many prime
  numbers of the form `\sum_{k=0}^{n} (kd+1)!` with
  `(d,n) ∈ (ℕ_{≤ 25} \ {0,8,18,20,23,25}) × ℕ`."
* Proposition 2.1 (`\label{finiteness}`): if some prime `p` satisfies
  `∑_{k=0}^{p-1} c_k k! ≡ 0 (mod p)`, then only finitely many numbers
  `∑_{k=0}^{n} c_k k!` are prime.
* Table 1 lists the least such `p` for `c_k = [k ≡ 1 (mod d)]`, `d ≤ 25`; the
  entries `d = 1, 3, 5, 9, 11, 15, 17, 21` are exactly `p = d + 2`.

The paper proves Theorem 1.1 case by case from computer-found primes `p`.

## Claim formalized here (uniform family, not stated in the paper)

For every `d ≥ 1` with `d + 2` prime, the set
`{n | ∑_{k=0}^{n} (1 + d k)! is prime}` is finite; in fact it is contained in
`{1}` (and equals `{1}` exactly when `d = 1`).

Proof: `p = d + 2` works uniformly.  The terms `k = 0, 1` give
`1 + (d + 1)! = 1 + (p - 1)! ≡ 0 (mod p)` by Wilson's theorem, and every later
term has `1 + d k ≥ 1 + 2 d ≥ p`, so `p ∣ (1 + d k)!`.  Hence `p` divides every
partial sum with `n ≥ 1`; for `n ≥ 2` the sum exceeds `p`, and the sum at
`n = 0` is `1`.  This covers the paper's cases `d = 1, 3, 5, 9, 11, 15, 17, 21`
and every further `d` with `d + 2` prime.  The hypothesis `d ≥ 1` is needed: at
`d = 0` the sum is `n + 1`.

Sharp forms: the set is `{1}` for `d = 1` and empty for `d ≥ 2`.

## Also formalized

* Proposition 2.1 specialized to these sums (`primes_subset_of_dvd`,
  `finite_primes_of_dvd`), with a verified residue loop for certificates.
* Theorem 1.1 for every `d` in the paper's range except `d = 19`
  (`thm_1_1_except_19`): Table 1 certificates `p = 107, 6323, 61, 19, 4093, 257,
  23, 2549, 32261, 61, 1087` for `d = 2, 4, 6, 7, 10, 12, 13, 14, 16, 22, 24`,
  checked by `decide` (kernel `decide` for the residue loop), and the uniform
  Wilson family for `d = 1, 3, 5, 9, 11, 15, 17, 21`.  The case `d = 19`
  (`p = 3977273`) is not checked: one kernel run of 20000 loop steps exceeded
  a 14 GB memory cap.

Status: everything stated here is proved (no `sorry`).  The paper proves
Theorem 1.1 itself; it does not state the uniform `d + 2` family, which does
not by itself establish novelty.
-/
import Mathlib

set_option autoImplicit false
-- Synchronous elaboration: the kernel `decide` certificates below otherwise
-- spawn concurrent elaboration threads that fail under a memory cap.
set_option Elab.async false

namespace NumberComplexity.FinitelyManyPrimesForm

open Nat

/-- The paper's sum `∑_{k=0}^{n} (1 + d k)!` (Theorem 1.1 of arXiv:2609.28805,
written there as `∑_{k=0}^{n} (kd+1)!`). -/
def factorialProgressionSum (d n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (1 + d * k)!

/-! Ground truth: `d = 1`: `1! = 1`, `1! + 2! = 3`, `1! + 2! + 3! = 9`;
`d = 2`: `1! + 3! + 5! = 127`; `d = 3`: `1! + 4! = 25 = 5²`. -/
example : factorialProgressionSum 1 0 = 1 := by decide
example : factorialProgressionSum 1 1 = 3 := by decide
example : factorialProgressionSum 1 2 = 9 := by decide
example : factorialProgressionSum 2 2 = 127 := by decide
example : factorialProgressionSum 3 1 = 25 := by decide

/-- Recursion: the partial sum at `n + 1` adds the term `(1 + d (n + 1))!`. -/
theorem factorialProgressionSum_succ (d n : ℕ) :
    factorialProgressionSum d (n + 1) =
      factorialProgressionSum d n + (1 + d * (n + 1))! := by
  unfold factorialProgressionSum
  rw [Finset.sum_range_succ]

/-- Wilson step: if `d + 2` is prime then `d + 2 ∣ 1! + (1 + d)!`. -/
theorem dvd_factorialProgressionSum_one {d : ℕ} (hp : (d + 2).Prime) :
    d + 2 ∣ factorialProgressionSum d 1 := by
  haveI : Fact (d + 2).Prime := ⟨hp⟩
  have hsum : factorialProgressionSum d 1 = 1 + (d + 1)! := by
    simp [factorialProgressionSum, Finset.sum_range_succ, add_comm]
  have hwilson : (((d + 1)! : ℕ) : ZMod (d + 2)) = -1 := by
    simpa using ZMod.wilsons_lemma (p := d + 2)
  rw [← ZMod.natCast_eq_zero_iff, hsum]
  push_cast
  rw [hwilson]
  ring

/-- If `d ≥ 1` and `d + 2` is prime, then `d + 2` divides every partial sum
with `n ≥ 1`. -/
theorem dvd_factorialProgressionSum {d : ℕ} (hd : 1 ≤ d) (hp : (d + 2).Prime) :
    ∀ n : ℕ, 1 ≤ n → d + 2 ∣ factorialProgressionSum d n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact dvd_factorialProgressionSum_one hp
  | succ m hm ih =>
    rw [factorialProgressionSum_succ]
    have hle : d + 2 ≤ 1 + d * (m + 1) := by nlinarith
    exact dvd_add ih (Nat.dvd_factorial (by omega) hle)

/-- For `n ≥ 2` the partial sum strictly exceeds `d + 2` (when `d ≥ 1`). -/
theorem lt_factorialProgressionSum {d : ℕ} (hd : 1 ≤ d) :
    ∀ n : ℕ, 2 ≤ n → d + 2 < factorialProgressionSum d n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have h1 : factorialProgressionSum d 2 = 1 + (1 + d)! + (1 + d * 2)! := by
      simp [factorialProgressionSum, Finset.sum_range_succ]
    have h2 : 1 + d * 2 ≤ (1 + d * 2)! := Nat.self_le_factorial _
    omega
  | succ m _ ih =>
    rw [factorialProgressionSum_succ]
    omega

/-- **Uniform Wilson family.** If `d ≥ 1` and `d + 2` is prime, then
`∑_{k=0}^{n} (1 + d k)!` is prime only for `n = 1`. -/
theorem primes_subset_singleton_one {d : ℕ} (hd : 1 ≤ d) (hp : (d + 2).Prime) :
    {n : ℕ | (factorialProgressionSum d n).Prime} ⊆ {1} := by
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn
  simp only [Set.mem_singleton_iff]
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · exact absurd hn Nat.not_prime_one
    · rfl
  · have hdvd := dvd_factorialProgressionSum hd hp n (by omega)
    have heq := (Nat.prime_dvd_prime_iff_eq hp hn).mp hdvd
    have hlt := lt_factorialProgressionSum hd n h
    omega

/-- **Finiteness (uniform extension of Theorem 1.1 of arXiv:2609.28805).** For
every `d ≥ 1` with `d + 2` prime, there are only finitely many `n` such that
`∑_{k=0}^{n} (1 + d k)!` is prime. -/
theorem finite_primes {d : ℕ} (hd : 1 ≤ d) (hp : (d + 2).Prime) :
    {n : ℕ | (factorialProgressionSum d n).Prime}.Finite :=
  (Set.finite_singleton 1).subset (primes_subset_singleton_one hd hp)

/-- Sharp form for `d ≥ 2`: if `d + 2` is prime, no partial sum
`∑_{k=0}^{n} (1 + d k)!` is prime. -/
theorem primes_eq_empty_of_two_le {d : ℕ} (hd : 2 ≤ d) (hp : (d + 2).Prime) :
    {n : ℕ | (factorialProgressionSum d n).Prime} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun n hn => ?_
  have h1 : n = 1 := primes_subset_singleton_one (by omega) hp hn
  subst h1
  simp only [Set.mem_ofPred_eq] at hn
  have heq := (Nat.prime_dvd_prime_iff_eq hp hn).mp (dvd_factorialProgressionSum_one hp)
  have hsum : factorialProgressionSum d 1 = 1 + (d + 1)! := by
    simp [factorialProgressionSum, Finset.sum_range_succ, add_comm]
  have hfac : (d + 1)! = (d + 1) * d ! := Nat.factorial_succ d
  have hdfac : d ≤ d ! := Nat.self_le_factorial d
  have hmul : (d + 1) * 2 ≤ (d + 1) * d ! := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Sharp form for `d = 1`: `∑_{k=0}^{n} (1 + k)!` is prime exactly for `n = 1`
(the value `1! + 2! = 3`). -/
theorem primes_eq_singleton_of_one :
    {n : ℕ | (factorialProgressionSum 1 n).Prime} = {1} := by
  refine (primes_subset_singleton_one le_rfl (by norm_num)).antisymm ?_
  intro n hn
  simp only [Set.mem_singleton_iff] at hn
  subst hn
  simp only [Set.mem_ofPred_eq]
  decide

/-! Non-vacuity: the hypotheses of `finite_primes` hold at `d = 1, 3, 5`, and
`d = 1` attains the bound `{1}`. -/
example : 1 ≤ 1 ∧ (1 + 2).Prime := ⟨le_rfl, by norm_num⟩
example : 1 ≤ 3 ∧ (3 + 2).Prime := ⟨by norm_num, by norm_num⟩
example : 1 ≤ 5 ∧ (5 + 2).Prime := ⟨by norm_num, by norm_num⟩
example : (factorialProgressionSum 1 1).Prime := by decide

/-! ## The paper's finiteness criterion (Proposition 2.1, specialized)

If a prime `p` divides the partial sum at `m`, and every later term
`(1 + d k)!` with `k > m` already contains the factor `p`, then `p` divides
every later partial sum, so those sums are prime only if they equal `p`. -/

/-- Each partial sum is at least `n + 1`, since every term is at least `1`. -/
theorem succ_le_factorialProgressionSum (d : ℕ) :
    ∀ n : ℕ, n + 1 ≤ factorialProgressionSum d n := by
  intro n
  induction n with
  | zero => simp [factorialProgressionSum]
  | succ n ih =>
    rw [factorialProgressionSum_succ]
    have hpos : 0 < (1 + d * (n + 1))! := Nat.factorial_pos _
    omega

/-- Propagation: if `0 < p`, `p ≤ 1 + d (m + 1)` and `p` divides the partial
sum at `m`, then `p` divides the partial sum at every `n ≥ m`. -/
theorem dvd_factorialProgressionSum_of_le {d p m : ℕ} (hp : 0 < p)
    (hm : p ≤ 1 + d * (m + 1)) (hdvd : p ∣ factorialProgressionSum d m) :
    ∀ n : ℕ, m ≤ n → p ∣ factorialProgressionSum d n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hdvd
  | succ k hk ih =>
    rw [factorialProgressionSum_succ]
    have hmono : d * (m + 1) ≤ d * (k + 1) := Nat.mul_le_mul_left d (by omega)
    exact dvd_add ih (Nat.dvd_factorial hp (by omega))

/-- **Proposition 2.1 of arXiv:2609.28805, for the sums `∑_{k ≤ n} (1 + d k)!`.**
If a prime `p` satisfies `p ≤ 1 + d (m + 1)` and `p ∣ ∑_{k ≤ m} (1 + d k)!`,
then `∑_{k ≤ n} (1 + d k)!` is prime only if `n ≤ m` or the sum equals `p`. -/
theorem primes_subset_of_dvd {d p m : ℕ} (hp : p.Prime)
    (hm : p ≤ 1 + d * (m + 1)) (hdvd : p ∣ factorialProgressionSum d m) :
    {n : ℕ | (factorialProgressionSum d n).Prime} ⊆
      {n : ℕ | n ≤ m ∨ factorialProgressionSum d n = p} := by
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  rcases Nat.lt_or_ge m n with h | h
  · have hdvdn := dvd_factorialProgressionSum_of_le hp.pos hm hdvd n h.le
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp hn).mp hdvdn).symm
  · exact Or.inl h

/-- Finiteness consequence of `primes_subset_of_dvd`: under its hypotheses only
finitely many `n` make `∑_{k ≤ n} (1 + d k)!` prime. -/
theorem finite_primes_of_dvd {d p m : ℕ} (hp : p.Prime)
    (hm : p ≤ 1 + d * (m + 1)) (hdvd : p ∣ factorialProgressionSum d m) :
    {n : ℕ | (factorialProgressionSum d n).Prime}.Finite := by
  refine (Set.finite_Iic (m + p)).subset ((primes_subset_of_dvd hp hm hdvd).trans ?_)
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn
  simp only [Set.mem_Iic]
  rcases hn with h | h
  · omega
  · have hle := succ_le_factorialProgressionSum d n
    omega

/-! ## A verified residue loop for certificates

`factorialProgressionMod p d n` returns `((1 + d n)! mod p, S_d(n) mod p)`,
computed with residues only; `factorialProgressionMod_eq` proves this. -/

/-- Residue loop: the pair `((1 + d n)! % p, (∑_{k ≤ n} (1 + d k)!) % p)`,
computed by multiplying in the `d` new factors `2 + d n, …, 1 + d (n + 1)`
modulo `p` at each step. -/
def factorialProgressionMod (p d : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1 % p, 1 % p)
  | n + 1 =>
    let r := factorialProgressionMod p d n
    let f := (List.range' (2 + d * n) d).foldl (fun a j => a * j % p) r.1
    (f, (r.2 + f) % p)

/-- Folding the factors `m + 1, …, m + k` into `m! mod p` gives `(m + k)! mod p`. -/
theorem foldl_factorial_mod (p : ℕ) : ∀ k m : ℕ,
    (List.range' (m + 1) k).foldl (fun a j => a * j % p) (m ! % p) = (m + k)! % p := by
  intro k
  induction k with
  | zero => intro m; simp
  | succ k ih =>
    intro m
    rw [List.range'_succ, List.foldl_cons]
    have h : m ! % p * (m + 1) % p = (m + 1)! % p := by
      rw [Nat.factorial_succ, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_comm]
    rw [h, ih (m + 1)]
    ring_nf

/-- Correctness of the residue loop. -/
theorem factorialProgressionMod_eq (p d : ℕ) : ∀ n : ℕ,
    factorialProgressionMod p d n =
      ((1 + d * n)! % p, factorialProgressionSum d n % p) := by
  intro n
  induction n with
  | zero => simp [factorialProgressionMod, factorialProgressionSum]
  | succ n ih =>
    have hf : (List.range' (2 + d * n) d).foldl (fun a j => a * j % p)
        (factorialProgressionMod p d n).1 = (1 + d * (n + 1))! % p := by
      rw [ih]
      have h2 : 2 + d * n = (1 + d * n) + 1 := by ring
      rw [h2, foldl_factorial_mod]
      ring_nf
    simp only [factorialProgressionMod]
    rw [hf, ih, factorialProgressionSum_succ]
    simp only [Prod.mk.injEq, true_and]
    rw [Nat.add_mod (factorialProgressionSum d n)]

/-- A zero residue from the loop certifies divisibility. -/
theorem dvd_of_factorialProgressionMod {p d m : ℕ}
    (h : (factorialProgressionMod p d m).2 = 0) :
    p ∣ factorialProgressionSum d m := by
  rw [factorialProgressionMod_eq] at h
  exact Nat.dvd_of_mod_eq_zero h

/-! Ground truth for the loop: `S_2(2) = 127`, so `127 % 10 = 7`, and
`(1 + 2·2)! = 120`. -/
example : factorialProgressionMod 10 2 2 = (0, 7) := by decide
example : factorialProgressionMod 1000 2 2 = (120, 127) := by decide

/-! ## Theorem 1.1 of arXiv:2609.28805, all cases except `d = 19`

The certificates are the least primes of the paper's Table 1.  For each `d`,
`m` is the largest index with `1 + d m ≤ p - 1`.  The case `d = 19`
(`p = 3977273`, `m = 209330`) is not checked here: a kernel `decide` over
`209330` loop steps exceeds this module's resource budget. -/

/-- `d = 2`: `107 ∣ ∑_{k ≤ 52} (1 + 2k)!`. -/
theorem dvd_d2 : 107 ∣ factorialProgressionSum 2 52 := Nat.dvd_of_mod_eq_zero (by decide)
/-- `d = 6`: `61 ∣ ∑_{k ≤ 9} (1 + 6k)!`. -/
theorem dvd_d6 : 61 ∣ factorialProgressionSum 6 9 := Nat.dvd_of_mod_eq_zero (by decide)
/-- `d = 7`: `19 ∣ ∑_{k ≤ 2} (1 + 7k)!`. -/
theorem dvd_d7 : 19 ∣ factorialProgressionSum 7 2 := Nat.dvd_of_mod_eq_zero (by decide)
/-- `d = 12`: `257 ∣ ∑_{k ≤ 21} (1 + 12k)!`. -/
theorem dvd_d12 : 257 ∣ factorialProgressionSum 12 21 := Nat.dvd_of_mod_eq_zero (by decide)
/-- `d = 13`: `23 ∣ ∑_{k ≤ 1} (1 + 13k)!`. -/
theorem dvd_d13 : 23 ∣ factorialProgressionSum 13 1 := Nat.dvd_of_mod_eq_zero (by decide)
/-- `d = 22`: `61 ∣ ∑_{k ≤ 2} (1 + 22k)!`. -/
theorem dvd_d22 : 61 ∣ factorialProgressionSum 22 2 := Nat.dvd_of_mod_eq_zero (by decide)
/-- `d = 24`: `1087 ∣ ∑_{k ≤ 45} (1 + 24k)!`. -/
theorem dvd_d24 : 1087 ∣ factorialProgressionSum 24 45 :=
  Nat.dvd_of_mod_eq_zero (by decide)
/-- `d = 4`: `6323 ∣ ∑_{k ≤ 1580} (1 + 4k)!` (residue loop, kernel `decide`). -/
theorem dvd_d4 : 6323 ∣ factorialProgressionSum 4 1580 :=
  dvd_of_factorialProgressionMod (by decide +kernel)
/-- `d = 10`: `4093 ∣ ∑_{k ≤ 409} (1 + 10k)!` (residue loop, kernel `decide`). -/
theorem dvd_d10 : 4093 ∣ factorialProgressionSum 10 409 :=
  dvd_of_factorialProgressionMod (by decide +kernel)
/-- `d = 14`: `2549 ∣ ∑_{k ≤ 181} (1 + 14k)!` (residue loop, kernel `decide`). -/
theorem dvd_d14 : 2549 ∣ factorialProgressionSum 14 181 :=
  dvd_of_factorialProgressionMod (by decide +kernel)
/-- `d = 16`: `32261 ∣ ∑_{k ≤ 2016} (1 + 16k)!` (residue loop, kernel `decide`). -/
theorem dvd_d16 : 32261 ∣ factorialProgressionSum 16 2016 :=
  dvd_of_factorialProgressionMod (by decide +kernel)

/-- **Theorem 1.1 of arXiv:2609.28805, except `d = 19`.** For every
`d ∈ {1, …, 25} \ {8, 18, 19, 20, 23, 25}` only finitely many `n` make
`∑_{k=0}^{n} (1 + d k)!` prime.  Odd `d` with `d + 2` prime use the uniform
Wilson family `finite_primes`; the others use the paper's Table 1 primes. -/
theorem thm_1_1_except_19 (d : ℕ) (hd : d ∈ Finset.Icc 1 25 \ {8, 18, 19, 20, 23, 25}) :
    {n : ℕ | (factorialProgressionSum d n).Prime}.Finite := by
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hd
  obtain ⟨⟨hd1, hd25⟩, hdne⟩ := hd
  interval_cases d <;> try exact absurd (by decide) hdne
  · exact finite_primes le_rfl (by norm_num)
  · exact finite_primes_of_dvd (m := 52) (by norm_num) (by norm_num) dvd_d2
  · exact finite_primes (by norm_num) (by norm_num)
  · exact finite_primes_of_dvd (m := 1580) (by norm_num) (by norm_num) dvd_d4
  · exact finite_primes (by norm_num) (by norm_num)
  · exact finite_primes_of_dvd (m := 9) (by norm_num) (by norm_num) dvd_d6
  · exact finite_primes_of_dvd (m := 2) (by norm_num) (by norm_num) dvd_d7
  · exact finite_primes (by norm_num) (by norm_num)
  · exact finite_primes_of_dvd (m := 409) (by norm_num) (by norm_num) dvd_d10
  · exact finite_primes (by norm_num) (by norm_num)
  · exact finite_primes_of_dvd (m := 21) (by norm_num) (by norm_num) dvd_d12
  · exact finite_primes_of_dvd (m := 1) (by norm_num) (by norm_num) dvd_d13
  · exact finite_primes_of_dvd (m := 181) (by norm_num) (by norm_num) dvd_d14
  · exact finite_primes (by norm_num) (by norm_num)
  · exact finite_primes_of_dvd (m := 2016) (by norm_num) (by norm_num) dvd_d16
  · exact finite_primes (by norm_num) (by norm_num)
  · exact finite_primes (by norm_num) (by norm_num)
  · exact finite_primes_of_dvd (m := 2) (by norm_num) (by norm_num) dvd_d22
  · exact finite_primes_of_dvd (m := 45) (by norm_num) (by norm_num) dvd_d24

/-! Non-vacuity of the case set of `thm_1_1_except_19`. -/
example : 2 ∈ Finset.Icc 1 25 \ {8, 18, 19, 20, 23, 25} := by decide

end NumberComplexity.FinitelyManyPrimesForm
