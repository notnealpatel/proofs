/-
  Erdős Problem #1058 — prime divisors of n! + 1.
  Status: proved (Luca 2001).  Tier A proof target.

  Verbatim statement (`goof erdos fetch 1058`, pulled 2026-08-05):

    "Let $2=p_1<p_2<\cdots$ be the sequence of prime numbers. Are there
    only finitely many $n$ such that $n\in [p_{k-1},p_k)$ and the only
    primes dividing $n!+1$ are $p_{k}$ and $p_{k+1}$?"

  DB remarks: conjecture of Erdős–Stewart (Guy A2); only known cases
  n = 1, 2, 3, 4, 5.  Luca [Lu01] proved these are the only solutions.
  Comment thread (Tao, Sep 2025): the indexing "p_k and p_{k+1}" is the
  corrected form (the original "p_{k-1} and p_k" was a typo — n!+1 is
  never divisible by a prime ≤ n).

  Formalization choice: since n ∈ [p_{k-1}, p_k) determines k, the pair
  (p_k, p_{k+1}) is exactly (the least prime > n, the next prime after
  that).  This removes all index bookkeeping.

  Mathlib inventory (leandoc 2026-08-05): `Nat.factorial`, `Nat.Prime`,
  `Nat.exists_infinite_primes`, `Nat.primeFactors`, `Nat.minFac`;
  `Nat.nth Nat.Prime` available if the indexed form is preferred.
  Certificate-then-tail pattern from
  `Proofs/Erdos/Covering/ErdosMinus2k.lean`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1058

/-- The least prime strictly greater than `n`.  Total: the set is
    nonempty by Euclid (`Nat.exists_infinite_primes`), so `sInf` is
    attained and never the junk value. -/
noncomputable def nextPrime (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ n < p}

private theorem nextPrime_eq_of_least (n p : ℕ) (hp : p.Prime) (hn : n < p)
    (hsmall : ∀ q : Fin p, ¬ (q.val.Prime ∧ n < q.val)) :
    nextPrime n = p := by
  apply IsLeast.csInf_eq
  refine ⟨⟨hp, hn⟩, ?_⟩
  intro q hq
  by_contra h
  exact hsmall ⟨q, Nat.lt_of_not_ge h⟩ hq

private theorem nextPrime_one : nextPrime 1 = 2 :=
  nextPrime_eq_of_least 1 2 (by decide) (by decide) (by decide)

private theorem nextPrime_two : nextPrime 2 = 3 :=
  nextPrime_eq_of_least 2 3 (by decide) (by decide) (by decide)

private theorem nextPrime_three : nextPrime 3 = 5 :=
  nextPrime_eq_of_least 3 5 (by decide) (by decide) (by decide)

private theorem nextPrime_four : nextPrime 4 = 5 :=
  nextPrime_eq_of_least 4 5 (by decide) (by decide) (by decide)

private theorem nextPrime_five : nextPrime 5 = 7 :=
  nextPrime_eq_of_least 5 7 (by decide) (by decide) (by decide)

private theorem nextPrime_six : nextPrime 6 = 7 :=
  nextPrime_eq_of_least 6 7 (by decide) (by decide) (by decide)

private theorem nextPrime_seven : nextPrime 7 = 11 :=
  nextPrime_eq_of_least 7 11 (by decide) (by decide) (by decide)

private theorem nextPrime_thirteen : nextPrime 13 = 17 :=
  nextPrime_eq_of_least 13 17 (by decide) (by decide) (by decide)

/-- The least primes above 1, 4, 5, and 13 are 2, 5, 7, and 17. -/
theorem nextPrime_sanity : nextPrime 1 = 2 ∧ nextPrime 4 = 5 ∧
    nextPrime 5 = 7 ∧ nextPrime 13 = 17 :=
  ⟨nextPrime_one, nextPrime_four, nextPrime_five, nextPrime_thirteen⟩

/-- Ground-truth checks for `nextPrime`.
    -- PROVABLE (via `Nat.sInf_eq` characterization + decide). -/
example : nextPrime 1 = 2 ∧ nextPrime 4 = 5 ∧ nextPrime 5 = 7 ∧
    nextPrime 13 = 17 := by
  exact nextPrime_sanity

/-- `ErdosStewart n`: every prime divisor of `n! + 1` is one of the two
    smallest primes exceeding `n`.  For `n ∈ [p_{k-1}, p_k)` these two
    primes are precisely `p_k` and `p_{k+1}`, so this is the property in
    the problem statement with the interval bookkeeping absorbed. -/
def ErdosStewart (n : ℕ) : Prop :=
  ∀ q ∈ (n.factorial + 1).primeFactors,
    q = nextPrime n ∨ q = nextPrime (nextPrime n)

/-- The five known positive cases satisfy the Erdős–Stewart property. -/
theorem erdosStewart_sanity : ErdosStewart 1 ∧ ErdosStewart 2 ∧
    ErdosStewart 3 ∧ ErdosStewart 4 ∧ ErdosStewart 5 := by
  unfold ErdosStewart
  rw [nextPrime_one, nextPrime_two, nextPrime_three, nextPrime_four,
    nextPrime_five, nextPrime_seven]
  have h25 : (25 : ℕ).primeFactors = {5} := by
    change (5 ^ 2 : ℕ).primeFactors = {5}
    exact Nat.primeFactors_prime_pow (by decide) (by decide)
  have h121 : (121 : ℕ).primeFactors = {11} := by
    change (11 ^ 2 : ℕ).primeFactors = {11}
    exact Nat.primeFactors_prime_pow (by decide) (by decide)
  change (∀ q ∈ (2 : ℕ).primeFactors, q = 2 ∨ q = 3) ∧
    (∀ q ∈ (3 : ℕ).primeFactors, q = 3 ∨ q = 5) ∧
    (∀ q ∈ (7 : ℕ).primeFactors, q = 5 ∨ q = 7) ∧
    (∀ q ∈ (25 : ℕ).primeFactors, q = 5 ∨ q = 7) ∧
    (∀ q ∈ (121 : ℕ).primeFactors, q = 7 ∨ q = 11)
  rw [Nat.Prime.primeFactors (by decide : Nat.Prime 2),
    Nat.Prime.primeFactors (by decide : Nat.Prime 3),
    Nat.Prime.primeFactors (by decide : Nat.Prime 7), h25, h121]
  simp

/-- Satisfiability: the five known cases.
    n=1: 2 = p₁ ✓;  n=2: 3 ✓;  n=3: 7 = p₄ = nextPrime(nextPrime 3) ✓;
    n=4: 25 = 5² ✓;  n=5: 121 = 11² and nextPrime(nextPrime 5) = 11 ✓.
    -- PROVABLE (decide, after rewriting `nextPrime` values). -/
example : ErdosStewart 1 ∧ ErdosStewart 2 ∧ ErdosStewart 3 ∧
    ErdosStewart 4 ∧ ErdosStewart 5 := by
  exact erdosStewart_sanity

/-- Six fails the Erdős–Stewart property, with prime divisor 103. -/
theorem not_erdosStewart_six : ¬ ErdosStewart 6 := by
  unfold ErdosStewart
  rw [nextPrime_six, nextPrime_seven]
  intro h
  have h103 : 103 ∈ ((6 : ℕ).factorial + 1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by decide, by decide, by decide⟩
  have hchoices : 103 = 7 ∨ 103 = 11 := h 103 h103
  norm_num at hchoices

/-- Non-degeneracy: `n = 6` fails (6! + 1 = 721 = 7 · 103, and
    103 is not among {7, 11}).  -- PROVABLE (decide). -/
example : ¬ ErdosStewart 6 := by
  exact not_erdosStewart_six

/-- **Erdős #1058, Luca's theorem** (Lu01): the only `n ≥ 1` with the
    Erdős–Stewart property are `n = 1, 2, 3, 4, 5`.  In particular the
    set is finite, answering the problem.

    Source text: "Are there only finitely many $n$ such that
    $n\in[p_{k-1},p_k)$ and the only primes dividing $n!+1$ are $p_k$
    and $p_{k+1}$?"  Luca proved yes, with the full solution list.

    Proof sketch (attack plan): if all prime factors of `n!+1` are among
    `{p, q}` with `p, q` the two primes following `n`, then
    `n! + 1 = p^a q^b`.  Both `p, q < 2n` for `n ≥ 2` well within
    Bertrand (`Nat.exists_prime_lt_and_le_two_mul`).  Luca's argument:
    compare `v_p` and sizes — `p^a q^b = n! + 1 < (2n)^{a+b}`-type
    counting against Stirling growth of `n!`, plus the classical
    congruence obstructions (`p ∣ n!+1` forces `p > n`; Wilson-type
    identities pin `a, b` small).  A 4-page elementary argument;
    factorial divisibility + Bertrand are the load-bearing inputs, both
    in Mathlib.  Full closure of an Erdős problem is plausible here.
    Effort M per candidates audit. -/
theorem luca_erdos_stewart :
    {n : ℕ | 1 ≤ n ∧ ErdosStewart n} = {1, 2, 3, 4, 5} := by
  sorry

/-- Finiteness corollary — the literal answer to the question as posed.
    -- PROVABLE from `luca_erdos_stewart` (finite explicit set). -/
theorem erdos_1058_finite : {n : ℕ | 1 ≤ n ∧ ErdosStewart n}.Finite := by
  rw [luca_erdos_stewart]
  exact Set.toFinite _

/-- `nextPrime m` is a prime exceeding `m` (the defining set is nonempty
    by Euclid). -/
private theorem nextPrime_spec (m : ℕ) : (nextPrime m).Prime ∧ m < nextPrime m := by
  obtain ⟨p, hmp, hp⟩ := Nat.exists_infinite_primes (m + 1)
  exact Nat.sInf_mem (s := {p : ℕ | p.Prime ∧ m < p}) ⟨p, hp, hmp⟩

/-- Bertrand: for `m ≠ 0`, the least prime above `m` is at most `2m`. -/
private theorem nextPrime_le_two_mul (m : ℕ) (hm : m ≠ 0) : nextPrime m ≤ 2 * m := by
  obtain ⟨p, hp, hmp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul m hm
  exact (Nat.sInf_le (s := {p : ℕ | p.Prime ∧ m < p}) ⟨hp, hmp⟩).trans hp2

/-- For `n ≠ 0`, both candidate primes of the Erdős–Stewart property are
    at most `4n`. -/
private theorem nextPrime_nextPrime_le (n : ℕ) (hn : n ≠ 0) :
    nextPrime n ≤ 4 * n ∧ nextPrime (nextPrime n) ≤ 4 * n := by
  have h1 : nextPrime n ≤ 2 * n := nextPrime_le_two_mul n hn
  have h1' : nextPrime n ≠ 0 := (nextPrime_spec n).1.ne_zero
  have h2 : nextPrime (nextPrime n) ≤ 2 * nextPrime n := nextPrime_le_two_mul _ h1'
  constructor <;> omega

/-- Certificate criterion: if some `R > 1` divides `n! + 1` and is coprime
    to `(4n)!`, then `n` fails the Erdős–Stewart property, since the least
    prime factor of `R` exceeds `4n`. -/
private theorem not_erdosStewart_of_cert (n R : ℕ) (hn : n ≠ 0) (hR : 1 < R)
    (hdvd : R ∣ n.factorial + 1) (hcop : Nat.gcd R (4 * n).factorial = 1) :
    ¬ ErdosStewart n := by
  intro hES
  have hℓ : (R.minFac).Prime := Nat.minFac_prime (by omega)
  have hℓdvd : R.minFac ∣ n.factorial + 1 := (Nat.minFac_dvd R).trans hdvd
  have hmem : R.minFac ∈ (n.factorial + 1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hℓ, hℓdvd, by positivity⟩
  have hle : R.minFac ≤ 4 * n := by
    obtain ⟨hb1, hb2⟩ := nextPrime_nextPrime_le n hn
    rcases hES _ hmem with h | h <;> omega
  have hfac : R.minFac ∣ (4 * n).factorial := Nat.dvd_factorial hℓ.pos hle
  have hone : R.minFac ∣ 1 := hcop ▸ Nat.dvd_gcd (Nat.minFac_dvd R) hfac
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp hone)

/-- Remove from `x` its common part with `M` (one pass). -/
private def stripBy (M x : ℕ) : ℕ := x / Nat.gcd x M

private theorem stripBy_dvd (M x : ℕ) : stripBy M x ∣ x :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x M)

/-- The two-pass certificate value for `n`: `n! + 1` stripped twice of
    its common factors with `(4n)!`. -/
private def certR (n : ℕ) : ℕ :=
  stripBy (4 * n).factorial (stripBy (4 * n).factorial (n.factorial + 1))

/-- Boolean certificate check for `n`. -/
private def certOK (n : ℕ) : Bool :=
  decide (1 < certR n) && Nat.gcd (certR n) (4 * n).factorial == 1

/-- Check `certOK` at `a, a+1, …, a+k-1`. -/
private def certAll (a : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => certOK (a + k) && certAll a k

private theorem certAll_spec (a k : ℕ) (h : certAll a k = true) (i : ℕ) (hi : i < k) :
    certOK (a + i) = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [certAll, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ih h.2 hi
    · exact hi ▸ h.1

/-- Kernel computation: the certificate check passes for `n = 6, …, 100`. -/
private theorem certAll_6_95 : certAll 6 95 = true := by
  decide +kernel

private theorem not_erdosStewart_of_certOK (n : ℕ) (hn : n ≠ 0) (h : certOK n = true) :
    ¬ ErdosStewart n := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine not_erdosStewart_of_cert n (certR n) hn h.1 ?_ h.2
  exact (stripBy_dvd _ _).trans (stripBy_dvd _ _)

/-- Sanity window: no further solutions up to 100.  Independent of the
    tail argument; a `decide`/`native_decide` sweep (the factorials get
    large, so kernel `decide` may need staging — note the enlarged trust
    surface if `native_decide` is used).
    -- PROVABLE (native_decide-scale). -/
theorem erdos_stewart_window_100 :
    ∀ n ∈ Finset.Icc 6 100, ¬ ErdosStewart n := by
  intro n hn
  obtain ⟨h6, h100⟩ := Finset.mem_Icc.mp hn
  have hok : certOK (6 + (n - 6)) = true := certAll_spec 6 95 certAll_6_95 (n - 6) (by omega)
  rw [show 6 + (n - 6) = n by omega] at hok
  exact not_erdosStewart_of_certOK n (by omega) hok

end ErdosCandidates.E1058

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - DB statement matches file header verbatim (with the corrected p_k/p_{k+1} indexing per TerenceTao comment post-753).
   - Solver attribution Luca [Lu01] matches DB.
   - `nextPrime` via `sInf` cleanly avoids the p_0 boundary issue for n=1.
   - Known cases verified: 1!+1=2={2}, 2!+1=3={3}, 3!+1=7={7}, 4!+1=25={5}, 5!+1=121={11}. All match nextPrime/nextPrime(nextPrime) values.
   - Non-example n=6: 6!+1=721=7*103, 103 is prime and not in {7,11}. Correct.
   - FLAG (minor): `nextPrime` is `noncomputable` and defined via `sInf`, so `ErdosStewart` is not `Decidable` without additional work. The `erdos_stewart_window_100` theorem acknowledges this needs `native_decide` with care. Not a fidelity error but a proof-engineering concern.
   - FLAG (minor): `luca_erdos_stewart` requires `1 ≤ n` in the set comprehension, which excludes n=0. The DB solution list "n=1,2,3,4,5" implicitly assumes n >= 1. 0!+1=2, nextPrime(0)=2, so ErdosStewart(0) would hold. The set should arguably be `{0,1,2,3,4,5}` or the guard should be documented as intentional. This is a genuine fidelity concern if Luca's theorem covers n=0.
-/
