/-
  Erdős Problem #699 — a common prime factor of two binomial
  coefficients in the same row.
  Status: falsifiable (open).  Tier UA attack target.

  Verbatim statement (`goof erdos fetch 699`, pulled 2026-08-05):

    "Is it true that for every $1\leq i<j\leq n/2$ there exists some
    prime $p\geq i$ such that
    \[p\mid \textrm{gcd}\left(\binom{n}{i}, \binom{n}{j}\right)?\]"

  DB remarks (Erdős–Szekeres): Sylvester–Schur gives a prime > i
  dividing C(n,i) alone.  GPT 5.6/Price proved the claim for j ≤ (3/2)i
  and for n = 2j.  For fixed i < j only finitely many n can fail (easy;
  Bloom's argument via the identity
  C(n,i)·C(n−i,j−i) = C(n,j)·C(j,i): if V_i(n) — the part of C(n,i)
  supported on primes ≥ i — is coprime to C(n,j) then V_i(n) ∣ C(j,i),
  bounding n).  The strict variant (p > i) fails at explicit exceptional
  pairs; the only known exception with i ≥ 4 is
  gcd(C(28,5), C(28,14)) = 2³·3³·5.  Verified up to n = 10⁷ (Cong,
  Jan 2026, comment-sourced).

  Mathlib inventory (leandoc 2026-08-05): `Nat.choose`, `Nat.gcd`,
  `Nat.primeFactors`, `Nat.Prime.dvd_choose`, `Nat.choose_mul_choose_le`?
  — the key identity C(n,i)·C(n−i,j−i) = C(n,j)·C(j,i) is
  `Nat.choose_mul_choose_eq`-shaped; `Nat.succ_mul_choose_eq` family in
  Data/Nat/Choose.  Kummer machinery adjacent to
  `Proofs/Erdos/Erdos175/NotSquarefree.lean`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E699

/-- `SharedLargePrime n i j`: some prime `p ≥ i` divides both `C(n,i)`
    and `C(n,j)`. -/
def SharedLargePrime (n i j : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)

/-- Satisfiability at a small model: `n = 10, i = 2, j = 5`:
    `C(10,2) = 45`, `C(10,5) = 252`, `gcd = 9`, and `p = 3 ≥ 2` works.
    -- PROVABLE (decide). -/
example : SharedLargePrime 10 2 5 := by sorry

/-- **Erdős #699, headline (OPEN)**: for all `1 ≤ i < j` with `2j ≤ n`,
    some prime `p ≥ i` divides `gcd(C(n,i), C(n,j))`.

    Source text: "Is it true that for every $1\leq i<j\leq n/2$ there
    exists some prime $p\geq i$ such that
    $p \mid \gcd(\binom{n}{i},\binom{n}{j})$?"

    `j ≤ n/2` is encoded multiplicatively as `2*j ≤ n` (STYLE.md: no
    ℕ-division in hypotheses).  Status: open/falsifiable; verified to
    n = 10⁷.  Archived; the provable slices are below. -/
theorem erdos_699 (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : 2 * j ≤ n) :
    SharedLargePrime n i j := by
  sorry

/-- **Proved slice 1 — the balanced case** `n = 2j` (GPT 5.6/Price via
    Bloom's identity; comment-sourced 2026, re-derive before trusting).
    Attack: from C(2j,i)·C(2j−i,j−i) = C(2j,j)·C(j,i), the part of
    C(2j,i) supported on primes ≥ i cannot be coprime to C(2j,j) unless
    it divides C(j,i); but the EEES 1978 bound V_i(n)² > C(n,i) (12
    exceptions) gives V_i(2j) > C(j,i).  Lemma chain: (a) the identity
    (`Nat.choose_mul_choose_eq`-family or direct factorial proof);
    (b) the smooth/rough split of C(n,i) (shared def with #684/#1093);
    (c) EEES lower bound — the deep input, sorry-able separately. -/
theorem erdos_699_balanced (j i : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    SharedLargePrime (2 * j) i j := by
  sorry

/-- **Proved slice 2 — finiteness of bad `n` for fixed `i < j`**
    (easy per DB; Bloom's argument).  For fixed `1 ≤ i < j` the set of
    `n ≥ 2j` violating the conclusion is finite: coprimality forces
    `V_i(n) ∣ C(j,i)` while `V_i(n) → ∞` with `n`.
    The natural first sorry-free target of this file. -/
theorem erdos_699_finitely_many_bad (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
    {n : ℕ | 2 * j ≤ n ∧ ¬ SharedLargePrime n i j}.Finite := by
  sorry

/-- The Erdős–Szekeres *strict* variant `p > i` fails: at
    `(n, i, j) = (28, 5, 14)`, `gcd(C(28,5), C(28,14)) = 2³·3³·5 = 1080`
    and no prime `> 5` divides it (but `p = 5 ≥ 5` does — the weak form
    holds).  The only known exception with `i ≥ 4`.
    -- PROVABLE (decide; C(28,14) = 40116600). -/
theorem strict_variant_fails_28_5_14 :
    Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) = 1080 ∧
    (∀ p : ℕ, p.Prime → 5 < p → ¬ p ∣ 1080) ∧
    SharedLargePrime 28 5 14 := by
  sorry

/-- Sanity window: the headline verified for all `n ≤ 60` and all
    admissible `(i, j)`.  -- PROVABLE (decide; small search space). -/
theorem erdos_699_window_60 :
    ∀ n ∈ Finset.range 61, ∀ i ∈ Finset.range 31, ∀ j ∈ Finset.range 31,
      1 ≤ i → i < j → 2 * j ≤ n → SharedLargePrime n i j := by
  sorry

/-- **Sylvester–Schur** (input lemma, also the prize of #683): for
    `1 ≤ k` and `2k ≤ n`, `C(n,k)` has a prime factor `> k`.  Not in
    Mathlib (leandoc miss "sylvester schur" re-verified 2026-08-05).
    Load-bearing for this problem, #683, #1094, #1095. -/
theorem sylvester_schur (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  sorry

end ErdosCandidates.E699

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB pull exactly.
   - SharedLargePrime uses p >= i (not p > i), matching the weak form; strict variant
     correctly separated into strict_variant_fails_28_5_14.
   - gcd(C(28,5), C(28,14)) = 1080 = 2^3 * 3^3 * 5 verified by computation.
   - C(10,2) = 45, C(10,5) = 252, gcd = 9, prime 3 >= 2 verified.
   - C(28,14) = 40116600 verified.
   - j <= n/2 encoded as 2*j <= n: correct ℕ-division avoidance per STYLE.md.
   - Attribution: DB says "GPT 5.6 (prompted by Price)" for balanced/3-2 cases; file
     says "GPT 5.6/Price" — faithful. Bloom's finiteness argument from comments
     correctly attributed. Cong verification to 10^7 correctly flagged comment-sourced.
   - Sylvester-Schur correctly noted as not in Mathlib.
   - Types: all ℕ, no ℤ/ℝ issues. No ℕ-subtraction or ℕ-division in hypotheses.
-/
