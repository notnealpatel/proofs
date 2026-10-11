/-
  Erdős Problem #684 — the smooth part of binomial coefficients.
  Status: open.  Tier UC lemma mine (the smooth/rough factorization
  is the reusable def feeding #1093/#1094/#1095).

  Verbatim statement (`goof erdos fetch 684`, pulled 2026-08-05):

    "For $0\leq k\leq n$ write\[\binom{n}{k} = uv\]where the only
    primes dividing $u$ are in $[2,k]$ and the only primes dividing
    $v$ are in $(k,n]$.

    Let $f(n)$ be the smallest $k$ such that $u>n^2$. Give bounds for
    $f(n)$."

  DB remarks: Mahler's theorem gives f(n) → ∞ (ineffective).
  Tang & ChatGPT: f(n) ≤ n^{30/43+o(1)} (n^{2/3+o(1)} on RH).
  Sothanaphan & ChatGPT heuristic: f(n) ~ 2·log n for most n.
  An internal OpenAI model [APSSV26, arXiv:2603.29961]: elementary
  f(n) ≪ (log n)², and arbitrarily large n with
  f(n) ≥ (1/2 − o(1))·log n.

  Audit verdict: kept OUT of UA — even the "elementary" (log n)²
  bound leans on prime-distribution input.  The mine: the smooth-part
  decomposition and Kummer-level valuation lemmas.

  OEIS anchor: A392019.

  Mathlib inventory: `Nat.factorization` (finsupp) — the smooth part
  is a `Finsupp.prod` restricted to small primes; `Nat.ord_proj`/
  `Nat.ord_compl` are the single-prime analogues.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E684

/-- `smoothPart k m`: the largest divisor of `m` supported on primes
    `≤ k` — the `u` of the problem (for `m = C(n,k)`). -/
def smoothPart (k m : ℕ) : ℕ :=
  m.factorization.prod (fun p e => if p ≤ k then p ^ e else 1)

/-- `roughPart k m`: the complementary divisor (`v`). -/
def roughPart (k m : ℕ) : ℕ :=
  m.factorization.prod (fun p e => if k < p then p ^ e else 1)

/-- Ground truth: `C(10,4) = 210 = 2·3·5·7`; smoothPart 4 = 2·3 = 6,
    roughPart 4 = 5·7 = 35.  -- PROVABLE (decide). -/
example : smoothPart 4 (Nat.choose 10 4) = 6 ∧
    roughPart 4 (Nat.choose 10 4) = 35 := by
  sorry

/-- The factorization identity `u·v = C(n,k)` — the definitional
    glue.  -- PROVABLE (`Nat.factorization_prod_pow_eq_self`; split
    the Finsupp product; effort S — the reusable lemma for
    #1093/#1094/#1095). -/
theorem smoothPart_mul_roughPart (k m : ℕ) (hm : m ≠ 0) :
    smoothPart k m * roughPart k m = m := by
  sorry

/-- `f n`: the least `k ≤ n` with `smoothPart k (C(n,k)) > n²` — the
    `f(n)` of the problem.  sInf honesty: `k = n` gives
    `C(n,n) = 1`… careful: u(n, n) = 1 ≤ n²!  Honesty instead comes
    from mid-range k (e.g. k = ⌊n/2⌋ makes the smooth part of the
    central binomial huge for large n — the Erdős–EGRS smooth-mass
    lower bounds); the set is nonempty for n large.  Theorems guard
    with the existence hypothesis or large-n. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | k ≤ n ∧ n ^ 2 < smoothPart k (n.choose k)}

/-- **Mahler consequence (ineffective)**, archived: `f(n) → ∞`.
    Stated as: for every `K`, eventually `K ≤ f n` — every fixed `k`
    eventually has smooth part `≤ n²` (this is the DB's reading of
    Mahler's theorem on smooth parts of products of consecutive
    integers; ineffective — no explicit N exists in the literature). -/
theorem mahler_f_tendsto (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ f n := by
  sorry

/-- **APSSV26 elementary upper bound**, archived:
    `f(n) ≪ (log n)²`. -/
theorem apssv_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (f n : ℝ) ≤ C * Real.log n ^ 2 := by
  sorry

/-- **APSSV26 lower bound along a subsequence**, archived: for every
    `ε > 0` there are arbitrarily large `n` with
    `f(n) ≥ (1/2 − ε)·log n`. -/
theorem apssv_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ((1 : ℝ) / 2 - ε) * Real.log n ≤ (f n : ℝ) := by
  sorry

/-- **Tang–ChatGPT bound** (comment-sourced per DB; refereed status
    unclear — flagged), archived: `f(n) ≤ n^{30/43+o(1)}`; on RH,
    `n^{2/3+o(1)}`.  Superseded in strength by `apssv_upper` but
    recorded for provenance. -/
theorem tang_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (f n : ℝ) ≤ (n : ℝ) ^ ((30 : ℝ) / 43 + ε) := by
  sorry

/-- Sanity for the sInf-set nonemptiness at a concrete point: probe
    whether some `k` has `smoothPart k (C(n,k)) > n²` at, say,
    n = 100 (heuristically k ≈ 2 log n ≈ 9).  Marked as the probe
    stub; run `#eval` sweeps before certifying.
    -- PROBE NEEDED (then decide). -/
theorem f_set_nonempty_100 :
    ∃ k : ℕ, k ≤ 100 ∧ 100 ^ 2 < smoothPart k (Nat.choose 100 k) := by
  sorry

end ErdosCandidates.E684

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - Verbatim statement matches DB fetch exactly.
   - smoothPart/roughPart definitions faithfully encode the u/v split at
     prime threshold k. The m = 0 junk is properly guarded by hm : m != 0
     in smoothPart_mul_roughPart.
   - Arithmetic verified: C(10,4) = 210, smoothPart 4 = 6, roughPart 4 = 35.
   - Mahler f -> infinity faithfully stated as ineffective.
   - APSSV26 upper (log n)^2 and lower (1/2-o(1))log n match DB exactly.
     arXiv:2603.29961 confirmed in DB reference.
   - FLAG (minor): DB says "An internal OpenAI model" citing APSSV26; the
     file header faithfully reproduces this wording. The DB itself labels it
     this way — the file is source-faithful but the provenance is unusual
     (DB acknowledges AI-assisted authorship throughout the comment thread).
   - Tang 30/43 exponent: DB confirms this is the Guth-Maynard-upgraded
     version of Tang's original 12/17, per Bloom's comment. Faithful.
   - Sothanaphan heuristic f(n) ~ 2 log n: confirmed in DB comments.
     "ChatGPT" attribution confirmed.
   - f sInf honesty: the file correctly notes k = n gives u = 1 (not > n^2)
     and defers nonemptiness to mid-range k for large n. Theorems guard
     with existence hypotheses. Acceptable.
-/
