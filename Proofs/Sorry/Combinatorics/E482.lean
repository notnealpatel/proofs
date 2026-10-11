/-
  Erdős Problem #482 — the Graham–Pollak recurrence and the binary
  expansion of √2.
  Status: solved (Graham–Pollak 1970; generalizations Stoll 2005, 2006).
  Tier A proof target.

  Verbatim statement (`goof erdos fetch 482`, pulled 2026-08-05):

    "Define a sequence by $a_1=1$ and
    \[a_{n+1}=\lfloor\sqrt{2}(a_n+1/2)\rfloor\]
    for $n\geq 1$. The difference $a_{2n+1}-2a_{2n-1}$ is the $n$th digit
    in the binary expansion of $\sqrt{2}$.

    Find similar results for $\theta=\sqrt{m}$, and other algebraic
    numbers."

  DB remarks: the √2 result is Graham–Pollak [GrPo70]; the open-ended
  generalization is answered by Stoll [St05], [St06].

  OEIS anchors: A004539 (binary expansion of √2, pulled 2026-08-05:
  1,0,1,1,0,1,0,1,0,0,0,0,0,1,…) and A001521 (the Graham–Pollak sequence
  1,2,3,4,6,9,13,19,27,38,…).

  Ground-truth trace (hand-checked): a₁..a₉ = 1,2,3,4,6,9,13,19,27;
  a₃−2a₁ = 1, a₅−2a₃ = 0, a₇−2a₅ = 1, a₉−2a₇ = 1 — matching A004539
  digits 1,0,1,1 (the leading digit is the integer-part bit of
  √2 = 1.0110101000001…₂).

  Mathlib inventory (leandoc 2026-08-05): `Real.sqrt`, `Int.floor`
  (`⌊·⌋`), `Nat.floor`, `zpow` for the digit definition; floor bracketing
  via `Int.floor_eq_iff`, `Real.sq_sqrt`, `Real.sqrt_lt_sqrt` for the
  numeric certificates.  `native_decide` cannot touch `Real.sqrt`; the
  small-index checks go through interval arithmetic (`norm_num`
  extensions / explicit rational bracketing 1.414213 < √2 < 1.414214).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E482

open Real

/-- The Graham–Pollak sequence, 1-indexed as in the source:
    `gp 1 = 1`, `gp (n+1) = ⌊√2 * (gp n + 1/2)⌋`.
    (`gp 0` is defined as `0`, an unused junk index — every theorem below
    quantifies over indices `≥ 1`.) -/
noncomputable def gp : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 => ⌊Real.sqrt 2 * (gp n + 1 / 2)⌋₊

/-- The `n`-th binary digit of `√2`, 1-indexed so that digit 1 is the
    integer-part bit: `digit n = ⌊2^(n-1)√2⌋ - 2⌊2^(n-2)√2⌋` with `zpow`
    (integer exponents, so `n = 1` uses `2^(-1)` and yields
    `⌊√2⌋ - 2⌊√2/2⌋ = 1`).  Values (A004539): 1,0,1,1,0,1,0,1,… -/
noncomputable def sqrtTwoDigit (n : ℕ) : ℤ :=
  ⌊Real.sqrt 2 * (2 : ℝ) ^ ((n : ℤ) - 1)⌋ -
    2 * ⌊Real.sqrt 2 * (2 : ℝ) ^ ((n : ℤ) - 2)⌋

/-- Ground truth for the digit stream against A004539:
    digits 1..8 are 1,0,1,1,0,1,0,1.
    -- PROVABLE (interval arithmetic on √2; not decide-able). -/
example : sqrtTwoDigit 1 = 1 ∧ sqrtTwoDigit 2 = 0 ∧ sqrtTwoDigit 3 = 1 ∧
    sqrtTwoDigit 4 = 1 ∧ sqrtTwoDigit 5 = 0 ∧ sqrtTwoDigit 6 = 1 := by
  sorry

/-- Ground truth for the recurrence against A001521: first terms
    1, 2, 3, 4, 6, 9, 13, 19, 27.
    -- PROVABLE (interval arithmetic: e.g. `gp 2 = ⌊√2·(3/2)⌋ = 2` from
    `2 ≤ (3/2)√2 < 3`, i.e. `16/9 ≤ 2 < 4`). -/
example : gp 2 = 2 ∧ gp 3 = 3 ∧ gp 4 = 4 ∧ gp 5 = 6 ∧ gp 6 = 9 ∧
    gp 7 = 13 ∧ gp 8 = 19 ∧ gp 9 = 27 := by
  sorry

/-- **Erdős #482, Graham–Pollak theorem** (GrPo70): for every `n ≥ 1`,
    `a_{2n+1} - 2·a_{2n-1}` equals the `n`-th binary digit of `√2`.

    Source text: "The difference $a_{2n+1}-2a_{2n-1}$ is the $n$th digit
    in the binary expansion of $\sqrt 2$."

    Formalization notes: the digit convention is pinned by the
    ground-truth trace above (digit 1 = integer-part bit = 1, matching
    a₃ − 2a₁ = 1); subtraction is in ℤ after casting (STYLE.md).

    Proof sketch (attack plan): Graham–Pollak's original proof shows by
    induction the closed form `a_{2n-1} = ⌊2^{(n-1)/…}√2·…⌋`-type
    invariant; the modern route (Stoll) proves the invariant pair
    `a_{2n} = ⌊√2 a_{2n-1}⌋ + a_{2n-1}`-free:  concretely one shows
    `a_{2n+1} = ⌊2^n √2⌋ + a stable correction` and the difference
    telescopes to the digit.  Key inductive claim to try first:
    `(a (2*n-1) : ℝ) = ⌊(2:ℝ)^(n-1) * √2⌋ + (something bounded)`; the
    floor-arithmetic bridge is the fiddly part flagged by the skeptic
    audit.  Mathlib tools: `Int.floor_eq_iff`, `Int.lt_floor_add_one`,
    `Real.sqrt_two_mul_self`, induction on `n`.
    Effort M per candidates audit. -/
theorem graham_pollak (n : ℕ) (hn : 1 ≤ n) :
    (gp (2 * n + 1) : ℤ) - 2 * (gp (2 * n - 1) : ℤ) = sqrtTwoDigit n := by
  sorry

/-- The digit stream is genuinely a binary digit stream: each value is
    `0` or `1`.  Needed to make `graham_pollak` meaningful (a difference
    identity against an unconstrained integer stream would be weak).
    -- PROVABLE (floor bracketing: `2⌊x⌋ ≤ ⌊2x⌋ ≤ 2⌊x⌋ + 1`). -/
theorem sqrtTwoDigit_mem (n : ℕ) (hn : 1 ≤ n) :
    sqrtTwoDigit n = 0 ∨ sqrtTwoDigit n = 1 := by
  sorry

/-- Reconstruction sanity: the digits do reconstruct √2, i.e.
    `∑_{n≤N} digit n · 2^{1-n} → √2`.  Pins the digit convention to the
    actual binary expansion (guards against an off-by-one digit stream
    that would make `graham_pollak` a statement about the wrong
    constant). -/
theorem sqrtTwoDigit_reconstructs :
    Filter.Tendsto
      (fun N => ∑ n ∈ Finset.Icc 1 N,
        (sqrtTwoDigit n : ℝ) * (2 : ℝ) ^ (1 - (n : ℤ)))
      Filter.atTop (nhds (Real.sqrt 2)) := by
  sorry

end ErdosCandidates.E482

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - DB statement matches file header verbatim.
   - Recurrence `a_{n+1} = ⌊√2*(a_n + 1/2)⌋` faithfully translated using `⌊·⌋₊` (Nat.floor). Since all terms are non-negative, Nat.floor = Int.floor here.
   - Graham-Pollak sequence verified: a₁..a₉ = 1,2,3,4,6,9,13,19,27 matches A001521.
   - Digit differences verified: a₃-2a₁=1, a₅-2a₃=0, a₇-2a₅=1, a₉-2a₇=1, matching A004539 digits 1,0,1,1.
   - `sqrtTwoDigit` definition verified: digit(n) = ⌊√2*2^(n-1)⌋ - 2⌊√2*2^(n-2)⌋ is the standard binary digit extraction formula.
   - Solver attribution Graham-Pollak [GrPo70] matches DB.
   - `gp 0 = 0` junk index documented; all theorems quantify over n >= 1.
   - Main theorem uses ℤ cast for the subtraction `gp(2n+1) - 2*gp(2n-1)`, avoiding ℕ-subtraction. Correct per STYLE.md.
   - `sqrtTwoDigit_reconstructs` reconstruction guard is a good anti-off-by-one check.
-/
