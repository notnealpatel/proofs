/-
  Erdős Problem #482 — the Graham–Pollak recurrence and the binary
  expansion of √2.

  Verbatim statement (`goof erdos fetch 482`, pulled 2026-08-05):

    "Define a sequence by $a_1=1$ and
    \[a_{n+1}=\lfloor\sqrt{2}(a_n+1/2)\rfloor\]
    for $n\geq 1$. The difference $a_{2n+1}-2a_{2n-1}$ is the $n$th digit
    in the binary expansion of $\sqrt{2}$.

    Find similar results for $\theta=\sqrt{m}$, and other algebraic
    numbers."

  This file closes the √2 theorem, not the open-ended request for
  other algebraic numbers. The definitions gp and sqrtTwoDigit have
  moved unchanged to the production dependency, in the same namespace.

  Source conventions checked against Stoll, JIS 8 (2005), Article
  05.3.2, introduction (Fact 1), and arXiv:0902.4168, §2. Both attribute
  the √2 result to Graham–Pollak (1970). The original 1970 paper was
  not consulted. Digit 1 is the integer-part bit of 1.011010…₂.

  Proof mechanism: set A(m)=m+floor(m/√2), B(m)=m+floor(√2 m).
  Fractional-part bracketing proves T(A(m))=B(m) and T(B(m))=A(2m),
  where T(u)=floor(√2(u+1/2)). Thus gp(2k+1)=A(2^k) and
  gp(2k+2)=B(2^k). Consecutive odd states cancel the powers of two,
  yielding the digit floor difference. Floor bracketing gives binary
  membership; the weighted partial sums telescope and their error
  is bounded by 2·(1/2)^N. This is an independently developed paired
  proof, with no claim of novelty or transcription of the 1970 proof.
-/
import Combinatorics.GrahamPollak

set_option autoImplicit false

namespace ErdosCandidates.E482

/-- Ground truth for the digit stream against A004539: digits 1..6. -/
example : sqrtTwoDigit 1 = 1 ∧ sqrtTwoDigit 2 = 0 ∧ sqrtTwoDigit 3 = 1 ∧
    sqrtTwoDigit 4 = 1 ∧ sqrtTwoDigit 5 = 0 ∧ sqrtTwoDigit 6 = 1 :=
  sqrtTwoDigit_first_six

/-- Ground truth for the recurrence against A001521: terms 2..9. -/
example : gp 2 = 2 ∧ gp 3 = 3 ∧ gp 4 = 4 ∧ gp 5 = 6 ∧ gp 6 = 9 ∧
    gp 7 = 13 ∧ gp 8 = 19 ∧ gp 9 = 27 :=
  gp_first_nine

/-- Graham–Pollak: for every n ≥ 1 the odd-state difference is the
n-th binary digit of √2, starting with its integer-part bit.
Subtraction takes place in ℤ after casting. -/
theorem graham_pollak (n : ℕ) (hn : 1 ≤ n) :
    (gp (2 * n + 1) : ℤ) - 2 * (gp (2 * n - 1) : ℤ) = sqrtTwoDigit n :=
  graham_pollak_identity n hn

/-- Every digit of the specified stream is zero or one. -/
theorem sqrtTwoDigit_mem (n : ℕ) (hn : 1 ≤ n) :
    sqrtTwoDigit n = 0 ∨ sqrtTwoDigit n = 1 :=
  sqrtTwoDigit_binary n hn

/-- The weighted partial digit sums reconstruct √2. -/
theorem sqrtTwoDigit_reconstructs :
    Filter.Tendsto
      (fun N => ∑ n ∈ Finset.Icc 1 N,
        (sqrtTwoDigit n : ℝ) * (2 : ℝ) ^ (1 - (n : ℤ)))
      Filter.atTop (nhds (Real.sqrt 2)) :=
  sqrtTwoDigit_tendsto

end ErdosCandidates.E482
