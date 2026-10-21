/-
  Erdős Problem #384 — small prime divisors of binomial coefficients.
  Status: corrected Ecklund variant, known in literature (1969); admitted here.
  This is NOT an unchanged formalization of the strict DB headline.

  Verbatim statement (`goof erdos fetch 384`, pulled 2026-08-05):

    "If $1<k<n-1$ then $\binom{n}{k}$ is divisible by a prime $p<n/2$
    (except $\binom{7}{3}=5\cdot 7$)."

  DB remarks: conjecture of Erdős–Selfridge, proved by Ecklund [Ec69].
  Ecklund conjectured further that for n > k² the binomial C(n,k) has a
  prime factor p < n/k; EEES proved p ≪ n/k^c.  Stronger forms: #1094,
  #1095.

  ⚠ SOURCE-FIDELITY WARNING (from DB comment post-4157, JoshuaB,
  Feb 2026): Ecklund's actual theorem has hypotheses n ≥ 2k and
  conclusion p ≤ n/2 (NON-strict).  The DB headline "1<k<n-1, p<n/2,
  except C(7,3)" is doubly off: (a) with strict p < n/2 the case
  (n,k) = (4,2) fails (C(4,2)=6, no prime < 2), and (b) with the range
  1<k<n-1 the symmetric exception C(7,4)=35 must also be excluded.
  We formalize Ecklund's true statement as the main target and the DB's
  range as a corollary with both exceptions.

  Mathlib inventory (leandoc 2026-08-05): `Nat.choose`,
  `Nat.Prime`, `Nat.exists_prime_lt_and_le_two_mul` (Bertrand),
  `Nat.Prime.dvd_choose` variants, Kummer-style valuation tools in
  `Proofs/Erdos/Erdos175/NotSquarefree.lean` (`padicValNat` machinery).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E384

/-- Ground truth for the exceptional case: `C(7,3) = 35 = 5·7`, whose
    prime factors `5, 7` both exceed `7/2`.  -- PROVABLE (decide). -/
theorem choose_seven_three_sanity : Nat.choose 7 3 = 35 ∧ (Nat.choose 7 3).primeFactors = {5, 7} := by
  have hc : Nat.choose 7 3 = 35 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  rw [hc]
  constructor
  · rfl
  · change (5 * 7 : ℕ).primeFactors = {5, 7}
    rw [Nat.primeFactors_mul (by decide) (by decide),
      Nat.Prime.primeFactors (by decide : Nat.Prime 5),
      Nat.Prime.primeFactors (by decide : Nat.Prime 7)]
    decide

/-- **Erdős #384, Ecklund's theorem** (Ec69), faithful form.
    If `2 ≤ k` and `2k ≤ n` and `(n, k) ≠ (7, 3)`, then `C(n,k)` has a
    prime factor `p` with `2p ≤ n` (i.e. `p ≤ n/2` in the real sense —
    stated multiplicatively per STYLE.md to avoid ℕ-division junk).

    Source text: "If $1<k<n-1$ then $\binom{n}{k}$ is divisible by a
    prime $p<n/2$ (except $\binom{7}{3}=5\cdot 7$)" — corrected to
    Ecklund's `n ≥ 2k`, `p ≤ n/2` form per the DB comment thread.

    Proof sketch (attack plan): for `k ≥ 2`, if no prime `≤ n/2` divides
    `C(n,k)`, every prime factor is in `(n/2, n]`, so
    `C(n,k) ∣ ∏_{n/2 < p ≤ n} p`; each such prime divides to the first
    power only (Kummer: one carry).  Compare sizes: `C(n,k) ≥ C(n,2)`
    grows quadratically while the number of primes in `(n/2, n]` with a
    single power each is too small for small `k`; Ecklund's argument is
    an elementary case analysis on `k = 2, 3` plus an induction using
    `C(n,k) = C(n-1,k-1)·n/k`.  Mathlib tools: `Nat.Prime.dvd_choose`,
    `Nat.choose_symm`, `padicValNat.choose` (Kummer),
    `Nat.exists_prime_lt_and_le_two_mul` (Bertrand for the base range).
    Effort S per candidates audit. -/
theorem ecklund (n k : ℕ) (hk : 2 ≤ k) (hkn : 2 * k ≤ n)
    (hexc : ¬(n = 7 ∧ k = 3)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  sorry

/-- The corrected non-strict Ecklund variant in the DB-headline range `1 < k < n - 1`, via `C(n,k) = C(n,n-k)`:
    both `C(7,3)` and `C(7,4)` are exceptions.  Follows from `ecklund`
    plus `Nat.choose_symm`.  -- PROVABLE once `ecklund` lands. -/
theorem erdos_384_db_range (n k : ℕ) (hk1 : 1 < k) (hk2 : k < n - 1)
    (hexc : ¬(n = 7 ∧ (k = 3 ∨ k = 4))) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  by_cases hhalf : 2 * k ≤ n
  · exact ecklund n k (by omega) hhalf (fun h => hexc ⟨h.1, Or.inl h.2⟩)
  · have hkn : k ≤ n := by omega
    obtain ⟨p, hp, hdvd, hbound⟩ :=
      ecklund n (n - k) (by omega) (by omega) (fun h => hexc ⟨h.1, Or.inr (by omega)⟩)
    rw [Nat.choose_symm hkn] at hdvd
    exact ⟨p, hp, hdvd, hbound⟩

/-- Sanity window: Ecklund's statement verified for all `n ≤ 30`,
    `2 ≤ k`, `2k ≤ n`, `(n,k) ≠ (7,3)` by kernel computation.
    -- PROVABLE (decide; the search space is tiny). -/
theorem ecklund_window_30 :
    ∀ n ∈ Finset.range 31, ∀ k ∈ Finset.range 16,
      2 ≤ k → 2 * k ≤ n → ¬(n = 7 ∧ k = 3) →
      ∃ p ∈ (n.choose k).primeFactors, 2 * p ≤ n := by
  have hfinite : ∀ n ∈ Finset.range 31, ∀ k ∈ Finset.range 16,
      2 ≤ k → 2 * k ≤ n → ¬(n = 7 ∧ k = 3) →
      ∃ p ∈ Finset.range 16,
        p.Prime ∧ p ∣ n.choose k ∧ n.choose k ≠ 0 ∧ 2 * p ≤ n := by
    simp_rw [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  intro n hn k hk hk2 hkn hexc
  obtain ⟨p, _, hp, hdvd, hne, hbound⟩ := hfinite n hn k hk hk2 hkn hexc
  exact ⟨p, hp.mem_primeFactors hdvd hne, hbound⟩

/-- The exception really is an exception: no prime `p ≤ 3` divides
    `C(7,3) = 35`.  Guards against a vacuous main statement.
    -- PROVABLE (decide). -/
theorem exceptional_prime_window : ∀ p ∈ (Nat.choose 7 3).primeFactors, ¬(2 * p ≤ 7) := by
  rw [choose_seven_three_sanity.2]
  decide

/- RETIRED (false as stated; refuted by `ecklund_conjecture_strong_false`).
   Original text:

/-- Ecklund's stronger conjecture (recorded in the DB remarks; still
    open): if `k^2 < n` then `C(n,k)` has a prime factor `p` with
    `p * k ≤ n`.  OPEN — archived here for the lane; see also #1094.
    (Selfridge's variant in Guy B31: `n > 17.125k` suffices for
    `p ≤ n/k`.) -/
theorem ecklund_conjecture_strong (n k : ℕ) (hk : 2 ≤ k) (hn : k ^ 2 < n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ p * k ≤ n := by
  sorry
-/

/-- Ground truth: `C(62,6) = 61474519 = 19·29·31·59·61`. -/
theorem choose_sixty_two_six : Nat.choose 62 6 = 61474519 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- **Refutation of the retired `ecklund_conjecture_strong`.**
    The original claim read: "if `2 ≤ k` and `k^2 < n` then `C(n,k)`
    has a prime factor `p` with `p * k ≤ n`".  It fails at
    `(n, k) = (62, 6)`: `6^2 = 36 < 62`, but
    `C(62,6) = 61474519 = 19·29·31·59·61`, and the only primes with
    `6p ≤ 62` are `2, 3, 5, 7`, none of which divides `C(62,6)`.
    The discrepancy is with the source: the DB remark on #384 paraphrases
    Ecklund's conjecture without its exception, while #1094 records
    Selfridge's form [Se77] "for `n ≥ k^2 - 1`, except `C(62,6)`", and
    `C(62,6)` is also among the 14 exceptions listed by
    Erdős–Lacampagne–Selfridge [ELS88].  A Python search (2026-10-21)
    found `(62,6)` to be the only failure for `n < 400`. -/
theorem ecklund_conjecture_strong_false :
    ¬ ∀ n k : ℕ, 2 ≤ k → k ^ 2 < n →
      ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ p * k ≤ n := by
  intro h
  obtain ⟨p, hp, hdvd, hle⟩ := h 62 6 (by norm_num) (by norm_num)
  rw [choose_sixty_two_six] at hdvd
  have hp10 : p ≤ 10 := by omega
  interval_cases p <;> revert hp hdvd <;> decide

/-- **Ecklund's stronger conjecture, corrected (OPEN).**  If `2 ≤ k`,
    `k^2 < n` and `(n, k) ≠ (62, 6)`, then `C(n,k)` has a prime factor
    `p` with `p * k ≤ n` (i.e. `p ≤ n/k`).  This is the
    Ecklund–Eggleton–Erdős–Selfridge conjecture with its documented
    exception `C(62,6)` (Selfridge [Se77], recorded in Erdős #1094;
    Selfridge states it already for `n ≥ k^2 - 1`).  The `sorry` marks an
    open problem, not a missing routine step; see
    `ecklund_conjecture_strong_false` for why the exception is needed.
    (Selfridge's variant in Guy B31: `n > 17.125k` suffices for
    `p ≤ n/k`.) -/
theorem ecklund_conjecture_strong_corrected (n k : ℕ) (hk : 2 ≤ k) (hn : k ^ 2 < n)
    (hexc : ¬(n = 62 ∧ k = 6)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ p * k ≤ n := by
  sorry

end ErdosCandidates.E384

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Disposition: corrected Ecklund variant, NOT headline unchanged; admitted
   - DB headline says "p < n/2" (strict); file uses "2*p ≤ n" (non-strict, i.e. p ≤ n/2). The correction is justified by JoshuaB comment (post-4157): Ecklund's actual theorem has p ≤ n/2.
   - DB headline range "1 < k < n-1" vs Ecklund's "n ≥ 2k": file uses the Ecklund form as main theorem and derives the DB range as a corollary with both exceptions {(7,3),(7,4)}. Faithful.
   - C(7,3) = 35 = 5*7 verified; both 5 > 3.5 and 7 > 3.5, so no prime ≤ 7/2 divides it. Exception confirmed.
   - Solver attribution Ecklund [Ec69] matches DB.
   - `Nat.choose` is the correct Mathlib definition for binomial coefficients.
   - Stronger conjecture `k^2 < n → ∃ p, p*k ≤ n` matches DB remark on Ecklund's conjecture.
   - UPDATE 2026-10-21: that DB remark omits the exception C(62,6); the
     unguarded form is refuted (`ecklund_conjecture_strong_false`) and the
     corrected open form is `ecklund_conjecture_strong_corrected`.
   - `ecklund_window_30` arithmetic is within kernel-decidable range.
-/

