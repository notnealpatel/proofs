/-
  Erdős Problem #1094 — the least prime factor of C(n,k).
  Status: open.  Tier UB archive target with decidable exception list.

  Verbatim statement (`goof erdos fetch 1094`, pulled 2026-08-05):

    "For all $n\geq 2k$ the least prime factor of $\binom{n}{k}$ is
    $\leq \max(n/k,k)$, with only finitely many exceptions."

  DB remarks: a stronger form of #384 from [ELS88].  Erdős: least
  prime factor ≤ n/k for n large in terms of k.  Selfridge [Se77]:
  conjecturally ≤ n/k once n ≥ k² − 1, except C(62,6).  ELS88
  conjecture: ≤ max(n/k, k) for n ≥ 2k with exactly 14 exceptions:
  C(7,3), C(13,4), C(23,5), C(14,4), C(44,8), C(46,10), C(47,10),
  C(47,11), C(62,6), C(74,10), C(94,10), C(95,10), C(241,16),
  C(284,28).  ELS93: possibly ≤ max(n/k, 13) with only 12 exceptions.
  Related to #1093 (counterexamples need deficiency ≥ 1).

  Formalization: least prime factor = `Nat.minFac` (Mathlib; junk:
  minFac 1 = 1, minFac 0 = 2 — binomials in range are ≥ 2 except the
  guard degeneracies, handled by `2 ≤ k` hypotheses).  `n/k ≤ …`
  encoded multiplicatively.

  Mathlib inventory: `Nat.minFac`, `Nat.choose`.  Hygiene note from
  the candidates doc honored: no Frankl-bound content here (that was
  #1020 cross-contamination).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1094

/-- The 14 ELS88 exceptional pairs `(n, k)`. -/
def exceptions : Finset (ℕ × ℕ) :=
  { (7, 3), (13, 4), (23, 5), (14, 4), (44, 8), (46, 10), (47, 10),
    (47, 11), (62, 6), (74, 10), (94, 10), (95, 10), (241, 16),
    (284, 28) }

/-- `SmallLeastFactor n k`: the least prime factor of `C(n,k)` is at
    most `max(n/k, k)`, encoded division-free:
    `minFac(C(n,k)) ≤ k ∨ minFac(C(n,k)) * k ≤ n`. -/
def SmallLeastFactor (n k : ℕ) : Prop :=
  (n.choose k).minFac ≤ k ∨ (n.choose k).minFac * k ≤ n

/-- The least-factor bound holds for C(10,4), but fails for C(62,6). -/
theorem smallLeastFactor_sanity :
    SmallLeastFactor 10 4 ∧ ¬ SmallLeastFactor 62 6 := by
  have h10 : Nat.choose 10 4 = 210 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  have h62 : Nat.choose 62 6 = 61474519 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  have hmin10 : Nat.minFac 210 = 2 := by decide
  have hmin62 : Nat.minFac 61474519 = 19 := by norm_num
  unfold SmallLeastFactor
  rw [h10, h62, hmin10, hmin62]
  decide

/-- Ground truth: C(10,4) = 210 has minFac 2 ≤ 4 ✓; the exception
    C(62,6): C(62,6) = 61474519, whose least prime factor is 19, and
    19 > 6 with 19·6 = 114 > 62 — genuinely exceptional. -/
example : SmallLeastFactor 10 4 ∧ ¬ SmallLeastFactor 62 6 := by
  exact smallLeastFactor_sanity

/-- **Erdős #1094 (OPEN)**: for all `n ≥ 2k`, `k ≥ 2`, outside the 14
    listed exceptions, the least prime factor of `C(n,k)` is
    `≤ max(n/k, k)`.

    Source text: "For all $n\geq 2k$ the least prime factor of
    $\binom{n}{k}$ is $\leq \max(n/k,k)$, with only finitely many
    exceptions."  The DB's "finitely many" is conjecturally EXACTLY
    the 14 pairs (ELS88); we state the strong exact-list form (the
    literal finiteness form is `erdos_1094_finiteness` below). -/
theorem erdos_1094_exact (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (hexc : (n, k) ∉ exceptions) :
    SmallLeastFactor n k := by
  sorry

/-- The literal statement: finitely many exceptions.  Implied by
    `erdos_1094_exact`; kept as the faithful weak form. -/
theorem erdos_1094_finiteness :
    {q : ℕ × ℕ | 2 ≤ q.2 ∧ 2 * q.2 ≤ q.1 ∧
      ¬ SmallLeastFactor q.1 q.2}.Finite := by
  sorry

/-- Search `d, d+1, …` (`f` steps) for a divisor of `c` witnessing the bound. -/
private def findWit (c n k : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => (c % d == 0 && (decide (d ≤ k) || decide (d * k ≤ n))) || findWit c n k f (d + 1)

/-- Soundness of `findWit`: success yields a divisor `e ≥ 2` of `c` with `e ≤ k ∨ e*k ≤ n`. -/
private theorem findWit_sound (c n k : ℕ) :
    ∀ f d, 2 ≤ d → findWit c n k f d = true →
      ∃ e, 2 ≤ e ∧ e ∣ c ∧ (e ≤ k ∨ e * k ≤ n) := by
  intro f
  induction f with
  | zero => intro d _ h; simp [findWit] at h
  | succ f ih =>
    intro d hd h
    simp only [findWit, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with ⟨hmod, hb⟩ | h
    · exact ⟨d, hd, Nat.dvd_of_mod_eq_zero hmod, hb⟩
    · exact ih (d + 1) (by omega) h

/-- Row checker: `c` is meant to be `n.choose k`. -/
private def rowOK (n : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | f + 1, k, c =>
    (decide (k < 2) || decide (n < 2 * k) || findWit c n k n 2 || decide ((n, k) ∈ exceptions))
      && rowOK n f (k + 1) (c * (n - k) / (k + 1))

/-- Checks `rowOK` for every row `n < m`. -/
private def allOK : ℕ → Bool
  | 0 => true
  | m + 1 => rowOK m 151 0 1 && allOK m

set_option maxRecDepth 100000 in
/-- Kernel-checked sweep: every row `n ≤ 300` passes `rowOK`. -/
private theorem allOK_301 : allOK 301 = true := by decide +kernel

/-- A `findWit` success for `C(n,k)` gives `SmallLeastFactor n k`. -/
private theorem smallLeastFactor_of_findWit (n k : ℕ) (h : findWit (n.choose k) n k n 2 = true) :
    SmallLeastFactor n k := by
  obtain ⟨e, he2, hdvd, hb⟩ := findWit_sound (n.choose k) n k n 2 le_rfl h
  have hmin : (n.choose k).minFac ≤ e := Nat.minFac_le_of_dvd he2 hdvd
  rcases hb with hb | hb
  · exact Or.inl (hmin.trans hb)
  · exact Or.inr ((Nat.mul_le_mul_right k hmin).trans hb)

/-- Soundness of `rowOK` when the accumulator equals `C(n,k)`. -/
private theorem rowOK_sound (n : ℕ) :
    ∀ f k c, rowOK n f k c = true → c = n.choose k →
      ∀ j, k ≤ j → j < k + f → 2 ≤ j → 2 * j ≤ n → (n, j) ∉ exceptions →
        SmallLeastFactor n j := by
  intro f
  induction f with
  | zero => intro k c _ _ j h1 h2; omega
  | succ f ih =>
    intro k c h hc j hkj hjk hj2 hjn hexc
    simp only [rowOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hhead, hrest⟩ := h
    rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
    · subst hc
      rcases hhead with ((h | h) | h) | h
      · omega
      · omega
      · exact smallLeastFactor_of_findWit n k h
      · exact absurd h hexc
    · have hnext : c * (n - k) / (k + 1) = n.choose (k + 1) := by
        rw [hc, ← Nat.choose_succ_right_eq]
        exact Nat.mul_div_cancel _ (Nat.succ_pos k)
      exact ih (k + 1) _ hrest hnext j hlt (by omega) hj2 hjn hexc

/-- Soundness of `allOK`: all non-exceptional pairs in range satisfy the bound. -/
private theorem allOK_sound :
    ∀ m, allOK m = true → ∀ n < m, ∀ k < 151, 2 ≤ k → 2 * k ≤ n → (n, k) ∉ exceptions →
      SmallLeastFactor n k := by
  intro m
  induction m with
  | zero => intro _ n hn; omega
  | succ m ih =>
    intro h n hn k hk h2 h2k hexc
    simp only [allOK, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | rfl
    · exact ih h.2 n hlt k hk h2 h2k hexc
    · exact rowOK_sound n 151 0 1 h.1 (Nat.choose_zero_right n).symm k (Nat.zero_le k)
        (by omega) h2 h2k hexc

/-- No `d ∈ [2, B]` divides `c`. -/
private def noSmallFactor (c B : ℕ) : Bool :=
  (List.range' 2 (B - 1)).all (fun d => c % d != 0)

/-- If no `d ∈ [2,B]` divides `c ≠ 1`, then `B < minFac c`. -/
private theorem lt_minFac_of_noSmallFactor (c B : ℕ) (hc : c ≠ 1) (h : noSmallFactor c B = true) :
    B < c.minFac := by
  by_contra hle
  rw [not_lt] at hle
  have h2 : 2 ≤ c.minFac := (Nat.minFac_prime hc).two_le
  simp only [noSmallFactor, List.all_eq_true, List.mem_range', bne_iff_ne, ne_eq] at h
  obtain ⟨i, hi, hd⟩ : ∃ i, i < B - 1 ∧ c.minFac = 2 + 1 * i := ⟨c.minFac - 2, by omega, by omega⟩
  exact h c.minFac ⟨i, hi, hd⟩ (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd c))

/-- Exception certificate for `(n, k)`. -/
private def excCheck (n k : ℕ) : Bool :=
  let c := n.descFactorial k / k.factorial
  decide (2 ≤ c) && decide (1 ≤ k) && noSmallFactor c (max k (n / k))

/-- A passing `excCheck` certifies that `(n,k)` violates the bound. -/
private theorem not_smallLeastFactor_of_excCheck (n k : ℕ) (h : excCheck n k = true) :
    ¬ SmallLeastFactor n k := by
  simp only [excCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc2, hk⟩, hns⟩ := h
  rw [← Nat.choose_eq_descFactorial_div_factorial] at hc2 hns
  have hlt := lt_minFac_of_noSmallFactor _ _ (by omega) hns
  have hk' : k < (n.choose k).minFac := lt_of_le_of_lt (le_max_left _ _) hlt
  have hnk : n / k < (n.choose k).minFac := lt_of_le_of_lt (le_max_right _ _) hlt
  have hmul : n < (n.choose k).minFac * k := (Nat.div_lt_iff_lt_mul hk).mp hnk
  unfold SmallLeastFactor
  omega

/-- All 14 exceptions really are exceptions.
    -- PROVABLE (decide; the largest is C(284,28) ≈ 10³⁵ — minFac of a
    35-digit number whose least factor is moderate; kernel-feasible,
    else native_decide). -/
theorem exceptions_are_exceptional :
    ∀ q ∈ exceptions, ¬ SmallLeastFactor q.1 q.2 := by
  intro q hq
  apply not_smallLeastFactor_of_excCheck
  simp only [exceptions, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- Verified window: no exceptions outside the list with `n ≤ 300`.
    -- PROVABLE (decide/native_decide sweep). -/
theorem window_300 :
    ∀ n ∈ Finset.range 301, ∀ k ∈ Finset.range 151,
      2 ≤ k → 2 * k ≤ n → (n, k) ∉ exceptions →
      SmallLeastFactor n k := by
  intro n hn k hk
  exact allOK_sound 301 allOK_301 n (Finset.mem_range.mp hn) k (Finset.mem_range.mp hk)

/-- **Selfridge's refinement** ([Se77], archived): once `k² − 1 ≤ n`
    (stated additively `k² ≤ n + 1`), the least prime factor is
    `≤ n/k` — no `max` needed — except C(62,6). -/
theorem selfridge_refinement (n k : ℕ) (hk : 2 ≤ k) (hn : k ^ 2 ≤ n + 1)
    (hexc : ¬(n = 62 ∧ k = 6)) :
    (n.choose k).minFac * k ≤ n := by
  sorry

end ErdosCandidates.E1094

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Statement matches DB verbatim (re-pulled 2026-08-05).
   - 14 exception pairs match DB list exactly (order preserved).
   - Division-free encoding: minFac <= k \/ minFac * k <= n faithfully
     encodes minFac <= max(n/k, k) for k > 0. Sound.
   - C(62,6)=61474519: factorization 19*29*31*59*61, minFac=19. 19 > 6
     and 19*6=114 > 62 -- genuinely exceptional. Correct.
   - C(10,4)=210, minFac=2 <= 4. SmallLeastFactor holds. Correct.
   - Selfridge refinement: DB says "n >= k^2 - 1 except C(62,6)".
     File encodes as k^2 <= n+1 (equivalent). Correct.
   - ELS93 stronger conjecture (max(n/k, 13) with 12 exceptions) mentioned
     in DB but not formalized -- no fidelity issue.
-/
