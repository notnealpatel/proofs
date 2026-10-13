/-
  Erdős Problem #1062 — largest subset of [1, n] with no element
  dividing two others.
  Status: open.  Tier UA attack target (lower bound slice).

  Verbatim statement (`goof erdos fetch 1062`, pulled 2026-08-05):

    "Let $f(n)$ be the size of the largest subset
    $A\subseteq \{1,\ldots,n\}$ such that there are no three distinct
    elements $a,b,c\in A$ such that $a\mid b$ and $a\mid c$. How large
    can $f(n)$ be? Is $\lim f(n)/n$ irrational?"

  DB remarks: the interval `[m+1, 3m+2]` shows f(n) ≥ ⌈2n/3⌉ (ceiling
  per Yongxi Lin's comment; Guy B24).  Lebensold [Le76]: for large n,
  0.6725·n ≤ f(n) ≤ 0.6736·n.  Damek Davis (Apr 2026, comment-sourced,
  arXiv tba): f(n) = c₂n + o(n) with c₂ effectively computable via
  McNew's divisor-graph machinery; irrationality of c₂ remains open.
  OEIS A038372 (pulled 2026-08-05): 1, 2, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8,
  9, 10, 10, 11, 12, 12, 13, 14, 14, …

  Mathlib inventory (leandoc 2026-08-05): `Finset.Icc`, `Nat.instDvd`;
  the extremal quantity is a `Finset.sup` over admissible subsets
  (decidable predicate, computable sup).  No divisor-graph machinery in
  Mathlib; not needed for the statement.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1062

/-- `NoDivFork A`: no three distinct elements `a, b, c` of `A` satisfy
    `a ∣ b` and `a ∣ c` ("fork" at `a`).  This is the constraint of the
    problem. -/
def NoDivFork (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    ¬(a ∣ b ∧ a ∣ c)

instance (A : Finset ℕ) : Decidable (NoDivFork A) := by
  unfold NoDivFork; infer_instance

/-- `f n`: the size of the largest fork-free subset of `{1, …, n}`
    (A038372).  Computable: sup of cards over the filtered powerset. -/
def f (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter NoDivFork).sup Finset.card

/-- Ground truth against A038372 prefix 1, 2, 2, 3, 4, 4, 5, 6, 6.
    -- PROVABLE (decide; n ≤ 6 is cheap, n ≤ 9 borderline kernel). -/
example : f 1 = 1 ∧ f 2 = 2 ∧ f 3 = 2 ∧ f 4 = 3 ∧ f 5 = 4 ∧ f 6 = 4 := by
  set_option maxRecDepth 4096 in
    decide

example : NoDivFork {1} := by decide

example : f 0 = 0 := by decide

example : f 1 = 1 := by decide

/-- The interval `[⌊n/3⌋+1, n]` is fork-free: if `a ∣ b`, `a ∣ c` with
    `a < b < c` all in the interval then `c ≥ 3a > n`, contradiction.
    The witness behind the lower bound.  -- PROVABLE (elementary). -/
theorem noDivFork_interval (n : ℕ) :
    NoDivFork (Finset.Icc (n / 3 + 1) n) := by
  intro a ha b hb c hc hab hac hbc hdiv
  obtain ⟨ha_lower, ha_upper⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb_lower, hb_upper⟩ := Finset.mem_Icc.mp hb
  obtain ⟨hc_lower, hc_upper⟩ := Finset.mem_Icc.mp hc
  have ha_pos : 0 < a := by omega
  have hthree : n < 3 * a := by omega
  obtain ⟨u, hu⟩ := hdiv.1
  obtain ⟨v, hv⟩ := hdiv.2
  have hu_two : 2 ≤ u := by
    by_contra h
    have hu_cases : u = 0 ∨ u = 1 := by omega
    rcases hu_cases with hu_zero | hu_one
    · simp only [hu_zero, Nat.mul_zero] at hu
      omega
    · simp only [hu_one, Nat.mul_one] at hu
      exact hab hu.symm
  have hv_two : 2 ≤ v := by
    by_contra h
    have hv_cases : v = 0 ∨ v = 1 := by omega
    rcases hv_cases with hv_zero | hv_one
    · simp only [hv_zero, Nat.mul_zero] at hv
      omega
    · simp only [hv_one, Nat.mul_one] at hv
      exact hac hv.symm
  have huv : u ≠ v := by
    intro heq
    exact hbc (hu.trans (heq ▸ hv.symm))
  have hlarge : 3 ≤ u ∨ 3 ≤ v := by omega
  rcases hlarge with hu_three | hv_three
  · have hmul := Nat.mul_le_mul_left a hu_three
    rw [← hu] at hmul
    omega
  · have hmul := Nat.mul_le_mul_left a hv_three
    rw [← hv] at hmul
    omega

/-- **Lower bound slice (the Tier-UA target)**: `f(n) ≥ ⌈2n/3⌉`, via the
    interval witness above.  Ceiling encoded as `(2 * n + 2) / 3` in ℕ
    (equals ⌈2n/3⌉; guard: `Nat.add_mul_div_left` arithmetic).
    Elementary divisibility-poset reasoning; effort S. -/
theorem f_lower_bound (n : ℕ) : (2 * n + 2) / 3 ≤ f n := by
  have hsubset : Finset.Icc (n / 3 + 1) n ⊆ Finset.Icc 1 n := by
    intro a ha
    obtain ⟨ha_lower, ha_upper⟩ := Finset.mem_Icc.mp ha
    exact Finset.mem_Icc.mpr ⟨by omega, ha_upper⟩
  have hmem : Finset.Icc (n / 3 + 1) n ∈
      (Finset.Icc 1 n).powerset.filter NoDivFork := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hsubset, noDivFork_interval n⟩
  have hcard : (Finset.Icc (n / 3 + 1) n).card = (2 * n + 2) / 3 := by
    rw [Nat.card_Icc]
    omega
  rw [← hcard]
  exact Finset.le_sup hmem

/-- **Lebensold's bounds** (Le76), archived: for sufficiently large `n`,
    `0.6725·n ≤ f(n) ≤ 0.6736·n`.  Rational constants; stated over ℚ to
    avoid ℝ-cast noise.  The proof is a finite computation with
    Lebensold's recursive method — feasible in principle but not
    scoped here. -/
theorem lebensold_bounds :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (6725 : ℚ) / 10000 * n ≤ (f n : ℚ) ∧
      (f n : ℚ) ≤ (6736 : ℚ) / 10000 * n := by
  sorry

/-- **Existence of the density limit** (Davis 2026, comment-sourced —
    claims f(n) = c₂n + o(n) via McNew's divisor-graph local statistics;
    not yet refereed).  Archived: the limit `f(n)/n` exists.  The
    irrationality of the limit is OPEN and not formalized (no way to
    state it without the constant; would need the sInf/limit value
    itself). -/
theorem density_limit_exists :
    ∃ c : ℝ, Filter.Tendsto (fun n => (f n : ℝ) / n) Filter.atTop
      (nhds c) := by
  sorry

/-- Sanity: monotonicity `f n ≤ f (n+1)` and the trivial bound
    `f n ≤ n`.  -- PROVABLE (sup-mono + card bounds). -/
theorem f_mono_le (n : ℕ) : f n ≤ f (n + 1) ∧ f n ≤ n := by
  constructor
  · apply Finset.sup_le_iff.mpr
    intro A hA
    obtain ⟨hA_power, hA_fork⟩ := Finset.mem_filter.mp hA
    have hA_subset := Finset.mem_powerset.mp hA_power
    have hA_next : A ⊆ Finset.Icc 1 (n + 1) := by
      intro a ha
      obtain ⟨ha_lower, ha_upper⟩ := Finset.mem_Icc.mp (hA_subset ha)
      exact Finset.mem_Icc.mpr ⟨ha_lower, by omega⟩
    exact Finset.le_sup (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hA_next, hA_fork⟩)
  · apply Finset.sup_le_iff.mpr
    intro A hA
    have hA_subset := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
    calc
      A.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hA_subset
      _ = n := by rw [Nat.card_Icc]; omega

end ErdosCandidates.E1062

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS-WITH-FLAGS
   - Verbatim statement matches DB pull exactly.
   - NoDivFork correctly encodes "no three distinct a,b,c with a|b and a|c" via
     universal quantification over all ordered triples with distinctness.
   - A038372 prefix 1,2,2,3,4,4,5,6,6,7,8,8 verified against OEIS pull.
   - Ceiling encoding (2*n+2)/3 = ceil(2n/3) verified for n in 1..14.
   - Lebensold bounds 0.6725, 0.6736 match DB body exactly.
   - Davis density limit correctly flagged comment-sourced; DB confirms "arxiv tba",
     unrefereed. File says "not yet refereed" — faithful.
   - FLAG (minor): f_mono_le claims f n <= n, but f n counts a subset of {1,...,n}
     which has n elements, so the sup of cards is indeed <= n. However, f 0 = 0 and
     0 <= 0 = n is fine. No issue.
   - FLAG (minor): the interval witness [n/3+1, n] in noDivFork_interval uses ℕ
     division n/3; for n=0 this gives Icc 1 0 = empty, which is trivially fork-free
     but the lower bound f_lower_bound at n=0 gives (0+2)/3=0 <= f 0 = 0, which is
     fine. No vacuousness bug.
-/
