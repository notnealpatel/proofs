/-
  Erdős Problem #1100 — coprime consecutive divisors.
  Status: open.  Tier UC lemma mine (τ⊥ decidable; trivial bounds and
  small tables immediate).

  Verbatim statement (`goof erdos fetch 1100`, pulled 2026-08-05):

    "If $1=d_1<\cdots<d_{\tau(n)}=n$ are the divisors of $n$, then
    let $\tau_\perp(n)$ count the number of $i$ for which
    $(d_i,d_{i+1})=1$.

    Is it true that $\tau_\perp(n)/\omega(n)\to \infty$ for almost
    all $n$? Is it true that
    \[\tau_\perp(n)< \exp((\log n)^{o(1)})\]for all $n$?

    Let\[g(k) = \max_{\omega(n)=k}\tau_\perp(n),\]
    where $\omega(n)$ counts the number of distinct prime divisors of
    $n$, and $n$ is restricted to squarefree integers. Determine the
    growth of $g(k)$."

  DB remarks (Erdős–Hall [ErHa78]): trivially τ⊥(n) ≥ ω(n) (equality
  infinitely often).  Erdős–Hall: max_{n<x} τ⊥(n) >
  exp((log log x)^{2−ε}).  Erdős–Simonovits (see [Er81h]):
  (√2 + o(1))^k < g(k) < (2 − c)^k over squarefree n.

  ⚠ OEIS mismatch note: the DB's `goof erdos list` metadata links
  A325864, whose OEIS name is "Number of subsets of {1..n} of which
  every subset has a different sum" — unrelated to τ⊥ on its face.
  Do not use A325864 as ground truth without resolving the mismatch
  (possibly a DB metadata error).

  Repo adjacency: `Proofs/Erdos/Erdos542/SchinzelSzekeres.lean`
  (divisor-structure work).  Mathlib: `Nat.divisors`, sorted lists as
  in the E673 sketch, `Nat.primeFactors.card` for ω.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1100

/-- The increasing list of divisors of `n` (shared shape with the
    E673 sketch). -/
def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

/-- `tauPerp n`: the number of adjacent coprime pairs in the sorted
    divisor list — the `τ⊥(n)` of the problem. -/
def tauPerp (n : ℕ) : ℕ :=
  (List.zipWith (fun a b => decide (Nat.gcd a b = 1)) (divisorList n)
    (divisorList n).tail).count true

/-- At 12 the adjacent coprime divisor count is three and there are two distinct prime factors. -/
theorem tauPerp_twelve_and_primeFactors_card :
    tauPerp 12 = 3 ∧ (12 : ℕ).primeFactors.card = 2 := by
  have hdivisors : (12 : ℕ).divisors = [1, 2, 3, 4, 6, 12].toFinset := by
    rw [← Nat.filter_dvd_eq_divisors (by decide : (12 : ℕ) ≠ 0)]
    decide
  have hlist : divisorList 12 = [1, 2, 3, 4, 6, 12] := by
    unfold divisorList
    rw [hdivisors]
    exact (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)
  unfold tauPerp
  rw [hlist]
  unfold Nat.primeFactors Nat.primeFactorsList
  decide +kernel

/-- Ground truth: divisors of 12: 1,2,3,4,6,12 — adjacent gcds:
    (1,2)=1 ✓, (2,3)=1 ✓, (3,4)=1 ✓, (4,6)=2, (6,12)=6 → τ⊥(12) = 3.
    ω(12) = 2.  -- PROVABLE (decide). -/
example : tauPerp 12 = 3 ∧ (12 : ℕ).primeFactors.card = 2 := by
  exact tauPerp_twelve_and_primeFactors_card

/-- Every element of the tail of a list is the second entry of some
    adjacent pair `(y, x)` in `l.zip l.tail`. -/
private theorem exists_mem_zip_tail_of_mem_tail {α : Type*} :
    ∀ (l : List α) (x : α), x ∈ l.tail → ∃ y, (y, x) ∈ l.zip l.tail
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: r, x, h => by
    rcases List.mem_cons.1 h with hxb | hxr
    · exact ⟨a, by simp [hxb]⟩
    · obtain ⟨y, hy⟩ := exists_mem_zip_tail_of_mem_tail (b :: r) x hxr
      exact ⟨y, by simp only [List.tail_cons, List.zip_cons_cons] at hy ⊢; simp [hy]⟩

/-- In a list pairwise related by `R`, every adjacent pair `(a, b)` from
    `l.zip l.tail` satisfies `R a b`. -/
private theorem rel_of_mem_zip_tail {α : Type*} {R : α → α → Prop} :
    ∀ (l : List α), l.Pairwise R → ∀ a b, (a, b) ∈ l.zip l.tail → R a b
  | [], _, _, _, h => by simp at h
  | [_], _, _, _, h => by simp at h
  | c :: d :: r, hl, a, b, h => by
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact List.rel_of_pairwise_cons hl (by simp)
    · exact rel_of_mem_zip_tail (d :: r) hl.of_cons a b (by simpa using h)

/-- **Trivial lower bound (first landing)**: `ω(n) ≤ τ⊥(n)` for
    `n ≥ 2` — below each prime power block boundary the divisors
    p·(largest divisor composed of smaller primes)… Erdős–Hall's
    observation: for each prime p ∣ n, the divisor just before p in
    the sorted list is coprime to p — wait, the clean classical
    argument: for each p ∣ n the pair (d, d') straddling where p
    first appears is coprime; formalize via the p-adic jump.
    Effort M (the combinatorial argument needs care).  -/
theorem omega_le_tauPerp (n : ℕ) (hn : 2 ≤ n) :
    n.primeFactors.card ≤ tauPerp n := by
  classical
  set l := divisorList n with hl_def
  have hn0 : n ≠ 0 := by omega
  have hsorted : l.Pairwise (· < ·) := (Finset.sortedLT_sort n.divisors).pairwise
  have hmem : ∀ d, d ∈ l ↔ d ∣ n := fun d => by
    simp [hl_def, divisorList, Finset.mem_sort, Nat.mem_divisors, hn0]
  set L := (l.zip l.tail).filter (fun q => decide (Nat.gcd q.1 q.2 = 1)) with hL_def
  have hcount : tauPerp n = L.length := by
    rw [tauPerp, ← hl_def, ← List.map_uncurry_zip_eq_zipWith, List.count_eq_countP,
      List.countP_map, List.countP_eq_length_filter, hL_def]
    congr 1
    apply List.filter_congr
    intro q _
    simp [Function.uncurry]
  -- every prime factor `p` is the right end of an adjacent coprime pair
  have hsub : n.primeFactors ⊆ L.toFinset.image Prod.snd := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpl : p ∈ l := (hmem p).2 hpn
    have h1l : 1 ∈ l := (hmem 1).2 (one_dvd n)
    have hptail : p ∈ l.tail := by
      cases hlc : l with
      | nil => simp [hlc] at hpl
      | cons a t =>
        rw [hlc] at hpl h1l hsorted
        rcases List.mem_cons.1 hpl with hpa | hpt
        · exfalso
          rcases List.mem_cons.1 h1l with h1a | h1t
          · exact hpp.one_lt.ne' (hpa.trans h1a.symm)
          · have ha1 : a < 1 := List.rel_of_pairwise_cons hsorted h1t
            have hp1 : 1 < p := hpp.one_lt
            omega
        · simpa using hpt
    obtain ⟨a, ha⟩ := exists_mem_zip_tail_of_mem_tail l p hptail
    have hap : a < p := rel_of_mem_zip_tail l hsorted a p ha
    have hal : a ∈ l := (List.of_mem_zip ha).1
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, hmem] at hal
      exact hn0 (Nat.eq_zero_of_zero_dvd hal)
    have hcop : Nat.gcd a p = 1 := (Nat.coprime_of_lt_prime ha0 hap hpp).symm
    rw [Finset.mem_image]
    exact ⟨(a, p), by simp [hL_def, ha, hcop], rfl⟩
  calc n.primeFactors.card ≤ (L.toFinset.image Prod.snd).card := Finset.card_le_card hsub
    _ ≤ L.toFinset.card := Finset.card_image_le
    _ ≤ L.length := List.toFinset_card_le L
    _ = tauPerp n := hcount.symm

/-- **Erdős #1100, question 1 (OPEN)**: `τ⊥(n)/ω(n) → ∞` for almost
    all `n` (density form). -/
theorem erdos_1100_q1 (M : ℕ) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.Icc 2 X).filter
          (fun n => tauPerp n ≤ M * n.primeFactors.card)).card : ℝ) / X)
      Filter.atTop (nhds 0) := by
  sorry

/-- **Erdős #1100, question 2 (OPEN)**: `τ⊥(n) < exp((log n)^{o(1)})`
    for all `n` — ε-form: for every `ε > 0`, eventually
    `τ⊥(n) < exp((log n)^ε)`. -/
theorem erdos_1100_q2 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (tauPerp n : ℝ) < Real.exp (Real.log n ^ ε) := by
  sorry

/-- `gPerp k`: max of τ⊥ over squarefree `n` with `ω(n) = k` — the
    `g(k)` of the third question.  (Well-defined: τ⊥(n) ≤ τ(n) = 2^k
    over squarefree n with ω(n) = k, so the sup is finite; encoded as
    an sSup over the value set.) -/
noncomputable def gPerp (k : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ n : ℕ, Squarefree n ∧ n.primeFactors.card = k ∧
    tauPerp n = t}

/-- **Erdős–Simonovits bounds** ([Er81h]), archived:
    `(√2 + o(1))^k < g(k) < (2 − c)^k`.  Stated as: for some c > 0
    and large k, `2^{k/2} ≤ g(k) ≤ (2 − c)^k`. -/
theorem erdos_simonovits_bounds :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (gPerp k : ℝ) ∧
      (gPerp k : ℝ) ≤ (2 - c) ^ (k : ℝ) := by
  sorry

/-- **Erdős–Hall max-order bound** ([ErHa78]), archived: for every
    `ε > 0` and large `x`, some `n < x` has
    `τ⊥(n) > exp((log log x)^{2−ε})`. -/
theorem erdos_hall_max_order (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, n < x ∧
        Real.exp (Real.log (Real.log x) ^ (2 - ε)) < (tauPerp n : ℝ) := by
  sorry

/-- The adjacent coprime divisor counts at two and thirty are one and four, respectively. -/
theorem tauPerp_two_and_thirty : tauPerp 2 = 1 ∧ tauPerp 30 = 4 := by
  have hdivisors2 : (2 : ℕ).divisors = [1, 2].toFinset := by
    rw [← Nat.filter_dvd_eq_divisors (by decide : (2 : ℕ) ≠ 0)]
    decide
  have hlist2 : divisorList 2 = [1, 2] := by
    unfold divisorList
    rw [hdivisors2]
    exact (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)
  have hdivisors30 : (30 : ℕ).divisors = [1, 2, 3, 5, 6, 10, 15, 30].toFinset := by
    rw [← Nat.filter_dvd_eq_divisors (by decide : (30 : ℕ) ≠ 0)]
    decide
  have hlist30 : divisorList 30 = [1, 2, 3, 5, 6, 10, 15, 30] := by
    unfold divisorList
    rw [hdivisors30]
    exact (List.toFinset_sort (· ≤ ·) (by decide)).2 (by decide)
  unfold tauPerp
  rw [hlist2, hlist30]
  decide

/-- Sanity: equality τ⊥ = ω happens — `n = 2`: divisors 1, 2;
    τ⊥ = 1 = ω(2).  And a squarefree table entry: τ⊥(30) — divisors
    1,2,3,5,6,10,15,30: coprime adjacent pairs (1,2),(2,3),(3,5),
    (5,6) → τ⊥(30) = 4 with ω = 3.  -- PROVABLE (decide). -/
example : tauPerp 2 = 1 ∧ tauPerp 30 = 4 := by
  exact tauPerp_two_and_thirty

end ErdosCandidates.E1100

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches erdos fetch 1100 exactly.
   - tau_perp definition, both questions, g(k) over squarefree with omega=k all faithful.
   - Erdos-Simonovits (sqrt(2)+o(1))^k < g(k) < (2-c)^k matches DB remarks.
   - Erdos-Hall max order exp((log log x)^{2-eps}) matches DB remarks.
   - Arithmetic: tau_perp(12)=3 (adj coprime pairs: (1,2),(2,3),(3,4)), tau_perp(30)=4
     ((1,2),(2,3),(3,5),(5,6)), tau_perp(2)=1. All verified.
   - A325864 OEIS flag: confirmed. goof oeis show A325864 returns "Number of subsets of
     {1..n} of which every subset has a different sum" — indeed unrelated to tau_perp.
     The DB comments show AlexisOlson flagged it as "related but not identical" and the
     site was updated. The file's warning is correct and well-judged; the sequence is
     tangentially connected (distinct subset sums arise in the Erdos-Simonovits reduction
     per Woett's comment remark 3) but is NOT a direct encoding of tau_perp values.
     Flag is legitimate and should be retained.
-/
