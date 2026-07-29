/-
  Erdős Problem #880 (erdosproblems.com/880) — the k = 2 positive case of
  the Burr–Erdős question on restricted addition.

  PROBLEM (Burr–Erdős, via [E97]): let A be an asymptotic basis of order
  k (every large integer is the sum of k or fewer elements of A) and let
  b₁ < b₂ < ⋯ enumerate the integers that are the sum of k or fewer
  PAIRWISE DISTINCT elements of A.  Is b_{i+1} − b_i bounded?

  ANSWER (Hegyvári–Hennecart–Plagne [HHP07]): yes for k = 2 — with
  b_{i+1} − b_i ≤ 2 for all large i — and no for every k ≥ 3.  This file
  formalizes the k = 2 positive case, [HHP07] Theorem 1(i) (paper p. 2,
  proof p. 4):

    (i)  If (A ∪ 2A) ∼ ℕ then Δ(A ∪ 2 × A) ≤ 2.
         If 2A ∼ ℕ then Δ(2 × A) ≤ 2.

  where 2A = {a + b : a, b ∈ A}, 2 × A = {a + b : a, b ∈ A, a ≠ b},
  S ∼ ℕ means S contains all but finitely many positive integers, and
  Δ(S) = lim sup_{i→∞} (s_{i+1} − s_i) is the largest asymptotic gap of
  the increasing enumeration s₁ < s₂ < ⋯ of S.  The proof is the paper's
  one-liner: an ODD n = a + b forces a ≠ b, so every odd element of 2A
  lies in 2 × A; if 2A is cofinite every large odd number is in 2 × A,
  and among any two consecutive integers one is odd.

  NOTATION MAP (paper → Lean, everything in namespace Erdos880):
    2A                        → A + A            (Mathlib pointwise Set.add)
    2 × A                     → A +ᵣ A           (Proofs.Erdos880.RestrictedSumset)
    S ∼ ℕ                     → ∀ᶠ n in atTop, n ∈ S
                                 (⇔ Sᶜ.Finite, `eventually_mem_iff_compl_finite`;
                                 over ℕ "all but finitely many positive
                                 integers" = "all sufficiently large naturals")
    Δ(S) ≤ d                  → HasGapsLE S d
    Theorem 1(i), 2A form     → eventually_odd_mem_restrictedSumset (odd part)
                                 hasGapsLE_restrictedSumset (gap bound)
                                 restrictedSumset_infinite_and_nth_succ_le
                                   (literal b_{i+1} − b_i form)
    Theorem 1(i), A ∪ 2A form → eventually_odd_mem_union_restrictedSumset
                                 hasGapsLE_union_restrictedSumset
                                 erdos880_k2 (headline, literal form)

  RENDERING OF Δ(S) ≤ d.  `HasGapsLE S d` says: every window of d
  consecutive integers beyond some point meets S
  (`∀ᶠ n in atTop, (S ∩ Set.Ico n (n + d)).Nonempty`).  This is the
  cleanest enumeration-free form, and it is FAITHFUL: for d ≥ 1 it is
  equivalent to "S is infinite and beyond some point each element of S
  is followed by another within distance d"
  (`hasGapsLE_iff_infinite_and_succ`), and — via the increasing
  enumeration `Nat.nth (· ∈ S)` of S, which is exactly the paper's
  s₁ < s₂ < ⋯ — to "S is infinite and s_{i+1} ≤ s_i + d for all large i"
  (`hasGapsLE_iff_infinite_and_nth`), which is precisely
  Δ(S) = lim sup (s_{i+1} − s_i) ≤ d for an ℕ-valued gap sequence.
  Note Δ(S) ≤ d presupposes an infinite S (else the enumeration
  terminates); `HasGapsLE` builds that in rather than assuming it.

  SHARPNESS (paper's optimality remark, formalized in the finite form
  scoped by the task card): for A₀ = {0} ∪ {odd n} we prove
  2A₀ = ℕ (so a fortiori 2A₀ ⊇ {n ≥ 1} and 2A₀ ∼ ℕ), yet
  2 × A₀ = ℕ \ {0, 2}: the even number 2 ∈ 2A₀ is missing from 2 × A₀,
  and 1, 3 ∈ 2 × A₀ are consecutive elements at distance exactly 2
  (`restrictedSumset_oddsWithZero_gap_attained`).  So the containment
  "odd elements of 2A lie in 2 × A" cannot be extended to even numbers,
  and a gap of size exactly 2 does occur: the constant 2 is attained.
  CAVEAT, stated to avoid overclaiming: 2 × A₀ is itself cofinite, so
  this example does NOT exhibit Δ(2 × A) = 2 (infinitely many gaps of
  size 2).  That stronger asymptotic optimality holds for asymptotic
  bases of order 2 with restricted order > 2, which exist by
  Kelly (1957) and Hennecart (2005) — cited but not proved in [HHP07]
  (p. 2), and out of scope here.

  [E97]   P. Erdős, "Some of my new and almost new problems and results
          in combinatorial number theory", Number Theory (Eger, 1996),
          de Gruyter, 1998.
  [HHP07] N. Hegyvári, F. Hennecart, A. Plagne, "Answer to a question by
          Burr and Erdős on restricted addition, and related results",
          Combin. Probab. Comput. 16 (2007), 747–756.  Local copy:
          References/Erdos-Burr/paper.txt.
-/

import Erdos.Erdos880.RestrictedSumset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Interval.Finset.Basic

open Filter Pointwise

namespace Erdos880

variable {A S : Set ℕ} {d n : ℕ}

-- ════════════════════════════════════════════════════════════════════
-- §1 THE GAP PREDICATE: rendering Δ(S) ≤ d
-- ════════════════════════════════════════════════════════════════════

/-- `HasGapsLE S d`: beyond some point, every window of `d` consecutive
    integers meets `S`.  This renders the paper's Δ(S) ≤ d, i.e.
    "the gaps between consecutive elements of `S` are eventually at most
    `d`"; see `hasGapsLE_iff_infinite_and_succ` and
    `hasGapsLE_iff_infinite_and_nth` for the proofs that the rendering
    is faithful. -/
def HasGapsLE (S : Set ℕ) (d : ℕ) : Prop :=
  ∀ᶠ n in atTop, (S ∩ Set.Ico n (n + d)).Nonempty

/-- Unfolding `HasGapsLE` to an explicit threshold. -/
theorem hasGapsLE_iff_exists :
    HasGapsLE S d ↔ ∃ N, ∀ n ≥ N, (S ∩ Set.Ico n (n + d)).Nonempty :=
  eventually_atTop

/-- Over `ℕ`, "`S` contains all but finitely many naturals" (the paper's
    `S ∼ ℕ`) is the same as "`n ∈ S` for all sufficiently large `n`";
    this justifies rendering `2A ∼ ℕ` as `∀ᶠ n in atTop, n ∈ A + A`. -/
theorem eventually_mem_iff_compl_finite :
    (∀ᶠ n in atTop, n ∈ S) ↔ Sᶜ.Finite := by
  rw [← Nat.cofinite_eq_atTop, eventually_cofinite]
  rfl

/-- Faithfulness of `HasGapsLE`, successor form: for `d ≥ 1`, the window
    rendering is equivalent to "`S` is infinite, and every sufficiently
    large element of `S` is followed by another element of `S` within
    distance `d`" — eventual consecutive gaps at most `d`. -/
theorem hasGapsLE_iff_infinite_and_succ (hd : 0 < d) :
    HasGapsLE S d ↔
      S.Infinite ∧ ∀ᶠ s in atTop, s ∈ S → ∃ t ∈ S, s < t ∧ t ≤ s + d := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := hasGapsLE_iff_exists.mp h
    refine ⟨fun hfin => ?_, ?_⟩
    · -- windows arbitrarily far out meet S, so S is unbounded
      obtain ⟨b, hb⟩ := hfin.bddAbove
      obtain ⟨t, htS, ht₁, -⟩ := hN (N + b + 1) (by omega)
      exact absurd (hb htS) (by omega)
    · -- the window starting just above s ∈ S produces the next element
      refine eventually_atTop.mpr ⟨N, fun s hs _hsS => ?_⟩
      obtain ⟨t, htS, ht₁, ht₂⟩ := hN (s + 1) (by omega)
      exact ⟨t, htS, by omega, by omega⟩
  · rintro ⟨hinf, h⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    obtain ⟨s₀, hs₀S, hs₀N⟩ := hinf.exists_gt N
    refine hasGapsLE_iff_exists.mpr ⟨s₀, fun n hn => ?_⟩
    -- induct the window along from the anchor s₀ ∈ S
    induction n, hn using Nat.le_induction with
    | base => exact ⟨s₀, hs₀S, le_rfl, by omega⟩
    | succ n hn ih =>
      obtain ⟨t, htS, ht₁, ht₂⟩ := ih
      by_cases hc : n + 1 ≤ t
      · exact ⟨t, htS, hc, by omega⟩
      · -- t = n: its successor in S lands in the next window
        obtain ⟨u, huS, hu₁, hu₂⟩ := hN t (by omega) htS
        exact ⟨u, huS, by omega, by omega⟩

/-- Faithfulness of `HasGapsLE`, enumeration form: for `d ≥ 1` and with
    `Nat.nth (· ∈ S)` the increasing enumeration s₀ < s₁ < ⋯ of `S`
    (the paper's b₁ < b₂ < ⋯), the window rendering is equivalent to
    "`S` is infinite and s_{i+1} − s_i ≤ d for all large i", which is
    literally Δ(S) = lim sup (s_{i+1} − s_i) ≤ d. -/
theorem hasGapsLE_iff_infinite_and_nth (hd : 0 < d) :
    HasGapsLE S d ↔
      S.Infinite ∧
        ∀ᶠ i in atTop, Nat.nth (· ∈ S) (i + 1) ≤ Nat.nth (· ∈ S) i + d := by
  rw [hasGapsLE_iff_infinite_and_succ hd]
  refine and_congr_right fun hinf => ⟨fun h => ?_, fun h => ?_⟩
  · -- successor form ⇒ enumeration form
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    refine eventually_atTop.mpr ⟨N, fun i hi => ?_⟩
    obtain ⟨t, htS, ht₁, ht₂⟩ :=
      hN (Nat.nth (· ∈ S) i) (hi.trans (Nat.nth_strictMono hinf).le_apply)
        (Nat.nth_mem_of_infinite hinf i)
    -- nth (i+1) is the least element of S above nth i, hence ≤ t
    refine le_trans (not_lt.mp fun hlt => ?_) ht₂
    exact absurd (Nat.le_nth_of_lt_nth_succ hlt htS) (not_le.mpr ht₁)
  · -- enumeration form ⇒ successor form
    obtain ⟨I, hI⟩ := eventually_atTop.mp h
    refine eventually_atTop.mpr ⟨Nat.nth (· ∈ S) I, fun s hs hsS => ?_⟩
    obtain ⟨i, rfl⟩ := Nat.subset_range_nth hsS
    exact ⟨Nat.nth (· ∈ S) (i + 1), Nat.nth_mem_of_infinite hinf _,
      (Nat.nth_lt_nth hinf).mpr i.lt_succ_self,
      hI i ((Nat.nth_le_nth hinf).mp hs)⟩

-- ════════════════════════════════════════════════════════════════════
-- §2 HHP07 THEOREM 1(i): the k = 2 Burr–Erdős question
-- ════════════════════════════════════════════════════════════════════

/-- The heart of [HHP07] Theorem 1(i): an odd element of the sumset
    `A + A` lies in the restricted sumset, because odd `n = a + b`
    forces `a ≠ b`. -/
theorem mem_restrictedSumset_of_odd (hn : Odd n) (h : n ∈ A + A) :
    n ∈ A +ᵣ A := by
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp h
  rcases eq_or_ne a b with rfl | hne
  · obtain ⟨m, hm⟩ := hn
    omega
  · exact ⟨a, ha, b, hb, hne, hab⟩

/-- Variant with single elements allowed ("sums of 2 or fewer"): an odd
    element of `A ∪ 2A` lies in `A ∪ (2 × A)`. -/
theorem mem_union_restrictedSumset_of_odd (hn : Odd n)
    (h : n ∈ A ∪ (A + A)) : n ∈ A ∪ (A +ᵣ A) := by
  rcases h with hA | h2
  · exact Set.mem_union_left _ hA
  · exact Set.mem_union_right _ (mem_restrictedSumset_of_odd hn h2)

/-- [HHP07] Theorem 1(i), second statement, odd part: if `2A ∼ ℕ` then
    every sufficiently large odd number is a sum of two distinct
    elements of `A`. -/
theorem eventually_odd_mem_restrictedSumset
    (h : ∀ᶠ n in atTop, n ∈ A + A) :
    ∀ᶠ n in atTop, Odd n → n ∈ A +ᵣ A :=
  h.mono fun _n hn ho => mem_restrictedSumset_of_odd ho hn

/-- [HHP07] Theorem 1(i), first statement, odd part: if `(A ∪ 2A) ∼ ℕ`
    then every sufficiently large odd number is a sum of at most two
    distinct elements of `A`. -/
theorem eventually_odd_mem_union_restrictedSumset
    (h : ∀ᶠ n in atTop, n ∈ A ∪ (A + A)) :
    ∀ᶠ n in atTop, Odd n → n ∈ A ∪ (A +ᵣ A) :=
  h.mono fun _n hn ho => mem_union_restrictedSumset_of_odd ho hn

/-- [HHP07] Theorem 1(i), second statement: if `2A ∼ ℕ` then
    `Δ(2 × A) ≤ 2`.  Proof: one of `n`, `n + 1` is odd, and large odd
    numbers lie in `2 × A`. -/
theorem hasGapsLE_restrictedSumset (h : ∀ᶠ n in atTop, n ∈ A + A) :
    HasGapsLE (A +ᵣ A) 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine hasGapsLE_iff_exists.mpr ⟨N, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · exact ⟨n + 1, mem_restrictedSumset_of_odd he.add_one
      (hN (n + 1) (by omega)), by omega, by omega⟩
  · exact ⟨n, mem_restrictedSumset_of_odd ho (hN n hn), le_rfl, by omega⟩

/-- [HHP07] Theorem 1(i), first statement: if `(A ∪ 2A) ∼ ℕ` — i.e. `A`
    is an asymptotic basis of order ≤ 2 in the "sums of 2 or fewer
    elements" sense of the Burr–Erdős problem — then
    `Δ(A ∪ (2 × A)) ≤ 2`. -/
theorem hasGapsLE_union_restrictedSumset
    (h : ∀ᶠ n in atTop, n ∈ A ∪ (A + A)) :
    HasGapsLE (A ∪ (A +ᵣ A)) 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine hasGapsLE_iff_exists.mpr ⟨N, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · exact ⟨n + 1, mem_union_restrictedSumset_of_odd he.add_one
      (hN (n + 1) (by omega)), by omega, by omega⟩
  · exact ⟨n, mem_union_restrictedSumset_of_odd ho (hN n hn), le_rfl,
      by omega⟩

/-- [HHP07] Theorem 1(i), second statement, in the literal gap form: if
    `2A ∼ ℕ` then `2 × A` is infinite, and its increasing enumeration
    s₀ < s₁ < ⋯ (`Nat.nth`) satisfies s_{i+1} − s_i ≤ 2 for all
    sufficiently large `i` — that is, Δ(2 × A) ≤ 2.  (The infiniteness
    conjunct guarantees `Nat.nth` really is the enumeration, with no
    junk values.) -/
theorem restrictedSumset_infinite_and_nth_succ_le
    (h : ∀ᶠ n in atTop, n ∈ A + A) :
    (A +ᵣ A).Infinite ∧
      ∀ᶠ i in atTop,
        Nat.nth (· ∈ A +ᵣ A) (i + 1) ≤ Nat.nth (· ∈ A +ᵣ A) i + 2 :=
  (hasGapsLE_iff_infinite_and_nth (by omega)).mp
    (hasGapsLE_restrictedSumset h)

/-- **Erdős Problem 880, k = 2 (Burr–Erdős question; positive answer of
    [HHP07], Theorem 1(i))**.  If `A` is an asymptotic basis of order at
    most 2 — every sufficiently large integer is a sum of 2 or fewer
    elements of `A` — then the set `B = A ∪ (2 × A)` of integers that
    are sums of 2 or fewer PAIRWISE DISTINCT elements of `A` is
    infinite, and its increasing enumeration b₀ < b₁ < ⋯ (`Nat.nth`)
    satisfies b_{i+1} − b_i ≤ 2 for all sufficiently large `i`; in
    particular the gaps b_{i+1} − b_i are bounded, as Burr and Erdős
    asked. -/
theorem erdos880_k2 (h : ∀ᶠ n in atTop, n ∈ A ∪ (A + A)) :
    (A ∪ (A +ᵣ A)).Infinite ∧
      ∀ᶠ i in atTop,
        Nat.nth (· ∈ A ∪ (A +ᵣ A)) (i + 1) ≤
          Nat.nth (· ∈ A ∪ (A +ᵣ A)) i + 2 :=
  (hasGapsLE_iff_infinite_and_nth (by omega)).mp
    (hasGapsLE_union_restrictedSumset h)

-- ════════════════════════════════════════════════════════════════════
-- §3 SHARPNESS: A₀ = {0} ∪ {odd n} attains the bound 2
-- ════════════════════════════════════════════════════════════════════

/-- The sharpness example: `A₀ = {0} ∪ {odd n}`. -/
def oddsWithZero : Set ℕ := {0} ∪ {n | Odd n}

/-- Membership in the sharpness example, in `omega`-friendly form. -/
theorem mem_oddsWithZero : n ∈ oddsWithZero ↔ n = 0 ∨ n % 2 = 1 := by
  simp [oddsWithZero, Nat.odd_iff]

/-- The unrestricted sumset of the example is everything: odd `n` is
    `0 + n`, even `n ≥ 2` is `1 + (n − 1)` with both summands odd, and
    `0 = 0 + 0`.  In particular `2A₀ ⊇ {n ≥ 1}`, so `2A₀ ∼ ℕ` and `A₀`
    satisfies the hypothesis of Theorem 1(i). -/
theorem add_oddsWithZero : oddsWithZero + oddsWithZero = Set.univ := by
  ext n
  simp only [Set.mem_univ, iff_true]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨0, mem_oddsWithZero.mpr (Or.inl rfl), 0,
        mem_oddsWithZero.mpr (Or.inl rfl), rfl⟩
    · exact ⟨1, mem_oddsWithZero.mpr (Or.inr rfl), n - 1,
        mem_oddsWithZero.mpr (Or.inr (by omega)),
        by show 1 + (n - 1) = n; omega⟩
  · exact ⟨0, mem_oddsWithZero.mpr (Or.inl rfl), n,
      mem_oddsWithZero.mpr (Or.inr (Nat.odd_iff.mp ho)),
      by show 0 + n = n; omega⟩

/-- The restricted sumset of the example misses exactly `0` and `2`:
    `2 × A₀ = ℕ \ {0, 2}`.  (`0 = 0 + 0` and `2 = 1 + 1` have no
    representation with distinct summands; everything else does.) -/
theorem restrictedSumset_oddsWithZero :
    oddsWithZero +ᵣ oddsWithZero = {n | n ≠ 0 ∧ n ≠ 2} := by
  ext n
  constructor
  · rintro ⟨a, ha, b, hb, hne, rfl⟩
    rw [mem_oddsWithZero] at ha hb
    exact ⟨by omega, by omega⟩
  · rintro ⟨h0, h2⟩
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, hm⟩ := he
      exact ⟨1, mem_oddsWithZero.mpr (Or.inr rfl), n - 1,
        mem_oddsWithZero.mpr (Or.inr (by omega)), by omega, by omega⟩
    · exact ⟨0, mem_oddsWithZero.mpr (Or.inl rfl), n,
        mem_oddsWithZero.mpr (Or.inr (Nat.odd_iff.mp ho)), by omega,
        by omega⟩

/-- Sharpness, headline containment failure: `2A₀ ∼ ℕ` (indeed
    `2A₀ = ℕ`), yet the even number `2` is NOT a sum of two distinct
    elements of `A₀`.  So "odd" cannot be dropped from
    `mem_restrictedSumset_of_odd`. -/
theorem two_notMem_restrictedSumset_oddsWithZero :
    2 ∉ oddsWithZero +ᵣ oddsWithZero := by
  rw [restrictedSumset_oddsWithZero]
  simp only [Set.mem_ofPred_eq]
  omega

/-- Sharpness, gap form: `1` and `3` are consecutive elements of
    `2 × A₀` at distance exactly `2` (`2` is missing), so the bound
    `Δ(2 × A) ≤ 2` of Theorem 1(i) is attained: it cannot be improved
    to gaps ≤ 1 starting from any point that includes this window. -/
theorem restrictedSumset_oddsWithZero_gap_attained :
    1 ∈ oddsWithZero +ᵣ oddsWithZero ∧
      2 ∉ oddsWithZero +ᵣ oddsWithZero ∧
        3 ∈ oddsWithZero +ᵣ oddsWithZero := by
  rw [restrictedSumset_oddsWithZero]
  simp only [Set.mem_ofPred_eq]
  omega

/-- The pipeline end-to-end on the example: `A₀` satisfies the
    hypothesis of Theorem 1(i), so `Δ(2 × A₀) ≤ 2`. -/
theorem hasGapsLE_restrictedSumset_oddsWithZero :
    HasGapsLE (oddsWithZero +ᵣ oddsWithZero) 2 :=
  hasGapsLE_restrictedSumset (by simp [add_oddsWithZero])

end Erdos880
