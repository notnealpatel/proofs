/-
# A382465 — the range of the greedy digit sequence A382462

The unsigned conjecture in OEIS A382465 says that its terms are A382462
sorted; A382464 gives the complementary missing-number conjecture.
A382465 consists of positive integers in which every even digit except
the first is immediately preceded by a smaller digit. A382462 is the
lexicographically earliest sequence of distinct positive integers obeying
this rule on the concatenated digit stream.

## Conventions

* A382462 is formalised as the greedy sequence `a`: `a n` is the least
  positive integer not among `a 0, …, a (n-1)` whose digits, appended to the
  digit stream of the earlier terms, keep the rule "every even digit is
  immediately preceded by a smaller digit".  The greedy never dead-ends
  (`exists_admissible`: an unused repunit is always admissible), so it is
  the lexicographically earliest such sequence.  Offset: `a 0` is the
  OEIS term `a(1)`.
* The very first digit of the stream has no predecessor and is left
  unconstrained, matching "except the first"; it is immaterial since
  `a 0 = 1`.
* "Every even digit except the first is immediately preceded by a smaller
  digit" is `List.IsChain StepOk` on the decimal digits, most significant
  first, with `StepOk c d := Even d → c < d`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A382465LexicographicallyEarliestDistinct

/-! ## Definitions -/

/-- Decimal digits of `m`, most significant digit first (empty for `m = 0`). -/
def digitsMSF (m : ℕ) : List ℕ := (Nat.digits 10 m).reverse

/-- The local digit rule between a digit `c` and the digit `d` immediately after
it: if `d` is even then `c < d`. -/
def StepOk (c d : ℕ) : Prop := Even d → c < d

instance : DecidableRel StepOk := fun c d => inferInstanceAs (Decidable (Even d → c < d))

/-- Membership in A382465: `m` is a positive integer in which every even digit
except the first is immediately preceded by a smaller digit. -/
def Elig (m : ℕ) : Prop := 0 < m ∧ List.IsChain StepOk (digitsMSF m)

instance : DecidablePred Elig := fun m =>
  inferInstanceAs (Decidable (0 < m ∧ List.IsChain StepOk (digitsMSF m)))

/-- The concatenated decimal digit stream of a list of numbers ("ignoring commas"). -/
def stream (l : List ℕ) : List ℕ := l.flatMap digitsMSF

/-- `c` is an admissible next term after the terms `l`: it is a positive integer
not yet used, and the digit stream of `l ++ [c]` obeys the A382462 rule (every
even digit is immediately preceded by a smaller digit). -/
def Admissible (l : List ℕ) (c : ℕ) : Prop :=
  0 < c ∧ c ∉ l ∧ List.IsChain StepOk (stream (l ++ [c]))

instance (l : List ℕ) : DecidablePred (Admissible l) := fun c =>
  inferInstanceAs (Decidable (0 < c ∧ c ∉ l ∧ List.IsChain StepOk (stream (l ++ [c]))))

/-- The greedy step: the least admissible next term after `l` (junk value `0` when
none exists; `exists_admissible` shows this never happens along the sequence). -/
noncomputable def next (l : List ℕ) : ℕ :=
  open Classical in if h : ∃ c, Admissible l c then Nat.find h else 0

/-- `hist n` is the list of the first `n` terms `[a 0, …, a (n-1)]` of A382462. -/
noncomputable def hist : ℕ → List ℕ
  | 0 => []
  | n + 1 => hist n ++ [next (hist n)]

/-- A382462 (offset shifted to `0`): the lexicographically earliest sequence of
distinct positive integers such that every even digit of the digit stream is
immediately preceded by a smaller digit, computed greedily. -/
noncomputable def a (n : ℕ) : ℕ := next (hist n)

/-- The repunit with `k` ones: `repunit k = (10^k - 1) / 9`. -/
def repunit : ℕ → ℕ
  | 0 => 0
  | k + 1 => 10 * repunit k + 1

/-! ## Repunits are always admissible -/

/-- The decimal digits of the `k`-th repunit are `k` ones. -/
theorem digits_repunit (k : ℕ) : Nat.digits 10 (repunit k) = List.replicate k 1 := by
  induction k with
  | zero => simp [repunit]
  | succ k ih =>
    rw [repunit, Nat.digits_def' (by norm_num) (by omega)]
    have h1 : (10 * repunit k + 1) % 10 = 1 := by omega
    have h2 : (10 * repunit k + 1) / 10 = repunit k := by omega
    rw [h1, h2, ih, List.replicate_succ]

/-- The most-significant-first digits of the `k`-th repunit are `k` ones. -/
theorem digitsMSF_repunit (k : ℕ) : digitsMSF (repunit k) = List.replicate k 1 := by
  rw [digitsMSF, digits_repunit, List.reverse_replicate]

/-- `k ≤ repunit k`. -/
theorem le_repunit (k : ℕ) : k ≤ repunit k := by
  induction k with
  | zero => simp [repunit]
  | succ k ih => rw [repunit]; omega

/-- The repunit of length `l.sum + 1` exceeds every entry of `l`, so it is not in `l`. -/
theorem repunit_not_mem (l : List ℕ) : repunit (l.sum + 1) ∉ l := by
  intro hmem
  have h1 := List.le_sum_of_mem hmem
  have h2 := le_repunit (l.sum + 1)
  omega

/-- A digit list with no even entry satisfies the rule. -/
theorem isChain_of_forall_odd (l : List ℕ) (h : ∀ y ∈ l, ¬ Even y) :
    List.IsChain StepOk l := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons x t ih =>
    rw [List.isChain_cons]
    refine ⟨fun y hy hev => absurd hev (h y ?_),
      ih fun y hy => h y (List.mem_cons_of_mem x hy)⟩
    exact List.mem_cons_of_mem x (List.mem_of_mem_head? hy)

/-- Appending digits with no even entry to a rule-abiding stream keeps the rule. -/
theorem isChain_append_of_forall_odd (l₁ l₂ : List ℕ) (h₁ : List.IsChain StepOk l₁)
    (h₂ : ∀ y ∈ l₂, ¬ Even y) : List.IsChain StepOk (l₁ ++ l₂) := by
  rw [List.isChain_append]
  refine ⟨h₁, isChain_of_forall_odd l₂ h₂, fun x _ y hy hev => absurd hev (h₂ y ?_)⟩
  exact List.mem_of_mem_head? hy

/-- The digit stream of `l ++ [c]` is the stream of `l` followed by the digits of `c`. -/
theorem stream_append_singleton (l : List ℕ) (c : ℕ) :
    stream (l ++ [c]) = stream l ++ digitsMSF c := by
  simp [stream]

/-- An unused repunit of positive length is admissible after any rule-abiding prefix. -/
theorem admissible_repunit (l : List ℕ) (k : ℕ) (hk : 0 < k)
    (hl : List.IsChain StepOk (stream l)) (hnot : repunit k ∉ l) :
    Admissible l (repunit k) := by
  refine ⟨?_, hnot, ?_⟩
  · have hle := le_repunit k
    omega
  · rw [stream_append_singleton, digitsMSF_repunit]
    refine isChain_append_of_forall_odd _ _ hl fun y hy => ?_
    rw [List.eq_of_mem_replicate hy]
    decide

/-- The greedy never dead-ends: after any rule-abiding prefix some term is admissible. -/
theorem exists_admissible (l : List ℕ) (hl : List.IsChain StepOk (stream l)) :
    ∃ c, Admissible l c :=
  ⟨_, admissible_repunit l _ (Nat.succ_pos _) hl (repunit_not_mem l)⟩

/-! ## The greedy sequence -/

/-- After a rule-abiding prefix, `next` is admissible and below every admissible term. -/
theorem next_spec (l : List ℕ) (hl : List.IsChain StepOk (stream l)) :
    Admissible l (next l) ∧ ∀ c, Admissible l c → next l ≤ c := by
  classical
  have hex := exists_admissible l hl
  have hnext : next l = Nat.find hex := by
    rw [next, dif_pos hex]
  rw [hnext]
  exact ⟨Nat.find_spec hex, fun c hc => Nat.find_min' hex hc⟩

/-- Characterisation of `next` by admissibility and minimality. -/
theorem next_eq_of (l : List ℕ) (c : ℕ) (hc : Admissible l c)
    (hmin : ∀ c' < c, ¬ Admissible l c') : next l = c := by
  have hl : List.IsChain StepOk (stream l) := by
    have h := hc.2.2
    rw [stream_append_singleton] at h
    exact h.left_of_append
  obtain ⟨hadm, hle⟩ := next_spec l hl
  have h1 := hle c hc
  by_contra hne
  exact hmin (next l) (lt_of_le_of_ne h1 hne) hadm

/-- The digit stream of the first `n` terms obeys the rule. -/
theorem isChain_stream_hist (n : ℕ) : List.IsChain StepOk (stream (hist n)) := by
  induction n with
  | zero => simp [hist, stream]
  | succ n ih => exact (next_spec (hist n) ih).1.2.2

/-- `a n` is admissible after the first `n` terms. -/
theorem a_admissible (n : ℕ) : Admissible (hist n) (a n) :=
  (next_spec (hist n) (isChain_stream_hist n)).1

/-- `a n` is the least admissible term after the first `n` terms. -/
theorem a_le_of_admissible (n c : ℕ) (hc : Admissible (hist n) c) : a n ≤ c :=
  (next_spec (hist n) (isChain_stream_hist n)).2 c hc

/-- `hist n = [a 0, …, a (n-1)]`. -/
theorem hist_eq (n : ℕ) : hist n = (List.range n).map a := by
  induction n with
  | zero => simp [hist]
  | succ n ih => rw [hist, List.range_succ, List.map_append, ← ih]; rfl

/-- Membership in `hist n` means being one of the first `n` terms. -/
theorem mem_hist_iff (n x : ℕ) : x ∈ hist n ↔ ∃ i < n, a i = x := by
  rw [hist_eq]
  simp

/-- The terms of A382462 are distinct. -/
theorem a_injective : Function.Injective a := by
  have key : ∀ i j, i < j → a i ≠ a j := by
    intro i j hij heq
    exact (a_admissible j).2.1 ((mem_hist_iff j (a j)).2 ⟨i, hij, heq⟩)
  intro i j h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h (key i j hij)
  · exact hij
  · exact absurd h.symm (key j i hij)

/-- Every term of A382462 lies in A382465. -/
theorem elig_a (n : ℕ) : Elig (a n) := by
  obtain ⟨hpos, -, hch⟩ := a_admissible n
  rw [stream_append_singleton] at hch
  exact ⟨hpos, hch.right_of_append⟩

/-! ## Every member of A382465 occurs -/

/-- If every member of A382465 below `m` occurs in A382462, they all occur among
the first `N` terms for some `N`. -/
theorem exists_cover (m : ℕ) (h : ∀ m' < m, Elig m' → m' ∈ Set.range a) :
    ∃ N, ∀ m' < m, Elig m' → m' ∈ hist N := by
  induction m with
  | zero => exact ⟨0, fun m' hm' => absurd hm' (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨N, hN⟩ := ih (fun m' hm' he => h m' (by omega) he)
    by_cases he : Elig m
    · obtain ⟨i, hi⟩ := h m (by omega) he
      refine ⟨max N (i + 1), fun m' hm' he' => ?_⟩
      rw [mem_hist_iff]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm' with hlt | heq
      · obtain ⟨j, hj, hja⟩ := (mem_hist_iff N m').1 (hN m' hlt he')
        exact ⟨j, by omega, hja⟩
      · exact ⟨i, by omega, by rw [hi, heq]⟩
    · refine ⟨N, fun m' hm' he' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm' with hlt | heq
      · exact hN m' hlt he'
      · exact absurd (heq ▸ he') he

/-- The leading decimal digit of a positive integer is nonzero. -/
theorem head_digitsMSF_ne_zero (m : ℕ) (hm : 0 < m) :
    ∀ y ∈ (digitsMSF m).head?, y ≠ 0 := by
  intro y hy
  have hne : m ≠ 0 := by omega
  rw [digitsMSF, List.head?_reverse,
    List.getLast?_eq_some_getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hne)] at hy
  rw [← Option.mem_some_iff.1 hy]
  exact Nat.getLast_digit_ne_zero 10 hne

/-- Right after a repunit term (stream ends in `1`), every unused member of
A382465 is admissible, since its leading digit is odd or an even digit `≥ 2`. -/
theorem admissible_after_repunit (m n k : ℕ) (hm : Elig m) (hmn : m ∉ hist (n + 1))
    (hak : a n = repunit k) (hk : 0 < k) : Admissible (hist (n + 1)) m := by
  refine ⟨hm.1, hmn, ?_⟩
  rw [stream_append_singleton, List.isChain_append]
  refine ⟨isChain_stream_hist (n + 1), hm.2, fun x hx y hy hev => ?_⟩
  have hx1 : x = 1 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hs : stream (hist (n + 1)) = (stream (hist n) ++ List.replicate k' 1) ++ [1] := by
      rw [hist, stream_append_singleton, ← a, hak, digitsMSF_repunit, List.replicate_succ',
        List.append_assoc]
    rw [hs, List.getLast?_concat] at hx
    exact (Option.mem_some_iff.1 hx).symm
  have hy0 := head_digitsMSF_ne_zero m hm.1 y hy
  obtain ⟨r, hr⟩ := hev
  omega

/-- Every member of A382465 occurs in A382462.

Strong induction on `m`.  If `m` never occurs, pick `N` after which every smaller
member has occurred.  From then on `m` is never admissible (else the greedy would
choose a smaller unused member), so no later term is a repunit.  An unused
repunit `w` is then admissible at every later step, forcing infinitely many
distinct terms below `w`: contradiction. -/
theorem elig_mem_range (m : ℕ) (hm : Elig m) : m ∈ Set.range a := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  by_contra hnot
  obtain ⟨N, hN⟩ := exists_cover m (fun m' hm' he => ih m' hm' he)
  have hm_not : ∀ n, m ∉ hist n := by
    intro n hmem
    obtain ⟨i, -, hi⟩ := (mem_hist_iff n m).1 hmem
    exact hnot ⟨i, hi⟩
  have hnadm : ∀ n, N ≤ n → ¬ Admissible (hist n) m := by
    intro n hn hadm
    have hle := a_le_of_admissible n m hadm
    have hne : a n ≠ m := fun h => hnot ⟨n, h⟩
    have hlt : a n < m := lt_of_le_of_ne hle hne
    obtain ⟨i, hi, hai⟩ := (mem_hist_iff N (a n)).1 (hN (a n) hlt (elig_a n))
    exact (a_admissible n).2.1 ((mem_hist_iff n (a n)).2 ⟨i, by omega, hai⟩)
  let k := (hist N).sum + 1
  let w := repunit k
  have hw_not_hist : w ∉ hist N := repunit_not_mem _
  have hw_range : ∀ n, a n ≠ w := by
    intro n hn
    rcases lt_or_ge n N with h | h
    · exact hw_not_hist ((mem_hist_iff N w).2 ⟨n, h, hn⟩)
    · exact hnadm (n + 1) (by omega)
        (admissible_after_repunit m n k hm (hm_not _) hn (Nat.succ_pos _))
  have hlt : ∀ j, a (N + j) < w := by
    intro j
    have hw_not : w ∉ hist (N + j) := by
      intro hmem
      obtain ⟨i, -, hi⟩ := (mem_hist_iff _ w).1 hmem
      exact hw_range i hi
    have hadm : Admissible (hist (N + j)) w :=
      admissible_repunit _ k (Nat.succ_pos _) (isChain_stream_hist _) hw_not
    exact lt_of_le_of_ne (a_le_of_admissible _ _ hadm) (hw_range _)
  obtain ⟨x, y, hxy, hfxy⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun j : ℕ => (⟨a (N + j), hlt j⟩ : Fin w))
  have hval : a (N + x) = a (N + y) := Fin.mk.inj_iff.1 hfxy
  have hidx := a_injective hval
  omega

/-! ## The conjecture -/

/-- **A382465 conjecture** (OEIS A382465 comment: "Conjecture: these are the terms
of A382462, sorted"; equivalently the A382464 comment "these are the numbers
missing from A382462").

A382462 — the lexicographically earliest sequence of distinct positive integers
whose concatenated decimal digit stream has every even digit immediately preceded
by a smaller digit — consists of distinct terms whose set of values is exactly
the set of positive integers in which every even digit other than the leading one
is immediately preceded by a smaller digit (A382465). -/
theorem conjecture : Function.Injective a ∧ Set.range a = {m | Elig m} := by
  refine ⟨a_injective, Set.ext fun m => ⟨?_, elig_mem_range m⟩⟩
  rintro ⟨n, rfl⟩
  exact elig_a n

/-! ## Examples -/

/-- `Elig` reproduces the listed terms of A382465 below `100`. -/
example : (List.range 100).filter (fun m => decide (Elig m)) =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 23, 24, 25, 26, 27,
     28, 29, 31, 33, 34, 35, 36, 37, 38, 39, 41, 43, 45, 46, 47, 48, 49, 51, 53, 55, 56, 57,
     58, 59, 61, 63, 65, 67, 68, 69, 71, 73, 75, 77, 78, 79, 81, 83, 85, 87, 89, 91, 93, 95,
     97, 99] := by
  decide

/-- One greedy step, certified by admissibility and minimality. -/
theorem hist_succ_of (n : ℕ) (l : List ℕ) (c : ℕ) (hn : hist n = l) (hc : Admissible l c)
    (hmin : ∀ c' < c, ¬ Admissible l c') : hist (n + 1) = l ++ [c] := by
  rw [hist, hn, next_eq_of l c hc hmin]

/-- The first 26 terms of `a` agree with the data of A382462. -/
theorem a_first_terms : (List.range 26).map a =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 31, 21, 23, 33, 34, 35,
     36, 37] := by
  rw [← hist_eq]
  have h1 := hist_succ_of 0 [] 1 rfl (by decide) (by decide)
  have h2 := hist_succ_of 1 _ 2 h1 (by decide) (by decide)
  have h3 := hist_succ_of 2 _ 3 h2 (by decide) (by decide)
  have h4 := hist_succ_of 3 _ 4 h3 (by decide) (by decide)
  have h5 := hist_succ_of 4 _ 5 h4 (by decide) (by decide)
  have h6 := hist_succ_of 5 _ 6 h5 (by decide) (by decide)
  have h7 := hist_succ_of 6 _ 7 h6 (by decide) (by decide)
  have h8 := hist_succ_of 7 _ 8 h7 (by decide) (by decide)
  have h9 := hist_succ_of 8 _ 9 h8 (by decide) (by decide)
  have h10 := hist_succ_of 9 _ 11 h9 (by decide) (by decide)
  have h11 := hist_succ_of 10 _ 12 h10 (by decide) (by decide)
  have h12 := hist_succ_of 11 _ 13 h11 (by decide) (by decide)
  have h13 := hist_succ_of 12 _ 14 h12 (by decide) (by decide)
  have h14 := hist_succ_of 13 _ 15 h13 (by decide) (by decide)
  have h15 := hist_succ_of 14 _ 16 h14 (by decide) (by decide)
  have h16 := hist_succ_of 15 _ 17 h15 (by decide) (by decide)
  have h17 := hist_succ_of 16 _ 18 h16 (by decide) (by decide)
  have h18 := hist_succ_of 17 _ 19 h17 (by decide) (by decide)
  have h19 := hist_succ_of 18 _ 31 h18 (by decide) (by decide)
  have h20 := hist_succ_of 19 _ 21 h19 (by decide) (by decide)
  have h21 := hist_succ_of 20 _ 23 h20 (by decide) (by decide)
  have h22 := hist_succ_of 21 _ 33 h21 (by decide) (by decide)
  have h23 := hist_succ_of 22 _ 34 h22 (by decide) (by decide)
  have h24 := hist_succ_of 23 _ 35 h23 (by decide) (by decide)
  have h25 := hist_succ_of 24 _ 36 h24 (by decide) (by decide)
  exact hist_succ_of 25 _ 37 h25 (by decide) (by decide)

end Candidates.A382465LexicographicallyEarliestDistinct
