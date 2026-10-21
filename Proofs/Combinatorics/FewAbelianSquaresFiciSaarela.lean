/-
# Fici–Saarela: words whose abelian squares are all trivial

## Source

arXiv:2604.23188, "Binary Words Containing Few Abelian Squares",
by Fazekas, Mammoliti, Mercaş and Simpson.
Section 1 (Introduction), Theorem 2 (`\label{FSthm}`), attributed to
G. Fici and A. Saarela, "On the minimum number of abelian squares in a word",
Dagstuhl Reports 4(3), 2014.  The paper quotes it without proof; the proof here
follows the paper's Theorem 3 (three runs of one letter force a non-trivial
abelian square), the run analysis of its "effective words" (Section 5) and its
Lemma "effective word inequality".

Verbatim (paper, Section 1):

  "Following Fici and Saarela we say that an abelian square of the form
   $a^{2i}$ or $b^{2i}$ for some positive integer $i$ is \emph{trivial}.
   They proved the following theorem.
   Theorem [FS]. If a binary word $w$ contains only trivial abelian squares
   then it satisfies Conjecture 1."
  "Conjecture 1. Any binary word of length $n$ contains at least
   $\lfloor n/4 \rfloor$ abelian squares."

Here "abelian square" means a factor $w[i+1..i+2p]$ whose two halves have the same
Parikh vector, and abelian squares are counted as distinct words.

Date: 2026-10-21.  Status: known result (proved by Fici–Saarela 2014; quoted as
Theorem 2 in the paper).  Formalised and proved here in full.

## Encoding

Letters are `Bool` (`a = true`, `b = false`).  Equal Parikh vectors of the two
halves are encoded as `List.Perm`.  `abelianSquares w` is the `Finset` of distinct
abelian-square factors of `w`, so `θ(w) = (abelianSquares w).card`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.FewAbelianSquaresFiciSaarela

open List

/-- `u` is an abelian square: `u = x ++ y` with `x` nonempty and `x`, `y` having the same
Parikh vector (equivalently, `x` is a permutation of `y`). -/
def IsAbelianSquare (u : List Bool) : Prop :=
  ∃ x y : List Bool, x ≠ [] ∧ x.Perm y ∧ u = x ++ y

/-- Take/drop characterisation of abelian squares: `u` is nonempty of even length and its
two halves are permutations of each other (used for decidability). -/
theorem isAbelianSquare_iff (u : List Bool) :
    IsAbelianSquare u ↔
      u ≠ [] ∧ Even u.length ∧ (u.take (u.length / 2)).Perm (u.drop (u.length / 2)) := by
  constructor
  · rintro ⟨x, y, hx, hxy, rfl⟩
    have hlen : x.length = y.length := hxy.length_eq
    have hhalf : (x ++ y).length / 2 = x.length := by simp [hlen]; omega
    refine ⟨by simp [hx], ⟨x.length, by simp [hlen]⟩, ?_⟩
    rw [hhalf, take_left, drop_left]
    exact hxy
  · rintro ⟨hne, ⟨k, hk⟩, hperm⟩
    refine ⟨u.take (u.length / 2), u.drop (u.length / 2), ?_, hperm, (take_append_drop _ _).symm⟩
    have hpos : 0 < u.length := length_pos_iff.mpr hne
    intro hnil
    rcases take_eq_nil_iff.mp hnil with h0 | h0
    · omega
    · exact hne h0

/-- Abelian squares are decidable via `isAbelianSquare_iff`. -/
instance : DecidablePred IsAbelianSquare := fun u =>
  decidable_of_iff _ (isAbelianSquare_iff u).symm

/-- A trivial abelian square: `a^{2i}` or `b^{2i}` with `i` positive. -/
def IsTrivialAbelianSquare (u : List Bool) : Prop :=
  ∃ (c : Bool) (i : ℕ), 0 < i ∧ u = replicate (2 * i) c

/-- The finite set of (distinct) factors of `w`, including the empty factor. -/
def factors (w : List Bool) : Finset (List Bool) :=
  (w.tails.flatMap inits).toFinset

/-- Membership in `factors w` is exactly being an infix (factor) of `w`. -/
theorem mem_factors {u w : List Bool} : u ∈ factors w ↔ u <:+: w := by
  simp only [factors, mem_toFinset, mem_flatMap, mem_inits, mem_tails, infix_iff_prefix_suffix]
  exact ⟨fun ⟨t, ht, hu⟩ => ⟨t, hu, ht⟩, fun ⟨t, hu, ht⟩ => ⟨t, ht, hu⟩⟩

/-- The set of distinct abelian-square factors of `w`; `θ(w)` is its cardinality. -/
def abelianSquares (w : List Bool) : Finset (List Bool) :=
  (factors w).filter IsAbelianSquare

/-! ## Ground truth

The paper's example `abaababa` has exactly the six abelian squares
`aa, abab, abaaba, baba, baab, aababa`; Table 3 gives `θ(b^9 a b^8) = 4` and
`θ(a^3 b^7 a^5 b^3) = 5`. -/

example : abelianSquares [true, false, true, true, false, true, false, true] =
    {[true, true], [true, false, true, false], [true, false, true, true, false, true],
      [false, true, false, true], [false, true, true, false],
      [true, true, false, true, false, true]} := by
  decide

set_option maxRecDepth 20000 in
example : (abelianSquares (replicate 9 false ++ [true] ++ replicate 8 false)).card = 4 := by
  decide

set_option maxRecDepth 20000 in
example : (abelianSquares
    (replicate 3 true ++ replicate 7 false ++ replicate 5 true ++ replicate 3 false)).card = 5 := by
  decide

example : IsAbelianSquare [true, false, false, true] := by decide
example : ¬ IsAbelianSquare [true, true, false, false] := by decide
example : ¬ IsAbelianSquare [] := by decide


/-- `v` contains a factor that is an abelian square using both letters (non-trivial). -/
def HasNontrivialAbSq (v : List Bool) : Prop :=
  ∃ u, u <:+: v ∧ IsAbelianSquare u ∧ true ∈ u ∧ false ∈ u

/-- Containing a nontrivial abelian square is inherited by superwords (infix order). -/
theorem HasNontrivialAbSq.mono {v v' : List Bool} (h : HasNontrivialAbSq v) (hv : v <:+: v') :
    HasNontrivialAbSq v' := by
  obtain ⟨u, hu, hsq, ht, hf⟩ := h
  exact ⟨u, hu.trans hv, hsq, ht, hf⟩

/-- An abelian square containing both letters is a nontrivial abelian square. -/
theorem hasNontrivialAbSq_of {u : List Bool} (c : Bool) (hsq : IsAbelianSquare u)
    (hc : c ∈ u) (hnc : (!c) ∈ u) : HasNontrivialAbSq u := by
  cases c
  · exact ⟨u, infix_refl u, hsq, hnc, hc⟩
  · exact ⟨u, infix_refl u, hsq, hc, hnc⟩

/-- `c d^s c` with `s` even and positive is a nontrivial abelian square. -/
theorem hasNontrivialAbSq_one (c : Bool) (s : ℕ) (hs : Even s) (hs1 : 1 ≤ s) :
    HasNontrivialAbSq ([c] ++ replicate s (!c) ++ [c]) := by
  obtain ⟨m, rfl⟩ := hs
  refine hasNontrivialAbSq_of c ⟨[c] ++ replicate m (!c), replicate m (!c) ++ [c], by simp,
    ?_, by simp only [replicate_add, append_assoc]⟩ (by simp) (by simp; omega)
  exact perm_append_comm

/-- `c^j d^{2m+1} c^j d` is a nontrivial abelian square. -/
theorem hasNontrivialAbSq_two (c : Bool) (j m : ℕ) (hj : 1 ≤ j) :
    HasNontrivialAbSq (replicate j c ++ replicate (2 * m + 1) (!c) ++ replicate j c ++ [!c]) := by
  refine hasNontrivialAbSq_of c ⟨replicate j c ++ replicate (m + 1) (!c),
    replicate m (!c) ++ replicate j c ++ [!c], by simp, ?_, ?_⟩ (by simp; omega) (by simp)
  · rw [perm_iff_count]
    intro a
    simp only [count_append, count_replicate, count_singleton]
    cases a <;> cases c <;> simp
  · simp only [append_assoc, append_cancel_left_eq]
    rw [show 2 * m + 1 = (m + 1) + m by omega, replicate_add, append_assoc]

/-- `c d^i c^{2m+1} d^i` is a nontrivial abelian square. -/
theorem hasNontrivialAbSq_three (c : Bool) (i m : ℕ) (hi : 1 ≤ i) :
    HasNontrivialAbSq ([c] ++ replicate i (!c) ++ replicate (2 * m + 1) c ++ replicate i (!c)) := by
  refine hasNontrivialAbSq_of c ⟨[c] ++ replicate i (!c) ++ replicate m c,
    replicate (m + 1) c ++ replicate i (!c), by simp, ?_, ?_⟩ (by simp) (by simp; omega)
  · rw [perm_iff_count]
    intro a
    simp only [count_append, count_replicate, count_singleton]
    cases a <;> cases c <;> simp <;> omega
  · simp only [append_assoc, append_cancel_left_eq]
    rw [show 2 * m + 1 = m + (m + 1) by omega, replicate_add, append_assoc]


/-- An explicit decomposition `w = s ++ u ++ t` makes `u` a factor of `w`. -/
theorem infix_of_eq {u w : List Bool} (s t : List Bool) (h : w = s ++ u ++ t) : u <:+: w :=
  ⟨s, t, h.symm⟩

/-- Five alternating runs `c d^p c^q d^r c` always contain a nontrivial abelian square. -/
theorem hasNontrivialAbSq_five (c : Bool) (p q r : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) :
    HasNontrivialAbSq
      ([c] ++ replicate p (!c) ++ replicate q c ++ replicate r (!c) ++ [c]) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rcases Nat.even_or_odd p with hpe | ⟨p', rfl⟩
  · refine (hasNontrivialAbSq_one c p hpe hp).mono
      (infix_of_eq [] (replicate q' c ++ replicate r (!c) ++ [c]) ?_)
    simp [replicate_succ]
  rcases Nat.even_or_odd r with hre | ⟨r', rfl⟩
  · refine (hasNontrivialAbSq_one c r hre hr).mono
      (infix_of_eq ([c] ++ replicate (2 * p' + 1) (!c) ++ replicate q' c) [] ?_)
    simp [replicate_succ']
  rcases Nat.even_or_odd (q' + 1) with hqe | ⟨m, hm⟩
  · have h1 := hasNontrivialAbSq_one (!c) (q' + 1) hqe hq
    rw [Bool.not_not, replicate_succ] at h1
    refine h1.mono (infix_of_eq ([c] ++ replicate (2 * p') (!c))
      (replicate (2 * r') (!c) ++ [c]) ?_)
    rw [replicate_succ' (n := 2 * p'), replicate_succ (n := 2 * r'), replicate_succ (n := q')]
    simp only [append_assoc, cons_append, nil_append]
  rw [hm]
  rcases le_total (2 * r' + 1) (2 * p' + 1) with hle | hle
  · have h2 := hasNontrivialAbSq_two (!c) (2 * r' + 1) m (by omega)
    rw [Bool.not_not] at h2
    obtain ⟨d, hd⟩ : ∃ d, 2 * p' + 1 = d + (2 * r' + 1) := ⟨2 * p' - 2 * r', by omega⟩
    refine h2.mono (infix_of_eq ([c] ++ replicate d (!c)) [] ?_)
    rw [hd, replicate_add]
    simp only [append_assoc, append_nil]
  · have h3 := hasNontrivialAbSq_three c (2 * p' + 1) m (by omega)
    obtain ⟨d, hd⟩ : ∃ d, 2 * r' + 1 = (2 * p' + 1) + d := ⟨2 * r' - 2 * p', by omega⟩
    refine h3.mono (infix_of_eq [] (replicate d (!c) ++ [c]) ?_)
    rw [hd, replicate_add (2 * p' + 1) d]
    simp only [append_assoc, nil_append]


/-- Maximal first run: `c :: l = c^h ++ t` with `h ≥ 1` and `t` empty or starting with `!c`. -/
theorem exists_run (c : Bool) (l : List Bool) :
    ∃ h t, 1 ≤ h ∧ c :: l = replicate h c ++ t ∧ (t = [] ∨ ∃ t', t = (!c) :: t') := by
  induction l with
  | nil => exact ⟨1, [], le_rfl, rfl, Or.inl rfl⟩
  | cons d l ih =>
    by_cases hdc : d = c
    · subst hdc
      obtain ⟨h, t, hh, heq, ht⟩ := ih
      refine ⟨h + 1, t, by omega, ?_, ht⟩
      rw [heq, replicate_succ, cons_append]
    · refine ⟨1, d :: l, le_rfl, rfl, Or.inr ⟨l, ?_⟩⟩
      cases c <;> cases d <;> simp_all

/-- `θ(w)` is at least `⌊r/2⌋ + ⌊s/2⌋` whenever `c^r` and `(!c)^s` are factors of `w`
(the distinct squares `c^2, c^4, …` and `(!c)^2, (!c)^4, …`). -/
theorem card_abelianSquares_ge (w : List Bool) (c : Bool) (r s : ℕ)
    (hr : replicate r c <:+: w) (hs : replicate s (!c) <:+: w) :
    r / 2 + s / 2 ≤ (abelianSquares w).card := by
  have key : ∀ (d : Bool) (k : ℕ), replicate k d <:+: w →
      (Finset.Icc 1 (k / 2)).image (fun m => replicate (2 * m) d) ⊆ abelianSquares w ∧
      ((Finset.Icc 1 (k / 2)).image (fun m => replicate (2 * m) d)).card = k / 2 := by
    intro d k hk
    constructor
    · intro u hu
      simp only [Finset.mem_image, Finset.mem_Icc] at hu
      obtain ⟨m, ⟨hm1, hm2⟩, rfl⟩ := hu
      simp only [abelianSquares, Finset.mem_filter, mem_factors]
      refine ⟨?_, ⟨replicate m d, replicate m d, by simp; omega, Perm.refl _, ?_⟩⟩
      · refine IsInfix.trans ?_ hk
        refine infix_of_eq [] (replicate (k - 2 * m) d) ?_
        rw [nil_append, ← replicate_add]
        congr 1
        omega
      · rw [← replicate_add]
        congr 1
        omega
    · rw [Finset.card_image_of_injective _ ?_, Nat.card_Icc]
      · omega
      intro m m' hmm
      have := congrArg List.length hmm
      simp only [length_replicate] at this
      omega
  obtain ⟨hA, hAc⟩ := key c r hr
  obtain ⟨hB, hBc⟩ := key (!c) s hs
  rw [← hAc, ← hBc, ← Finset.card_union_of_disjoint]
  · exact Finset.card_le_card (Finset.union_subset hA hB)
  · rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [Finset.mem_image, Finset.mem_Icc] at hu hu'
    obtain ⟨m, ⟨hm1, -⟩, rfl⟩ := hu
    obtain ⟨m', -, hmm⟩ := hu'
    have hmem : c ∈ replicate (2 * m) c := by simp; omega
    rw [← hmm] at hmem
    cases c <;> simp at hmem


/-- If all abelian-square factors of `w` are trivial, no factor of `w` contains a
nontrivial abelian square. -/
theorem not_hasNontrivialAbSq {w : List Bool}
    (hw : ∀ u ∈ abelianSquares w, IsTrivialAbelianSquare u) {v : List Bool} (hv : v <:+: w) :
    ¬ HasNontrivialAbSq v := by
  rintro ⟨u, hu, hsq, ht, hf⟩
  have hmem : u ∈ abelianSquares w := by
    simp only [abelianSquares, Finset.mem_filter, mem_factors]
    exact ⟨hu.trans hv, hsq⟩
  obtain ⟨c, i, -, rfl⟩ := hw u hmem
  rw [mem_replicate] at ht hf
  exact Bool.noConfusion (ht.2.trans hf.2.symm)

/-- Run analysis: a word with no nontrivial abelian-square factor has a run `c^r` and a run
`(!c)^s` with `⌊|w|/4⌋ ≤ ⌊r/2⌋ + ⌊s/2⌋`. -/
theorem exists_runs_of_no_nontrivial (w : List Bool)
    (hno : ∀ v, v <:+: w → ¬ HasNontrivialAbSq v) :
    ∃ c r s, replicate r c <:+: w ∧ replicate s (!c) <:+: w ∧
      w.length / 4 ≤ r / 2 + s / 2 := by
  cases w with
  | nil => exact ⟨true, 0, 0, nil_infix, nil_infix, by simp⟩
  | cons c l =>
  obtain ⟨h, t1, hh, e1, ht1⟩ := exists_run c l
  rw [e1] at hno ⊢
  rcases ht1 with rfl | ⟨l1, rfl⟩
  · refine ⟨c, h, 0, infix_of_eq [] [] (by simp), nil_infix, by simp; omega⟩
  obtain ⟨i, t2, hi, e2, ht2⟩ := exists_run (!c) l1
  rw [e2] at hno ⊢
  rcases ht2 with rfl | ⟨l2, rfl⟩
  · refine ⟨c, h, i, infix_of_eq [] _ rfl, infix_of_eq (replicate h c) [] (by simp),
      by simp; omega⟩
  rw [Bool.not_not] at hno ⊢
  obtain ⟨j, t3, hj, e3, ht3⟩ := exists_run c l2
  rw [e3] at hno ⊢
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  -- the middle run `(!c)^i` is odd
  have hiodd : Odd i := by
    rcases Nat.even_or_odd i with hie | hio
    · exfalso
      refine hno _ ?_ (hasNontrivialAbSq_one c i hie hi)
      refine infix_of_eq (replicate h' c) (replicate j' c ++ t3) ?_
      rw [replicate_succ' (n := h'), replicate_succ (n := j')]
      simp only [append_assoc, cons_append, nil_append]
    · exact hio
  rcases ht3 with rfl | ⟨l3, rfl⟩
  · rcases le_total (h' + 1) (j' + 1) with hle | hle
    · refine ⟨c, j' + 1, i, infix_of_eq (replicate (h' + 1) c ++ replicate i (!c)) [] (by simp),
        infix_of_eq (replicate (h' + 1) c) (replicate (j' + 1) c) (by simp), ?_⟩
      obtain ⟨u, rfl⟩ := hiodd
      simp only [length_append, length_replicate, length_nil]
      omega
    · refine ⟨c, h' + 1, i, infix_of_eq [] _ rfl,
        infix_of_eq (replicate (h' + 1) c) (replicate (j' + 1) c) (by simp), ?_⟩
      obtain ⟨u, rfl⟩ := hiodd
      simp only [length_append, length_replicate, length_nil]
      omega
  obtain ⟨k, t4, hk, e4, ht4⟩ := exists_run (!c) l3
  rw [e4] at hno ⊢
  rcases ht4 with rfl | ⟨l4, rfl⟩
  · -- four runs `c^h (!c)^i c^j (!c)^k`
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨u, rfl⟩ := hiodd
    have hjodd : Odd (j' + 1) := by
      rcases Nat.even_or_odd (j' + 1) with hje | hjo
      · exfalso
        have h1 := hasNontrivialAbSq_one (!c) (j' + 1) hje hj
        rw [Bool.not_not] at h1
        refine hno _ ?_ h1
        refine infix_of_eq (replicate (h' + 1) c ++ replicate (2 * u) (!c))
          (replicate k' (!c)) ?_
        rw [replicate_succ' (n := 2 * u), replicate_succ (n := k')]
        simp only [append_assoc, cons_append, nil_append, append_nil]
      · exact hjo
    obtain ⟨v, hv⟩ := hjodd
    have hhj : h' + 1 < j' + 1 := by
      by_contra hcon
      have h2 := hasNontrivialAbSq_two c (j' + 1) u hj
      refine hno _ ?_ h2
      obtain ⟨d, hd⟩ : ∃ d, h' + 1 = d + (j' + 1) := ⟨h' - j', by omega⟩
      refine infix_of_eq (replicate d c) (replicate k' (!c)) ?_
      rw [hd, replicate_add d (j' + 1), replicate_succ (n := k')]
      simp only [append_assoc, cons_append, nil_append, append_nil]
    have hki : k' + 1 < 2 * u + 1 := by
      by_contra hcon
      have h3 := hasNontrivialAbSq_three c (2 * u + 1) v (by omega)
      rw [← hv] at h3
      refine hno _ ?_ h3
      obtain ⟨d, hd⟩ : ∃ d, k' + 1 = (2 * u + 1) + d := ⟨k' - 2 * u, by omega⟩
      refine infix_of_eq (replicate h' c) (replicate d (!c)) ?_
      rw [hd, replicate_add (2 * u + 1) d, replicate_succ' (n := h')]
      simp only [append_assoc, cons_append, nil_append, append_nil]
    refine ⟨c, j' + 1, 2 * u + 1,
      infix_of_eq (replicate (h' + 1) c ++ replicate (2 * u + 1) (!c))
        (replicate (k' + 1) (!c)) (by simp),
      infix_of_eq (replicate (h' + 1) c) (replicate (j' + 1) c ++ replicate (k' + 1) (!c))
        (by simp), ?_⟩
    simp only [length_append, length_replicate, length_nil]
    omega
  · -- five runs: impossible
    exfalso
    rw [Bool.not_not] at hno
    refine hno _ ?_ (hasNontrivialAbSq_five c i (j' + 1) k hi hj hk)
    refine infix_of_eq (replicate h' c) l4 ?_
    rw [replicate_succ' (n := h')]
    simp only [append_assoc, cons_append, nil_append]


/-- Satisfiability witness: `a b^3 a^3 b` has only the trivial abelian squares `aa` and
`bb`, attaining the bound `⌊8/4⌋ = 2`. -/
example :
    let w := [true, false, false, false, true, true, true, false]
    (∀ u ∈ abelianSquares w, IsTrivialAbelianSquare u) ∧ (abelianSquares w).card = 2 := by
  intro w
  have hw : abelianSquares w = {[true, true], [false, false]} := by decide
  refine ⟨?_, by rw [hw]; decide⟩
  intro u hu
  rw [hw, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · exact ⟨true, 1, Nat.one_pos, rfl⟩
  · exact ⟨false, 1, Nat.one_pos, rfl⟩

/-- **Fici–Saarela (Theorem 2 of arXiv:2604.23188, after Fici–Saarela 2014).**
If every abelian-square factor of a binary word `w` is trivial (of the form `a^{2i}` or
`b^{2i}`), then `w` contains at least `⌊|w|/4⌋` distinct abelian squares. -/
theorem fici_saarela_of_trivial (w : List Bool)
    (hw : ∀ u ∈ abelianSquares w, IsTrivialAbelianSquare u) :
    w.length / 4 ≤ (abelianSquares w).card := by
  obtain ⟨c, r, s, hr, hs, hle⟩ :=
    exists_runs_of_no_nontrivial w (fun v hv => not_hasNontrivialAbSq hw hv)
  exact hle.trans (card_abelianSquares_ge w c r s hr hs)

end Candidates.FewAbelianSquaresFiciSaarela
