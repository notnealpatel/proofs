/-
# Pattern avoidance in canon permutations: Conjecture 1231

## Source

R. Laudone, *Pattern avoidance in canon permutations*, arXiv:2608.21351,
Section "Further directions", subsection "Changing the patterns",
Conjecture `conj: 1231` (with the special cases listed right after it).
Pulled with `fetch 2608.21351` on 2026-10-21.

Verbatim:

> \begin{conjecture} \label{conj: 1231}
>     Let $a_n = |\mathcal{L}_n^k(\O(1231))|$. Then $a_1 = 1$, $a_2 = C_k$, and for
>     $n \ge 3$ and $k \ge 1$,
>     \[ a_n = a_{n-1} + (C_k - 1) \, a_{n-2}. \]
> \end{conjecture}
>
> Here $\O(1231) = \{1231,1321,2132,2312,3123,3213\}$. [...]
> If we take $n = 3$, we get $|\mathcal{L}_3^k(\O(1231))| = 2C_k -1$ for every $k \ge 1$.

Definitions from the paper: a *lattice word* on `[n]` is a word in which every prefix has at
least as many letters `i` as letters `i + 1` (`1 ≤ i ≤ n - 1`); `𝓛_n^k` is the set of
`k`-regular lattice words of length `kn` on `[n]`; a word contains a pattern if some
subsequence has the same relative order (here, the same equality pattern, since every pattern
in `O(1231)` has pairwise distinct letters apart from the repeated `x`).

## Status

Open in the paper (stated as a conjecture, supported by computation).  Proved here, for every
`k ≥ 0`, by the following decomposition (`latticeWords1231_eq`): a word in `𝓛_{n+2}^k(O(1231))`
is either `0^k` followed by a word of `𝓛_{n+1}^k(O(1231))` shifted up by one, or a `k`-regular
binary lattice word on `{0, 1}` other than `0^k 1^k` (a Dyck word of semilength `k` other than
`U^k D^k`; there are `C_k - 1`) followed by a word of `𝓛_n^k(O(1231))` shifted up by two.

Computation (2026-10-21, exhaustive, python): `a_n` matches the recurrence for
`k = 2, n ≤ 8`; `k = 3, n ≤ 7`; `k = 4, n ≤ 5`; `k = 5, n ≤ 4`; `k ∈ {0, 1}, n ≤ 8`.
-/
import Mathlib

set_option autoImplicit false
open List

namespace CanonPermutationPattern1231

/-- A word `w` *contains a pattern of `O(1231)`* if it has a (not necessarily contiguous)
subsequence `x y z x` with `x, y, z` pairwise distinct.  The orbit
`O(1231) = {1231, 1321, 2132, 2312, 3123, 3213}` is exactly the set of relabelings of `1231`,
so containing some element of `O(1231)` in the paper's classical sense is this predicate. -/
def Contains1231 {α : Type*} (w : List α) : Prop :=
  ∃ x y z : α, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ [x, y, z, x] <+ w

/-- A word over `Fin m` is `k`-regular if every letter occurs exactly `k` times. -/
def IsRegular (k : ℕ) {m : ℕ} (w : List (Fin m)) : Prop :=
  ∀ i : Fin m, w.count i = k

/-- A word over `Fin m` is a *lattice word* if in every prefix the number of occurrences of the
letter `i` is at least the number of occurrences of the letter `i + 1` (letters are `0`-indexed:
the paper's letter `i ∈ [n]` is `i - 1 : Fin n` here). -/
def IsLattice {m : ℕ} (w : List (Fin m)) : Prop :=
  ∀ p ∈ w.inits, ∀ i j : Fin m, i.val + 1 = j.val → p.count j ≤ p.count i

/-- `𝓛_m^k(O(1231))`: the `k`-regular lattice words on the alphabet `[m]` (here `Fin m`) that
avoid every pattern of `O(1231)`. -/
def latticeWords1231 (k m : ℕ) : Set (List (Fin m)) :=
  {w | IsRegular k w ∧ IsLattice w ∧ ¬ Contains1231 w}

/-- The paper's `a_n = |𝓛_n^k(O(1231))|`, written `a k n`. -/
noncomputable def a (k m : ℕ) : ℕ := (latticeWords1231 k m).ncard

/-- Decidability, used by the ground-truth `decide` checks. -/
instance {m : ℕ} (w : List (Fin m)) : Decidable (Contains1231 w) := by
  unfold Contains1231; infer_instance

/-- Decidability, used by the ground-truth `decide` checks. -/
instance {k m : ℕ} (w : List (Fin m)) : Decidable (IsRegular k w) := by
  unfold IsRegular; infer_instance

/-- Decidability, used by the ground-truth `decide` checks. -/
instance {m : ℕ} (w : List (Fin m)) : Decidable (IsLattice w) := by
  unfold IsLattice; infer_instance

/-! ### Ground truth

For `k = 2`, `n = 3` the conjecture predicts `a_3 = 2 C_2 - 1 = 3`; the three words are
`001122`, `001212`, `010122` (letters shifted to start at `0`). -/

example : IsRegular 2 [(0 : Fin 3), 0, 1, 1, 2, 2] ∧ IsLattice [(0 : Fin 3), 0, 1, 1, 2, 2] ∧
    ¬ Contains1231 [(0 : Fin 3), 0, 1, 1, 2, 2] := by decide
example : IsRegular 2 [(0 : Fin 3), 0, 1, 2, 1, 2] ∧ IsLattice [(0 : Fin 3), 0, 1, 2, 1, 2] ∧
    ¬ Contains1231 [(0 : Fin 3), 0, 1, 2, 1, 2] := by decide
example : IsRegular 2 [(0 : Fin 3), 1, 0, 1, 2, 2] ∧ IsLattice [(0 : Fin 3), 1, 0, 1, 2, 2] ∧
    ¬ Contains1231 [(0 : Fin 3), 1, 0, 1, 2, 2] := by decide
/-- `010212` is a regular lattice word but contains `1 0 2 1`. -/
example : IsRegular 2 [(0 : Fin 3), 1, 0, 2, 1, 2] ∧ IsLattice [(0 : Fin 3), 1, 0, 2, 1, 2] ∧
    Contains1231 [(0 : Fin 3), 1, 0, 2, 1, 2] := by decide
/-- `012012` contains `0 1 2 0`. -/
example : Contains1231 [(0 : Fin 3), 1, 2, 0, 1, 2] := by decide
/-- `0110...` is not a lattice word (the prefix `011` has more `1`s than `0`s). -/
example : ¬ IsLattice [(0 : Fin 2), 1, 1, 0] := by decide
/-- The paper's example lattice word `111122112231122333223333` (`k = 8`, `n = 3`), shifted. -/
example : IsRegular 8 [(0 : Fin 3), 0, 0, 0, 1, 1, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 2, 2, 1, 1,
      2, 2, 2, 2] ∧
    IsLattice [(0 : Fin 3), 0, 0, 0, 1, 1, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2] :=
  by decide

/-- A `1231`-occurrence in `A ++ B` lies entirely in `A` or entirely in `B` when `A` and `B`
share no letter. -/
theorem contains_append {α : Type*} {A B : List α} (h : Contains1231 (A ++ B))
    (hd : ∀ x ∈ A, x ∉ B) : Contains1231 A ∨ Contains1231 B := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := h
  obtain ⟨l1, l2, heq, h1, h2⟩ := List.sublist_append_iff.mp hs
  rcases l1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l1⟩⟩⟩⟩⟩
  · simp only [nil_append] at heq
    exact Or.inr ⟨x, y, z, hxy, hxz, hyz, heq ▸ h2⟩
  all_goals simp only [cons_append, nil_append, cons.injEq] at heq
  · obtain ⟨rfl, rfl⟩ := heq
    exact absurd (h2.subset (by simp)) (hd x (h1.subset (by simp)))
  · obtain ⟨rfl, rfl, rfl⟩ := heq
    exact absurd (h2.subset (by simp)) (hd x (h1.subset (by simp)))
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    exact absurd (h2.subset (by simp)) (hd x (h1.subset (by simp)))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
    exact Or.inl ⟨x, y, z, hxy, hxz, hyz, h1⟩
  · obtain ⟨-, -, -, -, h5⟩ := heq
    simp at h5

/-- `O(1231)`-containment is invariant under injective relabeling of letters. -/
theorem contains_map_iff {α β : Type*} {f : α → β} (hf : Function.Injective f) {w : List α} :
    Contains1231 (w.map f) ↔ Contains1231 w := by
  constructor
  · rintro ⟨x, y, z, hxy, hxz, hyz, hs⟩
    obtain ⟨l, hl, heq⟩ := List.sublist_map_iff.mp hs
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;>
      simp only [map_cons, map_nil, cons.injEq, reduceCtorEq, and_false] at heq
    obtain ⟨rfl, rfl, rfl, had, -⟩ := heq
    obtain rfl := hf had
    exact ⟨a, b, c, fun h => hxy (congrArg f h), fun h => hxz (congrArg f h),
      fun h => hyz (congrArg f h), hl⟩
  · rintro ⟨x, y, z, hxy, hxz, hyz, hs⟩
    exact ⟨f x, f y, f z, hf.ne hxy, hf.ne hxz, hf.ne hyz, by simpa using hs.map f⟩

/-- A word using at most two distinct letters avoids `O(1231)`. -/
theorem not_contains_of_two {α : Type*} {w : List α} {u v : α}
    (h : ∀ c ∈ w, c = u ∨ c = v) : ¬ Contains1231 w := by
  rintro ⟨x, y, z, hxy, hxz, hyz, hs⟩
  have hx := h x (hs.subset (by simp))
  have hy := h y (hs.subset (by simp))
  have hz := h z (hs.subset (by simp))
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp_all

/-- The lattice condition, stated with `List.take` instead of `List.inits`. -/
theorem isLattice_iff_take {m : ℕ} {w : List (Fin m)} :
    IsLattice w ↔ ∀ t : ℕ, ∀ i j : Fin m, i.val + 1 = j.val →
      (w.take t).count j ≤ (w.take t).count i := by
  constructor
  · intro h t i j hij
    exact h _ ((List.mem_inits _ _).mpr (List.take_prefix t w)) i j hij
  · intro h p hp i j hij
    rw [List.mem_inits, List.prefix_iff_eq_take] at hp
    rw [hp]
    exact h _ i j hij


/-- `0` does not occur in a word shifted by `Fin.succ`. -/
theorem count_map_succ_zero {m : ℕ} (l : List (Fin m)) : (l.map Fin.succ).count 0 = 0 := by
  simp [List.count_eq_zero, Fin.succ_ne_zero]

/-- Shifting by `Fin.succ` preserves letter counts. -/
theorem count_map_succ_succ {m : ℕ} (l : List (Fin m)) (j : Fin m) :
    (l.map Fin.succ).count j.succ = l.count j :=
  List.count_map_of_injective _ _ (Fin.succ_injective _) _

/-- The first decomposition map: `w ↦ 0^k (w + 1)`, i.e. a block of `k` zeros followed by `w`
with every letter shifted up by one. -/
def prepend (k : ℕ) {m : ℕ} (w : List (Fin m)) : List (Fin (m + 1)) :=
  List.replicate k 0 ++ w.map Fin.succ

/-- `prepend k w` has exactly `k` zeros. -/
theorem count_prepend_zero (k : ℕ) {m : ℕ} (w : List (Fin m)) :
    (prepend k w).count 0 = k := by
  simp [prepend, count_map_succ_zero, List.count_replicate_self]

/-- Prefixes of `prepend k w`. -/
theorem take_prepend (k : ℕ) {m : ℕ} (w : List (Fin m)) (t : ℕ) :
    (prepend k w).take t = List.replicate (min t k) 0 ++ (w.take (t - k)).map Fin.succ := by
  simp [prepend, List.take_append, List.take_replicate, List.map_take]

/-- `prepend k` maps `𝓛_m^k(O(1231))` into `𝓛_{m+1}^k(O(1231))`. -/
theorem prepend_mem {k m : ℕ} {w : List (Fin m)} (hw : w ∈ latticeWords1231 k m) :
    prepend k w ∈ latticeWords1231 k (m + 1) := by
  obtain ⟨hreg, hlat, hav⟩ := hw
  refine ⟨?_, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact count_prepend_zero k w
    | succ i =>
      simp [prepend, count_map_succ_succ, List.count_replicate, (Fin.succ_ne_zero i).symm, hreg i]
  · rw [isLattice_iff_take] at hlat ⊢
    intro t i j hij
    rw [take_prepend]
    cases j using Fin.cases with
    | zero => simp at hij
    | succ j =>
      cases i using Fin.cases with
      | zero =>
        simp only [List.count_append, count_map_succ_succ, count_map_succ_zero,
          List.count_replicate_self, List.count_replicate, beq_iff_eq,
          (Fin.succ_ne_zero j).symm, if_false, zero_add, add_zero]
        rcases le_or_gt t k with htk | htk
        · simp [Nat.sub_eq_zero_of_le htk]
        · have hle : (w.take (t - k)).count j ≤ w.count j := (List.take_sublist _ _).count_le j
          rw [hreg j] at hle
          omega
      | succ i =>
        simp only [List.count_append, count_map_succ_succ, List.count_replicate, beq_iff_eq,
          (Fin.succ_ne_zero j).symm, (Fin.succ_ne_zero i).symm, if_false, zero_add]
        exact hlat (t - k) i j (by simpa using hij)
  · intro hc
    rcases contains_append hc (by
        intro x hx hx'
        rw [(List.eq_of_mem_replicate hx)] at hx'
        simp [Fin.succ_ne_zero] at hx') with h | h
    · exact not_contains_of_two (u := 0) (v := 0)
        (fun c hc => Or.inl (List.eq_of_mem_replicate hc)) h
    · exact hav ((contains_map_iff (Fin.succ_injective _)).mp h)


/-- Every `i : Fin (m + 2)` is `0`, `1`, or `j + 2` for some `j : Fin m`. -/
theorem fin_trichotomy {m : ℕ} (i : Fin (m + 2)) :
    i = 0 ∨ i = Fin.succ 0 ∨ ∃ i' : Fin m, i = i'.succ.succ := by
  cases i using Fin.cases with
  | zero => exact Or.inl rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => exact Or.inr (Or.inl rfl)
    | succ i => exact Or.inr (Or.inr ⟨i, rfl⟩)

/-- Encode a Dyck step as a letter: `U ↦ 0`, `D ↦ 1`. -/
def dyckLetter {m : ℕ} : DyckStep → Fin (m + 2)
  | .U => 0
  | .D => Fin.succ 0

/-- `dyckLetter` is injective. -/
theorem dyckLetter_injective {m : ℕ} : Function.Injective (dyckLetter (m := m)) := by
  intro s t h
  cases s <;> cases t <;> first | rfl | exact absurd h (by simp [dyckLetter])

/-- An encoded Dyck step is never a letter `≥ 2`. -/
theorem dyckLetter_ne_succ_succ {m : ℕ} (s : DyckStep) (i : Fin m) :
    dyckLetter s ≠ i.succ.succ := by
  cases s
  · exact (Fin.succ_ne_zero _).symm
  · intro h
    have hv := congrArg Fin.val h
    simp only [dyckLetter, Fin.val_succ, Fin.val_zero] at hv
    omega

/-- The second decomposition map: a Dyck word `p` (encoded on the letters `0, 1`) followed by `w`
with every letter shifted up by two. -/
def splice {m : ℕ} (p : DyckWord) (w : List (Fin m)) : List (Fin (m + 2)) :=
  p.toList.map dyckLetter ++ (w.map Fin.succ).map Fin.succ

/-- Counting encoded Dyck steps. -/
theorem count_dyck_dyckLetter {m : ℕ} (l : List DyckStep) (s : DyckStep) :
    (l.map (dyckLetter (m := m))).count (dyckLetter s) = l.count s :=
  List.count_map_of_injective _ _ dyckLetter_injective _

/-- Letters `≥ 2` do not occur in an encoded Dyck word. -/
theorem count_dyck_succ_succ {m : ℕ} (l : List DyckStep) (i : Fin m) :
    (l.map (dyckLetter (m := m))).count i.succ.succ = 0 := by
  rw [List.count_eq_zero]
  simp only [List.mem_map, not_exists, not_and]
  exact fun s _ => dyckLetter_ne_succ_succ s i

/-- `0` does not occur in a word shifted by two. -/
theorem count_ss_zero {m : ℕ} (l : List (Fin m)) :
    ((l.map Fin.succ).map Fin.succ).count 0 = 0 := count_map_succ_zero _

/-- `1` does not occur in a word shifted by two. -/
theorem count_ss_one {m : ℕ} (l : List (Fin m)) :
    ((l.map Fin.succ).map Fin.succ).count (Fin.succ 0) = 0 := by
  rw [count_map_succ_succ, count_map_succ_zero]

/-- Shifting by two preserves letter counts. -/
theorem count_ss_ss {m : ℕ} (l : List (Fin m)) (j : Fin m) :
    ((l.map Fin.succ).map Fin.succ).count j.succ.succ = l.count j := by
  rw [count_map_succ_succ, count_map_succ_succ]

/-- Prefixes of `splice p w`. -/
theorem take_splice {m : ℕ} (p : DyckWord) (w : List (Fin m)) (t : ℕ) :
    (splice p w).take t = (p.toList.take t).map dyckLetter ++
      ((w.take (t - p.toList.length)).map Fin.succ).map Fin.succ := by
  simp [splice, List.take_append, List.map_take]

/-- For a Dyck word `p` of semilength `k`, `splice p` maps `𝓛_m^k(O(1231))` into
`𝓛_{m+2}^k(O(1231))`. -/
theorem splice_mem {k m : ℕ} {p : DyckWord} (hp : p.semilength = k) {w : List (Fin m)}
    (hw : w ∈ latticeWords1231 k m) : splice p w ∈ latticeWords1231 k (m + 2) := by
  obtain ⟨hreg, hlat, hav⟩ := hw
  have hU : p.toList.count .U = k := hp
  have hD : p.toList.count .D = k := by rw [← DyckWord.semilength_eq_count_D, hp]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases fin_trichotomy i with rfl | rfl | ⟨i, rfl⟩
    · simp only [splice, List.count_append, count_ss_zero, add_zero]
      exact (count_dyck_dyckLetter p.toList .U).trans hU
    · simp only [splice, List.count_append, count_ss_one, add_zero]
      exact (count_dyck_dyckLetter p.toList .D).trans hD
    · simp only [splice, List.count_append, count_ss_ss, count_dyck_succ_succ, zero_add]
      exact hreg i
  · rw [isLattice_iff_take] at hlat ⊢
    intro t i j hij
    rw [take_splice]
    rcases fin_trichotomy i with rfl | rfl | ⟨i, rfl⟩ <;>
      rcases fin_trichotomy j with rfl | rfl | ⟨j, rfl⟩ <;>
      simp only [Fin.val_zero, Fin.val_succ] at hij
    all_goals first | omega | skip
    · simp only [List.count_append, count_ss_one, count_ss_zero, add_zero]
      have h1 := count_dyck_dyckLetter (m := m) (p.toList.take t) .D
      have h0 := count_dyck_dyckLetter (m := m) (p.toList.take t) .U
      simp only [dyckLetter] at h1 h0
      rw [h1, h0]
      exact p.count_D_le_count_U t
    · simp only [List.count_append, count_ss_ss, count_dyck_succ_succ, zero_add, count_ss_one,
        add_zero]
      have h1 := count_dyck_dyckLetter (m := m) (p.toList.take t) .D
      simp only [dyckLetter] at h1
      rw [h1]
      rcases le_or_gt t p.toList.length with htk | htk
      · simp [Nat.sub_eq_zero_of_le htk]
      · have hle : (w.take (t - p.toList.length)).count j ≤ w.count j :=
          (List.take_sublist _ _).count_le j
        rw [hreg j] at hle
        rw [List.take_of_length_le htk.le, hD]
        exact hle
    · simp only [List.count_append, count_ss_ss, count_dyck_succ_succ, zero_add]
      exact hlat _ i j (by omega)
  · intro hc
    rcases contains_append hc (by
        intro x hx hx'
        simp only [List.mem_map] at hx hx'
        obtain ⟨s, -, rfl⟩ := hx
        obtain ⟨y, ⟨z, -, rfl⟩, hy⟩ := hx'
        exact dyckLetter_ne_succ_succ s z hy.symm) with h | h
    · refine not_contains_of_two (u := 0) (v := Fin.succ 0) (fun c hc => ?_) h
      simp only [List.mem_map] at hc
      obtain ⟨s, -, rfl⟩ := hc
      cases s
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact hav ((contains_map_iff (Fin.succ_injective _)).mp
        ((contains_map_iff (Fin.succ_injective _)).mp h))


/-- The Dyck word `U^k D^k`; it encodes the binary lattice word `0^k 1^k`. -/
def stair (k : ℕ) : DyckWord where
  toList := List.replicate k .U ++ List.replicate k .D
  count_U_eq_count_D := by simp [List.count_replicate]
  count_D_le_count_U i := by
    simp [List.take_append, List.take_replicate, List.count_replicate]

/-- A list of Dyck steps with no `D` before a `U` is `U^a D^b`. -/
theorem eq_stair_of_not_sublist (l : List DyckStep) (h : ¬ [DyckStep.D, DyckStep.U] <+ l) :
    l = List.replicate (l.count .U) .U ++ List.replicate (l.count .D) .D := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | U =>
      have h' : ¬ [DyckStep.D, DyckStep.U] <+ l := fun h' => h (h'.cons _)
      rw [ih h']
      simp [List.count_replicate, List.replicate_succ]
    | D =>
      have hU : DyckStep.U ∉ l := fun hU => h ((List.singleton_sublist.mpr hU).cons_cons _)
      have hlD : ∀ c ∈ l, c = DyckStep.D := by
        intro c hc
        cases c
        · exact absurd hc hU
        · rfl
      rw [List.eq_replicate_iff.mpr ⟨rfl, hlD⟩]
      simp [List.count_replicate, List.replicate_succ]


/-- `O(1231)`-containment is monotone under taking superwords. -/
theorem Contains1231.mono {α : Type*} {l l' : List α} (h : Contains1231 l) (hl : l <+ l') :
    Contains1231 l' := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := h
  exact ⟨x, y, z, hxy, hxz, hyz, hs.trans hl⟩

/-- If `A` uses only the letter `y ≠ x` and `y ∉ B`, then `x y` is not a subsequence of
`A ++ B`. -/
theorem not_pair_sublist_append {α : Type*} {x y : α} {A B : List α} (hA : ∀ c ∈ A, c = y)
    (hxy : x ≠ y) (hB : y ∉ B) : ¬ [x, y] <+ A ++ B := by
  intro hs
  obtain ⟨l1, l2, heq, h1, h2⟩ := List.sublist_append_iff.mp hs
  rcases l1 with _ | ⟨a, _ | ⟨b, l1⟩⟩
  · simp only [nil_append] at heq
    exact hB (h2.subset (by simp [← heq]))
  · simp only [cons_append, nil_append, cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact hxy (hA _ (h1.subset (by simp)))
  · simp only [cons_append, cons.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact hxy (hA _ (h1.subset (by simp)))

/-- A list all of whose entries lie in the range of `f` is the image of a list under `f`. -/
theorem exists_map_eq {α β : Type*} {f : α → β} {t : List β} (h : ∀ c ∈ t, ∃ a, f a = c) :
    ∃ v : List α, v.map f = t := by
  induction t with
  | nil => exact ⟨[], rfl⟩
  | cons c t ih =>
    obtain ⟨a, ha⟩ := h c (by simp)
    obtain ⟨v, hv⟩ := ih (fun c' hc' => h c' (by simp [hc']))
    exact ⟨a :: v, by simp [ha, hv]⟩

/-- Regularity descends from `u ++ map f v` to `v` when no `f j` occurs in `u`. -/
theorem regular_of_append_map {k m m' : ℕ} {u : List (Fin m')} {v : List (Fin m)}
    {f : Fin m → Fin m'} (hf : Function.Injective f) (hu : ∀ j, f j ∉ u)
    (h : IsRegular k (u ++ v.map f)) : IsRegular k v := by
  intro j
  have hj := h (f j)
  rwa [List.count_append, List.count_eq_zero.mpr (hu j), zero_add,
    List.count_map_of_injective _ _ hf] at hj

/-- The lattice property descends from `u ++ map f v` to `v` when `f` is injective, no `f j`
occurs in `u`, and `f` preserves adjacency of letters. -/
theorem lattice_of_append_map {m m' : ℕ} {u : List (Fin m')} {v : List (Fin m)}
    {f : Fin m → Fin m'} (hf : Function.Injective f) (hu : ∀ j, f j ∉ u)
    (hadj : ∀ i j : Fin m, i.val + 1 = j.val → (f i).val + 1 = (f j).val)
    (h : IsLattice (u ++ v.map f)) : IsLattice v := by
  rw [isLattice_iff_take] at h ⊢
  intro s i j hij
  have hs := h (u.length + s) (f i) (f j) (hadj i j hij)
  have htake : (u ++ v.map f).take (u.length + s) = u ++ (v.take s).map f := by
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      List.map_take]
  rwa [htake, List.count_append, List.count_append, List.count_eq_zero.mpr (hu i),
    List.count_eq_zero.mpr (hu j), zero_add, zero_add, List.count_map_of_injective _ _ hf,
    List.count_map_of_injective _ _ hf] at hs

/-- `prepend k` is injective. -/
theorem prepend_injective (k : ℕ) {m : ℕ} : Function.Injective (prepend k (m := m)) := by
  intro w w' h
  exact (List.map_injective_iff.mpr (Fin.succ_injective _)) (List.append_cancel_left h)

/-- `splice` is injective on Dyck words of a fixed semilength. -/
theorem splice_injOn {k m : ℕ} {p p' : DyckWord} (hp : p.semilength = k)
    (hp' : p'.semilength = k) {w w' : List (Fin m)} (h : splice p w = splice p' w') :
    p = p' ∧ w = w' := by
  have hlen : (p.toList.map (dyckLetter (m := m))).length =
      (p'.toList.map (dyckLetter (m := m))).length := by
    rw [List.length_map, List.length_map, ← p.two_mul_semilength_eq_length,
      ← p'.two_mul_semilength_eq_length, hp, hp']
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  refine ⟨DyckWord.ext ((List.map_injective_iff.mpr dyckLetter_injective) h1), ?_⟩
  exact (List.map_injective_iff.mpr (Fin.succ_injective _))
    ((List.map_injective_iff.mpr (Fin.succ_injective _)) h2)

/-- A Dyck word of semilength `k` other than `U^k D^k` has a `D` before some `U`. -/
theorem dyck_sublist_of_ne_stair {k : ℕ} {p : DyckWord} (hp : p.semilength = k)
    (hne : p ≠ stair k) : [DyckStep.D, DyckStep.U] <+ p.toList := by
  by_contra hs
  apply hne
  ext1
  rw [eq_stair_of_not_sublist _ hs, ← DyckWord.semilength_eq_count_D]
  change replicate p.semilength DyckStep.U ++ replicate p.semilength DyckStep.D = _
  rw [hp]
  rfl

/-- The images of `prepend` and of `splice` (on Dyck words other than `U^k D^k`) are
disjoint: `1 0` is a subsequence of the latter but not of the former. -/
theorem prepend_ne_splice {k m : ℕ} {p : DyckWord} (hp : p.semilength = k)
    (hne : p ≠ stair k) (w : List (Fin (m + 1))) (w' : List (Fin m)) :
    prepend k w ≠ splice p w' := by
  intro h
  have hs : [Fin.succ (0 : Fin (m + 1)), 0] <+ splice p w' := by
    have := (dyck_sublist_of_ne_stair hp hne).map (dyckLetter (m := m))
    exact this.trans (List.sublist_append_left _ _)
  rw [← h] at hs
  refine not_pair_sublist_append (fun c hc => List.eq_of_mem_replicate hc)
    (Fin.succ_ne_zero _) ?_ hs
  simp [Fin.succ_ne_zero]


/-- Split a list into its longest prefix satisfying `P` and the remainder. -/
theorem split_prefix {α : Type*} (P : α → Prop) [DecidablePred P] (w : List α) :
    ∃ d t : List α, w = d ++ t ∧ (∀ c ∈ d, P c) ∧ (∀ c0 t', t = c0 :: t' → ¬ P c0) := by
  induction w with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons a w ih =>
    by_cases ha : P a
    · obtain ⟨d, t, hw, hd, ht⟩ := ih
      refine ⟨a :: d, t, by simp [hw], ?_, ht⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ha
      · exact hd c hc
    · refine ⟨[], a :: w, rfl, by simp, ?_⟩
      intro c0 t' h
      obtain ⟨rfl, -⟩ := List.cons.inj h
      exact ha

/-- In a lattice word, a letter `c` cannot occur before every occurrence of its predecessor. -/
theorem lattice_prefix_contra {m : ℕ} {w : List (Fin m)} (hl : IsLattice w)
    {u rest : List (Fin m)} {c i : Fin m} (hw : w = u ++ c :: rest) (hic : i.val + 1 = c.val)
    (hi : i ∉ u) : False := by
  rw [isLattice_iff_take] at hl
  have h := hl (u.length + 1) i c hic
  have htake : w.take (u.length + 1) = u ++ [c] := by
    rw [hw, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
    rfl
  have hic' : i ≠ c := fun h' => by rw [h'] at hic; omega
  rw [htake, List.count_append, List.count_append, List.count_eq_zero.mpr hi,
    List.count_singleton_self, List.count_singleton, if_neg (by simpa using hic'.symm)] at h
  omega

/-- If `x y` is a subsequence of `A ++ B` and `y ∉ B`, then `x y` is a subsequence of `A`. -/
theorem pair_sublist_left {α : Type*} {x y : α} {A B : List α} (hs : [x, y] <+ A ++ B)
    (hB : y ∉ B) : [x, y] <+ A := by
  obtain ⟨l1, l2, heq, h1, h2⟩ := List.sublist_append_iff.mp hs
  rcases l1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, l1⟩⟩⟩
  · simp only [nil_append] at heq
    exact absurd (h2.subset (by simp [← heq])) hB
  · simp only [cons_append, nil_append, cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact absurd (h2.subset (by simp)) hB
  · simp only [cons_append, nil_append, cons.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact h1
  · simp at heq

/-- Decomposition, first case: if no `1` precedes a `0` in `w ∈ 𝓛_{m+2}^k(O(1231))`, then
`w = 0^k (w' + 1)` with `w' ∈ 𝓛_{m+1}^k(O(1231))`. -/
theorem surj_prepend {k m : ℕ} {w : List (Fin (m + 2))} (hw : w ∈ latticeWords1231 k (m + 2))
    (h10 : ¬ [Fin.succ 0, 0] <+ w) :
    ∃ w' ∈ latticeWords1231 k (m + 1), prepend k w' = w := by
  obtain ⟨hreg, hlat, hav⟩ := hw
  obtain ⟨d, t, hwdt, hd, ht⟩ := split_prefix (fun c : Fin (m + 2) => c = 0) w
  have ht0 : ∀ c ∈ t, c ≠ 0 := by
    rintro c hc rfl
    rcases t with _ | ⟨c0, t'⟩
    · simp at hc
    have hc0 : c0 ≠ 0 := ht c0 t' rfl
    have h0t' : (0 : Fin (m + 2)) ∈ t' := by
      rcases List.mem_cons.mp hc with h | h
      · exact absurd h.symm hc0
      · exact h
    rcases fin_trichotomy c0 with rfl | rfl | ⟨j, rfl⟩
    · exact hc0 rfl
    · apply h10
      rw [hwdt]
      exact ((List.singleton_sublist.mpr h0t').cons_cons _).trans (List.sublist_append_right _ _)
    · refine lattice_prefix_contra hlat (i := j.succ.castSucc) hwdt (by simp) ?_
      intro hj
      have := hd _ hj
      exact absurd this (by simp [Fin.ext_iff])
  obtain ⟨w', hw'⟩ := exists_map_eq (f := Fin.succ) (fun c hc => Fin.exists_succ_eq.mpr (ht0 c hc))
  have hdrep : d = List.replicate d.length 0 := List.eq_replicate_iff.mpr ⟨rfl, hd⟩
  have hdlen : d.length = k := by
    have h0 := hreg 0
    rw [hwdt, List.count_append, List.count_eq_zero.mpr (fun h => ht0 0 h rfl), add_zero,
      hdrep, List.count_replicate_self] at h0
    rw [hdrep, List.length_replicate]
    exact h0
  have hwp : w = prepend k w' := by
    rw [prepend, hw', hwdt, hdrep, hdlen]
  have hu : ∀ j : Fin (m + 1), j.succ ∉ List.replicate k (0 : Fin (m + 2)) := by
    intro j hj
    exact Fin.succ_ne_zero j (List.eq_of_mem_replicate hj)
  refine ⟨w', ⟨?_, ?_, ?_⟩, hwp.symm⟩
  · rw [hwp] at hreg
    exact regular_of_append_map (Fin.succ_injective _) hu hreg
  · rw [hwp] at hlat
    exact lattice_of_append_map (Fin.succ_injective _) hu (fun i j hij => by simp [hij]) hlat
  · intro hc
    apply hav
    rw [hwp]
    exact ((contains_map_iff (Fin.succ_injective _)).mpr hc).mono (List.sublist_append_right _ _)


/-- Decode a letter as a Dyck step: `0 ↦ U`, anything else `↦ D`. -/
def toStep {m : ℕ} (c : Fin (m + 2)) : DyckStep := if c = 0 then .U else .D

/-- Decomposition, second case: if some `1` precedes a `0` in `w ∈ 𝓛_{m+2}^k(O(1231))`, then all
`0`s and `1`s precede every letter `≥ 2`, and `w = splice p w''` with `p` a Dyck word of
semilength `k` other than `U^k D^k` and `w'' ∈ 𝓛_m^k(O(1231))`. -/
theorem surj_splice {k m : ℕ} {w : List (Fin (m + 2))} (hw : w ∈ latticeWords1231 k (m + 2))
    (h10 : [Fin.succ 0, 0] <+ w) :
    ∃ p : DyckWord, (p.semilength = k ∧ p ≠ stair k) ∧
      ∃ w'' ∈ latticeWords1231 k m, splice p w'' = w := by
  obtain ⟨hreg, hlat, hav⟩ := hw
  obtain ⟨d, t, hwdt, hd, ht⟩ := split_prefix (fun c : Fin (m + 2) => c.val < 2) w
  have hd01 : ∀ c ∈ d, c = 0 ∨ c = Fin.succ 0 := by
    intro c hc
    have := hd c hc
    rcases fin_trichotomy c with h | h | ⟨j, rfl⟩
    · exact Or.inl h
    · exact Or.inr h
    · simp at this
  -- the head of `t` forces `0` and then `1` to occur in `d`
  have hhead : ∀ c0 t', t = c0 :: t' → [0, Fin.succ 0] <+ d := by
    intro c0 t' hct
    have hc0 : ¬ c0.val < 2 := ht c0 t' hct
    have hw' : w = d ++ c0 :: t' := by rw [hwdt, hct]
    have h1d : Fin.succ (0 : Fin (m + 1)) ∈ d := by
      by_contra h1d
      refine lattice_prefix_contra hlat (i := ⟨c0.val - 1, by omega⟩) hw' (by show c0.val - 1 + 1 = c0.val; omega) ?_
      intro hi
      have hv := hd _ hi
      have heq : (⟨c0.val - 1, by omega⟩ : Fin (m + 2)) = Fin.succ 0 :=
        Fin.ext (by simp only [Fin.val_succ, Fin.val_zero] at hv ⊢; omega)
      exact h1d (heq ▸ hi)
    obtain ⟨d1, d2, hd12⟩ := List.append_of_mem h1d
    have h0d1 : (0 : Fin (m + 2)) ∈ d1 := by
      by_contra h0
      exact lattice_prefix_contra hlat (u := d1) (rest := d2 ++ c0 :: t') (c := Fin.succ 0)
        (i := 0) (by rw [hw', hd12]; simp) (by simp) h0
    rw [hd12]
    exact (List.singleton_sublist.mpr h0d1).append ((List.nil_sublist d2).cons_cons _)
  have hne : ∀ c0 : Fin (m + 2), ¬ c0.val < 2 →
      (0 : Fin (m + 2)) ≠ Fin.succ 0 ∧ (0 : Fin (m + 2)) ≠ c0 ∧ Fin.succ 0 ≠ c0 := by
    intro c0 hc0
    refine ⟨(Fin.succ_ne_zero _).symm, fun h => hc0 (by simp [← h]), fun h => hc0 (by simp [← h])⟩
  have h0t : (0 : Fin (m + 2)) ∉ t := by
    intro h0
    rcases t with _ | ⟨c0, t'⟩
    · simp at h0
    have hc0 : ¬ c0.val < 2 := ht c0 t' rfl
    obtain ⟨n01, n0c, n1c⟩ := hne c0 hc0
    have h0t' : (0 : Fin (m + 2)) ∈ t' := by
      rcases List.mem_cons.mp h0 with h | h
      · exact absurd h n0c
      · exact h
    apply hav
    refine ⟨0, Fin.succ 0, c0, n01, n0c, n1c, ?_⟩
    rw [hwdt]
    exact (hhead c0 t' rfl).append ((List.singleton_sublist.mpr h0t').cons_cons c0)
  have h10d : [Fin.succ 0, 0] <+ d := pair_sublist_left (hwdt ▸ h10) h0t
  have h1t : Fin.succ (0 : Fin (m + 1)) ∉ t := by
    intro h1
    rcases t with _ | ⟨c0, t'⟩
    · simp at h1
    have hc0 : ¬ c0.val < 2 := ht c0 t' rfl
    obtain ⟨n01, n0c, n1c⟩ := hne c0 hc0
    have h1t' : Fin.succ (0 : Fin (m + 1)) ∈ t' := by
      rcases List.mem_cons.mp h1 with h | h
      · exact absurd h n1c
      · exact h
    apply hav
    refine ⟨Fin.succ 0, 0, c0, n01.symm, n1c, n0c, ?_⟩
    rw [hwdt]
    exact h10d.append ((List.singleton_sublist.mpr h1t').cons_cons c0)
  have ht2 : ∀ c ∈ t, ∃ j : Fin m, j.succ.succ = c := by
    intro c hc
    rcases fin_trichotomy c with rfl | rfl | ⟨j, rfl⟩
    · exact absurd hc h0t
    · exact absurd hc h1t
    · exact ⟨j, rfl⟩
  obtain ⟨w'', hw''⟩ := exists_map_eq ht2
  -- the Dyck word read off from `d`
  set dd : List DyckStep := d.map toStep with hdd_def
  have hdd : dd.map dyckLetter = d := by
    rw [hdd_def, List.map_map]
    conv_rhs => rw [← List.map_id d]
    apply List.map_congr_left
    intro c hc
    rcases hd01 c hc with rfl | rfl
    · rfl
    · simp [toStep, dyckLetter]
  have hcount : ∀ s : DyckStep, dd.count s = (w.count (dyckLetter s)) := by
    intro s
    rw [hwdt, List.count_append, ← hdd, count_dyck_dyckLetter]
    have : (dyckLetter s : Fin (m + 2)) ∉ t := by
      cases s
      · exact h0t
      · exact h1t
    rw [List.count_eq_zero.mpr this, add_zero]
  have hcU : dd.count .U = k := (hcount _).trans (hreg _)
  have hcD : dd.count .D = k := (hcount _).trans (hreg _)
  have hpre : ∀ i : ℕ, (dd.take i).count .D ≤ (dd.take i).count .U := by
    intro i
    have hdi : (dd.take i).map dyckLetter = w.take (min i d.length) := by
      rw [List.map_take, hdd, ← List.take_take]
      congr 1
      rw [hwdt, List.take_left' rfl]
    rw [← count_dyck_dyckLetter (m := m), ← count_dyck_dyckLetter (m := m), hdi]
    exact (isLattice_iff_take.mp hlat) _ 0 (Fin.succ 0) (by simp)
  let p : DyckWord := ⟨dd, hcU.trans hcD.symm, hpre⟩
  have hpd : p.toList.map dyckLetter = d := hdd
  have hu : ∀ j : Fin m, j.succ.succ ∉ d := by
    intro j hj
    have := hd _ hj
    simp at this
  have hssinj : Function.Injective (fun j : Fin m => j.succ.succ) :=
    fun a b h => Fin.succ_injective _ (Fin.succ_injective _ h)
  have hwsplit : w = d ++ w''.map (fun j : Fin m => j.succ.succ) := by rw [hw'', hwdt]
  refine ⟨p, ⟨hcU, ?_⟩, w'', ⟨?_, ?_, ?_⟩, ?_⟩
  · intro hps
    have hdst : d = List.replicate k 0 ++ List.replicate k (Fin.succ 0) := by
      rw [← hpd, hps]
      simp [stair, dyckLetter, List.map_replicate]
    rw [hdst] at h10d
    refine not_pair_sublist_append (fun c hc => List.eq_of_mem_replicate hc)
      (Fin.succ_ne_zero _) ?_ h10d
    intro h
    exact Fin.succ_ne_zero _ (List.eq_of_mem_replicate h).symm
  · rw [hwsplit] at hreg
    exact regular_of_append_map hssinj hu hreg
  · rw [hwsplit] at hlat
    exact lattice_of_append_map hssinj hu (fun i j hij => by simp [hij]) hlat
  · intro hc
    apply hav
    rw [hwsplit]
    exact ((contains_map_iff hssinj).mpr hc).mono (List.sublist_append_right _ _)
  · rw [splice, hpd, List.map_map, hwsplit]
    rfl


/-- A `k`-regular word on `Fin m` has length `k * m`. -/
theorem length_of_regular {k m : ℕ} {w : List (Fin m)} (h : IsRegular k w) :
    w.length = k * m := by
  have hsum := Multiset.sum_count_eq_card (s := Finset.univ) (m := (w : Multiset (Fin m)))
    (fun a _ => Finset.mem_univ a)
  simp only [Multiset.coe_count, Multiset.coe_card] at hsum
  rw [← hsum, Finset.sum_congr rfl (fun i _ => h i)]
  simp [mul_comm]

/-- `𝓛_m^k(O(1231))` is finite. -/
theorem latticeWords1231_finite (k m : ℕ) : (latticeWords1231 k m).Finite :=
  (List.finite_length_eq (Fin m) (k * m)).subset fun _ hw => length_of_regular hw.1

/-- Dyck words of semilength `k` other than `U^k D^k`. -/
def dyckSet (k : ℕ) : Set DyckWord := {p | p.semilength = k ∧ p ≠ stair k}

/-- `U^k D^k` has semilength `k`. -/
theorem stair_semilength (k : ℕ) : (stair k).semilength = k := by
  simp [DyckWord.semilength, stair, List.count_replicate]

/-- There are `C_k - 1` Dyck words of semilength `k` other than `U^k D^k`. -/
theorem ncard_dyckSet (k : ℕ) : (dyckSet k).ncard = catalan k - 1 := by
  have hset : dyckSet k = {p : DyckWord | p.semilength = k} \ {stair k} := by
    ext p
    simp [dyckSet]
  have hall : {p : DyckWord | p.semilength = k}.ncard = catalan k := by
    rw [← Nat.card_coe_set_eq]
    show Nat.card {p : DyckWord // p.semilength = k} = _
    exact Nat.card_eq_fintype_card.trans (DyckWord.card_dyckWord_semilength_eq_catalan k)
  rw [hset, Set.ncard_sdiff_singleton_of_mem (by exact stair_semilength k), hall]

/-- The structural decomposition
`𝓛_{m+2}^k(O(1231)) = prepend(𝓛_{m+1}^k(O(1231))) ∪ splice((Dyck_k \ {U^k D^k}) × 𝓛_m^k(O(1231)))`. -/
theorem latticeWords1231_eq (k m : ℕ) :
    latticeWords1231 k (m + 2) = prepend k '' latticeWords1231 k (m + 1) ∪
      (fun q : DyckWord × List (Fin m) => splice q.1 q.2) ''
        (dyckSet k ×ˢ latticeWords1231 k m) := by
  ext w
  constructor
  · intro hw
    by_cases h10 : [Fin.succ 0, 0] <+ w
    · obtain ⟨p, hp, w'', hw'', hsp⟩ := surj_splice hw h10
      exact Or.inr ⟨(p, w''), ⟨hp, hw''⟩, hsp⟩
    · obtain ⟨w', hw', hpw⟩ := surj_prepend hw h10
      exact Or.inl ⟨w', hw', hpw⟩
  · rintro (⟨w', hw', rfl⟩ | ⟨⟨p, w''⟩, ⟨⟨hp, -⟩, hw''⟩, rfl⟩)
    · exact prepend_mem hw'
    · exact splice_mem hp hw''

/-- **Conjecture 1231 (Laudone, arXiv:2608.21351), recurrence form.**  For all `k, n ≥ 0`,
`a_{n+2} = a_{n+1} + (C_k - 1) a_n`, where `a_n = |𝓛_n^k(O(1231))|` and `C_k` is the `k`-th
Catalan number.  (`catalan k ≥ 1`, see `catalan_pos'`, so the natural-number subtraction
`catalan k - 1` is the true difference.) -/
theorem a_add_two (k n : ℕ) : a k (n + 2) = a k (n + 1) + (catalan k - 1) * a k n := by
  unfold a
  rw [latticeWords1231_eq]
  have hfin := latticeWords1231_finite k (n + 2)
  rw [latticeWords1231_eq] at hfin
  rw [Set.ncard_union_eq ?_ (hfin.subset Set.subset_union_left)
    (hfin.subset Set.subset_union_right)]
  · rw [Set.InjOn.ncard_image (prepend_injective k).injOn, Set.InjOn.ncard_image, Set.ncard_prod,
      ncard_dyckSet]
    rintro ⟨p, w⟩ ⟨⟨hp, -⟩, -⟩ ⟨p', w'⟩ ⟨⟨hp', -⟩, -⟩ h
    obtain ⟨rfl, rfl⟩ := splice_injOn hp hp' h
    rfl
  · rw [Set.disjoint_left]
    rintro _ ⟨w', -, rfl⟩ ⟨⟨p, w''⟩, ⟨⟨hp, hne⟩, -⟩, h⟩
    exact prepend_ne_splice hp hne w' w'' h.symm


/-- The only word on the empty alphabet is the empty word, which qualifies. -/
theorem latticeWords1231_zero (k : ℕ) : latticeWords1231 k 0 = {[]} := by
  ext w
  simp only [Set.mem_singleton_iff]
  constructor
  · intro _
    exact List.eq_nil_iff_forall_not_mem.mpr fun c => c.elim0
  · rintro rfl
    refine ⟨fun i => i.elim0, fun _ _ i => i.elim0, ?_⟩
    rintro ⟨x, -⟩
    exact x.elim0

/-- On a one-letter alphabet the only `k`-regular word is `0^k`, which qualifies. -/
theorem latticeWords1231_one (k : ℕ) : latticeWords1231 k 1 = {List.replicate k 0} := by
  ext w
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hreg, -, -⟩
    rw [List.eq_replicate_iff]
    refine ⟨?_, fun c _ => Subsingleton.elim c 0⟩
    rw [length_of_regular hreg, mul_one]
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [Subsingleton.elim i 0, List.count_replicate_self]
    · intro p _ i j hij
      have hi := i.isLt
      have hj := j.isLt
      omega
    · exact not_contains_of_two (u := 0) (v := 0)
        (fun c _ => Or.inl (Subsingleton.elim c 0))

/-- Catalan numbers are positive. -/
theorem catalan_pos' (k : ℕ) : 0 < catalan k := by
  rw [← DyckWord.card_dyckWord_semilength_eq_catalan]
  exact Fintype.card_pos_iff.mpr ⟨⟨stair k, stair_semilength k⟩⟩

/-- `a_0 = 1`. -/
theorem a_zero (k : ℕ) : a k 0 = 1 := by
  rw [a, latticeWords1231_zero, Set.ncard_singleton]

/-- `a_1 = 1`. -/
theorem a_one (k : ℕ) : a k 1 = 1 := by
  rw [a, latticeWords1231_one, Set.ncard_singleton]

/-- `a_2 = C_k` (stated in the paper as forced). -/
theorem a_two (k : ℕ) : a k 2 = catalan k := by
  have hc : 0 < catalan k := catalan_pos' k
  rw [a_add_two, a_one, a_zero]
  omega

/-- The paper's `n = 3` special case: `|𝓛_3^k(O(1231))| = 2 C_k - 1` for every `k`. -/
theorem a_three (k : ℕ) : a k 3 = 2 * catalan k - 1 := by
  have hc : 0 < catalan k := catalan_pos' k
  rw [a_add_two, a_two, a_one]
  omega

/-- **Conjecture 1231 (Laudone, arXiv:2608.21351), as stated.**  With
`a_n = |𝓛_n^k(O(1231))|`: `a_1 = 1`, `a_2 = C_k`, and `a_n = a_{n-1} + (C_k - 1) a_{n-2}` for
`n ≥ 3`.  Proved here for every `k` (the paper asks for `k ≥ 1`). -/
theorem conj_1231 (k : ℕ) :
    a k 1 = 1 ∧ a k 2 = catalan k ∧
      ∀ n : ℕ, 3 ≤ n → a k n = a k (n - 1) + (catalan k - 1) * a k (n - 2) := by
  refine ⟨a_one k, a_two k, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [a_add_two]
  rfl

/-- Ground truth: for `k = 2` the counts are Fibonacci numbers, `a_3 = 3`. -/
example : a 2 3 = 3 := by
  rw [a_three, catalan_two]

/-- Ground truth: for `k = 3` (`C_3 = 5`), `a_3 = 9`, matching the exhaustive count. -/
example : a 3 3 = 9 := by
  rw [a_three, catalan_three]

end CanonPermutationPattern1231
