/-
# UUDD-avoiding Dyck paths and bargraphs

*Simplicial Complexes of Antichains in Root Posets and Related Combinatorics
of Dyck Paths*, arXiv:2609.14054, Section 3, conjecture following
`thm:typeA-f` and the remark on OEIS A086581 / A082582. By Lemma `lem:max`,
Dyck paths whose valley sets are maximal faces of `Δ_{Dyck_n}` are precisely
the UUDD-avoiding paths. The conjecture identifies their counts by valleys
with OEIS A271942, counting bargraphs by semiperimeter and width.

For `n ≥ 2` and every `k`, the bijection below identifies UUDD-avoiding Dyck
paths of semilength `n` with `k` valleys and bargraphs of semiperimeter `n`
and width `k`; both sets are empty for `k = 0`. Valley heights `v₁,…,v_k` determine the peak
heights `max(v_{i-1},v_i)+1`, with `v₀ = v_{k+1} = 0`; the corresponding
bargraph has column heights `v_i+1`. Its perimeter is
`2k + h₁ + ∑ |h_{i+1}-h_i| + h_k`.
-/
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

namespace RootPosetAntichainComplexes

open DyckStep

/-! ## Definitions mirroring the source -/

/-- A word over `{U, D}` is *UUDD-avoiding* if it has no factorization
`w₁ UUDD w₂`, i.e. `[U, U, D, D]` is not a contiguous factor (infix) of it.
For Dyck words this is the paper's characterization (Lemma `lem:max`) of the
maximal faces of `Δ_{Dyck_n}`. -/
def UUDDFree (w : List DyckStep) : Prop := ¬ [U, U, D, D] <:+: w

/-- `UUDDFree` is decidable. -/
instance : DecidablePred UUDDFree := fun w => inferInstanceAs (Decidable (¬ [U, U, D, D] <:+: w))

/-- The number of valleys of a word `w = w₁ ⋯ w_r`: the number of indices
`1 ≤ i < r` with `w_i = D` and `w_{i+1} = U`, i.e. the number of adjacent
pairs `(D, U)`. -/
def valleyCount (w : List DyckStep) : ℕ := ((w.zip w.tail).filter (· = (D, U))).length

/-- The total vertical variation `Σ |l_{i+1} - l_i|` of a list of heights. -/
def verticalVariation : List ℕ → ℕ
  | a :: b :: t => ((b : ℤ) - a).natAbs + verticalVariation (b :: t)
  | _ => 0

/-- The perimeter of the bargraph with column heights `h = [h₁, …, h_k]`:
`2k` horizontal unit edges plus the vertical edges
`h₁ + Σ |h_{i+1} - h_i| + h_k`, i.e. the vertical variation of
`0, h₁, …, h_k, 0`.  The semiperimeter is half of this. -/
def bargraphPerimeter (h : List ℕ) : ℕ := 2 * h.length + verticalVariation (0 :: (h ++ [0]))

example : valleyCount [U, D, U, D] = 1 := by decide
example : valleyCount [U, U, D, U, D, D, U, D] = 2 := by decide
example : valleyCount [U, U, D, D] = 0 := by decide
example : UUDDFree [U, D, U, D] := by decide
example : UUDDFree [U, U, U, D, U, D, D, D] := by decide
example : ¬ UUDDFree [U, D, U, U, D, D] := by decide
-- the bargraph with columns `1, 2` has perimeter `8`, semiperimeter `4`
example : bargraphPerimeter [1, 2] = 2 * 4 := by decide
-- the bargraph with columns `2, 1, 3` has perimeter `2·3 + 2 + 1 + 2 + 3 = 14`
example : bargraphPerimeter [2, 1, 3] = 2 * 7 := by decide
example : bargraphPerimeter [1] = 2 * 2 := by decide

/-! ## A recursive description of Dyck paths -/

/-- `Reaches x w`: reading `w` from height `x`, the path never goes below `0`
and ends at height `0`. -/
def Reaches : ℕ → List DyckStep → Prop
  | x, [] => x = 0
  | x, U :: t => Reaches (x + 1) t
  | x, D :: t => 0 < x ∧ Reaches (x - 1) t

/-- `Reaches x w` in terms of prefix counts. -/
theorem reaches_iff (x : ℕ) (w : List DyckStep) :
    Reaches x w ↔ (∀ i, (w.take i).count D ≤ x + (w.take i).count U) ∧
      w.count D = x + w.count U := by
  induction w generalizing x with
  | nil =>
    simp only [Reaches, List.take_nil, List.count_nil, add_zero, zero_le, implies_true, true_and]
    omega
  | cons c t ih =>
    cases c with
    | U =>
      simp only [Reaches, ih, List.count_cons_self, ne_eq, reduceCtorEq, not_false_eq_true,
        List.count_cons_of_ne]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i => ?_, by omega⟩
        cases i with
        | zero => simp
        | succ i =>
          have hi := h1 i
          simp only [List.take_succ_cons, ne_eq, reduceCtorEq, not_false_eq_true,
            List.count_cons_of_ne, List.count_cons_self]
          omega
      · rintro ⟨h1, h2⟩
        refine ⟨fun i => ?_, by omega⟩
        have hi := h1 (i + 1)
        simp only [List.take_succ_cons, ne_eq, reduceCtorEq, not_false_eq_true,
          List.count_cons_of_ne, List.count_cons_self] at hi
        omega
    | D =>
      simp only [Reaches, ih, List.count_cons_self, ne_eq, reduceCtorEq, not_false_eq_true,
        List.count_cons_of_ne]
      constructor
      · rintro ⟨hx, h1, h2⟩
        refine ⟨fun i => ?_, by omega⟩
        cases i with
        | zero => simp
        | succ i =>
          have hi := h1 i
          simp only [List.take_succ_cons, ne_eq, reduceCtorEq, not_false_eq_true,
            List.count_cons_of_ne, List.count_cons_self]
          omega
      · rintro ⟨h1, h2⟩
        have h0 := h1 1
        simp only [List.take_succ_cons, List.take_zero, List.count_cons_self, List.count_nil,
          ne_eq, reduceCtorEq, not_false_eq_true, List.count_cons_of_ne] at h0
        refine ⟨by omega, fun i => ?_, by omega⟩
        have hi := h1 (i + 1)
        simp only [List.take_succ_cons, ne_eq, reduceCtorEq, not_false_eq_true,
          List.count_cons_of_ne, List.count_cons_self] at hi
        omega

/-- `Reaches 0 w` is exactly the pair of conditions defining a `DyckWord`. -/
theorem reaches_zero_iff (w : List DyckStep) :
    Reaches 0 w ↔ (w.count U = w.count D ∧ ∀ i, (w.take i).count D ≤ (w.take i).count U) := by
  rw [reaches_iff]
  simp only [zero_add]
  tauto

open List in
/-- Reading a run `U^a`. -/
theorem reaches_replicate_U_append (x a : ℕ) (l : List DyckStep) :
    Reaches x (replicate a U ++ l) ↔ Reaches (x + a) l := by
  induction a generalizing x with
  | zero => simp
  | succ a ih =>
    simp only [replicate_succ, cons_append, Reaches, ih]
    rw [show x + 1 + a = x + (a + 1) by omega]

open List in
/-- Reading a run `D^b`. -/
theorem reaches_replicate_D_append (x b : ℕ) (l : List DyckStep) :
    Reaches x (replicate b D ++ l) ↔ b ≤ x ∧ Reaches (x - b) l := by
  induction b generalizing x with
  | zero => simp
  | succ b ih =>
    simp only [replicate_succ, cons_append, Reaches, ih]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, by rwa [show x - (b + 1) = x - 1 - b by omega]⟩
    · rintro ⟨h1, h3⟩
      exact ⟨by omega, by omega, by rwa [show x - 1 - b = x - (b + 1) by omega]⟩

/-! ## The bijection: valley heights determine a UUDD-avoiding path -/

/-- The unique UUDD-free peak block from a valley (or start) at height `x` to a
valley (or end) at height `y`: `U^{y-x+1} D^{x-y+1}` (truncated subtraction, so
one of the two runs has length `1`). -/
def block (x y : ℕ) : List DyckStep :=
  List.replicate (y - x + 1) U ++ List.replicate (x - y + 1) D

/-- The path through the successive valley heights `x₀, x₁, …, x_m`: the
concatenation of the blocks `block x_i x_{i+1}`. -/
def pathOf : List ℕ → List DyckStep
  | x :: y :: t => block x y ++ pathOf (y :: t)
  | _ => []

/-- The heights of the valleys of `w`, read from starting height `x`. -/
def valleyHeights : ℕ → List DyckStep → List ℕ
  | _, [] => []
  | x, U :: t => valleyHeights (x + 1) t
  | x, D :: t => if t.head? = some U then (x - 1) :: valleyHeights (x - 1) t
      else valleyHeights (x - 1) t

/-- The total ascent `Σ (l_{i+1} - l_i)₊` of a list of heights. -/
def ascent : List ℕ → ℕ
  | a :: b :: t => (b - a) + ascent (b :: t)
  | _ => 0

/-- The total descent `Σ (l_i - l_{i+1})₊` of a list of heights. -/
def descent : List ℕ → ℕ
  | a :: b :: t => (a - b) + descent (b :: t)
  | _ => 0

example : pathOf [0, 1, 0] = [U, U, D, U, D, D] := by decide
example : pathOf [0, 0, 2, 0] = [U, D, U, U, U, D, U, D, D, D] := by decide
example : valleyHeights 0 [U, U, D, U, D, D] = [1] := by decide
example : valleyHeights 0 [U, D, U, U, U, D, U, D, D, D] = [0, 2] := by decide
example : ascent [0, 3, 1, 2, 0] = 4 := by decide
example : descent [0, 3, 1, 2, 0] = 4 := by decide

open List in
/-- Valley heights across a run `U^a`. -/
theorem valleyHeights_replicate_U_append (x a : ℕ) (l : List DyckStep) :
    valleyHeights x (replicate a U ++ l) = valleyHeights (x + a) l := by
  induction a generalizing x with
  | zero => simp
  | succ a ih =>
    simp only [replicate_succ, cons_append, valleyHeights, ih]
    rw [show x + 1 + a = x + (a + 1) by omega]

open List in
/-- Valley heights across a run `D^b` followed by `U`: one valley at `x - b`. -/
theorem valleyHeights_replicate_D_append_U (x b : ℕ) (hb : 1 ≤ b) (t : List DyckStep) :
    valleyHeights x (replicate b D ++ U :: t) = (x - b) :: valleyHeights (x - b) (U :: t) := by
  induction b generalizing x with
  | zero => omega
  | succ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb'
    · simp [valleyHeights]
    · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      rw [replicate_succ, cons_append, valleyHeights.eq_3, ih (x - 1) hb']
      simp only [replicate_succ, cons_append, head?_cons, Option.some.injEq, reduceCtorEq,
        if_false]
      rw [show x - 1 - (c + 1) = x - (c + 1 + 1) by omega]

open List in
/-- A final run `D^b` contains no valley. -/
theorem valleyHeights_replicate_D (x b : ℕ) :
    valleyHeights x (replicate b D) = [] := by
  induction b generalizing x with
  | zero => simp [valleyHeights]
  | succ b ih =>
    rw [replicate_succ, valleyHeights, ih]
    cases b <;> simp [replicate_succ]

/-- Unfolding `UUDDFree` one letter at a time. -/
theorem uuddFree_cons_iff (c : DyckStep) (t : List DyckStep) :
    UUDDFree (c :: t) ↔ ¬ [U, U, D, D] <+: c :: t ∧ UUDDFree t := by
  simp only [UUDDFree, List.infix_cons_iff, not_or]

/-- The empty word is UUDD-free. -/
theorem uuddFree_nil : UUDDFree [] := by
  simp [UUDDFree]

/-- A leading `D` does not affect UUDD-freeness. -/
theorem uuddFree_D_cons_iff (t : List DyckStep) : UUDDFree (D :: t) ↔ UUDDFree t := by
  rw [uuddFree_cons_iff]
  simp

/-- A leading `UD` does not affect UUDD-freeness. -/
theorem uuddFree_U_D_cons_iff (t : List DyckStep) :
    UUDDFree (U :: D :: t) ↔ UUDDFree (D :: t) := by
  rw [uuddFree_cons_iff]
  simp

open List in
/-- A leading run `D^b` does not affect UUDD-freeness. -/
theorem uuddFree_replicate_D_append_iff (b : ℕ) (l : List DyckStep) :
    UUDDFree (replicate b D ++ l) ↔ UUDDFree l := by
  induction b with
  | zero => simp
  | succ b ih => rw [replicate_succ, cons_append, uuddFree_D_cons_iff, ih]

open List in
/-- A peak block `U^a D` followed by a UUDD-free word not starting with `D` is
UUDD-free. -/
theorem uuddFree_replicate_U_append_D (a : ℕ) (l : List DyckStep) (hl : l.head? ≠ some D)
    (hfree : UUDDFree l) : UUDDFree (replicate a U ++ D :: l) := by
  have h2 : UUDDFree (U :: D :: l) := by
    rw [uuddFree_U_D_cons_iff, uuddFree_D_cons_iff]
    exact hfree
  induction a with
  | zero => simpa [uuddFree_D_cons_iff] using hfree
  | succ a ih =>
    rcases a with _ | a
    · simpa using h2
    · rw [replicate_succ, cons_append, uuddFree_cons_iff]
      refine ⟨?_, ih⟩
      rcases a with _ | a
      · cases l with
        | nil => simp
        | cons c l => cases c <;> simp_all
      · simp [replicate_succ]

open List in
/-- A peak block `U^a D^b` with `a, b ≥ 2` contains `UUDD`. -/
theorem not_uuddFree_of_two_le (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (l : List DyckStep) :
    ¬ UUDDFree (replicate a U ++ replicate b D ++ l) := by
  intro h
  apply h
  refine ⟨replicate (a - 2) U, replicate (b - 2) D ++ l, ?_⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  rw [replicate_add a' 2]
  simp [replicate_succ]

/-- Suffixes of UUDD-free words are UUDD-free. -/
theorem UUDDFree.of_append_right {l₁ l₂ : List DyckStep} (h : UUDDFree (l₁ ++ l₂)) :
    UUDDFree l₂ := fun h' => h (h'.trans (List.suffix_append l₁ l₂).isInfix)

/-- A path through at least two heights starts with `U`. -/
theorem exists_pathOf_eq_U_cons (x y : ℕ) (t : List ℕ) :
    ∃ s, pathOf (x :: y :: t) = U :: s :=
  ⟨List.replicate (y - x) U ++ List.replicate (x - y + 1) D ++ pathOf (y :: t), by
    simp [pathOf, block, List.replicate_succ]⟩

/-- A path from `x` through `v` back to `0` starts with `U`. -/
theorem exists_pathOf_append_zero_eq_U_cons (x : ℕ) (v : List ℕ) :
    ∃ s, pathOf (x :: (v ++ [0])) = U :: s := by
  cases v with
  | nil => exact exists_pathOf_eq_U_cons x 0 []
  | cons y v => exact exists_pathOf_eq_U_cons x y _

/-- A block from `x` to `y` moves the height from `x` to `y` and stays `≥ 0`. -/
theorem reaches_block_append (x y : ℕ) (l : List DyckStep) :
    Reaches x (block x y ++ l) ↔ Reaches y l := by
  rw [block, List.append_assoc, reaches_replicate_U_append, reaches_replicate_D_append]
  rw [show x + (y - x + 1) - (x - y + 1) = y by omega]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

/-- The path from `x` through the valley heights `v` back to `0` is a valid
path from height `x`. -/
theorem reaches_pathOf (v : List ℕ) (x : ℕ) : Reaches x (pathOf (x :: (v ++ [0]))) := by
  induction v generalizing x with
  | nil =>
    have h := (reaches_block_append x 0 []).2 rfl
    simpa [pathOf] using h
  | cons y v ih =>
    simp only [List.cons_append, pathOf]
    exact (reaches_block_append x y _).2 (ih y)

/-- A block followed by a UUDD-free word not starting with `D` is UUDD-free. -/
theorem uuddFree_block_append (x y : ℕ) (l : List DyckStep) (hl : l.head? ≠ some D)
    (hfree : UUDDFree l) : UUDDFree (block x y ++ l) := by
  rcases le_or_gt x y with hxy | hxy
  · rw [block, show x - y + 1 = 1 by omega, List.append_assoc]
    exact uuddFree_replicate_U_append_D _ l hl hfree
  · rw [block, show y - x + 1 = 1 by omega, List.append_assoc, List.replicate_succ,
      show x - y + 1 = (x - y) + 1 by omega, List.replicate_succ]
    simp only [List.replicate_zero, List.nil_append, List.cons_append]
    rw [uuddFree_U_D_cons_iff, uuddFree_D_cons_iff, uuddFree_replicate_D_append_iff]
    exact hfree

/-- Every path built from valley heights is UUDD-free. -/
theorem uuddFree_pathOf (v : List ℕ) (x : ℕ) : UUDDFree (pathOf (x :: (v ++ [0]))) := by
  induction v generalizing x with
  | nil => simpa [pathOf] using uuddFree_block_append x 0 [] (by simp) uuddFree_nil
  | cons y v ih =>
    simp only [List.cons_append, pathOf]
    obtain ⟨s, hs⟩ := exists_pathOf_append_zero_eq_U_cons y v
    refine uuddFree_block_append x y _ ?_ (ih y)
    rw [hs]
    simp

/-- A single block has no valley. -/
theorem valleyHeights_block (x y : ℕ) : valleyHeights x (block x y) = [] := by
  rw [block, valleyHeights_replicate_U_append, valleyHeights_replicate_D]

/-- A block followed by `U` produces one valley, at height `y`. -/
theorem valleyHeights_block_append_U (x y : ℕ) (t : List DyckStep) :
    valleyHeights x (block x y ++ U :: t) = y :: valleyHeights y (U :: t) := by
  rw [block, List.append_assoc, valleyHeights_replicate_U_append,
    valleyHeights_replicate_D_append_U _ _ (by omega)]
  rw [show x + (y - x + 1) - (x - y + 1) = y by omega]

/-- The valley heights of the path built from `v` are `v` (right inverse). -/
theorem valleyHeights_pathOf (v : List ℕ) (x : ℕ) :
    valleyHeights x (pathOf (x :: (v ++ [0]))) = v := by
  induction v generalizing x with
  | nil => simpa [pathOf] using valleyHeights_block x 0
  | cons y v ih =>
    simp only [List.cons_append, pathOf]
    obtain ⟨s, hs⟩ := exists_pathOf_append_zero_eq_U_cons y v
    rw [hs, valleyHeights_block_append_U, ← hs, ih]

/-- The number of up-steps of the path built from `v`. -/
theorem count_U_pathOf (v : List ℕ) (x : ℕ) :
    (pathOf (x :: (v ++ [0]))).count U = v.length + 1 + ascent (x :: (v ++ [0])) := by
  induction v generalizing x with
  | nil => simp [pathOf, block, ascent, List.count_replicate]
  | cons y v ih =>
    simp only [List.cons_append, pathOf, ascent, List.count_append, block, List.count_replicate]
    rw [ih y]
    simp only [BEq.rfl, ↓reduceIte, beq_iff_eq, reduceCtorEq, add_zero, List.length_cons]
    omega

/-- Unfolding `valleyCount` on the first two letters. -/
theorem valleyCount_cons_cons (c d : DyckStep) (t : List DyckStep) :
    valleyCount (c :: d :: t) = (if (c, d) = (D, U) then 1 else 0) + valleyCount (d :: t) := by
  simp only [valleyCount, List.tail_cons, List.zip_cons_cons, List.filter_cons]
  split_ifs <;> simp_all [add_comm]

/-- The valley count is the length of the list of valley heights. -/
theorem valleyCount_eq_length_valleyHeights (w : List DyckStep) (x : ℕ) :
    valleyCount w = (valleyHeights x w).length := by
  induction w generalizing x with
  | nil => rfl
  | cons c t ih =>
    cases t with
    | nil => cases c <;> rfl
    | cons d t =>
      rw [valleyCount_cons_cons]
      cases c with
      | U =>
        rw [ih (x + 1)]
        simp [valleyHeights]
      | D =>
        rw [ih (x - 1)]
        cases d <;> simp [valleyHeights, add_comm]

/-- Every list splits as a maximal leading run of a letter `s` and a remainder. -/
theorem exists_replicate_append (s : DyckStep) (l : List DyckStep) :
    ∃ a l', l = List.replicate a s ++ l' ∧ l'.head? ≠ some s := by
  induction l with
  | nil => exact ⟨0, [], rfl, by simp⟩
  | cons c t ih =>
    by_cases hc : c = s
    · obtain ⟨a, l', h1, h2⟩ := ih
      exact ⟨a + 1, l', by rw [h1, hc, List.replicate_succ, List.cons_append], h2⟩
    · exact ⟨0, c :: t, rfl, by simpa using hc⟩

/-- **Load-bearing step (left inverse).** A UUDD-free path `w` from height `x`
to `0`, starting with `U`, is rebuilt from its valley heights: each peak block
`U^a D^b` has `a = 1` or `b = 1`, hence equals `block x y` for the surrounding
valley heights `x, y`. Stated with a length bound `n` for strong induction. -/
theorem pathOf_valleyHeights (n : ℕ) : ∀ (w : List DyckStep) (x : ℕ), w.length ≤ n →
    Reaches x w → UUDDFree w → w.head? = some U →
    pathOf (x :: (valleyHeights x w ++ [0])) = w := by
  induction n with
  | zero =>
    intro w x hlen _ _ hU
    cases w with
    | nil => simp at hU
    | cons c t => simp at hlen
  | succ n ih =>
    intro w x hlen hw hfree hU
    obtain ⟨a, l₁, rfl, ha₁⟩ := exists_replicate_append U w
    obtain ⟨b, rest, rfl, hrest⟩ := exists_replicate_append D l₁
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp only [List.replicate_zero, List.nil_append] at hU
        exact absurd hU ha₁
      · exact h
    have hb : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with rfl | h
      · exfalso
        simp only [List.replicate_zero, List.nil_append] at ha₁ hw
        cases rest with
        | nil =>
          have hw' := (reaches_replicate_U_append x a []).1 (by simpa using hw)
          simp only [Reaches] at hw'
          omega
        | cons c t => cases c <;> simp at ha₁ hrest
      · exact h
    have hab : a = 1 ∨ b = 1 := by
      by_contra hcon
      exact not_uuddFree_of_two_le a b (by omega) (by omega) rest (by rwa [List.append_assoc])
    rw [reaches_replicate_U_append, reaches_replicate_D_append] at hw
    obtain ⟨hbx, hrest_reach⟩ := hw
    cases rest with
    | nil =>
      have hy : x + a - b = 0 := hrest_reach
      rw [List.append_nil, valleyHeights_replicate_U_append, valleyHeights_replicate_D]
      simp only [List.nil_append, pathOf, List.append_nil, block]
      congr 2 <;> omega
    | cons c t =>
      cases c with
      | D => simp at hrest
      | U =>
        rw [valleyHeights_replicate_U_append, valleyHeights_replicate_D_append_U _ _ hb]
        simp only [List.cons_append, pathOf]
        have hfree' : UUDDFree (U :: t) :=
          UUDDFree.of_append_right (l₁ := List.replicate a U ++ List.replicate b D)
            (by rwa [List.append_assoc])
        have hlen' : (U :: t).length ≤ n := by
          simp only [List.length_append, List.length_replicate, List.length_cons] at hlen ⊢
          omega
        rw [ih (U :: t) (x + a - b) hlen' hrest_reach hfree' rfl]
        rw [block, List.append_assoc, show x + a - b - x + 1 = a by omega,
          show x - (x + a - b) + 1 = b by omega]

/-! ## Bargraph perimeter in terms of ascents -/

/-- Vertical variation splits into total ascent plus total descent. -/
theorem verticalVariation_eq (l : List ℕ) : verticalVariation l = ascent l + descent l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t =>
      simp only [verticalVariation, ascent, descent] at ih ⊢
      rw [ih]
      omega

/-- Telescoping: from `x` down to a final `0`, ascent plus `x` equals descent. -/
theorem ascent_add_eq_descent (v : List ℕ) (x : ℕ) :
    ascent (x :: (v ++ [0])) + x = descent (x :: (v ++ [0])) := by
  induction v generalizing x with
  | nil => simp [ascent, descent]
  | cons y v ih =>
    have hy := ih y
    simp only [List.cons_append, ascent, descent] at hy ⊢
    omega

/-- Shifting all interior heights (and the start) up by one keeps the ascent. -/
theorem ascent_map_succ (v : List ℕ) (x : ℕ) :
    ascent ((x + 1) :: (v.map (· + 1) ++ [0])) = ascent (x :: (v ++ [0])) := by
  induction v generalizing x with
  | nil => simp [ascent]
  | cons y v ih =>
    simp only [List.map_cons, List.cons_append, ascent] at ih ⊢
    rw [ih y]
    omega

/-- The perimeter of the bargraph `v + 1` is twice the semilength
`k + 1 + ascent (0, v, 0)` of the path built from `v` (for `v` nonempty). -/
theorem bargraphPerimeter_map_succ (v : List ℕ) (hv : v ≠ []) :
    bargraphPerimeter (v.map (· + 1)) = 2 * (v.length + 1 + ascent (0 :: (v ++ [0]))) := by
  obtain ⟨y, v, rfl⟩ := List.exists_cons_of_ne_nil hv
  have h1 := ascent_add_eq_descent ((y :: v).map (· + 1)) 0
  have h2 := ascent_map_succ v y
  simp only [bargraphPerimeter, verticalVariation_eq, List.length_map]
  simp only [List.map_cons, List.cons_append, ascent, descent, add_zero] at h1 h2 ⊢
  omega

/-! ## The three families and the bijections -/

/-- `Dyck^max_n` with `k` valleys: UUDD-avoiding Dyck paths of semilength `n`
with exactly `k` valleys (counted by `f_{kk}` in the paper). -/
def UUDDFreeDyck (n k : ℕ) : Type :=
  {p : DyckWord // p.semilength = n ∧ UUDDFree p.toList ∧ valleyCount p.toList = k}

/-- Bargraphs of semiperimeter `n` and width `k` (counted by A271942 `T(n,k)`). -/
def Bargraph (n k : ℕ) : Type :=
  {h : List ℕ // (∀ x ∈ h, 1 ≤ x) ∧ h.length = k ∧ bargraphPerimeter h = 2 * n}

/-- Free valley-height sequences of length `k` whose path has semilength `n`. -/
def HeightSet (n k : ℕ) : Type :=
  {v : List ℕ // v.length = k ∧ v.length + 1 + ascent (0 :: (v ++ [0])) = n}

/-- The Dyck word `pathOf (0, v, 0)` built from valley heights `v`. -/
def toDyckWord (v : List ℕ) : DyckWord where
  toList := pathOf (0 :: (v ++ [0]))
  count_U_eq_count_D := ((reaches_zero_iff _).1 (reaches_pathOf v 0)).1
  count_D_le_count_U := ((reaches_zero_iff _).1 (reaches_pathOf v 0)).2

-- satisfiability witnesses: `UDUD ∈ Dyck^max_2` with one valley, bargraph `[1]`
example : (toDyckWord [0]).toList = [U, D, U, D] := by decide
example : (toDyckWord [0]).semilength = 2 ∧ UUDDFree (toDyckWord [0]).toList ∧
    valleyCount (toDyckWord [0]).toList = 1 := by decide
example : (∀ x ∈ [1], 1 ≤ x) ∧ [1].length = 1 ∧ bargraphPerimeter [1] = 2 * 2 := by decide

/-- A Dyck word with a valley starts with `U`. -/
theorem head?_eq_some_U_of_valleyCount_pos (p : DyckWord) (hp : 1 ≤ valleyCount p.toList) :
    p.toList.head? = some U := by
  have hne : p.toList ≠ [] := by
    intro h
    rw [h] at hp
    simp [valleyCount] at hp
  rw [List.head?_eq_some_head hne, DyckWord.head_eq_U]

/-- A UUDD-free Dyck word with a valley is the path built from its valley
heights. -/
theorem toList_eq_pathOf (p : DyckWord) (hp : 1 ≤ valleyCount p.toList)
    (hfree : UUDDFree p.toList) :
    pathOf (0 :: (valleyHeights 0 p.toList ++ [0])) = p.toList :=
  pathOf_valleyHeights _ p.toList 0 le_rfl
    ((reaches_zero_iff _).2 ⟨p.count_U_eq_count_D, p.count_D_le_count_U⟩) hfree
    (head?_eq_some_U_of_valleyCount_pos p hp)

/-- For `k ≥ 1`, UUDD-avoiding Dyck paths of semilength `n` with `k` valleys
correspond to their valley-height sequences. -/
def dyckEquivHeights (n k : ℕ) (hk : 1 ≤ k) : UUDDFreeDyck n k ≃ HeightSet n k where
  toFun p := ⟨valleyHeights 0 p.1.toList, by
    obtain ⟨p, hn, hfree, hval⟩ := p
    have hl : (valleyHeights 0 p.toList).length = k := by
      rw [← valleyCount_eq_length_valleyHeights, hval]
    refine ⟨hl, ?_⟩
    rw [← count_U_pathOf, toList_eq_pathOf p (by omega) hfree]
    exact hn⟩
  invFun v := ⟨toDyckWord v.1, by
    obtain ⟨v, hl, hn⟩ := v
    refine ⟨?_, uuddFree_pathOf v 0, ?_⟩
    · rw [DyckWord.semilength]
      exact (count_U_pathOf v 0).trans hn
    · rw [toDyckWord, valleyCount_eq_length_valleyHeights _ 0, valleyHeights_pathOf, hl]⟩
  left_inv p := by
    obtain ⟨p, hn, hfree, hval⟩ := p
    apply Subtype.ext
    apply DyckWord.ext
    exact toList_eq_pathOf p (by omega) hfree
  right_inv v := by
    obtain ⟨v, hl, hn⟩ := v
    apply Subtype.ext
    exact valleyHeights_pathOf v 0

/-- `(v + 1) - 1 = v` entrywise. -/
theorem map_pred_map_succ (v : List ℕ) : (v.map (· + 1)).map (· - 1) = v := by
  simp [List.map_map, Function.comp_def]

/-- `(h - 1) + 1 = h` entrywise when all entries are positive. -/
theorem map_succ_map_pred (h : List ℕ) (hh : ∀ x ∈ h, 1 ≤ x) :
    (h.map (· - 1)).map (· + 1) = h := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id h]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply, id_eq]
  have hx1 := hh x hx
  omega

/-- For `k ≥ 1`, valley-height sequences `v` correspond to bargraphs `v + 1`. -/
def heightsEquivBargraph (n k : ℕ) (hk : 1 ≤ k) : HeightSet n k ≃ Bargraph n k where
  toFun v := ⟨v.1.map (· + 1), by
    obtain ⟨v, hl, hn⟩ := v
    have hv : v ≠ [] := by
      rintro rfl
      simp only [List.length_nil] at hl
      omega
    refine ⟨by simp, by simpa using hl, ?_⟩
    rw [bargraphPerimeter_map_succ v hv, hn]⟩
  invFun h := ⟨h.1.map (· - 1), by
    obtain ⟨h, hpos, hl, hn⟩ := h
    dsimp only
    have hv : h.map (· - 1) ≠ [] := by
      intro he
      rw [List.map_eq_nil_iff] at he
      subst he
      simp only [List.length_nil] at hl
      omega
    refine ⟨by simpa using hl, ?_⟩
    have hper := bargraphPerimeter_map_succ _ hv
    rw [map_succ_map_pred h hpos, hn] at hper
    omega⟩
  left_inv v := Subtype.ext (map_pred_map_succ v.1)
  right_inv h := Subtype.ext (map_succ_map_pred h.1 h.2.1)

/-- **Explicit bijection.** For `k ≥ 1`, UUDD-avoiding Dyck paths of semilength
`n` with `k` valleys are in bijection with bargraphs of semiperimeter `n` and
width `k`, via `w ↦ (valley heights of w) + 1`. -/
def uuddFreeDyckEquivBargraph (n k : ℕ) (hk : 1 ≤ k) : UUDDFreeDyck n k ≃ Bargraph n k :=
  (dyckEquivHeights n k hk).trans (heightsEquivBargraph n k hk)

/-- For `n ≥ 2` there is no UUDD-avoiding Dyck path of semilength `n` without
valleys. -/
theorem isEmpty_uuddFreeDyck_zero (n : ℕ) (hn : 2 ≤ n) : IsEmpty (UUDDFreeDyck n 0) := by
  constructor
  rintro ⟨p, hsl, hfree, hval⟩
  by_cases hne : p.toList = []
  · rw [DyckWord.semilength, hne] at hsl
    simp only [List.count_nil] at hsl
    omega
  · have hU : p.toList.head? = some U := by
      rw [List.head?_eq_some_head hne, DyckWord.head_eq_U]
    have hvh : valleyHeights 0 p.toList = [] := by
      rw [← List.length_eq_zero_iff, ← valleyCount_eq_length_valleyHeights, hval]
    have hp := pathOf_valleyHeights _ p.toList 0 le_rfl
      ((reaches_zero_iff _).2 ⟨p.count_U_eq_count_D, p.count_D_le_count_U⟩) hfree hU
    rw [hvh] at hp
    have hUD : p.toList = [U, D] := by rw [← hp]; decide
    rw [DyckWord.semilength, hUD] at hsl
    have h1 : [U, D].count U = 1 := by decide
    omega

/-- There is no bargraph of width `0` and semiperimeter `n ≥ 2`. -/
theorem isEmpty_bargraph_zero (n : ℕ) (hn : 2 ≤ n) : IsEmpty (Bargraph n 0) := by
  constructor
  rintro ⟨h, hpos, hl, hper⟩
  rw [List.length_eq_zero_iff] at hl
  subst hl
  have h0 : bargraphPerimeter [] = 0 := by decide
  omega

/-- **Conjecture of arXiv:2609.14054, Section 3.** For `n ≥ 2`
and every `k`, the number `f_{kk}` of Dyck paths of semilength `n` whose valley
set is a maximal face of `Δ_{Dyck_n}` — equivalently (paper, Lemma `lem:max`)
the UUDD-avoiding Dyck paths — having exactly `k` valleys equals the number
A271942`(n, k)` of bargraphs of semiperimeter `n` (perimeter `2n`) and width
`k`, a bargraph being a list of `k` column heights `≥ 1`. -/
theorem card_uuddFreeDyck_eq_card_bargraph (n k : ℕ) (hn : 2 ≤ n) :
    Nat.card {p : DyckWord // p.semilength = n ∧ UUDDFree p.toList ∧ valleyCount p.toList = k} =
      Nat.card {h : List ℕ // (∀ x ∈ h, 1 ≤ x) ∧ h.length = k ∧ bargraphPerimeter h = 2 * n} := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 := isEmpty_uuddFreeDyck_zero n hn
    have h2 := isEmpty_bargraph_zero n hn
    unfold UUDDFreeDyck at h1
    unfold Bargraph at h2
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]
  · exact Nat.card_congr (uuddFreeDyckEquivBargraph n k hk)

end RootPosetAntichainComplexes
