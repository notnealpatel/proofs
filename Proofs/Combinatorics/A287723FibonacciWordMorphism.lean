/-
# A287723 — Kimberling: positions of 0 in the {0->1, 1->010}-transform of the Fibonacci word

OEIS A287723 (Clark Kimberling, June 2, 2017) conjectures
`-1 < nr - a(n) < 1` for `n ≥ 1`, where `r = (7+√5)/4`.
Here `a(n)` lists the 1-based zero positions in A287722, the
`0 ↦ 1`, `1 ↦ 010` transform of the Fibonacci word A003849
(the limit of `0 ↦ 01`, `1 ↦ 0` starting at 0).

The `1 ↦ 011` rule in the program copied into A287723 differs from
A287722's `1 ↦ 010` rule; this file uses the latter, matching the listed terms.

The proof proceeds as follows:

1. `fibWord` is the limit of `fibIter k` (iterates of `0 ↦ 01, 1 ↦ 0` on `[0]`).
2. Self-similarity `σ(F) = F` gives, for `L(m) = |σ(F[0,m))|`,
   `L(m) + ones m = 2m`, `ones (L m) + ones m = m`, `F(L m) = 0`.
3. A strong-induction bridge `onesBound_all`:
   `ones n < (n+1)·alpha < ones n + 1` with `alpha = (3 - √5)/2 = 2 - φ`,
   i.e. `ones n = ⌊(n+1)(2-φ)⌋` (`ones_eq_floor`), whence Cloitre's
   A003849 formula (`fibWord_eq_floor_sub`).
4. The `j`-th `1` of `F` (0-indexed position `p`) produces the block `010` of
   A287722 at 0-indexed positions `p + 2(j-1), …, p + 2(j-1) + 2`; the
   bound `(p+1)·alpha < j < (p+2)·alpha` then gives the conjecture.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A287723FibonacciWordMorphism

/-! ## Definitions mirroring the entries -/

/-- The Fibonacci morphism `0 ↦ 01, 1 ↦ 0` of A003849 (letters other than `0`
are sent to `[0]`; only the letters `0, 1` ever occur). -/
def fibMorph (b : ℕ) : List ℕ := if b = 0 then [0, 1] else [0]

/-- The `k`-th iterate of `fibMorph` applied to the word `[0]`
(Mathematica `Nest[Flatten[# /. {0 -> {0, 1}, 1 -> {0}}] &, {0}, k]`). -/
def fibIter : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (fibIter k).flatMap fibMorph

/-- The infinite Fibonacci word A003849 (offset 0): letter `n` read off the
iterate `fibIter n`, which has length `≥ n + 1` (`length_fibIter`) and is a
prefix of every later iterate (`fibIter_prefix_of_le`). -/
def fibWord (n : ℕ) : ℕ := (fibIter n).getD n 0

/-- The transform morphism `0 ↦ 1, 1 ↦ 010` of A287722. -/
def transMorph (b : ℕ) : List ℕ := if b = 0 then [1] else [0, 1, 0]

/-- The word A287722 indexed from `0`: `transWord i = A287722(i + 1)`, read off
the image of `fibIter i` (of length `≥ i + 1`) under `transMorph`. -/
def transWord (i : ℕ) : ℕ := ((fibIter i).flatMap transMorph).getD i 0

/-- A287723 (offset 1): the 1-indexed position of the `n`-th `0` of A287722.
The value at `n = 0` is junk; every statement below assumes `1 ≤ n`. -/
noncomputable def a287723 (n : ℕ) : ℕ := Nat.nth (fun i => transWord i = 0) (n - 1) + 1

/-! ## Examples -/

example : (List.range 14).map fibWord = [0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0] := by decide

example : (List.range 30).map transWord =
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0] := by
  decide

/-- If position `t` of A287722 (0-indexed) is a `0`, then it is the
`(count + 1)`-th zero, so `a287723 (count + 1) = t + 1`. -/
lemma a287723_count_succ {t : ℕ} (ht : transWord t = 0) :
    a287723 (Nat.count (fun i => transWord i = 0) t + 1) = t + 1 := by
  unfold a287723
  rw [Nat.add_sub_cancel, Nat.nth_count (p := fun i => transWord i = 0) ht]

example : a287723 1 = 2 := by
  have h := a287723_count_succ (t := 1) (by decide)
  rwa [show Nat.count (fun i => transWord i = 0) 1 = 0 by decide] at h

example : a287723 2 = 4 := by
  have h := a287723_count_succ (t := 3) (by decide)
  rwa [show Nat.count (fun i => transWord i = 0) 3 = 1 by decide] at h

example : a287723 3 = 7 := by
  have h := a287723_count_succ (t := 6) (by decide)
  rwa [show Nat.count (fun i => transWord i = 0) 6 = 2 by decide] at h

example : a287723 7 = 16 := by
  have h := a287723_count_succ (t := 15) (by decide)
  rwa [show Nat.count (fun i => transWord i = 0) 15 = 6 by decide] at h

example : a287723 10 = 23 := by
  have h := a287723_count_succ (t := 22) (by decide)
  rwa [show Nat.count (fun i => transWord i = 0) 22 = 9 by decide] at h

/-! ## Word combinatorics -/

/-- A word is binary when all of its letters are `0` or `1`. -/
def Binary (u : List ℕ) : Prop := ∀ x ∈ u, x ≤ 1

/-- Every iterate `fibIter k` is a word over `{0, 1}`. -/
lemma fibIter_binary (k : ℕ) : Binary (fibIter k) := by
  induction k with
  | zero => simp [Binary, fibIter]
  | succ k ih =>
    intro x hx
    simp only [fibIter, List.mem_flatMap] at hx
    obtain ⟨b, -, hb⟩ := hx
    unfold fibMorph at hb
    split_ifs at hb <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> omega

/-- Each iterate is a prefix of the next one (`[0] <+: [0, 1]`, then apply `σ`). -/
lemma fibIter_prefix_succ (k : ℕ) : fibIter k <+: fibIter (k + 1) := by
  induction k with
  | zero => exact ⟨[1], rfl⟩
  | succ k ih => exact ih.flatMap fibMorph

/-- Iterates form a prefix chain: `fibIter k <+: fibIter l` for `k ≤ l`. -/
lemma fibIter_prefix_of_le {k l : ℕ} (h : k ≤ l) : fibIter k <+: fibIter l := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (fibIter_prefix_succ _)

/-- Every iterate begins with the letter `0`. -/
lemma fibIter_eq_cons (k : ℕ) : ∃ r, fibIter k = 0 :: r := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨1 :: r.flatMap fibMorph, by simp [fibIter, hr, fibMorph]⟩

/-- `σ` does not shorten words. -/
lemma length_le_flatMap_fibMorph (u : List ℕ) : u.length ≤ (u.flatMap fibMorph).length := by
  induction u with
  | nil => simp
  | cons b u ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (fibMorph b).length := by unfold fibMorph; split_ifs <;> simp
    omega

/-- For a binary word `u`: `|σ(u)| + #₁(u) = 2|u|`
(each `0` gives two letters, each `1` gives one). -/
lemma flatMap_fibMorph_length (u : List ℕ) (hu : Binary u) :
    (u.flatMap fibMorph).length + u.sum = 2 * u.length := by
  induction u with
  | nil => simp
  | cons b u ih =>
    have hb : b ≤ 1 := hu b (by simp)
    have ih' := ih (fun x hx => hu x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.sum_cons]
    interval_cases b
    · simp only [List.length_flatMap, fibMorph, ↓reduceIte, List.length_cons, List.length_nil,
        zero_add, Nat.reduceAdd] at ih' ⊢
      omega
    · simp only [List.length_flatMap, fibMorph, one_ne_zero, ↓reduceIte, List.length_cons,
        List.length_nil, zero_add] at ih' ⊢
      omega

/-- For a binary word `u`: `#₁(σ(u)) + #₁(u) = |u|`
(the `1`s of `σ(u)` come from the `0`s of `u`). -/
lemma flatMap_fibMorph_sum (u : List ℕ) (hu : Binary u) :
    (u.flatMap fibMorph).sum + u.sum = u.length := by
  induction u with
  | nil => simp
  | cons b u ih =>
    have hb : b ≤ 1 := hu b (by simp)
    have ih' := ih (fun x hx => hu x (by simp [hx]))
    simp only [List.flatMap_cons, List.sum_append, List.length_cons, List.sum_cons]
    interval_cases b
    · simp only [fibMorph, ↓reduceIte, List.sum_cons, List.sum_nil, add_zero, zero_add] at ih' ⊢
      omega
    · simp only [fibMorph, one_ne_zero, ↓reduceIte, List.sum_cons, List.sum_nil, add_zero,
        zero_add] at ih' ⊢
      omega

/-- For a binary word `u`: `|τ(u)| = |u| + 2·#₁(u)` where `τ = transMorph`. -/
lemma flatMap_transMorph_length (u : List ℕ) (hu : Binary u) :
    (u.flatMap transMorph).length = u.length + 2 * u.sum := by
  induction u with
  | nil => simp
  | cons b u ih =>
    have hb : b ≤ 1 := hu b (by simp)
    have ih' := ih (fun x hx => hu x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.sum_cons]
    interval_cases b
    · simp only [List.length_flatMap, transMorph, ↓reduceIte, List.length_cons, List.length_nil,
        zero_add] at ih' ⊢
      omega
    · simp only [List.length_flatMap, transMorph, one_ne_zero, ↓reduceIte, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd] at ih' ⊢
      omega

/-- For a binary word `u`: `#₀(τ(u)) = 2·#₁(u)` (each `1 ↦ 010` gives two `0`s). -/
lemma flatMap_transMorph_count (u : List ℕ) (hu : Binary u) :
    (u.flatMap transMorph).count 0 = 2 * u.sum := by
  induction u with
  | nil => simp
  | cons b u ih =>
    have hb : b ≤ 1 := hu b (by simp)
    have ih' := ih (fun x hx => hu x (by simp [hx]))
    simp only [List.flatMap_cons, List.count_append, List.sum_cons]
    interval_cases b
    · simp only [transMorph, ↓reduceIte, not_false_eq_true, ne_eq, one_ne_zero,
        List.count_cons_of_ne, List.count_nil, zero_add] at ih' ⊢
      omega
    · simp only [transMorph, one_ne_zero, ↓reduceIte, List.count_cons_self, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_self, not_false_eq_true, List.nodup_nil, and_self,
        zero_ne_one, or_false, or_true, List.count_eq_one_of_mem, Nat.reduceAdd] at ih' ⊢
      omega

/-- `fibIter k` has more than `k` letters, so `fibWord k` reads a genuine letter. -/
lemma length_fibIter (k : ℕ) : k < (fibIter k).length := by
  induction k with
  | zero => simp [fibIter]
  | succ k ih =>
    obtain ⟨r, hr⟩ := fibIter_eq_cons k
    have h1 := length_le_flatMap_fibMorph r
    have h2 : (fibIter (k + 1)).length = r.length + 2 + (r.flatMap fibMorph).length - r.length := by
      simp only [fibIter, hr, List.flatMap_cons, fibMorph, ↓reduceIte, List.cons_append,
        List.nil_append, List.length_cons, List.length_flatMap]
      omega
    rw [hr] at ih
    simp only [List.length_cons, Order.lt_add_one_iff] at ih
    omega

/-- `τ = transMorph` does not shorten words. -/
lemma length_le_flatMap_transMorph (u : List ℕ) : u.length ≤ (u.flatMap transMorph).length := by
  induction u with
  | nil => simp
  | cons b u ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have : 1 ≤ (transMorph b).length := by unfold transMorph; split_ifs <;> simp
    omega

/-- Two prefixes of a common list agree at every index lying in both. -/
lemma getD_eq_of_prefix {u v w : List ℕ} (hu : u <+: w) (hv : v <+: w) {i : ℕ}
    (hiu : i < u.length) (hiv : i < v.length) : u.getD i 0 = v.getD i 0 := by
  rw [List.getD_eq_getElem _ _ hiu, List.getD_eq_getElem _ _ hiv, hu.getElem hiu, hv.getElem hiv]

/-- Any prefix `u` of an iterate `fibIter k` is the corresponding prefix of the
infinite word `fibWord`. -/
lemma map_fibWord_of_prefix {u : List ℕ} {k : ℕ} (h : u <+: fibIter k) :
    (List.range u.length).map fibWord = u := by
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.getElem_map, List.getElem_range]
  have hik : i < (fibIter k).length := lt_of_lt_of_le hi2 h.length_le
  have hii : i < (fibIter i).length := length_fibIter i
  unfold fibWord
  rw [← List.getD_eq_getElem _ 0 hi2]
  rcases le_total i k with hle | hle
  · exact getD_eq_of_prefix (fibIter_prefix_of_le hle) h hii hi2
  · exact getD_eq_of_prefix (List.prefix_refl _) (h.trans (fibIter_prefix_of_le hle)) hii hi2


/-- Any prefix `u` of `τ(fibIter k)` is the corresponding prefix of the
infinite word `transWord`. -/
lemma map_transWord_of_prefix {u : List ℕ} {k : ℕ} (h : u <+: (fibIter k).flatMap transMorph) :
    (List.range u.length).map transWord = u := by
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.getElem_map, List.getElem_range]
  have hii : i < ((fibIter i).flatMap transMorph).length :=
    lt_of_lt_of_le (length_fibIter i) (length_le_flatMap_transMorph _)
  unfold transWord
  rw [← List.getD_eq_getElem _ 0 hi2]
  rcases le_total i k with hle | hle
  · exact getD_eq_of_prefix ((fibIter_prefix_of_le hle).flatMap transMorph) h hii hi2
  · exact getD_eq_of_prefix (List.prefix_refl _)
      (h.trans ((fibIter_prefix_of_le hle).flatMap transMorph)) hii hi2

/-- The prefix `F[0, m)` of length `m` of the Fibonacci word. -/
def pre (m : ℕ) : List ℕ := (List.range m).map fibWord

/-- `F[0, m)` is a prefix of the iterate `fibIter m`. -/
lemma pre_prefix (m : ℕ) : pre m <+: fibIter m := by
  have hlen : ((fibIter m).take m).length = m := by
    simp only [List.length_take]; have := length_fibIter m; omega
  have h := map_fibWord_of_prefix (List.take_prefix m (fibIter m))
  rw [hlen] at h
  unfold pre; rw [h]; exact List.take_prefix m (fibIter m)

/-- The Fibonacci word is binary. -/
lemma fibWord_le_one (n : ℕ) : fibWord n ≤ 1 := by
  have h := pre_prefix (n + 1)
  have hmem : fibWord n ∈ pre (n + 1) := by
    simp only [pre, List.mem_map, List.mem_range, Order.lt_add_one_iff]
    exact ⟨n, le_rfl, rfl⟩
  exact fibIter_binary _ _ (h.subset hmem)

/-- Every prefix of the Fibonacci word is binary. -/
lemma pre_binary (m : ℕ) : Binary (pre m) := by
  intro x hx
  simp only [pre, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact fibWord_le_one i

/-- `F[0, m + 1) = F[0, m) ++ [F m]`. -/
lemma pre_succ (m : ℕ) : pre (m + 1) = pre m ++ [fibWord m] := by
  simp [pre, List.range_succ]

/-- `F[0, m)` has length `m`. -/
lemma length_pre (m : ℕ) : (pre m).length = m := by simp [pre]

/-- `ones m` is the number of `1`s in `F[0, m)`. -/
def ones (m : ℕ) : ℕ := (pre m).sum

/-- `ones (m + 1) = ones m + F m`. -/
lemma ones_succ (m : ℕ) : ones (m + 1) = ones m + fibWord m := by
  simp [ones, pre_succ]

/-- `blockStart m = |σ(F[0, m))|`, the start of the `σ`-block of letter `m`
in `F = σ(F)`. -/
def blockStart (m : ℕ) : ℕ := ((pre m).flatMap fibMorph).length

/-- Self-similarity `σ(F) = F` on prefixes: `F[0, blockStart m) = σ(F[0, m))`. -/
lemma pre_blockStart (m : ℕ) : pre (blockStart m) = (pre m).flatMap fibMorph := by
  have h := map_fibWord_of_prefix (k := m + 1) ((pre_prefix m).flatMap fibMorph)
  exact h

/-- `blockStart m + ones m = 2m`. -/
lemma blockStart_add_ones (m : ℕ) : blockStart m + ones m = 2 * m := by
  have := flatMap_fibMorph_length (pre m) (pre_binary m)
  rw [length_pre] at this
  exact this

/-- `ones (blockStart m) + ones m = m`: the `1`s of `σ(F[0, m))` are the `0`s of `F[0, m)`. -/
lemma ones_blockStart (m : ℕ) : ones (blockStart m) + ones m = m := by
  have := flatMap_fibMorph_sum (pre m) (pre_binary m)
  rw [length_pre] at this
  unfold ones; rw [pre_blockStart]; exact this

/-- Every `σ`-block starts with `0`: `F (blockStart m) = 0`. -/
lemma fibWord_blockStart (m : ℕ) : fibWord (blockStart m) = 0 := by
  have h := pre_blockStart (m + 1)
  rw [pre_succ, List.flatMap_append] at h
  have hlt : blockStart m < (pre (blockStart (m + 1))).length := by
    rw [length_pre]
    have h1 := blockStart_add_ones m
    have h2 := blockStart_add_ones (m + 1)
    have h3 := ones_succ m
    have h4 := fibWord_le_one m
    omega
  have hg : (pre (blockStart (m + 1)))[blockStart m] = fibWord (blockStart m) := by
    simp [pre]
  rw [← hg]
  simp only [h]
  rw [List.getElem_append_right (by simp [blockStart])]
  simp only [List.flatMap_cons, fibMorph, List.flatMap_nil, List.append_nil, blockStart,
    List.length_flatMap, tsub_self]
  split_ifs <;> simp


/-- `alpha = (3 - √5)/2 = 2 - φ = 1/φ²`, the frequency of `1` in the Fibonacci word. -/
noncomputable def alpha : ℝ := (3 - √5) / 2

/-- Crude bounds `2 < √5 < 7/3`. -/
lemma sqrt5_bounds : 2 < √5 ∧ √5 < 7 / 3 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  constructor <;> nlinarith

/-- `alpha` is a root of `x² - 3x + 1`. -/
lemma alpha_sq : alpha ^ 2 = 3 * alpha - 1 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold alpha; linear_combination h5 / 4

/-- `1/3 < alpha < 1/2`. -/
lemma alpha_bounds : 1 / 3 < alpha ∧ alpha < 1 / 2 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  unfold alpha; constructor <;> linarith

/-- The Beatty bound at `n`: `ones n < (n + 1)·alpha < ones n + 1`,
i.e. `ones n = ⌊(n + 1)·alpha⌋`. -/
def OnesBound (n : ℕ) : Prop := (ones n : ℝ) < (n + 1) * alpha ∧ (n + 1) * alpha < ones n + 1

/-- Real-arithmetic core: if `k < (m+1)α < k+1`, `L = 2m - k` and `j = m - k`,
then `j < (L+1)α < j+1` and `j < (L+2)α < j+1` (uses `α² = 3α - 1`). -/
lemma onesBound_step {m k L j : ℕ} (hL : L + k = 2 * m) (hj : j + k = m)
    (h1 : (k : ℝ) < (m + 1) * alpha) (h2 : (m + 1) * alpha < k + 1) :
    ((j : ℝ) < (L + 1) * alpha ∧ (L + 1) * alpha < j + 1) ∧
      ((j : ℝ) < (L + 2) * alpha ∧ (L + 2) * alpha < j + 1) := by
  have hL' : (L : ℝ) = 2 * m - k := by
    have : ((L + k : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) := by rw [hL]
    push_cast at this; linarith
  have hj' : (j : ℝ) = m - k := by
    have : ((j + k : ℕ) : ℝ) = (m : ℝ) := by rw [hj]
    push_cast at this; linarith
  obtain ⟨hα1, hα2⟩ := alpha_bounds
  have hsq := alpha_sq
  have key : (L + 1) * alpha - j = (1 - alpha) * (k + 1 - (m + 1) * alpha) := by
    rw [hL', hj']; linear_combination (-(m : ℝ) - 1) * hsq
  have hpos : 0 < (1 - alpha) * (k + 1 - (m + 1) * alpha) := mul_pos (by linarith) (by linarith)
  have hlt : (1 - alpha) * (k + 1 - (m + 1) * alpha) < 1 - alpha := by
    have : k + 1 - (m + 1) * alpha < 1 := by linarith
    nlinarith
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by nlinarith⟩⟩


/-- `F 0 = 0`. -/
lemma fibWord_zero : fibWord 0 = 0 := by decide

/-- Since `F 0 = 0`, `ones (m + 1) ≤ m`. -/
lemma ones_succ_le (m : ℕ) : ones (m + 1) ≤ m := by
  induction m with
  | zero => rw [ones_succ, fibWord_zero]; simp [ones, pre]
  | succ m ih => rw [ones_succ (m + 1)]; have := fibWord_le_one (m + 1); omega

/-- The Beatty bound propagates from `m` to `blockStart m` and `blockStart m + 1`. -/
lemma onesBound_blockStart (m : ℕ) (hm : OnesBound m) :
    OnesBound (blockStart m) ∧ OnesBound (blockStart m + 1) := by
  have hL := blockStart_add_ones m
  have hj := ones_blockStart m
  have hs : ones (blockStart m + 1) = ones (blockStart m) := by
    rw [ones_succ, fibWord_blockStart]; rfl
  obtain ⟨h1, h2⟩ := onesBound_step hL hj hm.1 hm.2
  refine ⟨?_, ?_⟩
  · exact h1
  · unfold OnesBound; rw [hs]; push_cast
    have : ((blockStart m : ℝ) + 1 + 1) = (blockStart m : ℝ) + 2 := by ring
    rw [this]; exact h2

/-- The Beatty bound holds below `blockStart (m + 1)` (induction on `m`). -/
lemma onesBound_aux (m : ℕ) : ∀ n < blockStart (m + 1), OnesBound n := by
  induction m with
  | zero =>
    intro n hn
    have hb : blockStart 1 = 2 := by decide
    obtain ⟨hα1, hα2⟩ := alpha_bounds
    rw [hb] at hn
    interval_cases n
    · unfold OnesBound
      simp only [ones, pre, List.range_zero, List.map_nil, List.sum_nil, CharP.cast_eq_zero,
        zero_add, one_mul]
      constructor <;> linarith
    · unfold OnesBound; have : ones 1 = 0 := by decide
      rw [this]; push_cast; constructor <;> linarith
  | succ m ih =>
    intro n hn
    by_cases hlt : n < blockStart (m + 1)
    · exact ih n hlt
    · have hm1 : m + 1 < blockStart (m + 1) := by
        have := blockStart_add_ones (m + 1); have := ones_succ_le m; omega
      have hinv := onesBound_blockStart (m + 1) (ih _ hm1)
      have h1 := blockStart_add_ones (m + 1)
      have h2 := blockStart_add_ones (m + 1 + 1)
      have h3 := ones_succ (m + 1)
      have h4 := fibWord_le_one (m + 1)
      have : n = blockStart (m + 1) ∨ n = blockStart (m + 1) + 1 := by omega
      rcases this with rfl | rfl
      · exact hinv.1
      · exact hinv.2

/-- **Bridge.** For every `n`, `ones n < (n + 1)·alpha < ones n + 1`. -/
theorem onesBound_all (n : ℕ) : OnesBound n := by
  apply onesBound_aux n n
  have := blockStart_add_ones (n + 1); have := ones_succ_le n; omega


/-- For every `q` there is a position `p` holding the `(q+1)`-th `1` of `F`:
`F p = 1` and `ones p = q`. -/
lemma exists_fibWord_one (q : ℕ) : ∃ p, fibWord p = 1 ∧ ones p = q := by
  have hex : ∃ N, q < ones N := by
    refine ⟨3 * (q + 1), ?_⟩
    have h := (onesBound_all (3 * (q + 1))).2
    obtain ⟨hα1, -⟩ := alpha_bounds
    push_cast at h
    have : (q : ℝ) < ones (3 * (q + 1)) := by nlinarith
    exact_mod_cast this
  classical
  let N := Nat.find hex
  have hN : q < ones N := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0; rw [h0] at hN; simp [ones, pre] at hN
  obtain ⟨p, hp⟩ : ∃ p, N = p + 1 := ⟨N - 1, by omega⟩
  have hmin : ¬ q < ones p := Nat.find_min hex (by omega)
  have hs := ones_succ p
  have hle := fibWord_le_one p
  rw [hp] at hN
  refine ⟨p, by omega, by omega⟩

/-- `preT p = τ(F[0, p))`, the A287722-prefix produced by the first `p` letters of `F`. -/
def preT (p : ℕ) : List ℕ := (pre p).flatMap transMorph

/-- `τ(F[0, p))` is a prefix of the infinite word A287722. -/
lemma map_transWord_preT (p : ℕ) : (List.range (preT p).length).map transWord = preT p :=
  map_transWord_of_prefix (k := p) ((pre_prefix p).flatMap transMorph)

/-- `Nat.count` of zeros of A287722 below `t` equals the list count on the length-`t` prefix. -/
lemma count_transWord_eq (t : ℕ) :
    Nat.count (fun i => transWord i = 0) t = ((List.range t).map transWord).count 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.count_succ, ih, List.range_succ, List.map_append, List.count_append]
    by_cases h : transWord t = 0 <;> simp [h]

/-- `|τ(F[0, p))| = p + 2·ones p`. -/
lemma length_preT (p : ℕ) : (preT p).length = p + 2 * ones p := by
  rw [preT, flatMap_transMorph_length _ (pre_binary p), length_pre]; rfl

/-- If `F p = 1`, A287722 carries the block `010` at 0-indexed positions
`p + 2·ones p + {0, 1, 2}`. -/
lemma transWord_block {p : ℕ} (hp : fibWord p = 1) (e : ℕ) (he : e < 3) :
    transWord (p + 2 * ones p + e) = [0, 1, 0][e]'(by simpa using he) := by
  have h := map_transWord_preT (p + 1)
  have hsplit : preT (p + 1) = preT p ++ [0, 1, 0] := by
    simp [preT, pre_succ, hp, transMorph]
  have hlen : p + 2 * ones p + e < (preT (p + 1)).length := by
    rw [hsplit, List.length_append, length_preT]
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    omega
  have hg : transWord (p + 2 * ones p + e) = (preT (p + 1))[p + 2 * ones p + e]'hlen := by
    have := List.getElem_of_eq h (i := p + 2 * ones p + e) (by simpa using hlen)
    simpa using this
  rw [hg, List.getElem_of_eq hsplit, List.getElem_append_right (by rw [length_preT]; omega)]
  simp only [length_preT]
  congr 1; omega

/-- If `F p = 1`, A287722 has `2·ones p` zeros before position `p + 2·ones p`
and `2·ones p + 1` zeros before position `p + 2·ones p + 2`. -/
lemma count_transWord_block {p : ℕ} (hp : fibWord p = 1) :
    Nat.count (fun i => transWord i = 0) (p + 2 * ones p) = 2 * ones p ∧
      Nat.count (fun i => transWord i = 0) (p + 2 * ones p + 2) = 2 * ones p + 1 := by
  have h0 : Nat.count (fun i => transWord i = 0) (p + 2 * ones p) = 2 * ones p := by
    rw [count_transWord_eq, ← length_preT, map_transWord_preT, preT,
      flatMap_transMorph_count _ (pre_binary p)]; rfl
  refine ⟨h0, ?_⟩
  have t0 := transWord_block hp 0 (by norm_num)
  have t1 := transWord_block hp 1 (by norm_num)
  simp only [add_zero, List.getElem_cons_zero] at t0
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at t1
  rw [show p + 2 * ones p + 2 = p + 2 * ones p + 1 + 1 by ring, Nat.count_succ, Nat.count_succ,
    h0, t0, t1]
  simp


/-- If `F p = 1` and `b ≤ 1`, then `a(2·ones p + b + 1) = p + 2·ones p + 2b + 1`. -/
lemma a287723_eq {p : ℕ} (hp : fibWord p = 1) (b : ℕ) (hb : b ≤ 1) :
    a287723 (2 * ones p + b + 1) = p + 2 * ones p + 2 * b + 1 := by
  obtain ⟨c0, c2⟩ := count_transWord_block hp
  have t0 := transWord_block hp 0 (by norm_num)
  have t2 := transWord_block hp 2 (by norm_num)
  simp only [add_zero, List.getElem_cons_zero] at t0
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at t2
  unfold a287723
  rw [Nat.add_sub_cancel]
  interval_cases b
  · have h := Nat.nth_count (p := fun i => transWord i = 0) t0
    rw [c0] at h
    rw [add_zero, h]
  · have h := Nat.nth_count (p := fun i => transWord i = 0) t2
    rw [c2] at h
    rw [h]

/-- If `F p = 1` then `(p+1)·alpha < ones p + 1 < (p+2)·alpha`. -/
lemma position_bounds {p : ℕ} (hp : fibWord p = 1) :
    ((p : ℝ) + 1) * alpha < ones p + 1 ∧ (ones p : ℝ) + 1 < (p + 2) * alpha := by
  have h1 := (onesBound_all p).2
  have h2 := (onesBound_all (p + 1)).1
  rw [ones_succ, hp] at h2
  push_cast at h1 h2
  constructor
  · linarith
  · linarith
/-- Kimberling's conjecture (OEIS A287723, June 2, 2017):
`-1 < nr - a(n) < 1` for `1 ≤ n`, where `r = (7+√5)/4` and
`a(n)` is the 1-indexed position of the `n`-th zero in the
`0 ↦ 1`, `1 ↦ 010` transform of the Fibonacci word A003849.
The guard is the source's offset; `a(0)` is unused. The proof uses
`a(2j-1) = ⌊jφ²⌋ + 2j - 2` and `a(2j) = ⌊jφ²⌋ + 2j`. -/
theorem a287723_conjecture (n : ℕ) (hn : 1 ≤ n) :
    -1 < (n : ℝ) * ((7 + √5) / 4) - a287723 n ∧ (n : ℝ) * ((7 + √5) / 4) - a287723 n < 1 := by
  obtain ⟨p, hp, hq⟩ := exists_fibWord_one ((n - 1) / 2)
  obtain ⟨b, hbdef⟩ : ∃ b, b = (n - 1) % 2 := ⟨_, rfl⟩
  have hb : b ≤ 1 := by omega
  have hn' : n = 2 * ones p + b + 1 := by omega
  have ha := a287723_eq hp b hb
  rw [← hn'] at ha
  rw [ha]
  have hnR : (n : ℝ) = 2 * (ones p : ℝ) + b + 1 := by rw [hn']; push_cast; ring
  rw [hnR]
  obtain ⟨h1, h2⟩ := position_bounds hp
  obtain ⟨hs1, hs2⟩ := sqrt5_bounds
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  set q := ones p
  set s := √5
  have k1 : (p : ℝ) + 1 < (q + 1) * (3 + s) / 2 := by
    unfold alpha at h1; nlinarith
  have k2 : (q + 1) * (3 + s) / 2 < (p : ℝ) + 2 := by
    unfold alpha at h2; nlinarith
  interval_cases b
  · push_cast
    constructor <;> nlinarith
  · push_cast
    constructor <;> nlinarith


/-! ## Golden-ratio form of the bridge -/

/-- `alpha = 2 - φ`. -/
lemma alpha_eq : alpha = 2 - Real.goldenRatio := by
  unfold alpha Real.goldenRatio; ring

/-- **Bridge (Beatty form).** The number of `1`s among the first `n` letters of
the Fibonacci word is `⌊(n + 1)(2 - φ)⌋`. -/
theorem ones_eq_floor (n : ℕ) :
    (ones n : ℤ) = ⌊((n : ℝ) + 1) * (2 - Real.goldenRatio)⌋ := by
  obtain ⟨h1, h2⟩ := onesBound_all n
  rw [← alpha_eq]
  symm
  rw [Int.floor_eq_iff]
  push_cast
  exact ⟨h1.le, h2⟩

/-- **A003849, Cloitre's formula.** `F(n) = ⌊(n+2)(2-φ)⌋ - ⌊(n+1)(2-φ)⌋`. -/
theorem fibWord_eq_floor_sub (n : ℕ) :
    (fibWord n : ℤ) = ⌊((n : ℝ) + 2) * (2 - Real.goldenRatio)⌋ -
      ⌊((n : ℝ) + 1) * (2 - Real.goldenRatio)⌋ := by
  have h := ones_eq_floor (n + 1)
  rw [← ones_eq_floor n, ones_succ] at *
  push_cast at h
  rw [show (n : ℝ) + 1 + 1 = n + 2 by ring] at h
  omega

/-- The hypothesis `1 ≤ n` is met, e.g. at `n = 1`, where
`a(1) = 2` and `r - 2 ≈ -0.309`. -/
example : -1 < (1 : ℝ) * ((7 + √5) / 4) - a287723 1 ∧ (1 : ℝ) * ((7 + √5) / 4) - a287723 1 < 1 := by
  have h := a287723_conjecture 1 le_rfl
  rwa [Nat.cast_one] at h

end Candidates.A287723FibonacciWordMorphism
