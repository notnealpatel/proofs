/-
# A284365 — Kimberling: `-2 < n r - a(n) < 2` for the positions of `0`

OEIS A284365 (Clark Kimberling, March 26, 2017) lists the 1-based
positions of 0 in A284364, the fixed point of `0 ↦ 1`, `1 ↦ 101010`.
Its conjectured bound `-2 < nr - a(n) < 2`, with `r = (9+√21)/6`,
fails at `n = 8933313`: `a(n) = 20222898` and `nr - a(n) > 2`.
Amiram Eldar's separate density conjecture is not addressed here.

The proof never materializes the 20-million-letter prefix. `cnt k c L` counts
the zeros among the first `L` letters of `σ^k(c)` by walking down the
substitution tree using closed-form block lengths, and `cnt_spec` proves it
correct. The kernel evaluates `cnt 13 1 …` by `decide`, and `Nat.nth_count`
turns the zero counts into the value of `a`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A284365Refutation

/-! ## Definition layer -/

/-- The substitution `0 ↦ 1`, `1 ↦ 101010` defining A284364. -/
def sigma : Fin 2 → List (Fin 2)
  | 0 => [1]
  | 1 => [1, 0, 1, 0, 1, 0]

/-- The iterates `W k = σ^k(1)`; each is a prefix of the next (`W_prefix_of_le`),
and their limit is the fixed point A284364. -/
def W : ℕ → List (Fin 2)
  | 0 => [1]
  | k + 1 => (W k).flatMap sigma

/-- The fixed point `u` of `σ` (A284364), indexed from `0`: the letter at index
`i` read off the iterate `W (i + 1)`, which has length greater than `i`
(`length_W_ge`). -/
def u (i : ℕ) : Fin 2 := (W (i + 1)).getD i 0

/-- A284365: the (1-indexed) position of the `n`-th letter `0` in `u`, for
`n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => u i = 0) (n - 1) + 1

/-- Kimberling's conjecture in OEIS A284365:
`-2 < nr - a(n) < 2` for `n ≥ 1`, where `r = (9+√21)/6`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (-2 : ℝ) < n * ((9 + Real.sqrt 21) / 6) - a n ∧
      (n : ℝ) * ((9 + Real.sqrt 21) / 6) - a n < 2

/-! ## Evaluation layer -/

/-- `expand k c = σ^k(c)`, expanded from the top: `σ^(k+1)(c)` is the
concatenation of `σ^k(d)` over the letters `d` of `σ(c)`. -/
def expand : ℕ → Fin 2 → List (Fin 2)
  | 0, c => [c]
  | k + 1, c => (sigma c).flatMap (expand k)

/-- The pair `(|σ^k(0)|, |σ^k(1)|)`. -/
def lens : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 => ((lens k).2, 3 * (lens k).2 + 3 * (lens k).1)

/-- The pair (number of `0`s in `σ^k(0)`, number of `0`s in `σ^k(1)`). -/
def zers : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 => ((zers k).2, 3 * (zers k).2 + 3 * (zers k).1)

/-- Select the component of a pair indexed by a letter. -/
def pick (p : ℕ × ℕ) (c : Fin 2) : ℕ := if c = 0 then p.1 else p.2

/-- Walk the blocks `σ^k(d)`, `d ∈ ds`, counting zeros in the first `L` letters,
given the counting function `f` for a single block, the block lengths `len`
and the block zero counts `zer`. -/
def walk (f : Fin 2 → ℕ → ℕ) (len zer : Fin 2 → ℕ) : List (Fin 2) → ℕ → ℕ
  | [], _ => 0
  | d :: ds, L => if L ≤ len d then f d L else zer d + walk f len zer ds (L - len d)

/-- `cnt k c L` is the number of zeros among the first `L` letters of
`σ^k(c)` (`cnt_spec`). -/
def cnt : ℕ → Fin 2 → ℕ → ℕ
  | 0, c, L => if L = 0 then 0 else if c = 0 then 1 else 0
  | k + 1, c, L => walk (cnt k) (pick (lens k)) (pick (zers k)) (sigma c) L

/-! ## Correctness of the evaluator -/

/-- `σ^(k+1)(c) = σ(σ^k(c))`. -/
theorem expand_succ' (k : ℕ) (c : Fin 2) :
    expand (k + 1) c = (expand k c).flatMap sigma := by
  induction k generalizing c with
  | zero => simp [expand]
  | succ k ih =>
    show (sigma c).flatMap (expand (k + 1)) =
      ((sigma c).flatMap (expand k)).flatMap sigma
    rw [List.flatMap_assoc]
    congr 1
    funext d
    exact ih d

/-- The iterates `W k` are the expansions `σ^k(1)`. -/
theorem W_eq_expand (k : ℕ) : W k = expand k 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [W, ih, expand_succ']

/-- The block lengths are given by `lens`. -/
theorem length_expand (k : ℕ) (c : Fin 2) :
    (expand k c).length = pick (lens k) c := by
  induction k generalizing c with
  | zero => simp [expand, pick, lens]
  | succ k ih =>
    fin_cases c
    · simp [expand, sigma, pick, lens, ih]
    · simp [expand, sigma, pick, lens, ih]
      ring

/-- The block zero counts are given by `zers`. -/
theorem count_expand (k : ℕ) (c : Fin 2) :
    (expand k c).count 0 = pick (zers k) c := by
  induction k generalizing c with
  | zero => fin_cases c <;> simp [expand, pick, zers]
  | succ k ih =>
    fin_cases c
    · simp [expand, sigma, pick, zers, ih]
    · simp [expand, sigma, pick, zers, ih]
      ring

/-- Correctness of one walk over a list of blocks. -/
theorem walk_spec (k : ℕ) (f : Fin 2 → ℕ → ℕ) (len zer : Fin 2 → ℕ)
    (hf : ∀ d L, f d L = ((expand k d).take L).count 0)
    (hl : ∀ d, len d = (expand k d).length)
    (hz : ∀ d, zer d = (expand k d).count 0) (ds : List (Fin 2)) (L : ℕ) :
    walk f len zer ds L = ((ds.flatMap (expand k)).take L).count 0 := by
  induction ds generalizing L with
  | nil => simp [walk]
  | cons d ds ih =>
    simp only [walk, List.flatMap_cons, List.take_append, List.count_append]
    split_ifs with h
    · rw [hl] at h
      have h0 : L - (expand k d).length = 0 := by omega
      simp [h0, hf]
    · rw [hl] at h
      rw [List.take_of_length_le (by omega), hz, ih, hl]

/-- `cnt k c L` counts the zeros among the first `L` letters of `σ^k(c)`. -/
theorem cnt_spec (k : ℕ) (c : Fin 2) (L : ℕ) :
    cnt k c L = ((expand k c).take L).count 0 := by
  induction k generalizing c L with
  | zero =>
    rcases L with _ | L
    · simp [cnt]
    · fin_cases c <;> simp [cnt, expand]
  | succ k ih =>
    rw [cnt, walk_spec k (cnt k) (pick (lens k)) (pick (zers k)) ih
      (fun d => (length_expand k d).symm) (fun d => (count_expand k d).symm)]
    rfl

/-! ## The prefix chain and the bridge to `u` -/

/-- Each iterate is a prefix of the next. -/
theorem W_prefix_succ (k : ℕ) : W k <+: W (k + 1) := by
  induction k with
  | zero => exact ⟨[0, 1, 0, 1, 0], rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap sigma, ?_⟩
    show (W k).flatMap sigma ++ t.flatMap sigma = (W (k + 1)).flatMap sigma
    rw [← ht, List.flatMap_append]

/-- The iterates form a prefix chain. -/
theorem W_prefix_of_le {j k : ℕ} (h : j ≤ k) : W j <+: W k := by
  induction k, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k _ ih => exact ih.trans (W_prefix_succ k)

theorem lens_ge (k : ℕ) : k + 1 ≤ (lens k).2 := by
  induction k with
  | zero => simp [lens]
  | succ k ih => simp only [lens]; omega

/-- `|W k| ≥ k + 1`, so `u i` is read inside `W (i + 1)`. -/
theorem length_W_ge (k : ℕ) : k + 1 ≤ (W k).length := by
  rw [W_eq_expand, length_expand]
  simpa [pick] using lens_ge k

theorem getD_of_prefix {l₁ l₂ : List (Fin 2)} (h : l₁ <+: l₂) {i : ℕ}
    (hi : i < l₁.length) (d : Fin 2) : l₁.getD i d = l₂.getD i d := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

/-- `u` agrees with every iterate long enough to contain index `i`. -/
theorem u_eq_getD (K i : ℕ) (hi : i < (W K).length) : u i = (W K).getD i 0 := by
  have hi' : i < (W (i + 1)).length := by have := length_W_ge (i + 1); omega
  rcases le_total (i + 1) K with h | h
  · exact getD_of_prefix (W_prefix_of_le h) hi' 0
  · exact (getD_of_prefix (W_prefix_of_le h) hi 0).symm

/-- The number of zeros of `u` below `N` is read off any long enough iterate. -/
theorem count_u (K N : ℕ) (hN : N ≤ (W K).length) :
    Nat.count (fun i => u i = 0) N = ((W K).take N).count 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN' : N < (W K).length := by omega
    rw [Nat.count_succ, ih (by omega), List.take_add_one, List.count_append,
      u_eq_getD K N hN', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hN']
    simp [List.count_singleton]

/-- Evaluation of `a` from two zero counts in `σ^K(1)`: if there are `n` zeros
before index `m` and `n + 1` before index `m + 1`, then `a (n + 1) = m + 1`. -/
theorem a_eq_of_cnt (K m n : ℕ) (hm : m < pick (lens K) 1)
    (h0 : cnt K 1 m = n) (h1 : cnt K 1 (m + 1) = n + 1) : a (n + 1) = m + 1 := by
  have hlen : (W K).length = pick (lens K) 1 := by rw [W_eq_expand, length_expand]
  have hc : Nat.count (fun i => u i = 0) m = n := by
    rw [count_u K m (by omega), W_eq_expand, ← cnt_spec, h0]
  have hc' : Nat.count (fun i => u i = 0) (m + 1) = n + 1 := by
    rw [count_u K (m + 1) (by omega), W_eq_expand, ← cnt_spec, h1]
  have hp : u m = 0 := by
    rw [Nat.count_succ, hc] at hc'
    by_contra hne
    simp [hne] at hc'
  rw [a, Nat.add_sub_cancel, ← hc, Nat.nth_count hp]

/-! ## Examples -/

/-- The first 86 letters of `u` agree with the listed terms of A284364. -/
example : (List.range 86).map u =
    [1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,
     1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0,
     1,0,1,1,0,1,0,1,0,1,0,1,0,1] := by
  rw [List.map_congr_left (g := fun i => (W 4).getD i 0)
    (fun i hi => u_eq_getD 4 i (by
      rw [show (W 4).length = 306 by decide +kernel]
      have hi86 := List.mem_range.1 hi
      omega))]
  decide +kernel

/-- The zero positions of `W 4` below 138 are the 61 listed terms of A284365. -/
example : ((List.range 138).filter (fun i => (W 4).getD i 0 = 0)).map (· + 1) =
    [2,4,6,9,11,13,16,18,20,23,25,27,29,31,33,36,38,40,43,45,47,50,52,54,
     56,58,60,63,65,67,70,72,74,77,79,81,83,85,87,90,92,94,97,99,101,104,
     106,108,111,113,115,118,120,122,125,127,129,131,133,135,138] := by
  decide +kernel

example : a 1 = 2 := a_eq_of_cnt 4 1 0 (by decide) (by decide) (by decide)
example : a 4 = 9 := a_eq_of_cnt 4 8 3 (by decide) (by decide) (by decide)
example : a 61 = 138 := a_eq_of_cnt 4 137 60 (by decide) (by decide) (by decide)

/-! ## The refutation -/

/-- The witness value: `a(8933313) = 20222898`, by kernel evaluation of the zero
counts of `σ^13(1)` (length 49553046) at `20222897` and `20222898`. -/
theorem a_witness : a 8933313 = 20222898 :=
  a_eq_of_cnt 13 20222897 8933312 (by decide) (by decide) (by decide)

/-- At `n = 8933313`, `n r - a(n) > 2`: exactly, `21 n² > 40937583²` with
`40937583 = 6 a(n) + 12 - 9 n`. -/
theorem two_lt_witness :
    (2 : ℝ) < (8933313 : ℕ) * ((9 + Real.sqrt 21) / 6) - (20222898 : ℕ) := by
  have hs : (40937583 / 8933313 : ℝ) < Real.sqrt 21 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  push_cast
  linarith

/-- Kimberling's A284365 bound fails at `n = 8933313`, where
`a(n) = 20222898` and `nr - a(n) > 2` for `r = (9+√21)/6`.
The lower bound is not addressed. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have hup := (h 8933313 (by norm_num)).2
  rw [a_witness] at hup
  exact absurd hup (not_lt.2 two_lt_witness.le)

end Candidates.A284365Refutation
