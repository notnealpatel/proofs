/-
# A333637 — Kotesovec: cells covered twice in the square Genealodron

## OEIS source (`oeis show A333637`, retrieved 2026-10-21)

```
NAME:     The number of cells which contain multiple squares of a Genealodron
          formed from 2^n - 1 equal-sized squares (when viewed from above).
TERMS:    0,0,0,2,7,15,27,41,57,75,95,117,141,167,195,225,257,291,327,365,...
KEYWORDS: nonn,easy
COMMENT:  See A179178 for the definition of a Genealodron. In this variation,
          a Genealodron is a rooted binary tree constructed from squares. One
          edge of each square is attached to its parent and the two adjacent
          edges to its child trees.
          The first Genealodron consists of one square.
          The second Genealodron is formed by joining another equal-sized
          square to the left edge and to the right edge of the first so that
          the second Genealodron is made up of three squares.
          The third Genealodron is formed by joining squares to the upper and
          lower edges of both the second and third square of the second
          Genealodron so that the third Genealodron is made up of seven squares.
          This continues, with the edges to which the new squares are attached
          alternating between left/right and upper/lower.
          From the fourth generation onwards, some squares will overlap. a(n)
          is the number of cells which contain overlapping squares.
FORMULA (the conjecture):
  Conjecture: for n>=6, a(n) = n^2 - n - 15. - _Vaclav Kotesovec_, Apr 07 2020
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell). Colin Barker's g.f. and recurrence in the same entry are also
marked conjectural; they follow from the closed form proved here.

## Model

Each square occupies one unit lattice cell of `ℤ × ℤ`; a child attached across
an edge occupies the adjacent cell. Generation `j` (0-indexed) attaches its
children left/right when `j` is even and down/up when `j` is odd. The
Genealodron is a multiset of cells and a cell "contains multiple squares" when
its multiplicity is at least `2`. The model reproduces all 60 listed terms
(Python check, 2026-10-21) and the ground-truth examples below check
`a(1), …, a(8)` in the kernel.

## Proof

A generation-`j` square sits at `(x, y)` with multiplicity
`walk ((j+1)/2) x * walk (j/2) y`, where `walk h x` counts `±1` walks.
The parity of `(x, y)` fixes `j mod 4`, and within one residue class the
supporting rectangles are nested with strictly growing interior, so a cell
is covered twice iff it is a non-corner point of the rectangle of one of the
last four generations. Those four layers are disjoint and have
`((J+1)/2 + 1)(J/2 + 1) - 4` cells each, which sums to `n^2 - n - 15`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A333637LatticeCellsCovered

/-- The children of a square of generation `j` (0-indexed) at cell `p`: generation `j + 1`
is attached to the left and right edges when `j` is even and to the lower and upper edges when
`j` is odd. Each child occupies the unit lattice cell adjacent to its parent across that edge. -/
def children (j : ℕ) (p : ℤ × ℤ) : Multiset (ℤ × ℤ) :=
  if j % 2 = 0 then {(p.1 - 1, p.2), (p.1 + 1, p.2)} else {(p.1, p.2 - 1), (p.1, p.2 + 1)}

/-- The squares of generation `j` (0-indexed; `generation j` is the entry's `(j+1)`-st
generation), as a multiset of the lattice cells they occupy; it has `2 ^ j` squares. -/
def generation : ℕ → Multiset (ℤ × ℤ)
  | 0 => {(0, 0)}
  | j + 1 => (generation j).bind (children j)

/-- The `n`-generation Genealodron: all `2 ^ n - 1` squares of generations `0, …, n - 1`,
as a multiset of occupied lattice cells (multiplicity = number of squares on the cell). -/
def genealodron (n : ℕ) : Multiset (ℤ × ℤ) := ∑ j ∈ Finset.range n, generation j

/-- The lattice cells covered by at least two squares of the `n`-generation Genealodron;
its cardinality is `A333637 n`. -/
def multiplyCovered (n : ℕ) : Finset (ℤ × ℤ) :=
  (genealodron n).toFinset.filter (fun c => 2 ≤ (genealodron n).count c)

/-! ## Ground truth against the listed terms `0, 0, 0, 2, 7, 15, 27, 41` -/

example : (genealodron 5).card = 2 ^ 5 - 1 := by decide
example : (multiplyCovered 1).card = 0 := by decide
example : (multiplyCovered 2).card = 0 := by decide
example : (multiplyCovered 3).card = 0 := by decide
example : (multiplyCovered 4).card = 2 := by decide
example : (multiplyCovered 5).card = 7 := by decide
example : (multiplyCovered 6).card = 15 := by decide
set_option maxRecDepth 100000 in
example : (multiplyCovered 7).card = 27 := by decide
set_option maxRecDepth 100000 in
example : (multiplyCovered 8).card = 41 := by decide

-- The guard `6 ≤ n` is load-bearing: `a(5) = 7`, while `5^2 - 5 - 15 = 5`.
example : ((multiplyCovered 5).card : ℤ) ≠ (5 : ℤ) ^ 2 - 5 - 15 := by decide

/-! ## Proof -/

/-- `walk h x` is the number of `±1` sequences of length `h` with sum `x`. -/
def walk : ℕ → ℤ → ℕ
  | 0, x => if x = 0 then 1 else 0
  | h + 1, x => walk h (x + 1) + walk h (x - 1)

/-- One generation step: the multiplicity of a cell after attaching children is the sum of the
multiplicities of its two possible parents. -/
theorem count_bind_children (j : ℕ) (s : Multiset (ℤ × ℤ)) (x y : ℤ) :
    (s.bind (children j)).count (x, y) =
      if j % 2 = 0 then s.count (x + 1, y) + s.count (x - 1, y)
      else s.count (x, y + 1) + s.count (x, y - 1) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    obtain ⟨a1, a2⟩ := a
    rw [Multiset.cons_bind, Multiset.count_add, ih]
    by_cases hj : j % 2 = 0
    · simp only [children, hj, if_true, Multiset.insert_eq_cons, Multiset.count_cons,
        Multiset.count_singleton, Prod.mk.injEq]
      split_ifs <;> omega
    · simp only [children, hj, if_false, Multiset.insert_eq_cons, Multiset.count_cons,
        Multiset.count_singleton, Prod.mk.injEq]
      split_ifs <;> omega

/-- Multiplicity of a cell in generation `j`: a product of a horizontal walk count with
`(j + 1) / 2` steps and a vertical walk count with `j / 2` steps. -/
theorem count_generation (j : ℕ) (x y : ℤ) :
    (generation j).count (x, y) = walk ((j + 1) / 2) x * walk (j / 2) y := by
  induction j generalizing x y with
  | zero =>
    simp only [generation, Multiset.count_singleton, Prod.mk.injEq]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [walk, hx, hy]
  | succ j ih =>
    rw [generation, count_bind_children]
    by_cases hj : j % 2 = 0
    · have h1 : (j + 1 + 1) / 2 = (j + 1) / 2 + 1 := by omega
      have h2 : (j + 1) / 2 = j / 2 := by omega
      rw [if_pos hj, ih, ih, h1, walk, h2]
      ring
    · have h1 : (j + 1 + 1) / 2 = (j + 1) / 2 := by omega
      have h2 : (j + 1) / 2 = j / 2 + 1 := by omega
      rw [if_neg hj, ih, ih, h1, h2, walk.eq_2 y (j / 2)]
      ring

/-- Support of `walk h`: `x ∈ [-h, h]` with `x ≡ h (mod 2)`. -/
theorem walk_pos_iff (h : ℕ) (x : ℤ) :
    0 < walk h x ↔ -(h : ℤ) ≤ x ∧ x ≤ h ∧ (x + h) % 2 = 0 := by
  induction h generalizing x with
  | zero => simp only [walk]; split_ifs <;> simp_all; omega
  | succ h ih =>
    rw [walk, Nat.add_pos_iff_pos_or_pos, ih, ih]
    push_cast
    omega

/-- The extreme sums `± h` are reached by exactly one `±1` sequence. -/
theorem walk_eq_one (h : ℕ) (x : ℤ) (hx : x = h ∨ x = -h) : walk h x = 1 := by
  induction h generalizing x with
  | zero => simp only [walk]; simp_all
  | succ h ih =>
    rw [walk]
    rcases hx with hx | hx
    · have h0 : walk h (x + 1) = 0 := by
        by_contra hne
        have := (walk_pos_iff h (x + 1)).1 (Nat.pos_of_ne_zero hne)
        push_cast at hx; omega
      rw [h0, ih]; push_cast at hx; omega
    · have h0 : walk h (x - 1) = 0 := by
        by_contra hne
        have := (walk_pos_iff h (x - 1)).1 (Nat.pos_of_ne_zero hne)
        push_cast at hx; omega
      rw [h0, ih]; push_cast at hx; omega

/-- Every interior point of the support of `walk h` is reached by at least two sequences. -/
theorem two_le_walk (h : ℕ) (x : ℤ) (h1 : -(h : ℤ) < x) (h2 : x < h) (hp : (x + h) % 2 = 0) :
    2 ≤ walk h x := by
  cases h with
  | zero => omega
  | succ h =>
    rw [walk]
    have ha := (walk_pos_iff h (x + 1)).2 (by push_cast at *; omega)
    have hb := (walk_pos_iff h (x - 1)).2 (by push_cast at *; omega)
    omega


/-- The multiplicity of cell `(x, y)` in generation `j`. -/
def term (j : ℕ) (x y : ℤ) : ℕ := walk ((j + 1) / 2) x * walk (j / 2) y

/-- The multiplicity of a cell in the Genealodron is the sum of its generation multiplicities. -/
theorem count_genealodron (n : ℕ) (x y : ℤ) :
    (genealodron n).count (x, y) = ∑ j ∈ Finset.range n, term j x y := by
  rw [genealodron, Multiset.count_sum']
  exact Finset.sum_congr rfl fun j _ => count_generation j x y

/-- Cell `(x, y)` meets generation `j` iff it lies in the parity-matched rectangle
`[-(j+1)/2, (j+1)/2] × [-j/2, j/2]`. -/
theorem term_pos_iff (j : ℕ) (x y : ℤ) :
    0 < term j x y ↔
      (-(((j + 1) / 2 : ℕ) : ℤ) ≤ x ∧ x ≤ ((j + 1) / 2 : ℕ) ∧ (x + ((j + 1) / 2 : ℕ)) % 2 = 0) ∧
      (-((j / 2 : ℕ) : ℤ) ≤ y ∧ y ≤ (j / 2 : ℕ) ∧ (y + (j / 2 : ℕ)) % 2 = 0) := by
  rw [term, Nat.pos_iff_ne_zero, mul_ne_zero_iff, ← Nat.pos_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    walk_pos_iff, walk_pos_iff]

/-- The parity class of a cell determines the residue mod `4` of every generation meeting it. -/
theorem mod_four_eq_of_term_pos (j₁ j₂ : ℕ) (x y : ℤ) (h₁ : 0 < term j₁ x y)
    (h₂ : 0 < term j₂ x y) : j₁ % 4 = j₂ % 4 := by
  rw [term_pos_iff] at h₁ h₂
  omega

/-- A cell meeting generation `j` is covered at least twice by generation `j + 4m`, `m ≥ 1`. -/
theorem two_le_term_add_four_mul (j m : ℕ) (x y : ℤ) (hm : 0 < m) (h : 0 < term j x y) :
    2 ≤ term (j + 4 * m) x y := by
  have hH : (j + 4 * m + 1) / 2 = (j + 1) / 2 + 2 * m := by omega
  have hV : (j + 4 * m) / 2 = j / 2 + 2 * m := by omega
  rw [term_pos_iff] at h
  rw [term, hH, hV]
  have hx := two_le_walk ((j + 1) / 2 + 2 * m) x (by push_cast; omega) (by push_cast; omega)
    (by push_cast; omega)
  have hy := (walk_pos_iff (j / 2 + 2 * m) y).2 (by push_cast; omega)
  calc 2 = 2 * 1 := rfl
    _ ≤ _ := Nat.mul_le_mul hx hy



/-- A cell is covered at least twice iff one of the last four generations alone covers it at
least twice. -/
theorem two_le_count_iff (n : ℕ) (x y : ℤ) :
    2 ≤ (genealodron n).count (x, y) ↔ ∃ J ∈ Finset.Ico (n - 4) n, 2 ≤ term J x y := by
  rw [count_genealodron]
  constructor
  · intro hsum
    by_contra hcon
    push Not at hcon
    have hle : ∀ j < n, term j x y ≤ 1 := by
      intro j hj
      by_contra hj2
      push Not at hj2
      by_cases hjtop : n - 4 ≤ j
      · have := hcon j (Finset.mem_Ico.2 ⟨hjtop, hj⟩)
        omega
      · have htop := two_le_term_add_four_mul j ((n - 1 - j) / 4) x y (by omega) (by omega)
        have := hcon (j + 4 * ((n - 1 - j) / 4)) (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
        omega
    have huniq : ∀ j₁ < n, ∀ j₂ < n, 0 < term j₁ x y → 0 < term j₂ x y → j₁ = j₂ := by
      have key : ∀ j₁ j₂, j₁ < j₂ → j₂ < n → 0 < term j₁ x y → 0 < term j₂ x y → False := by
        intro j₁ j₂ hlt hj₂ h₁ h₂
        have hmod := mod_four_eq_of_term_pos j₁ j₂ x y h₁ h₂
        have hj : j₂ = j₁ + 4 * ((j₂ - j₁) / 4) := by omega
        have h2 := two_le_term_add_four_mul j₁ ((j₂ - j₁) / 4) x y (by omega) h₁
        rw [← hj] at h2
        have := hle j₂ hj₂
        omega
      intro j₁ hj₁ j₂ hj₂ h₁ h₂
      rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
      · exact (key j₁ j₂ hlt hj₂ h₁ h₂).elim
      · exact heq
      · exact (key j₂ j₁ hgt hj₁ h₂ h₁).elim
    have hsum_le : ∑ j ∈ Finset.range n, term j x y ≤ 1 := by
      by_cases hex : ∃ j₀ < n, 0 < term j₀ x y
      · obtain ⟨j₀, hj₀, hpos⟩ := hex
        rw [Finset.sum_eq_single j₀]
        · exact hle j₀ hj₀
        · intro b hb hne
          by_contra hb0
          exact hne (huniq b (Finset.mem_range.1 hb) j₀ hj₀ (Nat.pos_of_ne_zero hb0) hpos)
        · intro hj₀'
          exact (hj₀' (Finset.mem_range.2 hj₀)).elim
      · push Not at hex
        rw [Finset.sum_eq_zero fun j hj => Nat.le_zero.1 (hex j (Finset.mem_range.1 hj))]
        exact Nat.zero_le 1
    omega
  · rintro ⟨J, hJ, h2⟩
    have hJn : J ∈ Finset.range n := Finset.mem_range.2 (Finset.mem_Ico.1 hJ).2
    exact h2.trans (Finset.single_le_sum (fun j _ => Nat.zero_le (term j x y)) hJn)

/-- Generation `j` covers a cell at least twice iff the cell is in its rectangle and is not one
of the rectangle's corners. -/
theorem two_le_term_iff (j : ℕ) (x y : ℤ) :
    2 ≤ term j x y ↔ 0 < term j x y ∧
      ((-(((j + 1) / 2 : ℕ) : ℤ) < x ∧ x < ((j + 1) / 2 : ℕ)) ∨
        (-((j / 2 : ℕ) : ℤ) < y ∧ y < (j / 2 : ℕ))) := by
  constructor
  · intro h2
    refine ⟨by omega, ?_⟩
    have hpos := (term_pos_iff j x y).1 (by omega)
    by_contra hcorner
    have hx : walk ((j + 1) / 2) x = 1 := walk_eq_one _ x (by omega)
    have hy : walk (j / 2) y = 1 := walk_eq_one _ y (by omega)
    rw [term, hx, hy] at h2
    omega
  · rintro ⟨hpos, hint⟩
    have hb := (term_pos_iff j x y).1 hpos
    have hxp := (walk_pos_iff _ x).2 hb.1
    have hyp := (walk_pos_iff _ y).2 hb.2
    rw [term]
    rcases hint with hint | hint
    · have hx2 := two_le_walk _ x hint.1 hint.2 hb.1.2.2
      calc 2 = 2 * 1 := rfl
        _ ≤ _ := Nat.mul_le_mul hx2 hyp
    · have hy2 := two_le_walk _ y hint.1 hint.2 hb.2.2.2
      calc 2 = 1 * 2 := rfl
        _ ≤ _ := Nat.mul_le_mul hxp hy2

/-- The non-corner points of the parity-matched rectangle of generation `J`, as the image of
the index box with its corner indices removed. -/
def layer (J : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.range ((J + 1) / 2 + 1) ×ˢ Finset.range (J / 2 + 1)) \
      ({0, (J + 1) / 2} ×ˢ {0, J / 2})).image
    fun p => (2 * (p.1 : ℤ) - ((J + 1) / 2 : ℕ), 2 * (p.2 : ℤ) - (J / 2 : ℕ))

/-- `layer J` is exactly the set of cells that generation `J` covers at least twice. -/
theorem mem_layer_iff (J : ℕ) (x y : ℤ) : (x, y) ∈ layer J ↔ 2 ≤ term J x y := by
  rw [two_le_term_iff, term_pos_iff]
  simp only [layer, Finset.mem_image, Finset.mem_sdiff, Finset.mem_product, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hc⟩, rfl, rfl⟩
    omega
  · rintro ⟨⟨hx, hy⟩, hint⟩
    refine ⟨((x + ((J + 1) / 2 : ℕ)) / 2).toNat, ((y + (J / 2 : ℕ)) / 2).toNat,
      ⟨⟨by omega, by omega⟩, by omega⟩, by omega, by omega⟩


/-- The multiply covered cells are the union of the layers of the last four generations. -/
theorem multiplyCovered_eq_biUnion (n : ℕ) :
    multiplyCovered n = (Finset.Ico (n - 4) n).biUnion layer := by
  ext ⟨x, y⟩
  rw [Finset.mem_biUnion]
  simp only [mem_layer_iff]
  rw [← two_le_count_iff, multiplyCovered, Finset.mem_filter, Multiset.mem_toFinset,
    ← Multiset.count_pos]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

/-- For `J ≥ 2` the layer of generation `J` has `((J+1)/2 + 1)(J/2 + 1) - 4` cells. -/
theorem card_layer (J : ℕ) (hJ : 2 ≤ J) :
    (layer J).card = ((J + 1) / 2 + 1) * (J / 2 + 1) - 4 := by
  rw [layer, Finset.card_image_of_injective]
  · rw [Finset.card_sdiff_of_subset, Finset.card_product, Finset.card_product, Finset.card_range,
      Finset.card_range, Finset.card_pair (by omega), Finset.card_pair (by omega)]
    intro p hp
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_range]
      at hp ⊢
    omega
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    omega

/-- The layers of the last four generations are pairwise disjoint. -/
theorem card_multiplyCovered_eq_sum (n : ℕ) :
    (multiplyCovered n).card = ∑ J ∈ Finset.Ico (n - 4) n, (layer J).card := by
  rw [multiplyCovered_eq_biUnion, Finset.card_biUnion]
  intro J₁ hJ₁ J₂ hJ₂ hne
  simp only [Finset.coe_Ico, Set.mem_Ico] at hJ₁ hJ₂
  rw [Function.onFun, Finset.disjoint_left]
  rintro ⟨x, y⟩ h₁ h₂
  rw [mem_layer_iff] at h₁ h₂
  have hmod := mod_four_eq_of_term_pos J₁ J₂ x y (by omega) (by omega)
  omega

/-- Area identity: `4 ((J+1)/2 + 1)(J/2 + 1) + J % 2 = (J + 2)^2`. -/
theorem four_mul_area_add_mod (J : ℕ) :
    4 * (((J + 1) / 2 + 1) * (J / 2 + 1)) + J % 2 = (J + 2) ^ 2 := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' J
  · have h1 : (2 * s + 1) / 2 = s := by omega
    have h2 : 2 * s / 2 = s := by omega
    have h3 : 2 * s % 2 = 0 := by omega
    rw [h1, h2, h3]
    ring
  · have h1 : (2 * s + 1 + 1) / 2 = s + 1 := by omega
    have h2 : (2 * s + 1) / 2 = s := by omega
    have h3 : (2 * s + 1) % 2 = 1 := by omega
    rw [h1, h2, h3]
    ring

/-- The layer cardinality in integer form, for `J ≥ 2`. -/
theorem four_mul_card_layer (J : ℕ) (hJ : 2 ≤ J) :
    4 * ((layer J).card : ℤ) = ((J : ℤ) + 2) ^ 2 - ((J % 2 : ℕ) : ℤ) - 16 := by
  rw [card_layer J hJ]
  have harea := four_mul_area_add_mod J
  generalize ((J + 1) / 2 + 1) * (J / 2 + 1) = P at harea ⊢
  have hP : 4 ≤ P := by
    have hJ2 : 16 ≤ (J + 2) ^ 2 := by nlinarith
    omega
  rw [Nat.cast_sub hP]
  have hcast : ((4 * P + J % 2 : ℕ) : ℤ) = (((J + 2) ^ 2 : ℕ) : ℤ) := by rw [harea]
  push_cast at hcast ⊢
  linear_combination hcast

/-- **Kotesovec's conjecture (A333637, Vaclav Kotesovec, Apr 07 2020).**

Verbatim: "Conjecture: for n>=6, a(n) = n^2 - n - 15."

Here `a(n) = (multiplyCovered n).card` is the number of lattice cells covered by at least two of
the `2 ^ n - 1` squares of the `n`-generation square Genealodron. The guard `6 ≤ n` is from the
source and is load-bearing: `a(5) = 7 ≠ 5^2 - 5 - 15 = 5`. The difference is taken in `ℤ`. -/
theorem kotesovec_conjecture (n : ℕ) (hn : 6 ≤ n) : ((multiplyCovered n).card : ℤ) = (n : ℤ) ^ 2 - n - 15 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [card_multiplyCovered_eq_sum]
  have hIco : Finset.Ico (m + 6 - 4) (m + 6) = {m + 2, m + 3, m + 4, m + 5} := by
    ext J; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [hIco, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_singleton]
  have h2 := four_mul_card_layer (m + 2) (by omega)
  have h3 := four_mul_card_layer (m + 3) (by omega)
  have h4 := four_mul_card_layer (m + 4) (by omega)
  have h5 := four_mul_card_layer (m + 5) (by omega)
  have hpar : ((m + 2) % 2 + (m + 3) % 2 + (m + 4) % 2 + (m + 5) % 2 : ℕ) = 2 := by omega
  have hparZ : (((m + 2) % 2 : ℕ) : ℤ) + (((m + 3) % 2 : ℕ) : ℤ) + (((m + 4) % 2 : ℕ) : ℤ)
      + (((m + 5) % 2 : ℕ) : ℤ) = 2 := by exact_mod_cast hpar
  push_cast at h2 h3 h4 h5 hparZ ⊢
  linarith

-- Satisfiability of the hypothesis at the boundary: `n = 6` gives `15 = 36 - 6 - 15`.
example : ((multiplyCovered 6).card : ℤ) = (6 : ℤ) ^ 2 - 6 - 15 := kotesovec_conjecture 6 le_rfl

end Candidates.A333637LatticeCellsCovered
