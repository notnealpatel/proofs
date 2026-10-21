/-
# Covering `C_n^3` by three equivalence subgraphs

## Source

Zhanping Yang, *Covering powers of cycles with equivalence subgraphs*,
arXiv:2610.15635.  The paper proves (Theorem `thm:main-divisible`) that
`eq(C_{q(k+1)}^k) = 1 + ⌈log₂(k+1)⌉`, and (Theorem `thm:odd-power`) that
`eq(C_n^k) ≥ 2 + ⌈log₂(k+1)⌉` when `k + 1` is a power of two and `n` is odd.
Theorem `thm:exact-values` therefore leaves open the case
`k + 1 = 2^s`, `n` even, `(k + 1) ∤ n`; its smallest instance is
`k = 3`, `n ≡ 2 (mod 4)`.

Paper wording (abstract): "The equivalence covering number `eq(G)` ... is
the minimum number of equivalence subgraphs needed to cover all edges of
`G`."  An equivalence subgraph is "a disjoint union of cliques, with isolated
vertices allowed".  `C_n^k` has vertex set `V(C_n)`, "with two distinct
vertices adjacent whenever their distance in `C_n` is at most `k`".

## Claim formalized here (date 2026-10-21)

Residual case `k = 3` (not stated in the paper; conjectured by the triage
from SAT computations):

> For `n ≥ 11`, `C_n^3` can be covered by three equivalence subgraphs if and
> only if `4 ∣ n`.

Status: the "if" direction is the paper's construction (Theorem
`thm:main-divisible` with `k = 3`).  The "only if" direction is open in the
paper (it covers only odd `n`); it is proved below for every `n ≥ 10`.
Together with the paper's Proposition `prop:quadratic` (`eq(C_n^3) ≤ 4` for
`n ≥ 18`) it gives `eq(C_n^3) = 4` for `n ≥ 18`, `4 ∤ n`.

## Proof outline

Pull a cover back to `ℤ` along `ℤ → ZMod n`.  Two local facts about a
3-layer cover of the path power `P^3` (all checked by `grind`):

* Lemma A: on seven consecutive vertices, some layer has four consecutive
  vertices as one class.
* Lemma B: if `[w, w+3]` is a class of layer `s`, so is `[w+4, w+7]`.

Propagating Lemma B around the cycle gives classes `[w + 4m, w + 4m + 3]`
for all `m`; if `4 ∤ n` two of them overlap without coinciding, which forces
a class of span at least `4`.
-/
import Mathlib

set_option autoImplicit false

namespace CyclePowerEquivalenceCover

/-! ## Definitions -/

/-- Cyclic distance between two vertices of `C_n`, as `min (u - v) (v - u)`
computed in `ZMod n`. -/
def cycDist (n : ℕ) (u v : ZMod n) : ℕ := min (u - v).val (v - u).val

/-- The `k`-th power `C_n^k` of the cycle on `ZMod n`: distinct vertices are
adjacent when their cyclic distance is at most `k`. -/
def cyclePower (n k : ℕ) : SimpleGraph (ZMod n) where
  Adj u v := u ≠ v ∧ cycDist n u v ≤ k
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [cycDist, min_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency in `C_n^k` unfolds to distinctness plus the distance bound. -/
theorem cyclePower_adj {n k : ℕ} {u v : ZMod n} :
    (cyclePower n k).Adj u v ↔ u ≠ v ∧ cycDist n u v ≤ k := Iff.rfl

/-- Adjacency in `C_n^k` is decidable. -/
instance (n k : ℕ) : DecidableRel (cyclePower n k).Adj := fun _ _ =>
  decidable_of_iff _ cyclePower_adj.symm

/-- `C_n^k` can be covered by `t` equivalence subgraphs (`eq(C_n^k) ≤ t`).
Layer `s` is the equivalence subgraph whose components are the fibres of
the labelling `c s`; each fibre must be a clique of `C_n^k`, and every edge
of `C_n^k` must lie inside a fibre of some layer. -/
def EqCoverable (n k t : ℕ) : Prop :=
  ∃ c : Fin t → ZMod n → ℕ,
    (∀ s u v, u ≠ v → c s u = c s v → (cyclePower n k).Adj u v) ∧
    (∀ u v, (cyclePower n k).Adj u v → ∃ s, c s u = c s v)

/-! ### Ground-truth checks -/

example : cycDist 12 1 10 = 3 := by decide
example : cycDist 12 0 6 = 6 := by decide
example : (cyclePower 12 3).Adj 1 10 := by decide
example : ¬ (cyclePower 12 3).Adj 0 4 := by decide
example : ¬ (cyclePower 12 3).Adj 5 5 := by decide

/-! ## Local lemmas on the path power -/

/-- Lemma A (local core).  Three labellings of `ℤ` whose classes have span at
most `3` (tested on gaps `4..6`) and which cover all pairs at distance
`1..3`: some layer has one of the four windows `[w, w+3]`, `0 ≤ w ≤ 3`, as a
single class. -/
theorem lemmaA_core (a b e : ℤ → ℕ)
    (hsep : ∀ i j : ℤ, 4 ≤ j - i → j - i ≤ 6 → a i ≠ a j ∧ b i ≠ b j ∧ e i ≠ e j)
    (hcov : ∀ i j : ℤ, 0 < j - i → j - i ≤ 3 → a i = a j ∨ b i = b j ∨ e i = e j) :
    (a 0 = a 1 ∧ a 1 = a 2 ∧ a 2 = a 3) ∨ (a 1 = a 2 ∧ a 2 = a 3 ∧ a 3 = a 4) ∨
    (a 2 = a 3 ∧ a 3 = a 4 ∧ a 4 = a 5) ∨ (a 3 = a 4 ∧ a 4 = a 5 ∧ a 5 = a 6) ∨
    (b 0 = b 1 ∧ b 1 = b 2 ∧ b 2 = b 3) ∨ (b 1 = b 2 ∧ b 2 = b 3 ∧ b 3 = b 4) ∨
    (b 2 = b 3 ∧ b 3 = b 4 ∧ b 4 = b 5) ∨ (b 3 = b 4 ∧ b 4 = b 5 ∧ b 5 = b 6) ∨
    (e 0 = e 1 ∧ e 1 = e 2 ∧ e 2 = e 3) ∨ (e 1 = e 2 ∧ e 2 = e 3 ∧ e 3 = e 4) ∨
    (e 2 = e 3 ∧ e 3 = e 4 ∧ e 4 = e 5) ∨ (e 3 = e 4 ∧ e 4 = e 5 ∧ e 5 = e 6) := by
  have c01 := hcov 0 1 (by norm_num) (by norm_num)
  have c02 := hcov 0 2 (by norm_num) (by norm_num)
  have c03 := hcov 0 3 (by norm_num) (by norm_num)
  have c12 := hcov 1 2 (by norm_num) (by norm_num)
  have c13 := hcov 1 3 (by norm_num) (by norm_num)
  have c14 := hcov 1 4 (by norm_num) (by norm_num)
  have c23 := hcov 2 3 (by norm_num) (by norm_num)
  have c24 := hcov 2 4 (by norm_num) (by norm_num)
  have c25 := hcov 2 5 (by norm_num) (by norm_num)
  have c34 := hcov 3 4 (by norm_num) (by norm_num)
  have c35 := hcov 3 5 (by norm_num) (by norm_num)
  have c36 := hcov 3 6 (by norm_num) (by norm_num)
  have c45 := hcov 4 5 (by norm_num) (by norm_num)
  have c46 := hcov 4 6 (by norm_num) (by norm_num)
  have c56 := hcov 5 6 (by norm_num) (by norm_num)
  have s04 := hsep 0 4 (by norm_num) (by norm_num)
  have s05 := hsep 0 5 (by norm_num) (by norm_num)
  have s06 := hsep 0 6 (by norm_num) (by norm_num)
  have s15 := hsep 1 5 (by norm_num) (by norm_num)
  have s16 := hsep 1 6 (by norm_num) (by norm_num)
  have s26 := hsep 2 6 (by norm_num) (by norm_num)
  clear hsep hcov
  grind (splits := 40)

/-- Lemma B (local core).  Under the same hypotheses, if `[0, 3]` is a class
of layer `a` then so is `[4, 7]`. -/
theorem lemmaB_core (a b e : ℤ → ℕ)
    (hsep : ∀ i j : ℤ, 4 ≤ j - i → j - i ≤ 6 → a i ≠ a j ∧ b i ≠ b j ∧ e i ≠ e j)
    (hcov : ∀ i j : ℤ, 0 < j - i → j - i ≤ 3 → a i = a j ∨ b i = b j ∨ e i = e j)
    (h01 : a 0 = a 1) (h12 : a 1 = a 2) (h23 : a 2 = a 3) :
    a 4 = a 5 ∧ a 5 = a 6 ∧ a 6 = a 7 := by
  have c01 := hcov 0 1 (by norm_num) (by norm_num)
  have c02 := hcov 0 2 (by norm_num) (by norm_num)
  have c03 := hcov 0 3 (by norm_num) (by norm_num)
  have c12 := hcov 1 2 (by norm_num) (by norm_num)
  have c13 := hcov 1 3 (by norm_num) (by norm_num)
  have c14 := hcov 1 4 (by norm_num) (by norm_num)
  have c23 := hcov 2 3 (by norm_num) (by norm_num)
  have c24 := hcov 2 4 (by norm_num) (by norm_num)
  have c25 := hcov 2 5 (by norm_num) (by norm_num)
  have c34 := hcov 3 4 (by norm_num) (by norm_num)
  have c35 := hcov 3 5 (by norm_num) (by norm_num)
  have c36 := hcov 3 6 (by norm_num) (by norm_num)
  have c45 := hcov 4 5 (by norm_num) (by norm_num)
  have c46 := hcov 4 6 (by norm_num) (by norm_num)
  have c47 := hcov 4 7 (by norm_num) (by norm_num)
  have c56 := hcov 5 6 (by norm_num) (by norm_num)
  have c57 := hcov 5 7 (by norm_num) (by norm_num)
  have c67 := hcov 6 7 (by norm_num) (by norm_num)
  have s04 := hsep 0 4 (by norm_num) (by norm_num)
  have s05 := hsep 0 5 (by norm_num) (by norm_num)
  have s06 := hsep 0 6 (by norm_num) (by norm_num)
  have s15 := hsep 1 5 (by norm_num) (by norm_num)
  have s16 := hsep 1 6 (by norm_num) (by norm_num)
  have s17 := hsep 1 7 (by norm_num) (by norm_num)
  have s26 := hsep 2 6 (by norm_num) (by norm_num)
  have s27 := hsep 2 7 (by norm_num) (by norm_num)
  have s37 := hsep 3 7 (by norm_num) (by norm_num)
  clear hsep hcov
  grind

/-! ## Arithmetic of `ZMod.val` -/

/-- The value of a sum in `ZMod n` is the sum of the values, reduced at most
once by `n`. -/
theorem val_add_cases {n : ℕ} [NeZero n] (a b : ZMod n) :
    (a + b).val = a.val + b.val ∨ (a + b).val + n = a.val + b.val := by
  rw [ZMod.val_add]
  have ha := a.val_lt
  have hb := b.val_lt
  by_cases h : a.val + b.val < n
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The two directed differences `(u - v).val` and `(v - u).val` add up to
`0` or to `n`. -/
theorem val_sub_add_val_sub {n : ℕ} [NeZero n] (u v : ZMod n) :
    (u - v).val + (v - u).val = 0 ∨ (u - v).val + (v - u).val = n := by
  have h := val_add_cases (u - v) (v - u)
  have h0 : (u - v) + (v - u) = 0 := by ring
  rw [h0, ZMod.val_zero] at h
  omega

/-- Cyclic distance between the images of integers `i, j` with
`j - i = m`, `0 < m < n`, is `min (n - m) m`. -/
theorem cycDist_intCast {n : ℕ} [NeZero n] (i j : ℤ) (m : ℕ) (hm0 : 0 < m)
    (hmn : m < n) (hij : j - i = m) :
    cycDist n (i : ZMod n) (j : ZMod n) = min (n - m) m := by
  have hval : ((j : ZMod n) - (i : ZMod n)).val = m := by
    have hcast : (j : ZMod n) - (i : ZMod n) = (m : ZMod n) := by
      rw [← Int.cast_sub, hij, Int.cast_natCast]
    rw [hcast, ZMod.val_cast_of_lt hmn]
  have h := val_sub_add_val_sub (i : ZMod n) (j : ZMod n)
  rw [hval] at h
  have hother : ((i : ZMod n) - (j : ZMod n)).val = n - m := by omega
  unfold cycDist
  rw [hval, hother]

/-! ## Pulling a cover back to `ℤ` -/

/-- In a cover of `C_n^3` (`n ≥ 10`), integers at distance `4`, `5` or `6`
receive different labels in every layer. -/
theorem pullback_sep {n : ℕ} (hn : 10 ≤ n) (c : Fin 3 → ZMod n → ℕ)
    (hclique : ∀ s u v, u ≠ v → c s u = c s v → (cyclePower n 3).Adj u v)
    (s : Fin 3) (i j : ℤ) (h4 : 4 ≤ j - i) (h6 : j - i ≤ 6) :
    c s (i : ZMod n) ≠ c s (j : ZMod n) := by
  haveI : NeZero n := ⟨by omega⟩
  intro heq
  obtain ⟨m, hm⟩ : ∃ m : ℕ, j - i = m := ⟨(j - i).toNat, by omega⟩
  have hd := cycDist_intCast (n := n) i j m (by omega) (by omega) hm
  have hne : (i : ZMod n) ≠ (j : ZMod n) := by
    intro h
    rw [h] at hd
    simp only [cycDist, sub_self, ZMod.val_zero, min_self] at hd
    omega
  have hle := (hclique s _ _ hne heq).2
  omega

/-- In a cover of `C_n^3` (`n ≥ 10`), integers at distance `1`, `2` or `3`
share a label in some layer. -/
theorem pullback_cov {n : ℕ} (hn : 10 ≤ n) (c : Fin 3 → ZMod n → ℕ)
    (hcover : ∀ u v, (cyclePower n 3).Adj u v → ∃ s, c s u = c s v)
    (i j : ℤ) (h0 : 0 < j - i) (h3 : j - i ≤ 3) :
    ∃ s, c s (i : ZMod n) = c s (j : ZMod n) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, j - i = m := ⟨(j - i).toNat, by omega⟩
  have hd := cycDist_intCast (n := n) i j m (by omega) (by omega) hm
  have hne : (i : ZMod n) ≠ (j : ZMod n) := by
    intro h
    rw [h] at hd
    simp only [cycDist, sub_self, ZMod.val_zero, min_self] at hd
    omega
  exact hcover _ _ ⟨hne, by omega⟩

/-- The pulled-back labelling is `n`-periodic. -/
theorem pullback_periodic {n : ℕ} (c : Fin 3 → ZMod n → ℕ) (s : Fin 3) (i : ℤ) :
    c s ((i + n : ℤ) : ZMod n) = c s (i : ZMod n) := by
  push_cast
  rw [ZMod.natCast_self, add_zero]

/-! ## The argument on `ℤ` -/

/-- `[w, w+3]` lies in one class of layer `s` of the labelling `d`. -/
def Block (d : Fin 3 → ℤ → ℕ) (s : Fin 3) (w : ℤ) : Prop :=
  d s w = d s (w + 1) ∧ d s (w + 1) = d s (w + 2) ∧ d s (w + 2) = d s (w + 3)

/-- Every point of a block carries the block's label. -/
theorem Block.eq {d : Fin 3 → ℤ → ℕ} {s : Fin 3} {w : ℤ} (hB : Block d s w)
    (j : ℤ) (hj0 : 0 ≤ j) (hj3 : j ≤ 3) : d s (w + j) = d s w := by
  obtain ⟨h1, h2, h3⟩ := hB
  interval_cases j
  · rw [add_zero]
  · exact h1.symm
  · rw [← h2, ← h1]
  · rw [← h3, ← h2, ← h1]

/-- Any layer index is `s`, `s + 1` or `s + 2`. -/
theorem fin3_cases (s t : Fin 3) : t = s ∨ t = s + 1 ∨ t = s + 2 := by
  revert s t
  decide

/-- Lemma A for a labelling of `ℤ`: some layer has a block. -/
theorem exists_block (d : Fin 3 → ℤ → ℕ)
    (hsep : ∀ s (i j : ℤ), 4 ≤ j - i → j - i ≤ 6 → d s i ≠ d s j)
    (hcov : ∀ i j : ℤ, 0 < j - i → j - i ≤ 3 → ∃ s, d s i = d s j) :
    ∃ s w, Block d s w := by
  have h := lemmaA_core (d 0) (d 1) (d 2)
    (fun i j h4 h6 => ⟨hsep 0 i j h4 h6, hsep 1 i j h4 h6, hsep 2 i j h4 h6⟩)
    (fun i j h0 h3 => by
      obtain ⟨t, ht⟩ := hcov i j h0 h3
      fin_cases t
      · exact Or.inl ht
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr ht))
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨0, 0, by simpa [Block] using h⟩
  · exact ⟨0, 1, by simpa [Block] using h⟩
  · exact ⟨0, 2, by simpa [Block] using h⟩
  · exact ⟨0, 3, by simpa [Block] using h⟩
  · exact ⟨1, 0, by simpa [Block] using h⟩
  · exact ⟨1, 1, by simpa [Block] using h⟩
  · exact ⟨1, 2, by simpa [Block] using h⟩
  · exact ⟨1, 3, by simpa [Block] using h⟩
  · exact ⟨2, 0, by simpa [Block] using h⟩
  · exact ⟨2, 1, by simpa [Block] using h⟩
  · exact ⟨2, 2, by simpa [Block] using h⟩
  · exact ⟨2, 3, by simpa [Block] using h⟩

/-- Lemma B for a labelling of `ℤ`: a block at `w` forces a block at
`w + 4` in the same layer. -/
theorem Block.succ (d : Fin 3 → ℤ → ℕ)
    (hsep : ∀ s (i j : ℤ), 4 ≤ j - i → j - i ≤ 6 → d s i ≠ d s j)
    (hcov : ∀ i j : ℤ, 0 < j - i → j - i ≤ 3 → ∃ s, d s i = d s j)
    {s : Fin 3} {w : ℤ} (hB : Block d s w) : Block d s (w + 4) := by
  obtain ⟨h1, h2, h3⟩ := hB
  have h := lemmaB_core (fun i => d s (w + i)) (fun i => d (s + 1) (w + i))
    (fun i => d (s + 2) (w + i))
    (fun i j h4 h6 => ⟨hsep s (w + i) (w + j) (by omega) (by omega),
      hsep (s + 1) (w + i) (w + j) (by omega) (by omega),
      hsep (s + 2) (w + i) (w + j) (by omega) (by omega)⟩)
    (fun i j h0 h3 => by
      obtain ⟨t, ht⟩ := hcov (w + i) (w + j) (by omega) (by omega)
      rcases fin3_cases s t with rfl | rfl | rfl
      · exact Or.inl ht
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr ht))
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
  obtain ⟨g1, g2, g3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa [add_assoc] using g1
  · simpa [add_assoc] using g2
  · simpa [add_assoc] using g3

/-- Iterating Lemma B: a block at `w` gives blocks at every `w + 4m`. -/
theorem Block.add_four_mul (d : Fin 3 → ℤ → ℕ)
    (hsep : ∀ s (i j : ℤ), 4 ≤ j - i → j - i ≤ 6 → d s i ≠ d s j)
    (hcov : ∀ i j : ℤ, 0 < j - i → j - i ≤ 3 → ∃ s, d s i = d s j)
    {s : Fin 3} {w : ℤ} (hB : Block d s w) (m : ℕ) : Block d s (w + 4 * m) := by
  induction m with
  | zero => simpa using hB
  | succ m ih =>
    have hnext := Block.succ d hsep hcov ih
    have hpt : w + 4 * (m : ℤ) + 4 = w + 4 * ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [hpt] at hnext

/-- Two blocks of one layer at offsets `0 < t ≤ 3` contradict separation. -/
theorem not_block_block (d : Fin 3 → ℤ → ℕ)
    (hsep : ∀ s (i j : ℤ), 4 ≤ j - i → j - i ≤ 6 → d s i ≠ d s j)
    {s : Fin 3} {w t : ℤ} (ht0 : 0 < t) (ht3 : t ≤ 3)
    (hB : Block d s w) (hB' : Block d s (w + t)) : False := by
  have e1 : d s (w + 3) = d s w := hB.eq 3 (by norm_num) (by norm_num)
  have e2 : d s (w + t + (3 - t)) = d s (w + t) := hB'.eq (3 - t) (by omega) (by omega)
  have e3 : d s (w + t + 3) = d s (w + t) := hB'.eq 3 (by norm_num) (by norm_num)
  have hpt : w + t + (3 - t) = w + 3 := by ring
  rw [hpt] at e2
  exact hsep s w (w + t + 3) (by omega) (by omega) (by rw [e3, ← e2, e1])

/-- **Main direction (new).**  If `C_n^3` (`n ≥ 10`) is covered by three
equivalence subgraphs, then `4 ∣ n`. -/
theorem four_dvd_of_eqCoverable {n : ℕ} (hn : 10 ≤ n) (h : EqCoverable n 3 3) :
    4 ∣ n := by
  obtain ⟨c, hclique, hcover⟩ := h
  set d : Fin 3 → ℤ → ℕ := fun s i => c s (i : ZMod n) with hd
  have hsep : ∀ s (i j : ℤ), 4 ≤ j - i → j - i ≤ 6 → d s i ≠ d s j :=
    fun s i j h4 h6 => pullback_sep hn c hclique s i j h4 h6
  have hcov : ∀ i j : ℤ, 0 < j - i → j - i ≤ 3 → ∃ s, d s i = d s j :=
    fun i j h0 h3 => pullback_cov hn c hcover i j h0 h3
  have hper : ∀ s (i : ℤ), d s (i + n) = d s i :=
    fun s i => pullback_periodic c s i
  have hperB : ∀ s (x : ℤ), Block d s (x + n) → Block d s x := by
    intro s x hB
    obtain ⟨h1, h2, h3⟩ := hB
    have r1 : x + 1 + n = x + n + 1 := by ring
    have r2 : x + 2 + n = x + n + 2 := by ring
    have r3 : x + 3 + n = x + n + 3 := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [← hper s x, ← hper s (x + 1), r1]
      exact h1
    · rw [← hper s (x + 1), ← hper s (x + 2), r1, r2]
      exact h2
    · rw [← hper s (x + 2), ← hper s (x + 3), r2, r3]
      exact h3
  obtain ⟨s, w, hB⟩ := exists_block d hsep hcov
  by_contra h4
  set q := n / 4 with hq
  have hall := Block.add_four_mul d hsep hcov hB (q + 1)
  have hn4 : (n : ℤ) = 4 * q + (n % 4 : ℕ) := by
    have := Nat.div_add_mod n 4
    rw [hq]
    exact_mod_cast this.symm
  have hr1 : 1 ≤ n % 4 := by omega
  have hr3 : n % 4 ≤ 3 := by omega
  have hpt : w + 4 * ((q + 1 : ℕ) : ℤ) = (w + (4 - (n % 4 : ℕ))) + n := by
    rw [hn4]; push_cast; ring
  rw [hpt] at hall
  exact not_block_block d hsep (t := 4 - (n % 4 : ℕ)) (by omega) (by omega) hB
    (hperB s _ hall)

/-! ## The construction for `4 ∣ n` (paper, Theorem `thm:main-divisible`) -/

/-- The paper's three layers for `C_{4q}^3`: blocks `[4j, 4j+3]`, blocks
`[4j+2, 4j+5]`, and the matching `{v, v+3}` for odd `v`. -/
def stdCover (n : ℕ) : Fin 3 → ZMod n → ℕ :=
  ![fun v => v.val / 4, fun v => (v + 2).val / 4,
    fun v => if v.val % 2 = 1 then v.val else (v - 3).val]

/-- `(2 : ZMod n).val = 2` for `n > 3`. -/
theorem val_two {n : ℕ} (hn : 3 < n) : (2 : ZMod n).val = 2 := by
  have := ZMod.val_cast_of_lt (n := n) (a := 2) (by omega)
  exact_mod_cast this

/-- `(3 : ZMod n).val = 3` for `n > 3`. -/
theorem val_three {n : ℕ} (hn : 3 < n) : (3 : ZMod n).val = 3 := by
  have := ZMod.val_cast_of_lt (n := n) (a := 3) (by omega)
  exact_mod_cast this

/-- **Paper direction.**  For `4 ∣ n`, `n > 4`, the three layers of
`stdCover` cover `C_n^3`. -/
theorem eqCoverable_of_four_dvd {n : ℕ} (hn : 4 < n) (h4 : 4 ∣ n) : EqCoverable n 3 3 := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨q, rfl⟩ := h4
  -- linear facts about the values used by `stdCover`
  have hfacts : ∀ u v : ZMod (4 * q),
      u.val < 4 * q ∧ (u - v).val < 4 * q ∧ (u + 2).val < 4 * q ∧ (u - 3).val < 4 * q ∧
      ((u - v).val + v.val = u.val ∨ (u - v).val + v.val = u.val + 4 * q) ∧
      ((u + 2).val = u.val + 2 ∨ (u + 2).val + 4 * q = u.val + 2) ∧
      ((u - 3).val + 3 = u.val ∨ (u - 3).val + 3 = u.val + 4 * q) := by
    intro u v
    refine ⟨u.val_lt, (u - v).val_lt, (u + 2).val_lt, (u - 3).val_lt, ?_, ?_, ?_⟩
    · have h := val_add_cases (u - v) v
      rw [sub_add_cancel] at h
      omega
    · have h := val_add_cases u 2
      rw [val_two (by omega)] at h
      exact h
    · have h := val_add_cases (u - 3) 3
      rw [sub_add_cancel, val_three (by omega)] at h
      omega
  refine ⟨stdCover (4 * q), ?_, ?_⟩
  · intro s u v huv hc
    refine ⟨huv, ?_⟩
    have hne : u.val ≠ v.val := fun h => huv (ZMod.val_injective _ h)
    obtain ⟨hu, hu', hu'', hu''', huv1, hu2, hu3⟩ := hfacts u v
    obtain ⟨hv, hv', hv'', hv''', hvu1, hv2, hv3⟩ := hfacts v u
    unfold cycDist
    fin_cases s <;>
      simp only [stdCover, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one,
        Matrix.cons_val_zero] at hc
    · omega
    · omega
    · split_ifs at hc <;> omega
  · intro u v ⟨huv, hd⟩
    have hne : u.val ≠ v.val := fun h => huv (ZMod.val_injective _ h)
    obtain ⟨hu, hu', hu'', hu''', huv1, hu2, hu3⟩ := hfacts u v
    obtain ⟨hv, hv', hv'', hv''', hvu1, hv2, hv3⟩ := hfacts v u
    unfold cycDist at hd
    by_cases h0 : u.val / 4 = v.val / 4
    · exact ⟨0, by simpa [stdCover] using h0⟩
    by_cases h1 : (u + 2).val / 4 = (v + 2).val / 4
    · exact ⟨1, by simpa [stdCover] using h1⟩
    refine ⟨2, ?_⟩
    simp only [stdCover, Fin.isValue, Matrix.cons_val]
    split_ifs <;> omega

/-- Ground truth for the construction on `C_12^3`. -/
example : stdCover 12 0 5 = 1 ∧ stdCover 12 1 11 = 0 ∧ stdCover 12 2 4 = 1 ∧
    stdCover 12 2 1 = 1 := by decide

/-! ## Main theorems -/

/-- For `n ≥ 10`: `C_n^3` is covered by three equivalence subgraphs iff
`4 ∣ n` (the "only if" half is new; the "if" half is the paper's
construction). -/
theorem eqCoverable_three_three_iff_of_ten_le {n : ℕ} (hn : 10 ≤ n) :
    EqCoverable n 3 3 ↔ 4 ∣ n :=
  ⟨four_dvd_of_eqCoverable hn, eqCoverable_of_four_dvd (by omega)⟩

/-- **Target `cycle-power-eq3`.**  For `n ≥ 11`, `C_n^3` can be covered by
three equivalence subgraphs if and only if `4 ∣ n`; this settles the `k = 3`
instance of the case left open by Theorem `thm:exact-values` of
arXiv:2610.15635. -/
theorem eqCoverable_three_three_iff {n : ℕ} (hn : 11 ≤ n) :
    EqCoverable n 3 3 ↔ 4 ∣ n :=
  eqCoverable_three_three_iff_of_ten_le (by omega)

/-- Non-vacuity: `C_12^3` is covered by three equivalence subgraphs. -/
example : EqCoverable 12 3 3 := (eqCoverable_three_three_iff (by norm_num)).2 (by norm_num)

/-- Non-vacuity: `C_14^3` is not. -/
example : ¬ EqCoverable 14 3 3 := fun h =>
  absurd ((eqCoverable_three_three_iff (by norm_num)).1 h) (by norm_num)

end CyclePowerEquivalenceCover
