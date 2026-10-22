/-
# Counterexamples to Liu–Qian Conjecture 1.7 and Li–Liang Theorem A

Jiantao Li and Xinyi Liang, *Infinite Families of Counterexamples to a
Conjecture of Liu and Qian and a Refined Inverse Theorem for Restricted
Sumsets in Z_p*, arXiv:2609.10148v2: Conjecture 1.3 (Liu–Qian, FFA 116,
2026, Conjecture 1.7), Theorems 2.1, 2.3 and 3.1 (Theorem A).
Li, Li and Yuan, arXiv:2609.23343, Example 4.1, give a counterexample to
Theorem 3.1 with `(|A|,|B|) = (7,4)` in `F_13`.

The restricted sumset is `A ∔ B = {a+b : a ∈ A, b ∈ B, a ≠ b}`. The
F_13 pair below is an affine image of their exception and refutes both
Theorem A and Conjecture 1.7 below the boundary `|A|+|B| = p`. The first
boundary family (Li–Liang Theorem 2.1) is proved for every prime `p ≥ 11`.

Arithmetic conventions: "|A ∔ B| = |A| + |B| - 2" is stated subtraction-free as
`(rsum A B).card + 2 = A.card + B.card` (equivalent since |A| + |B| ≥ 9), and
"|A| + |B| ≤ p - 1" as `A.card + B.card + 1 ≤ p` (equivalent since p ≥ 2).
-/
import Mathlib

set_option autoImplicit false

namespace LiuQianRefutation

/-! ## Definitions -/

/-- Restricted sumset `A ∔ B = {a + b : a ∈ A, b ∈ B, a ≠ b}` in `ZMod p`. -/
def rsum {p : ℕ} (A B : Finset (ZMod p)) : Finset (ZMod p) :=
  ((A ×ˢ B).filter (fun x => x.1 ≠ x.2)).image (fun x => x.1 + x.2)

/-- Membership in the restricted sumset. -/
theorem mem_rsum {p : ℕ} {A B : Finset (ZMod p)} {x : ZMod p} :
    x ∈ rsum A B ↔ ∃ a ∈ A, ∃ b ∈ B, a ≠ b ∧ a + b = x := by
  simp only [rsum, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩
    exact ⟨a, ha, b, hb, hab, rfl⟩
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    exact ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩

/-- The arithmetic progression `{a, a + d, …, a + (n - 1) d}` (`n` terms) in `ZMod p`. -/
def apSet {p : ℕ} (a d : ZMod p) (n : ℕ) : Finset (ZMod p) :=
  (Finset.range n).image (fun i : ℕ => a + (i : ZMod p) * d)

/-- The Liu–Qian shape: `A` is the arithmetic progression `a, a + d, …, a + (k - 1) d`
with `d ≠ 0` and `k = |A|`, and `B` is an arithmetic progression with the same common
difference `d` consisting of the first `l = |B|` terms `a, …, a + (l - 1) d` or the last
`l` terms `a + (k - l) d, …, a + (k - 1) d` of `A`.  (The offset `k - l` is computed in
`ZMod p` after casting.) -/
def IsLQPair {p : ℕ} (A B : Finset (ZMod p)) : Prop :=
  ∃ a d : ZMod p, d ≠ 0 ∧ A = apSet a d A.card ∧
    (B = apSet a d B.card ∨
      B = apSet (a + ((A.card : ZMod p) - (B.card : ZMod p)) * d) d B.card)

/-- Liu–Qian Conjecture 1.7: for `|B| ≥ 3`, `|A| ≥ |B| + 3`, `|A| + |B| ≤ p`,
`|A ∔ B| = |A| + |B| - 2` iff `(A, B)` has the Liu–Qian shape. -/
def LiuQianConj17 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), 3 ≤ B.card → B.card + 3 ≤ A.card →
    A.card + B.card ≤ p → ((rsum A B).card + 2 = A.card + B.card ↔ IsLQPair A B)

/-- Li–Liang Theorem A (Theorem 3.1 of arXiv:2609.10148v2): the same equivalence under
`|B| ≥ 3`, `|A| ≥ |B| + 3`, `|A| + |B| ≤ p - 1`. -/
def TheoremA : Prop :=
  ∀ p : ℕ, p.Prime → ∀ A B : Finset (ZMod p), 3 ≤ B.card → B.card + 3 ≤ A.card →
    A.card + B.card + 1 ≤ p → ((rsum A B).card + 2 = A.card + B.card ↔ IsLQPair A B)

/-! ## Small examples -/

example : apSet (0 : ZMod 13) 1 3 = {0, 1, 2} := by decide

example : apSet (5 : ZMod 13) 4 3 = {5, 9, 0} := by decide

example : rsum ({0, 1, 2} : Finset (ZMod 13)) {0, 1} = {1, 2, 3} := by decide

/-- The "if" direction on a concrete instance (p = 13, A = [0,6], B = first 3 terms):
the hypotheses of Theorem A are jointly satisfiable and both sides hold. -/
example :
    let A : Finset (ZMod 13) := {0, 1, 2, 3, 4, 5, 6}
    let B : Finset (ZMod 13) := {0, 1, 2}
    3 ≤ B.card ∧ B.card + 3 ≤ A.card ∧ A.card + B.card + 1 ≤ 13 ∧
      (rsum A B).card + 2 = A.card + B.card ∧ IsLQPair A B :=
  ⟨by decide, by decide, by decide, by decide, 0, 1, by decide, by decide, Or.inl (by decide)⟩

/-- A last-terms instance of the Liu–Qian shape. -/
example : IsLQPair ({0, 1, 2, 3, 4, 5, 6} : Finset (ZMod 13)) {4, 5, 6} :=
  ⟨0, 1, by decide, by decide, Or.inr (by decide)⟩

/-- A non-critical pair: `|A ∔ B| ≠ |A| + |B| - 2`. -/
example : (rsum ({0, 1, 2, 3, 4, 6} : Finset (ZMod 13)) {0, 1, 2}).card = 8 := by decide

/-! ## The F_13 counterexample to Theorem A -/

/-- The larger set of the F_13 counterexample. -/
def A13 : Finset (ZMod 13) := {0, 1, 3, 7, 8, 9, 11}

/-- The smaller set of the F_13 counterexample. -/
def B13 : Finset (ZMod 13) := {0, 1, 3, 9}

/-- `A13` is not a 7-term arithmetic progression in `ZMod 13` (for any difference,
including `0`). -/
theorem A13_not_ap : ∀ a d : ZMod 13, apSet a d 7 ≠ A13 := by decide

/-- `B13` is not a 4-term arithmetic progression in `ZMod 13`. -/
theorem B13_not_ap : ∀ a d : ZMod 13, apSet a d 4 ≠ B13 := by decide

/-- The F_13 pair: `|A| = 7`, `|B| = 4`, `|A ∔ B| = 9 = |A| + |B| - 2`. -/
theorem counterexample13_card :
    A13.card = 7 ∧ B13.card = 4 ∧ (rsum A13 B13).card = 9 := by decide

/-- The F_13 pair does not have the Liu–Qian shape (since `A13` is not an arithmetic
progression). -/
theorem counterexample13_not_isLQPair : ¬ IsLQPair A13 B13 := by
  rintro ⟨a, d, _, hA, _⟩
  have hcard : A13.card = 7 := counterexample13_card.1
  rw [hcard] at hA
  exact A13_not_ap a d hA.symm

/-- **Theorem A of arXiv:2609.10148v2 is false.**  For p = 13, A = {0,1,3,7,8,9,11},
B = {0,1,3,9} one has |B| = 4 ≥ 3, |A| = 7 ≥ |B| + 3, |A| + |B| = 11 ≤ p - 1, and
|A ∔ B| = 9 = |A| + |B| - 2, but A is not an arithmetic progression. -/
theorem not_theoremA : ¬ TheoremA := by
  intro h
  obtain ⟨hA, hB, hS⟩ := counterexample13_card
  have hiff := h 13 (by norm_num) A13 B13 (by omega) (by omega) (by omega)
  exact counterexample13_not_isLQPair (hiff.mp (by omega))

/-- **Liu–Qian Conjecture 1.7 is false**, already strictly below the boundary
`|A| + |B| = p` (the F_13 pair has `|A| + |B| = p - 2`). -/
theorem not_liuQianConj17 : ¬ LiuQianConj17 := by
  intro h
  apply not_theoremA
  intro p hp A B hB hAB hsum
  exact h p hp A B hB hAB (by omega)

/-! ## The first boundary family (Li–Liang Theorem 2.1), every prime p ≥ 11 -/

/-- A nonzero natural number below `p` is nonzero in `ZMod p`. -/
theorem natCast_ne_zero_of_lt {p : ℕ} {n : ℕ} (h0 : 0 < n) (hn : n < p) :
    (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

/-- Small residues are nonzero in `ZMod p` once `p ≥ 11`. -/
theorem small_ne {p : ℕ} (hp : 11 ≤ p) :
    (1 : ZMod p) ≠ 0 ∧ (2 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 0 ∧ (4 : ZMod p) ≠ 0 ∧
      (5 : ZMod p) ≠ 0 ∧ (7 : ZMod p) ≠ 0 ∧ (8 : ZMod p) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
  · exact_mod_cast natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
  · exact_mod_cast natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
  · exact_mod_cast natCast_ne_zero_of_lt (p := p) (n := 4) (by norm_num) (by omega)
  · exact_mod_cast natCast_ne_zero_of_lt (p := p) (n := 5) (by norm_num) (by omega)
  · exact_mod_cast natCast_ne_zero_of_lt (p := p) (n := 7) (by norm_num) (by omega)
  · exact_mod_cast natCast_ne_zero_of_lt (p := p) (n := 8) (by norm_num) (by omega)

/-- Li–Liang Theorem 2.1, sumset identity: if `p ≥ 11` and `3c = 1` in `ZMod p`, then
`(Z_p \ {-1, -c, 2c}) ∔ {0, 1, c} = Z_p \ {0, 2c}`. -/
theorem family1_rsum {p : ℕ} [NeZero p] (hp : 11 ≤ p) (c : ZMod p) (hc : 3 * c = 1) :
    rsum ({-1, -c, 2 * c} : Finset (ZMod p))ᶜ {0, 1, c} = ({0, 2 * c} : Finset (ZMod p))ᶜ := by
  obtain ⟨h1, h2, h3, h4, h5, h7, h8⟩ := small_ne hp
  ext x
  simp only [mem_rsum, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨a, ⟨ha1, hac, ha2⟩, b, hb, hab, rfl⟩
    rcases hb with rfl | rfl | rfl
    · refine ⟨fun h => hab (by simpa using h), fun h => ha2 (by simpa using h)⟩
    · refine ⟨fun h => ha1 (by linear_combination h), fun h => hac (by linear_combination h + hc)⟩
    · refine ⟨fun h => hac (by linear_combination h), fun h => hab (by linear_combination h)⟩
  · rintro ⟨hx0, hx2⟩
    by_cases hx1 : x = -1
    · subst hx1
      refine ⟨-2, ⟨?_, ?_, ?_⟩, 1, by simp, ?_, by ring⟩
      · intro h; apply h2; linear_combination (-2) * h
      · intro h; apply h5; linear_combination hc - 3 * h
      · intro h; apply h8; linear_combination (-3) * h - 2 * hc
      · intro h; apply h3; linear_combination -h
    by_cases hxc : x = -c
    · subst hxc
      refine ⟨-c - 1, ⟨?_, ?_, ?_⟩, 1, by simp, ?_, by ring⟩
      · intro h; apply h1; linear_combination (-3) * h - hc
      · intro h; apply h1; linear_combination -h
      · intro h; apply h2; linear_combination -h - hc
      · intro h; apply h7; linear_combination (-3) * h - hc
    · exact ⟨x, ⟨hx1, hxc, hx2⟩, 0, by simp, hx0, by ring⟩

/-- Li–Liang Theorem 2.1, non-AP part: `{0, 1, c}` with `3c = 1` is not a 3-term
arithmetic progression with any nonzero difference, for a prime `p ≥ 11`. -/
theorem family1_B_not_ap {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p) (c : ZMod p) (hc : 3 * c = 1)
    (x d : ZMod p) (hd : d ≠ 0) : apSet x d 3 ≠ {0, 1, c} := by
  obtain ⟨h1, h2, h3, h4, h5, h7, h8⟩ := small_ne hp
  intro h
  have hmem : ∀ i : ℕ, i < 3 → x + (i : ZMod p) * d ∈ ({0, 1, c} : Finset (ZMod p)) := fun i hi =>
    h ▸ Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)
  have hu := hmem 0 (by norm_num)
  have hv := hmem 1 (by norm_num)
  have hw := hmem 2 (by norm_num)
  have huv : x ≠ x + d := fun e => hd (by linear_combination -e)
  have hvw : x + d ≠ x + 2 * d := fun e => hd (by linear_combination -e)
  have huw : x ≠ x + 2 * d := fun e => by
    have h2d : (2 : ZMod p) * d = 0 := by linear_combination -e
    rcases mul_eq_zero.mp h2d with h0 | h0
    · exact h2 h0
    · exact hd h0
  have hrel : x + (x + 2 * d) = 2 * (x + d) := by ring
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, add_zero, one_mul] at hu hv hw
  generalize x + 2 * d = w at *
  generalize x + d = v at *
  generalize x = u at *
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl huv
    | exact absurd rfl hvw
    | exact absurd rfl huw
    | exact h5 (by linear_combination hc - 3 * hrel)
    | exact h1 (by linear_combination 3 * hrel + 2 * hc)
    | exact h4 (by linear_combination 3 * hrel - hc)

/-- **Li–Liang Theorem 2.1 / Theorem B (boundary counterexamples to Conjecture 1.7).**
For every prime `p ≥ 11` there are `A, B ⊆ Z_p` with `|B| = 3`, `|A| = p - 3` (so
`|A| ≥ |B| + 3` and `|A| + |B| = p`), `|A ∔ B| = |A| + |B| - 2`, and `(A, B)` without the
Liu–Qian shape. -/
theorem exists_boundary_counterexample (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) :
    ∃ A B : Finset (ZMod p), B.card = 3 ∧ A.card + B.card = p ∧
      (rsum A B).card + 2 = A.card + B.card ∧ ¬ IsLQPair A B := by
  obtain ⟨h1, h2, h3, h4, h5, h7, h8⟩ := small_ne hp
  set c : ZMod p := (3 : ZMod p)⁻¹
  have hc : 3 * c = 1 := mul_inv_cancel₀ h3
  have hB : ({0, 1, c} : Finset (ZMod p)).card = 3 := by
    refine Finset.card_eq_three.mpr ⟨0, 1, c, ?_, ?_, ?_, rfl⟩
    · intro h; exact h1 (by linear_combination -h)
    · intro h; exact h1 (by linear_combination (-3) * h - hc)
    · intro h; exact h2 (by linear_combination 3 * h + hc)
  have hM : ({-1, -c, 2 * c} : Finset (ZMod p)).card = 3 := by
    refine Finset.card_eq_three.mpr ⟨-1, -c, 2 * c, ?_, ?_, ?_, rfl⟩
    · intro h; exact h2 (by linear_combination (-3) * h + hc)
    · intro h; exact h5 (by linear_combination (-3) * h - 2 * hc)
    · intro h; exact h1 (by linear_combination -h - hc)
  have hZ : ({0, 2 * c} : Finset (ZMod p)).card = 2 := by
    refine Finset.card_eq_two.mpr ⟨0, 2 * c, ?_, rfl⟩
    intro h; exact h2 (by linear_combination (-3) * h - 2 * hc)
  have hA : ({-1, -c, 2 * c} : Finset (ZMod p))ᶜ.card = p - 3 := by
    rw [Finset.card_compl, ZMod.card, hM]
  have hS : (rsum ({-1, -c, 2 * c} : Finset (ZMod p))ᶜ {0, 1, c}).card = p - 2 := by
    rw [family1_rsum hp c hc, Finset.card_compl, ZMod.card, hZ]
  refine ⟨({-1, -c, 2 * c} : Finset (ZMod p))ᶜ, {0, 1, c}, hB, ?_, ?_, ?_⟩
  · rw [hA, hB]; omega
  · rw [hA, hB, hS]; omega
  · rintro ⟨a, d, hd, _, hBap⟩
    rw [hB] at hBap
    rcases hBap with hBap | hBap
    · exact family1_B_not_ap hp c hc a d hd hBap.symm
    · exact family1_B_not_ap hp c hc _ d hd hBap.symm

end LiuQianRefutation
