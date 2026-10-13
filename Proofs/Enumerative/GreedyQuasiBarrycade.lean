import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Greedy infinite quasi-barrycade: model and uniqueness

Primary source: arXiv:2609.18476, definition and greedy construction
(lines 202–220), and Appendix Algorithm `alvarrho` (lines 548–570).
This module specifies complete infinite rows, not finite approximations of
forbidden partial sums. It does not yet certify the explicit fifth row.

`table r n` represents the paper's entry `ρ_{r+1}(n+1)`.
`partialSum row n` is the sum of the first `n` entries, including the empty
sum at `n = 0`; only positive lengths are forbidden in earlier rows.
-/

set_option autoImplicit false

namespace GreedyQuasiBarrycade

/-- An infinite row with zero-based entry indices and natural-number values.
Positivity is imposed by admissibility, rather than by the ambient type. -/
abbrev Row := ℕ → ℕ

/-- An infinite table with zero-based row indices. -/
abbrev Table := ℕ → Row

/-- Sum of the first `n` entries of a row; length zero gives the empty sum. -/
def partialSum (row : Row) (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range n, row m

example : partialSum (fun n => n + 1) 0 = 0 := rfl
example : partialSum (fun n => n + 1) 3 = 6 := by decide
example : Row = (ℕ → ℕ) := rfl
example : Table = (ℕ → ℕ → ℕ) := rfl

/-- A candidate is positive, unused in the current prefix, and its new sum
avoids every positive-length partial sum of every complete earlier row. -/
def Admissible (table : Table) (r n a : ℕ) : Prop :=
  0 < a ∧
  (∀ m, m < n → table r m ≠ a) ∧
  ∀ i, i < r → ∀ k, 0 < k →
    partialSum (table i) k ≠ partialSum (table r) n + a

/-- The first `R` complete infinite rows obey the least-admissible rule at
every entry. Rows with indices at least `R` are unconstrained. -/
def GreedyPrefix (R : ℕ) (table : Table) : Prop :=
  ∀ r, r < R → ∀ n,
    Admissible table r n (table r n) ∧
    ∀ b, Admissible table r n b → table r n ≤ b

example : Admissible (fun _ n => n + 1) 0 0 1 := by
  simp [Admissible]

example (table : Table) : GreedyPrefix 0 table := by
  simp [GreedyPrefix]

/-- A nonempty concrete greedy prefix: the first row is `1, 2, 3, …`.
This witnesses jointly the positivity, unusedness, and least-choice hypotheses. -/
theorem increasing_first_row : GreedyPrefix 1 (fun _ n => n + 1) := by
  intro r hr n
  have hr0 : r = 0 := by omega
  subst r
  dsimp only [Admissible]
  constructor
  · refine ⟨by omega, ?_, ?_⟩
    · intro m hm heq
      omega
    · intro i hi
      omega
  · intro b hb
    by_contra hnot
    have hbpos : 0 < b := hb.1
    have hm : b - 1 < n := by omega
    have hunused := hb.2.1 (b - 1) hm
    have heq : b - 1 + 1 = b := by omega
    exact hunused heq

private theorem partialSum_eq_of_prefix_eq (row₁ row₂ : Row) (n : ℕ)
    (h : ∀ m, m < n → row₁ m = row₂ m) :
    partialSum row₁ n = partialSum row₂ n := by
  apply Finset.sum_congr rfl
  intro m hm
  exact h m (Finset.mem_range.mp hm)

/-- Admissibility depends only on the current prefix and complete earlier rows.
In particular the earlier-row comparison retains its unbounded length index. -/
theorem admissible_iff_of_agree (table₁ table₂ : Table) (r n a : ℕ)
    (hearlier : ∀ i, i < r → table₁ i = table₂ i)
    (hprefix : ∀ m, m < n → table₁ r m = table₂ r m) :
    Admissible table₁ r n a ↔ Admissible table₂ r n a := by
  have hsum : partialSum (table₁ r) n = partialSum (table₂ r) n :=
    partialSum_eq_of_prefix_eq _ _ n hprefix
  have hused : (∀ m, m < n → table₁ r m ≠ a) ↔
      (∀ m, m < n → table₂ r m ≠ a) := by
    constructor
    · intro h m hm
      rw [← hprefix m hm]
      exact h m hm
    · intro h m hm
      rw [hprefix m hm]
      exact h m hm
  unfold Admissible
  rw [hused, hsum]
  constructor
  · rintro ⟨hpos, hunused, havoid⟩
    refine ⟨hpos, hunused, ?_⟩
    intro i hi k hk
    rw [← hearlier i hi]
    exact havoid i hi k hk
  · rintro ⟨hpos, hunused, havoid⟩
    refine ⟨hpos, hunused, ?_⟩
    intro i hi k hk
    rw [hearlier i hi]
    exact havoid i hi k hk

/-- Any two tables obeying the greedy rule on their first `R` complete rows
have identical rows there. No global existence assumption is needed. -/
theorem greedyPrefix_unique (R : ℕ) (table₁ table₂ : Table)
    (h₁ : GreedyPrefix R table₁) (h₂ : GreedyPrefix R table₂) :
    ∀ r, r < R → table₁ r = table₂ r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    have hearlier : ∀ i, i < r → table₁ i = table₂ i := by
      intro i hi
      exact ih i hi (Nat.lt_trans hi hr)
    funext n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      have htransfer (a : ℕ) :
          Admissible table₁ r n a ↔ Admissible table₂ r n a :=
        admissible_iff_of_agree table₁ table₂ r n a hearlier ihn
      have hchoice₁ := h₁ r hr n
      have hchoice₂ := h₂ r hr n
      have hle₁ : table₁ r n ≤ table₂ r n :=
        hchoice₁.2 _ ((htransfer _).mpr hchoice₂.1)
      have hle₂ : table₂ r n ≤ table₁ r n :=
        hchoice₂.2 _ ((htransfer _).mp hchoice₁.1)
      exact Nat.le_antisymm hle₁ hle₂

example : ∃ table : Table, GreedyPrefix 1 table :=
  ⟨fun _ n => n + 1, increasing_first_row⟩

end GreedyQuasiBarrycade
