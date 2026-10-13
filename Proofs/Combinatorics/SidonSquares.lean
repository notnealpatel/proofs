import Combinatorics.Sidon

set_option autoImplicit false

namespace SidonSquares

open Sidon (IsSidon)

/-- The first `n` positive perfect squares, `{1², 2², …, n²}`. -/
def squares (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).image (fun k => k ^ 2)

example : squares 0 = ∅ := by decide
example : squares 3 = {1, 4, 9} := by decide

/-- The largest cardinality of a Sidon subset of the first `n` positive squares. -/
noncomputable def a390813 (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S ⊆ squares n, IsSidon S ∧ S.card = k}

/-- The achievable cardinalities form a nonempty set, even at `n=0`. -/
theorem a390813_set_nonempty (n : ℕ) :
    {k : ℕ | ∃ S ⊆ squares n, IsSidon S ∧ S.card = k}.Nonempty := by
  exact ⟨0, ∅, Finset.empty_subset _, Sidon.isSidon_empty, rfl⟩

/-- There are at most `n` squares among the first `n` positive squares. -/
theorem card_squares_le (n : ℕ) : (squares n).card ≤ n := by
  calc
    (squares n).card ≤ (Finset.Icc 1 n).card := Finset.card_image_le
    _ ≤ n := by simp

/-- Achievable Sidon cardinalities are bounded by the ambient cardinality. -/
theorem a390813_bddAbove (n : ℕ) :
    BddAbove {k : ℕ | ∃ S ⊆ squares n, IsSidon S ∧ S.card = k} := by
  refine ⟨n, ?_⟩
  rintro k ⟨S, hS, _, rfl⟩
  exact (Finset.card_le_card hS).trans (card_squares_le n)

/-- The supremum defining the sequence is attained by a Sidon subset. -/
theorem a390813_attained (n : ℕ) :
    ∃ S ⊆ squares n, IsSidon S ∧ S.card = a390813 n :=
  Nat.sSup_mem (a390813_set_nonempty n) (a390813_bddAbove n)

/-- The trivial ambient upper bound is valid also at `n=0`. -/
theorem a390813_le (n : ℕ) : a390813 n ≤ n := by
  obtain ⟨S, hS, _, hcard⟩ := a390813_attained n
  rw [← hcard]
  exact (Finset.card_le_card hS).trans (card_squares_le n)

example : a390813 0 = 0 := Nat.eq_zero_of_le_zero (a390813_le 0)

/-- The OEIS sorted-sum formulation is exactly the general Sidon predicate. -/
theorem isSidon_iff_sums_distinct (S : Finset ℕ) :
    IsSidon S ↔ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d :=
  Sidon.isSidon_iff_sums_distinct S

example : IsSidon (squares 6) := by decide
example : ¬ IsSidon (squares 7) := by decide
example : IsSidon ({1, 4, 9, 16, 36, 49} : Finset ℕ) := by decide

/-- Every exhibited Sidon subset gives a lower bound for the maximum. -/
theorem card_le_a390813 {n : ℕ} {S : Finset ℕ} (hS : S ⊆ squares n)
    (h : IsSidon S) : S.card ≤ a390813 n :=
  le_csSup (a390813_bddAbove n) ⟨S, hS, h, rfl⟩

/-- The first six squares are all Sidon, so the maximum is six. -/
theorem a390813_six : a390813 6 = 6 := by
  have hw : IsSidon (squares 6) := by decide
  have hc : (squares 6).card = 6 := by decide
  apply Nat.le_antisymm (a390813_le 6)
  simpa [hc] using card_le_a390813 (Finset.Subset.refl _) hw

/-- A collision rules out all seven squares, while a six-square witness works. -/
theorem a390813_seven : a390813 7 = 6 := by
  apply Nat.le_antisymm
  · obtain ⟨S, hS, hsidon, hcard⟩ := a390813_attained 7
    have hseven : (squares 7).card = 7 := by decide
    have hnot : ¬ IsSidon (squares 7) := by decide
    have hne : a390813 7 ≠ 7 := by
      intro heq
      have heqS : S = squares 7 := Finset.eq_of_subset_of_card_le hS (by omega)
      exact hnot (heqS ▸ hsidon)
    have hle := a390813_le 7
    omega
  · let S : Finset ℕ := {1, 4, 9, 16, 36, 49}
    have hS : S ⊆ squares 7 := by decide
    have hw : IsSidon S := by decide
    have hc : S.card = 6 := by decide
    simpa [hc] using card_le_a390813 hS hw

end SidonSquares
