import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E124

/-- `PowSumSet d k`: integers of the form `∑_{i ∈ S} d^i` over finite
    index sets `S` with all exponents `≥ k` — the `P(d, k)` of the
    problem.  `0` (empty `S`) is included, which harmlessly absorbs
    the `c_i ∈ {0,1}` choice: `c_i = 0` ⟺ pick `a_i = 0`. -/
def PowSumSet (d k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ S : Finset ℕ, (∀ i ∈ S, k ≤ i) ∧ m = ∑ i ∈ S, d ^ i}

/-- `CompleteFor ds k`: all sufficiently large integers are sums
    `∑ a_i` with `a_i ∈ P(d_i, k)` (one term per base, zeros
    allowed = the `c_i ∈ {0,1}` form). -/
def CompleteFor (ds : List ℕ) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ f : ℕ → ℕ, (∀ j < ds.length, f j ∈ PowSumSet (ds.getD j 0) k) ∧
      n = ∑ j ∈ Finset.range ds.length, f j

example : (0 : ℕ) ∈ PowSumSet 3 1 := by
  exact ⟨∅, by simp, by simp⟩

example : ¬ CompleteFor [] 0 := by
  rintro ⟨N, hN⟩
  obtain ⟨f, hf, heq⟩ := hN (N + 1) (by omega)
  simp only [List.length_nil, Finset.range_zero, Finset.sum_empty] at heq
  omega

/-- A strictly increasing natural sequence starting at `1`, whose every next
term is at most one plus the sum of all earlier terms, represents every natural
number as a sum over a finite set of indices. The bound is global, not eventual. -/
theorem partial_sum_completeness (a : ℕ → ℕ) (ha : StrictMono a)
    (h1 : ∀ m : ℕ, a (m + 1) ≤ 1 + ∑ j ∈ Finset.range (m + 1), a j)
    (h0 : a 0 = 1) :
    ∀ n : ℕ, ∃ S : Finset ℕ, n = ∑ i ∈ S, a i := by
  have hcap (m : ℕ) : a m ≤ (∑ j ∈ Finset.range m, a j) + 1 := by
    cases m with
    | zero => simp [h0]
    | succ k => simpa [Nat.add_comm] using h1 k
  have hrep (m : ℕ) : ∀ n : ℕ, n ≤ ∑ j ∈ Finset.range m, a j →
      ∃ S : Finset ℕ, S ⊆ Finset.range m ∧ n = ∑ i ∈ S, a i := by
    induction m with
    | zero =>
      intro n hn
      simp only [Finset.range_zero, Finset.sum_empty] at hn
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      simp only [Finset.sum_empty]
      omega
    | succ m ih =>
      intro n hn
      rw [Finset.sum_range_succ] at hn
      by_cases hsmall : n ≤ ∑ j ∈ Finset.range m, a j
      · obtain ⟨S, hS, heq⟩ := ih n hsmall
        exact ⟨S, hS.trans (Finset.range_mono (by omega)), heq⟩
      · have ham : a m ≤ n := by
          have hc := hcap m
          omega
        have hres : n - a m ≤ ∑ j ∈ Finset.range m, a j := by omega
        obtain ⟨S, hS, heq⟩ := ih (n - a m) hres
        have hnot : m ∉ S := by
          intro hm
          have hlt := Finset.mem_range.mp (hS hm)
          omega
        refine ⟨insert m S, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_range.mpr (by omega)
          · exact Finset.range_mono (by omega) (hS hi)
        · rw [Finset.sum_insert hnot, ← heq]
          omega
  have hpos (i : ℕ) : 1 ≤ a i := by
    rw [← h0]
    exact ha.monotone (Nat.zero_le i)
  have hsum (m : ℕ) : m ≤ ∑ j ∈ Finset.range m, a j := by
    calc
      m = ∑ _j ∈ Finset.range m, (1 : ℕ) := by simp
      _ ≤ ∑ j ∈ Finset.range m, a j := Finset.sum_le_sum (fun i _hi => hpos i)
  intro n
  obtain ⟨S, _hS, heq⟩ := hrep n n (hsum n)
  exact ⟨S, heq⟩

example : StrictMono (fun i : ℕ => i + 1) ∧
    (∀ m : ℕ, (m + 1) + 1 ≤ 1 + ∑ j ∈ Finset.range (m + 1), (j + 1)) ∧
    (0 : ℕ) + 1 = 1 := by
  refine ⟨by intro i j hij; dsimp only; omega, ?_, rfl⟩
  intro m
  rw [Finset.sum_range_succ]
  omega

end ErdosCandidates.E124
