/-
# Prefix reversals: counterexample to Conjecture 4 as stated

S. A. Blanco, M. P. Golubyatnikov, E. V. Konstantinova, N. V. Maslova
and L. A. Nikiforov, *Generating the symmetric group by three prefix
reversals*, arXiv:2511.16959, Section 4.1, Conjecture 4 (`conj:km_sum`).
For `2 ≤ k < m < n`, its first clause asserts that `m+k < n` forces
`⟨r_n,r_m,r_k⟩` to be proper; the second asserts this for odd `n` when
`m+k < n-1`. Here `r_i` reverses the first `i` positions and fixes the rest.

The first clause fails: `⟨r_7,r_4,r_2⟩ = Sym_7`, although `4+2 < 7`.
This triple also appears among the paper's generating triples in Section 4.2.

Certificate: `σ = r_7 r_4 r_2` is a `7`-cycle, `r_2` is the transposition
`(1 2)`, and `7` is prime, so `Equiv.Perm.closure_prime_cycle_swap` gives
`⟨σ, r_2⟩ = Sym_7`.  Since every `r_i` is an involution and the inverse of a
`7`-cycle is a `7`-cycle, the certificate is independent of the composition
convention.

## Encoding

Positions are `Fin n` (0-indexed): `prefixRev n i` sends `x < i` to
`i - 1 - x` and fixes `x ≥ i`.  For `i > n` (outside the paper's range
`1 < i ≤ n`) it is the identity by convention; the conjecture only uses
`i ∈ {k, m, n}` with `k < m < n`, so this junk value is never reached.
-/
import Mathlib

set_option autoImplicit false

namespace PrefixReversalGeneration

open Equiv

/-- The underlying function of the prefix reversal `r_i` on `Fin n`
(0-indexed positions): `x ↦ i - 1 - x` for `x < i`, identity otherwise.
For `n < i` it is the identity (junk value outside the paper's range). -/
def prefixRevFun (n i : ℕ) (x : Fin n) : Fin n :=
  if h : (x : ℕ) < i ∧ i ≤ n then ⟨i - 1 - x, by omega⟩ else x

/-- Each prefix reversal is an involution. -/
theorem prefixRevFun_involutive (n i : ℕ) : Function.Involutive (prefixRevFun n i) := by
  intro x
  unfold prefixRevFun
  by_cases h : (x : ℕ) < i ∧ i ≤ n
  · rw [dif_pos h, dif_pos (by simp only; omega)]
    ext
    simp only
    omega
  · rw [dif_neg h, dif_neg h]

/-- The prefix reversal `r_i ∈ Sym_n` of the paper (equation (1)): reverse the
first `i` positions and fix the remaining `n - i`. -/
def prefixRev (n i : ℕ) : Perm (Fin n) :=
  Function.Involutive.toPerm (prefixRevFun n i) (prefixRevFun_involutive n i)

/-! ## Examples -/

/-- One-line notation of `r_4 ∈ Sym_7`: `[4 3 2 1 5 6 7]` (0-indexed). -/
example : (List.finRange 7).map (prefixRev 7 4) = [3, 2, 1, 0, 4, 5, 6] := by decide

/-- One-line notation of `r_7 ∈ Sym_7`: the full reversal. -/
example : (List.finRange 7).map (prefixRev 7 7) = [6, 5, 4, 3, 2, 1, 0] := by decide

/-- `r_2` is the transposition `(1 2)`. -/
example : prefixRev 7 2 = swap 0 1 := by decide

/-- The paper's identity `r_n r_{n-1} = (1 2 … n)` (right-to-left composition),
checked at `n = 5`: the `n`-cycle `x ↦ x + 1` is `finRotate`. -/
example : prefixRev 5 5 * prefixRev 5 4 = finRotate 5 := by decide

/-- `r_i = (1 i)(2 (i-1))⋯` as stated in the paper, at `i = 5`, `n = 6`. -/
example : prefixRev 6 5 = swap 0 4 * swap 1 3 := by decide

/-! ## The conjecture -/

/-- **Conjecture 4 of arXiv:2511.16959, literal statement.** For
`2 ≤ k < m < n`: if `m + k < n` then `⟨r_n, r_m, r_k⟩` is a proper subgroup of
`Sym_n`; moreover, if `n` is odd and `m + k < n - 1` then
`⟨r_n, r_m, r_k⟩ < Sym_n`.  (`n - 1` is natural subtraction with `3 ≤ n`
forced by the hypotheses, so it is the true predecessor.) -/
def Conjecture4 : Prop :=
  ∀ n m k : ℕ, 2 ≤ k → k < m → m < n →
    (m + k < n →
      Subgroup.closure ({prefixRev n n, prefixRev n m, prefixRev n k} : Set (Perm (Fin n))) < ⊤) ∧
    (Odd n → m + k < n - 1 →
      Subgroup.closure ({prefixRev n n, prefixRev n m, prefixRev n k} : Set (Perm (Fin n))) < ⊤)

/-- The certificate permutation `σ = r_7 r_4 r_2` is a cycle. -/
theorem certificate_isCycle : (prefixRev 7 7 * prefixRev 7 4 * prefixRev 7 2).IsCycle :=
  Perm.card_cycleType_eq_one.mp (by decide)

/-- The certificate permutation `σ = r_7 r_4 r_2` moves every point, so it is a
`7`-cycle. -/
theorem certificate_support :
    (prefixRev 7 7 * prefixRev 7 4 * prefixRev 7 2).support = Finset.univ := by
  decide

/-- `r_2 ∈ Sym_7` is a transposition. -/
theorem prefixRev_seven_two_isSwap : (prefixRev 7 2).IsSwap :=
  ⟨0, 1, by decide, by decide⟩

/-- **`⟨r_7, r_4, r_2⟩ = Sym_7`** (listed among the generating triples for
`n = 7` in Section 4.2 of arXiv:2511.16959). -/
theorem closure_prefixRev_seven_four_two :
    Subgroup.closure ({prefixRev 7 7, prefixRev 7 4, prefixRev 7 2} : Set (Perm (Fin 7))) = ⊤ := by
  set H := Subgroup.closure ({prefixRev 7 7, prefixRev 7 4, prefixRev 7 2} : Set (Perm (Fin 7)))
  have h7 : prefixRev 7 7 ∈ H := Subgroup.subset_closure (by simp)
  have h4 : prefixRev 7 4 ∈ H := Subgroup.subset_closure (by simp)
  have h2 : prefixRev 7 2 ∈ H := Subgroup.subset_closure (by simp)
  have hσ : prefixRev 7 7 * prefixRev 7 4 * prefixRev 7 2 ∈ H :=
    H.mul_mem (H.mul_mem h7 h4) h2
  have hprime : (Fintype.card (Fin 7)).Prime := by
    rw [Fintype.card_fin]
    norm_num
  have htop : Subgroup.closure
      ({prefixRev 7 7 * prefixRev 7 4 * prefixRev 7 2, prefixRev 7 2} : Set (Perm (Fin 7))) = ⊤ :=
    Perm.closure_prime_cycle_swap hprime certificate_isCycle certificate_support
      prefixRev_seven_two_isSwap
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact hσ
  · exact h2

/-- **The first sentence of Conjecture 4 (arXiv:2511.16959) is false.**
It is not the case that for all `2 ≤ k < m < n` with `m + k < n` the group
`⟨r_n, r_m, r_k⟩` is a proper subgroup of `Sym_n`: the triple
`(n, m, k) = (7, 4, 2)` satisfies the hypotheses and generates `Sym_7`. -/
theorem not_conjecture4_first_sentence :
    ¬ ∀ n m k : ℕ, 2 ≤ k → k < m → m < n → m + k < n →
      Subgroup.closure ({prefixRev n n, prefixRev n m, prefixRev n k} : Set (Perm (Fin n))) < ⊤ := by
  intro h
  have hlt := h 7 4 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [closure_prefixRev_seven_four_two] at hlt
  exact lt_irrefl _ hlt

/-- **Conjecture 4 of arXiv:2511.16959, as literally stated, is false**
(witness `(n, m, k) = (7, 4, 2)`). -/
theorem not_conjecture4 : ¬ Conjecture4 := fun h =>
  not_conjecture4_first_sentence fun n m k hk hkm hmn hsum => (h n m k hk hkm hmn).1 hsum

end PrefixReversalGeneration
