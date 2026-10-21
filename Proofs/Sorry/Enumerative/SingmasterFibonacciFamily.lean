/-
# Singmaster's Fibonacci family: infinitely many numbers occur at least
# six times in Pascal's triangle

## Source (pulled 2026-10-21)

MathOverflow question 100265, "Not especially famous, long-open problems
which anyone can understand" (asked by David Feldman), answer 101093 by
Michael Hardy (2012-07-01), https://mathoverflow.net/a/101093.  Verbatim:

```
Singmaster's conjecture says there is a finite upper bound on the number
of times a number (other than the 1s on the edge) can appear in Pascal's
triangle. [...] It has been proved that infinitely many numbers appear
twice; similarly three times, four times, and six times.
```

The six-fold claim is Singmaster's theorem: D. Singmaster, "Repeated
binomial coefficients and Fibonacci numbers", Fibonacci Quart. 13 (1975),
295--298.  Writing `F` for the Fibonacci numbers, for every `i ≥ 1`
with `N = F(2i+2) F(2i+3)` and `K = F(2i) F(2i+3)` one has
`C(N, K) = C(N - 1, K + 1)`; for `i = 1` this is `C(15,5) = C(14,6) = 3003`.
The value `a = C(N, K)` then occurs at the six positions
`(N,K), (N,N-K), (N-1,K+1), (N-1,N-2-K), (a,1), (a,a-1)`.
No arXiv paper is involved.

## Status

Proved in the literature (Singmaster 1975); the thread states it as known.
Singmaster's conjecture itself (an absolute bound) remains open and is not
formalized here.  "Appear six times" is formalized as "at least six times":
it is not known that these values occur exactly six times.

## Counting conventions

* `solutions a` follows google-deepmind formal-conjectures
  `Wikipedia/Singmaster.lean`: pairs `(n, k)` with `1 ≤ k < n` and
  `C(n, k) = a` (the edge `1`s are excluded).
* `halfSolutions a` follows `Proofs/Sorry/Erdos/E849.lean`
  (`ErdosCandidates.E849.solutions`): pairs with `1 ≤ k` and `2k ≤ n`.

Mathlib inventory (leandoc): `Nat.choose`, `Nat.fib`; no binomial
repetition or Singmaster result exists in Mathlib.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.SingmasterFibonacciFamily

/-! ## Definitions -/

/-- Positions of `a` in Pascal's triangle off the edge: pairs `(n, k)` with
`1 ≤ k < n` and `C(n, k) = a` (formal-conjectures `Singmaster.solutions`). -/
def solutions (a : ℕ) : Set (ℕ × ℕ) :=
  {q | 1 ≤ q.2 ∧ q.2 < q.1 ∧ q.1.choose q.2 = a}

/-- Half-triangle positions of `a`: pairs `(n, k)` with `1 ≤ k`, `2k ≤ n` and
`C(n, k) = a` (the convention of Erdős problem 849). -/
def halfSolutions (a : ℕ) : Set (ℕ × ℕ) :=
  {q | 1 ≤ q.2 ∧ 2 * q.2 ≤ q.1 ∧ q.1.choose q.2 = a}

/-! Ground truth: `3003 = C(15,5) = C(14,6)` lies in both solution sets. -/

example : (15, 5) ∈ solutions 3003 := ⟨by norm_num, by norm_num, by decide⟩
example : (14, 8) ∈ solutions 3003 := ⟨by norm_num, by norm_num, by decide⟩
example : (14, 6) ∈ halfSolutions 3003 := ⟨by norm_num, by norm_num, by decide⟩
example : (6, 2) ∉ solutions 3003 := fun h => by
  have h3 : Nat.choose 6 2 = 3003 := h.2.2
  revert h3
  decide
example : (4, 4) ∉ solutions 1 := fun h => absurd h.2.1 (lt_irrefl 4)

/-! ## Binomial lemmas -/

/-- Off the edge, a binomial coefficient is at least its row index:
`n ≤ C(n, k)` for `1 ≤ k < n`. -/
theorem le_choose_of_one_le_of_lt {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rcases Nat.lt_or_ge (j + 1) m with hlt | hge
    · have hrec : m ≤ m.choose (j + 1) := ih (by omega) hlt
      have hpos : 0 < m.choose j := Nat.choose_pos (by omega)
      rw [Nat.choose_succ_succ']
      omega
    · have hjm : j + 1 = m := by omega
      rw [hjm, Nat.choose_succ_self_right]

/-- The solution set of `C(n, k) = a` with `1 ≤ k < n` is finite: every
solution has `k < n ≤ a`. -/
theorem solutions_finite (a : ℕ) : (solutions a).Finite := by
  refine (Finset.finite_toSet (Finset.range (a + 1) ×ˢ Finset.range (a + 1))).subset ?_
  rintro ⟨n, k⟩ ⟨hk, hkn, hc⟩
  have hle : n ≤ a := hc ▸ le_choose_of_one_le_of_lt hk hkn
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  omega

/-- Half-triangle solutions are solutions. -/
theorem halfSolutions_subset_solutions (a : ℕ) : halfSolutions a ⊆ solutions a :=
  fun _ ⟨hk, hkn, hc⟩ => ⟨hk, by omega, hc⟩

/-- Adjacent-row criterion: if `(K+L+1)(K+1) = (L+1)L` then
`C(K+L+1, K) = C(K+L, K+1)`. -/
theorem choose_eq_choose_of_mul_eq (K L : ℕ) (h : (K + L + 1) * (K + 1) = (L + 1) * L) :
    (K + L + 1).choose K = (K + L).choose (K + 1) := by
  have h1 : (K + L).choose K * (K + L + 1) = (K + L + 1).choose K * (L + 1) := by
    have hc := Nat.choose_mul_succ_eq (K + L) K
    rwa [show K + L + 1 - K = L + 1 by omega] at hc
  have h2 : (K + L).choose (K + 1) * (K + 1) = (K + L).choose K * L := by
    have hc := Nat.choose_succ_right_eq (K + L) K
    rwa [show K + L - K = L by omega] at hc
  have hpos : 0 < (L + 1) * (K + 1) := Nat.mul_pos (Nat.succ_pos L) (Nat.succ_pos K)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (K + L + 1).choose K * ((L + 1) * (K + 1))
      = (K + L).choose K * ((K + L + 1) * (K + 1)) := by rw [← mul_assoc, ← h1]; ring
    _ = (K + L).choose K * L * (L + 1) := by rw [h]; ring
    _ = (K + L).choose (K + 1) * ((L + 1) * (K + 1)) := by rw [← h2]; ring

/-! ## Fibonacci lemmas -/

/-- Cassini's identity at odd index, over `ℕ`:
`F(2n) F(2n+2) + 1 = F(2n+1)^2`. -/
theorem fib_two_mul_mul_fib_two_mul_add_two_add_one (n : ℕ) :
    Nat.fib (2 * n) * Nat.fib (2 * n + 2) + 1 = Nat.fib (2 * n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have e2 : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
    have e3 : Nat.fib (2 * m + 3) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := Nat.fib_add_two
    have e4 : Nat.fib (2 * m + 4) = Nat.fib (2 * m + 2) + Nat.fib (2 * m + 3) := Nat.fib_add_two
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, show 2 * m + 2 + 2 = 2 * m + 4 by ring,
      show 2 * m + 2 + 1 = 2 * m + 3 by ring, e4, e3, e2]
    rw [e2] at ih
    nlinarith [ih]

/-- **Singmaster's identity (1975).** With `N = F(2i+2) F(2i+3)` and
`K = F(2i) F(2i+3)`, `C(N, K) = C(N - 1, K + 1)`.  The identity holds for every
`i` (at `i = 0` it reads `C(2,0) = C(1,1)`); it is nontrivial for `i ≥ 1`,
e.g. `C(15,5) = C(14,6)` at `i = 1`.  Here `1 ≤ N`, so `N - 1` is honest. -/
theorem choose_fib_eq_choose_fib (i : ℕ) :
    (Nat.fib (2 * i + 2) * Nat.fib (2 * i + 3)).choose (Nat.fib (2 * i) * Nat.fib (2 * i + 3)) =
      (Nat.fib (2 * i + 2) * Nat.fib (2 * i + 3) - 1).choose
        (Nat.fib (2 * i) * Nat.fib (2 * i + 3) + 1) := by
  set a := Nat.fib (2 * i) with ha
  set b := Nat.fib (2 * i + 1) with hb
  set c := Nat.fib (2 * i + 2) with hc
  set d := Nat.fib (2 * i + 3) with hd
  have hcab : c = a + b := Nat.fib_add_two
  have hdbc : d = b + c := Nat.fib_add_two
  have hcas : a * c + 1 = b ^ 2 := fib_two_mul_mul_fib_two_mul_add_two_add_one i
  have hbpos : 0 < b := Nat.fib_pos.mpr (by omega)
  have hdpos : 0 < d := by omega
  obtain ⟨L, hL⟩ : ∃ L, b * d = L + 1 := ⟨b * d - 1, by have := Nat.mul_pos hbpos hdpos; omega⟩
  have hN : c * d = a * d + L + 1 := by rw [hcab, add_mul, hL]; ring
  have hkey : (a * d + L + 1) * (a * d + 1) = (L + 1) * L := by
    -- `c d (a d + 1) + b d = (b d)^2` reduces to Cassini `a c + 1 = b^2`.
    have hcd : c * d * (a * d + 1) + b * d = (b * d) ^ 2 := by
      have e : c * d * (a * d + 1) + b * d = d * d * (a * c + 1) := by rw [hdbc]; ring
      rw [e, hcas]; ring
    rw [← hN]
    rw [hL] at hcd
    nlinarith [hcd]
  rw [hN, show a * d + L + 1 - 1 = a * d + L by omega]
  exact choose_eq_choose_of_mul_eq (a * d) L hkey

/-- Ground truth: the case `i = 1` is `C(15,5) = C(14,6)`. -/
example : (Nat.fib 4 * Nat.fib 5, Nat.fib 2 * Nat.fib 5) = (15, 5) := by decide

/-! ## Counting the repetitions -/

/-- If `a = C(N, K)` with `2 ≤ K` and `2K + 4 ≤ N`, then `N < a`
(`C(N, K) = C(N-1, K-1) + C(N-1, K) ≥ 2 (N - 1)`). -/
theorem lt_choose_of_two_le {N K : ℕ} (hK : 2 ≤ K) (hN : 2 * K + 4 ≤ N) :
    N < N.choose K := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
  have h1 : M ≤ M.choose j := le_choose_of_one_le_of_lt (by omega) (by omega)
  have h2 : M ≤ M.choose (j + 1) := le_choose_of_one_le_of_lt (by omega) (by omega)
  rw [Nat.choose_succ_succ']
  omega

/-- Six-fold repetition from an adjacent-row coincidence: if `2 ≤ K`,
`2K + 4 ≤ N` and `C(N, K) = C(N-1, K+1)`, then `a = C(N, K)` has at least six
positions `(n, k)` with `1 ≤ k < n`, namely `(N,K)`, `(N,N-K)`, `(N-1,K+1)`,
`(N-1,N-2-K)`, `(a,1)`, `(a,a-1)`. -/
theorem six_le_ncard_solutions_of_choose_eq {N K : ℕ} (hK : 2 ≤ K) (hN : 2 * K + 4 ≤ N)
    (heq : N.choose K = (N - 1).choose (K + 1)) : 6 ≤ (solutions (N.choose K)).ncard := by
  have hlt : N < N.choose K := lt_choose_of_two_le hK hN
  set a := N.choose K with ha
  let L : List (ℕ × ℕ) :=
    [(N, K), (N, N - K), (N - 1, K + 1), (N - 1, N - 1 - (K + 1)), (a, 1), (a, a - 1)]
  have hnodup : L.Nodup := by
    simp only [L, List.nodup_cons, List.mem_cons, List.not_mem_nil, Prod.mk.injEq,
      List.nodup_nil, or_false, not_or, not_and, true_implies, not_false_eq_true, and_true]
    omega
  have hcard : L.toFinset.card = 6 := List.toFinset_card_of_nodup hnodup
  have hsub : (↑L.toFinset : Set (ℕ × ℕ)) ⊆ solutions a := by
    intro q hq
    simp only [L, List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_ofPred_eq] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, by omega, rfl⟩
    · exact ⟨by omega, by omega, Nat.choose_symm (by omega)⟩
    · exact ⟨by omega, by omega, heq.symm⟩
    · exact ⟨by omega, by omega, (Nat.choose_symm (by omega)).trans heq.symm⟩
    · exact ⟨le_rfl, by omega, Nat.choose_one_right a⟩
    · exact ⟨by omega, by omega,
        (Nat.choose_symm (by omega : 1 ≤ a)).trans (Nat.choose_one_right a)⟩
  calc 6 = (↑L.toFinset : Set (ℕ × ℕ)).ncard := by rw [Set.ncard_coe_finset, hcard]
    _ ≤ (solutions a).ncard := Set.ncard_le_ncard hsub (solutions_finite a)

/-- Three-fold half-triangle repetition from an adjacent-row coincidence: under
the same hypotheses, `a = C(N, K)` has the half-triangle positions `(N,K)`,
`(N-1,K+1)`, `(a,1)`. -/
theorem three_le_ncard_halfSolutions_of_choose_eq {N K : ℕ} (hK : 2 ≤ K)
    (hN : 2 * K + 4 ≤ N) (heq : N.choose K = (N - 1).choose (K + 1)) :
    3 ≤ (halfSolutions (N.choose K)).ncard := by
  have hlt : N < N.choose K := lt_choose_of_two_le hK hN
  set a := N.choose K with ha
  let L : List (ℕ × ℕ) := [(N, K), (N - 1, K + 1), (a, 1)]
  have hnodup : L.Nodup := by
    simp only [L, List.nodup_cons, List.mem_cons, List.not_mem_nil, Prod.mk.injEq,
      List.nodup_nil, or_false, not_or, not_and, not_false_eq_true, and_true]
    omega
  have hcard : L.toFinset.card = 3 := List.toFinset_card_of_nodup hnodup
  have hsub : (↑L.toFinset : Set (ℕ × ℕ)) ⊆ halfSolutions a := by
    intro q hq
    simp only [L, List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_ofPred_eq] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨by omega, by omega, rfl⟩
    · exact ⟨by omega, by omega, heq.symm⟩
    · exact ⟨le_rfl, by omega, Nat.choose_one_right a⟩
  have hfin : (halfSolutions a).Finite :=
    (solutions_finite a).subset (halfSolutions_subset_solutions a)
  calc 3 = (↑L.toFinset : Set (ℕ × ℕ)).ncard := by rw [Set.ncard_coe_finset, hcard]
    _ ≤ (halfSolutions a).ncard := Set.ncard_le_ncard hsub hfin

/-- Size facts for Singmaster's family at `i ≥ 1`: with `N = F(2i+2) F(2i+3)`
and `K = F(2i) F(2i+3)`, `2 ≤ K`, `2K + 4 ≤ N` and `2i + 2 ≤ N`. -/
theorem fib_family_bounds (i : ℕ) (hi : 1 ≤ i) :
    2 ≤ Nat.fib (2 * i) * Nat.fib (2 * i + 3) ∧
      2 * (Nat.fib (2 * i) * Nat.fib (2 * i + 3)) + 4 ≤
        Nat.fib (2 * i + 2) * Nat.fib (2 * i + 3) ∧
      2 * i + 2 ≤ Nat.fib (2 * i + 2) * Nat.fib (2 * i + 3) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have e1 : Nat.fib (2 * (j + 1)) = Nat.fib (2 * j) + Nat.fib (2 * j + 1) := by
    rw [show 2 * (j + 1) = 2 * j + 2 by ring]; exact Nat.fib_add_two
  have e2 : Nat.fib (2 * (j + 1) + 1) = Nat.fib (2 * j + 1) + Nat.fib (2 * (j + 1)) := by
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    exact Nat.fib_add_two
  have e3 : Nat.fib (2 * (j + 1) + 2) = Nat.fib (2 * (j + 1)) + Nat.fib (2 * (j + 1) + 1) :=
    Nat.fib_add_two
  have hodd : 1 ≤ Nat.fib (2 * j + 1) := Nat.fib_pos.mpr (by omega)
  have hd5 : 5 ≤ Nat.fib (2 * (j + 1) + 3) := by
    have hmono : Nat.fib 5 ≤ Nat.fib (2 * (j + 1) + 3) := Nat.fib_mono (by omega)
    have h5 : Nat.fib 5 = 5 := by decide
    omega
  have hdi : 2 * (j + 1) + 2 ≤ Nat.fib (2 * (j + 1) + 3) := by
    have := Nat.le_fib_add_one (2 * (j + 1) + 3)
    omega
  set a := Nat.fib (2 * (j + 1))
  set b := Nat.fib (2 * (j + 1) + 1)
  set c := Nat.fib (2 * (j + 1) + 2)
  set d := Nat.fib (2 * (j + 1) + 3)
  have ha1 : 1 ≤ a := by omega
  have hba : a + 1 ≤ b := by omega
  have hc : c = a + b := e3
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · have hN : c * d = 2 * (a * d) + (b - a) * d := by
      rw [hc]; zify [(by omega : a ≤ b)]; ring
    have hbd : d ≤ (b - a) * d := Nat.le_mul_of_pos_left d (by omega)
    omega
  · have hcd : d ≤ c * d := Nat.le_mul_of_pos_left d (by omega)
    omega

/-- **Singmaster's six-fold repetition (1975).** For every `i ≥ 1`, the value
`a = C(F(2i+2) F(2i+3), F(2i) F(2i+3))` occurs at least six times in Pascal's
triangle off the edge: `6 ≤ #{(n, k) | 1 ≤ k < n, C(n, k) = a}`. -/
theorem six_le_ncard_solutions_fib (i : ℕ) (hi : 1 ≤ i) :
    6 ≤ (solutions ((Nat.fib (2 * i + 2) * Nat.fib (2 * i + 3)).choose
      (Nat.fib (2 * i) * Nat.fib (2 * i + 3)))).ncard := by
  obtain ⟨hK, hN, -⟩ := fib_family_bounds i hi
  exact six_le_ncard_solutions_of_choose_eq hK hN (choose_fib_eq_choose_fib i)

/-- **Singmaster's theorem (1975), MathOverflow answer 101093.** Infinitely many
numbers occur at least six times in Pascal's triangle: the set of `a` with at
least six positions `(n, k)`, `1 ≤ k < n`, `C(n, k) = a`, is infinite. -/
theorem infinite_setOf_six_le_ncard_solutions :
    {a : ℕ | 6 ≤ (solutions a).ncard}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun B => ?_
  obtain ⟨hK, hN, hNi⟩ := fib_family_bounds (B + 1) (by omega)
  refine ⟨_, six_le_ncard_solutions_fib (B + 1) (by omega), ?_⟩
  have hlt := lt_choose_of_two_le hK hN
  omega

/-- Half-triangle form (Erdős problem 849 convention): infinitely many `a` have
at least three solutions of `C(n, k) = a` with `1 ≤ k` and `2k ≤ n`. -/
theorem infinite_setOf_three_le_ncard_halfSolutions :
    {a : ℕ | 3 ≤ (halfSolutions a).ncard}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun B => ?_
  obtain ⟨hK, hN, hNi⟩ := fib_family_bounds (B + 1) (by omega)
  refine ⟨_, three_le_ncard_halfSolutions_of_choose_eq hK hN
    (choose_fib_eq_choose_fib (B + 1)), ?_⟩
  have hlt := lt_choose_of_two_le hK hN
  omega

end Candidates.SingmasterFibonacciFamily
