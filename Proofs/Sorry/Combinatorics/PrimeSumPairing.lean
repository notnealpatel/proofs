/-
# Prime-sum pairing of `{1, …, 2n}` (perfect matching in the prime-sum graph)

## Source

* MathOverflow answer https://mathoverflow.net/a/130466 (answer id 130466 in
  the thread on the prime circle problem; the parent question id was not
  re-fetched, mathoverflow.net being unreachable from this environment).  The thread remarks that it is a
  "simple consequence of Bertrand's postulate" that the prime-sum graph
  `G_n` on `{1, …, 2n}` (distinct `x, y` adjacent iff `x + y` is prime) is
  connected and has a perfect matching.
* Literature: L. Greenfield and S. Greenfield, "Some problems of combinatorial
  number theory related to Bertrand's postulate", J. Integer Seq. 1 (1998),
  Article 98.1.2; reproduced as Theorem 1.1 of Chen–Fu–Guo, arXiv:1804.07104.
* Surrounding conjecture (open, not formalized here): the prime circle problem
  of Filz (1982, J. Recreational Math. problem 1046): for `n ≥ 2`, can
  `{1, …, 2n}` be arranged in a circle so that adjacent numbers sum to a
  prime, i.e. is `G_n` Hamiltonian?

## Informal claim (verbatim from the target specification)

"For every n, the set {1,...,2n} splits into n pairs, each summing to a prime,
i.e. a fixed-point-free involution f on [1,2n] with i + f i prime.  The
companion statement is a permutation pi of {1,...,n} with i + pi(i) prime for
all i."

## Status

Proved in the literature (Greenfield–Greenfield 1998); recorded here
2026-10-21.  The proof is the Bertrand recursion: take a prime `p` with
`m < p ≤ 2m`, pair `i ↔ p - i` on `[p - m, m]`, recurse on `[1, p - m - 1]`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.PrimeSumPairing

/-! ## Definitions -/

/-- The prime-sum graph on `{1, …, m}`: two distinct vertices `x, y` are adjacent
iff `x + y` is prime.  For `m = 2n` this is the graph `G_n` of the prime circle
problem. -/
def primeSumGraph (m : ℕ) : SimpleGraph (Finset.Icc 1 m) where
  Adj x y := x ≠ y ∧ (x.1 + y.1).Prime
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [Nat.add_comm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

instance (m : ℕ) : DecidableRel (primeSumGraph m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ (x.1 + y.1).Prime))

/-! ### Ground truth for `primeSumGraph` -/

example : (primeSumGraph 4).Adj ⟨1, by decide⟩ ⟨4, by decide⟩ := by decide
example : (primeSumGraph 4).Adj ⟨2, by decide⟩ ⟨3, by decide⟩ := by decide
example : ¬ (primeSumGraph 4).Adj ⟨2, by decide⟩ ⟨4, by decide⟩ := by decide
example : ¬ (primeSumGraph 4).Adj ⟨1, by decide⟩ ⟨1, by decide⟩ := by decide

/-! ## The Bertrand recursion -/

/-- An involution of `ℕ` fixing everything outside `[1, k]` maps `[0, k]` into
`[0, k]`. -/
theorem le_of_involutive_of_fix {g : ℕ → ℕ} {k : ℕ} (hg : Function.Involutive g)
    (hout : ∀ i, i ∉ Finset.Icc 1 k → g i = i) {i : ℕ} (hi : i ≤ k) : g i ≤ k := by
  by_contra hgt
  have hfix : g (g i) = g i := hout (g i) (by simp only [Finset.mem_Icc]; omega)
  rw [hg i] at hfix
  omega

/-- Core recursion (Greenfield–Greenfield via Bertrand's postulate): for every
`n` there is an involution `f` of `ℕ` fixing everything outside `{1, …, n}`
with `i + f i` prime for all `i ∈ {1, …, n}`; if `n` is even, `f` has no fixed
point in `{1, …, n}`. -/
theorem exists_involutive_primeSum (n : ℕ) :
    ∃ f : ℕ → ℕ, Function.Involutive f ∧ (∀ i, i ∉ Finset.Icc 1 n → f i = i) ∧
      (∀ i ∈ Finset.Icc 1 n, (i + f i).Prime) ∧
      (Even n → ∀ i ∈ Finset.Icc 1 n, f i ≠ i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨id, fun _ => rfl, fun _ _ => rfl, by simp, by simp⟩
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n hn.ne'
  set k := p - n - 1 with hk
  have hkn : k < n := by omega
  obtain ⟨g, hg_inv, hg_out, hg_prime, hg_ne⟩ := ih k hkn
  have hg_le : ∀ i, i ≤ k → g i ≤ k := fun i hi =>
    le_of_involutive_of_fix hg_inv hg_out hi
  refine ⟨fun i => if i ≤ k then g i else if i ≤ n then p - i else i, ?_, ?_, ?_, ?_⟩
  · -- involutivity
    intro i
    by_cases hik : i ≤ k
    · have hgi := hg_le i hik
      simp only [hik, hgi, if_true]
      exact hg_inv i
    · by_cases hin : i ≤ n
      · have h1 : ¬ p - i ≤ k := by omega
        have h2 : p - i ≤ n := by omega
        simp only [hik, hin, h1, h2, if_false, if_true]
        omega
      · simp only [hik, hin, if_false]
  · -- fixes the outside of `[1, n]`
    intro i hi
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · have hi0 : i = 0 := by omega
      subst hi0
      simp only [Nat.zero_le, if_true]
      exact hg_out 0 (by simp)
    · have h1 : ¬ i ≤ k := by omega
      have h2 : ¬ i ≤ n := by omega
      simp only [h1, h2, if_false]
  · -- prime sums
    intro i hi
    simp only [Finset.mem_Icc] at hi
    by_cases hik : i ≤ k
    · simp only [hik, if_true]
      exact hg_prime i (by simp only [Finset.mem_Icc]; omega)
    · have hin : i ≤ n := hi.2
      simp only [hik, hin, if_false, if_true]
      have hsum : i + (p - i) = p := by omega
      rw [hsum]
      exact hp
  · -- no fixed points when `n` is even
    intro hev i hi
    simp only [Finset.mem_Icc] at hi
    obtain ⟨a, ha⟩ := hev
    have hp2 : p ≠ 2 := by omega
    obtain ⟨b, hb⟩ := hp.odd_of_ne_two hp2
    have hkev : Even k := ⟨b - a, by omega⟩
    by_cases hik : i ≤ k
    · simp only [hik, if_true]
      exact hg_ne hkev i (by simp only [Finset.mem_Icc]; omega)
    · have hin : i ≤ n := hi.2
      simp only [hik, hin, if_false, if_true]
      omega

/-! ## Main theorems -/

/-- **Prime-sum pairing** (Greenfield–Greenfield 1998; MathOverflow 130466):
for every `n`, `{1, …, 2n}` splits into `n` pairs each summing to a prime, i.e.
there is a fixed-point-free involution `f` of `{1, …, 2n}` with `i + f i`
prime for every `i`. -/
theorem exists_primeSum_pairing (n : ℕ) :
    ∃ f : ℕ → ℕ, ∀ i ∈ Finset.Icc 1 (2 * n),
      f i ∈ Finset.Icc 1 (2 * n) ∧ f i ≠ i ∧ f (f i) = i ∧ (i + f i).Prime := by
  obtain ⟨f, hinv, hout, hprime, hne⟩ := exists_involutive_primeSum (2 * n)
  refine ⟨f, fun i hi => ⟨?_, hne (even_two_mul n) i hi, hinv i, hprime i hi⟩⟩
  by_contra hfi
  have hfix : f (f i) = f i := hout (f i) hfi
  rw [hinv i] at hfix
  exact hfi (hfix ▸ hi)

/-- **Prime-sum permutation** (companion statement, Greenfield–Greenfield 1998):
for every `n` there is a permutation `σ` of `ℕ` supported in `{1, …, n}` with
`i + σ i` prime for every `i ∈ {1, …, n}`. -/
theorem exists_primeSum_perm (n : ℕ) :
    ∃ σ : Equiv.Perm ℕ, (∀ i, i ∉ Finset.Icc 1 n → σ i = i) ∧
      ∀ i ∈ Finset.Icc 1 n, (i + σ i).Prime := by
  obtain ⟨f, hinv, hout, hprime, -⟩ := exists_involutive_primeSum n
  exact ⟨hinv.toPerm f, hout, hprime⟩

/-- **Perfect matching in the prime-sum graph** (MathOverflow 130466, "a simple
consequence of Bertrand's postulate"): for every `n`, the graph on
`{1, …, 2n}` in which distinct `x, y` are adjacent iff `x + y` is prime has a
perfect matching. -/
theorem primeSumGraph_exists_isPerfectMatching (n : ℕ) :
    ∃ M : (primeSumGraph (2 * n)).Subgraph, M.IsPerfectMatching := by
  obtain ⟨f, hf⟩ := exists_primeSum_pairing n
  let F : Finset.Icc 1 (2 * n) → Finset.Icc 1 (2 * n) :=
    fun x => ⟨f x.1, (hf x.1 x.2).1⟩
  let H : SimpleGraph (Finset.Icc 1 (2 * n)) :=
    SimpleGraph.fromRel fun x y => y = F x
  have hFne : ∀ x, F x ≠ x := fun x h => (hf x.1 x.2).2.1 (congrArg Subtype.val h)
  have hFF : ∀ x, F (F x) = x := fun x => Subtype.ext (hf x.1 x.2).2.2.1
  have hHadj : ∀ x y, H.Adj x y ↔ y = F x := by
    intro x y
    simp only [H, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, h | h⟩
      · exact h
      · rw [h, hFF]
    · rintro rfl
      exact ⟨(hFne x).symm, Or.inl rfl⟩
  have hle : H ≤ primeSumGraph (2 * n) := by
    intro x y hxy
    rw [hHadj] at hxy
    subst hxy
    show x ≠ F x ∧ (x.1 + f x.1).Prime
    exact ⟨(hFne x).symm, (hf x.1 x.2).2.2.2⟩
  refine ⟨SimpleGraph.toSubgraph H hle, ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro x
  refine ⟨F x, ?_, ?_⟩
  · show H.Adj x (F x)
    exact (hHadj x (F x)).2 rfl
  · intro y hy
    exact (hHadj x y).1 hy

end Candidates.PrimeSumPairing
