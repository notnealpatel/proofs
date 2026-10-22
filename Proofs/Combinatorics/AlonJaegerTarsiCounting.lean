/-
# Alon–Jaeger–Tarsi conjecture: the counting case `|F| ≥ d + 2`

Baker, Bonin, Lazebnik and Shustin, *On the number of nowhere zero points
in linear mappings*, Combinatorica 14 (1994), 149–157, prove the
Alon–Jaeger–Tarsi counting case `d + 2 ≤ |F|`. It is cited in
George A. Kirkup, *Minimal Primes Over Permanental Ideals* (2005),
arXiv:math/0510025, Section `AJTsec`, following Conjecture `AJTconj1`.

This is the established counting case, not the general conjecture.
The theorem below weakens nonsingularity to the condition that every row
is nonzero; the nonsingular form is a corollary.

## Proof (union bound with a scaling injection)

Let `N` be the nowhere-zero vectors and `B i ⊆ N` those with `(A v) i = 0`.
Pick `j` with `A i j ≠ 0`.  The map `(v, c) ↦ update v j c` from
`B i × F^×` to `N` is injective (a vector in `B i` is determined by its
coordinates off `j`), so `|B i| (q - 1) ≤ |N|`.  Summing over the `d` rows,
`|⋃ B i| (q - 1) ≤ d |N| < (q - 1) |N|` as `d < q - 1` and `N ≠ ∅`.
-/
import Mathlib

set_option autoImplicit false

namespace AlonJaegerTarsiCounting

open Finset Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The vectors `v : Fin d → F` with no zero coordinate. -/
def nowhereZero (d : ℕ) : Finset (Fin d → F) :=
  univ.filter fun v => ∀ j, v j ≠ 0

/-- The nowhere-zero vectors `v` whose image `A v` vanishes in coordinate `i`. -/
def badAt {d : ℕ} (A : Matrix (Fin d) (Fin d) F) (i : Fin d) : Finset (Fin d → F) :=
  (nowhereZero (F := F) d).filter fun v => (A *ᵥ v) i = 0

/-- Over `ZMod 3` in dimension `1` the nowhere-zero vectors are
the two vectors with entry `1` or `2`. -/
example : (nowhereZero (F := ZMod 3) 1).card = 2 := by decide

/-- For `A = [[1, 1], [1, 2]]` over `ZMod 3`, the vector `(1, 2)`
is nowhere zero with `(A v) 0 = 1 + 2 = 0`. -/
example : ![1, 2] ∈ badAt (F := ZMod 3) !![1, 1; 1, 2] 0 := by
  simp only [badAt, nowhereZero, mem_filter, mem_univ, true_and]
  decide

/-- For the same matrix, `(1, 1)` is not bad at row `0`,
since `(A v) 0 = 2 ≠ 0`. -/
example : ![1, 1] ∉ badAt (F := ZMod 3) !![1, 1; 1, 2] 0 := by
  simp only [badAt, nowhereZero, mem_filter, mem_univ, true_and]
  decide

/-- A nowhere-zero vector exists (the all-ones vector). -/
lemma nowhereZero_nonempty (d : ℕ) : (nowhereZero (F := F) d).Nonempty :=
  ⟨fun _ => 1, by simp [nowhereZero]⟩

/-- Key injection: if `A i j ≠ 0`, then `(v, c) ↦ update v j c` maps
`badAt A i × F^×` injectively into the nowhere-zero vectors, hence
`|badAt A i| * (q - 1) ≤ |nowhereZero d|`. -/
lemma card_badAt_mul_le {d : ℕ} (A : Matrix (Fin d) (Fin d) F) (i : Fin d)
    (hrow : A i ≠ 0) :
    (badAt A i).card * (univ.erase (0 : F)).card ≤ (nowhereZero (F := F) d).card := by
  obtain ⟨j, hj⟩ : ∃ j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hrow (funext h)
  rw [← card_product]
  refine card_le_card_of_injOn (fun p => Function.update p.1 j p.2) ?_ ?_
  · intro p hp
    simp only [coe_product, Set.mem_prod, mem_coe, badAt, nowhereZero, mem_filter,
      mem_univ, true_and, mem_erase, ne_eq, and_true] at hp ⊢
    intro k
    by_cases hk : k = j
    · subst hk
      simpa using hp.2
    · simpa [Function.update_of_ne hk] using hp.1.1 k
  · intro p hp p' hp' hpp
    simp only [coe_product, Set.mem_prod, mem_coe, badAt, nowhereZero, mem_filter,
      mem_univ, true_and] at hp hp'
    have hc : p.2 = p'.2 := by
      simpa using congrFun hpp j
    have hoff : ∀ k, k ≠ j → p.1 k = p'.1 k := by
      intro k hk
      simpa [Function.update_of_ne hk] using congrFun hpp k
    have hdiff : p.1 - p'.1 = Pi.single j (p.1 j - p'.1 j) := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [hk, hoff k hk]
    have hzero : (A *ᵥ (p.1 - p'.1)) i = 0 := by
      rw [Matrix.mulVec_sub, Pi.sub_apply, hp.1.2, hp'.1.2, sub_zero]
    have hmul : A i j * (p.1 j - p'.1 j) = 0 := by
      rw [hdiff] at hzero
      simpa [Matrix.mulVec_single, mul_comm] using hzero
    have hj' : p.1 j = p'.1 j := by
      have := (mul_eq_zero.mp hmul).resolve_left hj
      exact sub_eq_zero.mp this
    have hv : p.1 = p'.1 := by
      funext k
      by_cases hk : k = j
      · subst hk
        exact hj'
      · exact hoff k hk
    exact Prod.ext hv hc

omit [DecidableEq F] in
/-- **Alon–Jaeger–Tarsi, counting case (Baker–Bonin–Lazebnik–Shustin 1994).**
If `F` is a finite field with `d + 2 ≤ |F|` and every row of the `d × d`
matrix `A` over `F` is nonzero, then some vector `v` has no zero coordinate
and `A v` has no zero coordinate.  (arXiv math/0510025, Section `AJTsec`,
cited from BBLS as the case `q ≥ d + 2`.) -/
theorem exists_nowhereZero_mulVec_nowhereZero (d : ℕ) (hq : d + 2 ≤ Fintype.card F)
    (A : Matrix (Fin d) (Fin d) F) (hA : ∀ i, A i ≠ 0) :
    ∃ v : Fin d → F, (∀ j, v j ≠ 0) ∧ ∀ i, (A *ᵥ v) i ≠ 0 := by
  classical
  set N := nowhereZero (F := F) d with hN
  set U := univ.biUnion (badAt A) with hU
  have hunits : (univ.erase (0 : F)).card = Fintype.card F - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ]
  have hNpos : 0 < N.card := card_pos.mpr (nowhereZero_nonempty d)
  have hUle : U.card * (Fintype.card F - 1) ≤ d * N.card := by
    calc U.card * (Fintype.card F - 1)
        ≤ (∑ i, (badAt A i).card) * (Fintype.card F - 1) :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ i, (badAt A i).card * (Fintype.card F - 1) := by rw [sum_mul]
      _ ≤ ∑ _i : Fin d, N.card := by
          refine sum_le_sum fun i _ => ?_
          rw [← hunits]
          exact card_badAt_mul_le A i (hA i)
      _ = d * N.card := by simp
  have hlt : U.card < N.card := by
    have hd : d < Fintype.card F - 1 := by omega
    by_contra hcon
    push Not at hcon
    have h1 : N.card * (Fintype.card F - 1) ≤ U.card * (Fintype.card F - 1) :=
      Nat.mul_le_mul_right _ hcon
    have h2 : d * N.card < (Fintype.card F - 1) * N.card :=
      Nat.mul_lt_mul_of_pos_right hd hNpos
    rw [mul_comm N.card] at h1
    omega
  obtain ⟨v, hvN, hvU⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨v, (mem_filter.mp hvN).2, fun i hi => hvU ?_⟩
  exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hvN, hi⟩⟩

omit [DecidableEq F] in
/-- **Alon–Jaeger–Tarsi for nonsingular matrices, case `|F| ≥ d + 2`.**
The form of Conjecture `AJTconj1` of arXiv math/0510025 in the BBLS counting
range: a nonsingular `d × d` matrix `A` over a finite field with
`d + 2 ≤ |F|` admits `v` with `v` and `A v` nowhere zero. -/
theorem exists_nowhereZero_mulVec_nowhereZero_of_det_ne_zero (d : ℕ)
    (hq : d + 2 ≤ Fintype.card F) (A : Matrix (Fin d) (Fin d) F) (hdet : A.det ≠ 0) :
    ∃ v : Fin d → F, (∀ j, v j ≠ 0) ∧ ∀ i, (A *ᵥ v) i ≠ 0 := by
  refine exists_nowhereZero_mulVec_nowhereZero d hq A fun i hi => hdet ?_
  exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [hi]

/-- The hypotheses are jointly satisfiable — `ZMod 5` has
`2 + 2 ≤ 5` and `[[1, 1], [1, 4]]` has nonzero rows. -/
example : ∃ v : Fin 2 → ZMod 5, (∀ j, v j ≠ 0) ∧
    ∀ i, ((!![1, 1; 1, 4] : Matrix (Fin 2) (Fin 2) (ZMod 5)) *ᵥ v) i ≠ 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine exists_nowhereZero_mulVec_nowhereZero (F := ZMod 5) 2 ?_ _ ?_
  · simp [ZMod.card]
  · intro i h
    fin_cases i
    · exact one_ne_zero (congrFun h 0)
    · exact one_ne_zero (congrFun h 0)

/-- Sharpness of the small-field hypothesis: over `ZMod 3` (where `|F| = d + 1`
for `d = 2`) the nonsingular matrix `[[1, 1], [1, -1]]` admits no `v` with
`v` and `A v` both nowhere zero. -/
theorem not_exists_zmod_three :
    ¬ ∃ v : Fin 2 → ZMod 3, (∀ j, v j ≠ 0) ∧
      ∀ i, ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v) i ≠ 0 := by
  decide

end AlonJaegerTarsiCounting
