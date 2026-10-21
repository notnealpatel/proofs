/-
# Mahonian distribution of inversions (Rodrigues 1839, MacMahon 1915)

## Classical source (recorded 2026-10-21)

* O. Rodrigues, "Note sur les inversions, ou dérangements produits dans les
  permutations", J. Math. Pures Appl. 4 (1839), 236–240.
* P. A. MacMahon, *Combinatory Analysis*, Vol. I (1915), Sect. III.
* R. P. Stanley, *Enumerative Combinatorics*, Vol. 1, 2nd ed. (2012),
  Corollary 1.3.13.

## Informal statement (verbatim from the target card)

```
Σ_{σ ∈ S_n} q^{inv(σ)} = ∏_{i=1}^{n} (1 + q + … + q^{i−1}),
where inv(σ) = #{i<j : σ i > σ j}. Equivalently, the number I(n,k) of
permutations with k inversions satisfies
I(n+1,k) = Σ_{j=0}^{min(k,n)} I(n,k−j).
```

## Mathlib absence check

`leandoc` / `grep` over Mathlib (2026-10-21): no inversion-count statistic on
`Equiv.Perm (Fin n)` and no Mahonian / q-factorial generating function.  The
inversion pairs appear only inside the sign computation (`Equiv.Perm.signAux`)
and in abstract Coxeter systems (`Mathlib/GroupTheory/Coxeter/Inversion.lean`).

## Proof

Insertion at the first position: `σ ↦ (σ 0, τ)` where `τ` standardises the
values `σ 1, …, σ n` through `(σ 0).succAbove`.  The pairs `(0, j)` contribute
exactly `σ 0` inversions (every smaller value sits to the right of position `0`),
and the remaining pairs are the inversions of `τ`.
-/
import Mathlib

set_option autoImplicit false

open Finset Polynomial

namespace Candidates.MahonianInversions

/-- The number of inversions of a permutation `σ` of `Fin n`:
`inv σ = #{(i, j) | i < j ∧ σ j < σ i}`. -/
def inv {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  #{p : Fin n × Fin n | p.1 < p.2 ∧ σ p.2 < σ p.1}

/-- The number `I(n, k)` of permutations of `Fin n` with exactly `k` inversions. -/
def mahonian (n k : ℕ) : ℕ :=
  #{σ : Equiv.Perm (Fin n) | inv σ = k}

/-! ### Ground truth -/

example : inv (1 : Equiv.Perm (Fin 3)) = 0 := by decide
example : inv (Equiv.swap (0 : Fin 3) 2) = 3 := by decide
example : inv (Equiv.swap (0 : Fin 3) 1) = 1 := by decide
example : inv (finRotate 4) = 3 := by decide
example : mahonian 3 0 = 1 := by decide
example : mahonian 3 1 = 2 := by decide
example : mahonian 3 2 = 2 := by decide
example : mahonian 3 3 = 1 := by decide

/-! ### Insertion at the first position -/

/-- The underlying function of `insertPerm c τ`: position `0` goes to `c`, and
position `i.succ` goes to `c.succAbove (τ i)`. -/
def insertFun {n : ℕ} (c : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cons c (fun i => c.succAbove (τ i))

/-- `insertFun c τ` is injective. -/
theorem insertFun_injective {n : ℕ} (c : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Function.Injective (insertFun c τ) := by
  refine Fin.cons_injective_iff.2 ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    exact Fin.succAbove_ne c (τ i) hi
  · intro i j hij
    exact τ.injective (Fin.succAbove_right_injective hij)

/-- The permutation of `Fin (n + 1)` with first value `c` whose remaining values,
standardised through `c.succAbove`, form `τ`. -/
noncomputable def insertPerm {n : ℕ} (c : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (insertFun c τ) (Finite.injective_iff_bijective.1 (insertFun_injective c τ))

/-- `insertPerm c τ` sends position `0` to `c`. -/
@[simp] theorem insertPerm_zero {n : ℕ} (c : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    insertPerm c τ 0 = c := rfl

/-- `insertPerm c τ` sends position `i.succ` to `c.succAbove (τ i)`. -/
@[simp] theorem insertPerm_succ {n : ℕ} (c : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    insertPerm c τ i.succ = c.succAbove (τ i) := rfl

/-- `(c, τ) ↦ insertPerm c τ` is injective. -/
theorem insertPerm_injective {n : ℕ} :
    Function.Injective (fun p : Fin (n + 1) × Equiv.Perm (Fin n) => insertPerm p.1 p.2) := by
  rintro ⟨c, τ⟩ ⟨d, ρ⟩ h
  have hc : c = d := by simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ 0) h
  subst hc
  refine Prod.ext rfl (Equiv.ext fun i => ?_)
  have hi := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ i.succ) h
  simpa using hi

/-- `(c, τ) ↦ insertPerm c τ` is a bijection onto `Equiv.Perm (Fin (n + 1))`. -/
theorem insertPerm_bijective {n : ℕ} :
    Function.Bijective (fun p : Fin (n + 1) × Equiv.Perm (Fin n) => insertPerm p.1 p.2) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨insertPerm_injective, ?_⟩
  simp [Fintype.card_perm, Nat.factorial_succ]

/-! ### Inversions of an inserted permutation -/

/-- Row decomposition: `inv σ = ∑ i, #{j | i < j ∧ σ j < σ i}`. -/
theorem inv_eq_sum {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    inv σ = ∑ i, #{j | i < j ∧ σ j < σ i} := by
  rw [inv, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Finset.card_filter]

/-- The first row of `insertPerm c τ` contributes exactly `c` inversions. -/
theorem card_row_zero {n : ℕ} (c : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    #{j | (0 : Fin (n + 1)) < j ∧ insertPerm c τ j < insertPerm c τ 0} = (c : ℕ) := by
  rw [Fin.card_filter_univ_succ]
  simp only [lt_self_iff_false, false_and, if_false, insertPerm_succ, insertPerm_zero,
    Fin.succ_pos, true_and, Fin.succAbove_lt_iff_castSucc_lt]
  have hτ : #{x : Fin n | (τ x).castSucc < c} = #{x : Fin n | x.castSucc < c} :=
    Finset.card_equiv τ (by simp)
  rw [hτ]
  have hval : #{x : Fin n | x.castSucc < c} = #{x : Fin n | (x : ℕ) < (c : ℕ)} := by
    congr 1
  rw [hval, Fin.card_filter_val_lt]
  omega

/-- Row `i.succ` of `insertPerm c τ` has as many inversions as row `i` of `τ`. -/
theorem card_row_succ {n : ℕ} (c : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    #{j | i.succ < j ∧ insertPerm c τ j < insertPerm c τ i.succ} = #{j | i < j ∧ τ j < τ i} := by
  rw [Fin.card_filter_univ_succ]
  simp [Fin.succAbove_lt_succAbove_iff]

/-- **Insertion recursion.** `inv (insertPerm c τ) = c + inv τ`. -/
theorem inv_insertPerm {n : ℕ} (c : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    inv (insertPerm c τ) = (c : ℕ) + inv τ := by
  rw [inv_eq_sum, Fin.sum_univ_succ, card_row_zero, inv_eq_sum]
  simp only [card_row_succ]

/-- Transfer along the insertion bijection: for any `f : ℕ → M`,
`∑ σ : S_{n+1}, f (inv σ) = ∑ c : Fin (n+1), ∑ τ : S_n, f (c + inv τ)`. -/
theorem sum_inv_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ σ : Equiv.Perm (Fin (n + 1)), f (inv σ) =
      ∑ c : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f ((c : ℕ) + inv τ) := by
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_bijective _ insertPerm_bijective _ _ fun p => ?_).symm
  rw [inv_insertPerm]

/-! ### Main theorems -/

/-- **Rodrigues–MacMahon (Mahonian generating function).**
`∑_{σ ∈ S_n} q^{inv σ} = ∏_{i=1}^{n} (1 + q + ⋯ + q^{i-1})`, as an identity in `ℕ[X]`
(the factor for `i + 1` is `∑_{j < i + 1} X^j`). -/
theorem sum_X_pow_inv (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin n), (X : ℕ[X]) ^ inv σ =
      ∏ i ∈ range n, ∑ j ∈ range (i + 1), (X : ℕ[X]) ^ j := by
  induction n with
  | zero =>
    have hinv : ∀ σ : Equiv.Perm (Fin 0), inv σ = 0 := fun σ => by decide +revert
    simp [hinv]
  | succ n ih =>
    rw [sum_inv_succ n (fun k => (X : ℕ[X]) ^ k), prod_range_succ, ← ih, mul_comm,
      Finset.sum_mul_sum, ← Fin.sum_univ_eq_sum_range
        (fun j => ∑ τ : Equiv.Perm (Fin n), (X : ℕ[X]) ^ j * X ^ inv τ) (n + 1)]
    simp only [pow_add]

/-- **Mahonian recurrence.** The number `I(n, k)` of permutations of `Fin n` with `k`
inversions satisfies `I(n+1, k) = ∑_{j=0}^{min(k,n)} I(n, k - j)` (the subtraction is
safe since `j ≤ k`). -/
theorem mahonian_succ (n k : ℕ) :
    mahonian (n + 1) k = ∑ j ∈ range (min k n + 1), mahonian n (k - j) := by
  have hcount : ∀ m, mahonian m k = ∑ σ : Equiv.Perm (Fin m), if inv σ = k then 1 else 0 :=
    fun m => Finset.card_filter _ _
  have hfiber : ∀ j : ℕ, (∑ τ : Equiv.Perm (Fin n), if j + inv τ = k then 1 else 0) =
      if j ≤ k then mahonian n (k - j) else 0 := by
    intro j
    rw [mahonian, Finset.card_filter]
    split_ifs with hj
    · refine Finset.sum_congr rfl fun τ _ => ?_
      exact if_congr (by omega) rfl rfl
    · refine Finset.sum_eq_zero fun τ _ => if_neg (by omega)
  have hrange : (range (n + 1)).filter (· ≤ k) = range (min k n + 1) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [hcount, sum_inv_succ n (fun m => if m = k then 1 else 0)]
  simp only [hfiber]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ k then mahonian n (k - j) else 0) (n + 1),
    ← Finset.sum_filter, hrange]

end Candidates.MahonianInversions
