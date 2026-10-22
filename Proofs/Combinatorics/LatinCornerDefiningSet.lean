/-
# Corner defining sets of cyclic Latin squares

Richard Bean, *A counting proof for the smallest critical set in a Latin
square*, arXiv:2610.18199, Section 10: the corner-set construction, forcing
order and filled-cell count. The construction is classical (Curran and
van Rees 1979; Smetaniuk; Cooper, Donovan and Seberry 1991).

For `k = ⌊n/2⌋`, the cells with ordinary sum `r+c < k` or `n+k ≤ r+c`
form a defining set of the cyclic Latin square with `k(n-k) = ⌊n²/4⌋`
filled cells. This is only the upper-bound half of Theorem B.

## Conventions

* Rows, columns and symbols are `Fin n`; a Latin square is a function
  `L : Fin n → Fin n → Fin n` whose rows and columns are bijections (each
  symbol exactly once in each row and each column).
* A partial Latin square is `P : Fin n → Fin n → Option (Fin n)` (`none` is an
  empty cell).  A completion of `P` is a Latin square agreeing with `P` on its
  filled cells; `P` is a defining set of `L` when `L` is a completion of `P`
  and every completion of `P` equals `L`.
* `cyclic n r c = r + c` uses `Fin` addition, i.e. `(r + c) mod n`.
* `cornerSet n` is `{(r, c) | r + c < n / 2 ∨ n + n / 2 ≤ r + c}` with the sum
  taken in `ℕ`, and `cornerSquare n` is `B_n` restricted to it.
* `n = 0` is allowed and trivially true; the claim is meaningful for `1 ≤ n`.
-/
import Mathlib

set_option autoImplicit false

namespace LatinCornerDefiningSet

open Finset

/-- The cyclic Latin square `B_n`: cell `(r, c)` holds `(r + c) mod n`. -/
def cyclic (n : ℕ) (r c : Fin n) : Fin n := r + c

/-- `L` is a Latin square of order `n`: each symbol occurs exactly once in every
row and exactly once in every column. -/
def IsLatin {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ r, Function.Bijective (L r)) ∧ ∀ c, Function.Bijective fun r => L r c

/-- `L` is a completion of the partial array `P`: `L` is a Latin square that
agrees with `P` in every filled cell. -/
def IsCompletion {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (L : Fin n → Fin n → Fin n) : Prop :=
  IsLatin L ∧ ∀ r c s, P r c = some s → L r c = s

/-- `P` is a defining set of the Latin square `L`: its filled cells agree with
`L` and `L` is its only completion. -/
def IsDefiningSet {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (L : Fin n → Fin n → Fin n) : Prop :=
  IsCompletion P L ∧ ∀ L', IsCompletion P L' → L' = L

/-- The filled cells of a partial array. -/
def filledCells {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) : Finset (Fin n × Fin n) :=
  univ.filter fun p => (P p.1 p.2).isSome

/-- The corner set of order `n`: cells `(r, c)` with `r + c < ⌊n/2⌋` or
`r + c ≥ n + ⌊n/2⌋` (ordinary integer sum). -/
def cornerSet (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.filter fun p => p.1.val + p.2.val < n / 2 ∨ n + n / 2 ≤ p.1.val + p.2.val

/-- The partial Latin square `C_n`: the cyclic square `B_n` restricted to the
corner set. -/
def cornerSquare (n : ℕ) (r c : Fin n) : Option (Fin n) :=
  if (r, c) ∈ cornerSet n then some (cyclic n r c) else none

/-! ## Examples -/

example : cyclic 5 3 4 = 2 := by decide
example : cornerSet 3 = {(0, 0), (2, 2)} := by decide
example : cornerSet 5 = {(0, 0), (0, 1), (1, 0), (3, 4), (4, 3), (4, 4)} := by decide
example : cornerSquare 5 4 4 = some 3 := by decide
example : cornerSquare 5 0 4 = none := by decide
example : cornerSquare 5 3 4 = some 2 := by decide
example : (cornerSet 4).card = 4 := by decide
example : (cornerSet 6).card = 9 := by decide
example : (cornerSet 7).card = 12 := by decide
example : ¬ IsLatin (fun (_ _ : Fin 2) => (0 : Fin 2)) := by
  intro h
  exact absurd ((h.1 0).1 (rfl : (0 : Fin 2) = 0) : (0 : Fin 2) = 1) (by decide)

/-! ## The cyclic square is Latin -/

/-- The cyclic square `B_n` is a Latin square. -/
theorem cyclic_isLatin (n : ℕ) : IsLatin (cyclic n) := by
  refine ⟨fun r => ?_, fun c => ?_⟩
  · haveI : NeZero n := NeZero.of_pos r.pos
    refine Function.Injective.bijective_of_finite ?_
    intro a b hab
    exact add_left_cancel (hab : r + a = r + b)
  · haveI : NeZero n := NeZero.of_pos c.pos
    refine Function.Injective.bijective_of_finite ?_
    intro a b hab
    exact add_right_cancel (hab : a + c = b + c)

/-! ## Forcing -/

/-- **Forcing step** (Section 10, "Why the same order works for every `n`").
Let `L` be a Latin square agreeing with `B_n` on the corner set `C_n`. If `L`
agrees with `B_n` in every row above `r` and in every cell of row `r` to the
right of column `c`, then `L` agrees with `B_n` at `(r, c)`: every other symbol
already occurs in row `r` or in column `c`. -/
theorem cell_forced {n : ℕ} {L : Fin n → Fin n → Fin n} (hL : IsLatin L)
    (hagree : ∀ p ∈ cornerSet n, L p.1 p.2 = cyclic n p.1 p.2) (r c : Fin n)
    (hprev : ∀ i : Fin n, i.val < r.val → ∀ c', L i c' = cyclic n i c')
    (hright : ∀ j : Fin n, c.val < j.val → L r j = cyclic n r j) :
    L r c = cyclic n r c := by
  haveI : NeZero n := NeZero.of_pos r.pos
  by_contra hne
  set j : Fin n := L r c - r with hjdef
  have hj : r + j = L r c := by rw [hjdef]; abel
  have hjc : j ≠ c := by
    intro h
    rw [h] at hj
    exact hne hj.symm
  have hrow : L r j ≠ cyclic n r j := fun h => hjc ((hL.1 r).1 (h.trans hj))
  have hjlt : j.val < c.val := by
    by_contra hcon
    have hcj : c.val < j.val := by
      have : j.val ≠ c.val := fun h => hjc (Fin.ext h)
      omega
    exact hrow (hright j hcj)
  have hjk : n / 2 ≤ r.val + j.val := by
    by_contra hcon
    exact hrow (hagree (r, j) (by simp only [cornerSet, mem_filter, mem_univ, true_and]; omega))
  have hcol : ∀ i : Fin n, i ≠ r → i + c = r + j → L i c = i + c → False := by
    intro i hir hsum hLi
    exact hir ((hL.2 c).1 (show L i c = L r c by rw [hLi, hsum, hj]))
  by_cases hcrj : c.val ≤ r.val + j.val
  · refine hcol ⟨r.val + j.val - c.val, by omega⟩ ?_ ?_ ?_
    · intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    · ext
      simp only [Fin.val_add]
      congr 1
      omega
    · exact hprev _ (by simp only; omega) c
  · refine hcol ⟨r.val + j.val + n - c.val, by omega⟩ ?_ ?_ ?_
    · intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    · ext
      simp only [Fin.val_add]
      rw [show r.val + j.val + n - c.val + c.val = r.val + j.val + n by omega, Nat.add_mod_right]
    · refine hagree (⟨r.val + j.val + n - c.val, by omega⟩, c) ?_
      simp only [cornerSet, mem_filter, mem_univ, true_and]
      omega

/-- **Unique completion.** A Latin square of order `n` that agrees with the
cyclic square `B_n` on the corner set `C_n` is `B_n` itself (induction over the
cells row by row from the top, right to left within each row). -/
theorem eq_cyclic_of_agree {n : ℕ} {L : Fin n → Fin n → Fin n} (hL : IsLatin L)
    (hagree : ∀ p ∈ cornerSet n, L p.1 p.2 = cyclic n p.1 p.2) : L = cyclic n := by
  have key : ∀ a : ℕ, ∀ r : Fin n, r.val = a → ∀ c, L r c = cyclic n r c := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a iha =>
      intro r hr
      have hrow : ∀ b : ℕ, ∀ c : Fin n, n - c.val = b → L r c = cyclic n r c := by
        intro b
        induction b using Nat.strong_induction_on with
        | _ b ihb =>
          intro c hc
          apply cell_forced hL hagree r c
          · intro i hi c'
            exact iha i.val (by omega) i rfl c'
          · intro j hj
            exact ihb (n - j.val) (by omega) j rfl
      intro c
      exact hrow _ c rfl
  funext r c
  exact key r.val r rfl c

/-- The lower triangle `{(r, c) : r + c < m}` of the `n × n` grid has
`m (m + 1) / 2` cells when `m ≤ n`, stated without division. -/
lemma two_mul_card_lower (n m : ℕ) (hm : m ≤ n) :
    2 * (univ.filter fun p : Fin n × Fin n => p.1.val + p.2.val < m).card = m * (m + 1) := by
  have hcard : (univ.filter fun p : Fin n × Fin n => p.1.val + p.2.val < m).card
      = ((range m).sigma fun s => range (s + 1)).card := by
    refine Finset.card_bij' (fun p _ => (⟨p.1.val + p.2.val, p.1.val⟩ : Σ _ : ℕ, ℕ))
      (fun q hq => ((⟨q.2, ?_⟩, ⟨q.1 - q.2, ?_⟩) : Fin n × Fin n)) ?_ ?_ ?_ ?_
    · simp only [mem_sigma, mem_range] at hq
      omega
    · simp only [mem_sigma, mem_range] at hq
      omega
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp only [mem_sigma, mem_range]
      omega
    · intro q hq
      simp only [mem_sigma, mem_range] at hq
      simp only [mem_filter, mem_univ, true_and]
      omega
    · intro p hp
      ext <;> simp
    · intro q hq
      simp only [mem_sigma, mem_range] at hq
      ext
      · simp only
        omega
      · simp
  rw [hcard, Finset.card_sigma]
  clear hcard hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih, card_range]
    ring

/-- Reflecting both coordinates (`r ↦ n - 1 - r`) maps the upper corner
`{r + c ≥ n + m}` bijectively onto the lower triangle `{r + c < n - 1 - m}`. -/
lemma card_upper_eq (n m : ℕ) :
    (univ.filter fun p : Fin n × Fin n => n + m ≤ p.1.val + p.2.val).card
      = (univ.filter fun p : Fin n × Fin n => p.1.val + p.2.val < n - 1 - m).card := by
  refine Finset.card_bij' (fun p _ => (p.1.rev, p.2.rev)) (fun p _ => (p.1.rev, p.2.rev))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, Fin.val_rev] at hp ⊢
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    omega
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, Fin.val_rev] at hp ⊢
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    omega
  · intro p hp
    simp
  · intro p hp
    simp

/-- **Size of the corner set** (Section 10, "The number of filled cells"):
`C_n` has exactly `⌊n² / 4⌋` cells. -/
theorem card_cornerSet (n : ℕ) : (cornerSet n).card = n ^ 2 / 4 := by
  have hsplit : (cornerSet n).card
      = (univ.filter fun p : Fin n × Fin n => p.1.val + p.2.val < n / 2).card
        + (univ.filter fun p : Fin n × Fin n => n + n / 2 ≤ p.1.val + p.2.val).card := by
    rw [cornerSet, filter_or, card_union_of_disjoint]
    rw [disjoint_filter]
    intro p _ h1 h2
    omega
  have hlow := two_mul_card_lower n (n / 2) (Nat.div_le_self n 2)
  have hup := two_mul_card_lower n (n - 1 - n / 2) (by omega)
  rw [← card_upper_eq] at hup
  rw [hsplit]
  generalize (univ.filter fun p : Fin n × Fin n => p.1.val + p.2.val < n / 2).card = a at hlow ⊢
  generalize (univ.filter fun p : Fin n × Fin n => n + n / 2 ≤ p.1.val + p.2.val).card = b
    at hup ⊢
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · clear hsplit
    rw [show (2 * k) ^ 2 / 4 = k ^ 2 by
      rw [show (2 * k) ^ 2 = k ^ 2 * 4 by ring, Nat.mul_div_cancel _ (by norm_num)]]
    rcases k with _ | k
    · simp only [mul_zero, Nat.zero_div, zero_mul, Nat.zero_sub, Nat.mul_eq_zero] at hlow hup ⊢
      omega
    · rw [show 2 * (k + 1) / 2 = k + 1 by omega] at hlow hup
      rw [show 2 * (k + 1) - 1 - (k + 1) = k by omega] at hup
      nlinarith
  · clear hsplit
    rw [show (2 * k + 1) / 2 = k by omega] at hlow hup
    rw [show 2 * k + 1 - 1 - k = k by omega] at hup
    rw [show (2 * k + 1) ^ 2 / 4 = k * (k + 1) by
      rw [show (2 * k + 1) ^ 2 = 1 + 4 * (k * (k + 1)) by ring]
      omega]
    nlinarith

/-! ## Main theorem -/

/-- The filled cells of `C_n` are exactly the corner set. -/
theorem filledCells_cornerSquare (n : ℕ) : filledCells (cornerSquare n) = cornerSet n := by
  ext p
  by_cases hp : p ∈ cornerSet n <;> simp [filledCells, cornerSquare, hp]

/-- **Corner sets are defining sets** (Bean, arXiv:2610.18199, Section 10;
classical, Curran–van Rees, Smetaniuk, Cooper–Donovan–Seberry): for every order
`n`, the partial Latin square `C_n` (the cyclic square `B_n` kept on the cells
with `r + c < ⌊n/2⌋` or `r + c ≥ n + ⌊n/2⌋`) has `B_n` as its unique
completion and has exactly `⌊n²/4⌋` filled cells. -/
theorem cornerSquare_isDefiningSet (n : ℕ) :
    IsDefiningSet (cornerSquare n) (cyclic n) ∧
      (filledCells (cornerSquare n)).card = n ^ 2 / 4 := by
  refine ⟨⟨⟨cyclic_isLatin n, ?_⟩, ?_⟩, ?_⟩
  · intro r c s hs
    unfold cornerSquare at hs
    split_ifs at hs with hmem
    exact Option.some.inj hs
  · intro L hcomp
    refine eq_cyclic_of_agree hcomp.1 ?_
    intro p hp
    exact hcomp.2 p.1 p.2 _ (by simp [cornerSquare, hp])
  · rw [filledCells_cornerSquare, card_cornerSet]

/-- **Upper half of Theorem B**, `scs(B_n) ≤ ⌊n²/4⌋`: the cyclic square of
order `n` has a defining set with at most `⌊n²/4⌋` filled cells. -/
theorem exists_definingSet_card_le (n : ℕ) :
    ∃ P : Fin n → Fin n → Option (Fin n),
      IsDefiningSet P (cyclic n) ∧ (filledCells P).card ≤ n ^ 2 / 4 :=
  ⟨cornerSquare n, (cornerSquare_isDefiningSet n).1,
    (cornerSquare_isDefiningSet n).2.le⟩

/-- The empty partial square of order `2` is
not a defining set of `B_2`, since the other cyclic square `r + c + 1` is also
a completion. -/
example : ¬ IsDefiningSet (fun (_ _ : Fin 2) => (none : Option (Fin 2))) (cyclic 2) := by
  rintro ⟨_, huniq⟩
  have hlat : IsLatin (fun (r c : Fin 2) => r + c + 1) := by
    refine ⟨fun r => ?_, fun c => ?_⟩
    · revert r
      decide
    · revert c
      decide
  have h := congrFun (congrFun (huniq _ ⟨hlat, by simp⟩) 0) 0
  exact absurd h (by decide)

end LatinCornerDefiningSet
