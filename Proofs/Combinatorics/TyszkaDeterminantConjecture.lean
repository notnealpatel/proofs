/-
# Tyszka's determinant conjecture

Apoloniusz Tyszka, *Bounds of some real (complex) solution of a finite
system of polynomial equations with rational coefficients*,
arXiv:math/0702558v86, Conjecture 4 (after Theorem 11); restated as
Conjecture 2 in arXiv:0807.3010. Its consequence for additive groups via
Cramer's rule was proved by Freitas–Friedland–Porta, ELA 24 (2012).

If each row of an `(n-1) × n` integer matrix, after removing zeros, is
one of `⟨1⟩`, `⟨-1,2⟩`, `⟨2,-1⟩`, `⟨-1,1,1⟩`, `⟨1,-1,1⟩`, `⟨1,1,-1⟩`,
deleting any column gives a determinant of absolute value at most `2^(n-1)`.

## Conventions

* The paper's `n - 1` rows and `n` columns are `m` rows (`Fin m`) and
  `m + 1` columns (`Fin (m + 1)`), so the paper's `n` is `m + 1` and the bound
  `2^(n-1)` is `2 ^ m`.  The theorem holds for every `m`, including the
  paper's range `m ≥ 1`.
* "Deleting column `c`" is `B.submatrix id c.succAbove`.
* "After deleting all zeros, the row forms a sequence in the list" is
  `(List.ofFn v).filter (· ≠ 0) ∈ tyszkaPatterns` (`TyszkaRow`).

## Proof

Every pattern row equals `e_i + e_j - e_k` (`TyszkaRow.exists_eq`), which is
`e_j + (e_i - e_k)`: a sum of two rows of a directed-graph incidence matrix
with a ground vertex (`IncRow`), and deleting a column preserves this form
(`IncRow.comp`).  Incidence-form square matrices have determinant in
`{-1, 0, 1}` (`det_eq_neg_one_or_zero_or_one_of_incRow`), and multilinearity
of the determinant in the rows gives `|det| ≤ 2 ^ m` for sums of two such
rows (`abs_det_le_two_pow`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.TyszkaDeterminantConjecture

/-! ## Incidence-form rows and total unimodularity -/

/-- A row `r : ι → ℤ` is in *incidence form* if `r = e_a - e_b` for some
`a b : Option ι`, where `e_none` is read as the zero vector.  These are the
rows of a directed-graph incidence matrix with an extra ground vertex `none`
(so `0`, `e_a`, `-e_b`, `e_a - e_b` all qualify). -/
def IncRow {ι : Type*} [DecidableEq ι] (r : ι → ℤ) : Prop :=
  ∃ a b : Option ι, r = fun j => (if a = some j then 1 else 0) - (if b = some j then 1 else 0)

example : IncRow ![1, 0, -1] := ⟨some 0, some 2, by funext j; fin_cases j <;> rfl⟩
example : IncRow ![0, -1, 0] := ⟨none, some 1, by funext j; fin_cases j <;> rfl⟩
example : IncRow ![0, 0, 0] := ⟨none, none, by funext j; fin_cases j <;> rfl⟩

/-- Restricting an incidence-form row along an injective reindexing (in
particular, deleting columns) keeps it in incidence form: endpoints outside
the range are sent to the ground vertex `none`. -/
theorem IncRow.comp {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {r : ι → ℤ} (hr : IncRow r)
    {f : κ → ι} (hf : Function.Injective f) : IncRow (r ∘ f) := by
  classical
  obtain ⟨a, b, rfl⟩ := hr
  have key : ∀ (c : Option ι) (l : κ),
      c.bind (Function.partialInv f) = some l ↔ c = some (f l) := by
    intro c l
    cases c with
    | none => simp
    | some y => simpa [eq_comm] using hf.isPartialInv l y
  refine ⟨a.bind (Function.partialInv f), b.bind (Function.partialInv f), ?_⟩
  funext l
  simp only [Function.comp_apply, key]

/-- A square integer matrix all of whose rows are in incidence form has
`|det| ≤ 1`.  Induction on the size: a degenerate row (`0` or `±e_x`) is
either zero or allows Laplace expansion onto an incidence-form minor;
otherwise every row is `e_x - e_y` with `x ≠ y`, so the all-ones vector lies
in the kernel. -/
theorem abs_det_le_one_of_incRow : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ),
    (∀ i, IncRow (M i)) → |M.det| ≤ 1 := by
  intro m
  induction m with
  | zero => intro M _; simp
  | succ m ih =>
    intro M hM
    choose a b hab using hM
    by_cases hdeg : ∃ i, a i = none ∨ b i = none ∨ a i = b i
    · obtain ⟨i, hi⟩ := hdeg
      have hminor : ∀ j : Fin (m + 1), |(M.submatrix i.succAbove j.succAbove).det| ≤ 1 := by
        intro j
        apply ih
        intro k
        exact IncRow.comp (r := M (i.succAbove k)) ⟨a _, b _, hab (i.succAbove k)⟩
          (Fin.succAbove_right_injective (p := j))
      rcases hi with ha | hb | hab'
      · cases hbi : b i with
        | none =>
          rw [Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [hab i, ha, hbi])]
          simp
        | some x =>
          rw [Matrix.det_succ_row M i]
          have hrow : ∀ j, M i j = -(if x = j then 1 else 0) := by
            intro j; simp [hab i, ha, hbi]
          simp only [hrow, mul_neg, neg_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
            Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, abs_neg,
            abs_mul, abs_pow, abs_one, one_pow, one_mul]
          exact hminor x
      · cases hai : a i with
        | none =>
          rw [Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [hab i, hb, hai])]
          simp
        | some x =>
          rw [Matrix.det_succ_row M i]
          have hrow : ∀ j, M i j = (if x = j then 1 else 0) := by
            intro j; simp [hab i, hb, hai]
          simp only [hrow, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
            Finset.sum_ite_eq, Finset.mem_univ, if_true, abs_mul,
            abs_pow, abs_neg, abs_one, one_pow, one_mul]
          exact hminor x
      · rw [Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [hab i, hab'])]
        simp
    · push Not at hdeg
      have hdet : M.det = 0 := by
        rw [← Matrix.exists_mulVec_eq_zero_iff]
        refine ⟨fun _ => 1, fun h => by simpa using congrFun h 0, ?_⟩
        funext i
        obtain ⟨ha, hb, hne⟩ := hdeg i
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp ha
        obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hb
        rw [hx, hy] at hne
        simp [Matrix.mulVec, dotProduct, hab i, hx, hy]
      simp [hdet]

/-- **Reusable lemma (total unimodularity of incidence-form matrices).** If
every row of a square integer matrix has the form `e_a - e_b` with
`a b : Option (Fin m)` (`none` read as the zero vector), then its determinant
is `-1`, `0` or `1`. -/
theorem det_eq_neg_one_or_zero_or_one_of_incRow {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ)
    (h : ∀ i, IncRow (M i)) : M.det = -1 ∨ M.det = 0 ∨ M.det = 1 := by
  have hle := abs_le.mp (abs_det_le_one_of_incRow M h)
  omega

/-- Induction step bookkeeping for `abs_det_le_two_pow`: if the rows indexed
by `S` are sums of two incidence-form rows and all other rows are in incidence
form, then `|det| ≤ 2 ^ S.card`.  Proved by splitting one row at a time with
`Matrix.det_updateRow_add`. -/
theorem abs_det_le_two_pow_card {m : ℕ} (S : Finset (Fin m)) :
    ∀ (M : Matrix (Fin m) (Fin m) ℤ),
      (∀ i ∈ S, ∃ r s : Fin m → ℤ, IncRow r ∧ IncRow s ∧ M i = r + s) →
      (∀ i ∉ S, IncRow (M i)) → |M.det| ≤ 2 ^ S.card := by
  induction S using Finset.induction_on with
  | empty =>
    intro M _ hout
    simpa using abs_det_le_one_of_incRow M (fun i => hout i (Finset.notMem_empty i))
  | insert i S hiS ih =>
    intro M hin hout
    obtain ⟨r, s, hr, hs, hrs⟩ := hin i (Finset.mem_insert_self i S)
    have hM : M = M.updateRow i (r + s) := by
      rw [← hrs, Matrix.updateRow_eq_self]
    have hbound : ∀ t : Fin m → ℤ, IncRow t → |(M.updateRow i t).det| ≤ 2 ^ S.card := by
      intro t ht
      apply ih
      · intro k hk
        have hki : k ≠ i := fun h => hiS (h ▸ hk)
        simpa [Matrix.updateRow_ne hki] using hin k (Finset.mem_insert_of_mem hk)
      · intro k hk
        by_cases hki : k = i
        · subst hki
          simpa using ht
        · have hk' : k ∉ insert i S := by simp [hki, hk]
          simpa [Matrix.updateRow_ne hki] using hout k hk'
    rw [hM, Matrix.det_updateRow_add, Finset.card_insert_of_notMem hiS, pow_succ, mul_two]
    exact (abs_add_le _ _).trans (add_le_add (hbound r hr) (hbound s hs))

/-- If every row of a square `m × m` integer matrix is the sum of two
incidence-form rows, then `|det| ≤ 2 ^ m`. -/
theorem abs_det_le_two_pow {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ)
    (h : ∀ i, ∃ r s : Fin m → ℤ, IncRow r ∧ IncRow s ∧ M i = r + s) : |M.det| ≤ 2 ^ m := by
  simpa using abs_det_le_two_pow_card Finset.univ M (fun i _ => h i)
    (fun i hi => absurd (Finset.mem_univ i) hi)

/-! ## The matrices of Conjecture 4 -/

/-- The `m × (m + 1)` matrix whose row `r` is `e_{I r} + e_{J r} - e_{K r}`
(coincidences allowed); this is the parametric form of the rows allowed in
Conjecture 4 (see `TyszkaRow.exists_eq`). -/
def tyszkaMatrix {m : ℕ} (I J K : Fin m → Fin (m + 1)) : Matrix (Fin m) (Fin (m + 1)) ℤ :=
  fun r t => (if I r = t then 1 else 0) + (if J r = t then 1 else 0) - (if K r = t then 1 else 0)

example : tyszkaMatrix (m := 1) ![1] ![1] ![0] = !![-1, 2] := by
  ext r t; fin_cases r; fin_cases t <;> rfl

/-- Conjecture 4 in parametric form: deleting any column of the matrix with
rows `e_{I r} + e_{J r} - e_{K r}` leaves a square matrix with
`|det| ≤ 2 ^ m`. -/
theorem abs_det_tyszkaMatrix_submatrix_le (m : ℕ) (I J K : Fin m → Fin (m + 1))
    (c : Fin (m + 1)) :
    |((tyszkaMatrix I J K).submatrix id c.succAbove).det| ≤ 2 ^ m := by
  apply abs_det_le_two_pow
  intro r
  have hJ : IncRow (fun t : Fin (m + 1) => if J r = t then (1 : ℤ) else 0) :=
    ⟨some (J r), none, by funext t; simp⟩
  have hIK : IncRow (fun t : Fin (m + 1) =>
      (if I r = t then (1 : ℤ) else 0) - (if K r = t then 1 else 0)) :=
    ⟨some (I r), some (K r), by funext t; simp⟩
  refine ⟨_, _, hJ.comp (Fin.succAbove_right_injective (p := c)),
    hIK.comp (Fin.succAbove_right_injective (p := c)), ?_⟩
  funext t
  simp only [Matrix.submatrix_apply, id, tyszkaMatrix, Pi.add_apply, Function.comp_apply]
  ring

/-! ## The row condition exactly as in the paper -/

/-- The six admissible zero-free row patterns of Conjecture 4:
`⟨1⟩, ⟨-1,2⟩, ⟨2,-1⟩, ⟨-1,1,1⟩, ⟨1,-1,1⟩, ⟨1,1,-1⟩`. -/
def tyszkaPatterns : List (List ℤ) :=
  [[1], [-1, 2], [2, -1], [-1, 1, 1], [1, -1, 1], [1, 1, -1]]

/-- A row `v` satisfies the hypothesis of Conjecture 4 if, after deleting all
zeros, it is one of the sequences in `tyszkaPatterns`. -/
def TyszkaRow {N : ℕ} (v : Fin N → ℤ) : Prop :=
  (List.ofFn v).filter (· ≠ 0) ∈ tyszkaPatterns

example : TyszkaRow ![0, 1, 0, -1, 1] := by unfold TyszkaRow; decide
example : TyszkaRow ![2, 0, -1] := by unfold TyszkaRow; decide
example : ¬ TyszkaRow ![2, 0] := by unfold TyszkaRow; decide
example : ¬ TyszkaRow ![0, 0, 0] := by unfold TyszkaRow; decide
example : ¬ TyszkaRow ![1, 1, 1] := by unfold TyszkaRow; decide

/-- Successor-shift of a position function, used to prepend a nonzero entry
in `filter_ne_zero_decomp`. -/
def consPos (pos : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => pos s + 1

/-- If the nonzero entries of a list `L`, in order, form the list `p`, then
`L` is the sum over `s < p.length` of `p[s]` placed at some position
`pos s < L.length`. -/
theorem filter_ne_zero_decomp : ∀ (L p : List ℤ), L.filter (· ≠ 0) = p →
    ∃ pos : ℕ → ℕ, (∀ s < p.length, pos s < L.length) ∧
      ∀ t, L.getD t 0 = ∑ s ∈ Finset.range p.length, if pos s = t then p.getD s 0 else 0 := by
  intro L
  induction L with
  | nil =>
    intro p hp
    obtain rfl : p = [] := by simpa using hp.symm
    exact ⟨id, by simp, by simp⟩
  | cons x L ih =>
    intro p hp
    by_cases hx : x = 0
    · subst hx
      have hp' : L.filter (· ≠ 0) = p := by simpa using hp
      obtain ⟨pos, hlt, hval⟩ := ih p hp'
      refine ⟨fun s => pos s + 1, fun s hs => by simpa using hlt s hs, ?_⟩
      intro t
      cases t with
      | zero => simp
      | succ t => rw [List.getD_cons_succ, hval t]; simp
    · have hp' : p = x :: L.filter (· ≠ 0) := by simp [← hp, hx]
      subst hp'
      obtain ⟨pos, hlt, hval⟩ := ih _ rfl
      refine ⟨consPos pos, ?_, ?_⟩
      · intro s hs
        cases s with
        | zero => simp [consPos]
        | succ s => simpa [consPos] using hlt s (by simpa using hs)
      · intro t
        rw [List.length_cons, Finset.sum_range_succ']
        cases t with
        | zero => simp [consPos]
        | succ t => rw [List.getD_cons_succ, hval t]; simp [consPos]

/-- Every row allowed by Conjecture 4 has the form `e_i + e_j - e_k`. -/
theorem TyszkaRow.exists_eq {N : ℕ} {v : Fin N → ℤ} (h : TyszkaRow v) :
    ∃ i j k : Fin N, v = fun t => (if i = t then 1 else 0) + (if j = t then 1 else 0) -
      (if k = t then 1 else 0) := by
  obtain ⟨pos, hlt, hval⟩ := filter_ne_zero_decomp (List.ofFn v) _ rfl
  have hv : ∀ t : Fin N, v t = ∑ s ∈ Finset.range ((List.ofFn v).filter (· ≠ 0)).length,
      if pos s = t then ((List.ofFn v).filter (· ≠ 0)).getD s 0 else 0 := by
    intro t
    rw [← hval]
    simp
  rw [List.length_ofFn] at hlt
  unfold TyszkaRow at h
  generalize ((List.ofFn v).filter (· ≠ 0)) = p at h hv hlt
  simp only [tyszkaPatterns, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨⟨pos 0, hlt 0 (by simp)⟩, ⟨pos 0, hlt 0 (by simp)⟩, ⟨pos 0, hlt 0 (by simp)⟩,
      funext fun t => ?_⟩
    rw [hv t]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fin.ext_iff, List.length_cons,
      List.length_nil, List.getD_cons_zero, zero_add]
    split_ifs <;> omega
  · refine ⟨⟨pos 1, hlt 1 (by simp)⟩, ⟨pos 1, hlt 1 (by simp)⟩, ⟨pos 0, hlt 0 (by simp)⟩,
      funext fun t => ?_⟩
    rw [hv t]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fin.ext_iff, List.length_cons,
      List.length_nil, List.getD_cons_zero, List.getD_cons_succ, zero_add]
    split_ifs <;> omega
  · refine ⟨⟨pos 0, hlt 0 (by simp)⟩, ⟨pos 0, hlt 0 (by simp)⟩, ⟨pos 1, hlt 1 (by simp)⟩,
      funext fun t => ?_⟩
    rw [hv t]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fin.ext_iff, List.length_cons,
      List.length_nil, List.getD_cons_zero, List.getD_cons_succ, zero_add]
    split_ifs <;> omega
  · refine ⟨⟨pos 1, hlt 1 (by simp)⟩, ⟨pos 2, hlt 2 (by simp)⟩, ⟨pos 0, hlt 0 (by simp)⟩,
      funext fun t => ?_⟩
    rw [hv t]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fin.ext_iff, List.length_cons,
      List.length_nil, List.getD_cons_zero, List.getD_cons_succ, zero_add]
    split_ifs <;> omega
  · refine ⟨⟨pos 0, hlt 0 (by simp)⟩, ⟨pos 2, hlt 2 (by simp)⟩, ⟨pos 1, hlt 1 (by simp)⟩,
      funext fun t => ?_⟩
    rw [hv t]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fin.ext_iff, List.length_cons,
      List.length_nil, List.getD_cons_zero, List.getD_cons_succ, zero_add]
    split_ifs <;> omega
  · refine ⟨⟨pos 0, hlt 0 (by simp)⟩, ⟨pos 1, hlt 1 (by simp)⟩, ⟨pos 2, hlt 2 (by simp)⟩,
      funext fun t => ?_⟩
    rw [hv t]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fin.ext_iff, List.length_cons,
      List.length_nil, List.getD_cons_zero, List.getD_cons_succ, zero_add]
    split_ifs <;> omega

/-- **Conjecture 4 of Tyszka (math/0702558).**  Let `B` be an integer matrix
with `m` rows and `m + 1` columns (the paper's `n - 1` and `n`), each row of
which, after deleting all zeros, is one of `⟨1⟩, ⟨-1,2⟩, ⟨2,-1⟩, ⟨-1,1,1⟩,
⟨1,-1,1⟩, ⟨1,1,-1⟩`.  Then after deleting any column `c` of `B`, the
resulting square matrix has determinant of absolute value at most `2 ^ m`
(the paper's `2^(n-1)`). -/
theorem conjecture_4 (m : ℕ) (B : Matrix (Fin m) (Fin (m + 1)) ℤ) (hB : ∀ r, TyszkaRow (B r))
    (c : Fin (m + 1)) : |(B.submatrix id c.succAbove).det| ≤ 2 ^ m := by
  choose I J K hIJK using fun r => (hB r).exists_eq
  have hBeq : B = tyszkaMatrix I J K := by
    ext r t
    rw [hIJK r]
    rfl
  rw [hBeq]
  exact abs_det_tyszkaMatrix_submatrix_le m I J K c

/-- The hypotheses of `conjecture_4` are satisfiable and the bound is sharp:
for `m = 2`, the rows `⟨-1, 2, 0⟩` and `⟨-1, 0, 2⟩` are admissible and deleting
column `0` leaves `2 • 1`, of determinant `4 = 2 ^ 2`. -/
example :
    (∀ r, TyszkaRow ((!![-1, 2, 0; -1, 0, 2] : Matrix (Fin 2) (Fin 3) ℤ) r)) ∧
      ((!![-1, 2, 0; -1, 0, 2] : Matrix (Fin 2) (Fin 3) ℤ).submatrix id
        (0 : Fin 3).succAbove).det = 2 ^ 2 := by
  refine ⟨fun r => ?_, ?_⟩
  · fin_cases r <;> (unfold TyszkaRow; decide)
  · rw [Matrix.det_fin_two]
    rfl

end Candidates.TyszkaDeterminantConjecture
