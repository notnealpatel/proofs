/-
  BilinearComplexity/PeelingMoves — structural moves on decompositions.

  Card Sd1: the S1 duplication lemma — appending a weight-1 triad twice
  in characteristic 2 preserves the decomposition and keeps the peak
  bounded by `max p 1`.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Proofs.BilinearComplexity.Peeling
import Mathlib.Algebra.CharP.Two

namespace BilinearComplexity

open CharTwo

variable {k : Type*} [DecidableEq k] [CommRing k] [CharP k 2] {a b c : ℕ}

/-! ## Helpers: residual and trajectory interact with append -/

omit [DecidableEq k] [CharP k 2] in
/-- `residual T (L ++ L') = residual (residual T L) L'`. -/
theorem residual_append (T : Tensor k a b c) (L L' : Decomp k a b c) :
    residual T (L ++ L') = residual (residual T L) L' := by
  induction L generalizing T with
  | nil => rfl
  | cons t ts ih => exact ih _

omit [CharP k 2] in
/-- `nnzTrajectory T (L ++ L')` splits as the trajectory of L
followed by the trajectory of L' starting from `residual T L`. -/
theorem nnzTrajectory_append (T : Tensor k a b c) (L L' : Decomp k a b c) :
    nnzTrajectory T (L ++ L') =
      nnzTrajectory T L ++ nnzTrajectory (residual T L) L' := by
  induction L generalizing T with
  | nil => rfl
  | cons t ts ih => simp only [List.cons_append, nnzTrajectory, List.cons_append]; exact congrArg _ (ih _)

private theorem foldl_max_append (xs ys : List ℕ) (init : ℕ) :
    (xs ++ ys).foldl max init = ys.foldl max (xs.foldl max init) :=
  List.foldl_append ..

private theorem foldl_max_split (xs : List ℕ) (init : ℕ) :
    xs.foldl max init = max init (xs.foldl max 0) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (max 0 x)]
    omega

omit [CharP k 2] in
/-- The peak of a concatenation is the max of the two sub-peaks. -/
theorem peak_append (T : Tensor k a b c) (L L' : Decomp k a b c) :
    peak T (L ++ L') = max (peak T L) (peak (residual T L) L') := by
  simp only [peak, nnzTrajectory_append, foldl_max_append]
  exact foldl_max_split _ _

omit [DecidableEq k] [CharP k 2] in
/-- `decompSum (L ++ L')` = `decompSum L + decompSum L'` entrywise. -/
theorem decompSum_append (L L' : Decomp k a b c) :
    decompSum (L ++ L') = fun i j l =>
      decompSum L i j l + decompSum L' i j l := by
  induction L with
  | nil =>
    funext i j l
    simp [decompSum]
  | cons t ts ih =>
    funext i j l
    simp only [List.cons_append, decompSum]
    rw [congr_fun (congr_fun (congr_fun ih i) j) l, add_assoc]

/-- The residual of a valid decomposition is zero. -/
theorem residual_of_isDecomp {T : Tensor k a b c} {L : Decomp k a b c}
    (h : IsDecomp T L) : residual T L = 0 := by
  sorry

/-! ## The S1 duplication lemma -/

/-- Appending any triad twice preserves a decomposition in characteristic 2:
the two copies cancel. -/
theorem isDecomp_append_double {T : Tensor k a b c} {L : Decomp k a b c}
    (h : IsDecomp T L) (τ : TriadData k a b c) :
    IsDecomp T (L ++ [τ, τ]) := by
  sorry

/-- The peak bound for the S1 duplication move: if the original peak is
at most `p`, then appending a triad `τ` twice gives peak ≤ `max p (nnz τ.eval)`.
In particular, for a weight-1 triad (`nnz τ.eval = 1`), the bound is `max p 1`. -/
theorem peak_append_double_le {T : Tensor k a b c} {L : Decomp k a b c}
    (h : IsDecomp T L) (τ : TriadData k a b c) {p : ℕ} (hp : peak T L ≤ p) :
    peak T (L ++ [τ, τ]) ≤ max p (nnz τ.eval) := by
  sorry

end BilinearComplexity
