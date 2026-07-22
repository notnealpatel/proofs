/-
  BilinearComplexity/PeelingSplit — the S2 splitting lemma.

  Card Ss1: if the last term of a decomposition is a triad τ whose eval
  can be written as τ₁.eval + τ₂.eval, and the nnz of the "remainder"
  triad τ₂ is at most p, then replacing τ with [τ₁, τ₂] gives a
  decomposition of length r + 1 with peak ≤ p.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Proofs.BilinearComplexity.PeelingMoves

namespace BilinearComplexity

open CharTwo

variable {k : Type*} [DecidableEq k] [CommRing k] [CharP k 2] {a b c : ℕ}

/-! ## 1. Splitting a decomposition at the last term -/

omit [DecidableEq k] [CharP k 2] in
/-- Replacing the last triad with two triads whose evals sum to it
preserves the decomposition. -/
theorem isDecomp_split_last {T : Tensor k a b c}
    {L : Decomp k a b c} {τ τ₁ τ₂ : TriadData k a b c}
    (hD : IsDecomp T (L ++ [τ]))
    (hSplit : ∀ i j l, τ₁.eval i j l + τ₂.eval i j l = τ.eval i j l) :
    IsDecomp T (L ++ [τ₁, τ₂]) := by
  simp only [IsDecomp] at hD ⊢
  rw [decompSum_append] at hD ⊢
  funext i j l
  have hD' := congr_fun (congr_fun (congr_fun hD i) j) l
  simp only [decompSum, Pi.zero_apply, add_zero] at hD' ⊢
  rw [hSplit]
  exact hD'

omit [DecidableEq k] in
/-- The residual at `L` for a valid decomposition `L ++ [τ]` equals `τ.eval`. -/
theorem residual_eq_last {T : Tensor k a b c}
    {L : Decomp k a b c} {τ : TriadData k a b c}
    (hD : IsDecomp T (L ++ [τ])) :
    residual T L = τ.eval := by
  have h0 := residual_of_isDecomp hD
  rw [residual_append] at h0
  -- h0 : residual (residual T L) [τ] = 0
  -- residual R [τ] = fun i j l => R i j l - τ.eval i j l
  funext i j l
  have h1 : (residual T L) i j l - τ.eval i j l = (0 : k) := by
    have := congr_fun (congr_fun (congr_fun h0 i) j) l
    simpa [residual] using this
  exact sub_eq_zero.mp h1

/-- Peak bound after splitting the last triad: the peak of the new
decomposition is at most `max (peak T L) (nnz τ₂.eval)`.
Since `peak T (L ++ [τ]) = peak T L` (the last step zeros out), this
means the peak only increases if `nnz τ₂.eval` exceeds the original peak. -/
theorem peak_split_last_le {T : Tensor k a b c}
    {L : Decomp k a b c} {τ τ₁ τ₂ : TriadData k a b c}
    (hD : IsDecomp T (L ++ [τ]))
    (hSplit : ∀ i j l, τ₁.eval i j l + τ₂.eval i j l = τ.eval i j l)
    {p : ℕ} (hp : peak T (L ++ [τ]) ≤ p)
    (hnnz : nnz τ₂.eval ≤ p) :
    peak T (L ++ [τ₁, τ₂]) ≤ p := by
  -- Step 1: peak T (L ++ [τ]) = peak T L (last step zeros out)
  have hResL := residual_eq_last hD
  have hPeakOrig : peak T L ≤ p := by
    rw [peak_append] at hp
    -- peak (residual T L) [τ] = 0 since residual T L = τ.eval
    -- and τ.eval - τ.eval = 0
    have : peak (residual T L) [τ] = 0 := by
      show [nnz fun i j l => (residual T L) i j l - τ.eval i j l].foldl max 0 = 0
      have hzero : (fun i j l => (residual T L) i j l - τ.eval i j l) = (0 : Tensor k a b c) := by
        rw [hResL]; funext i j l; simp
      rw [hzero, nnz_zero]; simp
    omega
  -- Step 2: peak T (L ++ [τ₁, τ₂]) = max (peak T L) (peak (residual T L) [τ₁, τ₂])
  rw [peak_append]
  -- Step 3: Compute peak (residual T L) [τ₁, τ₂]
  -- residual T L = τ.eval, so the trajectory is [nnz τ₂.eval, nnz 0]
  have hTraj : peak (residual T L) [τ₁, τ₂] = nnz τ₂.eval := by
    show [nnz fun i j l => (residual T L) i j l - τ₁.eval i j l,
         nnz fun i j l => ((residual T L) i j l - τ₁.eval i j l) - τ₂.eval i j l].foldl max 0 = _
    have h1 : (fun i j l => (residual T L) i j l - τ₁.eval i j l) = τ₂.eval := by
      rw [hResL]; funext i j l
      rw [← hSplit i j l, add_sub_cancel_left]
    have h2 : (fun i j l => ((residual T L) i j l - τ₁.eval i j l) - τ₂.eval i j l) =
        (0 : Tensor k a b c) := by
      funext i j l
      simp only [Pi.zero_apply]
      have h1' := congr_fun (congr_fun (congr_fun h1 i) j) l
      rw [h1']
      exact sub_self _
    rw [h1, h2, nnz_zero]; simp
  rw [hTraj]
  exact Nat.max_le.mpr ⟨hPeakOrig, hnnz⟩

/-! ## 2. Triad splitting along the first factor -/

omit [DecidableEq k] [CharP k 2] in
/-- Splitting a triad along the first factor: `triad (u₁ + u₂) v w`
equals `triad u₁ v w + triad u₂ v w` entrywise. -/
theorem triad_add_left (u₁ u₂ : Fin a → k) (v : Fin b → k) (w : Fin c → k) :
    ∀ i j l, triad (u₁ + u₂) v w i j l =
      triad u₁ v w i j l + triad u₂ v w i j l := by
  intro i j l
  simp [triad, Pi.add_apply, add_mul]

/-- The S2 splitting lemma (first-factor variant):
if `L ++ [triad u v w]` is a decomposition of `T` with `peak ≤ p`,
and `u = u₁ + u₂`, and `nnz (triad u₂ v w) ≤ p`, then
`L ++ [triad u₁ v w, triad u₂ v w]` is a decomposition of length
`L.length + 2` with `peak ≤ p`. -/
theorem split_last_first_factor {T : Tensor k a b c}
    {L : Decomp k a b c}
    {u u₁ u₂ : Fin a → k} {v : Fin b → k} {w : Fin c → k}
    (hD : IsDecomp T (L ++ [(u, v, w)]))
    (hSplit : u = u₁ + u₂)
    {p : ℕ} (hp : peak T (L ++ [(u, v, w)]) ≤ p)
    (hnnz : nnz (triad u₂ v w) ≤ p) :
    IsDecomp T (L ++ [(u₁, v, w), (u₂, v, w)]) ∧
    peak T (L ++ [(u₁, v, w), (u₂, v, w)]) ≤ p := by
  have hEvalSplit : ∀ i j l,
      TriadData.eval (u₁, v, w) i j l + TriadData.eval (u₂, v, w) i j l =
      TriadData.eval (u, v, w) i j l := by
    intro i j l
    simp only [TriadData.eval, triad]
    rw [hSplit, Pi.add_apply, add_mul, add_mul]
  constructor
  · exact isDecomp_split_last hD hEvalSplit
  · exact peak_split_last_le hD hEvalSplit hp hnnz

omit [DecidableEq k] [CharP k 2] in
/-- Splitting a triad along the second factor. -/
theorem triad_add_mid (u : Fin a → k) (v₁ v₂ : Fin b → k) (w : Fin c → k) :
    ∀ i j l, triad u (v₁ + v₂) w i j l =
      triad u v₁ w i j l + triad u v₂ w i j l := by
  intro i j l
  simp only [triad, Pi.add_apply, mul_add, add_mul]

omit [DecidableEq k] [CharP k 2] in
/-- Splitting a triad along the third factor. -/
theorem triad_add_right (u : Fin a → k) (v : Fin b → k) (w₁ w₂ : Fin c → k) :
    ∀ i j l, triad u v (w₁ + w₂) i j l =
      triad u v w₁ i j l + triad u v w₂ i j l := by
  intro i j l
  simp only [triad, Pi.add_apply, mul_add, add_mul]

/-- The S2 splitting lemma (second-factor variant). -/
theorem split_last_second_factor {T : Tensor k a b c}
    {L : Decomp k a b c}
    {u : Fin a → k} {v v₁ v₂ : Fin b → k} {w : Fin c → k}
    (hD : IsDecomp T (L ++ [(u, v, w)]))
    (hSplit : v = v₁ + v₂)
    {p : ℕ} (hp : peak T (L ++ [(u, v, w)]) ≤ p)
    (hnnz : nnz (triad u v₂ w) ≤ p) :
    IsDecomp T (L ++ [(u, v₁, w), (u, v₂, w)]) ∧
    peak T (L ++ [(u, v₁, w), (u, v₂, w)]) ≤ p := by
  have hEvalSplit : ∀ i j l,
      TriadData.eval (u, v₁, w) i j l + TriadData.eval (u, v₂, w) i j l =
      TriadData.eval (u, v, w) i j l := by
    intro i j l
    simp only [TriadData.eval, triad]
    rw [hSplit, Pi.add_apply, mul_add, add_mul, add_mul]
  exact ⟨isDecomp_split_last hD hEvalSplit, peak_split_last_le hD hEvalSplit hp hnnz⟩

/-- The S2 splitting lemma (third-factor variant). -/
theorem split_last_third_factor {T : Tensor k a b c}
    {L : Decomp k a b c}
    {u : Fin a → k} {v : Fin b → k} {w w₁ w₂ : Fin c → k}
    (hD : IsDecomp T (L ++ [(u, v, w)]))
    (hSplit : w = w₁ + w₂)
    {p : ℕ} (hp : peak T (L ++ [(u, v, w)]) ≤ p)
    (hnnz : nnz (triad u v w₂) ≤ p) :
    IsDecomp T (L ++ [(u, v, w₁), (u, v, w₂)]) ∧
    peak T (L ++ [(u, v, w₁), (u, v, w₂)]) ≤ p := by
  have hEvalSplit : ∀ i j l,
      TriadData.eval (u, v, w₁) i j l + TriadData.eval (u, v, w₂) i j l =
      TriadData.eval (u, v, w) i j l := by
    intro i j l
    simp only [TriadData.eval, triad]
    rw [hSplit, Pi.add_apply]; ring
  exact ⟨isDecomp_split_last hD hEvalSplit, peak_split_last_le hD hEvalSplit hp hnnz⟩

end BilinearComplexity
