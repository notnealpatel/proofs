import BilinearComplexity.SchemeAction

set_option autoImplicit false

namespace BilinearComplexity.Scheme.Action

variable {k : Type*} [CommSemiring k] {n₁ n₂ n₃ r : ℕ}

private theorem kernel_congr {α β γ δ ε ζ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (A : δ → α → k) (B : ε → β → k) (C : ζ → γ → k)
    (u u' : α → k) (v v' : β → k) (w w' : γ → k)
    (h : ∀ i j l, u i * v j * w l = u' i * v' j * w' l) :
    ∀ x y z, (∑ i, A x i * u i) * (∑ j, B y j * v j) * (∑ l, C z l * w l) =
      (∑ i, A x i * u' i) * (∑ j, B y j * v' j) * (∑ l, C z l * w' l) := by
  intro x y z
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = (A x i * B y j * C z l) * (u i * v j * w l) := by ac_rfl
    _ = (A x i * B y j * C z l) * (u' i * v' j * w' l) := by rw [h]
    _ = _ := by ac_rfl

private theorem mul_entry {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) k) (B : Matrix (Fin n) (Fin n) k)
    (U : Matrix (Fin m) (Fin n) k) (i : Fin m) (j : Fin n) :
    (A * U * B) i j = ∑ p : Fin m × Fin n, (A i p.1 * B p.2 j) * U p.1 p.2 := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ac_rfl

private theorem sandwich_eval_congr (S T : MatrixScheme k n₁ n₂ n₃ r)
    (d : Sandwich k n₁ n₂ n₃) (s t : Fin r)
    (h : (S.term s).eval = (T.term t).eval) :
    ((sandwich S d).term s).eval = ((sandwich T d).term t).eval := by
  have he : ∀ (p : Fin n₁ × Fin n₂) (q : Fin n₂ × Fin n₃) (z : Fin n₃ × Fin n₁),
      reshapeVector (S.term s).1 p.1 p.2 * reshapeVector (S.term s).2.1 q.1 q.2 *
        reshapeVector (S.term s).2.2 z.1 z.2 =
      reshapeVector (T.term t).1 p.1 p.2 * reshapeVector (T.term t).2.1 q.1 q.2 *
        reshapeVector (T.term t).2.2 z.1 z.2 := by
    intro p q z
    exact congrFun (congrFun (congrFun h (matrixIndexEquiv _ _ p))
      (matrixIndexEquiv _ _ q)) (matrixIndexEquiv _ _ z)
  funext x y z
  obtain ⟨⟨i,j⟩, rfl⟩ := (matrixIndexEquiv n₁ n₂).surjective x
  obtain ⟨⟨j',l⟩, rfl⟩ := (matrixIndexEquiv n₂ n₃).surjective y
  obtain ⟨⟨l',i'⟩, rfl⟩ := (matrixIndexEquiv n₃ n₁).surjective z
  simp only [sandwich, TriadData.eval, triad]
  change matrixEntry (flattenMatrix _) i j * matrixEntry (flattenMatrix _) j' l *
    matrixEntry (flattenMatrix _) l' i' =
    matrixEntry (flattenMatrix _) i j * matrixEntry (flattenMatrix _) j' l *
    matrixEntry (flattenMatrix _) l' i'
  simp only [flattenMatrix_entry, mul_entry]
  exact kernel_congr
    (fun x p => d.P x.1 p.1 * d.QInv p.2 x.2)
    (fun y q => d.Q y.1 q.1 * d.RInv q.2 y.2)
    (fun z v => d.R z.1 v.1 * d.PInv v.2 z.2)
    _ _ _ _ _ _ he (i,j) (j',l) (l',i')

omit [CommSemiring k] in
private theorem reshape_flatten {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) :
    reshapeVector (flattenMatrix M) = M :=
  (matrixVectorEquiv k m n).symm_apply_apply M

omit [CommSemiring k] in
private theorem flatten_reshape {m n : ℕ} (u : Fin (m * n) → k) :
    flattenMatrix (reshapeVector u) = u :=
  (matrixVectorEquiv k m n).apply_symm_apply u

private theorem sandwich_eval_reflect (S T : MatrixScheme k n₁ n₂ n₃ r)
    (d : Sandwich k n₁ n₂ n₃) (s t : Fin r)
    (h : ((sandwich S d).term s).eval = ((sandwich T d).term t).eval) :
    (S.term s).eval = (T.term t).eval := by
  let e : Sandwich k n₁ n₂ n₃ :=
    ⟨d.PInv, d.P, d.QInv, d.Q, d.RInv, d.R,
      d.P_mul_PInv, d.PInv_mul_P, d.Q_mul_QInv, d.QInv_mul_Q,
      d.R_mul_RInv, d.RInv_mul_R⟩
  have hi (X : MatrixScheme k n₁ n₂ n₃ r) : sandwich (sandwich X d) e = X := by
    cases X with
    | mk term =>
      simp only [sandwich, e, reshape_flatten]
      congr 1
      funext v
      simp only [← Matrix.mul_assoc, d.PInv_mul_P, d.QInv_mul_Q, d.RInv_mul_R,
        Matrix.one_mul]
      simp only [Matrix.mul_assoc, d.QInv_mul_Q, d.RInv_mul_R, d.PInv_mul_P,
        Matrix.mul_one, flatten_reshape]
  have hh := sandwich_eval_congr (sandwich S d) (sandwich T d) e s t h
  simpa only [hi S, hi T] using hh

omit [CommSemiring k] in
private theorem transpose_apply {a b : ℕ} (u : Fin (a * b) → k)
    (j : Fin b) (i : Fin a) :
    transposeFactor u (matrixIndexEquiv b a (j,i)) = u (matrixIndexEquiv a b (i,j)) :=
  matrixEntry_transposeFactor u j i

private theorem orient_eval_reflect (S T : MatrixScheme k n₁ n₂ n₃ r)
    (o : Orientation) (s t : Fin r)
    (h : ((orientMatrix o S).term s).eval = ((orientMatrix o T).term t).eval) :
    (S.term s).eval = (T.term t).eval := by
  funext x y z
  obtain ⟨⟨i,j⟩, rfl⟩ := (matrixIndexEquiv n₁ n₂).surjective x
  obtain ⟨⟨j',l⟩, rfl⟩ := (matrixIndexEquiv n₂ n₃).surjective y
  obtain ⟨⟨l',i'⟩, rfl⟩ := (matrixIndexEquiv n₃ n₁).surjective z
  cases o with
  | abc =>
      have hh := congrFun (congrFun (congrFun h
        (matrixIndexEquiv n₁ n₂ (i,j)))
        (matrixIndexEquiv n₂ n₃ (j',l)))
        (matrixIndexEquiv n₃ n₁ (l',i'))
      simp only [orientMatrix, Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim, TriadData.eval, triad] at hh
      simpa only [TriadData.eval, triad, matrixEntry, mul_comm, mul_left_comm, mul_assoc] using hh
  | bca =>
      have hh := congrFun (congrFun (congrFun h
        (matrixIndexEquiv n₂ n₃ (j',l)))
        (matrixIndexEquiv n₃ n₁ (l',i')))
        (matrixIndexEquiv n₁ n₂ (i,j))
      simp only [orientMatrix, Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim, TriadData.eval, triad] at hh
      simpa only [TriadData.eval, triad, matrixEntry, mul_comm, mul_left_comm, mul_assoc] using hh
  | cab =>
      have hh := congrFun (congrFun (congrFun h
        (matrixIndexEquiv n₃ n₁ (l',i')))
        (matrixIndexEquiv n₁ n₂ (i,j)))
        (matrixIndexEquiv n₂ n₃ (j',l))
      simp only [orientMatrix, Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim, TriadData.eval, triad] at hh
      simpa only [TriadData.eval, triad, matrixEntry, mul_comm, mul_left_comm, mul_assoc] using hh
  | acb =>
      have hh := congrFun (congrFun (congrFun h
        (matrixIndexEquiv n₁ n₃ (i',l')))
        (matrixIndexEquiv n₃ n₂ (l,j')))
        (matrixIndexEquiv n₂ n₁ (j,i))
      simp only [orientMatrix, Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim, TriadData.eval, triad] at hh
      rw [transpose_apply (S.term s).2.2 i' l', transpose_apply (T.term t).2.2 i' l', transpose_apply (S.term s).2.1 l j', transpose_apply (T.term t).2.1 l j', transpose_apply (S.term s).1 j i, transpose_apply (T.term t).1 j i] at hh
      simpa only [TriadData.eval, triad, matrixEntry, mul_comm, mul_left_comm, mul_assoc] using hh
  | cba =>
      have hh := congrFun (congrFun (congrFun h
        (matrixIndexEquiv n₃ n₂ (l,j')))
        (matrixIndexEquiv n₂ n₁ (j,i)))
        (matrixIndexEquiv n₁ n₃ (i',l'))
      simp only [orientMatrix, Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim, TriadData.eval, triad] at hh
      rw [transpose_apply (S.term s).2.1 l j', transpose_apply (T.term t).2.1 l j', transpose_apply (S.term s).1 j i, transpose_apply (T.term t).1 j i, transpose_apply (S.term s).2.2 i' l', transpose_apply (T.term t).2.2 i' l'] at hh
      simpa only [TriadData.eval, triad, matrixEntry, mul_comm, mul_left_comm, mul_assoc] using hh
  | bac =>
      have hh := congrFun (congrFun (congrFun h
        (matrixIndexEquiv n₂ n₁ (j,i)))
        (matrixIndexEquiv n₁ n₃ (i',l')))
        (matrixIndexEquiv n₃ n₂ (l,j'))
      simp only [orientMatrix, Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim, TriadData.eval, triad] at hh
      rw [transpose_apply (S.term s).1 j i, transpose_apply (T.term t).1 j i, transpose_apply (S.term s).2.2 i' l', transpose_apply (T.term t).2.2 i' l', transpose_apply (S.term s).2.1 l j', transpose_apply (T.term t).2.1 l j'] at hh
      simpa only [TriadData.eval, triad, matrixEntry, mul_comm, mul_left_comm, mul_assoc] using hh

private theorem zero_sandwich_eval (d : Sandwich k n₁ n₂ n₃) (s : Fin r) :
    ((sandwich (⟨fun _ => (0,0,0)⟩ : MatrixScheme k n₁ n₂ n₃ r) d).term s).eval = 0 := by
  have hz {m n : ℕ} : reshapeVector (0 : Fin (m * n) → k) = 0 := rfl
  have hf {m n : ℕ} : flattenMatrix (0 : Matrix (Fin m) (Fin n) k) = 0 := rfl
  simp only [sandwich, hz, Matrix.mul_zero, Matrix.zero_mul, hf]
  funext i j l
  simp [TriadData.eval, triad]

private theorem zero_orient_eval (o : Orientation) (s : Fin r) :
    ((orientMatrix o (⟨fun _ => (0,0,0)⟩ : MatrixScheme k n₁ n₂ n₃ r)).term s).eval = 0 := by
  cases o <;>
    simp only [orientMatrix, Orientation.firstDim, Orientation.secondDim, Orientation.thirdDim]
  all_goals
    change triad _ _ _ = 0
    funext i j l
    change (0 : k) * 0 * 0 = 0
    simp

/-- An invertible sandwich preserves exact matrix multiplication, nonzero evaluated terms,
and pairwise distinct evaluated terms, including in zero dimensions. -/
theorem Valid.sandwich {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.Valid (matMulTensor k n₁ n₂ n₃)) (d : Sandwich k n₁ n₂ n₃) :
    (Action.sandwich S d).Valid (matMulTensor k n₁ n₂ n₃) := by
  refine ⟨(brent_iff_sumTensor_eq_matMulTensor _).mp
    (Brent.sandwich ((brent_iff_sumTensor_eq_matMulTensor S).mpr hS.1) d), ?_, ?_⟩
  · intro s hzero
    let Z : MatrixScheme k n₁ n₂ n₃ r := ⟨fun _ => (0,0,0)⟩
    have he : ((Action.sandwich S d).term s).eval = ((Action.sandwich Z d).term s).eval :=
      hzero.trans (zero_sandwich_eval d s).symm
    have hs := sandwich_eval_reflect S Z d s s he
    apply hS.2.1 s
    have hz : (Z.term s).eval = 0 := by
      funext i j l
      change (0 : k) * 0 * 0 = 0
      simp
    exact hs.trans hz
  · intro s t hst
    exact hS.2.2 (sandwich_eval_reflect S S d s t hst)

/-- Physical vertex orientation, including all three transposes in odd orientations,
preserves exact matrix multiplication and both evaluated-term validity conditions. -/
theorem Valid.orientMatrix {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.Valid (matMulTensor k n₁ n₂ n₃)) (o : Orientation) :
    (Action.orientMatrix o S).Valid (matMulTensor k (o.firstDim n₁ n₂ n₃)
      (o.secondDim n₁ n₂ n₃) (o.thirdDim n₁ n₂ n₃)) := by
  refine ⟨(brent_iff_sumTensor_eq_matMulTensor _).mp
    (Brent.orientMatrix ((brent_iff_sumTensor_eq_matMulTensor S).mpr hS.1) o), ?_, ?_⟩
  · intro s hzero
    let Z : MatrixScheme k n₁ n₂ n₃ r := ⟨fun _ => (0,0,0)⟩
    have he : ((Action.orientMatrix o S).term s).eval = ((Action.orientMatrix o Z).term s).eval :=
      hzero.trans (zero_orient_eval o s).symm
    have hs := orient_eval_reflect S Z o s s he
    apply hS.2.1 s
    have hz : (Z.term s).eval = 0 := by
      funext i j l
      change (0 : k) * 0 * 0 = 0
      simp
    exact hs.trans hz
  · intro s t hst
    exact hS.2.2 (orient_eval_reflect S S o s t hst)

/-- Product-one gauges preserve all three conjuncts of validity for any tensor. -/
theorem Valid.gauge {a b c : ℕ} {X : Tensor k a b c} {S : Scheme k a b c r}
    (hS : S.Valid X) (g : Fin r → Gauge k) : (Action.gauge S g).Valid X := by
  refine ⟨(sumTensor_gauge S g).trans hS.1, ?_, ?_⟩
  · intro s
    simpa only [TermNonzero, eval_gauge] using hS.2.1 s
  · intro s t hst
    exact hS.2.2 (by simpa only [eval_gauge] using hst)

/-- Computed standard action replay preserves the full validity predicate in the
explicit oriented matrix-multiplication shape, with no dimension or nontriviality guard. -/
theorem Valid.replay {S : MatrixScheme k n₁ n₂ n₃ r}
    (hS : S.Valid (matMulTensor k n₁ n₂ n₃)) (o : Orientation)
    (x : Replay (k := k) n₁ n₂ n₃ r o) :
    (Action.replay o S x).Valid (matMulTensor k (o.firstDim n₁ n₂ n₃)
      (o.secondDim n₁ n₂ n₃) (o.thirdDim n₁ n₂ n₃)) := by
  exact Valid.gauge
    (Scheme.Valid.permute (Valid.sandwich (Valid.orientMatrix hS o) x.sandwich)
      x.permutation) x.gauges

/-- An arbitrary exact replay witness transports all three validity conjuncts from
its source to its target, not merely the Brent equations. -/
theorem ReplayWitness.valid {S : MatrixScheme k n₁ n₂ n₃ r} {o : Orientation}
    {T : MatrixScheme k (o.firstDim n₁ n₂ n₃) (o.secondDim n₁ n₂ n₃)
      (o.thirdDim n₁ n₂ n₃) r} (h : ReplayWitness S o T)
    (hS : S.Valid (matMulTensor k n₁ n₂ n₃)) :
    T.Valid (matMulTensor k (o.firstDim n₁ n₂ n₃)
      (o.secondDim n₁ n₂ n₃) (o.thirdDim n₁ n₂ n₃)) := by
  rw [h.target_eq_replay]
  exact Valid.replay hS o h.data

namespace AsymmetricReplay

/-- The explicit asymmetric source is valid: its two evaluated summands are nonzero
and distinct, as well as satisfying the already checked Brent equations. -/
theorem source_valid : source.Valid (matMulTensor (ZMod 3) 1 2 1) := by
  refine ⟨(brent_iff_sumTensor_eq_matMulTensor source).mp source_replayableBrent.2, ?_, ?_⟩
  · unfold TermNonzero source TriadData.eval triad
    decide
  · decide

/-- The independently specified asymmetric target inherits full validity through its
nonidentity exact replay witness. -/
theorem target_valid : target.Valid (matMulTensor (ZMod 3) 2 1 1) :=
  witness.valid source_valid

example : Nonempty (ReplayWitness source orientation target) ∧
    source.Valid (matMulTensor (ZMod 3) 1 2 1) :=
  ⟨⟨witness⟩, source_valid⟩

end AsymmetricReplay

end BilinearComplexity.Scheme.Action
