/-
  BilinearComplexity/FlipQuantum/Phase4FiniteQuery — a finite, amplitude-level quantum
  query model for marked flip-graph vertices.

  A state is an explicit complex amplitude vector.  Finite-basis operations use
  `Fintype`, while search algorithms additionally require a nonempty basis.  A
  `Unitary` is represented by a finite matrix together with its norm-mass
  preservation law.  Query algorithms alternate an initial oracle-free
  unitary with one phase-oracle call and one oracle-free unitary per round.
  No asymptotic search or quantum-walk claim is made here.
-/
import BilinearComplexity.FlipQuantum.Phase2Algebra

set_option autoImplicit false

namespace BilinearComplexity.FlipQuantum

namespace Quantum

/-- An amplitude vector on basis labels `ι`; normalization is a separate
predicate because linear evolution also acts on arbitrary vectors. -/
abbrev State (ι : Type*) := ι → ℂ

/-- The total Born mass of a state is the finite sum of squared amplitude norms. -/
def mass {ι : Type*} [Fintype ι] (ψ : State ι) : ℝ :=
  ∑ x, Complex.normSq (ψ x)

/-- A finite pure state is normalized when its total Born mass is exactly one. -/
def Normalized {ι : Type*} [Fintype ι] (ψ : State ι) : Prop :=
  mass ψ = 1

/-- A finite matrix acts on amplitudes by ordinary matrix-vector multiplication. -/
def matrixAction {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (ψ : State ι) : State ι :=
  Matrix.mulVec M ψ

/-- A finite unitary evolution is an explicit complex matrix whose action
preserves total Born mass on every input state.  Matrix action supplies
complex linearity; in finite dimension, a linear norm-preserver is unitary. -/
structure Unitary (ι : Type*) [Fintype ι] where
  /-- Matrix entries in the exposed finite computational basis. -/
  matrix : Matrix ι ι ℂ
  /-- The explicit norm-mass preservation obligation. -/
  preserves_mass : ∀ ψ : State ι, mass (matrixAction matrix ψ) = mass ψ

/-- Apply a finite unitary's matrix to a state. -/
def Unitary.apply {ι : Type*} [Fintype ι]
    (U : Unitary ι) (ψ : State ι) : State ι :=
  matrixAction U.matrix ψ

/-- Matrix action, and hence every represented unitary action, is additive. -/
theorem matrixAction_add {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (ψ φ : State ι) :
    matrixAction M (ψ + φ) = matrixAction M ψ + matrixAction M φ := by
  funext x
  simp only [matrixAction, Matrix.mulVec, dotProduct, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

/-- Matrix action, and hence every represented unitary action, commutes with
complex scalar multiplication. -/
theorem matrixAction_smul {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (q : ℂ) (ψ : State ι) :
    matrixAction M (q • ψ) = q • matrixAction M ψ := by
  funext x
  simp only [matrixAction, Matrix.mulVec, dotProduct, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  ring

/-- Applying a represented unitary preserves total Born mass. -/
theorem Unitary.mass_apply {ι : Type*} [Fintype ι]
    (U : Unitary ι) (ψ : State ι) : mass (U.apply ψ) = mass ψ :=
  U.preserves_mass ψ

/-- Applying a represented unitary preserves state normalization. -/
theorem Unitary.normalized_apply {ι : Type*} [Fintype ι]
    (U : Unitary ι) {ψ : State ι} (hψ : Normalized ψ) :
    Normalized (U.apply ψ) := by
  rw [Normalized, U.mass_apply]
  exact hψ

/-- The identity matrix, packaged with its exact mass-preservation proof. -/
def identity (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Unitary ι where
  matrix := 1
  preserves_mass := by
    intro ψ
    rw [matrixAction, Matrix.one_mulVec]

/-- The identity unitary fixes every state exactly. -/
theorem identity_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : State ι) : (identity ι).apply ψ = ψ := by
  rw [Unitary.apply, identity, matrixAction, Matrix.one_mulVec]

/-- The two-dimensional Hadamard transform, with its mass-preservation law
proved directly from the explicit matrix. -/
noncomputable def hadamard : Unitary (Fin 2) := by
  let q : ℂ := (Real.sqrt 2 / 2 : ℝ)
  have hq : Complex.normSq q = 1 / 2 := by
    norm_num [q, Complex.normSq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  refine ⟨fun i j => if i = 0 ∨ j = 0 then q else -q, ?_⟩
  intro ψ
  simp only [mass, matrixAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change Complex.normSq (q * ψ 0 + q * ψ 1) +
      Complex.normSq (q * ψ 0 + -q * ψ 1) =
    Complex.normSq (ψ 0) + Complex.normSq (ψ 1)
  rw [show q * ψ 0 + -q * ψ 1 = q * ψ 0 - q * ψ 1 by ring,
    Complex.normSq_add, Complex.normSq_sub]
  simp_rw [Complex.normSq_mul, hq]
  ring

/-- The zero output amplitude of Hadamard is the normalized sum of inputs. -/
theorem hadamard_apply_zero (ψ : State (Fin 2)) :
    hadamard.apply ψ 0 =
      (Real.sqrt 2 / 2 : ℝ) * ψ 0 + (Real.sqrt 2 / 2 : ℝ) * ψ 1 := by
  norm_num [hadamard, Unitary.apply, matrixAction, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

/-- The one output amplitude of Hadamard is the normalized input difference. -/
theorem hadamard_apply_one (ψ : State (Fin 2)) :
    hadamard.apply ψ 1 =
      (Real.sqrt 2 / 2 : ℝ) * ψ 0 - (Real.sqrt 2 / 2 : ℝ) * ψ 1 := by
  norm_num [hadamard, Unitary.apply, matrixAction, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

/-- The computational-basis state concentrated at `b`. -/
def basisState {ι : Type*} [DecidableEq ι] (b : ι) : State ι :=
  fun x => if x = b then 1 else 0

/-- Every computational-basis state on a finite basis is normalized. -/
theorem basisState_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι) : Normalized (basisState b) := by
  classical
  rw [Normalized, mass]
  calc
    (∑ x, Complex.normSq (basisState b x)) = Complex.normSq (basisState b b) := by
      apply Finset.sum_eq_single b
      · intro x _hx hxb
        simp only [basisState, if_neg hxb, map_zero]
      · simp
    _ = 1 := by simp [basisState]

/-- Hadamard maps the equal superposition to the zero basis state. -/
theorem hadamard_equal_superposition :
    hadamard.apply (fun _ : Fin 2 => (Real.sqrt 2 / 2 : ℝ)) = basisState 0 := by
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · norm_num [basisState]
    rw [hadamard_apply_zero]
    have hreal :
        Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) +
          Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hq : (((Real.sqrt 2 / 2 : ℝ) : ℂ)) = (Real.sqrt 2 : ℂ) / 2 :=
      Complex.ofReal_div _ _
    rw [← hq]
    exact_mod_cast hreal
  · norm_num [basisState]
    rw [hadamard_apply_one]
    ring

/-- The Boolean-marked phase-oracle matrix has diagonal entry `-1` on marked
basis labels, diagonal entry `1` elsewhere, and zero off the diagonal. -/
def phaseMatrix {ι : Type*} [DecidableEq ι] (marked : ι → Bool) :
    Matrix ι ι ℂ :=
  fun x y => if x = y then if marked x = true then -1 else 1 else 0

/-- The phase matrix acts pointwise by sign: marked amplitudes are negated and
unmarked amplitudes are unchanged. -/
theorem matrixAction_phaseMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (marked : ι → Bool) (ψ : State ι) (x : ι) :
    matrixAction (phaseMatrix marked) ψ x =
      (if marked x = true then -1 else 1) * ψ x := by
  classical
  simp [matrixAction, Matrix.mulVec, dotProduct, phaseMatrix]

/-- The Boolean phase oracle is an explicit diagonal unitary. -/
def phaseOracle (ι : Type*) [Fintype ι] [DecidableEq ι]
    (marked : ι → Bool) : Unitary ι where
  matrix := phaseMatrix marked
  preserves_mass := by
    intro ψ
    rw [mass, mass]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [matrixAction_phaseMatrix]
    by_cases hx : marked x = true
    · simp [hx, Complex.normSq_neg]
    · simp [hx]

/-- The packaged phase oracle negates exactly the marked amplitudes. -/
theorem phaseOracle_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (marked : ι → Bool) (ψ : State ι) (x : ι) :
    (phaseOracle ι marked).apply ψ x =
      if marked x = true then -ψ x else ψ x := by
  rw [Unitary.apply]
  change matrixAction (phaseMatrix marked) ψ x = _
  rw [matrixAction_phaseMatrix]
  by_cases hx : marked x = true
  · simp only [if_pos hx, neg_one_mul]
  · simp only [if_neg hx, one_mul]

/-- A query algorithm first applies `initial`, then for each unitary in
`afterQuery`, in list order, calls the marked phase oracle once and applies that
unitary.  Thus the stored list is an explicit `O, U₁, O, U₂, ...` schedule after
an oracle-free `U₀`. -/
structure QueryAlgorithm (ι : Type*) [Fintype ι] [Nonempty ι] where
  /-- The oracle-free unitary `U₀` applied before the first query. -/
  initial : Unitary ι
  /-- Ordered oracle-free unitaries, each immediately following one query. -/
  afterQuery : List (Unitary ι)

/-- The exact query count is the number of oracle/unitary rounds.  No truncated
subtraction or asymptotic convention is involved. -/
def QueryAlgorithm.queryCount {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : QueryAlgorithm ι) : ℕ :=
  A.afterQuery.length

/-- Execute the ordered finite query algorithm against a Boolean phase oracle. -/
def QueryAlgorithm.run {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : QueryAlgorithm ι) (marked : ι → Bool) (ψ : State ι) : State ι :=
  A.afterQuery.foldl
    (fun state U => U.apply ((phaseOracle ι marked).apply state))
    (A.initial.apply ψ)

/-- Execute the same schedule while operationally incrementing a counter once
at each actual phase-oracle call. -/
def QueryAlgorithm.runCounted {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (A : QueryAlgorithm ι) (marked : ι → Bool)
    (ψ : State ι) : State ι × ℕ :=
  A.afterQuery.foldl
    (fun result U =>
      (U.apply ((phaseOracle ι marked).apply result.1), result.2 + 1))
    (A.initial.apply ψ, 0)

private theorem foldl_counted_fst {ι : Type*} [Fintype ι]
    [DecidableEq ι] (marked : ι → Bool) (layers : List (Unitary ι))
    (ψ : State ι) (q : ℕ) :
    (layers.foldl
      (fun result U =>
        (U.apply ((phaseOracle ι marked).apply result.1), result.2 + 1))
      (ψ, q)).1 =
    layers.foldl
      (fun state U => U.apply ((phaseOracle ι marked).apply state)) ψ := by
  induction layers generalizing ψ q with
  | nil => rfl
  | cons U layers ih =>
      simp only [List.foldl_cons]
      exact ih (U.apply ((phaseOracle ι marked).apply ψ)) (q + 1)

private theorem foldl_counted_snd {ι : Type*} [Fintype ι]
    [DecidableEq ι] (marked : ι → Bool) (layers : List (Unitary ι))
    (ψ : State ι) (q : ℕ) :
    (layers.foldl
      (fun result U =>
        (U.apply ((phaseOracle ι marked).apply result.1), result.2 + 1))
      (ψ, q)).2 = q + layers.length := by
  induction layers generalizing ψ q with
  | nil => simp
  | cons U layers ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      omega

/-- Counted execution returns exactly the same final state as ordinary execution. -/
theorem QueryAlgorithm.runCounted_fst {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (A : QueryAlgorithm ι) (marked : ι → Bool)
    (ψ : State ι) : (A.runCounted marked ψ).1 = A.run marked ψ := by
  exact foldl_counted_fst marked A.afterQuery (A.initial.apply ψ) 0

/-- The operational counter equals the algorithm's exact declared query count. -/
theorem QueryAlgorithm.runCounted_snd {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (A : QueryAlgorithm ι) (marked : ι → Bool)
    (ψ : State ι) : (A.runCounted marked ψ).2 = A.queryCount := by
  rw [runCounted, queryCount, foldl_counted_snd]
  exact Nat.zero_add A.afterQuery.length

/-- Every finite list of oracle/unitary rounds preserves normalization. -/
private theorem normalized_foldl {ι : Type*} [Fintype ι]
    [DecidableEq ι] (marked : ι → Bool) (layers : List (Unitary ι))
    {ψ : State ι} (hψ : Normalized ψ) :
    Normalized (layers.foldl
      (fun state U => U.apply ((phaseOracle ι marked).apply state)) ψ) := by
  induction layers generalizing ψ with
  | nil => exact hψ
  | cons U layers ih =>
      simp only [List.foldl_cons]
      apply ih
      exact U.normalized_apply ((phaseOracle ι marked).normalized_apply hψ)

/-- Every finite query schedule preserves normalization, because both its
oracle-free matrices and every phase-oracle call preserve Born mass. -/
theorem QueryAlgorithm.normalized_run {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (A : QueryAlgorithm ι) (marked : ι → Bool)
    {ψ : State ι} (hψ : Normalized ψ) : Normalized (A.run marked ψ) := by
  rw [run]
  apply normalized_foldl marked A.afterQuery
  exact A.initial.normalized_apply hψ

/-- The Born weight of a basis label is the squared norm of its amplitude.
It is a probability only when the enclosing amplitude vector is normalized. -/
def bornWeight {ι : Type*} (ψ : State ι) (x : ι) : ℝ :=
  Complex.normSq (ψ x)

/-- The Born weight of a Boolean event is the sum of basis-label weights on
labels for which the event returns `true`. It is not called a probability until
normalization is supplied. -/
def eventWeight {ι : Type*} [Fintype ι]
    (event : ι → Bool) (ψ : State ι) : ℝ :=
  ∑ x, if event x = true then bornWeight ψ x else 0

/-- The final marked Born weight of an algorithm on an arbitrary amplitude
vector. This unrestricted quantity need not lie in `[0,1]`. -/
def QueryAlgorithm.successWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (A : QueryAlgorithm ι) (marked : ι → Bool)
    (ψ : State ι) : ℝ :=
  eventWeight marked (A.run marked ψ)

/-- Exact success probability on a normalized input. The normalization witness
makes the probabilistic precondition explicit at every use site. -/
def QueryAlgorithm.successProbability {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (A : QueryAlgorithm ι) (marked : ι → Bool)
    (ψ : State ι) (_hψ : Normalized ψ) : ℝ :=
  A.successWeight marked ψ

/-- The Born weights sum to the amplitude vector's total mass. -/
theorem sum_bornWeight_eq_mass {ι : Type*} [Fintype ι]
    (ψ : State ι) : ∑ x, bornWeight ψ x = mass ψ :=
  rfl

/-- Every computational-basis Born weight is nonnegative. -/
theorem bornWeight_nonneg {ι : Type*} (ψ : State ι) (x : ι) :
    0 ≤ bornWeight ψ x :=
  Complex.normSq_nonneg (ψ x)

/-- Every Boolean event has nonnegative Born weight. -/
theorem eventWeight_nonneg {ι : Type*} [Fintype ι]
    (event : ι → Bool) (ψ : State ι) : 0 ≤ eventWeight event ψ := by
  rw [eventWeight]
  apply Finset.sum_nonneg
  intro x _hx
  by_cases h : event x = true
  · simp only [if_pos h]
    exact bornWeight_nonneg ψ x
  · simp only [if_neg h, le_refl]

/-- A Boolean event's Born weight is at most the vector's total mass. -/
theorem eventWeight_le_mass {ι : Type*} [Fintype ι]
    (event : ι → Bool) (ψ : State ι) : eventWeight event ψ ≤ mass ψ := by
  rw [eventWeight, mass]
  apply Finset.sum_le_sum
  intro x _hx
  by_cases h : event x = true
  · simp only [if_pos h, bornWeight]
    exact le_rfl
  · simp only [if_neg h]
    exact Complex.normSq_nonneg (ψ x)

/-- Exact success probability lies in `[0,1]`. This is a semantic bound,
not a search-efficiency claim. -/
theorem QueryAlgorithm.successProbability_mem_unitInterval
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : QueryAlgorithm ι) (marked : ι → Bool) {ψ : State ι}
    (hψ : Normalized ψ) :
    0 ≤ A.successProbability marked ψ hψ ∧
      A.successProbability marked ψ hψ ≤ 1 := by
  rw [successProbability]
  constructor
  · exact eventWeight_nonneg marked (A.run marked ψ)
  · calc
      A.successWeight marked ψ ≤ mass (A.run marked ψ) :=
        eventWeight_le_mass marked (A.run marked ψ)
      _ = 1 := A.normalized_run marked hψ

/-- A marked basis label's Born weight is at most total marked Born weight.
This is finite-sum monotonicity, not an algorithmic amplification claim. -/
theorem QueryAlgorithm.successWeight_ge_of_marked_weight
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : QueryAlgorithm ι) (marked : ι → Bool) (ψ : State ι)
    (x : ι) (p : ℝ) (hx : marked x = true)
    (hweight : p ≤ bornWeight (A.run marked ψ) x) :
    p ≤ A.successWeight marked ψ := by
  apply hweight.trans
  rw [successWeight, eventWeight]
  have hnonneg : ∀ y ∈ (Finset.univ : Finset ι),
      0 ≤ if marked y = true then bornWeight (A.run marked ψ) y else 0 := by
    intro y _hy
    by_cases hy : marked y = true
    · simp only [if_pos hy]
      exact bornWeight_nonneg (A.run marked ψ) y
    · simp only [if_neg hy, le_refl]
  simpa only [if_pos hx] using
    Finset.single_le_sum hnonneg (Finset.mem_univ x)

end Quantum

namespace Scheme

/-- `MarksReducible T decode marked` says that a nonempty finite quantum basis
injectively enumerates exact level-`r` flip-graph vertices, and that its Boolean
marking is true exactly on vertices satisfying the established `Reducible`
predicate.  It neither assumes that every graph vertex is enumerated nor that a
large marked fraction exists. -/
def MarksReducible {k : Type*} [Field k] {a b c r : ℕ}
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : BilinearComplexity.Tensor k a b c)
    (decode : ι → Scheme k a b c r) (marked : ι → Bool) : Prop :=
  Function.Injective decode ∧
    (∀ i, (decode i).GraphVertex T) ∧
    ∀ i, marked i = true ↔ (decode i).Reducible T

end Scheme

/-! Ground checks and one jointly satisfiable finite flip-search model. -/

example : Quantum.State (Fin 2) = (Fin 2 → ℂ) := rfl

example : Quantum.mass (fun _ : Fin 1 => (1 : ℂ)) = 1 := by
  norm_num [Quantum.mass]

example : Quantum.Normalized (fun _ : Fin 1 => (1 : ℂ)) := by
  norm_num [Quantum.Normalized, Quantum.mass]

example : Quantum.matrixAction (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (fun _ => (2 : ℂ)) = fun _ => 2 := by
  rw [Quantum.matrixAction, Matrix.one_mulVec]

example : (Quantum.identity (Fin 1)).apply (fun _ => (2 : ℂ)) = fun _ => 2 := by
  exact Quantum.identity_apply _

example : Quantum.basisState (0 : Fin 2) 0 = 1 := by
  simp [Quantum.basisState]

example : Quantum.phaseMatrix (fun x : Fin 2 => x == 0) 0 0 = -1 := by
  norm_num [Quantum.phaseMatrix]

example :
    (Quantum.phaseOracle (Fin 2) (fun x => x == 0)).apply
      (Quantum.basisState 0) = -Quantum.basisState 0 := by
  funext x
  fin_cases x <;>
    simp [Quantum.phaseOracle_apply, Quantum.basisState]

example :
    let A : Quantum.QueryAlgorithm (Fin 2) :=
      ⟨Quantum.identity (Fin 2), [Quantum.identity (Fin 2)]⟩
    A.queryCount = 1 := by
  rfl

example :
    let A : Quantum.QueryAlgorithm (Fin 2) :=
      ⟨Quantum.identity (Fin 2), [Quantum.identity (Fin 2)]⟩
    A.run (fun x => x == 0) (Quantum.basisState 0) =
      -Quantum.basisState 0 := by
  dsimp [Quantum.QueryAlgorithm.run]
  simp only [Quantum.identity_apply]
  funext x
  rw [Quantum.phaseOracle_apply]
  fin_cases x <;> simp [Quantum.basisState]

example :
    let A : Quantum.QueryAlgorithm (Fin 2) :=
      ⟨Quantum.identity (Fin 2), [Quantum.identity (Fin 2)]⟩
    (A.runCounted (fun x => x == 0) (Quantum.basisState 0)).2 = 1 := by
  rfl

example : Quantum.bornWeight (Quantum.basisState (0 : Fin 2)) 0 = 1 := by
  norm_num [Quantum.bornWeight, Quantum.basisState]

example : Quantum.eventWeight (fun x : Fin 2 => x == 0)
    (Quantum.basisState 0) = 1 := by
  norm_num [Quantum.eventWeight, Quantum.bornWeight,
    Quantum.basisState, Fin.sum_univ_two]

example :
    let A : Quantum.QueryAlgorithm (Fin 2) :=
      ⟨Quantum.identity (Fin 2), [Quantum.identity (Fin 2)]⟩
    A.successWeight (fun x => x == 0) (Quantum.basisState 0) = 1 := by
  dsimp [Quantum.QueryAlgorithm.successWeight, Quantum.QueryAlgorithm.run]
  simp only [Quantum.identity_apply]
  norm_num [Quantum.eventWeight, Quantum.bornWeight,
    Quantum.phaseOracle_apply, Quantum.basisState, Fin.sum_univ_two]

example :
    let ψ : Quantum.State (Fin 2) :=
      fun _ => (Real.sqrt 2 / 2 : ℝ)
    Quantum.Normalized ψ ∧ ψ 0 ≠ 0 ∧ ψ 1 ≠ 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · change Quantum.mass (fun _ : Fin 2 => (Real.sqrt 2 / 2 : ℝ)) = 1
    rw [← Quantum.hadamard.mass_apply,
      Quantum.hadamard_equal_superposition]
    exact Quantum.basisState_normalized 0
  · have hs : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
    exact_mod_cast hs.ne'
  · have hs : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
    exact_mod_cast hs.ne'

example :
    let marked : Fin 2 → Bool := fun x => x == 0
    let ψ : Quantum.State (Fin 2) :=
      fun _ => (Real.sqrt 2 / 2 : ℝ)
    Quantum.bornWeight (Quantum.hadamard.apply ψ) 0 = 1 ∧
      Quantum.bornWeight
        (Quantum.hadamard.apply
          ((Quantum.phaseOracle (Fin 2) marked).apply ψ)) 0 = 0 := by
  dsimp only
  constructor
  · rw [Quantum.hadamard_equal_superposition]
    norm_num [Quantum.bornWeight, Quantum.basisState]
  · rw [Quantum.bornWeight, Quantum.hadamard_apply_zero,
      Quantum.phaseOracle_apply, Quantum.phaseOracle_apply]
    norm_num

example :
    let marked : Fin 2 → Bool := fun x => x == 0
    let A : Quantum.QueryAlgorithm (Fin 2) :=
      ⟨Quantum.identity (Fin 2), []⟩
    (1 : ℝ) ≤ A.successWeight marked (Quantum.basisState 0) := by
  dsimp only
  apply Quantum.QueryAlgorithm.successWeight_ge_of_marked_weight _ _ _ 0 1
  · rfl
  · rw [Quantum.QueryAlgorithm.run]
    simp only [List.foldl_nil, Quantum.identity_apply]
    norm_num [Quantum.bornWeight, Quantum.basisState]





end BilinearComplexity.FlipQuantum
