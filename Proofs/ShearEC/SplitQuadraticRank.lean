import ShearEC.ShearQuadraticRank
import BilinearComplexity.LinearFlattening

set_option autoImplicit false

namespace ShearEC.ShearQuadraticRank

open MvPolynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-- The split quadratic on the selected left and right coordinates; coordinates
outside the image of `emb` do not occur. -/
noncomputable def splitQuadratic (emb : Fin m ⊕ Fin m → Fin n) : MvPolynomial (Fin n) K :=
  ∑ i, X (emb (.inl i)) * X (emb (.inr i))

example (emb : Fin 0 ⊕ Fin 0 → Fin n) : splitQuadratic (K := K) emb = 0 := by
  simp [splitQuadratic]

example (emb : Fin 1 ⊕ Fin 1 → Fin n) :
    splitQuadratic (K := K) emb = X (emb (.inl 0)) * X (emb (.inr 0)) := by
  simp [splitQuadratic]

/-- Pairwise sampled second differences of evaluations on selected standard
assignments. No bilinearity in the assignments is asserted. -/
private noncomputable def sample (emb : Fin m ⊕ Fin m → Fin n)
    (P : MvPolynomial (Fin n) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  fun i j => eval (Pi.single (emb i) 1 + Pi.single (emb j) 1) P -
    eval (Pi.single (emb i) 1) P - eval (Pi.single (emb j) 1) P

example (emb : Fin m ⊕ Fin m → Fin n) :
    sample emb (0 : MvPolynomial (Fin n) K) = 0 := by
  ext i j
  simp [sample]

private lemma eval_linear_add {L : MvPolynomial (Fin n) K}
    (hL : L.IsHomogeneous 1) (x y : Fin n → K) :
    eval (x + y) L = eval x L + eval y L := by
  rw [hL.eq_sum_C_mul_X]
  simp [mul_add, Finset.sum_add_distrib]

private lemma sample_product (emb : Fin m ⊕ Fin m → Fin n)
    {L L' : MvPolynomial (Fin n) K} (hL : L.IsHomogeneous 1)
    (hL' : L'.IsHomogeneous 1) :
    sample emb (L * L') =
      Matrix.vecMulVec (fun i => eval (Pi.single (emb i) 1) L)
        (fun i => eval (Pi.single (emb i) 1) L') +
      Matrix.vecMulVec (fun i => eval (Pi.single (emb i) 1) L')
        (fun i => eval (Pi.single (emb i) 1) L) := by
  ext i j
  simp only [sample, map_mul, eval_linear_add hL, eval_linear_add hL',
    Matrix.add_apply, Matrix.vecMulVec_apply]
  ring

private lemma sample_sum (emb : Fin m ⊕ Fin m → Fin n) {s : ℕ}
    (P : Fin s → MvPolynomial (Fin n) K) :
    sample emb (∑ r, P r) = ∑ r, sample emb (P r) := by
  ext i j
  simp [Matrix.sum_apply, sample, Finset.sum_sub_distrib]

private lemma sample_split (emb : Fin m ⊕ Fin m → Fin n)
    (he : Function.Injective emb) :
    sample emb (splitQuadratic (K := K) emb) =
      Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) K) 1 1 0 := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp [sample, splitQuadratic, Pi.single_apply, he.eq_iff,
      Matrix.fromBlocks, Matrix.one_apply, mul_add, eq_comm]

/-- The displayed split quadratic is a sum of `m` homogeneous linear products. -/
theorem splitQuadratic_isSumOfProducts (emb : Fin m ⊕ Fin m → Fin n) :
    IsSumOfProducts m (splitQuadratic (K := K) emb) := by
  refine ⟨(fun i => X (emb (.inl i))), (fun i => X (emb (.inr i))), ?_, ?_, rfl⟩
  · intro i
    exact isHomogeneous_X K _
  · intro i
    exact isHomogeneous_X K _

private lemma rank_sample_split (emb : Fin m ⊕ Fin m → Fin n)
    (he : Function.Injective emb) :
    (sample emb (splitQuadratic (K := K) emb)).rank = m + m := by
  classical
  let H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    Matrix.fromBlocks 0 1 1 0
  have hsq : H * H = 1 := by
    dsimp [H]
    rw [Matrix.fromBlocks_multiply]
    simp only [zero_mul, mul_zero, one_mul, zero_add, add_zero,
      Matrix.fromBlocks_one]
  have hlower : m + m ≤ H.rank := by
    have hmul := Matrix.rank_mul_le_left H H
    rw [hsq, Matrix.rank_one] at hmul
    simpa using hmul
  have hupper : H.rank ≤ m + m := by
    simpa using Matrix.rank_le_card_width H
  rw [sample_split emb he]
  exact Nat.le_antisymm hupper hlower

/-- Distinct active coordinates force at least `m` products of homogeneous
linear forms in any exact polynomial decomposition of the split quadratic. -/
theorem le_of_isSumOfProducts_splitQuadratic
    (emb : Fin m ⊕ Fin m → Fin n) (he : Function.Injective emb) {s : ℕ}
    (hQ : IsSumOfProducts s (splitQuadratic (K := K) emb)) : m ≤ s := by
  classical
  obtain ⟨L, L', hL, hL', hQ⟩ := hQ
  have hrank : ∀ r, (sample emb (L r * L' r)).rank ≤ 2 := by
    intro r
    rw [sample_product emb (hL r) (hL' r)]
    exact (BilinearComplexity.matrix_rank_add_le _ _).trans
      (by have ha := Matrix.rank_vecMulVec_le
            (fun i => eval (Pi.single (emb i) 1) (L r))
            (fun i => eval (Pi.single (emb i) 1) (L' r))
          have hb := Matrix.rank_vecMulVec_le
            (fun i => eval (Pi.single (emb i) 1) (L' r))
            (fun i => eval (Pi.single (emb i) 1) (L r))
          omega)
  have hsum : (∑ r, sample emb (L r * L' r)).rank ≤ s * 2 := by
    calc
      (∑ r, sample emb (L r * L' r)).rank ≤
          ∑ r, (sample emb (L r * L' r)).rank :=
        BilinearComplexity.matrix_rank_sum_le _ _
      _ ≤ ∑ _ : Fin s, 2 := Finset.sum_le_sum (fun r _ => hrank r)
      _ = s * 2 := by simp
  have hbound : m + m ≤ s * 2 := by
    rw [← rank_sample_split (K := K) emb he, hQ, sample_sum]
    exact hsum
  omega

/-- Over every field, the minimum homogeneous-linear product count of a
split quadratic on distinct active coordinates is exactly `m`. -/
theorem isSumOfProducts_splitQuadratic_iff
    (emb : Fin m ⊕ Fin m → Fin n) (he : Function.Injective emb) (s : ℕ) :
    IsSumOfProducts s (splitQuadratic (K := K) emb) ↔ m ≤ s := by
  constructor
  · exact le_of_isSumOfProducts_splitQuadratic emb he
  · intro hms
    exact (splitQuadratic_isSumOfProducts emb).mono hms

-- A nonempty characteristic-two model, with one inactive coordinate.
example : ∃ emb : Fin 1 ⊕ Fin 1 → Fin 3,
    Function.Injective emb ∧ IsSumOfProducts 1 (splitQuadratic (K := ZMod 2) emb) := by
  let emb : Fin 1 ⊕ Fin 1 → Fin 3 := fun i => Fin.castAdd 1 (finSumFinEquiv i)
  refine ⟨emb, ?_, splitQuadratic_isSumOfProducts emb⟩
  exact (Fin.castAdd_injective 2 1).comp finSumFinEquiv.injective

-- The empty case is intentional and includes an empty ambient coordinate set.
example : IsSumOfProducts 0
    (splitQuadratic (K := K) (finSumFinEquiv : Fin 0 ⊕ Fin 0 → Fin 0)) :=
  splitQuadratic_isSumOfProducts _

example : ¬ IsSumOfProducts 0
    (splitQuadratic (K := K) (finSumFinEquiv : Fin 1 ⊕ Fin 1 → Fin 2)) := by
  rw [isSumOfProducts_splitQuadratic_iff _ finSumFinEquiv.injective]
  omega

end ShearEC.ShearQuadraticRank
