/- Retained native-backed finite flip-graph evidence.
This cohesive package preserves the original finite checks; it is not
a standard-axiom production theorem package. -/
import BilinearComplexity.FlipQuantum.Phase4FiniteQuery

set_option autoImplicit false

namespace BilinearComplexity.FlipQuantum

namespace FiniteModel

private abbrev F := ZMod 2

private def vectorA : Fin 2 → F := ![0, 1]

private def vectorB : Fin 2 → F := ![1, 0]

private def vectorC : Fin 2 → F := ![1, 1]

example : vectorA 0 = 0 ∧ vectorA 1 = 1 := by
  norm_num [vectorA]

example : vectorB 0 = 1 ∧ vectorB 1 = 0 := by
  norm_num [vectorB]

example : vectorC 0 = 1 ∧ vectorC 1 = 1 := by
  norm_num [vectorC]

private def reducibleScheme : Scheme F 2 2 2 3 := ⟨![
  (vectorA, vectorA, vectorA),
  (vectorA, vectorB, vectorA),
  (vectorC, vectorB, vectorC)]⟩

private def irreducibleScheme : Scheme F 2 2 2 3 := ⟨![
  (vectorA, vectorA, vectorA),
  (vectorA, vectorB, vectorB),
  (vectorB, vectorB, vectorC)]⟩

example : reducibleScheme.term 0 = (vectorA, vectorA, vectorA) ∧
    reducibleScheme.term 1 = (vectorA, vectorB, vectorA) ∧
    reducibleScheme.term 2 = (vectorC, vectorB, vectorC) := by
  norm_num [reducibleScheme]
  -- This closed fallback enlarges the trust surface; kernel reduction does not
  -- simplify the final `Fin 3` vector index.
  native_decide

example : irreducibleScheme.term 0 = (vectorA, vectorA, vectorA) ∧
    irreducibleScheme.term 1 = (vectorA, vectorB, vectorB) ∧
    irreducibleScheme.term 2 = (vectorB, vectorB, vectorC) := by
  norm_num [irreducibleScheme]
  -- This closed fallback enlarges the trust surface; kernel reduction does not
  -- simplify the final `Fin 3` vector index.
  native_decide

private def tensor : BilinearComplexity.Tensor F 2 2 2 :=
  reducibleScheme.sumTensor

-- This closed computation checks the advertised lexicographic tensor
-- coordinates. `native_decide` enlarges the trust surface, but is used here
-- because kernel reduction gets stuck on characteristic-two residual numerals
-- after ordinary simplification.
example :
    tensor 0 0 0 = 1 ∧ tensor 0 0 1 = 1 ∧
      tensor 0 1 0 = 0 ∧ tensor 0 1 1 = 0 ∧
      tensor 1 0 0 = 1 ∧ tensor 1 0 1 = 0 ∧
      tensor 1 1 0 = 0 ∧ tensor 1 1 1 = 1 := by
  native_decide

private theorem reducibleScheme_valid : reducibleScheme.Valid tensor := by
  refine ⟨rfl, ?_, ?_⟩
  · intro s hzero
    fin_cases s
    · have hentry := congrFun (congrFun (congrFun hzero 1) 1) 1
      norm_num [reducibleScheme, vectorA,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hzero 1) 0) 1
      norm_num [reducibleScheme, vectorA, vectorB,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
      norm_num [reducibleScheme, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · have hentry := congrFun (congrFun (congrFun hxy 1) 1) 1
      norm_num [reducibleScheme, vectorA, vectorB,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hxy 1) 1) 1
      norm_num [reducibleScheme, vectorA, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hxy 1) 1) 1
      norm_num [reducibleScheme, vectorA, vectorB,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · rfl
    · have hentry := congrFun (congrFun (congrFun hxy 0) 0) 0
      norm_num [reducibleScheme, vectorA, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hxy 1) 1) 1
      norm_num [reducibleScheme, vectorA, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hxy 0) 0) 0
      norm_num [reducibleScheme, vectorA, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · rfl

private theorem irreducibleScheme_valid : irreducibleScheme.Valid tensor := by
  refine ⟨?_, ?_, ?_⟩
  · funext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [irreducibleScheme, tensor, reducibleScheme, Scheme.sumTensor,
        vectorA, vectorB, vectorC, BilinearComplexity.TriadData.eval,
        BilinearComplexity.triad, Fin.sum_univ_succ]
    -- This closed fallback enlarges the trust surface; kernel reduction stalls
    -- on the remaining characteristic-two numeral equality.
    all_goals native_decide
  · intro s hzero
    fin_cases s
    · have hentry := congrFun (congrFun (congrFun hzero 1) 1) 1
      norm_num [irreducibleScheme, vectorA,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hzero 1) 0) 0
      norm_num [irreducibleScheme, vectorA, vectorB,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hzero 0) 0) 0
      norm_num [irreducibleScheme, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · have hentry := congrFun (congrFun (congrFun hxy 1) 1) 1
      norm_num [irreducibleScheme, vectorA, vectorB,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hxy 1) 1) 1
      norm_num [irreducibleScheme, vectorA, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hxy 1) 1) 1
      norm_num [irreducibleScheme, vectorA, vectorB,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · rfl
    · have hentry := congrFun (congrFun (congrFun hxy 1) 0) 0
      norm_num [irreducibleScheme, vectorA, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hxy 1) 1) 1
      norm_num [irreducibleScheme, vectorA, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · have hentry := congrFun (congrFun (congrFun hxy 1) 0) 0
      norm_num [irreducibleScheme, vectorA, vectorB, vectorC,
        BilinearComplexity.TriadData.eval, BilinearComplexity.triad] at hentry
    · rfl

private theorem reducibleScheme_graphVertex :
    reducibleScheme.GraphVertex tensor :=
  ⟨by omega, reducibleScheme_valid⟩

private theorem irreducibleScheme_graphVertex :
    irreducibleScheme.GraphVertex tensor :=
  ⟨by omega, irreducibleScheme_valid⟩

private theorem reducibleScheme_reducible :
    reducibleScheme.Reducible tensor := by
  refine ⟨reducibleScheme_graphVertex, Or.inr (Or.inl ?_)⟩
  let I : Finset (Fin 3) := {0, 1}
  refine ⟨I, by simp [I], ?_, ?_⟩
  · refine ⟨0, by simp [I], ?_⟩
    intro i hi
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;>
      exact projectivelyEqual_of_eq rfl
  · intro hli
    have hinj := hli.injective
    let x : {i : Fin 3 // i ∈ I} := ⟨0, by simp [I]⟩
    let y : {i : Fin 3 // i ∈ I} := ⟨1, by simp [I]⟩
    have hxy : x = y := hinj rfl
    have hval := congrArg (fun i => (i.1 : Fin 3).val) hxy
    norm_num [x, y] at hval

private def reducibleFamilyDecidable
    (x y : Fin 3 → Fin 2 → F) : Decidable (Scheme.ReducibleFamily x y) := by
  unfold Scheme.ReducibleFamily
  letI (I : Finset (Fin 3)) :
      Decidable (LinearIndependent F
        (fun i : {i : Fin 3 // i ∈ I} => y i.1)) := by
    rw [Fintype.linearIndependent_iff]
    exact Fintype.decidableForallFintype
  letI (p i : Fin 3) : Decidable (ProjectivelyEqual (x p) (x i)) := by
    unfold ProjectivelyEqual
    infer_instance
  exact Fintype.decidableExistsFintype

-- These six closed computations exhaust the six ordered mode pairs in
-- `Scheme.Reducible`. The decision procedure unfolds projective equality and
-- uses `Fintype.linearIndependent_iff`. These `native_decide` calls enlarge
-- the trust surface, but kernel reduction of the resulting finite `ZMod 2`
-- searches is infeasible.
private theorem irreducibleScheme_not_reducible_12 :
    ¬ Scheme.ReducibleFamily
      (fun s => (irreducibleScheme.term s).1)
      (fun s => (irreducibleScheme.term s).2.1) :=
  @of_decide_eq_true _
    (@instDecidableNot _ (reducibleFamilyDecidable _ _)) (by native_decide)

private theorem irreducibleScheme_not_reducible_13 :
    ¬ Scheme.ReducibleFamily
      (fun s => (irreducibleScheme.term s).1)
      (fun s => (irreducibleScheme.term s).2.2) :=
  @of_decide_eq_true _
    (@instDecidableNot _ (reducibleFamilyDecidable _ _)) (by native_decide)

private theorem irreducibleScheme_not_reducible_21 :
    ¬ Scheme.ReducibleFamily
      (fun s => (irreducibleScheme.term s).2.1)
      (fun s => (irreducibleScheme.term s).1) :=
  @of_decide_eq_true _
    (@instDecidableNot _ (reducibleFamilyDecidable _ _)) (by native_decide)

private theorem irreducibleScheme_not_reducible_23 :
    ¬ Scheme.ReducibleFamily
      (fun s => (irreducibleScheme.term s).2.1)
      (fun s => (irreducibleScheme.term s).2.2) :=
  @of_decide_eq_true _
    (@instDecidableNot _ (reducibleFamilyDecidable _ _)) (by native_decide)

private theorem irreducibleScheme_not_reducible_31 :
    ¬ Scheme.ReducibleFamily
      (fun s => (irreducibleScheme.term s).2.2)
      (fun s => (irreducibleScheme.term s).1) :=
  @of_decide_eq_true _
    (@instDecidableNot _ (reducibleFamilyDecidable _ _)) (by native_decide)

private theorem irreducibleScheme_not_reducible_32 :
    ¬ Scheme.ReducibleFamily
      (fun s => (irreducibleScheme.term s).2.2)
      (fun s => (irreducibleScheme.term s).2.1) :=
  @of_decide_eq_true _
    (@instDecidableNot _ (reducibleFamilyDecidable _ _)) (by native_decide)

private theorem irreducibleScheme_irreducible :
    ¬ irreducibleScheme.Reducible tensor := by
  intro hirr
  rcases hirr.2 with h12 | h13 | h21 | h23 | h31 | h32
  · exact irreducibleScheme_not_reducible_12 h12
  · exact irreducibleScheme_not_reducible_13 h13
  · exact irreducibleScheme_not_reducible_21 h21
  · exact irreducibleScheme_not_reducible_23 h23
  · exact irreducibleScheme_not_reducible_31 h31
  · exact irreducibleScheme_not_reducible_32 h32

private def decode : Fin 2 → Scheme F 2 2 2 3 :=
  ![reducibleScheme, irreducibleScheme]

example : decode 0 = reducibleScheme ∧ decode 1 = irreducibleScheme := by
  norm_num [decode]

private theorem decode_injective : Function.Injective decode := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have hfactor := congrArg (fun S => (S.term 1).2.2 0) hij
    norm_num [decode, reducibleScheme, irreducibleScheme,
      vectorA, vectorB] at hfactor
  · have hfactor := congrArg (fun S => (S.term 1).2.2 0) hij
    norm_num [decode, reducibleScheme, irreducibleScheme,
      vectorA, vectorB] at hfactor
  · rfl

private def marked : Fin 2 → Bool := fun i => i == 0

example : marked 0 = true ∧ marked 1 = false := by
  norm_num [marked]

private theorem marksReducible :
    Scheme.MarksReducible tensor decode marked := by
  refine ⟨decode_injective, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [decode] using reducibleScheme_graphVertex
    · simpa [decode] using irreducibleScheme_graphVertex
  · intro i
    fin_cases i
    · constructor
      · intro _hmarked
        simpa [decode] using reducibleScheme_reducible
      · intro _hreducible
        rfl
    · constructor
      · intro hmarked
        norm_num [marked] at hmarked
      · intro hreducible
        have hirreducible : irreducibleScheme.Reducible tensor := by
          simpa [decode] using hreducible
        exact (irreducibleScheme_irreducible hirreducible).elim

private noncomputable def amplitude : Quantum.State (Fin 2) :=
  fun _ => (Real.sqrt 2 / 2 : ℝ)

example : amplitude 0 = (Real.sqrt 2 / 2 : ℝ) ∧
    amplitude 1 = (Real.sqrt 2 / 2 : ℝ) := by
  constructor <;> rfl

private theorem amplitude_normalized_support :
    Quantum.Normalized amplitude ∧ amplitude 0 ≠ 0 ∧ amplitude 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change Quantum.mass (fun _ : Fin 2 => (Real.sqrt 2 / 2 : ℝ)) = 1
    rw [← Quantum.hadamard.mass_apply,
      Quantum.hadamard_equal_superposition]
    exact Quantum.basisState_normalized 0
  · change (((Real.sqrt 2 / 2 : ℝ) : ℂ)) ≠ 0
    have hsqrt : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
    exact_mod_cast hsqrt.ne'
  · change (((Real.sqrt 2 / 2 : ℝ) : ℂ)) ≠ 0
    have hsqrt : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
    exact_mod_cast hsqrt.ne'

example :
    Scheme.MarksReducible tensor decode marked ∧
      decode 0 ≠ decode 1 ∧
      (decode 0).GraphVertex tensor ∧
      (decode 1).GraphVertex tensor ∧
      (decode 0).Reducible tensor ∧
      ¬ (decode 1).Reducible tensor ∧
      Quantum.Normalized amplitude ∧ amplitude 0 ≠ 0 ∧ amplitude 1 ≠ 0 := by
  refine ⟨marksReducible, ?_, ?_, ?_, ?_, ?_, amplitude_normalized_support⟩
  · intro hdecode
    have hlabels : (0 : Fin 2) = 1 := decode_injective hdecode
    omega
  · simpa [decode] using reducibleScheme_graphVertex
  · simpa [decode] using irreducibleScheme_graphVertex
  · simpa [decode] using reducibleScheme_reducible
  · simpa [decode] using irreducibleScheme_irreducible

end FiniteModel

end BilinearComplexity.FlipQuantum
