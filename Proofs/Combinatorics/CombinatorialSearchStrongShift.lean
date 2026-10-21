/-
# Combinatorial search for strong shift equivalence: Ashley's eight-by-eight

## Source

arXiv:2609.03567, Emmanuel Jeandel, "Combinatorial Search for Strong Shift
Equivalence".  Recorded 2026-10-21.

* Definitions: §Background "Definitions" (ESSE and SSE over a semiring,
  here `ℕ = ℤ₊`).
* Ashley's matrix: §Background "Open problems", displayed after the Little
  Shift Equivalence Conjecture for `n = 2`.
* Theorem (§Results "The Ashley example"), verbatim:

  > The Ashley matrix is SSE to the matrix $\begin{pmatrix}2 \end{pmatrix}$.
  > The SSE uses 23 steps and involves 10 by 10 matrices.

* Certificate: appendix "Ashley eight-by-eight is SSE to the matrix $(2)$
  (optimized)" (source file `ashley_opt.tex`), 23 printed triples
  `A_i = R_i S_i`, `S_i R_i = A_{i+1}`, with `A_0` the Ashley matrix and
  `A_23 = (2)`.
* Secondary: Theorem `thm:baker` at `k = 3`, certificate in the appendix
  "$A_3$ is SSE to $B_3$ (optimized)" (source file `1341_opt.tex`), 17
  printed triples.

Definition (verbatim): "Two square matrices $A$ and $B$, possibly of
different size, with elements in $\mathcal{S}$, are elementary strong shift
equivalent (ESSE ...), if there exist matrices $R,S$ over $\mathcal{S}$ s.t.,
$A = RS$ and $B = SR$.  Strong shift equivalence is the symmetric, reflexive,
and transitive closure of elementary strong shift equivalence."

## Status

Proved in the paper (by computer search; the certificate is printed in the
appendix).  Here every printed product is re-checked by kernel evaluation
(`decide +kernel`, no `native_decide`).  The matrices below were transcribed
mechanically from the paper's LaTeX source; the transcription is faithful
because each kernel check would fail on any mistranscribed entry that breaks
`A_i = R_i S_i` or `S_i R_i = A_{i+1}`, and the endpoints `ashley` and `(2)`
are stated independently in the main theorem.
-/
import Mathlib

set_option autoImplicit false

/- Sequential elaboration: under the repository's `ulimit -v` memory cap, parallel
elaboration of the many `decide +kernel` certificate checks fails to spawn threads. -/
set_option Elab.async false

namespace Candidates.CombinatorialSearchStrongShift

/-! ## Definitions -/

/-- Elementary strong shift equivalence over `ℤ₊ = ℕ` (Jeandel, §Background
"Definitions"): square matrices `A` (size `m`) and `B` (size `n`) are ESSE if there are
nonnegative integer matrices `R : m × n` and `S : n × m` with `A = R S` and `B = S R`. -/
def ESSE {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℕ) (B : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∃ (R : Matrix (Fin m) (Fin n) ℕ) (S : Matrix (Fin n) (Fin m) ℕ), A = R * S ∧ B = S * R

/-- A square nonnegative integer matrix of arbitrary size, packaged with its size. -/
abbrev SqMat : Type := Σ n : ℕ, Matrix (Fin n) (Fin n) ℕ

/-- Elementary strong shift equivalence as a relation on size-tagged square matrices. -/
def ESSERel (X Y : SqMat) : Prop := ESSE X.2 Y.2

/-- Strong shift equivalence over `ℤ₊` (Jeandel, §Background "Definitions"): the
symmetric, reflexive and transitive closure of elementary strong shift equivalence. -/
def SSE (X Y : SqMat) : Prop := Relation.EqvGen ESSERel X Y

/-- ESSE is symmetric: swap the roles of `R` and `S`. -/
theorem ESSE.symm {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℕ} {B : Matrix (Fin n) (Fin n) ℕ}
    (h : ESSE A B) : ESSE B A := by
  obtain ⟨R, S, hA, hB⟩ := h
  exact ⟨S, R, hB, hA⟩

/-- A forward chain of elementary strong shift equivalences (the explicit form
`A = A_1, …, A_l = B` used in the paper) yields strong shift equivalence. -/
theorem SSE.of_reflTransGen {X Y : SqMat} (h : Relation.ReflTransGen ESSERel X Y) :
    SSE X Y := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hstep ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hstep)

/-- The trace is an SSE invariant (since `tr (R S) = tr (S R)`). -/
theorem SSE.trace_eq {X Y : SqMat} (h : SSE X Y) : X.2.trace = Y.2.trace := by
  induction h with
  | rel X Y hXY =>
    obtain ⟨R, S, hA, hB⟩ := hXY
    rw [hA, hB, Matrix.trace_mul_comm]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Ground-truth checks of the definitions -/

/-- `(2) = (1 1)(1 1)ᵀ` and `(1 1)ᵀ(1 1)` is the all-ones `2 × 2` matrix (a splitting). -/
example : ESSE !![(2 : ℕ)] !![1, 1; 1, 1] :=
  ⟨!![1, 1], !![1; 1], by decide, by decide⟩

/-- Every matrix is ESSE to itself (take `R = 1`, `S = A`). -/
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) : ESSE A A :=
  ⟨1, A, (one_mul A).symm, (mul_one A).symm⟩

/-- Non-vacuity of `SSE`: `(1)` and `(2)` are not SSE, since their traces differ. -/
example : ¬ SSE ⟨1, !![1]⟩ ⟨1, !![2]⟩ := by
  intro h
  have htr := h.trace_eq
  simp [Matrix.trace] at htr

/-! ## The matrices of the paper -/

/-- Ashley's eight-by-eight matrix as displayed in Jeandel, §Background "Open problems"
(a `0/1` matrix whose only nonzero eigenvalue is `2`); it is also `A_0` of the
appendix certificate. -/
def ashley : Matrix (Fin 8) (Fin 8) ℕ :=
  !![1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 1, 0;
    0, 1, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley's matrix has trace `2`, matching the trace of `(2)`. -/
example : ashley.trace = 2 := by decide +kernel

/-- Ashley's matrix has row sums `2` (it is the adjacency matrix of a 2-out-regular graph). -/
example : ∀ i, ∑ j, ashley i j = 2 := by decide +kernel

/-- Baker's matrix `A_k = [[1, k+1], [k, 1]]` at `k = 3`. -/
def bakerA3 : Matrix (Fin 2) (Fin 2) ℕ := !![1, 4; 3, 1]

/-- Baker's matrix `B_k = [[1, k(k+1)], [1, 1]]` at `k = 3`. -/
def bakerB3 : Matrix (Fin 2) (Fin 2) ℕ := !![1, 12; 1, 1]

/-! ## The certificates (transcribed from the appendix of arXiv:2609.03567) -/

/-- Ashley certificate: the intermediate matrix `A_{1}` of the printed certificate. -/
def ashleyA1 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    1, 1, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 1;
    1, 2, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 1]

/-- Ashley certificate: the intermediate matrix `A_{2}` of the printed certificate. -/
def ashleyA2 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 1, 1;
    0, 1, 1, 0, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{3}` of the printed certificate. -/
def ashleyA3 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0, 0, 1;
    0, 0, 2, 1, 0, 0, 0, 2, 0;
    0, 1, 2, 0, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{4}` of the printed certificate. -/
def ashleyA4 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    1, 1, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 2, 0, 0, 1, 1, 1;
    0, 0, 1, 2, 0, 0, 0, 0, 2;
    0, 1, 0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{5}` of the printed certificate. -/
def ashleyA5 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 2, 2, 0, 0, 0, 0, 0;
    1, 1, 1, 2, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{6}` of the printed certificate. -/
def ashleyA6 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 2, 2, 0, 0, 0, 0;
    1, 1, 1, 1, 2, 1, 1, 0, 2, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1, 1, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{7}` of the printed certificate. -/
def ashleyA7 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 2, 0, 0, 0, 0;
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 1, 0, 1, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{8}` of the printed certificate. -/
def ashleyA8 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 1, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 1, 1, 0;
    1, 0, 2, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{9}` of the printed certificate. -/
def ashleyA9 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    2, 0, 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{10}` of the printed certificate. -/
def ashleyA10 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 1, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 1;
    1, 1, 2, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{11}` of the printed certificate. -/
def ashleyA11 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 1, 0, 0;
    1, 0, 1, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 1, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{12}` of the printed certificate. -/
def ashleyA12 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 1, 1, 0, 0, 1, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 1, 0;
    0, 1, 1, 0, 1, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{13}` of the printed certificate. -/
def ashleyA13 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 1;
    1, 1, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    1, 0, 1, 0, 0, 1, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{14}` of the printed certificate. -/
def ashleyA14 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 1, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 1, 0, 1, 0, 1, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{15}` of the printed certificate. -/
def ashleyA15 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 1, 1, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{16}` of the printed certificate. -/
def ashleyA16 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 1, 1, 1, 0, 1, 1;
    0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 1, 0, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{17}` of the printed certificate. -/
def ashleyA17 : Matrix (Fin 7) (Fin 7) ℕ :=
  !![0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 1, 0, 0;
    0, 0, 1, 1, 0, 1, 0;
    0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 1, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{18}` of the printed certificate. -/
def ashleyA18 : Matrix (Fin 6) (Fin 6) ℕ :=
  !![0, 0, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0;
    0, 0, 0, 1, 1, 0;
    0, 0, 1, 1, 1, 1]

/-- Ashley certificate: the intermediate matrix `A_{19}` of the printed certificate. -/
def ashleyA19 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 0, 1, 0;
    1, 0, 0, 0, 0;
    0, 1, 0, 0, 1;
    0, 1, 0, 1, 1;
    0, 1, 1, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{20}` of the printed certificate. -/
def ashleyA20 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 0, 0, 1;
    0, 0, 1, 0;
    0, 0, 1, 1;
    1, 1, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{21}` of the printed certificate. -/
def ashleyA21 : Matrix (Fin 3) (Fin 3) ℕ :=
  !![0, 1, 1;
    0, 1, 1;
    1, 0, 1]

/-- Ashley certificate: the intermediate matrix `A_{22}` of the printed certificate. -/
def ashleyA22 : Matrix (Fin 2) (Fin 2) ℕ :=
  !![1, 1;
    1, 1]

/-- Ashley certificate: the factor `R` of step 0 (`A_{0} = R S`, `S R = A_{1}`). -/
def ashleyR0 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 1]

/-- Ashley certificate: the factor `S` of step 0 (`A_{0} = R S`, `S R = A_{1}`). -/
def ashleyS0 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 1 (`A_{1} = R S`, `S R = A_{2}`). -/
def ashleyR1 : Matrix (Fin 8) (Fin 9) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 1]

/-- Ashley certificate: the factor `S` of step 1 (`A_{1} = R S`, `S R = A_{2}`). -/
def ashleyS1 : Matrix (Fin 9) (Fin 8) ℕ :=
  !![0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    1, 1, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 2, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0]

/-- Ashley certificate: the factor `R` of step 2 (`A_{2} = R S`, `S R = A_{3}`). -/
def ashleyR2 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `S` of step 2 (`A_{2} = R S`, `S R = A_{3}`). -/
def ashleyS2 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 1, 0;
    0, 1, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 3 (`A_{3} = R S`, `S R = A_{4}`). -/
def ashleyR3 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 2, 0, 0, 0, 0, 2;
    0, 0, 0, 2, 0, 0, 1, 1, 1;
    1, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- Ashley certificate: the factor `S` of step 3 (`A_{3} = R S`, `S R = A_{4}`). -/
def ashleyS3 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- Ashley certificate: the factor `R` of step 4 (`A_{4} = R S`, `S R = A_{5}`). -/
def ashleyR4 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 1, 2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- Ashley certificate: the factor `S` of step 4 (`A_{4} = R S`, `S R = A_{5}`). -/
def ashleyS4 : Matrix (Fin 9) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 1, 0, 0;
    1, 1, 1, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 1, 0]

/-- Ashley certificate: the factor `R` of step 5 (`A_{5} = R S`, `S R = A_{6}`). -/
def ashleyR5 : Matrix (Fin 9) (Fin 10) ℕ :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 2, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `S` of step 5 (`A_{5} = R S`, `S R = A_{6}`). -/
def ashleyS5 : Matrix (Fin 10) (Fin 9) ℕ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 1, 1, 2, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 6 (`A_{6} = R S`, `S R = A_{7}`). -/
def ashleyR6 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 2, 0, 0, 0, 0;
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 1]

/-- Ashley certificate: the factor `S` of step 6 (`A_{6} = R S`, `S R = A_{7}`). -/
def ashleyS6 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 7 (`A_{7} = R S`, `S R = A_{8}`). -/
def ashleyR7 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0]

/-- Ashley certificate: the factor `S` of step 7 (`A_{7} = R S`, `S R = A_{8}`). -/
def ashleyS7 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 1;
    0, 1, 0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 1, 0]

/-- Ashley certificate: the factor `R` of step 8 (`A_{8} = R S`, `S R = A_{9}`). -/
def ashleyR8 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- Ashley certificate: the factor `S` of step 8 (`A_{8} = R S`, `S R = A_{9}`). -/
def ashleyS8 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 2, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0]

/-- Ashley certificate: the factor `R` of step 9 (`A_{9} = R S`, `S R = A_{10}`). -/
def ashleyR9 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

/-- Ashley certificate: the factor `S` of step 9 (`A_{9} = R S`, `S R = A_{10}`). -/
def ashleyS9 : Matrix (Fin 10) (Fin 10) ℕ :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
    2, 0, 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0]

/-- Ashley certificate: the factor `R` of step 10 (`A_{10} = R S`, `S R = A_{11}`). -/
def ashleyR10 : Matrix (Fin 10) (Fin 9) ℕ :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 1;
    0, 1, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `S` of step 10 (`A_{10} = R S`, `S R = A_{11}`). -/
def ashleyS10 : Matrix (Fin 9) (Fin 10) ℕ :=
  !![0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 11 (`A_{11} = R S`, `S R = A_{12}`). -/
def ashleyR11 : Matrix (Fin 9) (Fin 8) ℕ :=
  !![0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 1, 1, 0, 0, 1, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 1, 0;
    0, 1, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `S` of step 11 (`A_{11} = R S`, `S R = A_{12}`). -/
def ashleyS11 : Matrix (Fin 8) (Fin 9) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 12 (`A_{12} = R S`, `S R = A_{13}`). -/
def ashleyR12 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 1, 0;
    1, 1, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 1, 1, 0;
    1, 0, 0, 0, 0, 1, 0, 1]

/-- Ashley certificate: the factor `S` of step 12 (`A_{12} = R S`, `S R = A_{13}`). -/
def ashleyS12 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 13 (`A_{13} = R S`, `S R = A_{14}`). -/
def ashleyR13 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 1, 0, 0, 0, 1, 0, 1]

/-- Ashley certificate: the factor `S` of step 13 (`A_{13} = R S`, `S R = A_{14}`). -/
def ashleyS13 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 14 (`A_{14} = R S`, `S R = A_{15}`). -/
def ashleyR14 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 1, 1, 0, 1]

/-- Ashley certificate: the factor `S` of step 14 (`A_{14} = R S`, `S R = A_{15}`). -/
def ashleyS14 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 15 (`A_{15} = R S`, `S R = A_{16}`). -/
def ashleyR15 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 1, 0, 0, 1]

/-- Ashley certificate: the factor `S` of step 15 (`A_{15} = R S`, `S R = A_{16}`). -/
def ashleyS15 : Matrix (Fin 8) (Fin 8) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 16 (`A_{16} = R S`, `S R = A_{17}`). -/
def ashleyR16 : Matrix (Fin 8) (Fin 7) ℕ :=
  !![0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 1, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `S` of step 16 (`A_{16} = R S`, `S R = A_{17}`). -/
def ashleyS16 : Matrix (Fin 7) (Fin 8) ℕ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 1, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 17 (`A_{17} = R S`, `S R = A_{18}`). -/
def ashleyR17 : Matrix (Fin 7) (Fin 6) ℕ :=
  !![0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

/-- Ashley certificate: the factor `S` of step 17 (`A_{17} = R S`, `S R = A_{18}`). -/
def ashleyS17 : Matrix (Fin 6) (Fin 7) ℕ :=
  !![0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 1, 0, 1]

/-- Ashley certificate: the factor `R` of step 18 (`A_{18} = R S`, `S R = A_{19}`). -/
def ashleyR18 : Matrix (Fin 6) (Fin 5) ℕ :=
  !![0, 0, 0, 1, 0;
    0, 1, 0, 0, 0;
    1, 0, 0, 0, 0;
    0, 1, 1, 0, 0;
    0, 0, 0, 0, 1;
    0, 1, 0, 1, 1]

/-- Ashley certificate: the factor `S` of step 18 (`A_{18} = R S`, `S R = A_{19}`). -/
def ashleyS18 : Matrix (Fin 5) (Fin 6) ℕ :=
  !![1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 1, 0]

/-- Ashley certificate: the factor `R` of step 19 (`A_{19} = R S`, `S R = A_{20}`). -/
def ashleyR19 : Matrix (Fin 5) (Fin 4) ℕ :=
  !![0, 0, 1, 0;
    0, 1, 0, 0;
    0, 0, 0, 1;
    0, 0, 1, 1;
    1, 0, 0, 1]

/-- Ashley certificate: the factor `S` of step 19 (`A_{19} = R S`, `S R = A_{20}`). -/
def ashleyS19 : Matrix (Fin 4) (Fin 5) ℕ :=
  !![0, 0, 1, 0, 0;
    1, 0, 0, 0, 0;
    0, 0, 0, 1, 0;
    0, 1, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 20 (`A_{20} = R S`, `S R = A_{21}`). -/
def ashleyR20 : Matrix (Fin 4) (Fin 3) ℕ :=
  !![0, 0, 1;
    0, 1, 0;
    0, 1, 1;
    1, 0, 1]

/-- Ashley certificate: the factor `S` of step 20 (`A_{20} = R S`, `S R = A_{21}`). -/
def ashleyS20 : Matrix (Fin 3) (Fin 4) ℕ :=
  !![1, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1]

/-- Ashley certificate: the factor `R` of step 21 (`A_{21} = R S`, `S R = A_{22}`). -/
def ashleyR21 : Matrix (Fin 3) (Fin 2) ℕ :=
  !![1, 0;
    1, 0;
    0, 1]

/-- Ashley certificate: the factor `S` of step 21 (`A_{21} = R S`, `S R = A_{22}`). -/
def ashleyS21 : Matrix (Fin 2) (Fin 3) ℕ :=
  !![0, 1, 1;
    1, 0, 1]

/-- Ashley certificate: the factor `R` of step 22 (`A_{22} = R S`, `S R = A_{23}`). -/
def ashleyR22 : Matrix (Fin 2) (Fin 1) ℕ :=
  !![1;
    1]

/-- Ashley certificate: the factor `S` of step 22 (`A_{22} = R S`, `S R = A_{23}`). -/
def ashleyS22 : Matrix (Fin 1) (Fin 2) ℕ :=
  !![1, 1]

/-- Ashley certificate, step 0: `A_{0}` is elementary strong shift equivalent to `A_{1}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_0 : ESSE ashley ashleyA1 :=
  ⟨ashleyR0, ashleyS0, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 1: `A_{1}` is elementary strong shift equivalent to `A_{2}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_1 : ESSE ashleyA1 ashleyA2 :=
  ⟨ashleyR1, ashleyS1, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 2: `A_{2}` is elementary strong shift equivalent to `A_{3}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_2 : ESSE ashleyA2 ashleyA3 :=
  ⟨ashleyR2, ashleyS2, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 3: `A_{3}` is elementary strong shift equivalent to `A_{4}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_3 : ESSE ashleyA3 ashleyA4 :=
  ⟨ashleyR3, ashleyS3, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 4: `A_{4}` is elementary strong shift equivalent to `A_{5}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_4 : ESSE ashleyA4 ashleyA5 :=
  ⟨ashleyR4, ashleyS4, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 5: `A_{5}` is elementary strong shift equivalent to `A_{6}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_5 : ESSE ashleyA5 ashleyA6 :=
  ⟨ashleyR5, ashleyS5, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 6: `A_{6}` is elementary strong shift equivalent to `A_{7}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_6 : ESSE ashleyA6 ashleyA7 :=
  ⟨ashleyR6, ashleyS6, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 7: `A_{7}` is elementary strong shift equivalent to `A_{8}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_7 : ESSE ashleyA7 ashleyA8 :=
  ⟨ashleyR7, ashleyS7, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 8: `A_{8}` is elementary strong shift equivalent to `A_{9}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_8 : ESSE ashleyA8 ashleyA9 :=
  ⟨ashleyR8, ashleyS8, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 9: `A_{9}` is elementary strong shift equivalent to `A_{10}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_9 : ESSE ashleyA9 ashleyA10 :=
  ⟨ashleyR9, ashleyS9, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 10: `A_{10}` is elementary strong shift equivalent to `A_{11}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_10 : ESSE ashleyA10 ashleyA11 :=
  ⟨ashleyR10, ashleyS10, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 11: `A_{11}` is elementary strong shift equivalent to `A_{12}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_11 : ESSE ashleyA11 ashleyA12 :=
  ⟨ashleyR11, ashleyS11, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 12: `A_{12}` is elementary strong shift equivalent to `A_{13}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_12 : ESSE ashleyA12 ashleyA13 :=
  ⟨ashleyR12, ashleyS12, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 13: `A_{13}` is elementary strong shift equivalent to `A_{14}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_13 : ESSE ashleyA13 ashleyA14 :=
  ⟨ashleyR13, ashleyS13, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 14: `A_{14}` is elementary strong shift equivalent to `A_{15}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_14 : ESSE ashleyA14 ashleyA15 :=
  ⟨ashleyR14, ashleyS14, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 15: `A_{15}` is elementary strong shift equivalent to `A_{16}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_15 : ESSE ashleyA15 ashleyA16 :=
  ⟨ashleyR15, ashleyS15, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 16: `A_{16}` is elementary strong shift equivalent to `A_{17}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_16 : ESSE ashleyA16 ashleyA17 :=
  ⟨ashleyR16, ashleyS16, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 17: `A_{17}` is elementary strong shift equivalent to `A_{18}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_17 : ESSE ashleyA17 ashleyA18 :=
  ⟨ashleyR17, ashleyS17, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 18: `A_{18}` is elementary strong shift equivalent to `A_{19}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_18 : ESSE ashleyA18 ashleyA19 :=
  ⟨ashleyR18, ashleyS18, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 19: `A_{19}` is elementary strong shift equivalent to `A_{20}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_19 : ESSE ashleyA19 ashleyA20 :=
  ⟨ashleyR19, ashleyS19, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 20: `A_{20}` is elementary strong shift equivalent to `A_{21}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_20 : ESSE ashleyA20 ashleyA21 :=
  ⟨ashleyR20, ashleyS20, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 21: `A_{21}` is elementary strong shift equivalent to `A_{22}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_21 : ESSE ashleyA21 ashleyA22 :=
  ⟨ashleyR21, ashleyS21, by decide +kernel, by decide +kernel⟩

/-- Ashley certificate, step 22: `A_{22}` is elementary strong shift equivalent to `A_{23}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem ashley_esse_22 : ESSE ashleyA22 !![2] :=
  ⟨ashleyR22, ashleyS22, by decide +kernel, by decide +kernel⟩

/-- The Ashley certificate as an explicit forward chain of 23 elementary strong shift
equivalences. -/
theorem ashley_chain :
    Relation.ReflTransGen ESSERel ⟨8, ashley⟩ ⟨1, !![2]⟩ := by
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨8, ashley⟩ ⟨8, ashleyA1⟩ from ashley_esse_0) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨8, ashleyA1⟩ ⟨9, ashleyA2⟩ from ashley_esse_1) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨9, ashleyA2⟩ ⟨9, ashleyA3⟩ from ashley_esse_2) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨9, ashleyA3⟩ ⟨9, ashleyA4⟩ from ashley_esse_3) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨9, ashleyA4⟩ ⟨9, ashleyA5⟩ from ashley_esse_4) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨9, ashleyA5⟩ ⟨10, ashleyA6⟩ from ashley_esse_5) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨10, ashleyA6⟩ ⟨10, ashleyA7⟩ from ashley_esse_6) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨10, ashleyA7⟩ ⟨10, ashleyA8⟩ from ashley_esse_7) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨10, ashleyA8⟩ ⟨10, ashleyA9⟩ from ashley_esse_8) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨10, ashleyA9⟩ ⟨10, ashleyA10⟩ from ashley_esse_9) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨10, ashleyA10⟩ ⟨9, ashleyA11⟩ from ashley_esse_10) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨9, ashleyA11⟩ ⟨8, ashleyA12⟩ from ashley_esse_11) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨8, ashleyA12⟩ ⟨8, ashleyA13⟩ from ashley_esse_12) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨8, ashleyA13⟩ ⟨8, ashleyA14⟩ from ashley_esse_13) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨8, ashleyA14⟩ ⟨8, ashleyA15⟩ from ashley_esse_14) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨8, ashleyA15⟩ ⟨8, ashleyA16⟩ from ashley_esse_15) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨8, ashleyA16⟩ ⟨7, ashleyA17⟩ from ashley_esse_16) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨7, ashleyA17⟩ ⟨6, ashleyA18⟩ from ashley_esse_17) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨6, ashleyA18⟩ ⟨5, ashleyA19⟩ from ashley_esse_18) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨5, ashleyA19⟩ ⟨4, ashleyA20⟩ from ashley_esse_19) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨4, ashleyA20⟩ ⟨3, ashleyA21⟩ from ashley_esse_20) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨3, ashleyA21⟩ ⟨2, ashleyA22⟩ from ashley_esse_21) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨2, ashleyA22⟩ ⟨1, !![2]⟩ from ashley_esse_22) ?_
  exact Relation.ReflTransGen.refl

/-- Baker `k = 3` certificate: the intermediate matrix `A_{1}` of the printed certificate. -/
def baker3A1 : Matrix (Fin 3) (Fin 3) ℕ :=
  !![0, 0, 1;
    1, 1, 2;
    4, 4, 1]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{2}` of the printed certificate. -/
def baker3A2 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 4, 1, 1;
    1, 1, 0, 1;
    0, 4, 1, 4;
    0, 4, 1, 0]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{3}` of the printed certificate. -/
def baker3A3 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 3, 1, 1;
    1, 0, 0, 1;
    0, 0, 1, 4;
    1, 4, 1, 1]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{4}` of the printed certificate. -/
def baker3A4 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 3, 1, 0;
    1, 0, 0, 1;
    1, 4, 2, 3;
    1, 4, 1, 0]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{5}` of the printed certificate. -/
def baker3A5 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 4, 2, 0;
    1, 0, 0, 1;
    0, 3, 2, 1;
    1, 5, 2, 0]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{6}` of the printed certificate. -/
def baker3A6 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 2, 1, 0;
    4, 0, 0, 1;
    3, 1, 1, 1;
    2, 1, 0, 0]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{7}` of the printed certificate. -/
def baker3A7 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 1, 1, 0;
    4, 1, 1, 1;
    7, 0, 1, 2;
    1, 1, 0, 0]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{8}` of the printed certificate. -/
def baker3A8 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 1, 1, 1;
    3, 0, 1, 1;
    7, 0, 1, 2;
    1, 1, 0, 1]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{9}` of the printed certificate. -/
def baker3A9 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 1, 0, 0;
    1, 0, 0, 1, 3;
    4, 3, 0, 1, 3;
    5, 5, 0, 1, 2;
    2, 1, 0, 0, 1]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{10}` of the printed certificate. -/
def baker3A10 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 1, 1, 0;
    1, 0, 0, 5, 1;
    2, 2, 0, 4, 1;
    2, 1, 0, 1, 0;
    1, 3, 0, 2, 1]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{11}` of the printed certificate. -/
def baker3A11 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 1, 1, 0;
    0, 0, 0, 5, 1;
    1, 2, 0, 4, 1;
    2, 1, 0, 1, 0;
    0, 3, 1, 3, 1]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{12}` of the printed certificate. -/
def baker3A12 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 1, 1, 0;
    2, 1, 0, 5, 1;
    1, 2, 0, 2, 1;
    2, 1, 0, 0, 0;
    0, 3, 1, 0, 1]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{13}` of the printed certificate. -/
def baker3A13 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 1, 1, 0;
    2, 0, 0, 5, 1;
    1, 1, 0, 2, 1;
    2, 1, 0, 0, 0;
    2, 2, 1, 5, 2]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{14}` of the printed certificate. -/
def baker3A14 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 0, 1, 1;
    3, 0, 2, 5;
    2, 1, 2, 2;
    2, 1, 0, 0]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{15}` of the printed certificate. -/
def baker3A15 : Matrix (Fin 3) (Fin 3) ℕ :=
  !![2, 0, 2;
    7, 0, 7;
    2, 1, 0]

/-- Baker `k = 3` certificate: the intermediate matrix `A_{16}` of the printed certificate. -/
def baker3A16 : Matrix (Fin 2) (Fin 2) ℕ :=
  !![0, 11;
    1, 2]

/-- Baker `k = 3` certificate: the factor `R` of step 0 (`A_{0} = R S`, `S R = A_{1}`). -/
def baker3R0 : Matrix (Fin 2) (Fin 3) ℕ :=
  !![0, 0, 1;
    1, 1, 0]

/-- Baker `k = 3` certificate: the factor `S` of step 0 (`A_{0} = R S`, `S R = A_{1}`). -/
def baker3S0 : Matrix (Fin 3) (Fin 2) ℕ :=
  !![1, 0;
    2, 1;
    1, 4]

/-- Baker `k = 3` certificate: the factor `R` of step 1 (`A_{1} = R S`, `S R = A_{2}`). -/
def baker3R1 : Matrix (Fin 3) (Fin 4) ℕ :=
  !![0, 0, 0, 1;
    1, 1, 0, 1;
    0, 4, 1, 0]

/-- Baker `k = 3` certificate: the factor `S` of step 1 (`A_{1} = R S`, `S R = A_{2}`). -/
def baker3S1 : Matrix (Fin 4) (Fin 3) ℕ :=
  !![1, 0, 1;
    0, 1, 0;
    4, 0, 1;
    0, 0, 1]

/-- Baker `k = 3` certificate: the factor `R` of step 2 (`A_{2} = R S`, `S R = A_{3}`). -/
def baker3R2 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 3, 1, 1;
    1, 0, 0, 1;
    0, 0, 1, 4;
    0, 4, 1, 0]

/-- Baker `k = 3` certificate: the factor `S` of step 2 (`A_{2} = R S`, `S R = A_{3}`). -/
def baker3S2 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 1, 0, 1]

/-- Baker `k = 3` certificate: the factor `R` of step 3 (`A_{3} = R S`, `S R = A_{4}`). -/
def baker3R3 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 3, 1, 0;
    1, 0, 0, 1;
    0, 0, 1, 3;
    1, 4, 1, 0]

/-- Baker `k = 3` certificate: the factor `S` of step 3 (`A_{3} = R S`, `S R = A_{4}`). -/
def baker3S3 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 1;
    0, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `R` of step 4 (`A_{4} = R S`, `S R = A_{5}`). -/
def baker3R4 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 1, 2, 0;
    0, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `S` of step 4 (`A_{4} = R S`, `S R = A_{5}`). -/
def baker3S4 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 3, 1, 0;
    1, 0, 0, 1;
    0, 2, 1, 1;
    1, 4, 1, 0]

/-- Baker `k = 3` certificate: the factor `R` of step 5 (`A_{5} = R S`, `S R = A_{6}`). -/
def baker3R5 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![2, 0, 0, 0;
    0, 1, 0, 0;
    1, 0, 1, 0;
    2, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `S` of step 5 (`A_{5} = R S`, `S R = A_{6}`). -/
def baker3S5 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 2, 1, 0;
    1, 0, 0, 1;
    0, 1, 1, 1;
    1, 1, 0, 0]

/-- Baker `k = 3` certificate: the factor `R` of step 6 (`A_{6} = R S`, `S R = A_{7}`). -/
def baker3R6 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 1, 1, 0;
    4, 0, 0, 1;
    3, 0, 1, 1;
    1, 1, 0, 0]

/-- Baker `k = 3` certificate: the factor `S` of step 6 (`A_{6} = R S`, `S R = A_{7}`). -/
def baker3S6 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 0, 0, 0;
    1, 1, 0, 0;
    0, 1, 1, 0;
    0, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `R` of step 7 (`A_{7} = R S`, `S R = A_{8}`). -/
def baker3R7 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 0, 0, 0;
    0, 1, 0, 1;
    0, 0, 1, 0;
    0, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `S` of step 7 (`A_{7} = R S`, `S R = A_{8}`). -/
def baker3S7 : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 1, 1, 0;
    3, 0, 1, 1;
    7, 0, 1, 2;
    1, 1, 0, 0]

/-- Baker `k = 3` certificate: the factor `R` of step 8 (`A_{8} = R S`, `S R = A_{9}`). -/
def baker3R8 : Matrix (Fin 4) (Fin 5) ℕ :=
  !![1, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 2;
    1, 0, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `S` of step 8 (`A_{8} = R S`, `S R = A_{9}`). -/
def baker3S8 : Matrix (Fin 5) (Fin 4) ℕ :=
  !![0, 1, 0, 0;
    0, 0, 1, 1;
    3, 0, 1, 1;
    5, 0, 1, 0;
    1, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `R` of step 9 (`A_{9} = R S`, `S R = A_{10}`). -/
def baker3R9 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 1, 0;
    0, 0, 0, 2, 1;
    0, 0, 0, 1, 0]

/-- Baker `k = 3` certificate: the factor `S` of step 9 (`A_{9} = R S`, `S R = A_{10}`). -/
def baker3S9 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 1, 0, 0;
    1, 0, 0, 1, 3;
    2, 2, 0, 1, 2;
    2, 1, 0, 0, 1;
    1, 3, 0, 1, 0]

/-- Baker `k = 3` certificate: the factor `R` of step 10 (`A_{10} = R S`, `S R = A_{11}`). -/
def baker3R10 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 1, 1, 0;
    0, 0, 0, 5, 1;
    1, 2, 0, 4, 1;
    2, 1, 0, 1, 0;
    0, 3, 0, 2, 1]

/-- Baker `k = 3` certificate: the factor `S` of step 10 (`A_{10} = R S`, `S R = A_{11}`). -/
def baker3S10 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    1, 0, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `R` of step 11 (`A_{11} = R S`, `S R = A_{12}`). -/
def baker3R11 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 1, 1, 0;
    0, 0, 0, 5, 1;
    1, 2, 0, 2, 1;
    2, 1, 0, 0, 0;
    0, 3, 1, 0, 1]

/-- Baker `k = 3` certificate: the factor `S` of step 11 (`A_{11} = R S`, `S R = A_{12}`). -/
def baker3S11 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 1, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `R` of step 12 (`A_{12} = R S`, `S R = A_{13}`). -/
def baker3R12 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0, 0, 1, 1, 0;
    2, 0, 0, 5, 1;
    1, 1, 0, 2, 1;
    2, 1, 0, 0, 0;
    0, 2, 1, 0, 1]

/-- Baker `k = 3` certificate: the factor `S` of step 12 (`A_{12} = R S`, `S R = A_{13}`). -/
def baker3S12 : Matrix (Fin 5) (Fin 5) ℕ :=
  !![1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 1, 0, 0, 1]

/-- Baker `k = 3` certificate: the factor `R` of step 13 (`A_{13} = R S`, `S R = A_{14}`). -/
def baker3R13 : Matrix (Fin 5) (Fin 4) ℕ :=
  !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1;
    1, 0, 2, 0]

/-- Baker `k = 3` certificate: the factor `S` of step 13 (`A_{13} = R S`, `S R = A_{14}`). -/
def baker3S13 : Matrix (Fin 4) (Fin 5) ℕ :=
  !![0, 0, 1, 1, 0;
    2, 0, 0, 5, 1;
    1, 1, 0, 2, 1;
    2, 1, 0, 0, 0]

/-- Baker `k = 3` certificate: the factor `R` of step 14 (`A_{14} = R S`, `S R = A_{15}`). -/
def baker3R14 : Matrix (Fin 4) (Fin 3) ℕ :=
  !![1, 0, 0;
    0, 1, 0;
    2, 0, 1;
    0, 0, 1]

/-- Baker `k = 3` certificate: the factor `S` of step 14 (`A_{14} = R S`, `S R = A_{15}`). -/
def baker3S14 : Matrix (Fin 3) (Fin 4) ℕ :=
  !![0, 0, 1, 1;
    3, 0, 2, 5;
    2, 1, 0, 0]

/-- Baker `k = 3` certificate: the factor `R` of step 15 (`A_{15} = R S`, `S R = A_{16}`). -/
def baker3R15 : Matrix (Fin 3) (Fin 2) ℕ :=
  !![0, 2;
    0, 7;
    1, 0]

/-- Baker `k = 3` certificate: the factor `S` of step 15 (`A_{15} = R S`, `S R = A_{16}`). -/
def baker3S15 : Matrix (Fin 2) (Fin 3) ℕ :=
  !![2, 1, 0;
    1, 0, 1]

/-- Baker `k = 3` certificate: the factor `R` of step 16 (`A_{16} = R S`, `S R = A_{17}`). -/
def baker3R16 : Matrix (Fin 2) (Fin 2) ℕ :=
  !![0, 11;
    1, 1]

/-- Baker `k = 3` certificate: the factor `S` of step 16 (`A_{16} = R S`, `S R = A_{17}`). -/
def baker3S16 : Matrix (Fin 2) (Fin 2) ℕ :=
  !![1, 1;
    0, 1]

/-- Baker `k = 3` certificate, step 0: `A_{0}` is elementary strong shift equivalent to `A_{1}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_0 : ESSE bakerA3 baker3A1 :=
  ⟨baker3R0, baker3S0, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 1: `A_{1}` is elementary strong shift equivalent to `A_{2}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_1 : ESSE baker3A1 baker3A2 :=
  ⟨baker3R1, baker3S1, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 2: `A_{2}` is elementary strong shift equivalent to `A_{3}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_2 : ESSE baker3A2 baker3A3 :=
  ⟨baker3R2, baker3S2, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 3: `A_{3}` is elementary strong shift equivalent to `A_{4}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_3 : ESSE baker3A3 baker3A4 :=
  ⟨baker3R3, baker3S3, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 4: `A_{4}` is elementary strong shift equivalent to `A_{5}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_4 : ESSE baker3A4 baker3A5 :=
  ⟨baker3R4, baker3S4, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 5: `A_{5}` is elementary strong shift equivalent to `A_{6}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_5 : ESSE baker3A5 baker3A6 :=
  ⟨baker3R5, baker3S5, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 6: `A_{6}` is elementary strong shift equivalent to `A_{7}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_6 : ESSE baker3A6 baker3A7 :=
  ⟨baker3R6, baker3S6, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 7: `A_{7}` is elementary strong shift equivalent to `A_{8}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_7 : ESSE baker3A7 baker3A8 :=
  ⟨baker3R7, baker3S7, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 8: `A_{8}` is elementary strong shift equivalent to `A_{9}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_8 : ESSE baker3A8 baker3A9 :=
  ⟨baker3R8, baker3S8, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 9: `A_{9}` is elementary strong shift equivalent to `A_{10}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_9 : ESSE baker3A9 baker3A10 :=
  ⟨baker3R9, baker3S9, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 10: `A_{10}` is elementary strong shift equivalent to `A_{11}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_10 : ESSE baker3A10 baker3A11 :=
  ⟨baker3R10, baker3S10, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 11: `A_{11}` is elementary strong shift equivalent to `A_{12}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_11 : ESSE baker3A11 baker3A12 :=
  ⟨baker3R11, baker3S11, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 12: `A_{12}` is elementary strong shift equivalent to `A_{13}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_12 : ESSE baker3A12 baker3A13 :=
  ⟨baker3R12, baker3S12, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 13: `A_{13}` is elementary strong shift equivalent to `A_{14}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_13 : ESSE baker3A13 baker3A14 :=
  ⟨baker3R13, baker3S13, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 14: `A_{14}` is elementary strong shift equivalent to `A_{15}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_14 : ESSE baker3A14 baker3A15 :=
  ⟨baker3R14, baker3S14, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 15: `A_{15}` is elementary strong shift equivalent to `A_{16}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_15 : ESSE baker3A15 baker3A16 :=
  ⟨baker3R15, baker3S15, by decide +kernel, by decide +kernel⟩

/-- Baker `k = 3` certificate, step 16: `A_{16}` is elementary strong shift equivalent to `A_{17}`,
witnessed by the printed pair `(R, S)`; both products are checked by kernel evaluation. -/
theorem baker3_esse_16 : ESSE baker3A16 bakerB3 :=
  ⟨baker3R16, baker3S16, by decide +kernel, by decide +kernel⟩

/-- The Baker `k = 3` certificate as an explicit forward chain of 17 elementary strong shift
equivalences. -/
theorem baker3_chain :
    Relation.ReflTransGen ESSERel ⟨2, bakerA3⟩ ⟨2, bakerB3⟩ := by
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨2, bakerA3⟩ ⟨3, baker3A1⟩ from baker3_esse_0) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨3, baker3A1⟩ ⟨4, baker3A2⟩ from baker3_esse_1) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨4, baker3A2⟩ ⟨4, baker3A3⟩ from baker3_esse_2) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨4, baker3A3⟩ ⟨4, baker3A4⟩ from baker3_esse_3) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨4, baker3A4⟩ ⟨4, baker3A5⟩ from baker3_esse_4) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨4, baker3A5⟩ ⟨4, baker3A6⟩ from baker3_esse_5) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨4, baker3A6⟩ ⟨4, baker3A7⟩ from baker3_esse_6) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨4, baker3A7⟩ ⟨4, baker3A8⟩ from baker3_esse_7) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨4, baker3A8⟩ ⟨5, baker3A9⟩ from baker3_esse_8) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨5, baker3A9⟩ ⟨5, baker3A10⟩ from baker3_esse_9) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨5, baker3A10⟩ ⟨5, baker3A11⟩ from baker3_esse_10) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨5, baker3A11⟩ ⟨5, baker3A12⟩ from baker3_esse_11) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨5, baker3A12⟩ ⟨5, baker3A13⟩ from baker3_esse_12) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨5, baker3A13⟩ ⟨4, baker3A14⟩ from baker3_esse_13) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨4, baker3A14⟩ ⟨3, baker3A15⟩ from baker3_esse_14) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨3, baker3A15⟩ ⟨2, baker3A16⟩ from baker3_esse_15) ?_
  refine Relation.ReflTransGen.head
    (show ESSERel ⟨2, baker3A16⟩ ⟨2, bakerB3⟩ from baker3_esse_16) ?_
  exact Relation.ReflTransGen.refl

/-! ## Main results -/

/-- **Ashley's eight-by-eight is SSE to `(2)`** (Jeandel, arXiv:2609.03567, §Results
"The Ashley example"): Ashley's eight-by-eight matrix is strong shift equivalent over
`ℤ₊` to the one-by-one matrix `(2)`.  Proved by the 23-step certificate of the appendix
"Ashley eight-by-eight is SSE to the matrix (2) (optimized)", each step kernel-checked. -/
theorem ashley_sse_two : SSE ⟨8, ashley⟩ ⟨1, !![2]⟩ :=
  SSE.of_reflTransGen ashley_chain

/-- **Baker's matrices at `k = 3`** (Jeandel, arXiv:2609.03567, Theorem `thm:baker`):
`[[1, 4], [3, 1]]` and `[[1, 12], [1, 1]]` are strong shift equivalent over `ℤ₊`.
Proved by the 17-step certificate of the appendix "A_3 is SSE to B_3 (optimized)". -/
theorem baker3_sse : SSE ⟨2, bakerA3⟩ ⟨2, bakerB3⟩ :=
  SSE.of_reflTransGen baker3_chain

end Candidates.CombinatorialSearchStrongShift
