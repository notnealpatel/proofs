/-
# Shift-equivalence obstruction for `E_n = [[1,n],[2,1]]` versus `F_n = [[1,2n],[1,1]]`

## Source

Emmanuel Jeandel, *Combinatorial Search for Strong Shift Equivalence*,
arXiv:2609.03567.  Retrieved 2026-10-21.

* Definitions (§Background, "Definitions" and Definition `defn:se`):
  ESSE (`A = RS`, `B = SR`), SSE (chain `A = A_1, ..., A_l = B` with
  `A_i` ESSE to `A_{i+1}`) and shift equivalence of lag `k`
  (`AR = RB`, `SA = BS`, `A^k = RS`, `B^k = SR`).  The paper notes
  (after `defn:se`) that an SSE `A = R_1 S_1, S_1 R_1 = M_2, ...` yields an
  SE with `R = R_1 ⋯ R_n`, `S = S_n ⋯ S_1` (Williams).
* §Results, "Other 2 by 2 matrices", the Lemma (verbatim):

  > Let $n$ and $p$ be integers. Let $A = \begin{pmatrix} 1 & n \\ p & 1
  > \end{pmatrix}$ and $B = \begin{pmatrix} 1 & np \\ 1 & 1\end{pmatrix}$.
  > If $np - 1$ is prime and neither $p$ nor $-p$ is a square modulo $n$,
  > then $A$ is not shift equivalent to $B$.

* The Theorem it serves (verbatim): "The matrices $E_n$ and $F_n$ are SSE
  for all odd $n < 50$ except $n = 15, 21, 37, 45$. For these four values,
  the matrices are not even shift equivalent, and hence not SSE."

## Status

Proved in the paper (the Lemma and the negative half of the Theorem).  The
positive half (SSE certificates for the other odd `n < 50`) lives on the
author's website and is *not* formalized here.

## What is formalized

1. Infrastructure over an arbitrary semiring: `ShiftEquivLag`, `ShiftEquiv`,
   `ESSE`, `SSE`; ESSE gives SE of lag 1, SE is reflexive, symmetric and
   transitive (lags add), hence SSE implies SE; SE transports along ring
   homomorphisms (used for `ℕ → ℤ`).
2. The paper's Lemma over `ℤ` (`not_shiftEquiv_of_prime`), stated for
   integers `n p` as in the paper; "prime" is `Prime` in `ℤ` (so it covers
   `np - 1 = ±q`), and "square modulo `n`" is `IsSquare` in `ZMod |n|`.
   The proof uses only `AR = RB` and `A^k = RS`.
3. The corollaries: `E_n` and `F_n` are not SE (over `ℤ`, hence over `ℕ`)
   and not SSE over `ℕ` for `n = 15, 21, 37, 45`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.ShiftEquivalenceObstruction

open Matrix

section Infrastructure

variable {R : Type*} [Semiring R]

/-- Shift equivalence of lag `k` (Jeandel, Definition `defn:se`, after
Williams): there are rectangular matrices `X`, `Y` with `A X = X B`,
`Y A = B Y`, `A ^ k = X Y` and `B ^ k = Y X`. -/
def ShiftEquivLag {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix n n R) (k : ℕ) : Prop :=
  ∃ (X : Matrix m n R) (Y : Matrix n m R),
    A * X = X * B ∧ Y * A = B * Y ∧ A ^ k = X * Y ∧ B ^ k = Y * X

/-- Shift equivalence (Jeandel, Definition `defn:se`): shift equivalence of
some lag `k`. -/
def ShiftEquiv {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix n n R) : Prop :=
  ∃ k : ℕ, ShiftEquivLag A B k

/-- A square matrix over `R` of some size `k`, packaged with its size so that
matrices of different sizes can be compared. -/
abbrev SqMat (R : Type*) : Type _ := Σ k : ℕ, Matrix (Fin k) (Fin k) R

/-- Elementary strong shift equivalence (Jeandel, §Background): `A = X Y`
and `B = Y X` for some rectangular `X`, `Y` over `R`. -/
def ESSE (A B : SqMat R) : Prop :=
  ∃ (X : Matrix (Fin A.1) (Fin B.1) R) (Y : Matrix (Fin B.1) (Fin A.1) R),
    A.2 = X * Y ∧ B.2 = Y * X

/-- Strong shift equivalence (Jeandel, §Background): a chain
`A = A_1, ..., A_l = B` with each `A_i` ESSE to `A_{i+1}`. -/
def SSE (A B : SqMat R) : Prop :=
  Relation.ReflTransGen ESSE A B

variable {m n o : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype o] [DecidableEq o]

/-- An intertwining relation `A X = X B` propagates to powers:
`A ^ j X = X B ^ j`. -/
theorem pow_mul_eq_mul_pow {A : Matrix m m R} {B : Matrix n n R} {X : Matrix m n R}
    (h : A * X = X * B) (j : ℕ) : A ^ j * X = X * B ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

/-- Every square matrix is shift equivalent to itself with lag `0`. -/
theorem shiftEquivLag_refl (A : Matrix m m R) : ShiftEquivLag A A 0 :=
  ⟨1, 1, by simp, by simp, by simp, by simp⟩

/-- Shift equivalence of lag `k` is symmetric. -/
theorem ShiftEquivLag.symm {A : Matrix m m R} {B : Matrix n n R} {k : ℕ}
    (h : ShiftEquivLag A B k) : ShiftEquivLag B A k := by
  obtain ⟨X, Y, hAX, hYA, hAk, hBk⟩ := h
  exact ⟨Y, X, hYA.symm, hAX.symm, hBk, hAk⟩

/-- Shift equivalence is transitive, and the lags add:
take `X = X₁ X₂` and `Y = Y₂ Y₁`. -/
theorem ShiftEquivLag.trans {A : Matrix m m R} {B : Matrix n n R} {C : Matrix o o R}
    {k₁ k₂ : ℕ} (h₁ : ShiftEquivLag A B k₁) (h₂ : ShiftEquivLag B C k₂) :
    ShiftEquivLag A C (k₁ + k₂) := by
  obtain ⟨X₁, Y₁, hAX₁, hY₁A, hAk₁, hBk₁⟩ := h₁
  obtain ⟨X₂, Y₂, hBX₂, hY₂B, hBk₂, hCk₂⟩ := h₂
  refine ⟨X₁ * X₂, Y₂ * Y₁, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, hAX₁, Matrix.mul_assoc, hBX₂, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, hY₁A, ← Matrix.mul_assoc, hY₂B, Matrix.mul_assoc]
  · have hcomm : A ^ k₂ * X₁ = X₁ * B ^ k₂ := pow_mul_eq_mul_pow hAX₁ k₂
    calc A ^ (k₁ + k₂) = A ^ k₂ * A ^ k₁ := by rw [add_comm, pow_add]
      _ = A ^ k₂ * (X₁ * Y₁) := by rw [hAk₁]
      _ = X₁ * B ^ k₂ * Y₁ := by rw [← Matrix.mul_assoc, hcomm]
      _ = X₁ * X₂ * (Y₂ * Y₁) := by
        rw [hBk₂]; simp only [Matrix.mul_assoc]
  · have hcomm : C ^ k₁ * Y₂ = Y₂ * B ^ k₁ := pow_mul_eq_mul_pow hY₂B.symm k₁
    calc C ^ (k₁ + k₂) = C ^ k₁ * C ^ k₂ := by rw [pow_add]
      _ = C ^ k₁ * (Y₂ * X₂) := by rw [hCk₂]
      _ = Y₂ * B ^ k₁ * X₂ := by rw [← Matrix.mul_assoc, hcomm]
      _ = Y₂ * Y₁ * (X₁ * X₂) := by
        rw [hBk₁]; simp only [Matrix.mul_assoc]

/-- Shift equivalence is reflexive. -/
theorem ShiftEquiv.refl (A : Matrix m m R) : ShiftEquiv A A :=
  ⟨0, shiftEquivLag_refl A⟩

/-- Shift equivalence is symmetric. -/
theorem ShiftEquiv.symm {A : Matrix m m R} {B : Matrix n n R} (h : ShiftEquiv A B) :
    ShiftEquiv B A := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk.symm⟩

/-- Shift equivalence is transitive. -/
theorem ShiftEquiv.trans {A : Matrix m m R} {B : Matrix n n R} {C : Matrix o o R}
    (h₁ : ShiftEquiv A B) (h₂ : ShiftEquiv B C) : ShiftEquiv A C := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  exact ⟨k₁ + k₂, hk₁.trans hk₂⟩

/-- An elementary strong shift equivalence `A = X Y`, `B = Y X` is a shift
equivalence of lag `1` (with the same `X`, `Y`). -/
theorem ESSE.shiftEquivLag_one {A B : SqMat R} (h : ESSE A B) :
    ShiftEquivLag A.2 B.2 1 := by
  obtain ⟨X, Y, hA, hB⟩ := h
  refine ⟨X, Y, ?_, ?_, ?_, ?_⟩
  · rw [hA, hB, Matrix.mul_assoc]
  · rw [hA, hB, Matrix.mul_assoc]
  · rw [pow_one, hA]
  · rw [pow_one, hB]

/-- Williams: strong shift equivalence implies shift equivalence. -/
theorem SSE.shiftEquiv {A B : SqMat R} (h : SSE A B) : ShiftEquiv A.2 B.2 := by
  induction h with
  | refl => exact ShiftEquiv.refl _
  | tail _ hBC ih => exact ih.trans ⟨1, hBC.shiftEquivLag_one⟩

/-- Shift equivalence of lag `k` is transported along a ring homomorphism
applied entrywise. -/
theorem ShiftEquivLag.map {S : Type*} [Semiring S] (f : R →+* S)
    {A : Matrix m m R} {B : Matrix n n R} {k : ℕ} (h : ShiftEquivLag A B k) :
    ShiftEquivLag (A.map f) (B.map f) k := by
  obtain ⟨X, Y, hAX, hYA, hAk, hBk⟩ := h
  refine ⟨X.map f, Y.map f, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, ← Matrix.map_mul, hAX]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, hYA]
  · rw [← Matrix.map_pow, ← Matrix.map_mul, hAk]
  · rw [← Matrix.map_pow, ← Matrix.map_mul, hBk]

/-- Shift equivalence is transported along a ring homomorphism applied
entrywise. -/
theorem ShiftEquiv.map {S : Type*} [Semiring S] (f : R →+* S)
    {A : Matrix m m R} {B : Matrix n n R} (h : ShiftEquiv A B) :
    ShiftEquiv (A.map f) (B.map f) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk.map f⟩

end Infrastructure

section Lemma

/-- The matrix `A = [[1, n], [p, 1]]` of Jeandel's Lemma (§"Other 2 by 2
matrices"). -/
def lemmaA (n p : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, n; p, 1]

/-- The matrix `B = [[1, n p], [1, 1]]` of Jeandel's Lemma (§"Other 2 by 2
matrices"). -/
def lemmaB (n p : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, n * p; 1, 1]

example : lemmaA 15 2 = !![1, 15; 2, 1] := rfl
example : lemmaB 15 2 = !![1, 30; 1, 1] := rfl

/-- `det A = 1 - n p`. -/
theorem det_lemmaA (n p : ℤ) : (lemmaA n p).det = 1 - n * p := by
  rw [lemmaA, Matrix.det_fin_two_of]
  ring

/-- If `A X = X B` then `X = [[a, n b], [b, p a]]`, so
`det X = p a ^ 2 - n b ^ 2` with `a = X 0 0`, `b = X 1 0`. -/
theorem det_eq_of_lemmaA_mul_eq (n p : ℤ) (X : Matrix (Fin 2) (Fin 2) ℤ)
    (h : lemmaA n p * X = X * lemmaB n p) :
    X.det = p * X 0 0 ^ 2 - n * X 1 0 ^ 2 := by
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp only [lemmaA, lemmaB, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
    cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two, one_mul, mul_one,
    add_right_inj] at h00 h10
  rw [Matrix.det_fin_two]
  linear_combination X 1 0 * h00 - X 0 0 * h10

/-- `n` vanishes in `ZMod |n|`. -/
theorem intCast_self_zmod_natAbs (n : ℤ) : ((n : ℤ) : ZMod n.natAbs) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd n n.natAbs).2 (Int.natAbs_dvd.2 dvd_rfl)

/-- **Jeandel's Lemma** (arXiv:2609.03567, §"Other 2 by 2 matrices"): let
`n p` be integers, `A = [[1, n], [p, 1]]` and `B = [[1, n p], [1, 1]]`.
If `n p - 1` is prime and neither `p` nor `-p` is a square modulo `n`,
then `A` is not shift equivalent to `B` (over `ℤ`, hence over `ℕ`). -/
theorem not_shiftEquiv_of_prime (n p : ℤ) (hprime : Prime (n * p - 1))
    (hp : ¬ IsSquare (p : ZMod n.natAbs)) (hnp : ¬ IsSquare (-(p : ZMod n.natAbs))) :
    ¬ ShiftEquiv (lemmaA n p) (lemmaB n p) := by
  rintro ⟨k, X, Y, hAX, -, hAk, -⟩
  have hdvd : X.det ∣ (1 - n * p) ^ k :=
    ⟨Y.det, by rw [← Matrix.det_mul, ← hAk, Matrix.det_pow, det_lemmaA]⟩
  have hq : Prime (1 - n * p) := by
    have hneg := hprime.neg
    rwa [neg_sub] at hneg
  obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow hq k).1 hdvd
  rw [det_eq_of_lemmaA_mul_eq n p X hAX] at hassoc
  have hn0 := intCast_self_zmod_natAbs n
  rcases Int.associated_iff.1 hassoc with h | h
  · apply hp
    refine ⟨p * X 0 0, ?_⟩
    have hcast := congrArg (Int.cast : ℤ → ZMod n.natAbs) h
    push_cast [hn0] at hcast
    simp only [zero_mul, sub_zero, one_pow] at hcast
    linear_combination (-(p : ZMod n.natAbs)) * hcast
  · apply hnp
    refine ⟨p * X 0 0, ?_⟩
    have hcast := congrArg (Int.cast : ℤ → ZMod n.natAbs) h
    push_cast [hn0] at hcast
    simp only [zero_mul, sub_zero, one_pow] at hcast
    linear_combination (-(p : ZMod n.natAbs)) * hcast

end Lemma

section Corollary

/-- Jeandel's `E_n = [[1, n], [2, 1]]` over `ℕ` (§"Other 2 by 2 matrices"). -/
def matE (n : ℕ) : Matrix (Fin 2) (Fin 2) ℕ := !![1, n; 2, 1]

/-- Jeandel's `F_n = [[1, 2 n], [1, 1]]` over `ℕ` (§"Other 2 by 2 matrices"). -/
def matF (n : ℕ) : Matrix (Fin 2) (Fin 2) ℕ := !![1, 2 * n; 1, 1]

example : matE 15 = !![1, 15; 2, 1] := rfl
example : matF 15 = !![1, 30; 1, 1] := rfl

/-- Sanity check of `ESSE`: `[[1, 1], [1, 1]] = (column of ones) (row of ones)`
and `(row of ones) (column of ones) = [2]`. -/
example : ESSE (⟨2, !![1, 1; 1, 1]⟩ : SqMat ℕ) ⟨1, !![2]⟩ :=
  ⟨!![1; 1], !![1, 1], by decide, by decide⟩

/-- `E_n` cast to `ℤ` is the Lemma's `A` with `p = 2`. -/
theorem matE_map (n : ℕ) : (matE n).map (Nat.castRingHom ℤ) = lemmaA n 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matE, lemmaA]

/-- `F_n` cast to `ℤ` is the Lemma's `B` with `p = 2`. -/
theorem matF_map (n : ℕ) : (matF n).map (Nat.castRingHom ℤ) = lemmaB n 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matF, lemmaB, mul_comm]

/-- The Lemma specialised to `p = 2`: if `2 n - 1` is prime and neither `2`
nor `-2` is a square modulo `n`, then `E_n` and `F_n` are not shift
equivalent over `ℕ`. -/
theorem not_shiftEquiv_matE_matF (n : ℕ) (hprime : Prime (2 * (n : ℤ) - 1))
    (h2 : ¬ IsSquare (2 : ZMod n)) (hm2 : ¬ IsSquare (-2 : ZMod n)) :
    ¬ ShiftEquiv (matE n) (matF n) := by
  intro hSE
  have hZ := hSE.map (Nat.castRingHom ℤ)
  rw [matE_map, matF_map] at hZ
  refine not_shiftEquiv_of_prime n 2 (by rwa [mul_comm]) ?_ ?_ hZ
  · rw [Int.natAbs_natCast]
    exact_mod_cast h2
  · rw [Int.natAbs_natCast]
    exact_mod_cast hm2

/-- The Lemma specialised to `p = 2`, SSE form: if `2 n - 1` is prime and
neither `2` nor `-2` is a square modulo `n`, then `E_n` and `F_n` are not
strong shift equivalent over `ℕ`. -/
theorem not_SSE_matE_matF (n : ℕ) (hprime : Prime (2 * (n : ℤ) - 1))
    (h2 : ¬ IsSquare (2 : ZMod n)) (hm2 : ¬ IsSquare (-2 : ZMod n)) :
    ¬ SSE (⟨2, matE n⟩ : SqMat ℕ) ⟨2, matF n⟩ := fun h =>
  not_shiftEquiv_matE_matF n hprime h2 hm2 h.shiftEquiv

/-- Jeandel (arXiv:2609.03567), Theorem in §"Other 2 by 2 matrices",
negative half: for `n = 15, 21, 37, 45` the matrices `E_n = [[1, n], [2, 1]]`
and `F_n = [[1, 2 n], [1, 1]]` are not shift equivalent over `ℕ`. -/
theorem not_shiftEquiv_matE_matF_exceptional (n : ℕ)
    (hn : n = 15 ∨ n = 21 ∨ n = 37 ∨ n = 45) :
    ¬ ShiftEquiv (matE n) (matF n) := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact not_shiftEquiv_matE_matF 15 (by norm_num [Int.prime_iff_natAbs_prime])
      (by decide) (by decide)
  · exact not_shiftEquiv_matE_matF 21 (by norm_num [Int.prime_iff_natAbs_prime])
      (by decide) (by decide)
  · exact not_shiftEquiv_matE_matF 37 (by norm_num [Int.prime_iff_natAbs_prime])
      (by decide) (by decide)
  · exact not_shiftEquiv_matE_matF 45 (by norm_num [Int.prime_iff_natAbs_prime])
      (by decide) (by decide)

/-- Jeandel (arXiv:2609.03567), Theorem in §"Other 2 by 2 matrices",
negative half: for `n = 15, 21, 37, 45` the matrices `E_n = [[1, n], [2, 1]]`
and `F_n = [[1, 2 n], [1, 1]]` are not strong shift equivalent over `ℕ`. -/
theorem not_SSE_matE_matF_exceptional (n : ℕ)
    (hn : n = 15 ∨ n = 21 ∨ n = 37 ∨ n = 45) :
    ¬ SSE (⟨2, matE n⟩ : SqMat ℕ) ⟨2, matF n⟩ := fun h =>
  not_shiftEquiv_matE_matF_exceptional n hn h.shiftEquiv

end Corollary

end Candidates.ShiftEquivalenceObstruction
