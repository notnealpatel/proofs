import Mathlib

/-!
# Shear circuits and the degree-doubling engine

The reversible-arithmetic cost model over a commutative (semi)ring `k`:
a machine with `n` registers `Fin n → k`, whose programs are lists of two
kinds of gates,

* `Gate.affine M c` — an affine layer `x ↦ M x + c` (these are "free"), and
* `Gate.shear i j t` — the reversible multiply-add `x t ← x t + x i * x j`,
  the `k`-algebraic Toffoli gate and the single nonlinear primitive; it is the
  "nonscalar multiplication" of arithmetic-circuit complexity.

`ShearEC.ShearAddition` treats the single-shear (`s = 1`, degree-2) slice of this
model; this file is the general engine.

Every register of a circuit is a polynomial in the initial register values
(`Circuit.polys`, with `Circuit.run_eq_eval_polys` the compatibility between
running the circuit and evaluating its polynomials). The engine theorem
(`Circuit.totalDegree_polys_le`):

> after a circuit containing `s` shear gates, every register holds a
> polynomial of total degree `≤ 2 ^ s`.

Affine layers preserve degree; a multiply-add at most doubles it. This is the
reusable lower-bound tool: computing any coordinate function of algebraic
degree `D` needs at least `log₂ D` shears (`ShearEC.ShearInversionLB` instantiates
this for modular inversion, where `D = p - 2`).

The shear gate with distinct registers is genuinely reversible:
`shearEquiv` packages it as an `Equiv` of the register file, its inverse
being the same shear with a subtraction. The degree bound holds with **no**
invertibility assumption on the affine layers — the lower bounds apply a
fortiori to the reversible-affine subclass.
-/

namespace ShearEC.ShearCircuit

open MvPolynomial

/-- A gate of the reversible arithmetic machine on `n` registers over `k`:
either a free affine layer `x ↦ M x + c`, or the multiply-add shear
`x t ← x t + x i * x j`. -/
inductive Gate (n : ℕ) (k : Type*) where
  | affine (M : Fin n → Fin n → k) (c : Fin n → k) : Gate n k
  | shear (i j t : Fin n) : Gate n k

variable {k : Type*} [CommSemiring k] {n : ℕ}

namespace Gate

/-- Operational semantics of one gate on a register file. -/
def app : Gate n k → (Fin n → k) → Fin n → k
  | affine M c, x, t => (∑ j, M t j * x j) + c t
  | shear i j t₀, x, t => if t = t₀ then x t₀ + x i * x j else x t

/-- Symbolic semantics: one gate acting on registers holding polynomials in
the initial register values. -/
noncomputable def polyApp :
    Gate n k → (Fin n → MvPolynomial (Fin n) k) → Fin n → MvPolynomial (Fin n) k
  | affine M c, p, t => (∑ j, C (M t j) * p j) + C (c t)
  | shear i j t₀, p, t => if t = t₀ then p t₀ + p i * p j else p t

/-- Evaluating the symbolic step is the operational step on evaluations. -/
lemma eval_polyApp (g : Gate n k) (p : Fin n → MvPolynomial (Fin n) k)
    (x : Fin n → k) (t : Fin n) :
    eval x (g.polyApp p t) = g.app (fun i => eval x (p i)) t := by
  cases g with
  | affine M c => simp [polyApp, app]
  | shear i j t₀ => by_cases h : t = t₀ <;> simp [polyApp, app, h]

/-- Affine layers do not increase the register degree bound. -/
lemma totalDegree_polyApp_affine_le (M : Fin n → Fin n → k) (c : Fin n → k)
    (p : Fin n → MvPolynomial (Fin n) k) {d : ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ d) (t : Fin n) :
    ((affine M c).polyApp p t).totalDegree ≤ d := by
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine totalDegree_finsetSum_le fun j _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact hp j
  · simp [totalDegree_C]

/-- A shear at most doubles the register degree bound. -/
lemma totalDegree_polyApp_shear_le (i j t₀ : Fin n)
    (p : Fin n → MvPolynomial (Fin n) k) {d : ℕ}
    (hp : ∀ r, (p r).totalDegree ≤ d) (t : Fin n) :
    ((shear i j t₀).polyApp p t).totalDegree ≤ 2 * d := by
  by_cases h : t = t₀
  · simp only [polyApp, if_pos h]
    refine (totalDegree_add _ _).trans (max_le ((hp t₀).trans (by omega)) ?_)
    refine (totalDegree_mul _ _).trans ?_
    have hi := hp i
    have hj := hp j
    omega
  · simp only [polyApp, if_neg h]
    exact (hp t).trans (by omega)

end Gate

/-- A shear circuit: a list of gates, applied left to right. -/
abbrev Circuit (n : ℕ) (k : Type*) := List (Gate n k)

namespace Circuit

/-- Run a circuit on an initial register file. -/
def run (C : Circuit n k) (x : Fin n → k) : Fin n → k :=
  C.foldl (fun s g => g.app s) x

/-- Symbolically run a circuit from an arbitrary polynomial register file. -/
noncomputable def polysFrom (C : Circuit n k)
    (p : Fin n → MvPolynomial (Fin n) k) : Fin n → MvPolynomial (Fin n) k :=
  C.foldl (fun q g => g.polyApp q) p

/-- The registers of a circuit as polynomials in the initial register
values. -/
noncomputable def polys (C : Circuit n k) : Fin n → MvPolynomial (Fin n) k :=
  polysFrom C X

/-- The number of shear (multiply-add) gates: the nonscalar-multiplication
cost of the circuit. -/
def shearCount : Circuit n k → ℕ
  | [] => 0
  | Gate.affine _ _ :: C => shearCount C
  | Gate.shear _ _ _ :: C => shearCount C + 1

omit [CommSemiring k] in
@[simp] lemma shearCount_nil : shearCount ([] : Circuit n k) = 0 := rfl

omit [CommSemiring k] in
@[simp] lemma shearCount_affine_cons (M : Fin n → Fin n → k) (c : Fin n → k)
    (C : Circuit n k) : shearCount (Gate.affine M c :: C) = shearCount C := rfl

omit [CommSemiring k] in
@[simp] lemma shearCount_shear_cons (i j t : Fin n) (C : Circuit n k) :
    shearCount (Gate.shear i j t :: C) = shearCount C + 1 := rfl

/-- Evaluating the symbolic run at `x` is the operational run on the
evaluated register file. -/
lemma eval_polysFrom (C : Circuit n k) (p : Fin n → MvPolynomial (Fin n) k)
    (x : Fin n → k) :
    (fun t => eval x (polysFrom C p t)) = run C (fun t => eval x (p t)) := by
  induction C generalizing p with
  | nil => rfl
  | cons g C ih =>
      show (fun t => eval x (polysFrom C (g.polyApp p) t))
        = run C (g.app fun t => eval x (p t))
      rw [ih (g.polyApp p)]
      congr 1
      funext t
      exact g.eval_polyApp p x t

/-- **Symbolic soundness**: running the circuit is evaluating its register
polynomials at the initial register values. -/
theorem run_eq_eval_polys (C : Circuit n k) (x : Fin n → k) (t : Fin n) :
    run C x t = eval x (polys C t) := by
  calc run C x t
      = run C (fun r => eval x (X r : MvPolynomial (Fin n) k)) t := by
        congr 1
        funext r
        simp
    _ = eval x (polysFrom C X t) := (congrFun (eval_polysFrom C X x) t).symm

/-- Degree engine, general form: if every initial register polynomial has
total degree `≤ d`, then after a circuit with `s` shears every register
polynomial has total degree `≤ d * 2 ^ s`. -/
theorem totalDegree_polysFrom_le (C : Circuit n k)
    (p : Fin n → MvPolynomial (Fin n) k) {d : ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ d) (t : Fin n) :
    (polysFrom C p t).totalDegree ≤ d * 2 ^ shearCount C := by
  induction C generalizing p d with
  | nil => simpa [polysFrom] using hp t
  | cons g C ih =>
      cases g with
      | affine M c =>
          exact ih ((Gate.affine M c).polyApp p)
            fun r => Gate.totalDegree_polyApp_affine_le M c p hp r
      | shear i j t₀ =>
          have h2 : ∀ r, (((Gate.shear i j t₀).polyApp p) r).totalDegree ≤ 2 * d :=
            fun r => Gate.totalDegree_polyApp_shear_le i j t₀ p hp r
          refine (ih ((Gate.shear i j t₀).polyApp p) h2).trans_eq ?_
          show 2 * d * 2 ^ shearCount C = d * 2 ^ (shearCount C + 1)
          ring

/-- `X i` has total degree at most `1` (with no nontriviality assumption). -/
lemma totalDegree_X_le (i : Fin n) :
    (X i : MvPolynomial (Fin n) k).totalDegree ≤ 1 :=
  (totalDegree_monomial_le _ _).trans (by simp)

/-- **The degree-doubling engine.** Every register of a circuit with `s`
shear gates holds a polynomial of total degree at most `2 ^ s` in the initial
register values. Hence computing any coordinate function of algebraic degree
`D` requires at least `log₂ D` multiply-add gates. -/
theorem totalDegree_polys_le (C : Circuit n k) (t : Fin n) :
    (polys C t).totalDegree ≤ 2 ^ shearCount C := by
  simpa [polys] using totalDegree_polysFrom_le C X (fun i => totalDegree_X_le i) t

end Circuit

section Reversible

variable {R : Type*} [CommRing R]

/-- Over a ring, the shear gate on three distinct registers is reversible: it
is an `Equiv` of the register file whose inverse is the corresponding
multiply-*subtract*. This is the `n`-register version of
`ShearEC.ShearAddition.shear`. -/
def shearEquiv (i j t₀ : Fin n) (hi : t₀ ≠ i) (hj : t₀ ≠ j) :
    (Fin n → R) ≃ (Fin n → R) where
  toFun := (Gate.shear i j t₀).app
  invFun y t := if t = t₀ then y t₀ - y i * y j else y t
  left_inv x := by
    funext t
    by_cases h : t = t₀
    · subst h
      simp [Gate.app, hi.symm, hj.symm]
    · simp [Gate.app, h]
  right_inv y := by
    funext t
    by_cases h : t = t₀
    · subst h
      simp [Gate.app, hi.symm, hj.symm]
    · simp [Gate.app, h]

@[simp] lemma shearEquiv_apply (i j t₀ : Fin n) (hi : t₀ ≠ i) (hj : t₀ ≠ j)
    (x : Fin n → R) : shearEquiv i j t₀ hi hj x = (Gate.shear i j t₀).app x :=
  rfl

end Reversible

end ShearEC.ShearCircuit
