import Mathlib

/-!
# Total degree under polynomial composition (`aeval`)

Mathlib's `MvPolynomial` degree API bounds the total degree of sums
(`totalDegree_add`, `totalDegree_finsetSum`), products (`totalDegree_mul`,
`totalDegree_finsetProd`) and powers (`totalDegree_pow`), and it bounds
substitution of *one-variable* polynomials (`MvPolynomial.aeval_natDegree_le`,
in `Mathlib/RingTheory/Polynomial/Basic.lean`) — but it has no bound for a
multivariate-to-multivariate *composition* `aeval f p`. This file fills that
gap and packages the surrounding kit:

* `Xlib.TotalDegreeAeval.totalDegree_aeval_le` — **the gap**: if every `f i`
  has total degree `≤ d`, then `aeval f p : MvPolynomial τ R` has total degree
  `≤ p.totalDegree * d`. This is the degree-composition inequality
  `deg (p ∘ f) ≤ deg p · max deg f`, absent from Mathlib for multivariate
  targets.
* `Xlib.TotalDegreeAeval.totalDegree_aeval_le_sup_vars` — the sharp form:
  `d = ⊔ i ∈ p.vars, totalDegree (f i)`, with the sup over the variables
  actually occurring in `p` (no finiteness assumption on the variable type).
* `Xlib.TotalDegreeAeval.totalDegree_aeval_le_sup` — corollary over a
  `Fintype` variable set with `d = ⊔ i, totalDegree (f i)`.
* `Xlib.TotalDegreeAeval.natDegree_aeval_le` — the one-variable-target bound,
  restated in composition-friendly form; this one is **not** new: it is
  Mathlib's `MvPolynomial.aeval_natDegree_le` (of which it is a direct
  instance, and from which it is derived below). Kept as the workhorse for
  restricting a multivariate circuit output to a single input line.
* `Xlib.TotalDegreeAeval.eval_aeval` — evaluation commutes with the
  substitution: `(aeval g p).eval x = eval (fun i => (g i).eval x) p`
  (no direct Mathlib counterpart under this or similar names).

These are the enabling lemmas for the shear-circuit degree engine
(`Xlib.ShearCircuit`) and the reversible-inversion lower bound
(`Xlib.ShearInversionLB`): a composition of `s` multiply-add gates has
coordinate degree `≤ 2 ^ s`, so a target of algebraic degree `D` needs
`≥ log₂ D` gates.
-/

namespace Xlib.TotalDegreeAeval

open MvPolynomial

variable {R : Type*} [CommSemiring R] {σ τ : Type*}

/-- **Total degree under composition.** If every substituted polynomial `f i`
has total degree at most `d`, then `aeval f p` has total degree at most
`p.totalDegree * d`. -/
theorem totalDegree_aeval_le (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R)
    {d : ℕ} (hf : ∀ i, (f i).totalDegree ≤ d) :
    (aeval f p).totalDegree ≤ p.totalDegree * d := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  calc (∏ i ∈ m.support, f i ^ m i).totalDegree
      ≤ ∑ i ∈ m.support, (f i ^ m i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i * d :=
        Finset.sum_le_sum fun i _ =>
          (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i))
    _ = (m.sum fun _ e => e) * d := by rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ p.totalDegree * d := Nat.mul_le_mul_right _ (le_totalDegree hm)

/-- Composition bound with the sup of the degrees of the substituted
polynomials over the variables actually occurring in `p`:
`deg (p ∘ f) ≤ deg p · (⊔ i ∈ p.vars, deg (f i))`. Sharper than
`totalDegree_aeval_le_sup`, and with no finiteness assumption on `σ`. -/
theorem totalDegree_aeval_le_sup_vars (f : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) :
    (aeval f p).totalDegree
      ≤ p.totalDegree * p.vars.sup fun i => (f i).totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  calc (∏ i ∈ m.support, f i ^ m i).totalDegree
      ≤ ∑ i ∈ m.support, (f i ^ m i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i * p.vars.sup fun i => (f i).totalDegree :=
        Finset.sum_le_sum fun i hi =>
          (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _
            (Finset.le_sup (f := fun i => (f i).totalDegree)
              ((mem_vars_iff_mem_support i).mpr ⟨m, hm, hi⟩)))
    _ = (m.sum fun _ e => e) * p.vars.sup fun i => (f i).totalDegree := by
        rw [Finsupp.sum, Finset.sum_mul]
    _ ≤ p.totalDegree * p.vars.sup fun i => (f i).totalDegree :=
        Nat.mul_le_mul_right _ (le_totalDegree hm)

/-- Composition bound with the sup of the degrees of the substituted
polynomials: `deg (p ∘ f) ≤ deg p · (⊔ i, deg (f i))`. Corollary of the
sharper `totalDegree_aeval_le_sup_vars`. -/
theorem totalDegree_aeval_le_sup [Fintype σ] (f : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) :
    (aeval f p).totalDegree
      ≤ p.totalDegree * Finset.univ.sup fun i => (f i).totalDegree :=
  (totalDegree_aeval_le_sup_vars f p).trans
    (Nat.mul_le_mul_left _ (Finset.sup_mono (Finset.subset_univ _)))

/-- **Degree under restriction to one variable.** Substituting one-variable
polynomials of `natDegree ≤ d` for the variables of `p` produces a
one-variable polynomial of `natDegree ≤ p.totalDegree * d`.

Not new: this is Mathlib's `MvPolynomial.aeval_natDegree_le` instantiated at
`m := p.totalDegree`; recorded here in the form the circuit lower bounds
consume. -/
theorem natDegree_aeval_le (f : σ → Polynomial R) (p : MvPolynomial σ R)
    {d : ℕ} (hf : ∀ i, (f i).natDegree ≤ d) :
    (aeval f p).natDegree ≤ p.totalDegree * d :=
  MvPolynomial.aeval_natDegree_le p le_rfl f hf

/-- Evaluating a composition: `(aeval g p).eval x` is `p` evaluated at the
point `i ↦ (g i).eval x`. -/
theorem eval_aeval (g : σ → Polynomial R) (x : R) (p : MvPolynomial σ R) :
    (aeval g p).eval x = eval (fun i => (g i).eval x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end Xlib.TotalDegreeAeval
