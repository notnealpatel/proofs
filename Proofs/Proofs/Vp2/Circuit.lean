/-
  Vp2/Circuit — a minimal arithmetic-circuit model (expression trees)
  with size and evaluation into `MvPolynomial`, plus the honest
  size-bound predicates (`ComputedInSize`, `VPFamily`) for the Vp2
  campaign.

  WHY THIS FILE EXISTS. Vp2.lean carries `IsVP` ("computable by a
  poly(n³)-size algebraic circuit") as a sorry-def, blocked on task card
  `VPCircuit`: Mathlib has no algebraic computation model at all (its
  "circuits" are matroid circuits; `Mathlib.Computability` is
  automata/TM/partrec only; the 2026-07 literature sweep found no prior
  ITP formalization either). This file supplies the missing model,
  minimally.

  THE MODEL, AND ITS HONESTY ENVELOPE. `Circuit σ k` is an expression
  TREE (a formula): leaves are variables `X i` and constants `C c`,
  gates are `add`/`mul`; `size` counts nodes; `eval` interprets a tree
  as a polynomial in `MvPolynomial σ k`. Trees do not share
  subcomputations, so `size` is FORMULA size, which upper-bounds
  DAG-circuit size. Consequently:
    · every positive statement proved here ("this polynomial is computed
      in size ≤ s", `ComputedInSize`) is a fortiori a DAG-circuit upper
      bound — the honest direction, and the only direction claimed;
    · a barrier-style statement quantifying over ALL poly-size circuits
      would need the DAG model (formulas = the class VF ⊆ VP, possibly
      strictly); nothing here states one.

  Proved here (all sorry-free):
    · simp API for `size`/`eval` per constructor;
    · builders `listSum`/`listProd`/`finsetSum`/`finsetProd`/`pow`/
      `monomial` with EXACT size lemmas, not just bounds;
    · degree bound `totalDegree_eval_le : (eval f).totalDegree ≤ size f`;
    · completeness `exists_circuit`: every `p : MvPolynomial σ k` (its
      support is finite by construction) is computed by a circuit of
      size ≤ #supp(p)·(4·totalDegree(p) + 4) + 1 — the model is not
      vacuous;
    · `ComputedInSize s p` (∃ circuit of size ≤ s computing `p`) and the
      family-level class `VPFamily D` (∃ c, ∀ n, `D n` is computed in
      size (n³ + c)^c — the standard cofinal form of "poly(n³)", where
      n³ = #(EntryIndex n) is the number of tensor-entry variables);
    · vacuity of single-n "poly-size": `exists_computedInSize` shows
      EVERY polynomial satisfies `∃ s, ComputedInSize s p`, which is why
      `Vp2.IsVP` at a single fixed `n` cannot be made non-vacuous
      without pinning an arbitrary threshold — see the sharpened `IsVP`
      annotation in Vp2.lean;
    · determinant circuits by Leibniz expansion (`Matrix.det_apply'`):
      `Circuit.det` with `eval_det` and `size_det_le`; for an m×m matrix
      of variables this gives size ≤ m!·(2m + 4) + 1;
    · the connection to Pf1's border-rank infrastructure
      (Vp2/BorderRank.lean): the generic-flattening (r+1)×(r+1) minor —
      the very polynomial witnessing `Vp2.exists_flattening_distinguisher`
      in Vp2.lean — satisfies
      `ComputedInSize ((r+1)!·(2(r+1)+4)+1)`
      (`computedInSize_flatteningMinor`), and for FIXED `r` the minor
      family n ↦ minor is a genuine `VPFamily`
      (`vpFamily_flatteningMinorFamily`), since that size bound is
      constant in n. This is the honest, family-level content of the
      `isVP` leg of `exists_flattening_vpDistinguisher`.

  Primary sources for the notions being modeled (labels as in
  docs/Vp1.md): FSV arXiv:1701.05328 (Defn 2.1: distinguishers computed
  by poly-size algebraic circuits); GKSS arXiv:1701.01717 (algebraic
  natural proofs; VP-naturality is a condition on circuit FAMILIES).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Proofs.Vp2.BorderRank
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Vp2

/-- An arithmetic circuit over variables `σ` with constants from `k`,
as an expression TREE (formula): leaves are variables and constants,
inner gates are `add`/`mul`, and no subcomputation is shared. Tree size
upper-bounds DAG-circuit size, so every `ComputedInSize` claim below is
an honest circuit upper bound. -/
inductive Circuit (σ : Type*) (k : Type*) where
  /-- an input gate carrying the variable `i` -/
  | X (i : σ) : Circuit σ k
  /-- a constant gate carrying `c : k` -/
  | C (c : k) : Circuit σ k
  /-- an addition gate -/
  | add (f g : Circuit σ k) : Circuit σ k
  /-- a multiplication gate -/
  | mul (f g : Circuit σ k) : Circuit σ k

namespace Circuit

variable {σ k : Type*}

/-! ### Size -/

/-- Circuit size: the number of gates (leaves count 1, a binary gate
counts 1 plus both subtrees). -/
def size : Circuit σ k → ℕ
  | X _ => 1
  | C _ => 1
  | add f g => f.size + g.size + 1
  | mul f g => f.size + g.size + 1

@[simp] theorem size_X (i : σ) : (X i : Circuit σ k).size = 1 := rfl

@[simp] theorem size_C (c : k) : (C c : Circuit σ k).size = 1 := rfl

@[simp] theorem size_add (f g : Circuit σ k) :
    (f.add g).size = f.size + g.size + 1 := rfl

@[simp] theorem size_mul (f g : Circuit σ k) :
    (f.mul g).size = f.size + g.size + 1 := rfl

theorem size_pos (f : Circuit σ k) : 0 < f.size := by
  cases f <;> simp only [size_X, size_C, size_add, size_mul] <;> omega

/-! ### Evaluation -/

section Eval

variable [CommSemiring k]

/-- The polynomial computed by a circuit. -/
noncomputable def eval : Circuit σ k → MvPolynomial σ k
  | X i => MvPolynomial.X i
  | C c => MvPolynomial.C c
  | add f g => f.eval + g.eval
  | mul f g => f.eval * g.eval

@[simp] theorem eval_X (i : σ) :
    (X i : Circuit σ k).eval = MvPolynomial.X i := rfl

@[simp] theorem eval_C (c : k) :
    (C c : Circuit σ k).eval = MvPolynomial.C c := rfl

@[simp] theorem eval_add (f g : Circuit σ k) :
    (f.add g).eval = f.eval + g.eval := rfl

@[simp] theorem eval_mul (f g : Circuit σ k) :
    (f.mul g).eval = f.eval * g.eval := rfl

end Eval

/-! ### Builders: list sums and products -/

/-- Sum of a list of circuits, right-associated, with `C 0` at the nil. -/
def listSum [Zero k] : List (Circuit σ k) → Circuit σ k
  | [] => C 0
  | f :: L => add f (listSum L)

@[simp] theorem listSum_nil [Zero k] :
    (listSum [] : Circuit σ k) = C 0 := rfl

@[simp] theorem listSum_cons [Zero k] (f : Circuit σ k) (L : List (Circuit σ k)) :
    listSum (f :: L) = add f (listSum L) := rfl

/-- Product of a list of circuits, right-associated, with `C 1` at the nil. -/
def listProd [One k] : List (Circuit σ k) → Circuit σ k
  | [] => C 1
  | f :: L => mul f (listProd L)

@[simp] theorem listProd_nil [One k] :
    (listProd [] : Circuit σ k) = C 1 := rfl

@[simp] theorem listProd_cons [One k] (f : Circuit σ k) (L : List (Circuit σ k)) :
    listProd (f :: L) = mul f (listProd L) := rfl

theorem eval_listSum [CommSemiring k] (L : List (Circuit σ k)) :
    (listSum L).eval = (L.map eval).sum := by
  induction L with
  | nil => simp
  | cons f L ih => simp [ih]

theorem eval_listProd [CommSemiring k] (L : List (Circuit σ k)) :
    (listProd L).eval = (L.map eval).prod := by
  induction L with
  | nil => simp
  | cons f L ih => simp [ih]

/-- Exact size of a list sum: total gate count of the summands, plus one
`add` gate per list element, plus the nil constant. -/
theorem size_listSum [Zero k] (L : List (Circuit σ k)) :
    (listSum L).size = (L.map size).sum + L.length + 1 := by
  induction L with
  | nil => simp
  | cons f L ih =>
      simp only [listSum_cons, size_add, ih, List.map_cons, List.sum_cons,
        List.length_cons]
      omega

/-- Exact size of a list product; same count as `size_listSum`. -/
theorem size_listProd [One k] (L : List (Circuit σ k)) :
    (listProd L).size = (L.map size).sum + L.length + 1 := by
  induction L with
  | nil => simp
  | cons f L ih =>
      simp only [listProd_cons, size_mul, ih, List.map_cons, List.sum_cons,
        List.length_cons]
      omega

/-! ### Builders: finset sums and products -/

variable {ι : Type*}

/-- Sum of circuits indexed by a `Finset` (via its `toList`). -/
noncomputable def finsetSum [Zero k] (s : Finset ι) (f : ι → Circuit σ k) :
    Circuit σ k :=
  listSum (s.toList.map f)

/-- Product of circuits indexed by a `Finset` (via its `toList`). -/
noncomputable def finsetProd [One k] (s : Finset ι) (f : ι → Circuit σ k) :
    Circuit σ k :=
  listProd (s.toList.map f)

theorem eval_finsetSum [CommSemiring k] (s : Finset ι) (f : ι → Circuit σ k) :
    (finsetSum s f).eval = ∑ i ∈ s, (f i).eval := by
  unfold finsetSum
  rw [eval_listSum]
  simp

theorem eval_finsetProd [CommSemiring k] (s : Finset ι) (f : ι → Circuit σ k) :
    (finsetProd s f).eval = ∏ i ∈ s, (f i).eval := by
  unfold finsetProd
  rw [eval_listProd]
  simp

/-- Exact size of a finset sum. -/
theorem size_finsetSum [Zero k] (s : Finset ι) (f : ι → Circuit σ k) :
    (finsetSum s f).size = (∑ i ∈ s, (f i).size) + s.card + 1 := by
  unfold finsetSum
  rw [size_listSum]
  simp

/-- Exact size of a finset product. -/
theorem size_finsetProd [One k] (s : Finset ι) (f : ι → Circuit σ k) :
    (finsetProd s f).size = (∑ i ∈ s, (f i).size) + s.card + 1 := by
  unfold finsetProd
  rw [size_listProd]
  simp

/-! ### Builders: powers and monomials -/

/-- `e`-th power of a circuit by repeated multiplication (`C 1` at 0). -/
def pow [One k] (f : Circuit σ k) : ℕ → Circuit σ k
  | 0 => C 1
  | e + 1 => mul f (pow f e)

@[simp] theorem pow_zero [One k] (f : Circuit σ k) : f.pow 0 = C 1 := rfl

@[simp] theorem pow_succ [One k] (f : Circuit σ k) (e : ℕ) :
    f.pow (e + 1) = mul f (f.pow e) := rfl

theorem eval_pow [CommSemiring k] (f : Circuit σ k) (e : ℕ) :
    (f.pow e).eval = f.eval ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, eval_mul, ih, _root_.pow_succ, mul_comm]

/-- Exact size of a power circuit. -/
theorem size_pow [One k] (f : Circuit σ k) (e : ℕ) :
    (f.pow e).size = e * (f.size + 1) + 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
      simp only [pow_succ, size_mul, ih]
      ring

/-- Circuit for the monomial `c · ∏ i ∈ supp(m), X i ^ m i`. -/
noncomputable def monomial [One k] (m : σ →₀ ℕ) (c : k) : Circuit σ k :=
  mul (C c) (finsetProd m.support fun i => (X i).pow (m i))

theorem eval_monomial [CommSemiring k] (m : σ →₀ ℕ) (c : k) :
    (monomial m c).eval = MvPolynomial.monomial m c := by
  unfold monomial
  rw [eval_mul, eval_C, eval_finsetProd, MvPolynomial.monomial_eq, Finsupp.prod]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by rw [eval_pow, eval_X])

/-- Exact size of a monomial circuit: `2·(degree) + 2·#supp + 3`. -/
theorem size_monomial [One k] (m : σ →₀ ℕ) (c : k) :
    (monomial m c).size = 2 * (∑ i ∈ m.support, m i) + 2 * m.support.card + 3 := by
  unfold monomial
  rw [size_mul, size_C, size_finsetProd]
  have h : (∑ i ∈ m.support, ((X i : Circuit σ k).pow (m i)).size)
      = 2 * (∑ i ∈ m.support, m i) + m.support.card := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [size_pow, size_X]; ring
  omega

/-- Size bound for a monomial circuit purely in terms of its degree:
each variable in the support contributes at least 1 to the degree. -/
theorem size_monomial_le [One k] (m : σ →₀ ℕ) (c : k) :
    (monomial m c).size ≤ 4 * (∑ i ∈ m.support, m i) + 3 := by
  rw [size_monomial]
  have hcard : m.support.card ≤ ∑ i ∈ m.support, m i := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  omega

/-! ### The degree–size bound -/

/-- The total degree of the computed polynomial never exceeds the
circuit size: leaves have degree ≤ 1, `add` takes a max, `mul` adds. -/
theorem totalDegree_eval_le [CommSemiring k] (f : Circuit σ k) :
    f.eval.totalDegree ≤ f.size := by
  induction f with
  | X i =>
      rw [eval_X, size_X]
      have h : (MvPolynomial.X i : MvPolynomial σ k).totalDegree
          ≤ (Finsupp.single i 1).sum fun _ => id :=
        MvPolynomial.totalDegree_monomial_le _ _
      simpa [Finsupp.sum_single_index] using h
  | C c => rw [eval_C, size_C]; simp
  | add f g ihf ihg =>
      rw [eval_add, size_add]
      exact (MvPolynomial.totalDegree_add _ _).trans (by omega)
  | mul f g ihf ihg =>
      rw [eval_mul, size_mul]
      exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

/-! ### Determinant circuits (Leibniz expansion) -/

section Det

variable [CommRing k]

/-- Determinant circuit for an `m × m` matrix of circuits, by Leibniz
expansion: sum over all permutations of (a sign constant) × (the product
of the selected entries). `CommRing k` makes the sign `±1` a constant of
`k`. Size is exponential in `m` (`m!` terms) — this is an EXPRESSION
TREE, adequate for the fixed-`r` upper bounds this campaign needs. -/
noncomputable def det {m : ℕ} (M : Matrix (Fin m) (Fin m) (Circuit σ k)) :
    Circuit σ k :=
  finsetSum Finset.univ fun τ : Equiv.Perm (Fin m) =>
    mul (C (((Equiv.Perm.sign τ : ℤ) : k)))
      (finsetProd Finset.univ fun i => M (τ i) i)

/-- The determinant circuit computes the determinant of the entrywise
evaluation (`Matrix.det_apply'`, the Leibniz formula). -/
theorem eval_det {m : ℕ} (M : Matrix (Fin m) (Fin m) (Circuit σ k)) :
    (det M).eval = (M.map eval).det := by
  rw [Matrix.det_apply']
  calc (det M).eval
      = ∑ τ : Equiv.Perm (Fin m),
          ((C (((Equiv.Perm.sign τ : ℤ) : k)) : Circuit σ k).mul
            (finsetProd Finset.univ fun i => M (τ i) i)).eval :=
        eval_finsetSum _ _
    _ = ∑ τ : Equiv.Perm (Fin m),
          (((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ k) *
            ∏ i, (M.map eval) (τ i) i) := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [eval_mul, eval_C, eval_finsetProd]
        simp [Matrix.map_apply]

/-- Size bound for the determinant circuit when every entry has size
≤ `s`: at most `m!·(m·s + m + 4) + 1` gates. -/
theorem size_det_le {m s : ℕ} (M : Matrix (Fin m) (Fin m) (Circuit σ k))
    (hM : ∀ i j, (M i j).size ≤ s) :
    (det M).size ≤ m.factorial * (m * s + m + 4) + 1 := by
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin m))).card = m.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hterm : ∀ τ : Equiv.Perm (Fin m),
      ((C (((Equiv.Perm.sign τ : ℤ) : k)) : Circuit σ k).mul
        (finsetProd Finset.univ fun i => M (τ i) i)).size ≤ m * s + m + 3 := by
    intro τ
    rw [size_mul, size_C, size_finsetProd, Finset.card_univ, Fintype.card_fin]
    have hsum : (∑ i : Fin m, (M (τ i) i).size) ≤ m * s := by
      calc (∑ i : Fin m, (M (τ i) i).size)
          ≤ ∑ _i : Fin m, s := Finset.sum_le_sum fun i _ => hM _ _
        _ = m * s := by
            rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
    omega
  have hsum : (∑ τ : Equiv.Perm (Fin m),
      ((C (((Equiv.Perm.sign τ : ℤ) : k)) : Circuit σ k).mul
        (finsetProd Finset.univ fun i => M (τ i) i)).size)
      ≤ m.factorial * (m * s + m + 3) := by
    calc (∑ τ : Equiv.Perm (Fin m),
        ((C (((Equiv.Perm.sign τ : ℤ) : k)) : Circuit σ k).mul
          (finsetProd Finset.univ fun i => M (τ i) i)).size)
        ≤ ∑ _τ : Equiv.Perm (Fin m), (m * s + m + 3) :=
          Finset.sum_le_sum fun τ _ => hterm τ
      _ = m.factorial * (m * s + m + 3) := by
          rw [Finset.sum_const, smul_eq_mul, hcard]
  have hfac : m.factorial * (m * s + m + 4)
      = m.factorial * (m * s + m + 3) + m.factorial := by ring
  calc (det M).size
      = (∑ τ : Equiv.Perm (Fin m),
          ((C (((Equiv.Perm.sign τ : ℤ) : k)) : Circuit σ k).mul
            (finsetProd Finset.univ fun i => M (τ i) i)).size)
        + (Finset.univ : Finset (Equiv.Perm (Fin m))).card + 1 :=
        size_finsetSum _ _
    _ ≤ m.factorial * (m * s + m + 4) + 1 := by omega

end Det

end Circuit

/-! ### The honest size predicates -/

section Honest

variable {σ k : Type*} [CommSemiring k]

/-- `ComputedInSize s p` : the polynomial `p` is computed by some
arithmetic circuit (expression tree) with at most `s` gates. This is the
real, non-vacuous object a "VP" definition must be built from: it is
meaningful for a FIXED size bound, whereas `∃ s, ComputedInSize s p` is
trivially true (`exists_computedInSize`). Formula size upper-bounds
DAG-circuit size, so this is a conservative (honest) upper-bound claim. -/
def ComputedInSize (s : ℕ) (p : MvPolynomial σ k) : Prop :=
  ∃ Cir : Circuit σ k, Cir.eval = p ∧ Cir.size ≤ s

/-- Monotonicity of `ComputedInSize` in the size bound. -/
theorem ComputedInSize.mono {s s' : ℕ} {p : MvPolynomial σ k}
    (h : ComputedInSize s p) (hss' : s ≤ s') : ComputedInSize s' p :=
  let ⟨Cir, he, hs⟩ := h
  ⟨Cir, he, hs.trans hss'⟩

/-- The zero polynomial is computed by the single constant gate `C 0`. -/
theorem computedInSize_zero : ComputedInSize 1 (0 : MvPolynomial σ k) :=
  ⟨Circuit.C 0, by simp, le_rfl⟩

/-- **Completeness** of the circuit model: every multivariate polynomial
(finite support by construction) is computed by some circuit, of size at
most `#supp(p) · (4·totalDegree(p) + 4) + 1` — one monomial circuit of
size ≤ 4·totalDegree(p) + 3 per monomial (`size_monomial_le`, using
#supp(m) ≤ deg(m)), plus one `add` gate per monomial, plus the nil
constant. The model is not vacuous. -/
theorem exists_circuit (p : MvPolynomial σ k) :
    ∃ Cir : Circuit σ k, Cir.eval = p ∧
      Cir.size ≤ p.support.card * (4 * p.totalDegree + 4) + 1 := by
  refine ⟨Circuit.finsetSum p.support fun m => Circuit.monomial m (p.coeff m),
    ?_, ?_⟩
  · rw [Circuit.eval_finsetSum]
    simp only [Circuit.eval_monomial]
    exact MvPolynomial.support_sum_monomial_coeff p
  · have hterm : ∀ m ∈ p.support,
        (Circuit.monomial m (p.coeff m)).size ≤ 4 * p.totalDegree + 3 := by
      intro m hm
      refine (Circuit.size_monomial_le m (p.coeff m)).trans ?_
      have hdeg : (∑ i ∈ m.support, m i) ≤ p.totalDegree := by
        simpa [Finsupp.sum] using MvPolynomial.le_totalDegree hm
      omega
    calc (Circuit.finsetSum p.support fun m => Circuit.monomial m (p.coeff m)).size
        = (∑ m ∈ p.support, (Circuit.monomial m (p.coeff m)).size)
          + p.support.card + 1 := Circuit.size_finsetSum _ _
      _ ≤ (∑ _m ∈ p.support, (4 * p.totalDegree + 3)) + p.support.card + 1 := by
          have := Finset.sum_le_sum hterm
          omega
      _ = p.support.card * (4 * p.totalDegree + 3) + p.support.card + 1 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = p.support.card * (4 * p.totalDegree + 4) + 1 := by ring

/-- **Vacuity of single-polynomial "poly-size"**: with the size bound
existentially quantified and no growth parameter, EVERY polynomial is
"computed in some size". This is the formal witness that `Vp2.IsVP` at
a single fixed `n` cannot be defined non-vacuously as "∃ a circuit of
size ≤ poly(n³)" — the honest definition must range over a family
(`VPFamily`) or pin an explicit bound (`ComputedInSize`). -/
theorem exists_computedInSize (p : MvPolynomial σ k) :
    ∃ s, ComputedInSize s p :=
  let ⟨Cir, he, _⟩ := exists_circuit p
  ⟨Cir.size, Cir, he, le_rfl⟩

end Honest

/-- `VPFamily D` : the family `D`, giving for each side `n` a polynomial
in the `n³` tensor-entry variables, is computable by circuits of size
polynomial in `n³ = #(EntryIndex n)`: for some `c`, the `n`-th member is
computed in size `(n³ + c)^c`. The form `(N + c)^c` is cofinal among
polynomial bounds in `N`, so this is the standard honest "poly(N)-size
family" — the object the natural-proofs barrier actually quantifies
over (FSV Defn 2.1, GKSS). Built on formula size, so membership claims
are conservative: `VPFamily` here is a VF-style witness, and VF ⊆ VP. -/
def VPFamily {k : Type*} [CommSemiring k]
    (D : (n : ℕ) → MvPolynomial (EntryIndex n) k) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, ComputedInSize ((n ^ 3 + c) ^ c) (D n)

/-! ### Explicit circuits for the generic flattening minors

The bridge to Pf1's border-rank infrastructure (Vp2/BorderRank.lean):
the `(r+1)×(r+1)` minors of the generic flattening — the distinguisher
polynomials of `Vp2.exists_flattening_distinguisher` — are computed by
explicit determinant circuits whose size depends only on `r`, not on
`n`. This is the honest fragment of the `isVP` leg of
`Vp2.exists_flattening_vpDistinguisher`. -/

section Flattening

variable {k : Type*} [CommRing k]

/-- Every `m × m` minor of the generic flattening is computed by an
explicit Leibniz circuit of size ≤ `m!·(2m + 4) + 1`: the entry matrix
consists of single variables (size-1 leaves). -/
theorem computedInSize_det_genericFlattening_submatrix {n m : ℕ}
    (ri : Fin m → Fin n) (ci : Fin m → Fin n × Fin n) :
    ComputedInSize (m.factorial * (2 * m + 4) + 1)
      ((genericFlattening k n).submatrix ri ci).det := by
  refine ⟨Circuit.det
    (Matrix.of fun s t => Circuit.X (ri s, (ci t).1, (ci t).2)), ?_, ?_⟩
  · rw [Circuit.eval_det]
    -- the two matrices agree entrywise by unfolding `map`/`of`/`submatrix`
    congr 1
  · calc (Circuit.det
        (Matrix.of fun s t => Circuit.X (ri s, (ci t).1, (ci t).2))).size
        ≤ m.factorial * (m * 1 + m + 4) + 1 :=
          Circuit.size_det_le _ fun i j => by simp
      _ = m.factorial * (2 * m + 4) + 1 := by ring

/-- The concrete `(r+1)×(r+1)` generic-flattening minor used as the
distinguisher witness in `Vp2.exists_flattening_distinguisher` (row pick
`Fin.castLE h`, column pick the diagonal pairs) is computed by an
explicit circuit of size ≤ `(r+1)!·(2(r+1)+4) + 1` — an explicit bound
DEPENDING ONLY ON `r`, not on the side `n`. -/
theorem computedInSize_flatteningMinor {n r : ℕ} (h : r + 1 ≤ n) :
    ComputedInSize ((r + 1).factorial * (2 * (r + 1) + 4) + 1)
      (((genericFlattening k n).submatrix (Fin.castLE h)
        fun t => (Fin.castLE h t, Fin.castLE h t)).det) :=
  computedInSize_det_genericFlattening_submatrix _ _

/-- The flattening-minor distinguisher family at a FIXED target rank
`r`: for each side `n`, the `(r+1)×(r+1)` diagonal minor of the generic
flattening when it fits (`r + 1 ≤ n`), and `0` otherwise. -/
noncomputable def flatteningMinorFamily (k : Type*) [CommRing k] (r n : ℕ) :
    MvPolynomial (EntryIndex n) k :=
  if h : r + 1 ≤ n then
    ((genericFlattening k n).submatrix (Fin.castLE h)
      fun t => (Fin.castLE h t, Fin.castLE h t)).det
  else 0

theorem flatteningMinorFamily_of_le {r n : ℕ} (h : r + 1 ≤ n) :
    flatteningMinorFamily k r n
      = ((genericFlattening k n).submatrix (Fin.castLE h)
          fun t => (Fin.castLE h t, Fin.castLE h t)).det :=
  dif_pos h

theorem flatteningMinorFamily_of_lt {r n : ℕ} (h : n < r + 1) :
    flatteningMinorFamily k r n = 0 :=
  dif_neg (by omega)

/-- **The flattening minors form a VP family** (fixed `r`): the circuit
size bound `(r+1)!·(2(r+1)+4) + 1` is CONSTANT in `n`, hence certainly
`≤ (n³ + c)^c` with `c` that very constant. This is the honest
family-level content of the `isVP` leg of
`Vp2.exists_flattening_vpDistinguisher` — the determinantal
distinguishers really are "VP-natural" in the sense the barrier
quantifies over. -/
theorem vpFamily_flatteningMinorFamily (k : Type*) [CommRing k] (r : ℕ) :
    VPFamily (flatteningMinorFamily k r) := by
  refine ⟨(r + 1).factorial * (2 * (r + 1) + 4) + 1, fun n => ?_⟩
  have h1 : 1 ≤ (r + 1).factorial * (2 * (r + 1) + 4) + 1 :=
    Nat.le_add_left 1 _
  have hle : (r + 1).factorial * (2 * (r + 1) + 4) + 1
      ≤ (n ^ 3 + ((r + 1).factorial * (2 * (r + 1) + 4) + 1))
        ^ ((r + 1).factorial * (2 * (r + 1) + 4) + 1) :=
    (Nat.le_add_left _ _).trans
      (le_self_pow (le_trans h1 (Nat.le_add_left _ _)) (by omega))
  by_cases hn : r + 1 ≤ n
  · rw [flatteningMinorFamily_of_le hn]
    exact (computedInSize_flatteningMinor hn).mono hle
  · rw [flatteningMinorFamily_of_lt (by omega)]
    exact computedInSize_zero.mono (h1.trans hle)

end Flattening

end Vp2
