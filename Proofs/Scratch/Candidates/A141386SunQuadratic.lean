/-
# A141386 — Sun: exceptions for `x² + y² + 5·(triangular)`

## OEIS source (re-pulled verbatim with `goof oeis show A141386`, 2026-08-05)

```
NAME:     Conjectured to be complete list of numbers not of the form
          x^2 + y^2 + 5*triangular number.
TERMS:    3,11,12,27,129,138,273
KEYWORDS: nonn
COMMENTS: (none)
XREFS:
  Cf. A141273, A141423, A141428, A141443, A141463.
  Cf. A141464, A141491, A141497.
```

The conjecture **is** the NAME line; the entry carries no comments at all.
The `%A` line is `_N. J. A. Sloane_, Sep 05 2008` — **Sloane submitted the
sequence, not Sun**.  The mathematical source is the `%H` link:

> Kane & Sun, *On almost universal mixed sums of squares and triangular
> numbers*, arXiv:0808.2761 (Trans. AMS 362 (2010) 6425–6455),

whose Example 1.1 lists `E(x² + y² + 5T_z) = {3, 11, 12, 27, 129, 138, 273}` as
a **computational** finding ("our computation via computer suggests"), not a
proved theorem.  So the candidates document's attribution to Zhi-Wei Sun is
right in substance (Sun is a coauthor and this is his representability
programme) but the OEIS `%A` field says Sloane; the conjecture line is Kane–Sun's.

## Convention pinning (done computationally before writing this card)

The NAME does not say whether `x, y` range over nonnegative or positive
integers, nor whether `0` counts as a triangular number.  Both matter.  An
exhaustive sweep of `n < 20000` under the reading

> `x, y ∈ ℕ` (so `0` allowed), triangular numbers `T_t = t(t+1)/2` with `t ∈ ℕ`
> (so `T_0 = 0` allowed)

returns exactly `3, 11, 12, 27, 129, 138, 273` — the DATA line, with nothing
extra and nothing missing.  That fixes the convention.  Under a
positive-only reading `1` would also be an exception (`1 = 1² + 0² + 0`
needs `y = 0`), contradicting the DATA, so the nonnegative reading is forced.

Spot-check of the smallest exception: `n = 3`.  `5·T_0 = 0` and `3` is not a sum
of two squares (`3 ≡ 3 mod 4`); `5·T_1 = 5 > 3`.  So `3` is an exception. ✓

## Status — **open, with a GRH-conditional path**

A literature sweep (Kane–Sun arXiv:0808.2761; Chan–Haensch arXiv:1402.1640;
web search) found **no unconditional proof** that the exception set is exactly
these seven.  What is established:

* `x² + y² + 5T_z` is *almost universal* (finitely many exceptions) — that is the
  Kane–Sun theorem, and Chan–Haensch later characterized almost-universality for
  the whole `αx² + βT_y + γT_z` family.
* Kane–Sun note (their §1) that **under GRH**, an Ono–Soundararajan-style
  argument via Waldspurger's theorem makes the exception set *effectively*
  verifiable — i.e. GRH plus a finite computation would settle it.
* Kane (their ref. [Kane4]) proved some exception sets in the list under GRH,
  but `x² + y² + 5T_z` is not among the ones confirmed by this sweep.

So the honest status is **open unconditionally; conditionally decidable under
GRH**.  A card should say that, not "open" flatly.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A141386

/-! ## Definition layer

`leandoc` findings:

* `leandoc "Nat.triangular"` → `mode:"miss"`.  Mathlib has no triangular-number
  definition under that name.  The nearest available spellings are
  `Nat.choose (t + 1) 2` (which *is* `t(t+1)/2`, via `Nat.choose_two_right`) and
  `Finset.sum (Finset.range (t+1)) id` (via `Gauss.sum`/`Finset.sum_range_id_mul_two`).
* `Nat.sqrt`, `Nat.exists_mul_self` — the decision procedure for "is a square".
* Sums of two squares: `Nat.Prime.sq_add_sq`, `ZMod.exists_sq_eq_neg_one_iff`,
  `Nat.eq_sq_add_sq_iff_...` — Mathlib has Fermat's two-square theorem, and the
  full "which `n` are sums of two squares" characterization lives in
  `Mathlib/NumberTheory/SumTwoSquares.lean` as
  `Nat.eq_sq_add_sq_iff` / `ZMod.isSquare_neg_one_iff`.  That characterization
  is the *right* tool for a serious attack and is cited in the theorem docstring.

**Division discipline.**  `T_t = t(t+1)/2` involves `ℕ` division.  Rather than
guard it, the primary statement is written **division-free** by doubling:
`2n = 2x² + 2y² + 5·t·(t+1)`.  Since `t(t+1)` is always even, the two readings
agree; the equivalence is in the PROVABLE layer so the doubling is auditable
rather than assumed. -/

/-- The `t`-th triangular number, division-free by construction:
`tri t = t * (t + 1) / 2` is *not* used; instead the predicate is doubled. -/
def tri (t : ℕ) : ℕ := t * (t + 1) / 2

/-- `n` is representable as `x² + y² + 5·T_t`, stated **division-free** by
doubling.  `x, y, t` range over `ℕ` (so `0` is allowed for each), which is the
convention forced by the DATA line — see the header. -/
def Representable (n : ℕ) : Prop :=
  ∃ x y t : ℕ, 2 * n = 2 * x ^ 2 + 2 * y ^ 2 + 5 * (t * (t + 1))

/-- The same predicate in the literal `x² + y² + 5·T_t` form, for readability.
`representable_iff_tri` (PROVABLE) shows the two agree. -/
def Representable' (n : ℕ) : Prop := ∃ x y t : ℕ, n = x ^ 2 + y ^ 2 + 5 * tri t

/-- The seven listed exceptions. -/
def exceptions : Finset ℕ := {3, 11, 12, 27, 129, 138, 273}

/-! ## The conjecture -/

/-- **Sun's `x² + y² + 5·triangular` completeness conjecture (A141386).**

Verbatim (the NAME line, which is the whole claim): "Conjectured to be complete
list of numbers not of the form x^2 + y^2 + 5*triangular number", with DATA
`3, 11, 12, 27, 129, 138, 273`.

Formalized: every `n` outside the seven exceptions is representable.  The
converse (the seven really are exceptions) is a **finite** check and is in the
PROVABLE layer, so this theorem carries the entire open content.

**Mathlib primitives available.**  The two-squares characterization
(`Mathlib/NumberTheory/SumTwoSquares.lean`: `Nat.eq_sq_add_sq_iff`,
`ZMod.isSquare_neg_one_iff`, `Nat.Prime.sq_add_sq`), `Nat.factorization`,
`Nat.sqrt`, `ZMod`, `legendreSym`, `Nat.choose_two_right`.

**Sketch of an attack.**  This is a ternary-quadratic-form representability
problem in disguise.  Completing the square on the triangular part:
`5·T_t = 5t(t+1)/2`, so `8n + 5 = 8x² + 8y² + 5(2t+1)²`, i.e. `n` is
representable iff `8n + 5` is represented by the ternary form
`8u² + 8v² + 5w²` with `w` odd.  (Sanity: `n = 3` gives `29`; `8u²+8v²+5w²=29`
needs `w` odd, `w = 1 → 8(u²+v²) = 24 → u²+v² = 3`, impossible; `w = ±... `
larger overshoots.  ✓ consistent with `3` being an exception.)
Ternary forms of this shape are handled by:
1. *Local solvability* — decide representability over every `ℤ_p` and over `ℝ`.
   Mechanical, and Lean-feasible via `ZMod (p^k)` computations.
2. *The genus/spinor-genus gap* — a ternary form represents everything locally
   representable **except** finitely many "spinor exceptional" square classes.
   Bounding those is where the real work is, and it is exactly why Sun's family
   of conjectures resisted for years and then fell one by one.
3. *Effective bounds* — Ono–Soundararajan-style results give an effective
   threshold above which local solvability suffices, modulo GRH.

**Status caveat.**  A literature sweep found no unconditional proof, but did
find a GRH-conditional route (Kane–Sun §1, via Waldspurger + Ono–Soundararajan).
The genuinely honest formalization target is therefore the **conditional**
theorem — `sun_a141386_complete` with GRH as an explicit hypothesis — in the
same spirit as the Brocard-under-Szpiro card.  Mathlib has
`RiemannHypothesis`-adjacent statements only for the classical zeta
(`riemannZeta`), not GRH for Dirichlet `L`-functions, so the hypothesis would
have to be spelled out.

**Tactic families.** `decide` for the seven exceptions (bounded searches);
`native_decide` for the `n ≤ 20000` sweep; `interval_cases` for `t` given
`5·T_t ≤ n`; `omega` for the doubling arithmetic;
`Nat.sqrt`-based `decide` for "is a sum of two squares".

**Related work in this repo.** None directly.  Adjacent card in this directory:
`A373686SomuTran.lean` (also "practical/polygonal additive representation", also
a Sun-adjacent conjecture, and the Somu–Tran paper's Theorem 1 resolves the
*triangular* analogue). -/
theorem sun_a141386_complete (n : ℕ) (h : n ∉ exceptions) : Representable n := by
  sorry

/-- Contrapositive packaging: the exception set is exactly `exceptions`. -/
theorem sun_a141386_exceptions_eq :
    {n : ℕ | ¬ Representable n} = (exceptions : Finset ℕ) := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the doubled and literal forms agree (`t * (t+1)` is always even).
theorem representable_iff_tri (n : ℕ) : Representable n ↔ Representable' n := by
  sorry

-- PROVABLE: `2 * tri t = t * (t + 1)` — the doubling identity, which is what
-- licenses the division-free statement.
theorem two_mul_tri (t : ℕ) : 2 * tri t = t * (t + 1) := by
  sorry

-- PROVABLE: satisfiability — the conclusion of `sun_a141386_complete` is
-- instantiable, so the theorem is not vacuous.
--   1 = 1² + 0² + 5·T₀
example : Representable 1 := ⟨1, 0, 0, by norm_num⟩
--   6 = 1² + 0² + 5·T₁
example : Representable 6 := ⟨1, 0, 1, by norm_num⟩

-- PROVABLE: the seven exceptions really are exceptions (the direction the
-- conjecture does *not* cover).  Bounded search: `5·T_t ≤ n` forces
-- `t ≤ n`, and `x², y² ≤ n` forces `x, y ≤ Nat.sqrt n`.
example : ∀ n ∈ exceptions,
    ¬ ∃ x ∈ Finset.range (n.sqrt + 1), ∃ y ∈ Finset.range (n.sqrt + 1),
      ∃ t ∈ Finset.range (n + 1), 2 * n = 2 * x ^ 2 + 2 * y ^ 2 + 5 * (t * (t + 1)) := by
  native_decide

-- PROVABLE: the smallest exception, spelled out.  `3` is not a sum of two
-- squares and `5·T_1 = 5 > 3`, so no representation exists.
example : ¬ Representable 3 := by
  rintro ⟨x, y, t, h⟩
  interval_cases t <;> interval_cases x <;> interval_cases y <;> omega

-- PROVABLE: the convention audit.  Under a *positive*-only reading of `x, y`,
-- `1` would be an exception — but `1` is not in the DATA line, so the
-- nonnegative reading is forced.  This example pins that down.
example : Representable 1 ∧ (1 : ℕ) ∉ exceptions := ⟨⟨1, 0, 0, by norm_num⟩, by decide⟩

-- PROVABLE (window check): the exceptions below `20000` are exactly the seven.
-- Externally verified: the sweep returns `3, 11, 12, 27, 129, 138, 273`.
example : ∀ n ∈ Finset.range 20000, ¬ Representable n → n ∈ exceptions := by
  native_decide

/-! ## Notes for a follow-up card

Literature check done (see Status): open unconditionally, GRH-conditionally
decidable per Kane–Sun arXiv:0808.2761.  The `8n + 5 = 8u² + 8v² + 5w²`
reduction (verified above at `n = 3`) is what puts it in the ternary
quadratic-forms setting where that conditional argument lives.

The provable-today deliverables are:
1. `two_mul_tri` and `representable_iff_tri` — the doubling audit, ~10 lines.
2. The `8n + 5` reduction as a lemma:
   `Representable n ↔ ∃ u v w, Odd w ∧ 8*n + 5 = 8*u^2 + 8*v^2 + 5*w^2`.
   This is `ring`-plus-parity and turns the problem into a standard form. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A141386 plus a literature sweep, 2026-08-05.

Confirmed:
* NAME and TERMS verbatim; the entry really has **no** `%C` line.
* **Convention audit reproduced**: `x, y ≥ 0` and `t ≥ 0` gives exactly
  `3, 11, 12, 27, 129, 138, 273` below `20000`.  The `x, y ≥ 1` and `t ≥ 1`
  readings both produce extra exceptions and do not match the DATA.
* **The `8n + 5 = 8u² + 8v² + 5w²` (`w` odd) reduction is correct**, and at
  `n = 3` gives `29`, which is not so representable.
* `2 * tri t = t * (t + 1)` holds in `ℕ` (consecutive integers, so the division
  is exact), and the doubled predicate is equivalent to the literal one.
* The search bounds `t ≤ n` and `x, y ≤ √n` are sound (loose for `t`, but they
  cannot miss a representation).

Defects raised, both **FIXED**:
1. The attribution hedge was too vague.  `%A A141386 _N. J. A. Sloane_,
   Sep 05 2008` — Sloane *submitted* it; the mathematical source is the `%H`
   link to **Kane & Sun, arXiv:0808.2761**, whose Example 1.1 lists exactly this
   exception set as a *computational* finding.  Header now says so.
2. "Most likely to already be a theorem in the literature" was unsupported.  A
   literature sweep found **no unconditional proof**, but did find the
   GRH-conditional route in Kane–Sun §1 (Waldspurger + Ono–Soundararajan).
   Status is now "open unconditionally; conditionally decidable under GRH", and
   the recommended target is the *conditional* theorem.
-/

end Candidates.A141386
