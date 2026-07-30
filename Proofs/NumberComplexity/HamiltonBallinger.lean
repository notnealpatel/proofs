/-
  NumberComplexity/HamiltonBallinger — the Hamilton–Ballinger finiteness
  conjecture (OEIS A005245 comment, Gordon Hamilton and Brad Ballinger,
  2022-05-23): the integer (Mahler–Popken) complexity A005245 is lower
  than the `{1, +, ^}`-complexity A348262 for only finitely many `n`.

    · `PowExpr`, `PowExpr.eval`, `PowExpr.cost`
        — the term language over {1, +, ^} (OEIS A348262), its value,
          and its number of 1-leaves; mirrors `Expr` of IntComplexity
          with `^` in place of `×`.
    · `powComplexity n`
        — A348262(n) as the subtype-indexed infimum
          `⨅ e : {e : PowExpr // e.eval = n}, e.1.cost`, with the same
          junk value `powComplexity 0 = 0` (empty index subtype) as
          `complexity 0` — pinned by `powComplexity_zero`.
    · order API — `powComplexity_le_cost`, `exists_cost_eq_powComplexity`,
      `le_powComplexity`, `one_le_powComplexity`, `powComplexity_le_self`,
      subadditivity `powComplexity_add_le` / `powComplexity_pow_le`.
    · `powScan`, `powSplit`, `powComplexityFuel`, `powComplexityRec`
        — a computable engine for the A348262 recurrence (min over
          additive splits `a + (n − a)`, `1 ≤ a ≤ n/2`, and perfect-power
          splits `x ^ y = n`, `2 ≤ x, y ≤ n/2`) by structural recursion
          on fuel, so concrete values close by kernel `decide`; the scan
          bounds `x, y ≤ n/2` are proved sufficient inside
          `powComplexityRec_pow_le`. No `native_decide` anywhere.
    · `powComplexity_eq_powComplexityRec`
        — master bridge; concrete values of A348262 become decidable.
          Ground checks against live OEIS A348262 data (`oeis show
          A348262`, pulled 2026-07-30): a(1..16) = 1, 2, 3, 4, 5, 6, 7,
          5, 5, 6, 7, 8, 9, 10, 11, 6.
    · `exists_complexity_lt_powComplexity` (witness `n = 6`: 5 < 6) and
      `exists_powComplexity_lt_complexity` (witness `n = 8`: 5 < 6)
        — PROVED: neither complexity measure dominates the other, so
          the conjecture below is nontrivial in both directions.
    · `hamiltonBallinger_finiteness`
        — the conjecture `{n | complexity n < powComplexity n}.Finite`,
          OPEN, carried as the file's single intended `sorry`; the OEIS
          entry offers only empirical evidence (within the pulled terms
          `n ≤ 78` the set has 31 elements, the largest being 78) and
          no route is known (card: requires comparative growth theory
          of the two measures).

  Card: Formalize/A005245-hamilton-ballinger.md. Builds on the committed
  layer NumberComplexity/IntComplexity (`complexity`, `complexityRec`,
  `complexity_eq_complexityRec`).

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib
import NumberComplexity.IntComplexity

set_option autoImplicit false

namespace NumberComplexity

/-! ## 1. Expressions over 1, +, ^ -/

/-- A well-formed arithmetic expression over the constant `1`, addition,
and exponentiation — the term language of the `{1, +, ^}`-complexity,
OEIS A348262. Juxtaposition of `1`s is not a constructor, exactly as in
`Expr` (IntComplexity). -/
inductive PowExpr : Type
  | one : PowExpr
  | add : PowExpr → PowExpr → PowExpr
  | pow : PowExpr → PowExpr → PowExpr
  deriving DecidableEq, Repr

namespace PowExpr

/-- The value of an expression: `one` evaluates to `1`, `add` to the sum,
and `pow a b` to `a.eval ^ b.eval`. -/
def eval : PowExpr → ℕ
  | one => 1
  | add a b => eval a + eval b
  | pow a b => eval a ^ eval b

/-- The cost of an expression: the number of `one`-leaves it contains. -/
def cost : PowExpr → ℕ
  | one => 1
  | add a b => cost a + cost b
  | pow a b => cost a + cost b

-- ground checks: (1+1) ^ (1+1+1) evaluates to 8 and spends five 1's —
-- the OEIS A348262 value a(8) = 5
example : (pow (add one one) (add one (add one one))).eval = 8 := rfl
example : (pow (add one one) (add one (add one one))).cost = 5 := rfl
example : one.eval = 1 := rfl
example : one.cost = 1 := rfl

/-- Every expression evaluates to a positive number; in particular `0`
is not expressible from `1` with `+` and `^`. -/
theorem one_le_eval (e : PowExpr) : 1 ≤ e.eval := by
  induction e with
  | one => exact le_refl 1
  | add a b iha ihb => simp only [eval]; omega
  | pow a b iha ihb =>
      simp only [eval]
      exact Nat.one_le_pow b.eval a.eval (by omega)

/-- Every expression costs at least one `1`. -/
theorem one_le_cost (e : PowExpr) : 1 ≤ e.cost := by
  induction e with
  | one => exact le_refl 1
  | add a b iha ihb => simp only [cost]; omega
  | pow a b iha ihb => simp only [cost]; omega

/-- `ones n` : the right-combed sum `1 + (1 + (⋯ + 1))` of `n + 1` ones —
the trivial witness that every positive number is expressible. -/
def ones : ℕ → PowExpr
  | 0 => one
  | n + 1 => add one (ones n)

/-- `ones n` evaluates to `n + 1`. -/
theorem eval_ones (n : ℕ) : (ones n).eval = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ones, eval, ih]; omega

/-- `ones n` costs `n + 1` ones. -/
theorem cost_ones (n : ℕ) : (ones n).cost = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ones, cost, ih]; omega

-- ground checks: five ones sum to 5 at cost 5
example : (ones 4).eval = 5 := rfl
example : (ones 4).cost = 5 := rfl

end PowExpr

/-! ## 2. The {1, +, ^}-complexity norm -/

/-- The `{1, +, ^}`-complexity of `n` (OEIS A348262): the least number of
`1`'s in a `{1, +, ^}`-expression evaluating to `n` — the infimum of
`PowExpr.cost` over the subtype of witnesses `{e // e.eval = n}`.

JUNK VALUE: for `n = 0` the index subtype is empty (`PowExpr.one_le_eval`),
the range is `∅`, and `Nat.sInf ∅ = 0`, so `powComplexity 0 = 0`
(`powComplexity_zero`) — the same convention as `complexity 0`. Statements
carry the guard `1 ≤ n` wherever the value at `0` would be load-bearing. -/
noncomputable def powComplexity (n : ℕ) : ℕ :=
  ⨅ e : {e : PowExpr // e.eval = n}, e.1.cost

/-- `powComplexity` unfolded to `Nat.sInf` of the set of achievable costs. -/
theorem powComplexity_def (n : ℕ) :
    powComplexity n =
      sInf (Set.range fun e : {e : PowExpr // e.eval = n} => e.1.cost) := rfl

/-- JUNK-VALUE PIN: `0` is not expressible, the witness subtype is empty,
and `Nat.sInf ∅ = 0`; so `powComplexity 0 = 0` by convention, not content. -/
theorem powComplexity_zero : powComplexity 0 = 0 := by
  haveI : IsEmpty {e : PowExpr // e.eval = 0} :=
    ⟨fun e => by have h1 := e.1.one_le_eval; have h2 := e.2; omega⟩
  rw [powComplexity_def, Set.range_eq_empty, Nat.sInf_empty]

/-- Any expression evaluating to `n` bounds the `{1, +, ^}`-complexity of
`n` by its cost. -/
theorem powComplexity_le_cost {n : ℕ} {e : PowExpr} (he : e.eval = n) :
    powComplexity n ≤ e.cost := by
  rw [powComplexity_def]
  exact Nat.sInf_le ⟨⟨e, he⟩, rfl⟩

/-- For `1 ≤ n` the infimum defining `powComplexity n` is attained: some
expression evaluates to `n` at cost exactly `powComplexity n`. -/
theorem exists_cost_eq_powComplexity {n : ℕ} (hn : 1 ≤ n) :
    ∃ e : PowExpr, e.eval = n ∧ e.cost = powComplexity n := by
  have hne :
      (Set.range
        fun e : {e : PowExpr // e.eval = n} => e.1.cost).Nonempty := by
    refine ⟨(PowExpr.ones (n - 1)).cost, ⟨PowExpr.ones (n - 1), ?_⟩, rfl⟩
    rw [PowExpr.eval_ones]
    omega
  obtain ⟨⟨e, he⟩, hc⟩ := Nat.sInf_mem hne
  refine ⟨e, he, ?_⟩
  rw [powComplexity_def]
  exact hc

/-- Lower bounds for the norm from lower bounds on every witness
(`1 ≤ n` keeps the statement off the empty-subtype junk case). -/
theorem le_powComplexity {n k : ℕ} (hn : 1 ≤ n)
    (h : ∀ e : PowExpr, e.eval = n → k ≤ e.cost) : k ≤ powComplexity n := by
  obtain ⟨e, he, hc⟩ := exists_cost_eq_powComplexity hn
  rw [← hc]
  exact h e he

/-- Positive numbers have positive `{1, +, ^}`-complexity. -/
theorem one_le_powComplexity {n : ℕ} (hn : 1 ≤ n) : 1 ≤ powComplexity n := by
  obtain ⟨e, _, hc⟩ := exists_cost_eq_powComplexity hn
  rw [← hc]
  exact e.one_le_cost

/-- The crude witness bound: `n` ones always suffice, so
`powComplexity n ≤ n` for `1 ≤ n`. -/
theorem powComplexity_le_self {n : ℕ} (hn : 1 ≤ n) : powComplexity n ≤ n := by
  have he : (PowExpr.ones (n - 1)).eval = n := by
    rw [PowExpr.eval_ones]
    omega
  have hc := powComplexity_le_cost he
  rw [PowExpr.cost_ones] at hc
  omega

/-- `powComplexity 1 = 1`: the single leaf `one` is optimal. -/
theorem powComplexity_one : powComplexity 1 = 1 :=
  le_antisymm (powComplexity_le_self (le_refl 1))
    (one_le_powComplexity (le_refl 1))

/-- Subadditivity under addition: gluing optimal witnesses with
`PowExpr.add` gives `powComplexity (a + b) ≤ powComplexity a +
powComplexity b` for `1 ≤ a`, `1 ≤ b`. -/
theorem powComplexity_add_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    powComplexity (a + b) ≤ powComplexity a + powComplexity b := by
  obtain ⟨e₁, he₁, hc₁⟩ := exists_cost_eq_powComplexity ha
  obtain ⟨e₂, he₂, hc₂⟩ := exists_cost_eq_powComplexity hb
  have he : (PowExpr.add e₁ e₂).eval = a + b := by
    simp only [PowExpr.eval, he₁, he₂]
  have hc := powComplexity_le_cost he
  simp only [PowExpr.cost, hc₁, hc₂] at hc
  exact hc

/-- Subadditivity under exponentiation: gluing optimal witnesses with
`PowExpr.pow` gives `powComplexity (a ^ b) ≤ powComplexity a +
powComplexity b` for `1 ≤ a`, `1 ≤ b`. -/
theorem powComplexity_pow_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    powComplexity (a ^ b) ≤ powComplexity a + powComplexity b := by
  obtain ⟨e₁, he₁, hc₁⟩ := exists_cost_eq_powComplexity ha
  obtain ⟨e₂, he₂, hc₂⟩ := exists_cost_eq_powComplexity hb
  have he : (PowExpr.pow e₁ e₂).eval = a ^ b := by
    simp only [PowExpr.eval, he₁, he₂]
  have hc := powComplexity_le_cost he
  simp only [PowExpr.cost, hc₁, hc₂] at hc
  exact hc

/-! ## 3. The computable recurrence engine

The A348262 recurrence (verified against all 78 live-pulled entry terms,
sage, 2026-07-30): for `2 ≤ n`,

  a(n) = min( min_{1 ≤ i ≤ n/2} a(i) + a(n−i),
              min_{x ^ y = n, 2 ≤ x, 2 ≤ y} a(x) + a(y) ).

Perfect-power splits `x ^ y = n` with `2 ≤ x, y` satisfy `x ≤ n / 2` and
`y ≤ n / 2` (since `2 * x ≤ x ^ 2 ≤ n` and `2 * y ≤ 2 ^ y ≤ n`), so a
scan over `x, y ≤ n / 2` sees them all — proved where it is needed, in
`powComplexityRec_pow_le`. `powScan` scans exponents for one base;
`powSplit` runs the additive scan and the base scan; `powComplexityFuel`
recurses on a fuel parameter (structural, NOT well-founded, recursion —
kernel-reducible, `decide`-friendly); `powComplexityRec n` supplies fuel
`n`, sufficient by `powComplexityFuel_eq_powComplexityRec`. -/

/-- `powScan g n x j` : the minimum of the trivial candidate `n` and the
power candidates `g x + g y` over exponents `2 ≤ y ≤ j` with `x ^ y = n`.
Intended use: `j = n / 2` with `g` a cost oracle for values below `n`. -/
def powScan (g : ℕ → ℕ) (n x : ℕ) : ℕ → ℕ
  | 0 => n
  | j + 1 =>
      min (if 2 ≤ j + 1 ∧ x ^ (j + 1) = n then g x + g (j + 1) else n)
        (powScan g n x j)

-- ground check with the identity oracle: 2 ^ 3 = 8 gives candidate
-- 2 + 3 = 5 by exponent scan up to j = 4
example : powScan id 8 2 4 = 5 := by decide
example : powScan id 8 2 0 = 8 := rfl

/-- The exponent scan never beats the trivial candidate `n`. -/
theorem powScan_le_self (g : ℕ → ℕ) (n x j : ℕ) : powScan g n x j ≤ n := by
  induction j with
  | zero => exact le_refl n
  | succ j ih =>
      simp only [powScan]
      exact le_trans (min_le_right _ _) ih

/-- The exponent scan is at most any power candidate it scans:
`powScan g n x j ≤ g x + g y` for `2 ≤ y ≤ j` with `x ^ y = n`. -/
theorem powScan_le (g : ℕ → ℕ) {n x y : ℕ} (hy : 2 ≤ y) (hxy : x ^ y = n) :
    ∀ {j : ℕ}, y ≤ j → powScan g n x j ≤ g x + g y := by
  intro j
  induction j with
  | zero => intro hyj; omega
  | succ j ih =>
      intro hyj
      simp only [powScan]
      rcases Nat.lt_or_ge y (j + 1) with hlt | hge
      · exact le_trans (min_le_right _ _) (ih (by omega))
      · have hye : y = j + 1 := by omega
        subst hye
        rw [if_pos ⟨hy, hxy⟩]
        exact min_le_left _ _

/-- The exponent scan is attained: it is the trivial candidate `n` or a
power candidate `g x + g y` with `2 ≤ y ≤ j` and `x ^ y = n`. -/
theorem powScan_cases (g : ℕ → ℕ) (n x j : ℕ) :
    powScan g n x j = n ∨
      ∃ y, 2 ≤ y ∧ y ≤ j ∧ x ^ y = n ∧ powScan g n x j = g x + g y := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
      simp only [powScan]
      rcases min_choice
          (if 2 ≤ j + 1 ∧ x ^ (j + 1) = n then g x + g (j + 1) else n)
          (powScan g n x j) with h | h
      · rw [h]
        by_cases hg : 2 ≤ j + 1 ∧ x ^ (j + 1) = n
        · rw [if_pos hg]
          exact Or.inr ⟨j + 1, hg.1, le_refl (j + 1), hg.2, rfl⟩
        · rw [if_neg hg]
          exact Or.inl rfl
      · rw [h]
        rcases ih with h1 | ⟨y, hy2, hyj, hxy, he⟩
        · exact Or.inl h1
        · exact Or.inr ⟨y, hy2, by omega, hxy, he⟩

/-- The exponent scan only queries its oracle at `x` and at exponents
`≤ j`, so oracles agreeing below `n` give equal scans when `x, j < n`. -/
theorem powScan_congr {g₁ g₂ : ℕ → ℕ} {n x : ℕ}
    (h : ∀ m, m < n → g₁ m = g₂ m) (hx : x < n) :
    ∀ {j : ℕ}, j < n → powScan g₁ n x j = powScan g₂ n x j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have h3 :
          (if 2 ≤ j + 1 ∧ x ^ (j + 1) = n then g₁ x + g₁ (j + 1) else n)
            = (if 2 ≤ j + 1 ∧ x ^ (j + 1) = n then g₂ x + g₂ (j + 1)
              else n) := by
        by_cases hg : 2 ≤ j + 1 ∧ x ^ (j + 1) = n
        · rw [if_pos hg, if_pos hg, h x hx, h (j + 1) hj]
        · rw [if_neg hg, if_neg hg]
      simp only [powScan]
      rw [h3, ih (by omega)]

/-- `powSplit g n k` : the minimum of the trivial candidate `n`, the
additive candidates `g a + g (n - a)` for `1 ≤ a ≤ k`, and the power
candidates `g x + g y` for bases `2 ≤ x ≤ k` and exponents
`2 ≤ y ≤ n / 2` with `x ^ y = n`. Intended use: `k = n / 2` with `g` a
cost oracle for values below `n`. -/
def powSplit (g : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 =>
      min
        (min (g (k + 1) + g (n - (k + 1)))
          (if 2 ≤ k + 1 then powScan g n (k + 1) (n / 2) else n))
        (powSplit g n k)

-- ground check with the identity oracle: for n = 8, k = 4 the best
-- additive candidate is a + (8 - a) = 8 and the power split 2 ^ 3 gives
-- 2 + 3 = 5
example : powSplit id 8 4 = 5 := by decide
example : powSplit id 8 0 = 8 := rfl

/-- The search never beats the trivial all-ones candidate bound `n`. -/
theorem powSplit_le_self (g : ℕ → ℕ) (n k : ℕ) : powSplit g n k ≤ n := by
  induction k with
  | zero => exact le_refl n
  | succ k ih =>
      simp only [powSplit]
      exact le_trans (min_le_right _ _) ih

/-- The search value is at most any additive candidate it scans:
`powSplit g n k ≤ g a + g (n - a)` for `1 ≤ a ≤ k`. -/
theorem powSplit_le_add (g : ℕ → ℕ) {n a : ℕ} (ha : 1 ≤ a) :
    ∀ {k : ℕ}, a ≤ k → powSplit g n k ≤ g a + g (n - a) := by
  intro k
  induction k with
  | zero => intro hak; omega
  | succ k ih =>
      intro hak
      simp only [powSplit]
      rcases Nat.lt_or_ge a (k + 1) with hlt | hge
      · exact le_trans (min_le_right _ _) (ih (by omega))
      · have hae : a = k + 1 := by omega
        subst hae
        exact le_trans (min_le_left _ _) (min_le_left _ _)

/-- The search value is at most any power candidate it scans:
`powSplit g n k ≤ g x + g y` for `2 ≤ x ≤ k`, `2 ≤ y ≤ n / 2`, and
`x ^ y = n`. -/
theorem powSplit_le_pow (g : ℕ → ℕ) {n x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hyn : y ≤ n / 2) (hxy : x ^ y = n) :
    ∀ {k : ℕ}, x ≤ k → powSplit g n k ≤ g x + g y := by
  intro k
  induction k with
  | zero => intro hxk; omega
  | succ k ih =>
      intro hxk
      simp only [powSplit]
      rcases Nat.lt_or_ge x (k + 1) with hlt | hge
      · exact le_trans (min_le_right _ _) (ih (by omega))
      · have hxe : x = k + 1 := by omega
        subst hxe
        rw [if_pos hx]
        exact le_trans (min_le_left _ _)
          (le_trans (min_le_right _ _) (powScan_le g hy hxy hyn))

/-- The search value is attained: it is the trivial candidate `n`, an
additive candidate, or a power candidate. This is the destructor used to
realize `powComplexityRec n` by an actual expression. -/
theorem powSplit_cases (g : ℕ → ℕ) (n k : ℕ) :
    powSplit g n k = n ∨
      (∃ a, 1 ≤ a ∧ a ≤ k ∧ powSplit g n k = g a + g (n - a)) ∨
      (∃ x y, 2 ≤ x ∧ x ≤ k ∧ 2 ≤ y ∧ y ≤ n / 2 ∧ x ^ y = n ∧
        powSplit g n k = g x + g y) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
      simp only [powSplit]
      rcases min_choice
          (min (g (k + 1) + g (n - (k + 1)))
            (if 2 ≤ k + 1 then powScan g n (k + 1) (n / 2) else n))
          (powSplit g n k) with h | h
      · rw [h]
        rcases min_choice (g (k + 1) + g (n - (k + 1)))
            (if 2 ≤ k + 1 then powScan g n (k + 1) (n / 2) else n)
            with h2 | h2
        · rw [h2]
          exact Or.inr (Or.inl ⟨k + 1, by omega, le_refl (k + 1), rfl⟩)
        · rw [h2]
          by_cases hg : 2 ≤ k + 1
          · rw [if_pos hg]
            rcases powScan_cases g n (k + 1) (n / 2) with
              hs | ⟨y, hy2, hyj, hxy, he⟩
            · exact Or.inl hs
            · exact Or.inr (Or.inr
                ⟨k + 1, y, hg, le_refl (k + 1), hy2, hyj, hxy, he⟩)
          · rw [if_neg hg]
            exact Or.inl rfl
      · rw [h]
        rcases ih with h1 | ⟨a, ha1, hak, he⟩ | ⟨x, y, hx2, hxk, hy2, hyn, hxy, he⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl ⟨a, ha1, by omega, he⟩)
        · exact Or.inr (Or.inr ⟨x, y, hx2, by omega, hy2, hyn, hxy, he⟩)

/-- The search only queries its oracle at arguments below `n` (all of
`a`, `n - a`, bases `≤ k`, and exponents `≤ n / 2` are `< n` when
`k < n`), so oracles agreeing below `n` give equal searches. -/
theorem powSplit_congr {g₁ g₂ : ℕ → ℕ} {n : ℕ}
    (h : ∀ m, m < n → g₁ m = g₂ m) :
    ∀ {k : ℕ}, k < n → powSplit g₁ n k = powSplit g₂ n k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have h1 : g₁ (k + 1) = g₂ (k + 1) := h (k + 1) hk
      have h2 : g₁ (n - (k + 1)) = g₂ (n - (k + 1)) := h (n - (k + 1)) (by omega)
      have h3 :
          (if 2 ≤ k + 1 then powScan g₁ n (k + 1) (n / 2) else n)
            = (if 2 ≤ k + 1 then powScan g₂ n (k + 1) (n / 2) else n) := by
        by_cases hg : 2 ≤ k + 1
        · rw [if_pos hg, if_pos hg,
            powScan_congr h hk (Nat.div_lt_self (by omega) (by omega))]
        · rw [if_neg hg, if_neg hg]
      simp only [powSplit]
      rw [h3, h1, h2, ih (by omega)]

/-- Fueled `{1, +, ^}`-complexity recursion: `powComplexityFuel fuel n`
runs the A348262 search with recursion depth `fuel`. Values: `0` at
`n = 0` (junk, matching `powComplexity_zero`), `1` at `n = 1`, and one
`powSplit` pass with oracle `powComplexityFuel (fuel - 1)` at `2 ≤ n`.
Exhausted fuel returns the junk value `0`;
`powComplexityFuel_eq_powComplexityRec` shows any fuel with `n ≤ fuel`
computes the true value. Structural recursion on `fuel` keeps ground
instances kernel-decidable. -/
def powComplexityFuel : ℕ → ℕ → ℕ
  | 0 => fun n => if n = 1 then 1 else 0
  | fuel + 1 => fun n =>
      match n with
      | 0 => 0
      | 1 => 1
      | m + 2 => powSplit (powComplexityFuel fuel) (m + 2) ((m + 2) / 2)

/-- `powComplexityFuel` at `n = 0` is `0` for every fuel. -/
theorem powComplexityFuel_zero (f : ℕ) : powComplexityFuel f 0 = 0 := by
  cases f <;> rfl

/-- `powComplexityFuel` at `n = 1` is `1` for every fuel. -/
theorem powComplexityFuel_one (f : ℕ) : powComplexityFuel f 1 = 1 := by
  cases f <;> rfl

/-- Unfolding lemma for `powComplexityFuel` at `2 ≤ n`, positive fuel. -/
theorem powComplexityFuel_succ (f m : ℕ) :
    powComplexityFuel (f + 1) (m + 2)
      = powSplit (powComplexityFuel f) (m + 2) ((m + 2) / 2) := rfl

/-- Computable `{1, +, ^}`-complexity: the fueled recursion with fuel `n`
(sufficient by `powComplexityFuel_eq_powComplexityRec`). Agrees with the
norm `powComplexity` by the master theorem
`powComplexity_eq_powComplexityRec`; concrete values close by kernel
`decide`. -/
def powComplexityRec (n : ℕ) : ℕ := powComplexityFuel n n

/-- `powComplexityRec 0 = 0` — the same junk value as
`powComplexity_zero`. -/
theorem powComplexityRec_zero : powComplexityRec 0 = 0 := rfl

/-- `powComplexityRec 1 = 1`. -/
theorem powComplexityRec_one : powComplexityRec 1 = 1 := rfl

-- ground checks for the fueled engine (OEIS A348262: a(8) = 5)
example : powComplexityFuel 8 8 = 5 := by decide
example : powComplexityFuel 0 5 = 0 := rfl   -- exhausted fuel: junk value
example : powComplexityFuel 1 1 = 1 := rfl
example : powComplexityRec 0 = 0 := rfl      -- junk value at 0

/-- Fuel invariance: any fuel of at least `n` computes
`powComplexityRec n`. Strong induction on the fuel through
`powSplit_congr`, whose oracle calls all land strictly below `n`. -/
theorem powComplexityFuel_eq_powComplexityRec (f : ℕ) :
    ∀ n, n ≤ f → powComplexityFuel f n = powComplexityRec n := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro n hnf
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · rw [powComplexityFuel_zero, powComplexityRec_zero]
      · rw [powComplexityFuel_one, powComplexityRec_one]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      obtain ⟨fp, rfl⟩ : ∃ fp, f = fp + 1 := ⟨f - 1, by omega⟩
      rw [powComplexityFuel_succ]
      have hR : powComplexityRec (m + 2)
          = powSplit (powComplexityFuel (m + 1)) (m + 2) ((m + 2) / 2) := rfl
      rw [hR]
      refine powSplit_congr (fun v hv => ?_) (by omega)
      rw [ih fp (by omega) v (by omega), ih (m + 1) (by omega) v (by omega)]

/-- THE RECURRENCE (OEIS A348262): for `2 ≤ n`, `powComplexityRec n` is
the minimum of `n`, of `powComplexityRec a + powComplexityRec (n - a)`
over `1 ≤ a ≤ n/2`, and of `powComplexityRec x + powComplexityRec y`
over power splits `x ^ y = n` with `2 ≤ x ≤ n/2`, `2 ≤ y ≤ n/2`. -/
theorem powComplexityRec_eq_powSplit {n : ℕ} (hn : 2 ≤ n) :
    powComplexityRec n = powSplit powComplexityRec n (n / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  calc powComplexityRec (m + 2)
      = powSplit (powComplexityFuel (m + 1)) (m + 2) ((m + 2) / 2) := rfl
    _ = powSplit powComplexityRec (m + 2) ((m + 2) / 2) :=
        powSplit_congr
          (fun v hv =>
            powComplexityFuel_eq_powComplexityRec (m + 1) v (by omega))
          (by omega)

/-- `powComplexityRec n ≤ n`: the search never beats the all-ones
bound. -/
theorem powComplexityRec_le_self (n : ℕ) : powComplexityRec n ≤ n := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · exact le_refl 0
    · exact le_refl 1
  · rw [powComplexityRec_eq_powSplit h2]
    exact powSplit_le_self powComplexityRec n (n / 2)

/-- Subadditivity of the recursion under addition (`1 ≤ a`, `1 ≤ b`):
the split at `min a b ≤ (a+b)/2` is among the scanned candidates. -/
theorem powComplexityRec_add_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    powComplexityRec (a + b) ≤ powComplexityRec a + powComplexityRec b := by
  rw [powComplexityRec_eq_powSplit (by omega)]
  rcases le_total a b with hab | hab
  · have h := powSplit_le_add powComplexityRec (n := a + b) ha
      (k := (a + b) / 2) (by omega)
    have hs : a + b - a = b := by omega
    rw [hs] at h
    exact h
  · have h := powSplit_le_add powComplexityRec (n := a + b) hb
      (k := (a + b) / 2) (by omega)
    have hs : a + b - b = a := by omega
    rw [hs] at h
    omega

/-- `2 * b ≤ 2 ^ b` for `2 ≤ b` — pins the exponent of a perfect-power
split inside the scan range `y ≤ n / 2` of `powSplit`. -/
theorem two_mul_le_two_pow {b : ℕ} (hb : 2 ≤ b) : 2 * b ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => omega
  | succ b hb ih =>
      have h2 : 2 ≤ 2 ^ b :=
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
      calc 2 * (b + 1) = 2 * b + 2 := by ring
        _ ≤ 2 ^ b + 2 ^ b := by omega
        _ = 2 ^ (b + 1) := by ring

/-- Subadditivity of the recursion under exponentiation (`1 ≤ a`,
`1 ≤ b`): base or exponent `1` is absorbed, and otherwise the power
split at `a ≤ a^b/2`, `b ≤ a^b/2` is among the scanned candidates —
this is where the scan bounds of `powSplit` are proved sufficient. -/
theorem powComplexityRec_pow_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    powComplexityRec (a ^ b) ≤ powComplexityRec a + powComplexityRec b := by
  rcases Nat.eq_or_lt_of_le ha with h1a | h2a
  · rw [← h1a, one_pow, powComplexityRec_one]
    omega
  rcases Nat.eq_or_lt_of_le hb with h1b | h2b
  · rw [← h1b, pow_one]
    omega
  have hn4 : 4 ≤ a ^ b :=
    calc 4 = 2 ^ 2 := rfl
      _ ≤ a ^ 2 := Nat.pow_le_pow_left h2a 2
      _ ≤ a ^ b := Nat.pow_le_pow_right (by omega) h2b
  have hxk : a ≤ a ^ b / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc a * 2 ≤ a * a := Nat.mul_le_mul (le_refl a) h2a
      _ = a ^ 2 := by ring
      _ ≤ a ^ b := Nat.pow_le_pow_right (by omega) h2b
  have hyk : b ≤ a ^ b / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc b * 2 = 2 * b := by ring
      _ ≤ 2 ^ b := two_mul_le_two_pow h2b
      _ ≤ a ^ b := Nat.pow_le_pow_left h2a b
  rw [powComplexityRec_eq_powSplit (by omega)]
  exact powSplit_le_pow powComplexityRec (by omega) (by omega) hyk rfl hxk

/-- Realization: for `1 ≤ n` some expression evaluates to `n` with cost
at most `powComplexityRec n` (strong induction along `powSplit_cases`;
power splits satisfy `x, y ≤ n / 2 < n`, so the induction descends). -/
theorem exists_cost_le_powComplexityRec :
    ∀ n : ℕ, 1 ≤ n →
      ∃ e : PowExpr, e.eval = n ∧ e.cost ≤ powComplexityRec n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have h1 : n = 1 := by omega
      subst h1
      exact ⟨PowExpr.one, rfl, le_refl 1⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rcases powSplit_cases powComplexityRec (m + 2) ((m + 2) / 2) with
        hb | ⟨a, ha1, hak, he⟩ | ⟨x, y, hx2, hxk, hy2, hyn, hxy, he⟩
      · refine ⟨PowExpr.ones (m + 1), ?_, ?_⟩
        · rw [PowExpr.eval_ones]
        · rw [PowExpr.cost_ones, powComplexityRec_eq_powSplit (by omega), hb]
      · obtain ⟨e₁, he₁, hc₁⟩ := ih a (by omega) (by omega)
        obtain ⟨e₂, he₂, hc₂⟩ := ih (m + 2 - a) (by omega) (by omega)
        refine ⟨PowExpr.add e₁ e₂, ?_, ?_⟩
        · simp only [PowExpr.eval, he₁, he₂]
          omega
        · simp only [PowExpr.cost]
          rw [powComplexityRec_eq_powSplit (by omega), he]
          exact Nat.add_le_add hc₁ hc₂
      · obtain ⟨e₁, he₁, hc₁⟩ := ih x (by omega) (by omega)
        obtain ⟨e₂, he₂, hc₂⟩ := ih y (by omega) (by omega)
        refine ⟨PowExpr.pow e₁ e₂, ?_, ?_⟩
        · simp only [PowExpr.eval, he₁, he₂]
          exact hxy
        · simp only [PowExpr.cost]
          rw [powComplexityRec_eq_powSplit (by omega), he]
          exact Nat.add_le_add hc₁ hc₂

/-- Optimality: the recursion lower-bounds the cost of every expression
(structural induction through the subadditivity lemmas). -/
theorem powComplexityRec_le_cost (e : PowExpr) :
    powComplexityRec e.eval ≤ e.cost := by
  induction e with
  | one => exact le_refl 1
  | add a b iha ihb =>
      simp only [PowExpr.eval, PowExpr.cost]
      calc powComplexityRec (a.eval + b.eval)
          ≤ powComplexityRec a.eval + powComplexityRec b.eval :=
            powComplexityRec_add_le a.one_le_eval b.one_le_eval
        _ ≤ a.cost + b.cost := Nat.add_le_add iha ihb
  | pow a b iha ihb =>
      simp only [PowExpr.eval, PowExpr.cost]
      calc powComplexityRec (a.eval ^ b.eval)
          ≤ powComplexityRec a.eval + powComplexityRec b.eval :=
            powComplexityRec_pow_le a.one_le_eval b.one_le_eval
        _ ≤ a.cost + b.cost := Nat.add_le_add iha ihb

/-! ## 4. The master theorem and OEIS ground checks -/

/-- MASTER THEOREM: the `{1, +, ^}`-norm agrees with the computable
recursion everywhere (at `0` both take the junk value `0`). Concrete
values of `powComplexity` are decidable through this bridge by kernel
`decide`. -/
theorem powComplexity_eq_powComplexityRec (n : ℕ) :
    powComplexity n = powComplexityRec n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [powComplexity_zero, powComplexityRec_zero]
  · apply le_antisymm
    · obtain ⟨e, he, hc⟩ := exists_cost_le_powComplexityRec n hn
      exact le_trans (powComplexity_le_cost he) hc
    · obtain ⟨e, he, hc⟩ := exists_cost_eq_powComplexity hn
      calc powComplexityRec n = powComplexityRec e.eval := by rw [he]
        _ ≤ e.cost := powComplexityRec_le_cost e
        _ = powComplexity n := hc

-- GROUND TRUTH (`oeis show A348262`, pulled live 2026-07-30):
-- a(1..16) = 1, 2, 3, 4, 5, 6, 7, 5, 5, 6, 7, 8, 9, 10, 11, 6. All
-- closed by kernel `decide`; no `native_decide` in this file.
-- `maxRecDepth`: cold evaluation of the fueled engine exceeds the
-- elaborator's default recursion depth (the kernel re-checks either way).
set_option maxRecDepth 16384 in
example :
    (List.range 16).map (fun i => powComplexityRec (i + 1))
      = [1, 2, 3, 4, 5, 6, 7, 5, 5, 6, 7, 8, 9, 10, 11, 6] := by decide

example : powComplexity 0 = 0 := powComplexity_zero  -- junk pin, not A348262
example : powComplexity 1 = 1 := powComplexity_one
example : powComplexity 8 = 5 := by
  rw [powComplexity_eq_powComplexityRec]; decide
-- a(16) = 6: the tower 2^(2^2) (or 4^2) at cost 2 + 4; compare
-- A005245(16) = 8 — exponentiation beats repeated multiplication here
set_option maxRecDepth 16384 in
example : powComplexity 16 = 6 := by
  rw [powComplexity_eq_powComplexityRec]; decide
set_option maxRecDepth 16384 in
example : complexity 16 = 8 := by
  rw [complexity_eq_complexityRec]; decide

/-! ## 5. The Hamilton–Ballinger conjecture (OEIS A005245 comment)

"It appears that this sequence is lower than A348262 {1,+,^} only a
finite number of times." — Gordon Hamilton and Brad Ballinger,
2022-05-23 (pulled live from `oeis show A005245`, 2026-07-30).

Within the kernel-checked range `n ≤ 16` the comparison set is
`{6, 7, 12, 13, 14, 15}` (checked below); against the full pulled entry data
(78 terms of each sequence, sage, 2026-07-30) it is

  {6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 24, 40, 42, 44, 45, 46, 47,
   48, 54, 55, 56, 57, 58, 60, 61, 62, 63, 75, 76, 77, 78},

31 elements with the largest at the very edge of the data — empirical
evidence only. The conjecture is OPEN; no route is known (card:
requires comparative growth theory of the two measures). -/

/-- Neither measure dominates, direction 1 — PROVED: at `n = 6` the
`{1, +, ×}`-complexity is strictly smaller (`5 = A005245(6) <
A348262(6) = 6`), so the conjecture's set is nonempty. -/
theorem exists_complexity_lt_powComplexity :
    ∃ n : ℕ, complexity n < powComplexity n := by
  refine ⟨6, ?_⟩
  rw [complexity_eq_complexityRec, powComplexity_eq_powComplexityRec]
  decide

/-- Neither measure dominates, direction 2 — PROVED: at `n = 8` the
`{1, +, ^}`-complexity is strictly smaller (`5 = A348262(8) <
A005245(8) = 6`, via `8 = (1+1)^(1+1+1)`), so the conjectured
finiteness is not an instance of one-sided domination. -/
theorem exists_powComplexity_lt_complexity :
    ∃ n : ℕ, powComplexity n < complexity n := by
  refine ⟨8, ?_⟩
  rw [complexity_eq_complexityRec, powComplexity_eq_powComplexityRec]
  decide

/-- **Hamilton–Ballinger finiteness conjecture** (OEIS A005245 comment,
Gordon Hamilton and Brad Ballinger, 2022-05-23) — OPEN: the integer
(Mahler–Popken) complexity A005245 is strictly below the
`{1, +, ^}`-complexity A348262 for only finitely many `n`. The set is
nonempty (`6` is a member, `exists_complexity_lt_powComplexity`), and
membership fails at `8` (`exists_powComplexity_lt_complexity`), so the
statement is nontrivial in both directions. `n = 0` contributes nothing:
both norms take the junk value `0` there and `0 < 0` is false. -/
theorem hamiltonBallinger_finiteness :
    {n : ℕ | complexity n < powComplexity n}.Finite := by
  -- intended sorry: open conjecture (card A005245-hamilton-ballinger,
  -- ROUTE: none known — requires comparative growth theory of the two
  -- complexity measures; the OEIS entry offers only empirical evidence).
  sorry

-- ground-truth/satisfiability layer for the sorried statement: the set is
-- inhabited and avoided at concrete points, both PROVED by kernel `decide`,
-- so the conjectured finiteness is not the degenerate finiteness of `∅`
example : 6 ∈ {n : ℕ | complexity n < powComplexity n} := by
  simp only [Set.mem_ofPred_eq, complexity_eq_complexityRec,
    powComplexity_eq_powComplexityRec]
  decide
example : 8 ∉ {n : ℕ | complexity n < powComplexity n} := by
  simp only [Set.mem_ofPred_eq, complexity_eq_complexityRec,
    powComplexity_eq_powComplexityRec]
  decide

-- the comparison set within the kernel-checked range `n ≤ 16` is exactly
-- `{6, 7, 12, 13, 14, 15}` (as indices `i = n - 1`: `{5, 6, 11, 12, 13,
-- 14}`), matching the sage sweep of the pulled entry terms
set_option maxRecDepth 16384 in
example :
    ((List.range 16).filter fun i =>
        decide (complexityRec (i + 1) < powComplexityRec (i + 1)))
      = [5, 6, 11, 12, 13, 14] := by decide

/-! ### Guy's question — bounded sanity computations only

Guy asked whether `A005245(p) = A005245(p-1) + 1` for every prime `p`
(A005245 entry). REFUTED: Martin Fuller (2008) found the least
counterexample `p = 353942783` (entry comment, Charles R Greathouse IV,
2012-10-04) — far beyond kernel range for the memoization-free fueled
engine, so the refutation is not formalized here. The instances below
are bounded sanity computations for the definitions at small primes,
NOT steps toward the refuted general claim (card LEAN NOTE). -/

example : complexity 2 = complexity 1 + 1 := by
  simp only [complexity_eq_complexityRec]; decide
example : complexity 3 = complexity 2 + 1 := by
  simp only [complexity_eq_complexityRec]; decide
example : complexity 5 = complexity 4 + 1 := by
  simp only [complexity_eq_complexityRec]; decide
example : complexity 7 = complexity 6 + 1 := by
  simp only [complexity_eq_complexityRec]; decide
set_option maxRecDepth 16384 in
example : complexity 11 = complexity 10 + 1 := by
  simp only [complexity_eq_complexityRec]; decide
set_option maxRecDepth 16384 in
example : complexity 13 = complexity 12 + 1 := by
  simp only [complexity_eq_complexityRec]; decide

/-! ### Satisfiability of the guarded statements

Every hypothesis-bearing theorem above is instantiated jointly at a
concrete model, so none of them is vacuous. -/

example : powComplexity (2 + 3) ≤ powComplexity 2 + powComplexity 3 :=
  powComplexity_add_le (by omega) (by omega)
example : powComplexity (2 ^ 3) = powComplexity 2 + powComplexity 3 := by
  simp only [powComplexity_eq_powComplexityRec]; decide
example : powComplexity (2 ^ 3) ≤ powComplexity 2 + powComplexity 3 :=
  powComplexity_pow_le (by omega) (by omega)
example : powComplexity 4 ≤ 4 := powComplexity_le_self (by omega)
example : 1 ≤ powComplexity 4 := one_le_powComplexity (by omega)
example : ∃ e : PowExpr, e.eval = 8 ∧ e.cost = powComplexity 8 :=
  exists_cost_eq_powComplexity (by omega)
example : ∃ e : PowExpr, e.eval = 8 ∧ e.cost ≤ powComplexityRec 8 :=
  exists_cost_le_powComplexityRec 8 (by omega)
example : powComplexity 2 ≤ (PowExpr.add PowExpr.one PowExpr.one).cost :=
  powComplexity_le_cost rfl
example : 5 ≤ powComplexity 8 :=
  le_powComplexity (by omega) fun e he => by
    have h := powComplexityRec_le_cost e
    rw [he] at h
    calc 5 = powComplexityRec 8 := by decide
      _ ≤ e.cost := h
example : powComplexityRec 8 = powSplit powComplexityRec 8 4 :=
  powComplexityRec_eq_powSplit (by omega)
example : powScan powComplexityRec 8 2 4
    ≤ powComplexityRec 2 + powComplexityRec 3 :=
  powScan_le powComplexityRec (by omega) (by norm_num) (by omega)
example : powScan powComplexityRec 8 2 4 ≤ 8 :=
  powScan_le_self powComplexityRec 8 2 4
/-- Agrees with `powComplexityRec` strictly below `8`, wrong at and above it —
a genuinely different oracle, so the `congr` examples below transport real
content rather than witnessing `X = X` (STYLE.md's degenerate-witness trap). -/
private def perturbed (m : ℕ) : ℕ := if m < 8 then powComplexityRec m else 999

example : perturbed 8 ≠ powComplexityRec 8 := by decide
example : powScan perturbed 8 2 4 = powScan powComplexityRec 8 2 4 :=
  powScan_congr (fun m hm => by simp only [perturbed, if_pos hm]) (by omega) (by omega)
example : powSplit powComplexityRec 12 6
    ≤ powComplexityRec 5 + powComplexityRec 7 :=
  powSplit_le_add powComplexityRec (by omega) (by omega)
example : powSplit powComplexityRec 8 4
    ≤ powComplexityRec 2 + powComplexityRec 3 :=
  powSplit_le_pow powComplexityRec (by omega) (by omega) (by omega)
    (by norm_num) (by omega)
example : powSplit powComplexityRec 8 4 ≤ 8 :=
  powSplit_le_self powComplexityRec 8 4
example : powSplit perturbed 8 4 = powSplit powComplexityRec 8 4 :=
  powSplit_congr (fun m hm => by simp only [perturbed, if_pos hm]) (by omega)
example : powComplexityFuel 100 8 = powComplexityRec 8 :=
  powComplexityFuel_eq_powComplexityRec 100 8 (by omega)
example : powComplexityRec (2 + 3) ≤ powComplexityRec 2 + powComplexityRec 3 :=
  powComplexityRec_add_le (by omega) (by omega)
example : powComplexityRec (2 ^ 3) ≤ powComplexityRec 2 + powComplexityRec 3 :=
  powComplexityRec_pow_le (by omega) (by omega)
example : 2 * 2 ≤ 2 ^ 2 := two_mul_le_two_pow (le_refl 2)

/-! ## Axiom audit (sorry-free declarations only)

`hamiltonBallinger_finiteness` is excluded: it carries the file's single
intended `sorry` and reports `sorryAx` by construction. Everything below
must report a subset of `{propext, Classical.choice, Quot.sound}`. -/

#print axioms PowExpr
#print axioms PowExpr.eval
#print axioms PowExpr.cost
#print axioms PowExpr.ones
#print axioms powComplexity_def
#print axioms PowExpr.one_le_eval
#print axioms PowExpr.one_le_cost
#print axioms PowExpr.eval_ones
#print axioms PowExpr.cost_ones
#print axioms powComplexity
#print axioms powComplexity_zero
#print axioms powComplexity_le_cost
#print axioms exists_cost_eq_powComplexity
#print axioms le_powComplexity
#print axioms one_le_powComplexity
#print axioms powComplexity_le_self
#print axioms powComplexity_one
#print axioms powComplexity_add_le
#print axioms powComplexity_pow_le
#print axioms powScan
#print axioms powScan_le_self
#print axioms powScan_le
#print axioms powScan_cases
#print axioms powScan_congr
#print axioms powSplit
#print axioms powSplit_le_self
#print axioms powSplit_le_add
#print axioms powSplit_le_pow
#print axioms powSplit_cases
#print axioms powSplit_congr
#print axioms powComplexityFuel
#print axioms powComplexityFuel_zero
#print axioms powComplexityFuel_one
#print axioms powComplexityFuel_succ
#print axioms powComplexityRec
#print axioms powComplexityRec_zero
#print axioms powComplexityRec_one
#print axioms powComplexityFuel_eq_powComplexityRec
#print axioms powComplexityRec_eq_powSplit
#print axioms powComplexityRec_le_self
#print axioms powComplexityRec_add_le
#print axioms two_mul_le_two_pow
#print axioms powComplexityRec_pow_le
#print axioms exists_cost_le_powComplexityRec
#print axioms powComplexityRec_le_cost
#print axioms powComplexity_eq_powComplexityRec
#print axioms exists_complexity_lt_powComplexity
#print axioms exists_powComplexity_lt_complexity

end NumberComplexity
