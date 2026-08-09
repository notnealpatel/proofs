/-
  NumberComplexity/IntComplexity — integer (Mahler–Popken) complexity:
  the minimal number of 1's needed to build `n` from the constant `1`
  using only `+` and `×` (OEIS A005245). Definition layer of the
  NumberComplexity campaign; HamiltonBallinger and ComplexityPatterns
  build on this API.

    · `Expr`, `Expr.eval`, `Expr.cost`
        — the term language over {1, +, ×}, its value, and its number
          of 1-leaves. `Expr.one_le_eval`: every expression evaluates
          to a positive number, so 0 is not expressible.
    · `complexity n`
        — the norm (written ‖n‖ in the literature; no notation is
          introduced here — Mathlib's ‖·‖ belongs to normed spaces),
          as the subtype-indexed infimum
          `⨅ e : {e : Expr // e.eval = n}, e.1.cost`.
          `complexity 0 = 0` is a JUNK value: the index subtype is
          empty and `Nat.sInf ∅ = 0` (`complexity_zero` pins it).
    · order API — `complexity_le_cost`, `le_complexity`,
      `exists_cost_eq_complexity` (the infimum is attained for
      `1 ≤ n`), `one_le_complexity`, `complexity_le_self`, and
      subadditivity `complexity_add_le` / `complexity_mul_le`.
    · `minSplit`, `complexityFuel`, `complexityRec`
        — a computable companion implementing the standard recurrence
          (min over additive splits `a + (n − a)`, `1 ≤ a ≤ n/2`, and
          divisor splits `d · (n/d)`, `2 ≤ d ≤ n/2`; the OEIS A005245
          program) by structural recursion on a fuel parameter, so
          concrete values kernel-reduce and close by `decide`.
          No `native_decide` anywhere: the trusted base stays the
          kernel.
    · `complexity_eq_complexityRec`
        — the master bridge; every concrete value of the norm is then
          decidable. Ground checks against the live OEIS A005245 data
          (`oeis show A005245`, pulled 2026-07-29):
          a(1..12) = 1,2,3,4,5,5,6,6,6,7,8,7 — including the
          non-monotone pair a(11) = 8, a(12) = 7.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib

set_option autoImplicit false

namespace NumberComplexity

/-! ## 1. Expressions over 1, +, × -/

/-- A well-formed arithmetic expression over the constant `1`, addition,
and multiplication — the term language of integer (Mahler–Popken)
complexity, OEIS A005245. Juxtaposition of `1`s is not a constructor:
`11` is only expressible through `+` and `×`. -/
inductive Expr : Type
  | one : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving DecidableEq, Repr

namespace Expr

/-- The value of an expression: `one` evaluates to `1`, and `add`/`mul`
evaluate to the sum/product of the values of the two parts. -/
def eval : Expr → ℕ
  | one => 1
  | add a b => eval a + eval b
  | mul a b => eval a * eval b

/-- The cost of an expression: the number of `one`-leaves it contains. -/
def cost : Expr → ℕ
  | one => 1
  | add a b => cost a + cost b
  | mul a b => cost a + cost b

-- ground checks: (1+1) × (1+(1+1)) evaluates to 6 and spends five 1's
example : (mul (add one one) (add one (add one one))).eval = 6 := rfl
example : (mul (add one one) (add one (add one one))).cost = 5 := rfl
example : one.eval = 1 := rfl
example : one.cost = 1 := rfl

/-- Every expression evaluates to a positive number; in particular `0`
is not expressible from `1` with `+` and `×`. -/
theorem one_le_eval (e : Expr) : 1 ≤ e.eval := by
  induction e with
  | one => exact le_refl 1
  | add a b iha ihb => simp only [eval]; omega
  | mul a b iha ihb =>
      simp only [eval]
      calc 1 = 1 * 1 := rfl
        _ ≤ a.eval * b.eval := Nat.mul_le_mul iha ihb

/-- Every expression costs at least one `1`. -/
theorem one_le_cost (e : Expr) : 1 ≤ e.cost := by
  induction e with
  | one => exact le_refl 1
  | add a b iha ihb => simp only [cost]; omega
  | mul a b iha ihb => simp only [cost]; omega

/-- `ones n` : the right-combed sum `1 + (1 + (⋯ + 1))` of `n + 1` ones —
the trivial witness that every positive number is expressible. (Indexing
by `n + 1` keeps the definition total without a junk case.) -/
def ones : ℕ → Expr
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

end Expr

/-! ## 2. The complexity norm -/

/-- Integer (Mahler–Popken) complexity of `n` (OEIS A005245): the least
number of `1`'s in a `{1, +, ×}`-expression evaluating to `n` — the
infimum of `Expr.cost` over the subtype of witnesses `{e // e.eval = n}`.

JUNK VALUE: for `n = 0` the index subtype is empty (`Expr.one_le_eval`),
the range is `∅`, and `Nat.sInf ∅ = 0`, so `complexity 0 = 0`
(`complexity_zero`). Statements about `complexity` therefore carry the
guard `1 ≤ n` wherever the value at `0` would otherwise be load-bearing. -/
noncomputable def complexity (n : ℕ) : ℕ :=
  ⨅ e : {e : Expr // e.eval = n}, e.1.cost

/-- `complexity` unfolded to `Nat.sInf` of the set of achievable costs. -/
theorem complexity_def (n : ℕ) :
    complexity n =
      sInf (Set.range fun e : {e : Expr // e.eval = n} => e.1.cost) := rfl

/-- JUNK-VALUE PIN: `0` is not expressible, the witness subtype is empty,
and `Nat.sInf ∅ = 0`; so `complexity 0 = 0` by convention, not content. -/
theorem complexity_zero : complexity 0 = 0 := by
  haveI : IsEmpty {e : Expr // e.eval = 0} :=
    ⟨fun e => by have h1 := e.1.one_le_eval; have h2 := e.2; omega⟩
  rw [complexity_def, Set.range_eq_empty, Nat.sInf_empty]

/-- Any expression evaluating to `n` bounds the complexity of `n` by its
cost. -/
theorem complexity_le_cost {n : ℕ} {e : Expr} (he : e.eval = n) :
    complexity n ≤ e.cost := by
  rw [complexity_def]
  exact Nat.sInf_le ⟨⟨e, he⟩, rfl⟩

/-- For `1 ≤ n` the infimum defining `complexity n` is attained: some
expression evaluates to `n` at cost exactly `complexity n`. -/
theorem exists_cost_eq_complexity {n : ℕ} (hn : 1 ≤ n) :
    ∃ e : Expr, e.eval = n ∧ e.cost = complexity n := by
  have hne :
      (Set.range fun e : {e : Expr // e.eval = n} => e.1.cost).Nonempty := by
    refine ⟨(Expr.ones (n - 1)).cost, ⟨Expr.ones (n - 1), ?_⟩, rfl⟩
    rw [Expr.eval_ones]
    omega
  obtain ⟨⟨e, he⟩, hc⟩ := Nat.sInf_mem hne
  refine ⟨e, he, ?_⟩
  rw [complexity_def]
  exact hc

/-- Lower bounds for the norm from lower bounds on every witness
(`1 ≤ n` keeps the statement off the empty-subtype junk case). -/
theorem le_complexity {n k : ℕ} (hn : 1 ≤ n)
    (h : ∀ e : Expr, e.eval = n → k ≤ e.cost) : k ≤ complexity n := by
  obtain ⟨e, he, hc⟩ := exists_cost_eq_complexity hn
  rw [← hc]
  exact h e he

/-- Positive numbers have positive complexity. -/
theorem one_le_complexity {n : ℕ} (hn : 1 ≤ n) : 1 ≤ complexity n := by
  obtain ⟨e, _, hc⟩ := exists_cost_eq_complexity hn
  rw [← hc]
  exact e.one_le_cost

/-- The crude witness bound: `n` ones always suffice, so
`complexity n ≤ n` for `1 ≤ n`. -/
theorem complexity_le_self {n : ℕ} (hn : 1 ≤ n) : complexity n ≤ n := by
  have he : (Expr.ones (n - 1)).eval = n := by
    rw [Expr.eval_ones]
    omega
  have hc := complexity_le_cost he
  rw [Expr.cost_ones] at hc
  omega

/-- `complexity 1 = 1`: the single leaf `one` is optimal. -/
theorem complexity_one : complexity 1 = 1 :=
  le_antisymm (complexity_le_self (le_refl 1)) (one_le_complexity (le_refl 1))

/-- Subadditivity under addition: gluing optimal witnesses with `Expr.add`
gives `complexity (a + b) ≤ complexity a + complexity b` for `1 ≤ a`,
`1 ≤ b`. -/
theorem complexity_add_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    complexity (a + b) ≤ complexity a + complexity b := by
  obtain ⟨e₁, he₁, hc₁⟩ := exists_cost_eq_complexity ha
  obtain ⟨e₂, he₂, hc₂⟩ := exists_cost_eq_complexity hb
  have he : (Expr.add e₁ e₂).eval = a + b := by
    simp only [Expr.eval, he₁, he₂]
  have hc := complexity_le_cost he
  simp only [Expr.cost, hc₁, hc₂] at hc
  exact hc

/-- Subadditivity under multiplication: gluing optimal witnesses with
`Expr.mul` gives `complexity (a * b) ≤ complexity a + complexity b` for
`1 ≤ a`, `1 ≤ b`. -/
theorem complexity_mul_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    complexity (a * b) ≤ complexity a + complexity b := by
  obtain ⟨e₁, he₁, hc₁⟩ := exists_cost_eq_complexity ha
  obtain ⟨e₂, he₂, hc₂⟩ := exists_cost_eq_complexity hb
  have he : (Expr.mul e₁ e₂).eval = a * b := by
    simp only [Expr.eval, he₁, he₂]
  have hc := complexity_le_cost he
  simp only [Expr.cost, hc₁, hc₂] at hc
  exact hc

/-! ## 3. The computable recurrence engine

The OEIS A005245 recurrence: for `2 ≤ n`,

  a(n) = min( min_{1 ≤ i ≤ n/2} a(i) + a(n−i),
              min_{d ∣ n, 2 ≤ d ≤ n/2} a(d) + a(n/d) ).

`minSplit` is one search pass given a cost oracle for smaller values;
`complexityFuel` runs it by structural recursion on a fuel parameter
(structural, NOT well-founded, recursion — so the kernel can reduce
ground instances and `decide` closes concrete goals); `complexityRec n`
supplies fuel `n`, which `complexityFuel_eq_complexityRec` proves
sufficient. -/

/-- `minSplit g n k` : the minimum of the trivial candidate `n` (the
all-ones witness), the additive candidates `g a + g (n - a)` for
`1 ≤ a ≤ k`, and the multiplicative candidates `g d + g (n / d)` for
`2 ≤ d ≤ k` with `d ∣ n`. Intended use: `k = n / 2` with `g` a cost
oracle for values below `n`. -/
def minSplit (g : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 =>
      min
        (min (g (k + 1) + g (n - (k + 1)))
          (if 2 ≤ k + 1 ∧ (k + 1) ∣ n then g (k + 1) + g (n / (k + 1)) else n))
        (minSplit g n k)

-- ground check with the identity oracle: for n = 6, k = 3 the additive
-- candidates are all 6 and the divisor splits 2·3, 3·2 both cost 2+3 = 5
example : minSplit id 6 3 = 5 := by decide
example : minSplit id 6 0 = 6 := rfl

/-- The search never beats the trivial all-ones candidate bound `n` —
i.e. it always returns at most `n`. -/
theorem minSplit_le_self (g : ℕ → ℕ) (n k : ℕ) : minSplit g n k ≤ n := by
  induction k with
  | zero => exact le_refl n
  | succ k ih =>
      simp only [minSplit]
      exact le_trans (min_le_right _ _) ih

/-- The search value is at most any additive candidate it scans:
`minSplit g n k ≤ g a + g (n - a)` for `1 ≤ a ≤ k`. -/
theorem minSplit_le_add (g : ℕ → ℕ) {n a : ℕ} (ha : 1 ≤ a) :
    ∀ {k : ℕ}, a ≤ k → minSplit g n k ≤ g a + g (n - a) := by
  intro k
  induction k with
  | zero => intro hak; omega
  | succ k ih =>
      intro hak
      simp only [minSplit]
      rcases Nat.lt_or_ge a (k + 1) with hlt | hge
      · exact le_trans (min_le_right _ _) (ih (by omega))
      · have hae : a = k + 1 := by omega
        subst hae
        exact le_trans (min_le_left _ _) (min_le_left _ _)

/-- The search value is at most any multiplicative candidate it scans:
`minSplit g n k ≤ g d + g (n / d)` for a divisor `2 ≤ d ≤ k` of `n`. -/
theorem minSplit_le_mul (g : ℕ → ℕ) {n d : ℕ} (hd : 2 ≤ d) (hdvd : d ∣ n) :
    ∀ {k : ℕ}, d ≤ k → minSplit g n k ≤ g d + g (n / d) := by
  intro k
  induction k with
  | zero => intro hdk; omega
  | succ k ih =>
      intro hdk
      simp only [minSplit]
      rcases Nat.lt_or_ge d (k + 1) with hlt | hge
      · exact le_trans (min_le_right _ _) (ih (by omega))
      · have hde : d = k + 1 := by omega
        subst hde
        rw [if_pos ⟨hd, hdvd⟩]
        exact le_trans (min_le_left _ _) (min_le_right _ _)

/-- The search value is attained: it is the trivial candidate `n`, an
additive candidate, or a multiplicative candidate. This is the
destructor used to realize `complexityRec n` by an actual expression. -/
theorem minSplit_cases (g : ℕ → ℕ) (n k : ℕ) :
    minSplit g n k = n ∨
      (∃ a, 1 ≤ a ∧ a ≤ k ∧ minSplit g n k = g a + g (n - a)) ∨
      (∃ d, 2 ≤ d ∧ d ≤ k ∧ d ∣ n ∧ minSplit g n k = g d + g (n / d)) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
      simp only [minSplit]
      rcases min_choice
          (min (g (k + 1) + g (n - (k + 1)))
            (if 2 ≤ k + 1 ∧ (k + 1) ∣ n then g (k + 1) + g (n / (k + 1)) else n))
          (minSplit g n k) with h | h
      · rw [h]
        rcases min_choice (g (k + 1) + g (n - (k + 1)))
            (if 2 ≤ k + 1 ∧ (k + 1) ∣ n then g (k + 1) + g (n / (k + 1)) else n)
            with h2 | h2
        · rw [h2]
          exact Or.inr (Or.inl ⟨k + 1, by omega, le_refl (k + 1), rfl⟩)
        · rw [h2]
          by_cases hg : 2 ≤ k + 1 ∧ (k + 1) ∣ n
          · rw [if_pos hg]
            exact Or.inr (Or.inr ⟨k + 1, hg.1, le_refl (k + 1), hg.2, rfl⟩)
          · rw [if_neg hg]
            exact Or.inl rfl
      · rw [h]
        rcases ih with h1 | ⟨a, ha1, hak, he⟩ | ⟨d, hd2, hdk, hdvd, he⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl ⟨a, ha1, by omega, he⟩)
        · exact Or.inr (Or.inr ⟨d, hd2, by omega, hdvd, he⟩)

/-- The search only queries its oracle at arguments below `n` (all of
`a`, `n - a`, `n / d` are `< n` when `k < n`), so oracles agreeing below
`n` give equal searches. -/
theorem minSplit_congr {g₁ g₂ : ℕ → ℕ} {n : ℕ}
    (h : ∀ m, m < n → g₁ m = g₂ m) :
    ∀ {k : ℕ}, k < n → minSplit g₁ n k = minSplit g₂ n k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have h1 : g₁ (k + 1) = g₂ (k + 1) := h (k + 1) hk
      have h2 : g₁ (n - (k + 1)) = g₂ (n - (k + 1)) := h (n - (k + 1)) (by omega)
      have h3 :
          (if 2 ≤ k + 1 ∧ (k + 1) ∣ n then g₁ (k + 1) + g₁ (n / (k + 1)) else n)
            = (if 2 ≤ k + 1 ∧ (k + 1) ∣ n then g₂ (k + 1) + g₂ (n / (k + 1))
              else n) := by
        by_cases hg : 2 ≤ k + 1 ∧ (k + 1) ∣ n
        · have h4 : g₁ (n / (k + 1)) = g₂ (n / (k + 1)) :=
            h (n / (k + 1)) (Nat.div_lt_self (by omega) (by omega))
          rw [if_pos hg, if_pos hg, h1, h4]
        · rw [if_neg hg, if_neg hg]
      simp only [minSplit]
      rw [h3, h1, h2, ih (by omega)]

/-- Fueled integer-complexity recursion: `complexityFuel fuel n` runs the
A005245 search with recursion depth `fuel`. Values: `0` at `n = 0` (junk,
matching `complexity_zero`), `1` at `n = 1`, and one `minSplit` pass with
oracle `complexityFuel (fuel - 1)` at `2 ≤ n`. Exhausted fuel returns the
junk value `0`; `complexityFuel_eq_complexityRec` shows any `fuel` with
`n ≤ fuel` computes the true value. Structural recursion on `fuel` keeps
ground instances kernel-decidable. -/
def complexityFuel : ℕ → ℕ → ℕ
  | 0 => fun n => if n = 1 then 1 else 0
  | fuel + 1 => fun n =>
      match n with
      | 0 => 0
      | 1 => 1
      | m + 2 => minSplit (complexityFuel fuel) (m + 2) ((m + 2) / 2)

/-- `complexityFuel` at `n = 0` is `0` for every fuel. -/
theorem complexityFuel_zero (f : ℕ) : complexityFuel f 0 = 0 := by
  cases f <;> rfl

/-- `complexityFuel` at `n = 1` is `1` for every fuel. -/
theorem complexityFuel_one (f : ℕ) : complexityFuel f 1 = 1 := by
  cases f <;> rfl

/-- Unfolding lemma for `complexityFuel` at `2 ≤ n` with positive fuel. -/
theorem complexityFuel_succ (f m : ℕ) :
    complexityFuel (f + 1) (m + 2)
      = minSplit (complexityFuel f) (m + 2) ((m + 2) / 2) := rfl

/-- Computable integer complexity: the fueled recursion with fuel `n`
(sufficient by `complexityFuel_eq_complexityRec`). Agrees with the norm
`complexity` by the master theorem `complexity_eq_complexityRec`; concrete
values close by kernel `decide`. -/
def complexityRec (n : ℕ) : ℕ := complexityFuel n n

/-- `complexityRec 0 = 0` — the same junk value as `complexity_zero`. -/
theorem complexityRec_zero : complexityRec 0 = 0 := rfl

/-- `complexityRec 1 = 1`. -/
theorem complexityRec_one : complexityRec 1 = 1 := rfl

-- ground checks for the fueled engine (OEIS A005245: a(6) = 5)
example : complexityFuel 6 6 = 5 := by decide
example : complexityFuel 0 5 = 0 := rfl   -- exhausted fuel: junk value
example : complexityFuel 1 1 = 1 := rfl
example : complexityRec 0 = 0 := rfl      -- junk value at 0

/-- Fuel invariance: any fuel of at least `n` computes `complexityRec n`.
The proof is strong induction on the fuel through `minSplit_congr`, whose
oracle calls all land strictly below `n`. -/
theorem complexityFuel_eq_complexityRec (f : ℕ) :
    ∀ n, n ≤ f → complexityFuel f n = complexityRec n := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro n hnf
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · rw [complexityFuel_zero, complexityRec_zero]
      · rw [complexityFuel_one, complexityRec_one]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      obtain ⟨fp, rfl⟩ : ∃ fp, f = fp + 1 := ⟨f - 1, by omega⟩
      rw [complexityFuel_succ]
      have hR : complexityRec (m + 2)
          = minSplit (complexityFuel (m + 1)) (m + 2) ((m + 2) / 2) := rfl
      rw [hR]
      refine minSplit_congr (fun v hv => ?_) (by omega)
      rw [ih fp (by omega) v (by omega), ih (m + 1) (by omega) v (by omega)]

/-- THE RECURRENCE (OEIS A005245): for `2 ≤ n`, `complexityRec n` is the
minimum of `n`, of `complexityRec a + complexityRec (n - a)` over
`1 ≤ a ≤ n/2`, and of `complexityRec d + complexityRec (n / d)` over
divisors `2 ≤ d ≤ n/2` of `n`. -/
theorem complexityRec_eq_minSplit {n : ℕ} (hn : 2 ≤ n) :
    complexityRec n = minSplit complexityRec n (n / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  calc complexityRec (m + 2)
      = minSplit (complexityFuel (m + 1)) (m + 2) ((m + 2) / 2) := rfl
    _ = minSplit complexityRec (m + 2) ((m + 2) / 2) :=
        minSplit_congr
          (fun v hv => complexityFuel_eq_complexityRec (m + 1) v (by omega))
          (by omega)

/-- `complexityRec n ≤ n`: the search never beats the all-ones bound. -/
theorem complexityRec_le_self (n : ℕ) : complexityRec n ≤ n := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · exact le_refl 0
    · exact le_refl 1
  · rw [complexityRec_eq_minSplit h2]
    exact minSplit_le_self complexityRec n (n / 2)

/-- Subadditivity of the recursion under addition (`1 ≤ a`, `1 ≤ b`):
the split at `min a b ≤ (a+b)/2` is among the scanned candidates. -/
theorem complexityRec_add_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    complexityRec (a + b) ≤ complexityRec a + complexityRec b := by
  rw [complexityRec_eq_minSplit (by omega)]
  rcases le_total a b with hab | hab
  · have h := minSplit_le_add complexityRec (n := a + b) ha
      (k := (a + b) / 2) (by omega)
    have hs : a + b - a = b := by omega
    rw [hs] at h
    exact h
  · have h := minSplit_le_add complexityRec (n := a + b) hb
      (k := (a + b) / 2) (by omega)
    have hs : a + b - b = a := by omega
    rw [hs] at h
    omega

/-- Subadditivity of the recursion under multiplication (`1 ≤ a`,
`1 ≤ b`): factors `1` are absorbed, and otherwise the divisor split at
`min a b ≤ (a·b)/2` is among the scanned candidates. -/
theorem complexityRec_mul_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    complexityRec (a * b) ≤ complexityRec a + complexityRec b := by
  rcases Nat.eq_or_lt_of_le ha with h1a | h2a
  · rw [← h1a, one_mul, complexityRec_one]
    omega
  rcases Nat.eq_or_lt_of_le hb with h1b | h2b
  · rw [← h1b, mul_one, complexityRec_one]
    omega
  have h4 : 4 ≤ a * b := by
    calc 4 = 2 * 2 := rfl
      _ ≤ a * b := Nat.mul_le_mul h2a h2b
  rw [complexityRec_eq_minSplit (by omega)]
  rcases le_total a b with hab | hab
  · have hk : a ≤ a * b / 2 := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      exact Nat.mul_le_mul (le_refl a) (by omega)
    have h := minSplit_le_mul complexityRec (by omega) (dvd_mul_right a b) hk
    rw [Nat.mul_div_cancel_left b (show 0 < a by omega)] at h
    exact h
  · have hk : b ≤ a * b / 2 := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc b * 2 ≤ b * a := Nat.mul_le_mul (le_refl b) (by omega)
        _ = a * b := Nat.mul_comm b a
    have h := minSplit_le_mul complexityRec (by omega) (dvd_mul_left b a) hk
    rw [Nat.mul_div_cancel a (show 0 < b by omega)] at h
    omega

/-- Realization: for `1 ≤ n` some expression evaluates to `n` with cost
at most `complexityRec n` (strong induction along `minSplit_cases`). -/
theorem exists_cost_le_complexityRec :
    ∀ n : ℕ, 1 ≤ n → ∃ e : Expr, e.eval = n ∧ e.cost ≤ complexityRec n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have h1 : n = 1 := by omega
      subst h1
      exact ⟨Expr.one, rfl, le_refl 1⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rcases minSplit_cases complexityRec (m + 2) ((m + 2) / 2) with
        hb | ⟨a, ha1, hak, he⟩ | ⟨d, hd2, hdk, hdvd, he⟩
      · refine ⟨Expr.ones (m + 1), ?_, ?_⟩
        · rw [Expr.eval_ones]
        · rw [Expr.cost_ones, complexityRec_eq_minSplit (by omega), hb]
      · obtain ⟨e₁, he₁, hc₁⟩ := ih a (by omega) (by omega)
        obtain ⟨e₂, he₂, hc₂⟩ := ih (m + 2 - a) (by omega) (by omega)
        refine ⟨Expr.add e₁ e₂, ?_, ?_⟩
        · simp only [Expr.eval, he₁, he₂]
          omega
        · simp only [Expr.cost]
          rw [complexityRec_eq_minSplit (by omega), he]
          exact Nat.add_le_add hc₁ hc₂
      · have hdn : d ≤ m + 2 := Nat.le_of_dvd (by omega) hdvd
        obtain ⟨e₁, he₁, hc₁⟩ := ih d (by omega) (by omega)
        obtain ⟨e₂, he₂, hc₂⟩ := ih ((m + 2) / d)
          (Nat.div_lt_self (by omega) (by omega))
          ((Nat.one_le_div_iff (by omega)).mpr hdn)
        refine ⟨Expr.mul e₁ e₂, ?_, ?_⟩
        · simp only [Expr.eval, he₁, he₂]
          exact Nat.mul_div_cancel' hdvd
        · simp only [Expr.cost]
          rw [complexityRec_eq_minSplit (by omega), he]
          exact Nat.add_le_add hc₁ hc₂

/-- Optimality: the recursion lower-bounds the cost of every expression
(structural induction through the subadditivity lemmas). -/
theorem complexityRec_le_cost (e : Expr) : complexityRec e.eval ≤ e.cost := by
  induction e with
  | one => exact le_refl 1
  | add a b iha ihb =>
      simp only [Expr.eval, Expr.cost]
      calc complexityRec (a.eval + b.eval)
          ≤ complexityRec a.eval + complexityRec b.eval :=
            complexityRec_add_le a.one_le_eval b.one_le_eval
        _ ≤ a.cost + b.cost := Nat.add_le_add iha ihb
  | mul a b iha ihb =>
      simp only [Expr.eval, Expr.cost]
      calc complexityRec (a.eval * b.eval)
          ≤ complexityRec a.eval + complexityRec b.eval :=
            complexityRec_mul_le a.one_le_eval b.one_le_eval
        _ ≤ a.cost + b.cost := Nat.add_le_add iha ihb

/-! ## 4. The master theorem and OEIS ground checks -/

/-- MASTER THEOREM: the norm agrees with the computable recursion
everywhere (at `0` both take the junk value `0`). Concrete values of
`complexity` are decidable through this bridge by kernel `decide`. -/
theorem complexity_eq_complexityRec (n : ℕ) : complexity n = complexityRec n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [complexity_zero, complexityRec_zero]
  · apply le_antisymm
    · obtain ⟨e, he, hc⟩ := exists_cost_le_complexityRec n hn
      exact le_trans (complexity_le_cost he) hc
    · obtain ⟨e, he, hc⟩ := exists_cost_eq_complexity hn
      calc complexityRec n = complexityRec e.eval := by rw [he]
        _ ≤ e.cost := complexityRec_le_cost e
        _ = complexity n := hc

-- GROUND TRUTH (`oeis show A005245`, pulled live 2026-07-29):
-- a(1..12) = 1, 2, 3, 4, 5, 5, 6, 6, 6, 7, 8, 7. All closed by kernel
-- `decide`; no `native_decide` in this file.
example :
    (List.range 12).map (fun i => complexityRec (i + 1))
      = [1, 2, 3, 4, 5, 5, 6, 6, 6, 7, 8, 7] := by decide

example : complexity 0 = 0 := complexity_zero   -- junk pin, not A005245
example : complexity 1 = 1 := complexity_one
example : complexity 6 = 5 := by
  rw [complexity_eq_complexityRec]; decide
-- `maxRecDepth`: evaluating `complexityRec 11` cold exceeds the
-- elaborator's default recursion depth (the kernel re-checks either way)
set_option maxRecDepth 8192 in
example : complexity 11 = 8 := by
  rw [complexity_eq_complexityRec]; decide
set_option maxRecDepth 8192 in
example : complexity 12 = 7 := by
  rw [complexity_eq_complexityRec]; decide

-- integer complexity is NOT monotone: a(12) = 7 < 8 = a(11)
set_option maxRecDepth 8192 in
example : complexity 12 < complexity 11 := by
  rw [complexity_eq_complexityRec, complexity_eq_complexityRec]; decide

/-! ### Satisfiability of the guarded statements

Every hypothesis-bearing theorem above is instantiated jointly at a
concrete model, so none of them is vacuous. -/

example : complexity (2 + 3) ≤ complexity 2 + complexity 3 :=
  complexity_add_le (by omega) (by omega)
example : complexity (2 * 3) = complexity 2 + complexity 3 := by
  simp only [complexity_eq_complexityRec]; decide
example : complexity (2 * 3) ≤ complexity 2 + complexity 3 :=
  complexity_mul_le (by omega) (by omega)
example : complexity 4 ≤ 4 := complexity_le_self (by omega)
example : 1 ≤ complexity 4 := one_le_complexity (by omega)
example : ∃ e : Expr, e.eval = 6 ∧ e.cost = complexity 6 :=
  exists_cost_eq_complexity (by omega)
example : ∃ e : Expr, e.eval = 6 ∧ e.cost ≤ complexityRec 6 :=
  exists_cost_le_complexityRec 6 (by omega)
example : complexity 2 ≤ (Expr.add Expr.one Expr.one).cost :=
  complexity_le_cost rfl
example : 5 ≤ complexity 6 :=
  le_complexity (by omega) fun e he => by
    have h := complexityRec_le_cost e
    rw [he] at h
    calc 5 = complexityRec 6 := by decide
      _ ≤ e.cost := h
example : complexityRec 6 = minSplit complexityRec 6 3 :=
  complexityRec_eq_minSplit (by omega)
example : minSplit complexityRec 12 6 ≤ complexityRec 5 + complexityRec 7 :=
  minSplit_le_add complexityRec (by omega) (by omega)
example : minSplit complexityRec 12 6 ≤ complexityRec 3 + complexityRec 4 :=
  minSplit_le_mul complexityRec (by omega) (by decide) (by omega)
example : minSplit complexityRec 12 6 ≤ 12 :=
  minSplit_le_self complexityRec 12 6
example : minSplit complexityRec 6 2 = minSplit complexityRec 6 2 :=
  minSplit_congr (fun _ _ => rfl) (by omega)
example : complexityFuel 100 6 = complexityRec 6 :=
  complexityFuel_eq_complexityRec 100 6 (by omega)
example : complexityRec (2 + 3) ≤ complexityRec 2 + complexityRec 3 :=
  complexityRec_add_le (by omega) (by omega)
example : complexityRec (2 * 3) ≤ complexityRec 2 + complexityRec 3 :=
  complexityRec_mul_le (by omega) (by omega)

end NumberComplexity
