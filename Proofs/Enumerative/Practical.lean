import Mathlib

/-!
# Practical numbers (OEIS A005153): definition, decidability, Stewart-step closure

A positive integer `n` is a *practical number* if every `m ≤ n` is a sum of distinct
divisors of `n`; the sequence begins `1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, 32, …`
(OEIS A005153, pulled live 2026-07-30).  The entry's name quantifies over
`m ≤ σ(n)` and its first comment records the classical `m ≤ n` form as equivalent;
this file takes the classical `m ≤ n` form as *the definition* (Srinivasan 1948,
Sierpiński 1955, Stewart 1954) and proves the `m ≤ σ(n)` form as a theorem
(`Nat.practical_iff_forall_le_sum_divisors`).

`Nat.Practical` is absent from Mathlib (leandoc miss re-verified 2026-07-30).
This file is the shared definition layer for the practical-number family:

* `Nat.Practical` — the predicate, with an explicit `0 < n` conjunct pinning the junk
  value `Nat.divisors 0 = ∅` (without the guard, `0` would be vacuously practical);
* a `Decidable` instance with `decide` ground-truth checks against the live OEIS data,
  including the full A005153 prefix below `33`;
* `Finset.exists_subset_sum_eq_of_forall_le_one_add_sum` — the *complete-set engine*:
  a finite set of naturals in which every element exceeds the sum of the smaller
  elements by at most `1` represents every value up to its total sum as a subset sum;
* `Nat.practical_iff_forall_le_sum_divisors` — the strong (`m ≤ σ(n)`) characterisation;
* `Nat.Practical.two_dvd` — every practical `n > 1` is even;
* `Nat.Practical.two_mul_le_one_add_sum_divisors` — Srinivasan's bound `2n ≤ σ(n) + 1`
  (A103288);
* `Nat.Practical.mul_prime_pow` — the **Stewart sufficiency step** (Stewart 1954): if
  `n` is practical, `p` is a prime not dividing `n`, and `p ≤ σ(n) + 1`, then
  `n * p ^ k` is practical.  The step is unordered in `p` (strictly stronger than the
  ascending-order step of Stewart's criterion).  Iterating it would yield the
  sufficiency direction of Stewart's structure theorem, but the factorisation-indexed
  iteration is **not formalized here** — this file provides the single step and
  hand-unrolled instances.  `Nat.practical_two_pow` is the base instance.
* `Nat.IsMultiperfect` and `Nat.coleman_multiperfect_practical` — the archived
  **Coleman conjecture** (OEIS A007691 comment, Jaycob Coleman, Oct 15 2013): every
  multiply-perfect number is practical.  **OPEN**; it is this file's single intended
  `sorry`.  The sorry-free realization layer certifies the conjecture at the first
  ten terms of A007691 (`1` through `523776`), via kernel `decide` where feasible and
  the Stewart step elsewhere.

## Axiom audit

`Nat.coleman_multiperfect_practical` carries the single intended `sorry` and reports
`sorryAx` by construction.  Every other declaration reports a subset of
`{propext, Classical.choice, Quot.sound}`.  There is no `native_decide` in this file;
kernel `decide` at ranges past `512` carries a per-declaration `maxRecDepth` bump.
-/

set_option autoImplicit false

namespace Nat

/-- A natural number `n` is a **practical number** (OEIS A005153) if `0 < n` and every
`m ≤ n` is a sum of distinct divisors of `n`; equivalently, some `S ⊆ n.divisors`
satisfies `∑ d ∈ S, d = m`.  This is the classical definition (Srinivasan 1948,
Stewart 1954); the OEIS-name form quantifying over all `m ≤ σ(n)` is equivalent —
`Nat.practical_iff_forall_le_sum_divisors`.

The `0 < n` conjunct is a deliberate guard: `Nat.divisors 0 = ∅` and the only `m ≤ 0`
is `m = 0`, represented by `S = ∅` (see `Nat.practical_condition_zero`), so without
the guard `0` would be vacuously practical, contradicting A005153's "positive
integers".  `1` and `2` are practical (`Nat.practical_one`, `Nat.practical_two`). -/
def Practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m ≤ n, ∃ S ∈ n.divisors.powerset, ∑ d ∈ S, d = m

/-- `Nat.Practical` is decidable: the outer quantifier is bounded by `n` and the inner
existential ranges over the finite powerset of the divisor set. -/
instance decidablePredPractical : DecidablePred Practical := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ ∀ m ≤ n, ∃ S ∈ n.divisors.powerset,
    ∑ d ∈ S, d = m))

/-- A practical number is positive. -/
theorem Practical.pos {n : ℕ} (h : n.Practical) : 0 < n := h.1

/-- The representation condition alone is *vacuously* satisfiable at `0`: the only
`m ≤ 0` is `0`, represented by `∅ ∈ (Nat.divisors 0).powerset`.  This records why
`Nat.Practical` carries the `0 < n` guard. -/
theorem practical_condition_zero :
    ∀ m ≤ 0, ∃ S ∈ (Nat.divisors 0).powerset, ∑ d ∈ S, d = m := by decide

/-- `0` is not practical: the positivity guard rules it out. -/
theorem not_practical_zero : ¬ Practical 0 := fun h => Nat.lt_irrefl 0 h.pos

/-- `1` is practical: `0 = ∑ ∅` and `1 = ∑ {1}`.  First term of A005153. -/
theorem practical_one : Practical 1 := by decide

/-- `2` is practical: `{1, 2}` represents `0, 1, 2`.  Second term of A005153.  The
even-ness forcing `Nat.Practical.two_dvd` starts only at `n > 1`, so `1` is the sole
odd practical number. -/
theorem practical_two : Practical 2 := by decide

/-- Subset form of the definition, for consumers who prefer `⊆` to powerset
membership. -/
theorem practical_iff_exists_subset (n : ℕ) :
    n.Practical ↔ 0 < n ∧ ∀ m ≤ n, ∃ S ⊆ n.divisors, ∑ d ∈ S, d = m := by
  constructor
  · rintro ⟨hn, hrep⟩
    exact ⟨hn, fun m hm => by
      obtain ⟨S, hS, hsum⟩ := hrep m hm
      exact ⟨S, Finset.mem_powerset.mp hS, hsum⟩⟩
  · rintro ⟨hn, hrep⟩
    exact ⟨hn, fun m hm => by
      obtain ⟨S, hS, hsum⟩ := hrep m hm
      exact ⟨S, Finset.mem_powerset.mpr hS, hsum⟩⟩

/-- Accessor: a practical `n` represents every `m ≤ n` as a subset sum of its
divisors. -/
theorem Practical.exists_sum_eq {n m : ℕ} (h : n.Practical) (hm : m ≤ n) :
    ∃ S ⊆ n.divisors, ∑ d ∈ S, d = m :=
  ((practical_iff_exists_subset n).mp h).2 m hm

end Nat

/-!
## Ground-truth checks

Live A005153 prefix: `1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, 32` are exactly the
practical numbers below `33`; `decide` confirms the full prefix, plus the individual
positive and negative witnesses the module docstring promises.
-/

example : Nat.Practical 1 := by decide
example : Nat.Practical 2 := by decide
example : Nat.Practical 4 := by decide
example : Nat.Practical 6 := by decide
example : Nat.Practical 8 := by decide
example : Nat.Practical 12 := by decide

-- Negative witnesses: `3`, `5` (odd `> 1`), and `10` (even, `4` unreachable).
example : ¬ Nat.Practical 0 := by decide
example : ¬ Nat.Practical 3 := by decide
example : ¬ Nat.Practical 5 := by decide
example : ¬ Nat.Practical 10 := by decide

-- Full prefix cross-check against the live A005153 data.
example : (List.range 33).filter (fun n => decide n.Practical) =
    [1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, 32] := by decide

-- Explicit witness at `6`, `m = 5`: the subset `{2, 3}` sums to `5`.
example : ({2, 3} : Finset ℕ) ⊆ (6 : ℕ).divisors ∧
    ∑ d ∈ ({2, 3} : Finset ℕ), d = 5 := by decide

/-!
## The complete-set engine

A finite set of naturals is *complete* if every element exceeds the sum of the
strictly smaller elements by at most `1`.  A complete set represents every value up
to its total sum as a subset sum — the interval-extension engine underneath both the
strong (`σ`) characterisation and Stewart's criterion.
-/

/-- **Complete-set engine.**  If every `a ∈ A` satisfies
`a ≤ 1 + ∑ x ∈ A.filter (· < a), x`, then every `m ≤ ∑ x ∈ A, x` is a sum over some
subset of `A`.  Induction peeling the largest element: values up to the remaining sum
use the induction hypothesis directly, and larger values subtract the peeled maximum
first — the completeness bound at the maximum makes the two ranges overlap. -/
theorem Finset.exists_subset_sum_eq_of_forall_le_one_add_sum {A : Finset ℕ}
    (hA : ∀ a ∈ A, a ≤ 1 + ∑ x ∈ A.filter (fun x => x < a), x)
    {m : ℕ} (hm : m ≤ ∑ x ∈ A, x) :
    ∃ S ⊆ A, ∑ x ∈ S, x = m := by
  induction A using Finset.strongInduction generalizing m with
  | _ A ih =>
    rcases A.eq_empty_or_nonempty with rfl | hne
    · have hm0 : m = 0 := by simpa using hm
      exact ⟨∅, Finset.Subset.refl _, by simp [hm0]⟩
    · -- peel the maximum `a`; write `A = A' ⊔ {a}`
      set a := A.max' hne with ha_def
      have ha_mem : a ∈ A := A.max'_mem hne
      set A' := A.erase a with hA'_def
      have hA'_ssub : A' ⊂ A := Finset.erase_ssubset ha_mem
      -- the completeness hypothesis restricts to `A'`
      have hA' : ∀ b ∈ A', b ≤ 1 + ∑ x ∈ A'.filter (fun x => x < b), x := by
        intro b hb
        have hb_le : b ≤ a := A.le_max' b (Finset.mem_of_mem_erase hb)
        have hfilter : A'.filter (fun x => x < b) = A.filter (fun x => x < b) := by
          rw [hA'_def, Finset.filter_erase]
          exact Finset.erase_eq_of_notMem fun hc =>
            absurd (Finset.mem_filter.mp hc).2 (by omega)
        rw [hfilter]
        exact hA b (Finset.mem_of_mem_erase hb)
      have hsplit : ∑ x ∈ A', x + a = ∑ x ∈ A, x :=
        Finset.sum_erase_add A _ ha_mem
      -- the maximum respects the completeness bound against the whole of `A'`
      have ha_le : a ≤ 1 + ∑ x ∈ A', x := by
        have hsub : A.filter (fun x => x < a) ⊆ A' := fun x hx => by
          have hx' := Finset.mem_filter.mp hx
          exact Finset.mem_erase.mpr ⟨by omega, hx'.1⟩
        exact (hA a ha_mem).trans
          (Nat.add_le_add_left (Finset.sum_le_sum_of_subset hsub) 1)
      rcases le_or_gt m (∑ x ∈ A', x) with hle | hgt
      · -- small values: recurse into `A'` directly
        obtain ⟨S, hS_sub, hS_sum⟩ := ih A' hA'_ssub hA' hle
        exact ⟨S, hS_sub.trans (Finset.erase_subset a A), hS_sum⟩
      · -- large values: subtract the peeled maximum first
        have ham : a ≤ m := by omega
        obtain ⟨S', hS'_sub, hS'_sum⟩ := ih A' hA'_ssub hA' (m := m - a) (by omega)
        have ha_not : a ∉ S' := fun hc => Finset.notMem_erase a A (hS'_sub hc)
        refine ⟨insert a S', ?_, ?_⟩
        · exact Finset.insert_subset_iff.mpr
            ⟨ha_mem, hS'_sub.trans (Finset.erase_subset a A)⟩
        · rw [Finset.sum_insert ha_not, hS'_sum]
          omega

-- Satisfiability at a concrete complete set: `{1, 2, 4}` represents `0`–`7`.
example : ∀ a ∈ ({1, 2, 4} : Finset ℕ),
    a ≤ 1 + ∑ x ∈ ({1, 2, 4} : Finset ℕ).filter (fun x => x < a), x := by decide

namespace Nat

/-- **Divisor-gap bound**: in a practical number, every divisor `d` exceeds the sum of
the strictly smaller divisors by at most `1` — the representation of `d - 1` can only
use divisors `< d`.  This is the completeness of `n.divisors` that feeds the
complete-set engine. -/
theorem Practical.divisor_le_one_add_sum {n d : ℕ} (h : n.Practical)
    (hd : d ∈ n.divisors) :
    d ≤ 1 + ∑ x ∈ n.divisors.filter (fun x => x < d), x := by
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
  obtain ⟨S, hS_sub, hS_sum⟩ :=
    h.exists_sum_eq ((Nat.sub_le d 1).trans (Nat.divisor_le hd))
  -- every divisor in the representation of `d - 1` is `< d`
  have hS_filter : S ⊆ n.divisors.filter (fun x => x < d) := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨hS_sub hx, ?_⟩
    have hx_le : x ≤ d - 1 :=
      hS_sum ▸ Finset.single_le_sum (f := fun x : ℕ => x) (fun i _ => Nat.zero_le i) hx
    omega
  have hle : d - 1 ≤ ∑ x ∈ n.divisors.filter (fun x => x < d), x :=
    hS_sum ▸ Finset.sum_le_sum_of_subset hS_filter
  omega

/-- **Strong characterisation** (the OEIS A005153 name form): `n` is practical iff
`0 < n` and every `m ≤ σ(n) = ∑ d ∈ n.divisors, d` is a sum of distinct divisors of
`n`.  Forward: the divisor-gap bound plus the complete-set engine.  Backward:
`m ≤ n ≤ σ(n)`. -/
theorem practical_iff_forall_le_sum_divisors {n : ℕ} :
    n.Practical ↔
      0 < n ∧ ∀ m ≤ ∑ d ∈ n.divisors, d, ∃ S ⊆ n.divisors, ∑ d ∈ S, d = m := by
  constructor
  · intro h
    exact ⟨h.pos, fun m hm =>
      Finset.exists_subset_sum_eq_of_forall_le_one_add_sum
        (fun d hd => h.divisor_le_one_add_sum hd) hm⟩
  · rintro ⟨hpos, hrep⟩
    rw [practical_iff_exists_subset]
    refine ⟨hpos, fun m hm => hrep m (hm.trans ?_)⟩
    exact Finset.single_le_sum (f := fun x : ℕ => x) (fun i _ => Nat.zero_le i)
      (Nat.mem_divisors_self n hpos.ne')

/-- Accessor for the strong characterisation: a practical `n` represents every
`m ≤ σ(n)` as a subset sum of its divisors. -/
theorem Practical.exists_sum_eq_of_le_sum_divisors {n m : ℕ} (h : n.Practical)
    (hm : m ≤ ∑ d ∈ n.divisors, d) : ∃ S ⊆ n.divisors, ∑ d ∈ S, d = m :=
  (practical_iff_forall_le_sum_divisors.mp h).2 m hm

/-- Every practical number `n > 1` is even: the only subset sums equal to `2` are
`{2}` and `{1, 1}`, and the latter is not a set, so `2` must itself divide `n`.
(A005153 comments; the guard `1 < n` is sharp — `1` is odd and practical.) -/
theorem Practical.two_dvd {n : ℕ} (h : n.Practical) (hn : 1 < n) : 2 ∣ n := by
  obtain ⟨S, hS_sub, hS_sum⟩ := h.exists_sum_eq (show 2 ≤ n from hn)
  by_cases h2 : 2 ∈ S
  · exact (Nat.mem_divisors.mp (hS_sub h2)).1
  · -- without `2`, all summands are `1`, so the sum is at most `1 < 2`
    exfalso
    have hS_one : S ⊆ {1} := by
      intro x hx
      have hx_pos : 0 < x := Nat.pos_of_mem_divisors (hS_sub hx)
      have hx_le : x ≤ 2 :=
        hS_sum ▸ Finset.single_le_sum (f := fun x : ℕ => x) (fun i _ => Nat.zero_le i) hx
      have hx_ne : x ≠ 2 := fun hc => h2 (hc ▸ hx)
      have hx1 : x = 1 := by omega
      simp [hx1]
    have hle : ∑ d ∈ S, d ≤ ∑ d ∈ ({1} : Finset ℕ), d :=
      Finset.sum_le_sum_of_subset hS_one
    rw [hS_sum, Finset.sum_singleton] at hle
    omega

-- Satisfiability and sharpness of `Nat.Practical.two_dvd`: `6` is practical with
-- `1 < 6` (and indeed even); `1` is practical and odd, so the guard is needed.
example : (6 : ℕ).Practical ∧ (1 : ℕ) < 6 := by decide
example : (1 : ℕ).Practical ∧ ¬ 2 ∣ (1 : ℕ) := by decide

-- Satisfiability of `Nat.Practical.divisor_le_one_add_sum` at `n = 6`, `d = 3`:
-- `3 ≤ 1 + (1 + 2)`.
example : (6 : ℕ).Practical ∧ 3 ∈ (6 : ℕ).divisors := by decide

/-- **Srinivasan's bound** (Srinivasan 1948; cf. OEIS A103288): a practical number satisfies
`σ(n) ≥ 2n - 1`, stated subtraction-free as `2n ≤ 1 + σ(n)`.  The representation of
`n - 1` cannot use the divisor `n`, so `σ(n) ≥ n + (n - 1)`. -/
theorem Practical.two_mul_le_one_add_sum_divisors {n : ℕ} (h : n.Practical) :
    2 * n ≤ 1 + ∑ d ∈ n.divisors, d := by
  have hpos := h.pos
  obtain ⟨S, hS_sub, hS_sum⟩ := h.exists_sum_eq (Nat.sub_le n 1)
  -- the representation of `n - 1` avoids the divisor `n` itself
  have hS_erase : S ⊆ n.divisors.erase n := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, hS_sub hx⟩
    have hx_le : x ≤ n - 1 :=
      hS_sum ▸ Finset.single_le_sum (f := fun x : ℕ => x) (fun i _ => Nat.zero_le i) hx
    omega
  have h1 : n - 1 ≤ ∑ x ∈ n.divisors.erase n, x :=
    hS_sum ▸ Finset.sum_le_sum_of_subset hS_erase
  have h2 : ∑ x ∈ n.divisors.erase n, x + n = ∑ d ∈ n.divisors, d :=
    Finset.sum_erase_add _ _ (Nat.mem_divisors_self n hpos.ne')
  omega

/-!
## The Stewart sufficiency step

Stewart's structure theorem (1954) characterises practical numbers: `n ≥ 2` with
factorisation `p₁^{a₁} ⋯ p_r^{a_r}`, `p₁ < ⋯ < p_r`, is practical iff `p₁ = 2` and
`p_{i+1} ≤ σ(p₁^{a₁} ⋯ p_i^{a_i}) + 1` for each `i`.  The sufficiency direction is
the closure engine below: one step adjoins a coprime prime power whose base respects
the `σ + 1` bound.  Iterating from `n = 1` (where `p ≤ σ(1) + 1 = 2` forces `p₁ = 2`)
would yield every admissible factorisation; the factorisation-indexed iteration and
the necessity direction are not formalized here (follow-on lane).
-/

/-- **Bounded base-`p` digits**: any `m ≤ B * (1 + p + ⋯ + p^k)` with `p ≤ 1 + B` is
`∑ i ∈ range (k+1), c i * p^i` for digits `c i ≤ B`.  (For `p ≤ 1 + B` the bounded
digit strings cover the whole interval with no gaps — the arithmetic core of the
Stewart step, applied with `B = σ(n)`.)  Greedy top digit: take
`c k = min B (m / p^k)` and recurse. -/
theorem exists_digits_le_mul_geom_sum {B p : ℕ} (hp : 0 < p) (hpB : p ≤ 1 + B) :
    ∀ k m : ℕ, m ≤ B * ∑ i ∈ Finset.range (k + 1), p ^ i →
      ∃ c : ℕ → ℕ, (∀ i, c i ≤ B) ∧ m = ∑ i ∈ Finset.range (k + 1), c i * p ^ i := by
  intro k
  induction k with
  | zero =>
    intro m hm
    have hmB : m ≤ B := by simpa using hm
    refine ⟨fun i => if i = 0 then m else 0, fun i => ?_, by simp⟩
    by_cases hi : i = 0 <;> simp [hi, hmB]
  | succ k ih =>
    intro m hm
    -- greedy top digit `q`, remainder `m - q * p^(k+1)`
    set b := p ^ (k + 1) with hb_def
    have hb_pos : 0 < b := pow_pos hp _
    set q := min B (m / b) with hq_def
    have hqb_le : q * b ≤ m :=
      (Nat.mul_le_mul (min_le_right B (m / b)) (le_refl b)).trans (Nat.div_mul_le_self m b)
    -- checkpoint: the remainder fits under the one-shorter geometric sum
    have hm' : m - q * b ≤ B * ∑ i ∈ Finset.range (k + 1), p ^ i := by
      rcases le_or_gt B (m / b) with hcase | hcase
      · -- saturated digit: `q = B`, subtract a full `B * p^(k+1)` block
        have hqB : q = B := min_eq_left hcase
        rw [Finset.sum_range_succ, Nat.mul_add, ← hb_def] at hm
        rw [hqB]
        omega
      · -- unsaturated digit: `q = m / b`, remainder is `m % b < b ≤ B * ∑ + 1`
        have hqm : q = m / b := min_eq_right hcase.le
        have hmod : m - q * b = m % b := by
          have hdm : m / b * b + m % b = m := Nat.div_add_mod' m b
          rw [hqm]
          omega
        have hlt : m % b < b := Nat.mod_lt m hb_pos
        -- geometric identity in `ℤ`: `(∑ p^i) * (p - 1) = p^(k+1) - 1`
        have hgeom : (b : ℤ) - 1 ≤ (B : ℤ) * ∑ i ∈ Finset.range (k + 1), (p : ℤ) ^ i := by
          have h1 : (∑ i ∈ Finset.range (k + 1), (p : ℤ) ^ i) * ((p : ℤ) - 1)
              = (p : ℤ) ^ (k + 1) - 1 := geom_sum_mul _ _
          have h2 : (p : ℤ) - 1 ≤ (B : ℤ) := by omega
          have h3 : (0 : ℤ) ≤ ∑ i ∈ Finset.range (k + 1), (p : ℤ) ^ i := by positivity
          calc (b : ℤ) - 1 = (p : ℤ) ^ (k + 1) - 1 := by rw [hb_def]; push_cast; ring
            _ = (∑ i ∈ Finset.range (k + 1), (p : ℤ) ^ i) * ((p : ℤ) - 1) := h1.symm
            _ ≤ (∑ i ∈ Finset.range (k + 1), (p : ℤ) ^ i) * (B : ℤ) :=
                mul_le_mul_of_nonneg_left h2 h3
            _ = (B : ℤ) * ∑ i ∈ Finset.range (k + 1), (p : ℤ) ^ i := mul_comm _ _
        have hcast : (B : ℤ) * ∑ i ∈ Finset.range (k + 1), (p : ℤ) ^ i
            = ((B * ∑ i ∈ Finset.range (k + 1), p ^ i : ℕ) : ℤ) := by push_cast; ring
        rw [hcast] at hgeom
        omega
    obtain ⟨c', hc'_le, hc'_sum⟩ := ih (m - q * b) hm'
    refine ⟨fun i => if i = k + 1 then q else c' i, fun i => ?_, ?_⟩
    · by_cases hi : i = k + 1
      · simp only [if_pos hi, hq_def]
        exact min_le_left _ _
      · simp only [if_neg hi]
        exact hc'_le i
    · -- reassemble: the new top digit contributes `q * p^(k+1)`
      have hsplit : ∑ i ∈ Finset.range (k + 1 + 1), (if i = k + 1 then q else c' i) * p ^ i
          = (∑ i ∈ Finset.range (k + 1), c' i * p ^ i) + q * b := by
        rw [Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ k + 1 := Nat.ne_of_lt (Finset.mem_range.mp hi)
          simp [hne]
        · simp [hb_def]
      rw [hsplit, ← hc'_sum]
      omega

-- Satisfiability of `exists_digits_le_mul_geom_sum`: all three hypotheses jointly at
-- `B = 12 = σ(6)`, `p = 7 ≤ 1 + 12`, `k = 1`, `m = 41 ≤ 12 * (1 + 7) = 96`.
example : ∃ c : ℕ → ℕ, (∀ i, c i ≤ 12) ∧
    (41 : ℕ) = ∑ i ∈ Finset.range (1 + 1), c i * 7 ^ i :=
  exists_digits_le_mul_geom_sum (B := 12) (p := 7) (by norm_num) (by norm_num) 1 41
    (by decide)

/-- **Stewart sufficiency step** (Stewart 1954, *Sums of distinct divisors*): if `n`
is practical, `p` is a prime not dividing `n`, and `p ≤ σ(n) + 1`, then `n * p ^ k`
is practical for every `k`.  Any `m ≤ n * p^k` splits into bounded base-`p` digits
`m = ∑ cᵢ p^i` with `cᵢ ≤ σ(n)`; the strong characterisation represents each digit
as a subset sum of `n.divisors`, and scaling the `i`-th subset by `p^i` gives
pairwise-disjoint sets of divisors of `n * p^k` (the `p`-adic valuation of `d * p^i`
is exactly `i`) whose union sums to `m`. -/
theorem Practical.mul_prime_pow {n p : ℕ} (hn : n.Practical) (hp : p.Prime)
    (hpn : ¬ p ∣ n) (hple : p ≤ 1 + ∑ d ∈ n.divisors, d) (k : ℕ) :
    (n * p ^ k).Practical := by
  classical
  have hn_pos : 0 < n := hn.pos
  have hnpk_pos : 0 < n * p ^ k := Nat.mul_pos hn_pos (pow_pos hp.pos k)
  rw [practical_iff_exists_subset]
  refine ⟨hnpk_pos, fun m hm => ?_⟩
  -- checkpoint 1: `m` fits under `σ(n) * (1 + p + ⋯ + p^k)`
  have hσ_ge : n ≤ ∑ d ∈ n.divisors, d :=
    Finset.single_le_sum (fun i _ => Nat.zero_le i)
      (Nat.mem_divisors_self n hn_pos.ne')
  have hpk_le : p ^ k ≤ ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [Finset.sum_range_succ]
    exact Nat.le_add_left _ _
  have hm' : m ≤ (∑ d ∈ n.divisors, d) * ∑ i ∈ Finset.range (k + 1), p ^ i :=
    hm.trans (Nat.mul_le_mul hσ_ge hpk_le)
  -- checkpoint 2: bounded base-`p` digits, each represented over `n.divisors`
  obtain ⟨c, hc_le, hc_sum⟩ :=
    Nat.exists_digits_le_mul_geom_sum hp.pos hple k m hm'
  choose S hS_sub hS_sum using fun i : ℕ =>
    hn.exists_sum_eq_of_le_sum_divisors (hc_le i)
  -- the scaled subsets `S i * p^i`, glued over `i ≤ k`
  set B : Finset ℕ :=
    (Finset.range (k + 1)).biUnion (fun i => (S i).image (fun d => d * p ^ i))
    with hB_def
  have hp_not_dvd : ∀ {d : ℕ}, d ∈ n.divisors → ¬ p ∣ d := fun hd hpd =>
    hpn (hpd.trans (Nat.mem_divisors.mp hd).1)
  -- checkpoint 3: `B` lands inside the divisors of `n * p^k`
  have hB_sub : B ⊆ (n * p ^ k).divisors := by
    intro b hb
    rw [hB_def, Finset.mem_biUnion] at hb
    obtain ⟨i, hi, hb⟩ := hb
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
    refine Nat.mem_divisors.mpr ⟨?_, hnpk_pos.ne'⟩
    exact mul_dvd_mul (Nat.mem_divisors.mp (hS_sub i hd)).1
      (pow_dvd_pow p (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
  -- checkpoint 4: distinct exponents give disjoint scaled sets (`p`-adic valuation)
  have hkey : ∀ {d e i j : ℕ}, i < j → d ∈ n.divisors → e ∈ n.divisors →
      d * p ^ i = e * p ^ j → False := by
    intro d e i j hlt hd he heq
    have hj : j = (j - i) + i := (Nat.sub_add_cancel hlt.le).symm
    rw [hj, pow_add, ← mul_assoc] at heq
    have hde : d = e * p ^ (j - i) :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos i) heq
    have hpd : p ∣ d := by
      rw [hde]
      exact Dvd.dvd.mul_left (dvd_pow_self p (Nat.sub_ne_zero_of_lt hlt)) e
    exact hp_not_dvd hd hpd
  have hdisj : Set.PairwiseDisjoint ↑(Finset.range (k + 1))
      (fun i => (S i).image (fun d => d * p ^ i)) := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro b hbi hbj
    obtain ⟨d, hd, hdb⟩ := Finset.mem_image.mp hbi
    obtain ⟨e, he, heb⟩ := Finset.mem_image.mp hbj
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hkey hlt (hS_sub i hd) (hS_sub j he) (heb ▸ hdb)
    · exact hkey hlt (hS_sub j he) (hS_sub i hd) (hdb ▸ heb)
  -- checkpoint 5: the sum over `B` recovers the digit expansion of `m`
  have hB_sum : ∑ b ∈ B, b = m := by
    rw [hB_def, Finset.sum_biUnion hdisj]
    calc ∑ i ∈ Finset.range (k + 1), ∑ b ∈ (S i).image (fun d => d * p ^ i), b
        = ∑ i ∈ Finset.range (k + 1), ∑ d ∈ S i, d * p ^ i := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_image ?_
          intro x _ y _ hxy
          exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos i) hxy
      _ = ∑ i ∈ Finset.range (k + 1), c i * p ^ i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_mul, hS_sum i]
      _ = m := hc_sum.symm
  exact ⟨B, hB_sub, hB_sum⟩

/-- Every power of `2` is practical (Srinivasan 1948; A005153 comments) — the base
case of Stewart iteration, from `Nat.practical_one` and the step at `p = 2 ≤ σ(1) + 1`. -/
theorem practical_two_pow (k : ℕ) : ((2 : ℕ) ^ k).Practical := by
  have h : ((1 * 2 ^ k : ℕ)).Practical :=
    practical_one.mul_prime_pow Nat.prime_two (by decide) (by decide) k
  simpa using h

end Nat

/-!
## Stewart-step satisfiability checks

All hypotheses of `Nat.Practical.mul_prime_pow` jointly instantiated at concrete
models, cross-checked against the direct decision procedure.
-/

-- `6 * 7 = 42`: `7 ∤ 6` and `7 ≤ 1 + σ(6) = 13`; engine output agrees with `decide`.
example : (42 : ℕ).Practical := by
  have h : ((6 * 7 ^ 1 : ℕ)).Practical :=
    (by decide : (6 : ℕ).Practical).mul_prime_pow (by norm_num) (by decide) (by decide) 1
  simpa using h

example : (42 : ℕ).Practical := by decide

-- `2 ^ 5 = 32 ∈ A005153`, beyond the individual hand checks above.
example : (32 : ℕ).Practical := Nat.practical_two_pow 5

namespace Nat

/-!
## Multiply-perfect numbers and the Coleman conjecture (OEIS A007691)

A007691 (pulled live 2026-07-30): "Multiply-perfect numbers: n divides sigma(n)",
terms `1, 6, 28, 120, 496, 672, 8128, 30240, 32760, 523776, …`.  The archived claim
is the entry's comment by **Jaycob Coleman, Oct 15 2013**: "Conjecture: Every
multiply-perfect number is practical (A005153). I've verified this conjecture for
the first 5261 terms with abundancy > 2 using Achim Flammenkamp's data. The even
perfect numbers are easily shown to be practical, but every practical number > 1 is
even, so a weak form says every even multiply-perfect number is practical."
-/

/-- A natural number `n` is **multiply-perfect** (OEIS A007691) if `0 < n` and
`n ∣ σ(n)`.  The `0 < n` conjunct is a deliberate guard: `Nat.divisors 0 = ∅` gives
`σ(0) = 0` and `0 ∣ 0`, so without the guard `0` would be vacuously multiply-perfect,
contradicting A007691's offset at `1`. -/
def IsMultiperfect (n : ℕ) : Prop :=
  0 < n ∧ n ∣ ∑ d ∈ n.divisors, d

/-- `Nat.IsMultiperfect` is decidable. -/
instance decidablePredIsMultiperfect : DecidablePred IsMultiperfect := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ n ∣ ∑ d ∈ n.divisors, d))

/-- A perfect number is multiply-perfect: `σ(n) = 2n` (abundancy `2`). -/
theorem Perfect.isMultiperfect {n : ℕ} (h : n.Perfect) : n.IsMultiperfect := by
  -- `Nat.Perfect` unfolds as (proper-divisor sum = n) ∧ (0 < n), in that order
  obtain ⟨hsum, hpos⟩ := h
  refine ⟨hpos, ?_⟩
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, hsum]
  exact ⟨2, by ring⟩

-- Satisfiability of `Nat.Perfect.isMultiperfect`: `6` is perfect.
example : Nat.Perfect 6 := ⟨by decide, by norm_num⟩

end Nat

-- Ground-truth checks against the live A007691 prefix, and negative witnesses.
example : Nat.IsMultiperfect 1 := by decide
example : Nat.IsMultiperfect 6 := by decide
example : Nat.IsMultiperfect 28 := by decide
example : Nat.IsMultiperfect 120 := by decide
example : ¬ Nat.IsMultiperfect 0 := by decide
example : ¬ Nat.IsMultiperfect 2 := by decide
example : ¬ Nat.IsMultiperfect 10 := by decide
example : ¬ Nat.IsMultiperfect 24 := by decide

-- Full-prefix discriminating check: exactly the A007691 terms below 200.
set_option maxRecDepth 20000 in
example : (List.range 200).filter (fun n => decide (Nat.IsMultiperfect n)) = [1, 6, 28, 120] := by
  decide

namespace Nat

/-- **Coleman's conjecture** — OEIS A007691, comment of Jaycob Coleman (Oct 15
2013), pulled live: "Conjecture: Every multiply-perfect number is practical
(A005153)."  **OPEN**; this is the file's single intended `sorry`.

Status, per the live entry and this file:

* Coleman reports verification "for the first 5261 terms with abundancy > 2 using
  Achim Flammenkamp's data";
* the realization layer below certifies the conjecture sorry-free at the first ten
  terms of A007691, `1, 6, 28, 120, 496, 672, 8128, 30240, 32760, 523776`
  (`Nat.coleman_instance_1` … `Nat.coleman_instance_523776`), which also witness
  joint satisfiability of the hypothesis;
* Coleman's weak form (every *even* multiply-perfect number is practical) is not
  formalized separately: for even perfect numbers it needs Euclid–Euler, which lives
  in Mathlib's `Archive`, outside this project's dependency set.

ROUTE: Stewart's criterion makes the conjecture verifiable per instance (as the
realization layer does); no proof of the full conjecture is known to anyone. -/
theorem coleman_multiperfect_practical {n : ℕ} (hn : n.IsMultiperfect) :
    n.Practical := by
  -- intended sorry: open conjecture (card Formalize/A007691-coleman-practical.md).
  sorry

/-!
## Sorry-free realization layer: the first ten terms of A007691

Each instance pairs the multiperfect certificate with the practical certificate.
Small terms go through kernel `decide`; from `120` on, the practical side iterates
`Nat.Practical.mul_prime_pow` along the factorisation (checking Stewart's
`p ≤ σ + 1` bound by `decide` at each step), and the multiperfect side of the large
terms splits `σ` through `Nat.Coprime.sum_divisors_mul` to keep kernel ranges small.
These also witness joint satisfiability of `Nat.coleman_multiperfect_practical`'s
hypothesis.
-/

/-- Coleman instance `1` (abundancy `1`). -/
theorem coleman_instance_1 : (1 : ℕ).IsMultiperfect ∧ (1 : ℕ).Practical :=
  ⟨by decide, practical_one⟩

/-- Coleman instance `6 = 2 · 3` (perfect). -/
theorem coleman_instance_6 : (6 : ℕ).IsMultiperfect ∧ (6 : ℕ).Practical := by
  decide

/-- Coleman instance `28 = 2² · 7` (perfect). -/
theorem coleman_instance_28 : (28 : ℕ).IsMultiperfect ∧ (28 : ℕ).Practical := by
  decide

/-- Coleman instance `120 = 2³ · 3 · 5` (abundancy `3`), practical by Stewart steps
`8 → 24 → 120`. -/
theorem coleman_instance_120 : (120 : ℕ).IsMultiperfect ∧ (120 : ℕ).Practical := by
  refine ⟨by decide, ?_⟩
  have h8 : (8 : ℕ).Practical := by decide
  have h24 : (24 : ℕ).Practical := by
    have h := h8.mul_prime_pow (p := 3) (by norm_num) (by decide) (by decide) 1
    simpa using h
  have h := h24.mul_prime_pow (p := 5) (by norm_num) (by decide) (by decide) 1
  simpa using h

set_option maxRecDepth 40000 in
/-- Coleman instance `496 = 2⁴ · 31` (perfect), practical by the Stewart step at
`31 = σ(16)`. -/
theorem coleman_instance_496 : (496 : ℕ).IsMultiperfect ∧ (496 : ℕ).Practical := by
  refine ⟨by decide, ?_⟩
  have h16 : (16 : ℕ).Practical := by decide
  have h := h16.mul_prime_pow (p := 31) (by norm_num) (by decide) (by decide) 1
  simpa using h

set_option maxRecDepth 40000 in
/-- Coleman instance `672 = 2⁵ · 3 · 7` (abundancy `3`), practical by Stewart steps
`32 → 96 → 672`. -/
theorem coleman_instance_672 : (672 : ℕ).IsMultiperfect ∧ (672 : ℕ).Practical := by
  refine ⟨by decide, ?_⟩
  have h32 : (32 : ℕ).Practical := by decide
  have h96 : (96 : ℕ).Practical := by
    have h := h32.mul_prime_pow (p := 3) (by norm_num) (by decide) (by decide) 1
    simpa using h
  have h := h96.mul_prime_pow (p := 7) (by norm_num) (by decide) (by decide) 1
  simpa using h

/-- Coleman instance `8128 = 2⁶ · 127` (perfect), practical by the Stewart step at
`127 = σ(64)`; the multiperfect side splits `σ` over `64 · 127`. -/
theorem coleman_instance_8128 : (8128 : ℕ).IsMultiperfect ∧ (8128 : ℕ).Practical := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    rw [show (8128 : ℕ) = 64 * 127 by norm_num,
      Nat.Coprime.sum_divisors_mul (by decide)]
    decide
  · have h64 : ((2 : ℕ) ^ 6).Practical := practical_two_pow 6
    have h := h64.mul_prime_pow (p := 127) (by norm_num) (by decide) (by decide) 1
    simpa using h

set_option maxRecDepth 40000 in
/-- Coleman instance `30240 = 2⁵ · 3³ · 5 · 7` (abundancy `4`), practical by Stewart
steps `32 → 864 → 4320 → 30240`; the multiperfect side splits `σ` over `864 · 35`. -/
theorem coleman_instance_30240 :
    (30240 : ℕ).IsMultiperfect ∧ (30240 : ℕ).Practical := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    rw [show (30240 : ℕ) = 864 * 35 by norm_num,
      Nat.Coprime.sum_divisors_mul (by decide)]
    decide
  · have h32 : (32 : ℕ).Practical := by decide
    have h864 : (864 : ℕ).Practical := by
      have h := h32.mul_prime_pow (p := 3) (by norm_num) (by decide) (by decide) 3
      simpa using h
    have h4320 : (4320 : ℕ).Practical := by
      have h := h864.mul_prime_pow (p := 5) (by norm_num) (by decide) (by decide) 1
      simpa using h
    have h := h4320.mul_prime_pow (p := 7) (by norm_num) (by decide) (by decide) 1
    simpa using h

set_option maxRecDepth 40000 in
/-- Coleman instance `32760 = 2³ · 3² · 5 · 7 · 13` (abundancy `4`), practical by
Stewart steps `8 → 72 → 360 → 2520 → 32760`; the multiperfect side splits `σ` over
`2520 · 13`. -/
theorem coleman_instance_32760 :
    (32760 : ℕ).IsMultiperfect ∧ (32760 : ℕ).Practical := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    rw [show (32760 : ℕ) = 2520 * 13 by norm_num,
      Nat.Coprime.sum_divisors_mul (by decide)]
    decide
  · have h8 : (8 : ℕ).Practical := by decide
    have h72 : (72 : ℕ).Practical := by
      have h := h8.mul_prime_pow (p := 3) (by norm_num) (by decide) (by decide) 2
      simpa using h
    have h360 : (360 : ℕ).Practical := by
      have h := h72.mul_prime_pow (p := 5) (by norm_num) (by decide) (by decide) 1
      simpa using h
    have h2520 : (2520 : ℕ).Practical := by
      have h := h360.mul_prime_pow (p := 7) (by norm_num) (by decide) (by decide) 1
      simpa using h
    have h := h2520.mul_prime_pow (p := 13) (by norm_num) (by decide) (by decide) 1
    simpa using h

set_option maxRecDepth 40000 in
/-- Coleman instance `523776 = 2⁹ · 3 · 11 · 31` (abundancy `3`), practical by
Stewart steps `512 → 1536 → 16896 → 523776`; both sides split `σ` through
`Nat.Coprime.sum_divisors_mul` to keep kernel ranges below `1537`. -/
theorem coleman_instance_523776 :
    (523776 : ℕ).IsMultiperfect ∧ (523776 : ℕ).Practical := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    rw [show (523776 : ℕ) = 1536 * 341 by norm_num,
      Nat.Coprime.sum_divisors_mul (by decide)]
    decide
  · have h512 : ((2 : ℕ) ^ 9).Practical := practical_two_pow 9
    have h1536 : (1536 : ℕ).Practical := by
      have h := h512.mul_prime_pow (p := 3) (by norm_num) (by decide) (by decide) 1
      simpa using h
    have h16896 : (16896 : ℕ).Practical := by
      have h := h1536.mul_prime_pow (p := 11) (by norm_num) (by decide) (by decide) 1
      simpa using h
    have hσ : (31 : ℕ) ≤ 1 + ∑ d ∈ (16896 : ℕ).divisors, d := by
      rw [show (16896 : ℕ) = 1536 * 11 by norm_num,
        Nat.Coprime.sum_divisors_mul (by decide)]
      decide
    have h := h16896.mul_prime_pow (p := 31) (by norm_num) (by decide) hσ 1
    simpa using h

end Nat

/-! ## Axiom audit

`Nat.coleman_multiperfect_practical` is the single intended `sorry` and reports
`sorryAx`.  Every other declaration below rests on a subset of
`{propext, Classical.choice, Quot.sound}`.  The subset check is the sound
`native_decide` detector on this toolchain: a use would surface as a
per-declaration `*._native.native_decide.ax_*` axiom (`Lean.ofReduceBool` is never
emitted).  There is no `native_decide` in this file. -/

#print axioms Nat.Practical
#print axioms Nat.decidablePredPractical
#print axioms Nat.Practical.pos
#print axioms Nat.practical_condition_zero
#print axioms Nat.not_practical_zero
#print axioms Nat.practical_one
#print axioms Nat.practical_two
#print axioms Nat.practical_iff_exists_subset
#print axioms Nat.Practical.exists_sum_eq
#print axioms Finset.exists_subset_sum_eq_of_forall_le_one_add_sum
#print axioms Nat.Practical.divisor_le_one_add_sum
#print axioms Nat.practical_iff_forall_le_sum_divisors
#print axioms Nat.Practical.exists_sum_eq_of_le_sum_divisors
#print axioms Nat.Practical.two_dvd
#print axioms Nat.Practical.two_mul_le_one_add_sum_divisors
#print axioms Nat.exists_digits_le_mul_geom_sum
#print axioms Nat.Practical.mul_prime_pow
#print axioms Nat.practical_two_pow
#print axioms Nat.IsMultiperfect
#print axioms Nat.decidablePredIsMultiperfect
#print axioms Nat.Perfect.isMultiperfect
#print axioms Nat.coleman_multiperfect_practical
#print axioms Nat.coleman_instance_1
#print axioms Nat.coleman_instance_6
#print axioms Nat.coleman_instance_28
#print axioms Nat.coleman_instance_120
#print axioms Nat.coleman_instance_496
#print axioms Nat.coleman_instance_672
#print axioms Nat.coleman_instance_8128
#print axioms Nat.coleman_instance_30240
#print axioms Nat.coleman_instance_32760
#print axioms Nat.coleman_instance_523776
