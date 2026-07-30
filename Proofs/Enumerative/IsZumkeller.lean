import Mathlib

/-!
# Zumkeller numbers (OEIS A083207): definition, decidability, coprime closure

A positive integer `n` is a *Zumkeller number* if its divisors can be partitioned
into two disjoint sets with equal sums; the sequence begins
`6, 12, 20, 24, 28, 30, 40, 42, 48, 54, …` (OEIS A083207).

This file is the shared root of the Zumkeller family of formalizations:

* `IsZumkeller` — the predicate, with an explicit `0 < n` conjunct pinning the junk
  value `Nat.divisors 0 = ∅` (without the guard, `0` would be vacuously Zumkeller);
* a `Decidable` instance with `decide` ground-truth checks against the OEIS data;
* `isZumkeller_iff_two_mul_sum_eq_sum_divisors` — the half-`σ` characterisation;
* `IsZumkeller.mul_of_coprime` — the closure engine: a Zumkeller number times a
  positive coprime factor is again Zumkeller (cf. Rao–Peng, *On Zumkeller numbers*,
  arXiv:0912.0052; OEIS A083207 comments).
-/

set_option autoImplicit false

open Finset

/-- A natural number `n` is a **Zumkeller number** (OEIS A083207) if `0 < n` and the
divisors of `n` can be partitioned into two disjoint sets with equal sums; equivalently,
some `A ⊆ n.divisors` satisfies `∑ a ∈ A, a = ∑ d ∈ n.divisors \ A, d`.

The `0 < n` conjunct is a deliberate guard: `Nat.divisors 0 = ∅` splits as `∅ ⊔ ∅` with
equal sums (see `exists_equal_sum_partition_zero`), so without the guard `0` would be
vacuously Zumkeller, contradicting A083207. -/
def IsZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ A ∈ n.divisors.powerset, ∑ a ∈ A, a = ∑ d ∈ n.divisors \ A, d

/-- `IsZumkeller` is decidable: the existential ranges over the finite powerset of the
divisor set. -/
instance : DecidablePred IsZumkeller := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ ∃ A ∈ n.divisors.powerset,
    ∑ a ∈ A, a = ∑ d ∈ n.divisors \ A, d))

/-- A Zumkeller number is positive. -/
theorem IsZumkeller.pos {n : ℕ} (h : IsZumkeller n) : 0 < n := h.1

/-- The partition condition alone is *vacuously* satisfiable at `0`, since
`Nat.divisors 0 = ∅` splits as `∅ ⊔ ∅` with equal sums `0 = 0`.  This records why
`IsZumkeller` carries the `0 < n` guard. -/
theorem exists_equal_sum_partition_zero :
    ∃ A ∈ (Nat.divisors 0).powerset, ∑ a ∈ A, a = ∑ d ∈ Nat.divisors 0 \ A, d := by
  decide

/-- `0` is not a Zumkeller number: the positivity guard rules it out. -/
theorem not_isZumkeller_zero : ¬ IsZumkeller 0 := fun h => Nat.lt_irrefl 0 h.pos

/-- `1` is not a Zumkeller number: its divisor set `{1}` admits no equal-sum split. -/
theorem not_isZumkeller_one : ¬ IsZumkeller 1 := by decide

/-- Nontriviality: every Zumkeller number satisfies `1 < n` (in fact the least one
is `6`, but `1 < n` is the bound downstream side conditions carry). -/
theorem IsZumkeller.one_lt {n : ℕ} (h : IsZumkeller n) : 1 < n := by
  by_contra hle
  have hcases : n = 0 ∨ n = 1 := by omega
  rcases hcases with rfl | rfl
  · exact not_isZumkeller_zero h
  · exact not_isZumkeller_one h

/-- Subset form of the definition, for consumers who prefer `⊆` to powerset
membership. -/
theorem isZumkeller_iff_exists_subset (n : ℕ) :
    IsZumkeller n ↔
      0 < n ∧ ∃ A ⊆ n.divisors, ∑ a ∈ A, a = ∑ d ∈ n.divisors \ A, d := by
  constructor
  · rintro ⟨hn, A, hA, hsum⟩
    exact ⟨hn, A, Finset.mem_powerset.mp hA, hsum⟩
  · rintro ⟨hn, A, hA, hsum⟩
    exact ⟨hn, A, Finset.mem_powerset.mpr hA, hsum⟩

/-- Half-`σ` characterisation: a positive `n` is Zumkeller iff some subset of its
divisors sums to half the divisor sum.  Stated multiplicatively (`2 * ∑ = σ`) to keep
`Nat` division out of the statement. -/
theorem isZumkeller_iff_two_mul_sum_eq_sum_divisors {n : ℕ} (hn : 0 < n) :
    IsZumkeller n ↔
      ∃ A ∈ n.divisors.powerset, 2 * ∑ a ∈ A, a = ∑ d ∈ n.divisors, d := by
  constructor
  · rintro ⟨-, A, hA, hsum⟩
    have hsplit : ∑ d ∈ n.divisors \ A, d + ∑ a ∈ A, a = ∑ d ∈ n.divisors, d :=
      Finset.sum_sdiff (Finset.mem_powerset.mp hA)
    exact ⟨A, hA, by omega⟩
  · rintro ⟨A, hA, hsum⟩
    have hsplit : ∑ d ∈ n.divisors \ A, d + ∑ a ∈ A, a = ∑ d ∈ n.divisors, d :=
      Finset.sum_sdiff (Finset.mem_powerset.mp hA)
    exact ⟨hn, A, hA, by omega⟩

/-- The divisor sum of a Zumkeller number is even: an equal-sum split doubles one
side. -/
theorem IsZumkeller.two_dvd_sum_divisors {n : ℕ} (h : IsZumkeller n) :
    2 ∣ ∑ d ∈ n.divisors, d := by
  obtain ⟨A, -, hA⟩ := (isZumkeller_iff_two_mul_sum_eq_sum_divisors h.pos).mp h
  exact ⟨∑ a ∈ A, a, hA.symm⟩

/-- **Coprime closure engine** (cf. Rao–Peng, *On Zumkeller numbers*): if `m` is
Zumkeller and `m` is coprime to `n`, then `m * n` is Zumkeller.

No further side conditions: `0 < n` is derivable — at `n = 0`, `m.Coprime 0` forces
`m = 1`, which is not Zumkeller.  Coprimality makes `(d, e) ↦ d * e` inject divisor
pairs into divisors of `m * n`, so an equal-sum split of `m.divisors` scales by each
divisor of `n` into an equal-sum split of `(m * n).divisors`, using
`σ(mn) = σ(m)σ(n)`. -/
theorem IsZumkeller.mul_of_coprime {m n : ℕ} (hm : IsZumkeller m)
    (hmn : m.Coprime n) : IsZumkeller (m * n) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 : m = 1 := by simpa [Nat.Coprime] using hmn
      exact absurd (h1 ▸ hm) not_isZumkeller_one
    · exact hn
  obtain ⟨A, hA_pow, hA_half⟩ :=
    (isZumkeller_iff_two_mul_sum_eq_sum_divisors hm.pos).mp hm
  have hA : A ⊆ m.divisors := Finset.mem_powerset.mp hA_pow
  have hmn_pos : 0 < m * n := Nat.mul_pos hm.pos hn
  set B : Finset ℕ := (A ×ˢ n.divisors).image (fun p => p.1 * p.2) with hB_def
  -- checkpoint 1: `B` lands inside the divisors of `m * n`
  have hB_sub : B ⊆ (m * n).divisors := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact Nat.mem_divisors.mpr
      ⟨mul_dvd_mul (Nat.mem_divisors.mp (hA hp1)).1 (Nat.mem_divisors.mp hp2).1,
        hmn_pos.ne'⟩
  -- checkpoint 2: coprimality makes `(d, e) ↦ d * e` injective on divisor pairs
  have hinj : ∀ p ∈ A ×ˢ n.divisors, ∀ q ∈ A ×ˢ n.divisors,
      p.1 * p.2 = q.1 * q.2 → p = q := by
    rintro ⟨d₁, e₁⟩ hp ⟨d₂, e₂⟩ hq hpq
    obtain ⟨hd₁, he₁⟩ := Finset.mem_product.mp hp
    obtain ⟨hd₂, he₂⟩ := Finset.mem_product.mp hq
    have hd₁m : d₁ ∣ m := (Nat.mem_divisors.mp (hA hd₁)).1
    have hd₂m : d₂ ∣ m := (Nat.mem_divisors.mp (hA hd₂)).1
    have he₁n : e₁ ∣ n := (Nat.mem_divisors.mp he₁).1
    have he₂n : e₂ ∣ n := (Nat.mem_divisors.mp he₂).1
    have hd₁d₂ : d₁ ∣ d₂ :=
      ((hmn.coprime_dvd_left hd₁m).coprime_dvd_right he₂n).dvd_of_dvd_mul_right
        (hpq ▸ dvd_mul_right d₁ e₁)
    have hd₂d₁ : d₂ ∣ d₁ :=
      ((hmn.coprime_dvd_left hd₂m).coprime_dvd_right he₁n).dvd_of_dvd_mul_right
        (hpq.symm ▸ dvd_mul_right d₂ e₂)
    have hd : d₁ = d₂ := Nat.dvd_antisymm hd₁d₂ hd₂d₁
    have he : e₁ = e₂ := by
      have hd₁_pos : 0 < d₁ := Nat.pos_of_mem_divisors (hA hd₁)
      subst hd
      exact Nat.eq_of_mul_eq_mul_left hd₁_pos hpq
    rw [hd, he]
  -- checkpoint 3: the sum over `B` factors through the product of sums
  have hB_sum : ∑ b ∈ B, b = (∑ a ∈ A, a) * ∑ d ∈ n.divisors, d := by
    calc ∑ b ∈ B, b = ∑ p ∈ A ×ˢ n.divisors, p.1 * p.2 := by
          rw [hB_def]; exact Finset.sum_image hinj
      _ = ∑ a ∈ A, ∑ e ∈ n.divisors, a * e := Finset.sum_product _ _ _
      _ = (∑ a ∈ A, a) * ∑ d ∈ n.divisors, d := (Finset.sum_mul_sum _ _ _ _).symm
  -- assemble via the half-σ characterisation at `m * n`
  rw [isZumkeller_iff_two_mul_sum_eq_sum_divisors hmn_pos]
  refine ⟨B, Finset.mem_powerset.mpr hB_sub, ?_⟩
  calc 2 * ∑ b ∈ B, b
      = (2 * ∑ a ∈ A, a) * ∑ d ∈ n.divisors, d := by rw [hB_sum, mul_assoc]
    _ = (∑ d ∈ m.divisors, d) * ∑ d ∈ n.divisors, d := by rw [hA_half]
    _ = ∑ d ∈ (m * n).divisors, d := (hmn.sum_divisors_mul).symm

/-- Coprime closure with the Zumkeller factor on the right: if `n` is Zumkeller
and `m` is coprime to `n`, then `m * n` is Zumkeller.  As in
`IsZumkeller.mul_of_coprime`, positivity of the other factor is derivable. -/
theorem IsZumkeller.coprime_mul_left {m n : ℕ} (hn : IsZumkeller n)
    (hmn : m.Coprime n) : IsZumkeller (m * n) := by
  rw [mul_comm]
  exact hn.mul_of_coprime hmn.symm

/-!
## Ground-truth checks

The first five terms of A083207 are `6, 12, 20, 24, 28`; `decide` confirms each, plus
negative checks below `6` and at the deficient number `10`.
-/

example : IsZumkeller 6 := by decide
example : IsZumkeller 12 := by decide
example : IsZumkeller 20 := by decide
example : IsZumkeller 24 := by decide
example : IsZumkeller 28 := by decide

-- Negative checks: A083207 has no term below 6, and `10` (deficient, `σ(10) = 18`) fails.
example : ¬ IsZumkeller 0 := by decide
example : ¬ IsZumkeller 1 := by decide
example : ¬ IsZumkeller 5 := by decide
example : ¬ IsZumkeller 10 := by decide

-- Explicit witness at `6`: the split `{6} ⊔ {1, 2, 3}` has equal sums `6 = 6`.
example : ({6} : Finset ℕ) ∈ (6 : ℕ).divisors.powerset ∧
    ∑ a ∈ ({6} : Finset ℕ), a = ∑ d ∈ (6 : ℕ).divisors \ {6}, d := by decide

/-!
## Satisfiability of the closure engine

All hypotheses of `IsZumkeller.mul_of_coprime` are jointly instantiated at the concrete
pair `(m, n) = (6, 5)`; the output agrees with the direct decision procedure at
`30 ∈ A083207`.  The pair `(6, 35)` then reaches `210 ∈ A083207`, whose 16-divisor
search space is beyond comfortable kernel `decide`.
-/

example : IsZumkeller 30 := by
  have h : IsZumkeller (6 * 5) :=
    IsZumkeller.mul_of_coprime (m := 6) (n := 5) (by decide) (by decide)
  simpa using h

-- direct cross-check of the same value, independent of the engine
example : IsZumkeller 30 := by decide

example : IsZumkeller 210 := by
  have h : IsZumkeller (6 * 35) :=
    IsZumkeller.mul_of_coprime (m := 6) (n := 35) (by decide) (by decide)
  simpa using h
