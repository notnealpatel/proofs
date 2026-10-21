/-
# Strict greedy 2-sumfree sequences: the `f = 1` column, `S_{1,2m}` in closed form

## Source

Daan van Berkel and Wieb Bosma, *Periodicity conjectures for all 2-sumfree
sequences*, arXiv:2609.18522 (retrieved and read 2026-10-21).

* Section 1 defines the strict greedy 2-sumfree sequence, verbatim: "initialize
  the first two values `s_0=f≥1` and `s_1=g>f`, and once the first `k≥2` values
  `s_0, s_1, ⋯, s_{k-1}` are defined, let `s_k` be the smallest integer greater
  than `s_{k-1}` that is not equal to the sum of 2 different previous elements
  in the sequence."
* Conjecture 1.1 (`conj:main`), verbatim: "Every 2-sumfree sequence is
  eventually periodic."  The paper says "We have not been able to establish the
  truth of this conjecture"; it proves it only for `g ≤ 2f` (Theorem 5.1, from
  van Berkel–Bosma, and the new Theorem 5.2 for `g = 2f`, `f ≥ 3`).
* Sections 2–3 (`conj:per`, `conj:pre`, with the special `f = 1` modifications
  of `𝓛_1` and `𝒦_1`) conjecture the period and preperiod lengths.  For `f = 1`
  these predict, for `d = g - 1` odd and `≥ 7` (i.e. `g = 2m`, `m ≥ 4`), period
  length `d + 4 = 2m + 3` and preperiod length `(d + 7)/2 = m + 3` (in numbers
  of terms).  The paper gives no proof for the `f = 1` column.

## Claim formalized here (the `f = 1` column)

For `m ≥ 4`, with `N = 8m + 3` and
`R = {1, 3} ∪ {even r : 2m ≤ r ≤ 4m - 2} ∪ {odd r : 4m + 5 ≤ r ≤ 6m + 1} ∪ {8m, 8m + 2}`:

  `S_{1,2m} = {1} ∪ {even x : 2m ≤ x ≤ 4m} ∪ {4m + 3} ∪ {x ≥ 4m + 4 : x mod N ∈ R}`

(`eq_T1_of_isGS`).  Consequences proved: the characteristic sequence is periodic
with period `N` from `4m + 4` on (`eventually_periodic_one_two_mul`), not from
`4m + 3` (`not_periodic_at_four_mul_add_three`), `N` is the least eventual
period (`exists_mem_add_not_mem`), a period contains `2m + 3` terms
(`ncard_inter_Ico`) and the preperiod `m + 3` terms (`ncard_inter_Iio`).
The remaining members of the column are also settled: odd `g ≥ 3`
(`S_{1,g} = {1} ∪ {odd x ≥ g}`, `eq_Todd_of_isGS`) and `g = 2, 4, 6`
(`eq_T2_of_isGS`, `eq_T4_of_isGS`, `eq_T6_of_isGS`).  The greedy sequence is
modelled by its set of terms, characterized by the fixpoint `IsGS`; uniqueness
is `IsGS.unique`, and `mem_gsBelow_iff` ties it to the literal greedy
computation `gsBelow`.

## Status

Open in the source (conjectural special case; the closed form for `g = 2m` was
found computationally by the triage).  Kernel-checked here with no `sorry`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.TwoSumfreeFOneColumn

/-! ## The greedy 2-sumfree sequence -/

/-- `IsGS f g S` says that `S` is the set of terms of the strict greedy
2-sumfree sequence `S_{f,g}` of van Berkel–Bosma: `x ∈ S` iff `x = f`, or
`x = g`, or `x > g` and `x` is not the sum of two distinct elements of `S`.
(Such summands are automatically smaller than `x`, so this is exactly the greedy
rule "the next term is the least integer above the previous one that is not a
sum of two distinct earlier terms".) -/
def IsGS (f g : ℕ) (S : Set ℕ) : Prop :=
  ∀ x, x ∈ S ↔ (x = f ∨ x = g ∨ (g < x ∧ ¬ ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a + b = x))

/-- The terms of the greedy sequence `S_{f,g}` that are smaller than `n`, in
increasing order, computed literally by the greedy rule. -/
def gsBelow (f g : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    if n = f ∨ n = g ∨ (g < n ∧ ¬ ∃ a ∈ gsBelow f g n, ∃ b ∈ gsBelow f g n, a < b ∧ a + b = n)
    then gsBelow f g n ++ [n] else gsBelow f g n

/-- Paper, Section 1: the first 26 terms of `S_{3,7}`. -/
example : gsBelow 3 7 79 = [3, 7, 8, 9, 13, 14, 18, 19, 24, 29, 30, 34, 35, 40, 45, 46, 50,
    51, 56, 61, 62, 66, 67, 72, 77, 78] := by decide +kernel

/-- Paper, Example before Theorem 5.2: `S_{1,2} = (1, 2, 4, 7, 10, 13, 16, 19, 22, …)`. -/
example : gsBelow 1 2 23 = [1, 2, 4, 7, 10, 13, 16, 19, 22] := by decide +kernel

/-- OEIS A003662 (`a(1) = 1`, `a(2) = 4`), first terms. -/
example : gsBelow 1 4 60 = [1, 4, 6, 8, 11, 13, 16, 18, 23, 25, 28, 30, 35, 37, 40, 42, 47, 49,
    52, 54, 59] := by decide +kernel

/-- OEIS A003663 (`a(1) = 1`, `a(2) = 6`), first terms. -/
example : gsBelow 1 6 61 = [1, 6, 8, 10, 12, 15, 17, 19, 24, 26, 28, 33, 35, 37, 42, 44, 46,
    51, 53, 55, 60] := by decide +kernel

/-- Uniqueness of the greedy set: for `0 < f < g` there is at most one `S` with
`IsGS f g S`. -/
theorem IsGS.unique {f g : ℕ} (hf : 0 < f) (hfg : f < g) {S S' : Set ℕ}
    (hS : IsGS f g S) (hS' : IsGS f g S') : S = S' := by
  have hpos : ∀ {T : Set ℕ}, IsGS f g T → ∀ a ∈ T, 0 < a := by
    intro T hT a ha
    rcases (hT a).1 ha with h | h | h <;> omega
  ext x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [hS x, hS' x]
    have hsum : (∃ a ∈ S, ∃ b ∈ S, a < b ∧ a + b = x) ↔
        (∃ a ∈ S', ∃ b ∈ S', a < b ∧ a + b = x) := by
      constructor
      · rintro ⟨a, ha, b, hb, hab, rfl⟩
        have ha0 := hpos hS a ha
        exact ⟨a, (ih a (by omega)).1 ha, b, (ih b (by omega)).1 hb, hab, rfl⟩
      · rintro ⟨a, ha, b, hb, hab, rfl⟩
        have ha0 := hpos hS' a ha
        exact ⟨a, (ih a (by omega)).2 ha, b, (ih b (by omega)).2 hb, hab, rfl⟩
    rw [hsum]

/-- The computed list `gsBelow f g n` consists exactly of the elements of the
greedy set `S` below `n`. -/
theorem mem_gsBelow_iff {f g : ℕ} (hf : 0 < f) (hfg : f < g) {S : Set ℕ} (hS : IsGS f g S)
    (n x : ℕ) : x ∈ gsBelow f g n ↔ x < n ∧ x ∈ S := by
  have hpos : ∀ a ∈ S, 0 < a := by
    intro a ha
    rcases (hS a).1 ha with h | h | h <;> omega
  induction n generalizing x with
  | zero => simp [gsBelow]
  | succ n ih =>
    have hstep : (n = f ∨ n = g ∨
        (g < n ∧ ¬ ∃ a ∈ gsBelow f g n, ∃ b ∈ gsBelow f g n, a < b ∧ a + b = n)) ↔ n ∈ S := by
      rw [hS n]
      have hsum : (∃ a ∈ gsBelow f g n, ∃ b ∈ gsBelow f g n, a < b ∧ a + b = n) ↔
          (∃ a ∈ S, ∃ b ∈ S, a < b ∧ a + b = n) := by
        constructor
        · rintro ⟨a, ha, b, hb, hab, hsum⟩
          exact ⟨a, ((ih a).1 ha).2, b, ((ih b).1 hb).2, hab, hsum⟩
        · rintro ⟨a, ha, b, hb, hab, hsum⟩
          have ha0 := hpos a ha
          exact ⟨a, (ih a).2 ⟨by omega, ha⟩, b, (ih b).2 ⟨by omega, hb⟩, hab, hsum⟩
      rw [hsum]
    simp only [gsBelow]
    split_ifs with h
    · simp only [List.mem_append, ih, List.mem_singleton]
      have hn := hstep.1 h
      constructor
      · rintro (⟨hx, hxS⟩ | rfl)
        · exact ⟨by omega, hxS⟩
        · exact ⟨by omega, hn⟩
      · rintro ⟨hx, hxS⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
        · exact Or.inl ⟨hx, hxS⟩
        · exact Or.inr hx
    · simp only [ih]
      have hn : n ∉ S := fun hn => h (hstep.2 hn)
      constructor
      · rintro ⟨hx, hxS⟩
        exact ⟨by omega, hxS⟩
      · rintro ⟨hx, hxS⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
        · exact ⟨hx, hxS⟩
        · exact absurd hxS hn

/-! ## The closed form for `g = 2m` -/

/-- The residue set `R` modulo `N = 8m + 3`:
`{1, 3} ∪ {even r : 2m ≤ r ≤ 4m - 2} ∪ {odd r : 4m + 5 ≤ r ≤ 6m + 1} ∪ {8m, 8m + 2}`
(the bound `r ≤ 4m - 2` is written `r + 2 ≤ 4m` to avoid truncated subtraction). -/
def R1 (m r : ℕ) : Prop :=
  r = 1 ∨ r = 3 ∨ (Even r ∧ 2 * m ≤ r ∧ r + 2 ≤ 4 * m) ∨
    (Odd r ∧ 4 * m + 5 ≤ r ∧ r ≤ 6 * m + 1) ∨ r = 8 * m ∨ r = 8 * m + 2

/-- The conjectured closed form of `S_{1,2m}`:
`{1} ∪ {even x : 2m ≤ x ≤ 4m} ∪ {4m + 3} ∪ {x ≥ 4m + 4 : x mod (8m + 3) ∈ R}`. -/
def T1 (m : ℕ) : Set ℕ :=
  {x | x = 1 ∨ (Even x ∧ 2 * m ≤ x ∧ x ≤ 4 * m) ∨ x = 4 * m + 3 ∨
    (4 * m + 4 ≤ x ∧ R1 m (x % (8 * m + 3)))}

/-- Membership in `T1 m` is decidable. -/
instance (m : ℕ) : DecidablePred (· ∈ T1 m) := fun x => by
  unfold T1 R1
  infer_instance

/-- Ground truth: `T1 4` agrees with the greedy sequence `S_{1,8}` below `81`. -/
example : (List.range 81).filter (· ∈ T1 4) = gsBelow 1 8 81 := by decide +kernel

/-- Ground truth: `T1 5` agrees with the greedy sequence `S_{1,10}` below `130`. -/
example : (List.range 130).filter (· ∈ T1 5) = gsBelow 1 10 130 := by decide +kernel

/-- Residues allowed in the first block `[0, 8m + 3)`. -/
def R0 (m r : ℕ) : Prop :=
  r = 1 ∨ (Even r ∧ 2 * m ≤ r ∧ r ≤ 4 * m) ∨ r = 4 * m + 3 ∨ (4 * m + 4 ≤ r ∧ R1 m r)

/-- Membership of `N q + r` in `T1 m`, expressed through block index `q` and
residue `r`. -/
def MemQR (m q r : ℕ) : Prop := (q = 0 ∧ R0 m r) ∨ (1 ≤ q ∧ R1 m r)

/-- `x = N q + r` with `r < N` is in `T1 m` iff `MemQR m q r`. -/
theorem mem_T1_iff_of_eq {m x q r : ℕ} (hm : 1 ≤ m) (h : x = (8 * m + 3) * q + r)
    (hr : r < 8 * m + 3) :
    x ∈ T1 m ↔ MemQR m q r := by
  have hmod : x % (8 * m + 3) = r := by
    rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  simp only [T1, Set.mem_ofPred_eq]
  rw [hmod]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have hx : x = r := by simpa using h
    subst hx
    unfold MemQR R0
    constructor
    · intro hmem
      exact Or.inl ⟨rfl, hmem⟩
    · rintro (⟨-, hmem⟩ | ⟨hq, -⟩)
      · exact hmem
      · omega
  · have hN : 8 * m + 3 ≤ (8 * m + 3) * q := Nat.le_mul_of_pos_right _ hq
    have hxN : 8 * m + 3 ≤ x := by omega
    unfold MemQR
    constructor
    · rintro (hx | ⟨-, -, hx⟩ | hx | ⟨-, hR⟩)
      · omega
      · omega
      · omega
      · exact Or.inr ⟨hq, hR⟩
    · rintro (⟨hq0, -⟩ | ⟨-, hR⟩)
      · omega
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, hR⟩))

/-- Residue-level sum-freeness: no two distinct elements of `T1 m` (written as
`N q + r`) add up to a third, where the block indices and residues of the sum
are related by the carry. -/
theorem memQR_sum_false (m qa ra qb rb qx rx : ℕ) (hm : 4 ≤ m)
    (hra : ra < 8 * m + 3) (hrb : rb < 8 * m + 3) (hrx : rx < 8 * m + 3)
    (hsum : (qx = qa + qb ∧ ra + rb = rx) ∨ (qx = qa + qb + 1 ∧ ra + rb = rx + (8 * m + 3)))
    (hne : qa ≠ qb ∨ ra ≠ rb)
    (ha : MemQR m qa ra) (hb : MemQR m qb rb) (hx : MemQR m qx rx) : False := by
  simp only [MemQR, R0, R1, Nat.even_iff, Nat.odd_iff] at ha hb hx
  rcases hsum with ⟨hq, hr⟩ | ⟨hq, hr⟩
  · omega
  · omega

/-- Unfold the residue predicates to linear arithmetic with parities and close by `omega`. -/
local macro "memqr_tac" : tactic =>
  `(tactic| (simp only [MemQR, R0, R1, Nat.even_iff, Nat.odd_iff, true_and, and_true, true_or,
    or_true]
    <;> omega))

/-- Sum-freeness of the closed form: for `m ≥ 4`, the sum of two distinct
elements of `T1 m` is never in `T1 m`. -/
theorem add_not_mem_T1 {m : ℕ} (hm : 4 ≤ m) {a b : ℕ} (ha : a ∈ T1 m) (hb : b ∈ T1 m)
    (hab : a ≠ b) : a + b ∉ T1 m := by
  intro hx
  have hN : 0 < 8 * m + 3 := by omega
  obtain ⟨qa, ra, hra, da⟩ : ∃ q r, r < 8 * m + 3 ∧ a = (8 * m + 3) * q + r :=
    ⟨a / (8 * m + 3), a % (8 * m + 3), Nat.mod_lt _ hN, (Nat.div_add_mod _ _).symm⟩
  obtain ⟨qb, rb, hrb, db⟩ : ∃ q r, r < 8 * m + 3 ∧ b = (8 * m + 3) * q + r :=
    ⟨b / (8 * m + 3), b % (8 * m + 3), Nat.mod_lt _ hN, (Nat.div_add_mod _ _).symm⟩
  have hsum : ∃ qx rx, rx < 8 * m + 3 ∧ a + b = (8 * m + 3) * qx + rx ∧
      ((qx = qa + qb ∧ ra + rb = rx) ∨ (qx = qa + qb + 1 ∧ ra + rb = rx + (8 * m + 3))) := by
    by_cases hc : ra + rb < 8 * m + 3
    · refine ⟨qa + qb, ra + rb, hc, ?_, Or.inl ⟨rfl, rfl⟩⟩
      rw [da, db]
      ring
    · refine ⟨qa + qb + 1, ra + rb - (8 * m + 3), by omega, ?_, Or.inr ⟨rfl, by omega⟩⟩
      have hmul : (8 * m + 3) * (qa + qb + 1) =
          (8 * m + 3) * qa + (8 * m + 3) * qb + (8 * m + 3) := by ring
      rw [hmul, da, db]
      omega
  obtain ⟨qx, rx, hrx, dx, hqr⟩ := hsum
  have hne : qa ≠ qb ∨ ra ≠ rb := by
    by_contra hcon
    push Not at hcon
    apply hab
    rw [da, db, hcon.1, hcon.2]
  exact memQR_sum_false m qa ra qb rb qx rx hm hra hrb hrx hqr hne
    ((mem_T1_iff_of_eq (by omega) da hra).1 ha) ((mem_T1_iff_of_eq (by omega) db hrb).1 hb)
    ((mem_T1_iff_of_eq (by omega) dx hrx).1 hx)

/-- Completeness witness without carry: if `x = N q + r`, `a ≤ r` is a
first-block element and `N q + (r - a)` is in `T1 m`, then `x` is a sum of two
distinct elements of `T1 m`. -/
theorem exists_sum_same {m x q r a : ℕ} (hm : 1 ≤ m) (hx : x = (8 * m + 3) * q + r)
    (hr : r < 8 * m + 3) (ha : MemQR m 0 a) (har : a ≤ r) (hb : MemQR m q (r - a))
    (hne : 1 ≤ q ∨ a + a ≠ r) :
    ∃ a ∈ T1 m, ∃ b ∈ T1 m, a ≠ b ∧ a + b = x := by
  have hqN : q = 0 ∨ 8 * m + 3 ≤ (8 * m + 3) * q := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · exact Or.inl hq
    · exact Or.inr (Nat.le_mul_of_pos_right _ hq)
  have hq0 : q = 0 → (8 * m + 3) * q = 0 := by
    rintro rfl
    simp
  refine ⟨a, (mem_T1_iff_of_eq hm (by simp) (by omega)).2 ha, x - a,
    (mem_T1_iff_of_eq hm (by omega) (by omega)).2 hb, ?_, by omega⟩
  omega

/-- Completeness witness with carry: if `x = N (q + 1) + r`, `r < a` is a
first-block element and `N q + (r + N - a)` is in `T1 m`, then `x` is a sum of
two distinct elements of `T1 m`. -/
theorem exists_sum_borrow {m x q r a : ℕ} (hm : 1 ≤ m) (hx : x = (8 * m + 3) * (q + 1) + r)
    (ha : MemQR m 0 a) (haN : a < 8 * m + 3) (har : r < a)
    (hb : MemQR m q (r + (8 * m + 3) - a)) (hne : 1 ≤ q ∨ a + a ≠ r + (8 * m + 3)) :
    ∃ a ∈ T1 m, ∃ b ∈ T1 m, a ≠ b ∧ a + b = x := by
  have hmul : (8 * m + 3) * (q + 1) = (8 * m + 3) * q + (8 * m + 3) := by ring
  have hqN : q = 0 ∨ 8 * m + 3 ≤ (8 * m + 3) * q := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · exact Or.inl hq
    · exact Or.inr (Nat.le_mul_of_pos_right _ hq)
  have hq0 : q = 0 → (8 * m + 3) * q = 0 := by
    rintro rfl
    simp
  refine ⟨a, (mem_T1_iff_of_eq hm (by simp) haN).2 ha, x - a,
    (mem_T1_iff_of_eq hm (q := q) (r := r + (8 * m + 3) - a) (by omega) (by omega)).2 hb, ?_,
    by omega⟩
  omega

/-- Completeness of the closed form: for `m ≥ 4`, every `x > 2m` outside
`T1 m` is a sum of two distinct elements of `T1 m`. -/
theorem exists_sum_of_not_mem_T1 {m x : ℕ} (hm : 4 ≤ m) (hx : x ∉ T1 m) (hgx : 2 * m < x) :
    ∃ a ∈ T1 m, ∃ b ∈ T1 m, a ≠ b ∧ a + b = x := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨q, r, hr, dx⟩ : ∃ q r, r < 8 * m + 3 ∧ x = (8 * m + 3) * q + r :=
    ⟨x / (8 * m + 3), x % (8 * m + 3), Nat.mod_lt _ (by omega), (Nat.div_add_mod _ _).symm⟩
  have hxm : ¬ MemQR m q r := fun h => hx ((mem_T1_iff_of_eq hm1 dx hr).2 h)
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have hxr : x = r := by simpa using dx
    simp only [MemQR, R0, R1, Nat.even_iff, Nat.odd_iff, true_and] at hxm
    rcases (by omega : (r % 2 = 1 ∧ 2 * m + 1 ≤ r ∧ r + 1 ≤ 4 * m) ∨ r = 4 * m + 1 ∨
        (r % 2 = 0 ∧ 4 * m + 6 ≤ r ∧ r ≤ 6 * m) ∨ r = 4 * m + 2 ∨ r = 4 * m + 4 ∨
        (r % 2 = 1 ∧ 6 * m + 3 ≤ r ∧ r ≤ 8 * m + 1) ∨
        (r % 2 = 0 ∧ 6 * m + 2 ≤ r ∧ r + 2 ≤ 8 * m)) with h | h | h | h | h | h | h
    · exact exists_sum_same (a := 1) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 1) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 1) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 2 * m) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 2 * m) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 4 * m + 3) hm1 dx hr (by memqr_tac) (by omega)
        (by memqr_tac) (by omega)
    · exact exists_sum_same (a := 4 * m) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
  · obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hq1 : 1 ≤ q + 1 := by omega
    simp only [MemQR, R0, R1, Nat.even_iff, Nat.odd_iff] at hxm
    rcases (by omega : (r % 2 = 0 ∧ r + 2 ≤ 2 * m) ∨ (r % 2 = 1 ∧ 5 ≤ r ∧ r + 1 ≤ 2 * m) ∨
        (r % 2 = 1 ∧ 2 * m + 1 ≤ r ∧ r + 1 ≤ 4 * m) ∨ r = 4 * m ∨ r = 4 * m + 1 ∨
        r = 4 * m + 2 ∨ r = 4 * m + 3 ∨ r = 4 * m + 4 ∨
        (r % 2 = 0 ∧ 4 * m + 6 ≤ r ∧ r ≤ 6 * m) ∨
        (r % 2 = 1 ∧ 6 * m + 3 ≤ r ∧ r ≤ 8 * m + 1) ∨
        (r % 2 = 0 ∧ 6 * m + 2 ≤ r ∧ r + 2 ≤ 8 * m)) with
        h | h | h | h | h | h | h | h | h | h | h
    · exact exists_sum_borrow (a := 2 * m + 2 + r) hm1 dx (by memqr_tac) (by omega)
        (by omega) (by memqr_tac) (by omega)
    · exact exists_sum_borrow (a := 4 * m + 3) hm1 dx (by memqr_tac) (by omega)
        (by omega) (by memqr_tac) (by omega)
    · exact exists_sum_same (a := 1) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 2 * m) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 4 * m - 2) hm1 dx hr (by memqr_tac) (by omega)
        (by memqr_tac) (by omega)
    · exact exists_sum_same (a := 2 * m) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 4 * m) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 2 * m) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 1) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)
    · exact exists_sum_same (a := 4 * m + 3) hm1 dx hr (by memqr_tac) (by omega)
        (by memqr_tac) (by omega)
    · exact exists_sum_same (a := 4 * m) hm1 dx hr (by memqr_tac) (by omega) (by memqr_tac)
        (by omega)

/-- Every element of `T1 m` other than `1` and `2m` exceeds `2m`. -/
theorem lt_of_mem_T1 {m x : ℕ} (hx : x ∈ T1 m) (h1 : x ≠ 1) (h2 : x ≠ 2 * m) : 2 * m < x := by
  simp only [T1, Set.mem_ofPred_eq] at hx
  rcases hx with hx | ⟨-, hx, -⟩ | hx | ⟨hx, -⟩ <;> omega

/-- **The closed form satisfies the greedy rule.** For `m ≥ 4`, `T1 m` is the
greedy strict 2-sumfree set with initial terms `1, 2m`. -/
theorem isGS_T1 {m : ℕ} (hm : 4 ≤ m) : IsGS 1 (2 * m) (T1 m) := by
  intro x
  constructor
  · intro hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    by_cases h2 : x = 2 * m
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ⟨lt_of_mem_T1 hx h1 h2, ?_⟩)
    rintro ⟨a, ha, b, hb, hab, hsum⟩
    exact add_not_mem_T1 hm ha hb hab.ne (hsum ▸ hx)
  · rintro (rfl | rfl | ⟨hgx, hns⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨even_two_mul m, le_rfl, by omega⟩)
    · by_contra hx
      obtain ⟨a, ha, b, hb, hne, hsum⟩ := exists_sum_of_not_mem_T1 hm hx hgx
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact hns ⟨a, ha, b, hb, hlt, hsum⟩
      · exact hns ⟨b, hb, a, ha, hlt, by omega⟩

/-- **Closed form of `S_{1,2m}` (`m ≥ 4`).** If `S` is the set of terms of the
strict greedy 2-sumfree sequence with `s_0 = 1`, `s_1 = 2m`, then
`S = {1} ∪ {even x : 2m ≤ x ≤ 4m} ∪ {4m + 3} ∪ {x ≥ 4m + 4 : x mod (8m + 3) ∈ R}`.
This is the `f = 1`, even-`g` case of van Berkel–Bosma's Conjecture 1.1
(arXiv:2609.18522), in the explicit form found by computation; the paper does
not prove it. -/
theorem eq_T1_of_isGS {m : ℕ} (hm : 4 ≤ m) {S : Set ℕ} (hS : IsGS 1 (2 * m) S) : S = T1 m :=
  IsGS.unique Nat.one_pos (by omega) hS (isGS_T1 hm)

/-- The literal greedy computation `gsBelow 1 (2m) n` lists exactly the elements of
the closed form `T1 m` below `n`, for every `n` and every `m ≥ 4`. -/
theorem mem_gsBelow_one_two_mul_iff {m : ℕ} (hm : 4 ≤ m) (n x : ℕ) :
    x ∈ gsBelow 1 (2 * m) n ↔ x < n ∧ x ∈ T1 m :=
  mem_gsBelow_iff Nat.one_pos (by omega) (isGS_T1 hm) n x

/-- Satisfiability of the hypotheses of `eq_T1_of_isGS` at `m = 4`. -/
example : IsGS 1 (2 * 4) (T1 4) := isGS_T1 le_rfl

/-- Periodicity of the closed form: from `4m + 4` on, membership in `T1 m` is
periodic with period `8m + 3`. -/
theorem add_period_mem_T1_iff {m x : ℕ} (hm : 1 ≤ m) (hx : 4 * m + 4 ≤ x) :
    x + (8 * m + 3) ∈ T1 m ↔ x ∈ T1 m := by
  simp only [T1, Set.mem_ofPred_eq, Nat.add_mod_right]
  constructor
  · rintro (h | ⟨-, -, h⟩ | h | ⟨-, hR⟩)
    · omega
    · omega
    · omega
    · exact Or.inr (Or.inr (Or.inr ⟨hx, hR⟩))
  · rintro (h | ⟨-, -, h⟩ | h | ⟨-, hR⟩)
    · omega
    · omega
    · omega
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, hR⟩))

/-- **Conjecture 1.1 for `S_{1,2m}`, `m ≥ 4` (eventual periodicity).** The
characteristic sequence of `S_{1,2m}` is periodic with period `8m + 3` from
`4m + 4` on. -/
theorem eventually_periodic_one_two_mul {m : ℕ} (hm : 4 ≤ m) {S : Set ℕ}
    (hS : IsGS 1 (2 * m) S) (x : ℕ) (hx : 4 * m + 4 ≤ x) :
    x + (8 * m + 3) ∈ S ↔ x ∈ S := by
  rw [eq_T1_of_isGS hm hS]
  exact add_period_mem_T1_iff (by omega) hx

/-- The periodic regime does not start earlier than `4m + 4`: `4m + 3 ∈ S_{1,2m}`
but `4m + 3 + (8m + 3) ∉ S_{1,2m}`. -/
theorem not_periodic_at_four_mul_add_three {m : ℕ} (hm : 4 ≤ m) {S : Set ℕ}
    (hS : IsGS 1 (2 * m) S) :
    4 * m + 3 ∈ S ∧ 4 * m + 3 + (8 * m + 3) ∉ S := by
  rw [eq_T1_of_isGS hm hS]
  refine ⟨Or.inr (Or.inr (Or.inl rfl)), ?_⟩
  rw [mem_T1_iff_of_eq (q := 1) (r := 4 * m + 3) (by omega) (by ring) (by omega)]
  memqr_tac

/-- A remainder below `2N` either is the number itself or loses exactly one `N`. -/
theorem mod_eq_or_add_eq {a n : ℕ} (h : a < 2 * n) : a % n = a ∨ a % n + n = a := by
  rcases Nat.lt_or_ge a n with h1 | h1
  · exact Or.inl (Nat.mod_eq_of_lt h1)
  · right
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    omega

/-- No nonzero shift `0 < p < 8m + 3` preserves the residue set `R`: one of the
residues `3, 2m, 4m - 2` is moved outside `R`. -/
theorem exists_R1_not_R1_shift {m p : ℕ} (hm : 4 ≤ m) (hp : 0 < p) (hpN : p < 8 * m + 3) :
    ∃ r, r < 8 * m + 3 ∧ R1 m r ∧ ¬ R1 m ((r + p) % (8 * m + 3)) := by
  by_contra h
  push Not at h
  have h1 := h 3 (by omega) (Or.inr (Or.inl rfl))
  have h2 := h (2 * m) (by omega) (Or.inr (Or.inr (Or.inl ⟨even_two_mul m, le_rfl, by omega⟩)))
  have h3 := h (4 * m - 2) (by omega)
    (Or.inr (Or.inr (Or.inl ⟨⟨2 * m - 1, by omega⟩, by omega, by omega⟩)))
  have e1 := mod_eq_or_add_eq (a := 3 + p) (n := 8 * m + 3) (by omega)
  have e2 := mod_eq_or_add_eq (a := 2 * m + p) (n := 8 * m + 3) (by omega)
  have e3 := mod_eq_or_add_eq (a := 4 * m - 2 + p) (n := 8 * m + 3) (by omega)
  simp only [R1, Nat.even_iff, Nat.odd_iff] at h1 h2 h3
  omega

/-- **Minimality of the period `8m + 3`.** For `m ≥ 4` and every shift
`0 < p < 8m + 3`, the characteristic sequence of `S_{1,2m}` is not eventually
`p`-periodic: beyond every bound `K` there is `x ∈ S_{1,2m}` with
`x + p ∉ S_{1,2m}`. -/
theorem exists_mem_add_not_mem {m : ℕ} (hm : 4 ≤ m) {S : Set ℕ} (hS : IsGS 1 (2 * m) S)
    {p : ℕ} (hp : 0 < p) (hpN : p < 8 * m + 3) (K : ℕ) :
    ∃ x, K ≤ x ∧ x ∈ S ∧ x + p ∉ S := by
  rw [eq_T1_of_isGS hm hS]
  obtain ⟨r, hr, hR, hnR⟩ := exists_R1_not_R1_shift hm hp hpN
  have hK : K + 1 ≤ (8 * m + 3) * (K + 1) := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨(8 * m + 3) * (K + 1) + r, by omega,
    (mem_T1_iff_of_eq (by omega) rfl hr).2 (Or.inr ⟨by omega, hR⟩), ?_⟩
  have hs := mod_eq_or_add_eq (a := r + p) (n := 8 * m + 3) (by omega)
  rcases hs with hs | hs
  · rw [mem_T1_iff_of_eq (q := K + 1) (r := (r + p) % (8 * m + 3)) (by omega) (by omega)
      (Nat.mod_lt _ (by omega))]
    rintro (⟨hq, -⟩ | ⟨-, hR'⟩)
    · omega
    · exact hnR hR'
  · have hmul : (8 * m + 3) * (K + 2) = (8 * m + 3) * (K + 1) + (8 * m + 3) := by ring
    rw [mem_T1_iff_of_eq (q := K + 2) (r := (r + p) % (8 * m + 3)) (by omega) (by omega)
      (Nat.mod_lt _ (by omega))]
    rintro (⟨hq, -⟩ | ⟨-, hR'⟩)
    · omega
    · exact hnR hR'

/-- An arithmetic progression `c, c + d, …, c + (n - 1) d` with `0 < d` has `n`
terms. -/
theorem card_image_affine (c d n : ℕ) (hd : 0 < d) :
    ((Finset.range n).image (fun i => c + d * i)).card = n := by
  rw [Finset.card_image_of_injective _ (fun i j hij => by
    simpa [hd.ne'] using hij), Finset.card_range]

/-- **Preperiod count.** For `m ≥ 4`, `S_{1,2m}` has exactly `m + 3` terms below
`4m + 4` (namely `1`, the even numbers `2m, …, 4m`, and `4m + 3`). -/
theorem ncard_inter_Iio {m : ℕ} (hm : 4 ≤ m) {S : Set ℕ} (hS : IsGS 1 (2 * m) S) :
    (S ∩ Set.Iio (4 * m + 4)).ncard = m + 3 := by
  rw [eq_T1_of_isGS hm hS]
  have hset : T1 m ∩ Set.Iio (4 * m + 4) =
      ↑((Finset.range 2).image (fun i => 1 + (4 * m + 2) * i) ∪
        (Finset.range (m + 1)).image (fun i => 2 * m + 2 * i)) := by
    ext x
    simp only [T1, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, Finset.coe_union,
      Finset.coe_image, Finset.coe_range, Set.mem_union, Set.mem_image, Set.mem_Iio,
      Nat.even_iff]
    constructor
    · rintro ⟨hx | hx | hx | hx, hlt⟩
      · exact Or.inl ⟨0, by omega, by omega⟩
      · exact Or.inr ⟨(x - 2 * m) / 2, by omega, by omega⟩
      · exact Or.inl ⟨1, by omega, by omega⟩
      · omega
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · interval_cases i <;> omega
      · constructor
        · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
        · omega
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint, card_image_affine _ _ _ (by omega),
    card_image_affine _ _ _ (by omega)]
  · omega
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_range]
    rintro x ⟨i, hi, rfl⟩ ⟨j, hj, hij⟩
    interval_cases i <;> omega

/-- **Period count.** For `m ≥ 4`, `S_{1,2m}` has exactly `2m + 3` terms in the
first full period `[4m + 4, 12m + 7)` (length `8m + 3`); by
`eventually_periodic_one_two_mul` every later window of length `8m + 3` starting
at or after `4m + 4` is a translate of this one. -/
theorem ncard_inter_Ico {m : ℕ} (hm : 4 ≤ m) {S : Set ℕ} (hS : IsGS 1 (2 * m) S) :
    (S ∩ Set.Ico (4 * m + 4) (12 * m + 7)).ncard = 2 * m + 3 := by
  rw [eq_T1_of_isGS hm hS]
  have hset : T1 m ∩ Set.Ico (4 * m + 4) (12 * m + 7) =
      ↑((Finset.range 4).image (fun i => 8 * m + 2 * i) ∪
        (Finset.range (m - 1)).image (fun i => 4 * m + 5 + 2 * i) ∪
        (Finset.range m).image (fun i => 10 * m + 3 + 2 * i)) := by
    ext x
    rw [Set.mem_inter_iff, Set.mem_Ico]
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨hx, hlo, hhi⟩
      rcases Nat.lt_or_ge x (8 * m + 3) with hxN | hxN
      · rw [mem_T1_iff_of_eq (q := 0) (r := x) (by omega) (by simp) hxN] at hx
        simp only [MemQR, R0, R1, Nat.even_iff, Nat.odd_iff] at hx
        rcases (by omega : x = 8 * m ∨ x = 8 * m + 2 ∨ (x % 2 = 1 ∧ 4 * m + 5 ≤ x ∧
            x ≤ 6 * m + 1)) with h | h | h
        · exact Or.inl (Or.inl ⟨0, by omega, by omega⟩)
        · exact Or.inl (Or.inl ⟨1, by omega, by omega⟩)
        · exact Or.inl (Or.inr ⟨(x - 4 * m - 5) / 2, by omega, by omega⟩)
      · rw [mem_T1_iff_of_eq (q := 1) (r := x - (8 * m + 3)) (by omega) (by omega)
          (by omega)] at hx
        simp only [MemQR, R0, R1, Nat.even_iff, Nat.odd_iff] at hx
        rcases (by omega : x = 8 * m + 4 ∨ x = 8 * m + 6 ∨ ((x - (8 * m + 3)) % 2 = 0 ∧
            2 * m ≤ x - (8 * m + 3) ∧ x - (8 * m + 3) + 2 ≤ 4 * m)) with h | h | h
        · exact Or.inl (Or.inl ⟨2, by omega, by omega⟩)
        · exact Or.inl (Or.inl ⟨3, by omega, by omega⟩)
        · exact Or.inr ⟨(x - 10 * m - 3) / 2, by omega, by omega⟩
    · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
      · refine ⟨?_, by omega, by omega⟩
        interval_cases i
        · rw [mem_T1_iff_of_eq (q := 0) (r := 8 * m + 2 * 0) (by omega) (by simp) (by omega)]
          memqr_tac
        · rw [mem_T1_iff_of_eq (q := 0) (r := 8 * m + 2 * 1) (by omega) (by simp) (by omega)]
          memqr_tac
        · rw [mem_T1_iff_of_eq (q := 1) (r := 1) (by omega) (by omega) (by omega)]
          memqr_tac
        · rw [mem_T1_iff_of_eq (q := 1) (r := 3) (by omega) (by omega) (by omega)]
          memqr_tac
      · refine ⟨?_, by omega, by omega⟩
        rw [mem_T1_iff_of_eq (q := 0) (r := 4 * m + 5 + 2 * i) (by omega) (by simp) (by omega)]
        memqr_tac
      · refine ⟨?_, by omega, by omega⟩
        rw [mem_T1_iff_of_eq (q := 1) (r := 2 * m + 2 * i) (by omega) (by omega) (by omega)]
        memqr_tac
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    card_image_affine _ _ _ (by omega), card_image_affine _ _ _ (by omega),
    card_image_affine _ _ _ (by omega)]
  · omega
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_range]
    rintro x ⟨i, hi, rfl⟩ ⟨j, hj, hij⟩
    omega
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    rintro x (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) ⟨j, hj, hij⟩
    · omega
    · omega

/-! ## The odd case `g = 2k + 1` -/

/-- The closed form of `S_{1,g}` for odd `g`: `{1} ∪ {odd x : g ≤ x}`. -/
def Todd (g : ℕ) : Set ℕ := {x | x = 1 ∨ (Odd x ∧ g ≤ x)}

/-- Membership in `Todd g` is decidable. -/
instance (g : ℕ) : DecidablePred (· ∈ Todd g) := fun x => by
  unfold Todd
  infer_instance

/-- Ground truth: `Todd 5` agrees with the greedy sequence `S_{1,5}` below `40`. -/
example : (List.range 40).filter (· ∈ Todd 5) = gsBelow 1 5 40 := by
  decide +kernel

/-- For odd `g ≥ 3`, `Todd g` satisfies the greedy rule with initial terms `1, g`. -/
theorem isGS_Todd {g : ℕ} (hg : Odd g) (hg3 : 3 ≤ g) : IsGS 1 g (Todd g) := by
  obtain ⟨k, rfl⟩ := hg
  intro x
  simp only [Todd, Set.mem_ofPred_eq, Nat.odd_iff]
  constructor
  · rintro (rfl | ⟨hxo, hgx⟩)
    · exact Or.inl rfl
    · rcases Nat.eq_or_lt_of_le hgx with h | h
      · exact Or.inr (Or.inl h.symm)
      · refine Or.inr (Or.inr ⟨h, ?_⟩)
        rintro ⟨a, ha, b, hb, hab, hsum⟩
        rcases ha with ha | ⟨ha, -⟩ <;> rcases hb with hb | ⟨hb, -⟩ <;> omega
  · rintro (rfl | rfl | ⟨hgx, hns⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨by omega, le_rfl⟩
    · refine Or.inr ⟨?_, by omega⟩
      by_contra hxe
      exact hns ⟨1, Or.inl rfl, x - 1, Or.inr ⟨by omega, by omega⟩, by omega, by omega⟩

/-- **Closed form of `S_{1,g}` for odd `g ≥ 3`:** `S_{1,g} = {1} ∪ {odd x ≥ g}`;
in particular it is eventually periodic with period `2`. -/
theorem eq_Todd_of_isGS {g : ℕ} (hg : Odd g) (hg3 : 3 ≤ g) {S : Set ℕ} (hS : IsGS 1 g S) :
    S = Todd g :=
  IsGS.unique Nat.one_pos (by omega) hS (isGS_Todd hg hg3)

/-! ## The small even cases `g = 2, 4, 6` -/

/-- A sum of two distinct elements satisfying `P` can be written with the smaller
summand first. -/
theorem exists_lt_of_ne {P : ℕ → Prop} {x a : ℕ} (ha : P a) (hb : P (x - a)) (hab : a ≠ x - a)
    (hax : a ≤ x) : ∃ a, P a ∧ ∃ b, P b ∧ a < b ∧ a + b = x := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact ⟨a, ha, x - a, hb, h, by omega⟩
  · exact ⟨x - a, hb, a, ha, h, by omega⟩

/-- The closed form `S_{1,2} = {1, 2} ∪ {x ≥ 4 : x ≡ 1 (mod 3)}` (paper, Example
before Theorem 5.2). -/
def T2 : Set ℕ := {x | x = 1 ∨ x = 2 ∨ (4 ≤ x ∧ x % 3 = 1)}

/-- Membership in `T2` is decidable. -/
instance : DecidablePred (· ∈ T2) := fun x => by
  unfold T2
  infer_instance

/-- Ground truth: `T2` agrees with the greedy sequence `S_{1,2}` below `40`. -/
example : (List.range 40).filter (· ∈ T2) = gsBelow 1 2 40 := by
  decide +kernel

/-- `T2` satisfies the greedy rule with initial terms `1, 2`. -/
theorem isGS_T2 : IsGS 1 2 T2 := by
  intro x
  simp only [T2, Set.mem_ofPred_eq]
  constructor
  · intro hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    by_cases h2 : x = 2
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ⟨by omega, ?_⟩)
    rintro ⟨a, ha, b, hb, hab, rfl⟩
    omega
  · rintro (rfl | rfl | ⟨hgx, hns⟩)
    · omega
    · omega
    · by_contra hx
      apply hns
      obtain ⟨r, hr, hxr⟩ : ∃ r, r < 3 ∧ x % 3 = r := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
      interval_cases r <;>
        first
        | exact exists_lt_of_ne (a := 1) (by omega) (by omega) (by omega) (by omega)
        | exact exists_lt_of_ne (a := 2) (by omega) (by omega) (by omega) (by omega)

/-- **Closed form of `S_{1,2}`:** `S_{1,2} = {1, 2} ∪ {x ≥ 4 : x ≡ 1 (mod 3)}`
(stated without proof in the paper, Example before Theorem 5.2); in particular it
is eventually periodic. -/
theorem eq_T2_of_isGS {S : Set ℕ} (hS : IsGS 1 2 S) : S = T2 :=
  IsGS.unique Nat.one_pos (by omega) hS isGS_T2

/-- The closed form `S_{1,4} = {1, 4, 6, 8} ∪ {x ≥ 11 : x mod 12 ∈ {1, 4, 6, 11}}`
(OEIS A003662). -/
def T4 : Set ℕ :=
  {x | x = 1 ∨ x = 4 ∨ x = 6 ∨ x = 8 ∨
    (11 ≤ x ∧ (x % 12 = 1 ∨ x % 12 = 4 ∨ x % 12 = 6 ∨ x % 12 = 11))}

/-- Membership in `T4` is decidable. -/
instance : DecidablePred (· ∈ T4) := fun x => by
  unfold T4
  infer_instance

/-- Ground truth: `T4` agrees with the greedy sequence `S_{1,4}` below `80`. -/
example : (List.range 80).filter (· ∈ T4) = gsBelow 1 4 80 := by
  decide +kernel

/-- `T4` satisfies the greedy rule with initial terms `1, 4`. -/
theorem isGS_T4 : IsGS 1 4 T4 := by
  intro x
  simp only [T4, Set.mem_ofPred_eq]
  constructor
  · intro hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    by_cases h2 : x = 4
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ⟨by omega, ?_⟩)
    rintro ⟨a, ha, b, hb, hab, rfl⟩
    omega
  · rintro (rfl | rfl | ⟨hgx, hns⟩)
    · omega
    · omega
    · by_contra hx
      apply hns
      obtain ⟨r, hr, hxr⟩ : ∃ r, r < 12 ∧ x % 12 = r := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
      interval_cases r <;>
        first
        | exact exists_lt_of_ne (a := 1) (by omega) (by omega) (by omega) (by omega)
        | exact exists_lt_of_ne (a := 4) (by omega) (by omega) (by omega) (by omega)
        | exact exists_lt_of_ne (a := 8) (by omega) (by omega) (by omega) (by omega)

/-- **Closed form of `S_{1,4}`:**
`S_{1,4} = {1, 4, 6, 8} ∪ {x ≥ 11 : x mod 12 ∈ {1, 4, 6, 11}}` (OEIS A003662);
in particular it is eventually periodic. -/
theorem eq_T4_of_isGS {S : Set ℕ} (hS : IsGS 1 4 S) : S = T4 :=
  IsGS.unique Nat.one_pos (by omega) hS isGS_T4

/-- The closed form `S_{1,6} = {1, 6, 8, 10, 12} ∪ {x ≥ 15 : x mod 9 ∈ {1, 6, 8}}`
(OEIS A003663). -/
def T6 : Set ℕ :=
  {x | x = 1 ∨ x = 6 ∨ x = 8 ∨ x = 10 ∨ x = 12 ∨
    (15 ≤ x ∧ (x % 9 = 1 ∨ x % 9 = 6 ∨ x % 9 = 8))}

/-- Membership in `T6` is decidable. -/
instance : DecidablePred (· ∈ T6) := fun x => by
  unfold T6
  infer_instance

/-- Ground truth: `T6` agrees with the greedy sequence `S_{1,6}` below `80`. -/
example : (List.range 80).filter (· ∈ T6) = gsBelow 1 6 80 := by
  decide +kernel

/-- `T6` satisfies the greedy rule with initial terms `1, 6`. -/
theorem isGS_T6 : IsGS 1 6 T6 := by
  intro x
  simp only [T6, Set.mem_ofPred_eq]
  constructor
  · intro hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    by_cases h2 : x = 6
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ⟨by omega, ?_⟩)
    rintro ⟨a, ha, b, hb, hab, rfl⟩
    omega
  · rintro (rfl | rfl | ⟨hgx, hns⟩)
    · omega
    · omega
    · by_contra hx
      apply hns
      obtain ⟨r, hr, hxr⟩ : ∃ r, r < 9 ∧ x % 9 = r := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
      interval_cases r <;>
        first
        | exact exists_lt_of_ne (a := 1) (by omega) (by omega) (by omega) (by omega)
        | exact exists_lt_of_ne (a := 6) (by omega) (by omega) (by omega) (by omega)
        | exact exists_lt_of_ne (a := 12) (by omega) (by omega) (by omega) (by omega)

/-- **Closed form of `S_{1,6}`:**
`S_{1,6} = {1, 6, 8, 10, 12} ∪ {x ≥ 15 : x mod 9 ∈ {1, 6, 8}}` (OEIS A003663);
in particular it is eventually periodic. -/
theorem eq_T6_of_isGS {S : Set ℕ} (hS : IsGS 1 6 S) : S = T6 :=
  IsGS.unique Nat.one_pos (by omega) hS isGS_T6

end Candidates.TwoSumfreeFOneColumn
