/-
# A075997 — Irwin: a carry-defect count reproduces `Σ (-1)^k ⌊n/k⌋`

## OEIS source (retrieved with `oeis show A075997`, 2026-10-21)

```
NAME:     a(n) = [n/2] - [n/3] + [n/4] - [n/5] + [n/6] - ..., where [n/k] = floor(n/k).
TERMS:    0,0,1,0,2,1,2,1,4,2,3,2,5,4,5,2,6,5,6,5,8,5,6,5,10,8,9,6,9,8,9,8,13,...
          (offset 0)
COMMENT:  a(n) is the number of terms among {floor(n/k)}, 1<=k<=n, which are
          even. - _Leroy Quet_, Jan 19 2006
FORMULA (the conjecture):
  Conjecture: Let f(a,b)=1, if (a+b) mod |a-b| != (a mod |a-b|)+(b mod |a-b|),
  and 0 otherwise. a(n) = Sum_{k=1..n-1} f(n+k,n-k).
  - _Benedict W. J. Irwin_, Sep 23 2016
PROGRAM:  (PARI) a(n) = sum(k=2, n, (-1)^k*(n\k)); \\ _Michel Marcus_, Dec 20 2020
```

## Status

Triage status: open (no proof in the entry; the triage found none in the
literature, while noting a short informal argument).  Numerically checked
for `0 ≤ n ≤ 3000` (Python, 2026-10-21) before formalization.

## Proof outline (proved below, no `sorry`)

1. *Carry criterion* (`f_eq_ite_even`).  For `1 ≤ k ≤ n`, `|(n+k)-(n-k)| = 2k`
   and `n+k ≡ n-k (mod 2k)`, so `f (n+k) (n-k) = 1` iff the two equal residues
   `r` overflow, `2r ≥ 2k`, iff `n mod 2k < k`, iff `⌊n/k⌋` is even.
2. *Quet's comment* (`sum_ite_even_div_eq_a`).  Using
   `[q even] = 1 + Σ_{j=1}^{q} (-1)^j` and swapping the double sum over
   `{(j,k) : j k ≤ n}`, `#{k ≤ n : ⌊n/k⌋ even} = n + Σ_{j=1}^{n} (-1)^j ⌊n/j⌋`,
   which is `a(n)` after peeling off the `j = 1` term.
3. The `k = n` term of Quet's count vanishes (`⌊n/n⌋ = 1` is odd), giving
   Irwin's range `1 ≤ k ≤ n-1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A075997IrwinMod

/-! ## Definition layer -/

/-- OEIS A075997 (NAME): `a(n) = ⌊n/2⌋ - ⌊n/3⌋ + ⌊n/4⌋ - ⌊n/5⌋ + ...`, i.e.
`a(n) = Σ_{k=2}^{n} (-1)^k ⌊n/k⌋` (the PARI program in the entry), as an integer. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 2 n, (-1 : ℤ) ^ k * ((n / k : ℕ) : ℤ)

/-- Irwin's indicator: `f(x,y) = 1` if `(x+y) mod |x-y| ≠ (x mod |x-y|) + (y mod |x-y|)`,
and `0` otherwise.  The modulus `|x-y|` is computed in `ℤ` (cast before subtracting).
Only `|x-y| = 2k ≥ 2` occurs in the conjecture, so Lean's `m % 0 = m` convention is never
reached there. -/
def f (x y : ℕ) : ℕ :=
  if (x + y) % ((x : ℤ) - (y : ℤ)).natAbs
      ≠ x % ((x : ℤ) - (y : ℤ)).natAbs + y % ((x : ℤ) - (y : ℤ)).natAbs then 1 else 0

/-- Irwin's sum `Σ_{k=1}^{n-1} f(n+k, n-k)`; the range `1 ≤ k < n` keeps the natural
subtraction `n - k` exact. -/
def irwinSum (n : ℕ) : ℕ := ∑ k ∈ Finset.Ico 1 n, f (n + k) (n - k)

/-! ### Ground truth against the listed terms `a(0..19)` -/

example : (List.range 20).map a = [0, 0, 1, 0, 2, 1, 2, 1, 4, 2, 3, 2, 5, 4, 5, 2, 6, 5, 6, 5] := by
  decide

example :
    (List.range 20).map irwinSum = [0, 0, 1, 0, 2, 1, 2, 1, 4, 2, 3, 2, 5, 4, 5, 2, 6, 5, 6, 5] := by
  decide

-- `f` is a carry test: modulus `|7-3| = 4`, `10 % 4 = 2 ≠ 3 + 3`, so `f 7 3 = 1`.
example : f 7 3 = 1 := by decide

-- modulus `|6-4| = 2`, `10 % 2 = 0 = 0 + 0`, so `f 6 4 = 0`.
example : f 6 4 = 0 := by decide

/-! ## Step 1: the carry criterion -/

/-- If `x = m q + r` with `r < m`, then `x % m = r`. -/
theorem mod_eq_of_eq_mul_add {x m q r : ℕ} (h : x = m * q + r) (hr : r < m) : x % m = r := by
  subst h
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- If `x = m q + r` with `r < m`, then `x / m = q`. -/
theorem div_eq_of_eq_mul_add {x m q r : ℕ} (h : x = m * q + r) (hr : r < m) : x / m = q := by
  subst h
  have hm : 0 < m := by omega
  rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hr, Nat.add_zero]

/-- **Carry criterion.** For `1 ≤ k ≤ n`, `f(n+k, n-k) = 1` exactly when `⌊n/k⌋` is even. -/
theorem f_eq_ite_even {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    f (n + k) (n - k) = if Even (n / k) then 1 else 0 := by
  have hd : (((n + k : ℕ) : ℤ) - ((n - k : ℕ) : ℤ)).natAbs = 2 * k := by
    push_cast [hkn]; omega
  unfold f
  rw [hd]
  obtain ⟨Q, r, hn, hr2⟩ : ∃ Q r, n = 2 * k * Q + r ∧ r < 2 * k :=
    ⟨n / (2 * k), n % (2 * k), (Nat.div_add_mod n (2 * k)).symm, Nat.mod_lt _ (by omega)⟩
  rcases lt_or_ge r k with hrk | hrk
  · -- `n mod 2k < k`: both residues are `r + k`, and their sum overflows.
    have hQ1 : 1 ≤ Q := by
      by_contra hQ0
      have hQ0' : Q = 0 := by omega
      rw [hQ0', Nat.mul_zero, Nat.zero_add] at hn
      omega
    have h1 : (n + k) % (2 * k) = r + k := mod_eq_of_eq_mul_add (q := Q) (by omega) (by omega)
    have h2 : (n - k) % (2 * k) = r + k := by
      apply mod_eq_of_eq_mul_add (q := Q - 1) _ (by omega)
      have hsplit : 2 * k * Q = 2 * k * (Q - 1) + 2 * k := by
        rw [← Nat.mul_succ]; congr 1; omega
      omega
    have h3 : (n + k + (n - k)) % (2 * k) = 2 * r := by
      apply mod_eq_of_eq_mul_add (q := 2 * Q) _ (by omega)
      rw [show 2 * k * (2 * Q) = 2 * (2 * k * Q) by ring]
      omega
    have h4 : n / k = 2 * Q := div_eq_of_eq_mul_add (by rw [hn]; ring) hrk
    rw [h1, h2, h3, h4, if_pos (by omega), if_pos (even_two_mul Q)]
  · -- `n mod 2k ≥ k`: both residues are `r - k`, and their sum does not overflow.
    have h1 : (n + k) % (2 * k) = r - k := by
      apply mod_eq_of_eq_mul_add (q := Q + 1) _ (by omega)
      rw [Nat.mul_succ]; omega
    have h2 : (n - k) % (2 * k) = r - k := mod_eq_of_eq_mul_add (q := Q) (by omega) (by omega)
    have h3 : (n + k + (n - k)) % (2 * k) = 2 * (r - k) := by
      apply mod_eq_of_eq_mul_add (q := 2 * Q + 1) _ (by omega)
      rw [show 2 * k * (2 * Q + 1) = 2 * (2 * k * Q) + 2 * k by ring]
      omega
    have h4 : n / k = 2 * Q + 1 :=
      div_eq_of_eq_mul_add (r := r - k) (by rw [hn]; ring_nf; omega) (by omega)
    have hodd : ¬ Even (2 * Q + 1) := by
      rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one Q
    rw [h1, h2, h3, h4, if_neg (by omega), if_neg hodd]

/-! ## Step 2: Quet's comment, `#{k ≤ n : ⌊n/k⌋ even} = a(n)` -/

/-- `[q even] = 1 + Σ_{j=1}^{q} (-1)^j` in `ℤ`. -/
theorem even_indicator (q : ℕ) :
    ((if Even q then 1 else 0 : ℕ) : ℤ) = 1 + ∑ j ∈ Finset.Icc 1 q, (-1 : ℤ) ^ j := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih]
    rcases Nat.even_or_odd q with hq | hq
    · have hq1 : ¬ Even (q + 1) := by rw [Nat.not_even_iff_odd]; exact hq.add_one
      rw [if_pos hq, if_neg hq1, pow_succ, hq.neg_one_pow]; norm_num
    · have hq1 : Even (q + 1) := hq.add_one
      rw [if_neg (Nat.not_even_iff_odd.mpr hq), if_pos hq1, hq1.neg_one_pow]; norm_num

/-- For `0 < j`, the `k ∈ [1, n]` with `j k ≤ n` are exactly `k ∈ [1, ⌊n/j⌋]`. -/
theorem filter_mul_le_eq_Icc (n j : ℕ) (hj : 0 < j) :
    (Finset.Icc 1 n).filter (fun k => j * k ≤ n) = Finset.Icc 1 (n / j) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_div_iff_mul_le hj]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨h1, ?_⟩, by linarith⟩
    nlinarith

/-- Hyperbola swap: `Σ_{k=1}^{n} Σ_{j=1}^{⌊n/k⌋} g(j) = Σ_{j=1}^{n} g(j) ⌊n/j⌋`
(both sides sum `g(j)` over pairs with `j k ≤ n`). -/
theorem sum_Icc_sum_Icc_div_eq (n : ℕ) (g : ℕ → ℤ) :
    ∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (n / k), g j
      = ∑ j ∈ Finset.Icc 1 n, g j * ((n / j : ℕ) : ℤ) := by
  have hin : ∀ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (n / k), g j
      = ∑ j ∈ Finset.Icc 1 n, if j * k ≤ n then g j else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [← Finset.sum_filter, ← filter_mul_le_eq_Icc n k (by omega)]
    congr 1
    ext j
    simp only [Finset.mem_filter, mul_comm j k]
  rw [Finset.sum_congr rfl hin, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [← Finset.sum_filter, filter_mul_le_eq_Icc n j (by omega), Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, Nat.add_sub_cancel, mul_comm]

/-- **Quet's comment (A075997, Leroy Quet, Jan 19 2006).** `a(n)` is the number of
`k ∈ [1, n]` with `⌊n/k⌋` even. -/
theorem sum_ite_even_div_eq_a (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ((if Even (n / k) then 1 else 0 : ℕ) : ℤ) = a n := by
  simp_rw [even_indicator]
  rw [Finset.sum_add_distrib, sum_Icc_sum_Icc_div_eq, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  unfold a
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩)]
    have hdiff : (Finset.Icc 1 n).erase 1 = Finset.Icc 2 n := by
      ext k; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
    rw [hdiff]
    simp only [Nat.div_one, pow_one]
    ring

/-! ## The conjecture -/

/-- **Irwin's conjecture (A075997, Benedict W. J. Irwin, Sep 23 2016).**

Verbatim: "Conjecture: Let f(a,b)=1, if (a+b) mod |a-b| != (a mod |a-b|)+(b mod |a-b|),
and 0 otherwise. a(n) = Sum_{k=1..n-1} f(n+k,n-k)."

Stated for every `n : ℕ` (the entry has offset 0; for `n ≤ 1` both sides are `0`). -/
theorem irwin_conjecture (n : ℕ) : (irwinSum n : ℤ) = a n := by
  rw [← sum_ite_even_div_eq_a, irwinSum, Nat.cast_sum]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hlast : ((if Even (n / n) then 1 else 0 : ℕ) : ℤ) = 0 := by
      rw [Nat.div_self hn, if_neg Nat.not_even_one, Nat.cast_zero]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top (by omega), hlast, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [f_eq_ite_even (by omega) hk.2.le]

end Candidates.A075997IrwinMod
