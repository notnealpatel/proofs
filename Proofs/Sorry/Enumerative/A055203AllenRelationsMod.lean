/-
# A055203 — Bala: Allen relation counts are `1 (mod 12)` and eventually periodic

## OEIS source (retrieved with `oeis show A055203`, 2026-10-21)

```
NAME:     Number of different relations between n intervals on a line.
TERMS:    1,1,13,409,23917,2244361,308682013,58514835289,14623910308237,
          4659168491711401,1843200116875263613,886470355671907534969,...
FORMULA (Bala, the definition used here):
  a(n) = Sum_{k = 2..2*n} Sum_{i = 0..k} (-1)^(k-i)*binomial(k,i)*(i*(i-1)/2)^n.
  (with a(0) = 1)
FORMULA (Jovovic, Aug 25 2006):
  a(n) = Sum_{k=0..n} k!*Stirling2(n,k)*A121251(k).
COMMENT (the conjecture):
  From _Peter Bala_, Jan 30 2018: (Start) ...
  Conjectures: a(n) == 1 (mod 12); for fixed k, the sequence a(n) (mod k)
  eventually becomes periodic with exact period a divisor of phi(k), where
  phi(k) is Euler's totient function A000010. (End)
```

## Status

Triage: open (the entry still calls both statements conjectures; no published
proof was found by the triage).  This module proves both, with the short
Stirling-number argument suggested by the triage:

* `C(i,2)^n = Σ_l S₂(n,l) l! C(C(i,2),l)`, so by linearity of finite
  differences `a(n) = Σ_{l ≤ n} l! S₂(n,l) U(l)` with
  `U(l) = Σ_{j ≤ 2l} Δ^j[i ↦ C(C(i,2),l)](0)` (= A121251; the higher
  differences vanish because `i ↦ C(C(i,2),l)` is a polynomial of degree `2l`).
* `l! S₂(n,l) = Δ^l[x ↦ x^n](0) = Σ_i (-1)^(l-i) C(l,i) i^n`.
* Modulo `m`, the terms with `l ≥ m` die (`m ∣ l!`), and `i^(n+φ(m)) ≡ i^n`
  for `n ≥ m`; this gives period `φ(m)` from `n = m` on.
* Modulo `12`, `U(0..3) = 1, 1, 6, 62`, so
  `a(n) ≡ S₂(n,0) + S₂(n,1) = 1`.

The definition `allen` sums `k` over `0..2n` rather than Bala's `2..2n`; the
extra terms vanish for `n ≥ 1` (`allen_eq_bala`) and make `a(0) = 1` come out
of the same formula.  `C(i,2)` is written `i.choose 2`, which equals Bala's
`i*(i-1)/2` (`Nat.choose_two_right`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A055203AllenRelationsMod

open Finset Polynomial

/-! ## Definition layer -/

/-- The OEIS A055203 sequence, via Bala's double-sum formula
`a(n) = Σ_{k=0}^{2n} Σ_{i=0}^{k} (-1)^(k-i) C(k,i) C(i,2)^n`.
The inner sum is the `k`-th forward difference of `i ↦ C(i,2)^n` at `0`. -/
def allen (n : ℕ) : ℤ :=
  ∑ k ∈ range (2 * n + 1), ∑ i ∈ range (k + 1),
    (-1) ^ (k - i) * (k.choose i : ℤ) * ((i.choose 2 : ℕ) : ℤ) ^ n

example : allen 0 = 1 := by decide
example : allen 1 = 1 := by decide
example : allen 2 = 13 := by decide
example : allen 3 = 409 := by decide
example : allen 4 = 23917 := by decide

/-- For `n ≥ 1`, `allen n` is literally Bala's formula with `k` running over
`2..2n` (the `k = 0, 1` terms vanish because `C(0,2) = C(1,2) = 0`). -/
theorem allen_eq_bala (n : ℕ) (hn : 1 ≤ n) :
    allen n = ∑ k ∈ Icc 2 (2 * n), ∑ i ∈ range (k + 1),
      (-1) ^ (k - i) * (k.choose i : ℤ) * ((i.choose 2 : ℕ) : ℤ) ^ n := by
  let F : ℕ → ℤ := fun k => ∑ i ∈ range (k + 1),
    (-1) ^ (k - i) * (k.choose i : ℤ) * ((i.choose 2 : ℕ) : ℤ) ^ n
  have hz : (0 : ℤ) ^ n = 0 := zero_pow (by omega)
  have hF0 : F 0 = 0 := by simp [F, hz]
  have hF1 : F 1 = 0 := by simp [F, hz, sum_range_succ]
  have hIcc : Icc 2 (2 * n) = Ico 2 (2 * n + 1) := rfl
  change ∑ k ∈ range (2 * n + 1), F k = ∑ k ∈ Icc 2 (2 * n), F k
  rw [hIcc, sum_Ico_eq_sum_range, show 2 * n + 1 = 2 * n - 1 + 1 + 1 by omega,
    sum_range_succ', sum_range_succ', hF0, hF1, add_zero, add_zero,
    show 2 * n - 1 + 1 + 1 - 2 = 2 * n - 1 by omega]
  exact sum_congr rfl fun k _ => by rw [add_comm 2 k]

/-- `diffAt k g` is the `k`-th forward difference of `g : ℕ → ℤ` at `0`,
`Σ_{i ≤ k} (-1)^(k-i) C(k,i) g(i)`. -/
def diffAt (k : ℕ) (g : ℕ → ℤ) : ℤ :=
  ∑ i ∈ range (k + 1), (-1) ^ (k - i) * (k.choose i : ℤ) * g i

/-- The function `i ↦ C(C(i,2), k)`. -/
def chooseChoose (k i : ℕ) : ℤ := ((i.choose 2).choose k : ℤ)

/-- `U(k) = Σ_{j ≤ 2k} Δ^j[i ↦ C(C(i,2),k)](0)`, the sequence A121251
(`1, 1, 6, 62, 900, ...`) in Jovovic's formula. -/
def allenU (k : ℕ) : ℤ := ∑ j ∈ range (2 * k + 1), diffAt j (chooseChoose k)

/-- `U(0) = 1`. -/
theorem allenU_zero : allenU 0 = 1 := by decide
/-- `U(1) = 1`. -/
theorem allenU_one : allenU 1 = 1 := by decide
/-- `U(2) = 6`. -/
theorem allenU_two : allenU 2 = 6 := by decide
/-- `U(3) = 62`. -/
theorem allenU_three : allenU 3 = 62 := by decide

/-- `p` is an eventual period of `s` modulo `m`: `s (n + p) ≡ s n (mod m)` for
all large `n`. -/
def IsEventualPeriodMod (s : ℕ → ℤ) (m p : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → s (n + p) ≡ s n [ZMOD m]

/-! ## Finite differences -/

/-- `diffAt` agrees with Mathlib's iterated forward difference at `0`. -/
theorem diffAt_eq_fwdDiff (k : ℕ) (g : ℕ → ℤ) : diffAt k g = (fwdDiff 1)^[k] g 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp [diffAt, smul_eq_mul]

/-- `Δ^k[x ↦ C(x,l)](0) = [k = l]`. -/
theorem diffAt_choose (k l : ℕ) :
    diffAt k (fun x => (x.choose l : ℤ)) = if k = l then 1 else 0 := by
  rw [diffAt_eq_fwdDiff, fwdDiff_iter_choose_zero]

/-- Linearity of `diffAt` over a finite linear combination. -/
theorem diffAt_sum {ι : Type*} (s : Finset ι) (c : ι → ℤ) (h : ι → ℕ → ℤ) (k : ℕ) :
    diffAt k (fun i => ∑ t ∈ s, c t * h t i) = ∑ t ∈ s, c t * diffAt k (h t) := by
  simp only [diffAt, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun i _ => ?_
  ring

/-- If `g` agrees on `ℕ` with a rational polynomial of degree `< j`, then the
`j`-th forward difference of `g` at `0` vanishes. -/
theorem diffAt_eq_zero_of_eval (g : ℕ → ℤ) (P : ℚ[X]) (hP : ∀ i : ℕ, P.eval (i : ℚ) = g i)
    (j : ℕ) (hj : P.natDegree < j) : diffAt j g = 0 := by
  have hcast : ((diffAt j g : ℤ) : ℚ) = (fwdDiff 1)^[j] P.eval 0 := by
    rw [fwdDiff_iter_eq_sum_shift]
    simp [diffAt, hP]
  rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hj, Pi.zero_apply] at hcast
  exact_mod_cast hcast

/-! ## Stirling expansion -/

/-- `x^(l+1) + l x^(l)` in falling factorials: `x^{\underline{l+1}} + l x^{\underline l}
= x · x^{\underline l}`. -/
theorem descFactorial_succ_add_mul (x l : ℕ) :
    x.descFactorial (l + 1) + l * x.descFactorial l = x * x.descFactorial l := by
  rw [Nat.descFactorial_succ]
  rcases le_or_gt l x with h | h
  · rw [← add_mul, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
    simp

/-- `x^n = Σ_{l ≤ n} S₂(n,l) x^{\underline l}`. -/
theorem pow_eq_sum_stirlingSecond (x n : ℕ) :
    x ^ n = ∑ l ∈ range (n + 1), n.stirlingSecond l * x.descFactorial l := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hshift : ∑ t ∈ range (n + 1),
        (t + 1) * n.stirlingSecond (t + 1) * x.descFactorial (t + 1)
        = ∑ l ∈ range (n + 1), l * n.stirlingSecond l * x.descFactorial l := by
      rw [sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n),
        sum_range_succ' (fun l => l * n.stirlingSecond l * x.descFactorial l)]
      simp
    rw [sum_range_succ', Nat.stirlingSecond_succ_zero, zero_mul, add_zero]
    have hterm : ∀ t, (n + 1).stirlingSecond (t + 1) * x.descFactorial (t + 1)
        = (t + 1) * n.stirlingSecond (t + 1) * x.descFactorial (t + 1)
          + n.stirlingSecond t * x.descFactorial (t + 1) := fun t => by
      rw [Nat.stirlingSecond_succ_succ, add_mul]
    simp only [hterm, sum_add_distrib, hshift]
    rw [pow_succ, ih, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_assoc, mul_comm (x.descFactorial l) x, ← descFactorial_succ_add_mul x l]
    ring

/-- `x^n = Σ_{l ≤ n} S₂(n,l) l! C(x,l)` over `ℤ`. -/
theorem cast_pow_eq_sum (x n : ℕ) :
    (x : ℤ) ^ n = ∑ l ∈ range (n + 1), ((n.stirlingSecond l * l.factorial : ℕ) : ℤ) *
      (x.choose l : ℤ) := by
  rw [← Nat.cast_pow, pow_eq_sum_stirlingSecond]
  push_cast
  refine sum_congr rfl fun l _ => ?_
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- `Δ^l[x ↦ x^n](0) = S₂(n,l) l!`. -/
theorem diffAt_pow (n l : ℕ) :
    diffAt l (fun i => (i : ℤ) ^ n) = ((n.stirlingSecond l * l.factorial : ℕ) : ℤ) := by
  simp_rw [cast_pow_eq_sum]
  rw [diffAt_sum]
  simp only [diffAt_choose, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range]
  split_ifs with h
  · rfl
  · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]
    simp

/-! ## The polynomial `C(C(x,2),k)` and the decomposition `a(n) = Σ l! S₂(n,l) U(l)` -/

/-- A rational polynomial of degree `≤ 2k` whose value at `i : ℕ` is `C(C(i,2),k)`. -/
noncomputable def chooseChoosePoly (k : ℕ) : ℚ[X] :=
  C ((k.factorial : ℚ)⁻¹) * (descPochhammer ℚ k).comp (C (1 / 2 : ℚ) * X * (X - 1))

/-- `deg C(C(x,2),k) ≤ 2k`. -/
theorem chooseChoosePoly_natDegree_le (k : ℕ) : (chooseChoosePoly k).natDegree ≤ 2 * k := by
  unfold chooseChoosePoly
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_comp_le.trans ?_
  rw [descPochhammer_natDegree]
  have h2 : (C (1 / 2 : ℚ) * X * (X - 1)).natDegree ≤ 2 := by compute_degree
  nlinarith

/-- `chooseChoosePoly k` evaluates to `C(C(i,2),k)` at natural `i`. -/
theorem chooseChoosePoly_eval (k i : ℕ) :
    (chooseChoosePoly k).eval (i : ℚ) = chooseChoose k i := by
  have hq : (C (1 / 2 : ℚ) * X * (X - 1)).eval (i : ℚ) = ((i.choose 2 : ℕ) : ℚ) := by
    rw [Nat.cast_choose_two]
    simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one]
    ring
  simp only [chooseChoose, chooseChoosePoly, eval_mul, eval_C, eval_comp, hq,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- `Δ^j[i ↦ C(C(i,2),k)](0) = 0` for `j > 2k`. -/
theorem diffAt_chooseChoose_eq_zero (k j : ℕ) (hj : 2 * k < j) :
    diffAt j (chooseChoose k) = 0 :=
  diffAt_eq_zero_of_eval _ _ (chooseChoosePoly_eval k) j
    ((chooseChoosePoly_natDegree_le k).trans_lt hj)

/-- Summing the differences of `C(C(i,2),k)` beyond `2k` does not change `U(k)`. -/
theorem sum_diffAt_chooseChoose (k N : ℕ) (hN : 2 * k + 1 ≤ N) :
    ∑ j ∈ range N, diffAt j (chooseChoose k) = allenU k := by
  symm
  refine sum_subset (range_subset_range.mpr hN) fun j _ hj => ?_
  exact diffAt_chooseChoose_eq_zero k j (by simp only [mem_range, not_lt] at hj; omega)

/-- Jovovic's formula: `a(n) = Σ_{l ≤ n} S₂(n,l) l! U(l)`. -/
theorem allen_eq_sum (n : ℕ) :
    allen n = ∑ l ∈ range (n + 1), ((n.stirlingSecond l * l.factorial : ℕ) : ℤ) * allenU l := by
  have hf : allen n =
      ∑ j ∈ range (2 * n + 1), diffAt j (fun i => ((i.choose 2 : ℕ) : ℤ) ^ n) := rfl
  simp_rw [hf, cast_pow_eq_sum (Nat.choose _ 2) n]
  have hcc : ∀ j, diffAt j (fun i => ∑ l ∈ range (n + 1),
      ((n.stirlingSecond l * l.factorial : ℕ) : ℤ) * (((i.choose 2).choose l : ℕ) : ℤ))
      = ∑ l ∈ range (n + 1), ((n.stirlingSecond l * l.factorial : ℕ) : ℤ) *
        diffAt j (chooseChoose l) := fun j => diffAt_sum _ _ (fun l i => chooseChoose l i) j
  simp_rw [hcc]
  rw [sum_comm]
  refine sum_congr rfl fun l hl => ?_
  rw [← mul_sum, sum_diffAt_chooseChoose l _ (by simp only [mem_range] at hl; omega)]

/-! ## Part (i): `a(n) ≡ 1 (mod 12)` -/

/-- **Bala's first conjecture (A055203), proved.** `a(n) ≡ 1 (mod 12)` for all `n ≥ 0`. -/
theorem allen_modEq_one (n : ℕ) : allen n ≡ 1 [ZMOD 12] := by
  rcases n with _ | n
  · decide
  refine (ZMod.intCast_eq_intCast_iff _ _ 12).mp ?_
  rw [allen_eq_sum]
  push_cast
  have hterm : ∀ l ∈ range (n + 1 + 1), ((n + 1).stirlingSecond l : ZMod 12) *
      (l.factorial : ZMod 12) * (allenU l : ZMod 12) = if l = 1 then 1 else 0 := by
    intro l _
    rcases l with _ | _ | _ | _ | l
    · simp
    · simp [Nat.stirlingSecond_one_right, allenU_one]
    · rw [allenU_two]
      simp only [if_neg (by decide : (2 : ℕ) ≠ 1)]
      have h12 : ((Nat.factorial 2 : ℕ) : ZMod 12) * ((6 : ℤ) : ZMod 12) = 0 := by decide
      rw [mul_assoc, h12, mul_zero]
    · rw [allenU_three]
      simp only [if_neg (by decide : (3 : ℕ) ≠ 1)]
      have h12 : ((Nat.factorial 3 : ℕ) : ZMod 12) * ((62 : ℤ) : ZMod 12) = 0 := by decide
      rw [mul_assoc, h12, mul_zero]
    · have hdvd : 12 ∣ (l + 4).factorial :=
        (by decide : 12 ∣ Nat.factorial 4).trans (Nat.factorial_dvd_factorial (by omega))
      have hfac : (((l + 4).factorial : ℕ) : ZMod 12) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      simp only [hfac, mul_zero, zero_mul, if_neg (by omega : l + 4 ≠ 1)]
  rw [sum_congr rfl hterm, sum_ite_eq']
  simp

/-! ## Part (ii): eventual periodicity modulo `m` with period dividing `φ(m)` -/

/-- `i^(n + φ(m)) ≡ i^n (mod m)` once `n ≥ m`, for every `i` (coprime or not). -/
theorem pow_add_totient_modEq (i m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    i ^ (n + m.totient) ≡ i ^ n [MOD m] := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [zero_pow (by omega), zero_pow (by omega)]
  have hle : i ^ n ≤ i ^ (n + m.totient) := Nat.pow_le_pow_right hi (by omega)
  refine ((Nat.modEq_iff_dvd' hle).mpr ?_).symm
  have hsplit : i ^ (n + m.totient) - i ^ n = i ^ n * (i ^ m.totient - 1) := by
    rw [Nat.mul_sub_one, pow_add]
  rw [hsplit, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  by_cases hpi : p ∣ i
  · have hkm : k < m := (Nat.lt_pow_self hp.one_lt).trans_le (Nat.le_of_dvd hm hpk)
    exact Dvd.dvd.mul_right ((pow_dvd_pow_of_dvd hpi k).trans (pow_dvd_pow i (by omega))) _
  · have hcop : Nat.Coprime i (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpi).symm
    obtain ⟨c, hc⟩ := Nat.totient_dvd_of_dvd hpk
    have hone : i ^ m.totient ≡ 1 [MOD p ^ k] := by
      rw [hc, pow_mul]
      simpa using (Nat.ModEq.pow_totient hcop).pow c
    exact Dvd.dvd.mul_left ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hi)).mp hone.symm) _

/-- For `n ≥ m > 0`, `a(n) ≡ Σ_{l < m} Δ^l[x ↦ x^n](0) · U(l) (mod m)`: the terms
with `l ≥ m` carry the factor `l!`, which `m` divides. -/
theorem allen_zmod_eq (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (allen n : ZMod m) =
      ∑ l ∈ range m, (diffAt l (fun i => (i : ℤ) ^ n) : ZMod m) * allenU l := by
  simp_rw [allen_eq_sum, ← diffAt_pow]
  push_cast
  symm
  refine sum_subset (range_subset_range.mpr (by omega)) fun l _ hl => ?_
  simp only [mem_range, not_lt] at hl
  rw [diffAt_pow]
  have hfac : ((l.factorial : ℕ) : ZMod m) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial (by omega) hl)
  push_cast
  rw [hfac]
  ring

/-- `a(n + φ(m)) ≡ a(n) (mod m)` for all `n ≥ m`, for every modulus `m ≥ 1`. -/
theorem allen_add_totient_modEq (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : m ≤ n) :
    allen (n + m.totient) ≡ allen n [ZMOD m] := by
  rw [← ZMod.intCast_eq_intCast_iff, allen_zmod_eq m _ hm (by omega), allen_zmod_eq m n hm hn]
  refine sum_congr rfl fun l _ => ?_
  congr 1
  simp only [diffAt]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  have h := (ZMod.natCast_eq_natCast_iff _ _ m).mpr (pow_add_totient_modEq i m n hm hn)
  push_cast at h
  rw [h]

/-- An eventual period `p` iterates: `s (n + p x) ≡ s n` past the threshold. -/
theorem modEq_add_mul_of_period {s : ℕ → ℤ} {m p N : ℕ}
    (h : ∀ n, N ≤ n → s (n + p) ≡ s n [ZMOD m]) (x n : ℕ) (hn : N ≤ n) :
    s (n + p * x) ≡ s n [ZMOD m] := by
  induction x with
  | zero => simp [Int.ModEq.refl]
  | succ x ih =>
    have h1 := h (n + p * x) (by omega)
    rw [show n + p * x + p = n + p * (x + 1) by ring] at h1
    exact h1.trans ih

/-- The gcd of two eventual periods is an eventual period. -/
theorem IsEventualPeriodMod.gcd {s : ℕ → ℤ} {m p q : ℕ}
    (hp : IsEventualPeriodMod s m p) (hq : IsEventualPeriodMod s m q) :
    IsEventualPeriodMod s m (Nat.gcd p q) := by
  obtain ⟨N₁, h₁⟩ := hp
  obtain ⟨N₂, h₂⟩ := hq
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · rw [Nat.gcd_zero_right]
    exact ⟨N₁, h₁⟩
  rcases (Nat.gcd_le_right (m := p) (n := q) hq0).eq_or_lt with hg | hg
  · rw [hg]
    exact ⟨N₂, h₂⟩
  obtain ⟨x, -, hx⟩ := Nat.exists_mul_mod_eq_gcd hg
  have hbez : p * x = Nat.gcd p q + q * (p * x / q) := by
    have hdm := Nat.mod_add_div (p * x) q
    omega
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hA := modEq_add_mul_of_period h₂ (p * x / q) (n + Nat.gcd p q) (by omega)
  have hB := modEq_add_mul_of_period h₁ x n (by omega)
  rw [show n + Nat.gcd p q + q * (p * x / q) = n + p * x by omega] at hA
  exact hA.symm.trans hB

/-- `φ(m)` is an eventual period of `a(n) mod m` (from `n = m` on). -/
theorem allen_isEventualPeriodMod_totient (m : ℕ) (hm : 0 < m) :
    IsEventualPeriodMod allen m m.totient :=
  ⟨m, fun n hn => allen_add_totient_modEq m hm n hn⟩

/-- The exact (least positive) eventual period of `a(n) mod m` divides `φ(m)`. -/
theorem dvd_totient_of_isLeast_period (m : ℕ) (hm : 0 < m) (p : ℕ) (hp0 : 0 < p)
    (hp : IsEventualPeriodMod allen m p)
    (hmin : ∀ q, 0 < q → IsEventualPeriodMod allen m q → p ≤ q) : p ∣ m.totient := by
  have hg := hp.gcd (allen_isEventualPeriodMod_totient m hm)
  have hgpos : 0 < Nat.gcd p m.totient := Nat.gcd_pos_of_pos_left _ hp0
  have hle := hmin _ hgpos hg
  have hge := Nat.le_of_dvd hp0 (Nat.gcd_dvd_left p m.totient)
  exact Nat.gcd_eq_left_iff_dvd.mp (le_antisymm hge hle)

/-- Non-vacuity of the exact-period clause: for every `m ≥ 1` a least positive
eventual period of `a(n) mod m` exists. -/
theorem exists_least_period (m : ℕ) (hm : 0 < m) :
    ∃ p, 0 < p ∧ IsEventualPeriodMod allen m p ∧
      ∀ q, 0 < q → IsEventualPeriodMod allen m q → p ≤ q := by
  classical
  have hex : ∃ p, 0 < p ∧ IsEventualPeriodMod allen m p :=
    ⟨m.totient, Nat.totient_pos.mpr hm, allen_isEventualPeriodMod_totient m hm⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun q hq0 hq => ?_⟩
  exact Nat.find_min' hex ⟨hq0, hq⟩

/-! ## The conjecture -/

/-- **Bala's conjectures on A055203 (Peter Bala, Jan 30 2018), proved.**

Verbatim: "Conjectures: a(n) == 1 (mod 12); for fixed k, the sequence a(n)
(mod k) eventually becomes periodic with exact period a divisor of phi(k), where
phi(k) is Euler's totient function A000010."

Formalized as: (i) `a(n) ≡ 1 (mod 12)` for every `n ≥ 0`; (ii) for every modulus
`m ≥ 1`, `φ(m)` is an eventual period of `a(n) mod m`, and every least positive
eventual period (the "exact period", which exists by `exists_least_period`)
divides `φ(m)`. -/
theorem bala_conjecture :
    (∀ n, allen n ≡ 1 [ZMOD 12]) ∧
      ∀ m, 0 < m → IsEventualPeriodMod allen m m.totient ∧
        ∀ p, 0 < p → IsEventualPeriodMod allen m p →
          (∀ q, 0 < q → IsEventualPeriodMod allen m q → p ≤ q) → p ∣ m.totient :=
  ⟨allen_modEq_one, fun m hm =>
    ⟨allen_isEventualPeriodMod_totient m hm, dvd_totient_of_isLeast_period m hm⟩⟩

end Candidates.A055203AllenRelationsMod
