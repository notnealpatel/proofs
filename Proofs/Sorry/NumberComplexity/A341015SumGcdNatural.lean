/-
# A341015 — Bergot–Israel: `gcd(A066840(n), A124440(n)) = 1` exactly for `4, 3^j, 2*3^j, 5^j`

## OEIS source (retrieved with `oeis show A341015` and the live entry, 2026-10-21)

```
NAME:     Numbers k such that A124446(k) = 1.
TERMS:    1,2,3,4,5,6,9,18,25,27,54,81,125,162,243,486,625,729,1458,2187,3125,...
AUTHOR:   J. M. Bergot and Robert Israel, Feb 02 2021
COMMENT:  Numbers k such that A066840(k) and A124440(k) are coprime.
COMMENT:  Contains all numbers of the forms 3^j, 2*3^j and 5^j.
COMMENT:  Conjecture: the only term not of one of those forms is 4.
```

A066840: "Sum of positive integers k where k <= n/2 and gcd(k,n) = 1."
A124440: "a(n) = Sum_{n/2<=k<=n, gcd(k,n)=1} k."
A124446: "a(n) = gcd(A066840(n), A124440(n))."

The conjecture line carries no separate attribution; it is part of the entry by
J. M. Bergot and Robert Israel (Feb 02 2021).

## Status

Triage: open (no proof in the entry; Baum, Math. Mag. 55 (1982) 111-113, linked from
A066840, gives the half-range totative sum formula but not this characterization; the
literature search was shallow, so this is not a novelty claim).  This module proves the
conjecture in full (`a341015`), with no `sorry`.

## Proof outline

* Reflection `k ↦ n - k`: `S2 n + S1 n = n * cnt n` (`n ≥ 2`), so
  `gcd(S1, S2) = gcd(S1, n * cnt n)`, where `cnt n = φ(n)/2` for `n ≥ 3`.
* `4 ∣ n`: the involution `k ↦ n/2 - k` gives `4 * S1 n = n * cnt n`, so the gcd is `S1 n`,
  which is `1` only for `n = 4`.
* Odd `m = 2r+1 ≥ 3`, odd `p = 2h+1`: block decomposition gives
  `S1 (p*m) = S1 m + m * cnt m * h(h+1)` if `p ∣ m`, and
  `S1 (p*m) + 2h * S1 m = m * cnt m * h(h+1)` if `p` is a prime not dividing `m`;
  also `S1 (2m) + 2 * S1 m = m * cnt m`.
* Hence `S1 m` is even when odd `m` has two distinct prime factors (and then `4 ∣ φ m`),
  while for `m = p^a` an odd prime `q ∣ p - 1`, or `2` when `8 ∣ p - 1`, divides both
  `S1 m` and `cnt m`.  The survivors are `3^a`, `5^a`, `2*3^a` (`2*5^a` fails by parity).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A341015SumGcdNatural

open Finset

/-- A066840: `S1 n` is the sum of the `k` with `1 ≤ k ≤ n/2` and `gcd(k, n) = 1`. -/
def S1 (n : ℕ) : ℕ := ∑ k ∈ (Icc 1 (n / 2)).filter (fun k => Nat.Coprime k n), k

/-- A124440: `S2 n` is the sum of the `k` with `n/2 ≤ k ≤ n` and `gcd(k, n) = 1`
(the real inequality `n/2 ≤ k` is written `n ≤ 2 * k`). -/
def S2 (n : ℕ) : ℕ := ∑ k ∈ (Icc 1 n).filter (fun k => n ≤ 2 * k ∧ Nat.Coprime k n), k

/-- Number of `k` with `1 ≤ k ≤ n/2` and `gcd(k, n) = 1` (auxiliary). -/
def cnt (n : ℕ) : ℕ := ((Icc 1 (n / 2)).filter (fun k => Nat.Coprime k n)).card

/-- Sum of the `k < x` coprime to `m` (auxiliary). -/
def F (m x : ℕ) : ℕ := ∑ k ∈ range x, if Nat.Coprime k m then k else 0

/-- Number of the `k < x` coprime to `m` (auxiliary). -/
def G (m x : ℕ) : ℕ := ∑ k ∈ range x, if Nat.Coprime k m then 1 else 0

/-! Ground truth against A066840 (offset 1) and A124440 (offset 1). -/
example : (List.range 12).map (fun i => S1 (i + 1)) = [0, 1, 1, 1, 3, 1, 6, 4, 7, 4, 15, 6] := by
  decide
example : (List.range 12).map (fun i => S2 (i + 1)) = [1, 1, 2, 3, 7, 5, 15, 12, 20, 16, 40, 18] :=
  by decide
/-- Ground truth: the first terms of A341015 below 30 are exactly 1,2,3,4,5,6,9,18,25,27. -/
example : (List.range 30).filter (fun n => Nat.gcd (S1 n) (S2 n) = 1) =
    [1, 2, 3, 4, 5, 6, 9, 18, 25, 27] := by decide

/-- Shift identity for the totative sums. -/
lemma F_add (m x : ℕ) : F m (m + x) = F m m + F m x + m * G m x := by
  unfold F G
  rw [sum_range_add, mul_sum, add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  simp only [Nat.coprime_self_add_left]
  split_ifs <;> simp [add_comm]

/-- Shift identity for the totative counts. -/
lemma G_add (m x : ℕ) : G m (m + x) = G m m + G m x := by
  unfold G
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  simp only [Nat.coprime_self_add_left]

/-- Iterated shift identity for the totative counts. -/
lemma G_mul_add (m h y : ℕ) : G m (h * m + y) = h * G m m + G m y := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show (h + 1) * m + y = m + (h * m + y) by ring, G_add, ih]
    ring

/-- Iterated shift identity for the totative sums. -/
lemma F_mul_add (m h y : ℕ) : F m (h * m + y) =
    h * F m m + m * G m m * h.choose 2 + F m y + h * m * G m y := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show (h + 1) * m + y = m + (h * m + y) by ring, F_add, ih, G_mul_add,
      Nat.choose_succ_succ, Nat.choose_one_right]
    ring

/-- Reflection `k ↦ n - k`: for `n ≥ 2`, `S2 n` is the sum of `n - k` over the totatives
`k ≤ n/2`, so `S2 n + S1 n = n * cnt n`. -/
lemma S2_add_S1 (n : ℕ) (hn : 2 ≤ n) : S2 n + S1 n = n * cnt n := by
  have hS2 : S2 n = ∑ k ∈ (Icc 1 (n / 2)).filter (fun k => Nat.Coprime k n), (n - k) := by
    unfold S2
    refine sum_nbij' (fun k => n - k) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_Icc] at ha ⊢
      obtain ⟨⟨ha1, ha2⟩, ha3, ha4⟩ := ha
      have hne : a ≠ n := by
        rintro rfl
        rw [Nat.coprime_self] at ha4
        omega
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rwa [Nat.coprime_self_sub_left ha2]
    · intro a ha
      simp only [mem_filter, mem_Icc] at ha ⊢
      obtain ⟨⟨ha1, ha2⟩, ha3⟩ := ha
      refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
      rwa [Nat.coprime_self_sub_left (by omega)]
    · intro a ha
      simp only [mem_filter, mem_Icc] at ha
      omega
    · intro a ha
      simp only [mem_filter, mem_Icc] at ha
      omega
    · intro a ha
      simp only [mem_filter, mem_Icc] at ha
      omega
  rw [hS2, S1, cnt, ← sum_add_distrib, sum_congr rfl (g := fun _ => n), sum_const,
    smul_eq_mul, mul_comm]
  intro k hk
  simp only [mem_filter, mem_Icc] at hk
  omega

/-- For `n ≥ 3` the totatives below `n` split into those `≤ n/2` and those `≥ n/2`. -/
lemma filter_range_eq_union (n : ℕ) (hn : 3 ≤ n) :
    (range n).filter (fun k => Nat.Coprime k n) =
      (Icc 1 (n / 2)).filter (fun k => Nat.Coprime k n) ∪
        (Icc 1 n).filter (fun k => n ≤ 2 * k ∧ Nat.Coprime k n) := by
  ext k
  simp only [mem_filter, mem_range, mem_Icc, mem_union]
  constructor
  · rintro ⟨hk, hc⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hc
      omega
    by_cases h2 : n ≤ 2 * k
    · exact Or.inr ⟨⟨by omega, by omega⟩, h2, hc⟩
    · exact Or.inl ⟨⟨by omega, by omega⟩, hc⟩
  · rintro (⟨⟨hk1, hk2⟩, hc⟩ | ⟨⟨hk1, hk2⟩, _, hc⟩)
    · exact ⟨by omega, hc⟩
    · refine ⟨?_, hc⟩
      rcases Nat.lt_or_ge k n with h | h
      · exact h
      · have hkn : k = n := le_antisymm hk2 h
        rw [hkn, Nat.coprime_self] at hc
        omega

/-- For `n ≥ 3` the two halves of the totatives are disjoint. -/
lemma disjoint_halves (n : ℕ) (hn : 3 ≤ n) :
    Disjoint ((Icc 1 (n / 2)).filter (fun k => Nat.Coprime k n))
      ((Icc 1 n).filter (fun k => n ≤ 2 * k ∧ Nat.Coprime k n)) := by
  rw [disjoint_left]
  intro k hk hk'
  simp only [mem_filter, mem_Icc] at hk hk'
  obtain ⟨⟨hk1, hk2⟩, hc⟩ := hk
  obtain ⟨_, hk3, _⟩ := hk'
  have h2k : n = 2 * k := by omega
  have hdvd : k ∣ n := ⟨2, by omega⟩
  have hk_one : k = 1 := by
    have := Nat.Coprime.eq_one_of_dvd hc hdvd
    exact this
  omega

/-- Half-count reflection: `card` of the upper half equals `cnt n`. -/
lemma card_upper (n : ℕ) (hn : 2 ≤ n) :
    ((Icc 1 n).filter (fun k => n ≤ 2 * k ∧ Nat.Coprime k n)).card = cnt n := by
  unfold cnt
  refine card_nbij' (fun k => n - k) (fun k => n - k) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨⟨ha1, ha2⟩, ha3, ha4⟩ := ha
    have hne : a ≠ n := by
      rintro rfl
      rw [Nat.coprime_self] at ha4
      omega
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rwa [Nat.coprime_self_sub_left ha2]
  · intro a ha
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨⟨ha1, ha2⟩, ha3⟩ := ha
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    rwa [Nat.coprime_self_sub_left (by omega)]
  · intro a ha
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha
    simp only
    omega
  · intro a ha
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha
    simp only
    omega

/-- For `n ≥ 3`, the sum of all totatives below `n` is `n * cnt n`. -/
lemma F_self (n : ℕ) (hn : 3 ≤ n) : F n n = n * cnt n := by
  rw [F, ← sum_filter, filter_range_eq_union n hn, sum_union (disjoint_halves n hn)]
  rw [← S2_add_S1 n (by omega), add_comm]
  rfl

/-- For `n ≥ 3`, `φ n = 2 * cnt n` (as the count of totatives below `n`). -/
lemma G_self (n : ℕ) (hn : 3 ≤ n) : G n n = 2 * cnt n := by
  rw [G, ← card_filter, filter_range_eq_union n hn, card_union_of_disjoint (disjoint_halves n hn),
    card_upper n (by omega), cnt]
  ring

/-- For `n ≥ 3`, `φ n = 2 * cnt n`. -/
lemma totient_eq_two_mul_cnt (n : ℕ) (hn : 3 ≤ n) : Nat.totient n = 2 * cnt n := by
  rw [← G_self n hn, G, ← card_filter, Nat.totient]
  congr 1
  exact filter_congr fun k _ => Nat.coprime_comm

/-- Inserting `0` into `Icc 1 x` gives `range (x + 1)`. -/
lemma range_succ_eq_insert (x : ℕ) : range (x + 1) = insert 0 (Icc 1 x) := by
  ext k
  simp only [mem_range, mem_insert, mem_Icc]
  omega

/-- `S1 n` as a totative sum over `range (n/2 + 1)` (the `k = 0` term is `0`). -/
lemma S1_eq_F (n : ℕ) : S1 n = F n (n / 2 + 1) := by
  rw [S1, F, range_succ_eq_insert, sum_insert (by simp), sum_filter]
  simp

/-- `cnt n` as a totative count over `range (n/2 + 1)`, for `n ≥ 2`. -/
lemma cnt_eq_G (n : ℕ) (hn : 2 ≤ n) : cnt n = G n (n / 2 + 1) := by
  rw [cnt, G, range_succ_eq_insert, sum_insert (by simp), card_filter]
  have h0 : ¬ Nat.Coprime 0 n := by
    rw [Nat.coprime_zero_left]
    omega
  simp [h0]

/-- `2 * C(h, 2) + 2 * h = h * (h + 1)`. -/
lemma two_mul_choose_two_add (h : ℕ) : 2 * h.choose 2 + 2 * h = h * (h + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

/-- Block decomposition: for odd `m = 2r+1 ≥ 3`, the totatives of `m` up to `h*m + r`
sum to `S1 m + m * cnt m * h * (h + 1)`. -/
lemma F_block (m r h : ℕ) (hm : m = 2 * r + 1) (hm3 : 3 ≤ m) :
    F m (h * m + (r + 1)) = S1 m + m * cnt m * (h * (h + 1)) := by
  have hr : m / 2 = r := by omega
  have hS1 : S1 m = F m (r + 1) := by rw [S1_eq_F, hr]
  have hc : cnt m = G m (r + 1) := by rw [cnt_eq_G m (by omega), hr]
  rw [F_mul_add, F_self m hm3, G_self m hm3, ← hS1, ← hc, ← two_mul_choose_two_add h]
  ring

/-- If `p ∣ m` then being coprime to `p * m` is the same as being coprime to `m`. -/
lemma F_mul_of_dvd (p m x : ℕ) (hpm : p ∣ m) : F (p * m) x = F m x := by
  unfold F
  refine sum_congr rfl fun k _ => ?_
  have hiff : Nat.Coprime k (p * m) ↔ Nat.Coprime k m := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨fun h => h.2, fun h => ⟨h.coprime_dvd_right hpm, h⟩⟩
  simp only [hiff]

/-- The totatives of `m` below `x` that are multiples of `p` (auxiliary). -/
def D (p m x : ℕ) : ℕ := ∑ k ∈ (range x).filter (fun k => p ∣ k ∧ Nat.Coprime k m), k

/-- Inclusion–exclusion for a new prime `p ∤ m`. -/
lemma F_mul_add_D (p m x : ℕ) (hp : p.Prime) : F (p * m) x + D p m x = F m x := by
  unfold F D
  rw [sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hiff : Nat.Coprime k (p * m) ↔ ¬ p ∣ k ∧ Nat.Coprime k m := by
    rw [Nat.coprime_mul_iff_right, Nat.coprime_comm.trans hp.coprime_iff_not_dvd]
  by_cases h1 : p ∣ k <;> by_cases h2 : Nat.Coprime k m <;> simp [hiff, h1, h2]

/-- The multiples of `p` among the totatives of `m` below `p*y + 1 + i` (`i < p`) are
`p * j` for the totatives `j ≤ y`. -/
lemma D_eq (p m y i : ℕ) (hp : 0 < p) (hpm : Nat.Coprime p m) (hi : i < p) :
    D p m (p * y + 1 + i) = p * F m (y + 1) := by
  have himg : (range (p * y + 1 + i)).filter (fun k => p ∣ k ∧ Nat.Coprime k m) =
      ((range (y + 1)).filter (fun j => Nat.Coprime j m)).image (fun j => p * j) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hk, ⟨j, rfl⟩, hc⟩
      refine ⟨j, ⟨?_, Nat.Coprime.coprime_mul_left hc⟩, rfl⟩
      have hlt : p * j < p * (y + 1) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_left hlt
    · rintro ⟨j, ⟨hj, hc⟩, rfl⟩
      have hle : p * j ≤ p * y := Nat.mul_le_mul_left p (by omega)
      exact ⟨by omega, dvd_mul_right p j, Nat.Coprime.mul_left hpm hc⟩
  rw [D, himg, sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp hab), ← mul_sum,
    F, sum_filter]

/-- Recursion (R1): for odd `p = 2h+1` dividing odd `m = 2r+1 ≥ 3`,
`S1 (p*m) = S1 m + m * cnt m * h * (h+1)`. -/
lemma S1_mul_of_dvd (p m h r : ℕ) (hp : p = 2 * h + 1) (hm : m = 2 * r + 1) (hm3 : 3 ≤ m)
    (hpm : p ∣ m) : S1 (p * m) = S1 m + m * cnt m * (h * (h + 1)) := by
  have e : p * m = 2 * (h * m + r) + 1 := by subst hp hm; ring
  have hdiv : p * m / 2 = h * m + r := by omega
  rw [S1_eq_F, hdiv, F_mul_of_dvd p m _ hpm, add_assoc, F_block m r h hm hm3]

/-- Recursion (R2): for an odd prime `p = 2h+1` not dividing odd `m = 2r+1 ≥ 3`,
`S1 (p*m) + 2h * S1 m = m * cnt m * h * (h+1)`. -/
lemma S1_mul_of_not_dvd (p m h r : ℕ) (hpp : p.Prime) (hp : p = 2 * h + 1)
    (hm : m = 2 * r + 1) (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m) :
    S1 (p * m) + 2 * h * S1 m = m * cnt m * (h * (h + 1)) := by
  have e : p * m = 2 * (h * m + r) + 1 := by subst hp hm; ring
  have hdiv : p * m / 2 = h * m + r := by omega
  have hx : h * m + r + 1 = p * r + 1 + h := by subst hp hm; ring
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hpp).2 hpm
  have hkey := F_mul_add_D p m (h * m + r + 1) hpp
  have hD : D p m (h * m + r + 1) = p * S1 m := by
    rw [hx, D_eq p m r h hpp.pos hcop (by omega), S1_eq_F, show m / 2 = r by omega]
  have hblock := F_block m r h hm hm3
  rw [← add_assoc] at hblock
  rw [hD, hblock] at hkey
  rw [S1_eq_F (p * m), hdiv]
  subst hp
  linarith [hkey]

/-- Recursion (R3): for odd `m = 2r+1 ≥ 3`, `S1 (2*m) + 2 * S1 m = m * cnt m`. -/
lemma S1_two_mul (m r : ℕ) (hm : m = 2 * r + 1) (hm3 : 3 ≤ m) :
    S1 (2 * m) + 2 * S1 m = m * cnt m := by
  have hcop : Nat.Coprime 2 m := by
    rw [Nat.coprime_two_left]
    exact ⟨r, hm⟩
  have hkey := F_mul_add_D 2 m (m + 1) Nat.prime_two
  have hD : D 2 m (m + 1) = 2 * S1 m := by
    rw [show m + 1 = 2 * r + 1 + 1 by omega, D_eq 2 m r 1 (by norm_num) hcop (by norm_num),
      S1_eq_F, show m / 2 = r by omega]
  have hFm : F m (m + 1) = m * cnt m := by
    have hnc : ¬ Nat.Coprime m m := by
      rw [Nat.coprime_self]
      omega
    rw [F, sum_range_succ, ← F, F_self m hm3]
    simp [hnc]
  rw [hD, hFm] at hkey
  rw [S1_eq_F (2 * m), show 2 * m / 2 + 1 = m + 1 by omega]
  exact hkey

/-- For `4 ∣ n`, the involution `k ↦ n/2 - k` on the totatives `≤ n/2` gives
`4 * S1 n = n * cnt n`. -/
lemma four_mul_S1 (n : ℕ) (h4 : 4 ∣ n) (hn : 0 < n) : 4 * S1 n = n * cnt n := by
  obtain ⟨u, rfl⟩ := h4
  set t := 2 * u with ht
  have hn2 : 4 * u / 2 = t := by omega
  have hcop_iff : ∀ a, Nat.Coprime a (4 * u) ↔ Nat.Coprime a t := by
    intro a
    rw [show 4 * u = 2 * t by omega, Nat.coprime_mul_iff_right]
    exact ⟨fun h => h.2, fun h => ⟨h.coprime_dvd_right ⟨u, ht⟩, h⟩⟩
  have hmem : ∀ k, k ∈ (Icc 1 (4 * u / 2)).filter (fun k => Nat.Coprime k (4 * u)) ↔
      1 ≤ k ∧ k < t ∧ Nat.Coprime k t := by
    intro k
    rw [mem_filter, mem_Icc, hn2, hcop_iff]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hc⟩
      refine ⟨hk1, ?_, hc⟩
      rcases Nat.lt_or_ge k t with h | h
      · exact h
      · have hkt : k = t := le_antisymm hk2 h
        rw [hkt, Nat.coprime_self] at hc
        omega
    · rintro ⟨hk1, hk2, hc⟩
      exact ⟨⟨hk1, hk2.le⟩, hc⟩
  have hrefl : S1 (4 * u) = ∑ k ∈ (Icc 1 (4 * u / 2)).filter (fun k => Nat.Coprime k (4 * u)),
      (t - k) := by
    unfold S1
    refine sum_nbij' (fun k => t - k) (fun k => t - k) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [hmem] at ha ⊢
      obtain ⟨ha1, ha2, ha3⟩ := ha
      exact ⟨by omega, by omega, (Nat.coprime_self_sub_left ha2.le).2 ha3⟩
    · intro a ha
      rw [hmem] at ha ⊢
      obtain ⟨ha1, ha2, ha3⟩ := ha
      exact ⟨by omega, by omega, (Nat.coprime_self_sub_left ha2.le).2 ha3⟩
    · intro a ha
      rw [hmem] at ha
      omega
    · intro a ha
      rw [hmem] at ha
      omega
    · intro a ha
      rw [hmem] at ha
      omega
  have htwo : 2 * S1 (4 * u) = t * cnt (4 * u) := by
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    rw [S1, cnt, ← sum_add_distrib, sum_congr rfl (g := fun _ => t), sum_const, smul_eq_mul,
      mul_comm]
    intro k hk
    rw [hmem] at hk
    omega
  rw [ht] at htwo
  linarith [htwo]

/-- For an odd prime `p = 2h+1`, `2 * S1 p = h * (h + 1)` (A066840: `a(p) = (p²-1)/8`). -/
lemma two_mul_S1_prime (p h : ℕ) (hpp : p.Prime) (hp : p = 2 * h + 1) :
    2 * S1 p = h * (h + 1) := by
  have hdiv : p / 2 = h := by omega
  have hfilt : (Icc 1 (p / 2)).filter (fun k => Nat.Coprime k p) = Icc 1 h := by
    rw [hdiv]
    refine filter_true_of_mem fun k hk => ?_
    rw [mem_Icc] at hk
    rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hsum : ∑ k ∈ Icc 1 h, k = ∑ k ∈ range (h + 1), k := by
    rw [range_succ_eq_insert, sum_insert (by simp), zero_add]
  have hgauss := sum_range_id_mul_two (h + 1)
  rw [S1, hfilt, hsum, Nat.add_sub_cancel] at *
  linarith [hgauss]

/-- Prime-power recursion: for an odd prime `p = 2h+1` and `a ≥ 1`,
`S1 (p^a) = S1 p + p * h * (h+1) * t` for some `t`. -/
lemma S1_prime_pow (p h : ℕ) (hpp : p.Prime) (hp : p = 2 * h + 1) (a : ℕ) (ha : 1 ≤ a) :
    ∃ t, S1 (p ^ a) = S1 p + p * (h * (h + 1)) * t := by
  induction a, ha using Nat.le_induction with
  | base => exact ⟨0, by simp⟩
  | succ a ha ih =>
    obtain ⟨t, ht⟩ := ih
    have hodd : Odd (p ^ a) := Odd.pow ⟨h, hp⟩
    obtain ⟨r, hr⟩ := hodd
    have hp3 : 3 ≤ p := by
      have := hpp.two_le
      omega
    have hpa : p ≤ p ^ a := Nat.le_self_pow (by omega) p
    have hrec := S1_mul_of_dvd p (p ^ a) h r hp hr (by omega) (dvd_pow_self p (by omega))
    refine ⟨t + p ^ (a - 1) * cnt (p ^ a), ?_⟩
    have hpow : p ^ a = p * p ^ (a - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [pow_succ', hrec, ht]
    rw [hpow]
    ring

/-- For an odd prime `p` and `a ≥ 1`, `2 * cnt (p^a) = p^(a-1) * (p - 1)`. -/
lemma two_mul_cnt_prime_pow (p a : ℕ) (hpp : p.Prime) (hp3 : 3 ≤ p) (ha : 1 ≤ a) :
    2 * cnt (p ^ a) = p ^ (a - 1) * (p - 1) := by
  have hpa : p ≤ p ^ a := Nat.le_self_pow (by omega) p
  rw [← totient_eq_two_mul_cnt _ (by omega), Nat.totient_prime_pow hpp (by omega)]

/-- If odd `m ≥ 3` has two distinct prime factors then `S1 m` is even. -/
lemma two_dvd_S1_of_two_primes (m : ℕ) (hodd : Odd m) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpm : p ∣ m) (hqm : q ∣ m) : 2 ∣ S1 m := by
  induction m using Nat.strong_induction_on generalizing p with
  | _ m ih =>
    obtain ⟨m', rfl⟩ := hpm
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      simp at hodd
    have hqm' : q ∣ m' := by
      rcases (Nat.Prime.dvd_mul hq).1 hqm with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 h).symm hpq
      · exact h
    have hoddp : Odd p := (Nat.odd_mul.1 hodd).1
    have hoddm' : Odd m' := (Nat.odd_mul.1 hodd).2
    obtain ⟨h, hh⟩ := hoddp
    obtain ⟨r, hr⟩ := hoddm'
    have hq2 : 2 ≤ q := hq.two_le
    have hm'q : q ≤ m' := Nat.le_of_dvd (by omega) hqm'
    have hm3 : 3 ≤ m' := by omega
    have heven : 2 ∣ m' * cnt m' * (h * (h + 1)) :=
      dvd_mul_of_dvd_right (even_iff_two_dvd.1 (Nat.even_mul_succ_self h)) _
    by_cases hpm' : p ∣ m'
    · have hlt : m' < p * m' := by
        have := hp.two_le
        nlinarith
      have hIH := ih m' hlt ⟨r, hr⟩ p hp hpq hpm' hqm'
      rw [S1_mul_of_dvd p m' h r hh hr hm3 hpm']
      exact dvd_add hIH heven
    · have hrec := S1_mul_of_not_dvd p m' h r hp hh hr hm3 hpm'
      rw [← hrec] at heven
      have h2 : 2 ∣ 2 * h * S1 m' := dvd_mul_of_dvd_left (dvd_mul_right 2 h) _
      exact (Nat.dvd_add_left h2).1 heven

/-- If odd `m` has two distinct prime factors then `cnt m` is even (as `4 ∣ φ m`). -/
lemma two_dvd_cnt_of_two_primes (m : ℕ) (hodd : Odd m) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpm : p ∣ m) (hqm : q ∣ m) : 2 ∣ cnt m := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hodd
  obtain ⟨e, w, hpw, hmw⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.one_lt.ne'
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hmw
    exact hpw (hmw ▸ hpm)
  have hqw : q ∣ w := by
    rw [hmw] at hqm
    rcases (Nat.Prime.dvd_mul hq).1 hqm with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)).symm hpq
    · exact h
  have hoddw : Odd w := Odd.of_dvd_nat hodd ⟨p ^ e, by rw [hmw, mul_comm]⟩
  have hoddp : Odd p := Odd.of_dvd_nat hodd hpm
  have hcop : Nat.Coprime (p ^ e) w :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpw)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := hoddp
    omega
  have hw0 : 0 < w := by
    obtain ⟨k, hk⟩ := hoddw
    omega
  have hw3 : 3 ≤ w := by
    have := hq.two_le
    have := Nat.le_of_dvd hw0 hqw
    obtain ⟨k, hk⟩ := hoddw
    omega
  have hpe : p ≤ p ^ e := Nat.le_self_pow he p
  have hm3 : 3 ≤ m := by
    rw [hmw]
    nlinarith
  obtain ⟨x, hx⟩ := Nat.totient_even (n := p ^ e) (by omega)
  obtain ⟨y, hy⟩ := Nat.totient_even (n := w) (by omega)
  have h4 : 4 ∣ Nat.totient m := by
    rw [hmw, Nat.totient_mul hcop, hx, hy]
    exact Dvd.intro (x * y) (by ring)
  rw [totient_eq_two_mul_cnt m hm3] at h4
  omega

/-- `gcd(S1 n, S2 n) = gcd(S1 n, n * cnt n)` for `n ≥ 2`, since `S2 n + S1 n = n * cnt n`. -/
lemma gcd_S1_S2 (n : ℕ) (hn : 2 ≤ n) : Nat.gcd (S1 n) (S2 n) = Nat.gcd (S1 n) (n * cnt n) := by
  rw [← S2_add_S1 n hn, Nat.gcd_add_self_right]

/-- For odd `m ≥ 3`, `cnt (2 * m) = cnt m` (since `φ (2m) = φ m`). -/
lemma cnt_two_mul (m : ℕ) (hodd : Odd m) (hm3 : 3 ≤ m) : cnt (2 * m) = cnt m := by
  have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.2 hodd
  have h1 := totient_eq_two_mul_cnt (2 * m) (by omega)
  have h2 := totient_eq_two_mul_cnt m hm3
  rw [Nat.totient_mul hcop, Nat.totient_two, one_mul, h2] at h1
  omega

/-- A prime not dividing `S` is coprime to every power of it. -/
lemma coprime_pow_of_not_dvd (S r b : ℕ) (hr : r.Prime) (hS : ¬ r ∣ S) :
    Nat.Coprime S (r ^ b) :=
  Nat.Coprime.pow_right b (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hr).2 hS))

/-- Obstruction: an odd `m ≥ 3` that is neither a power of `3` nor a power of `5` has a
common divisor `d > 1` of `S1 m` and `cnt m`. -/
lemma exists_common_dvd (m : ℕ) (hodd : Odd m) (hm3 : 3 ≤ m) (h3 : ∀ a, m ≠ 3 ^ a)
    (h5 : ∀ a, m ≠ 5 ^ a) : ∃ d, 1 < d ∧ d ∣ S1 m ∧ d ∣ cnt m := by
  have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hpm : m.minFac ∣ m := Nat.minFac_dvd m
  by_cases hq : ∃ q, q.Prime ∧ q ∣ m ∧ q ≠ m.minFac
  · obtain ⟨q, hq, hqm, hqp⟩ := hq
    exact ⟨2, by norm_num, two_dvd_S1_of_two_primes m hodd _ q hp hq (Ne.symm hqp) hpm hqm,
      two_dvd_cnt_of_two_primes m hodd _ q hp hq (Ne.symm hqp) hpm hqm⟩
  push Not at hq
  obtain ⟨a, hma⟩ : ∃ a, m = m.minFac ^ a :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun hd hdm => hq _ hd hdm)⟩
  set p := m.minFac with hp_def
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, pow_zero] at hma
      omega
    · exact h0
  obtain ⟨h, hh⟩ := Odd.of_dvd_nat hodd hpm
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp3' : p ≠ 3 := fun hp3 => h3 a (by rw [hma, hp3])
  have hp5' : p ≠ 5 := fun hp5 => h5 a (by rw [hma, hp5])
  obtain ⟨t, ht⟩ := S1_prime_pow p h hp hh a ha
  have hS1p := two_mul_S1_prime p h hp hh
  have hcnt := two_mul_cnt_prime_pow p a hp hp3 ha
  rw [hma]
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (p - 1) with ⟨e, he⟩ | ⟨q, hq, hqd, hqodd⟩
  · -- `p - 1 = 2^e` with `e ≥ 3`, so `8 ∣ p - 1`: everything is even.
    have h8 : 8 ∣ p - 1 := by
      rcases e with _ | _ | _ | e
      · norm_num at he
        omega
      · norm_num at he
        omega
      · norm_num at he
        omega
      · rw [he, pow_add]
        exact Dvd.intro_left (2 ^ e) (by ring)
    have h4h : 4 ∣ h := by omega
    have h4 : 4 ∣ h * (h + 1) := dvd_mul_of_dvd_left h4h _
    have h2p : 2 ∣ S1 p := by omega
    have h2hh : 2 ∣ p * (h * (h + 1)) * t :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_trans (by norm_num) h4) _) _
    refine ⟨2, by norm_num, ?_, ?_⟩
    · rw [ht]
      exact dvd_add h2p h2hh
    · have h4c : 4 ∣ 2 * cnt (p ^ a) := by
        rw [hcnt]
        exact dvd_mul_of_dvd_right (dvd_trans (by norm_num) h8) _
      omega
  · -- an odd prime `q ∣ p - 1` divides everything.
    have hq2 : Nat.Coprime q 2 := Nat.coprime_two_right.2 hqodd
    have hqh : q ∣ h := by
      have : q ∣ 2 * h := by rwa [show p - 1 = 2 * h by omega] at hqd
      exact hq2.dvd_of_dvd_mul_left this
    have hqp : q ∣ S1 p := by
      have : q ∣ 2 * S1 p := by
        rw [hS1p]
        exact dvd_mul_of_dvd_left hqh _
      exact hq2.dvd_of_dvd_mul_left this
    refine ⟨q, hq.one_lt, ?_, ?_⟩
    · rw [ht]
      exact dvd_add hqp
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hqh _) _) _)
    · have : q ∣ 2 * cnt (p ^ a) := by
        rw [hcnt]
        exact dvd_mul_of_dvd_right hqd _
      exact hq2.dvd_of_dvd_mul_left this

/-- For `a ≥ 1`, `S1 (3^a) = 1 + 6t` and `cnt (3^a) = 3^(a-1)`. -/
lemma S1_cnt_three_pow (a : ℕ) (ha : 1 ≤ a) :
    (∃ t, S1 (3 ^ a) = 1 + 6 * t) ∧ cnt (3 ^ a) = 3 ^ (a - 1) := by
  obtain ⟨t, ht⟩ := S1_prime_pow 3 1 Nat.prime_three rfl a ha
  have hS := two_mul_S1_prime 3 1 Nat.prime_three rfl
  have hc := two_mul_cnt_prime_pow 3 a Nat.prime_three le_rfl ha
  refine ⟨⟨t, by omega⟩, by omega⟩

/-- For `a ≥ 1`, `S1 (5^a) = 3 + 30t` and `cnt (5^a) = 2 * 5^(a-1)`. -/
lemma S1_cnt_five_pow (a : ℕ) (ha : 1 ≤ a) :
    (∃ t, S1 (5 ^ a) = 3 + 30 * t) ∧ cnt (5 ^ a) = 2 * 5 ^ (a - 1) := by
  obtain ⟨t, ht⟩ := S1_prime_pow 5 2 (by norm_num) rfl a ha
  have hS := two_mul_S1_prime 5 2 (by norm_num) rfl
  have hc := two_mul_cnt_prime_pow 5 a (by norm_num) (by norm_num) ha
  refine ⟨⟨t, by omega⟩, by omega⟩

/-- The values `n = 3^a` (`a ≥ 1`) satisfy the coprimality. -/
lemma coprime_three_pow (a : ℕ) (ha : 1 ≤ a) :
    Nat.Coprime (S1 (3 ^ a)) (3 ^ a * cnt (3 ^ a)) := by
  obtain ⟨⟨t, ht⟩, hc⟩ := S1_cnt_three_pow a ha
  have h3 : ¬ 3 ∣ S1 (3 ^ a) := by omega
  rw [hc]
  exact Nat.Coprime.mul_right (coprime_pow_of_not_dvd _ 3 a Nat.prime_three h3)
    (coprime_pow_of_not_dvd _ 3 (a - 1) Nat.prime_three h3)

/-- The values `n = 5^a` (`a ≥ 1`) satisfy the coprimality. -/
lemma coprime_five_pow (a : ℕ) (ha : 1 ≤ a) :
    Nat.Coprime (S1 (5 ^ a)) (5 ^ a * cnt (5 ^ a)) := by
  obtain ⟨⟨t, ht⟩, hc⟩ := S1_cnt_five_pow a ha
  have h5 : ¬ 5 ∣ S1 (5 ^ a) := by omega
  have h2 : ¬ 2 ∣ S1 (5 ^ a) := by omega
  rw [hc]
  refine Nat.Coprime.mul_right (coprime_pow_of_not_dvd _ 5 a (by norm_num) h5)
    (Nat.Coprime.mul_right ?_ (coprime_pow_of_not_dvd _ 5 (a - 1) (by norm_num) h5))
  simpa using coprime_pow_of_not_dvd _ 2 1 Nat.prime_two h2

/-- The values `n = 2 * 3^a` (`a ≥ 1`) satisfy the coprimality. -/
lemma coprime_two_mul_three_pow (a : ℕ) (ha : 1 ≤ a) :
    Nat.Coprime (S1 (2 * 3 ^ a)) (2 * 3 ^ a * cnt (2 * 3 ^ a)) := by
  obtain ⟨⟨t, ht⟩, hc⟩ := S1_cnt_three_pow a ha
  have hodd : Odd (3 ^ a) := Odd.pow (by decide)
  obtain ⟨r, hr⟩ := hodd
  have h3a : 3 ≤ 3 ^ a := by
    calc 3 = 3 ^ 1 := rfl
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hrec := S1_two_mul (3 ^ a) r hr h3a
  rw [cnt_two_mul (3 ^ a) ⟨r, hr⟩ h3a, hc]
  rw [hc, ht] at hrec
  have hX3 : 3 ∣ 3 ^ a * 3 ^ (a - 1) := dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _
  have hXodd : Odd (3 ^ a * 3 ^ (a - 1)) := Odd.mul ⟨r, hr⟩ (Odd.pow (by decide))
  obtain ⟨y, hy⟩ := hXodd
  have h3 : ¬ 3 ∣ S1 (2 * 3 ^ a) := by omega
  have h2 : ¬ 2 ∣ S1 (2 * 3 ^ a) := by omega
  refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_
    (coprime_pow_of_not_dvd _ 3 a Nat.prime_three h3))
    (coprime_pow_of_not_dvd _ 3 (a - 1) Nat.prime_three h3)
  simpa using coprime_pow_of_not_dvd _ 2 1 Nat.prime_two h2

/-- For `n = 2m` with odd `m ≥ 3`, a common divisor `d > 1` of `S1 m` and `cnt m` obstructs
coprimality. -/
lemma not_coprime_two_mul (m d : ℕ) (hodd : Odd m) (hm3 : 3 ≤ m) (hd : 1 < d)
    (hdS : d ∣ S1 m) (hdc : d ∣ cnt m) :
    ¬ Nat.Coprime (S1 (2 * m)) (2 * m * cnt (2 * m)) := by
  obtain ⟨r, hr⟩ := hodd
  have hrec := S1_two_mul m r hr hm3
  have hdS2 : d ∣ S1 (2 * m) := by
    have : d ∣ S1 (2 * m) + 2 * S1 m := by
      rw [hrec]
      exact dvd_mul_of_dvd_right hdc _
    exact (Nat.dvd_add_left (dvd_mul_of_dvd_right hdS 2)).1 this
  rw [cnt_two_mul m ⟨r, hr⟩ hm3]
  exact Nat.not_coprime_of_dvd_of_dvd hd hdS2 (dvd_mul_of_dvd_right hdc _)

/-- `n = 2 * 5^a` (`a ≥ 1`) fails: both `S1 n` and `n * cnt n` are even. -/
lemma not_coprime_two_mul_five_pow (a : ℕ) (ha : 1 ≤ a) :
    ¬ Nat.Coprime (S1 (2 * 5 ^ a)) (2 * 5 ^ a * cnt (2 * 5 ^ a)) := by
  obtain ⟨⟨t, ht⟩, hc⟩ := S1_cnt_five_pow a ha
  have hodd : Odd (5 ^ a) := Odd.pow (by decide)
  obtain ⟨r, hr⟩ := hodd
  have h5a : 5 ≤ 5 ^ a := by
    calc 5 = 5 ^ 1 := rfl
      _ ≤ 5 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hrec := S1_two_mul (5 ^ a) r hr (by omega)
  rw [hc] at hrec
  have h2 : 2 ∣ S1 (2 * 5 ^ a) := by
    have : 2 ∣ S1 (2 * 5 ^ a) + 2 * S1 (5 ^ a) := by
      rw [hrec]
      exact Dvd.intro (5 ^ a * 5 ^ (a - 1)) (by ring)
    exact (Nat.dvd_add_left (dvd_mul_right 2 _)).1 this
  exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) h2 (dvd_mul_of_dvd_left (dvd_mul_right 2 _) _)

/-- `4 ∣ n`, `n ≥ 3` and coprimality force `n = 4`. -/
lemma eq_four_of_four_dvd (n : ℕ) (hn : 3 ≤ n) (h4 : 4 ∣ n)
    (hc : Nat.Coprime (S1 n) (n * cnt n)) : n = 4 := by
  have hkey := four_mul_S1 n h4 (by omega)
  rw [← hkey] at hc
  have hS : S1 n = 1 := Nat.Coprime.eq_one_of_dvd hc (dvd_mul_left _ _)
  have hcnt : 1 ≤ cnt n := by
    rw [cnt, Nat.one_le_iff_ne_zero, Ne, card_eq_zero, ← Ne, ← nonempty_iff_ne_empty]
    exact ⟨1, by simp only [mem_filter, mem_Icc]; exact ⟨⟨le_rfl, by omega⟩, Nat.coprime_one_left n⟩⟩
  have hle : n ≤ n * cnt n := Nat.le_mul_of_pos_right n hcnt
  rw [hS] at hkey
  omega

/-- **A341015 conjecture (J. M. Bergot and Robert Israel, Feb 02 2021).**
Let `S1 n` (A066840) be the sum of the `k` with `1 ≤ k ≤ n/2` and `gcd(k, n) = 1`, and
`S2 n` (A124440) the sum of the `k` with `n/2 ≤ k ≤ n` and `gcd(k, n) = 1`. Then
`gcd(S1 n, S2 n) = 1` if and only if `n = 4`, `n = 3^j`, `n = 2 * 3^j` or `n = 5^j` for
some `j ≥ 0`. (The statement also holds at `n = 0`, where both sides are false.) -/
theorem a341015 (n : ℕ) :
    Nat.gcd (S1 n) (S2 n) = 1 ↔
      n = 4 ∨ (∃ j, n = 3 ^ j) ∨ (∃ j, n = 2 * 3 ^ j) ∨ (∃ j, n = 5 ^ j) := by
  rcases lt_or_ge n 3 with hsmall | hn3
  · interval_cases n
    · refine iff_of_false (by decide) ?_
      rintro (h | ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩)
      · omega
      · exact absurd hj.symm (pow_ne_zero j (by norm_num))
      · have := pow_pos (by norm_num : 0 < 3) j
        omega
      · exact absurd hj.symm (pow_ne_zero j (by norm_num))
    · exact iff_of_true (by decide) (Or.inr (Or.inl ⟨0, rfl⟩))
    · exact iff_of_true (by decide) (Or.inr (Or.inr (Or.inl ⟨0, rfl⟩)))
  rw [gcd_S1_S2 n (by omega), ← Nat.coprime_iff_gcd_eq_one]
  constructor
  · intro hc
    obtain ⟨k, hk⟩ | hodd := Nat.even_or_odd n
    · rcases Nat.even_or_odd k with ⟨l, hl⟩ | hko
      · exact Or.inl (eq_four_of_four_dvd n hn3 ⟨l, by omega⟩ hc)
      · have hk3 : 3 ≤ k := by
          obtain ⟨u, hu⟩ := hko
          omega
        have hn2k : n = 2 * k := by omega
        rw [hn2k] at hc ⊢
        by_cases h3 : ∃ a, k = 3 ^ a
        · obtain ⟨a, ha⟩ := h3
          exact Or.inr (Or.inr (Or.inl ⟨a, by rw [ha]⟩))
        by_cases h5 : ∃ a, k = 5 ^ a
        · obtain ⟨a, ha⟩ := h5
          have ha1 : 1 ≤ a := by
            rcases Nat.eq_zero_or_pos a with h0 | h0
            · rw [h0, pow_zero] at ha
              omega
            · exact h0
          rw [ha] at hc
          exact absurd hc (not_coprime_two_mul_five_pow a ha1)
        push Not at h3 h5
        obtain ⟨d, hd, hdS, hdc⟩ := exists_common_dvd k hko hk3 h3 h5
        exact absurd hc (not_coprime_two_mul k d hko hk3 hd hdS hdc)
    · by_cases h3 : ∃ a, n = 3 ^ a
      · exact Or.inr (Or.inl h3)
      by_cases h5 : ∃ a, n = 5 ^ a
      · exact Or.inr (Or.inr (Or.inr h5))
      push Not at h3 h5
      obtain ⟨d, hd, hdS, hdc⟩ := exists_common_dvd n hodd hn3 h3 h5
      exact absurd hc (Nat.not_coprime_of_dvd_of_dvd hd hdS (dvd_mul_of_dvd_right hdc n))
  · rintro (rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩)
    · decide
    · rcases j with _ | j
      · norm_num at hn3
      · exact coprime_three_pow (j + 1) (by omega)
    · rcases j with _ | j
      · norm_num at hn3
      · exact coprime_two_mul_three_pow (j + 1) (by omega)
    · rcases j with _ | j
      · norm_num at hn3
      · exact coprime_five_pow (j + 1) (by omega)

end Candidates.A341015SumGcdNatural
