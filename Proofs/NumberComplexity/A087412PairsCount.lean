/-
# A087412 — Howroyd: a(3^e) = 2*3^e for e > 1

## OEIS source (retrieved with `oeis show A087412`, 2026-10-21)

```
NAME:     a(n) is the number of solutions to x^3 + y^3 == 1 (mod n).
TERMS:    1,2,3,4,5,6,6,8,18,10,11,12,6,12,15,16,17,36,24,20,18,22,23,24,25,
          12,54,24,29,30,33,32,33,34,30,72,24,48,18,40,41,36,33,44,90,...
FORMULA:  From _Andrew Howroyd_, Jul 17 2018: (Start)
          a(p^e) = p^e for p prime and p mod 3 = 2.
          Conjecture: a(3^e) = 2*3^e for e > 1.
          ... (End)
PROGRAM:  (PARI) a(n) = {nb = 0; for (x = 0, n-1, for (y = 0, n-1,
          if (Mod(x^3,n) + Mod(y^3,n) == Mod(1, n), nb++););); nb;}
          \\ _Michel Marcus_, Aug 06 2013
```

## Status

Triage: open in the sense that the entry gives no proof; no literature
source was located (a web search found only the entry itself).  Counts of
points on diagonal cubics modulo prime powers are plausibly classical.
Computation (count table of cubes) confirms `a(3^e) = 2*3^e` for
`e = 2..13` and `a(3) = 3`.

## Result

Proved here (`a_three_pow`, `card_zmod_three_pow`) by an elementary
3-adic argument: modulo 9, exactly one of `x, y` is divisible by 3; for
`x ≡ 0 (mod 3)` the cube map on `y ≡ 1 (mod 3)` hits `1 - x^3 ≡ 1 (mod 9)`
with fibre exactly the class `y ≡ r (mod 3^(e-1))`, i.e. three residues;
by symmetry the case `y ≡ 0 (mod 3)` contributes the same `3^e`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A087412PairsCount

/-! ## Definition layer -/

/-- **A087412.** `a n` is the number of pairs `(x, y)` with `0 ≤ x, y < n` and
`x^3 + y^3 ≡ 1 (mod n)`; this mirrors the entry's PARI program (Michel Marcus).  The right
side `1 % n` makes `a 1 = 1` (every pair is a solution modulo `1`). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter
    (fun p : ℕ × ℕ => (p.1 ^ 3 + p.2 ^ 3) % n = 1 % n)).card

-- Ground truth against the DATA line `1,2,3,4,5,6,6,8,18,10,...`.
example : a 1 = 1 := by decide
-- Boundary `e = 1`: `a 3 = 3`, not `2 * 3 = 6`, so the guard `2 ≤ e` is load-bearing.
example : a 3 = 3 := by decide
example : a 9 = 18 := by decide
example : [a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10]
    = [1, 2, 3, 4, 5, 6, 6, 8, 18, 10] := by
  decide

/-! ## 3-adic helper lemmas -/

/-- **Cube-difference valuation.** For integers `y ≡ z ≡ 1 (mod 3)` and every `k`,
`3^(k+1) ∣ y^3 - z^3` holds exactly when `3^k ∣ y - z`.  Reason:
`y^3 - z^3 = (y - z) (y^2 + y z + z^2)` and `y^2 + y z + z^2 = 3 u` with `u ≡ 1 (mod 3)`. -/
theorem cube_dvd_iff (k : ℕ) (y z : ℤ) (hy : (3 : ℤ) ∣ y - 1) (hz : (3 : ℤ) ∣ z - 1) :
    (3 : ℤ) ^ (k + 1) ∣ y ^ 3 - z ^ 3 ↔ (3 : ℤ) ^ k ∣ y - z := by
  obtain ⟨a, ha⟩ := hy
  obtain ⟨b, hb⟩ := hz
  have hy' : y = 1 + 3 * a := by linarith
  have hz' : z = 1 + 3 * b := by linarith
  set u : ℤ := 1 + 3 * (a + b + a ^ 2 + a * b + b ^ 2) with hu
  have hfac : y ^ 3 - z ^ 3 = (y - z) * u * 3 := by
    rw [hy', hz', hu]; ring
  have hcop : IsCoprime ((3 : ℤ) ^ k) u := by
    apply IsCoprime.pow_left
    refine ⟨-(a + b + a ^ 2 + a * b + b ^ 2), 1, ?_⟩
    rw [hu]; ring
  rw [hfac, pow_succ]
  constructor
  · intro h
    have h' : (3 : ℤ) ^ k ∣ (y - z) * u := (mul_dvd_mul_iff_right (by norm_num)).mp h
    exact hcop.dvd_of_dvd_mul_right h'
  · intro h
    exact mul_dvd_mul_right (dvd_mul_of_dvd_left h u) 3

/-- **Cube roots of `1 (mod 9)` classes.** If `d ≡ 1 (mod 9)` then for every `k` there is
an integer `y ≡ 1 (mod 3)` with `3^(k+2) ∣ y^3 - d`.  Hensel-type lift: from
`y^3 - d = 3^(k+2) m` pass to `y + 2 m 3^(k+1)`. -/
theorem exists_cube_root (d : ℤ) (hd : (9 : ℤ) ∣ d - 1) (k : ℕ) :
    ∃ y : ℤ, (3 : ℤ) ∣ y - 1 ∧ (3 : ℤ) ^ (k + 2) ∣ y ^ 3 - d := by
  induction k with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    rw [show ((3 : ℤ) ^ (0 + 2)) = 9 by norm_num, show (1 : ℤ) ^ 3 - d = -(d - 1) by ring]
    exact hd.neg_right
  | succ k ih =>
    obtain ⟨y, ⟨a, ha⟩, ⟨m, hm⟩⟩ := ih
    refine ⟨y + 2 * m * 3 ^ (k + 1), ⟨a + 2 * m * 3 ^ k, by rw [pow_succ]; linarith⟩, ?_⟩
    refine ⟨m * (1 + 4 * a + 6 * a ^ 2) + 4 * m ^ 2 * y * 3 ^ k + 8 * m ^ 3 * 3 ^ (2 * k), ?_⟩
    have hy' : y = 1 + 3 * a := by linarith
    have hd' : d = y ^ 3 - 3 ^ (k + 2) * m := by linarith
    rw [hd']
    subst hy'
    ring

/-- If `y^3 ≡ 1 (mod 3)` then `y ≡ 1 (mod 3)` (Fermat in `ZMod 3`). -/
theorem three_dvd_sub_one_of_cube (y : ℤ) (h : (3 : ℤ) ∣ y ^ 3 - 1) : (3 : ℤ) ∣ y - 1 := by
  have h' : ((y ^ 3 - 1 : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  have goal : ((y - 1 : ℤ) : ZMod 3) = 0 := by
    push_cast at h' ⊢
    generalize (y : ZMod 3) = t at h' ⊢
    revert t h'
    decide
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at goal
  exact_mod_cast goal

/-- Normalised cube root: for `d ≡ 1 (mod 9)` there is a natural `r < 3^(k+1)` with
`r ≡ 1 (mod 3)` and `r^3 ≡ d (mod 3^(k+2))`. -/
theorem exists_nat_cube_root (k : ℕ) (d : ℤ) (hd : (9 : ℤ) ∣ d - 1) :
    ∃ r : ℕ, r < 3 ^ (k + 1) ∧ (3 : ℤ) ∣ (r : ℤ) - 1 ∧ (3 : ℤ) ^ (k + 2) ∣ (r : ℤ) ^ 3 - d := by
  obtain ⟨y, hy1, hyd⟩ := exists_cube_root d hd k
  have hM : (0 : ℤ) < 3 ^ (k + 1) := by positivity
  have hr : ((y % 3 ^ (k + 1)).toNat : ℤ) = y % 3 ^ (k + 1) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  have hdiff : (3 : ℤ) ^ (k + 1) ∣ ((y % 3 ^ (k + 1)).toNat : ℤ) - y := by
    rw [hr, Int.emod_def]
    exact ⟨-(y / 3 ^ (k + 1)), by ring⟩
  have h3M : (3 : ℤ) ∣ 3 ^ (k + 1) := dvd_pow_self 3 (by omega)
  have hr1 : (3 : ℤ) ∣ ((y % 3 ^ (k + 1)).toNat : ℤ) - 1 := by
    have := dvd_add (h3M.trans hdiff) hy1
    rwa [sub_add_sub_cancel] at this
  refine ⟨(y % 3 ^ (k + 1)).toNat, ?_, hr1, ?_⟩
  · have hlt : y % 3 ^ (k + 1) < 3 ^ (k + 1) := Int.emod_lt_of_pos _ hM
    rw [← hr] at hlt
    exact_mod_cast hlt
  · have hcube := (cube_dvd_iff (k + 1) _ y hr1 hy1).mpr hdiff
    have := dvd_add hcube hyd
    rwa [sub_add_sub_cancel] at this

/-- **Fibre count.** For `x ≡ 0 (mod 3)`, exactly three residues `y < 3^(k+2)` satisfy
`x^3 + y^3 ≡ 1 (mod 3^(k+2))`: namely the residues `y ≡ r (mod 3^(k+1))` for the cube root
`r` of `1 - x^3`. -/
theorem fibre_card (k x : ℕ) (hx : x % 3 = 0) :
    ((Finset.range (3 ^ (k + 2))).filter (fun y => (x ^ 3 + y ^ 3) % 3 ^ (k + 2) = 1)).card
      = 3 := by
  set d : ℤ := 1 - (x : ℤ) ^ 3 with hd_def
  have hd : (9 : ℤ) ∣ d - 1 := by
    obtain ⟨t, rfl⟩ : 3 ∣ x := Nat.dvd_of_mod_eq_zero hx
    exact ⟨-(3 * (t : ℤ) ^ 3), by rw [hd_def]; push_cast; ring⟩
  obtain ⟨r, hrM, hr1, hrd⟩ := exists_nat_cube_root k d hd
  have hMpos : 0 < 3 ^ (k + 1) := by positivity
  have h3M : (3 : ℤ) ∣ 3 ^ (k + 1) := dvd_pow_self 3 (by omega)
  have h3N : (3 : ℤ) ∣ 3 ^ (k + 2) := dvd_pow_self 3 (by omega)
  have key : ∀ y : ℕ, (x ^ 3 + y ^ 3) % 3 ^ (k + 2) = 1 ↔ y % 3 ^ (k + 1) = r := by
    intro y
    have h1N : 1 % 3 ^ (k + 2) = 1 := Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) (by norm_num))
    have hstep1 : (x ^ 3 + y ^ 3) % 3 ^ (k + 2) = 1 ↔ (3 : ℤ) ^ (k + 2) ∣ (y : ℤ) ^ 3 - d := by
      have hmod : (x ^ 3 + y ^ 3) % 3 ^ (k + 2) = 1 ↔ x ^ 3 + y ^ 3 ≡ 1 [MOD 3 ^ (k + 2)] := by
        unfold Nat.ModEq; rw [h1N]
      rw [hmod, Nat.modEq_iff_dvd, hd_def]
      push_cast
      rw [show (y : ℤ) ^ 3 - (1 - (x : ℤ) ^ 3) = -((1 : ℤ) - ((x : ℤ) ^ 3 + (y : ℤ) ^ 3)) by ring,
        dvd_neg]
    have hstep2 : (3 : ℤ) ^ (k + 2) ∣ (y : ℤ) ^ 3 - d ↔ (3 : ℤ) ^ (k + 1) ∣ (y : ℤ) - r := by
      rw [show (y : ℤ) ^ 3 - d = ((y : ℤ) ^ 3 - (r : ℤ) ^ 3) + ((r : ℤ) ^ 3 - d) by ring,
        dvd_add_left hrd]
      constructor
      · intro h
        have hy1 : (3 : ℤ) ∣ (y : ℤ) - 1 := by
          apply three_dvd_sub_one_of_cube
          have := dvd_add (h3N.trans (dvd_add h hrd)) ((show (3 : ℤ) ∣ 9 by norm_num).trans hd)
          rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
        exact (cube_dvd_iff (k + 1) _ _ hy1 hr1).mp h
      · intro h
        have hy1 : (3 : ℤ) ∣ (y : ℤ) - 1 := by
          have := dvd_add (h3M.trans h) hr1
          rwa [sub_add_sub_cancel] at this
        exact (cube_dvd_iff (k + 1) _ _ hy1 hr1).mpr h
    have hstep3 : (3 : ℤ) ^ (k + 1) ∣ (y : ℤ) - r ↔ y % 3 ^ (k + 1) = r := by
      have hc : ((3 ^ (k + 1) : ℕ) : ℤ) = (3 : ℤ) ^ (k + 1) := by push_cast; rfl
      rw [← hc, ← Nat.modEq_iff_dvd]
      unfold Nat.ModEq
      rw [Nat.mod_eq_of_lt hrM]
      exact eq_comm
    rw [hstep1, hstep2, hstep3]
  have himage : (Finset.range (3 ^ (k + 2))).filter (fun y => (x ^ 3 + y ^ 3) % 3 ^ (k + 2) = 1)
      = (Finset.range 3).image (fun j => r + j * 3 ^ (k + 1)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, key]
    have hN : 3 ^ (k + 2) = 3 * 3 ^ (k + 1) := by ring
    constructor
    · rintro ⟨hy, hyr⟩
      refine ⟨y / 3 ^ (k + 1), ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hMpos]; omega
      · rw [← hyr]; exact Nat.mod_add_div' y _
    · rintro ⟨j, hj, rfl⟩
      constructor
      · have : j * 3 ^ (k + 1) ≤ 2 * 3 ^ (k + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrM]
  rw [himage, Finset.card_image_of_injective, Finset.card_range]
  intro i j hij
  simp only at hij
  exact Nat.eq_of_mul_eq_mul_right hMpos (by omega)

/-- There are `3^(k+1)` multiples of `3` below `3^(k+2)`. -/
theorem card_mod_three_eq_zero (k : ℕ) :
    ((Finset.range (3 ^ (k + 2))).filter (fun x => x % 3 = 0)).card = 3 ^ (k + 1) := by
  have himage : (Finset.range (3 ^ (k + 2))).filter (fun x => x % 3 = 0)
      = (Finset.range (3 ^ (k + 1))).image (fun t => 3 * t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    have hN : 3 ^ (k + 2) = 3 * 3 ^ (k + 1) := by ring
    constructor
    · rintro ⟨hx, hx3⟩
      exact ⟨x / 3, by omega, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      omega
  rw [himage, Finset.card_image_of_injective _ (fun i j hij => by simpa using hij),
    Finset.card_range]

/-- **Residues mod 3.** If `x^3 + y^3 ≡ 1 (mod 9)` then exactly one of `x, y` is divisible
by `3`.  (Modulo `3` one gets `x + y ≡ 1`; the case `x ≡ y ≡ 2 (mod 3)` gives
`x^3 + y^3 ≡ -2 (mod 9)`.) -/
theorem mod_three_cases (x y : ℕ) (h : (x ^ 3 + y ^ 3) % 9 = 1) :
    (x % 3 = 0 ∨ y % 3 = 0) ∧ ¬ (x % 3 = 0 ∧ y % 3 = 0) := by
  have h' : ((x % 9) ^ 3 % 9 + (y % 9) ^ 3 % 9) % 9 = 1 := by
    rw [← Nat.pow_mod, ← Nat.pow_mod, ← Nat.add_mod]; exact h
  have hx : x % 3 = x % 9 % 3 := (Nat.mod_mod_of_dvd x (by norm_num)).symm
  have hy : y % 3 = y % 9 % 3 := (Nat.mod_mod_of_dvd y (by norm_num)).symm
  have hx9 : x % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hy9 : y % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have htable : ∀ a < 9, ∀ b < 9, (a ^ 3 % 9 + b ^ 3 % 9) % 9 = 1 →
      (a % 3 = 0 ∨ b % 3 = 0) ∧ ¬ (a % 3 = 0 ∧ b % 3 = 0) := by decide
  rw [hx, hy]
  exact htable _ hx9 _ hy9 h'

/-- The solutions modulo `3^(k+2)` with `x ≡ 0 (mod 3)` number exactly `3^(k+2)`:
`3^(k+1)` choices of `x`, each with three `y` by `fibre_card`. -/
theorem card_first_zero (k : ℕ) :
    ((Finset.range (3 ^ (k + 2)) ×ˢ Finset.range (3 ^ (k + 2))).filter
      (fun p : ℕ × ℕ => p.1 % 3 = 0 ∧ (p.1 ^ 3 + p.2 ^ 3) % 3 ^ (k + 2) = 1)).card
      = 3 ^ (k + 2) := by
  rw [Finset.card_filter, Finset.sum_product]
  have hinner : ∀ x ∈ Finset.range (3 ^ (k + 2)),
      (∑ y ∈ Finset.range (3 ^ (k + 2)),
        if x % 3 = 0 ∧ (x ^ 3 + y ^ 3) % 3 ^ (k + 2) = 1 then 1 else 0)
        = if x % 3 = 0 then 3 else 0 := by
    intro x _
    split_ifs with hx
    · refine Eq.trans ?_ (fibre_card k x hx)
      rw [Finset.card_filter]
      simp only [hx, true_and]
    · exact Finset.sum_eq_zero (fun y _ => if_neg (fun h => hx h.1))
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul,
    card_mod_three_eq_zero]
  ring

/-! ## The conjecture -/

/-- **Howroyd's conjecture (A087412, Andrew Howroyd, Jul 17 2018), proved.**

Verbatim: "Conjecture: a(3^e) = 2*3^e for e > 1."

For every `e ≥ 2`, the number of pairs `(x, y)` of residues modulo `3^e` with
`x^3 + y^3 ≡ 1 (mod 3^e)` equals `2 * 3^e`.  The guard `2 ≤ e` is load-bearing:
`a 3 = 3 ≠ 6` (and `a 1 = 1 ≠ 2`). -/
theorem a_three_pow (e : ℕ) (he : 2 ≤ e) : a (3 ^ e) = 2 * 3 ^ e := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  have h1N : 1 % 3 ^ (k + 2) = 1 := Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) (by norm_num))
  have h9 : 9 ∣ 3 ^ (k + 2) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]; exact pow_dvd_pow 3 (by omega)
  unfold a
  rw [h1N]
  set S := (Finset.range (3 ^ (k + 2)) ×ˢ Finset.range (3 ^ (k + 2))).filter
    (fun p : ℕ × ℕ => (p.1 ^ 3 + p.2 ^ 3) % 3 ^ (k + 2) = 1) with hS
  have hcases : ∀ p ∈ S, (p.1 % 3 = 0 ∨ p.2 % 3 = 0) ∧ ¬ (p.1 % 3 = 0 ∧ p.2 % 3 = 0) := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    apply mod_three_cases
    rw [← Nat.mod_mod_of_dvd _ h9, hp.2]
  have hA : (S.filter (fun p => p.1 % 3 = 0)).card = 3 ^ (k + 2) := by
    have hfilt : S.filter (fun p => p.1 % 3 = 0)
        = (Finset.range (3 ^ (k + 2)) ×ˢ Finset.range (3 ^ (k + 2))).filter
          (fun p : ℕ × ℕ => p.1 % 3 = 0 ∧ (p.1 ^ 3 + p.2 ^ 3) % 3 ^ (k + 2) = 1) := by
      ext p
      simp only [hS, Finset.mem_filter]
      tauto
    rw [hfilt, card_first_zero k]
  have hB : (S.filter (fun p => ¬ p.1 % 3 = 0)).card = 3 ^ (k + 2) := by
    have hcongr : S.filter (fun p => ¬ p.1 % 3 = 0) = S.filter (fun p => p.2 % 3 = 0) := by
      refine Finset.filter_congr (fun p hp => ?_)
      have := hcases p hp
      tauto
    rw [hcongr, ← hA]
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ (fun p _ => rfl) (fun p _ => rfl)
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, hS, Finset.mem_product, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, by rw [add_comm]; exact hp.1.2⟩, hp.2⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, hS, Finset.mem_product, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, by rw [add_comm]; exact hp.1.2⟩, hp.2⟩
  rw [← Finset.card_filter_add_card_filter_not (fun p : ℕ × ℕ => p.1 % 3 = 0), hA, hB]
  ring

/-- **Fidelity bridge.** For `n ≠ 0`, `a n` is the number of pairs `(x, y) ∈ (ℤ/nℤ)^2`
with `x^3 + y^3 = 1`. -/
theorem a_eq_card_zmod (n : ℕ) [NeZero n] :
    a n = (Finset.univ.filter (fun p : ZMod n × ZMod n => p.1 ^ 3 + p.2 ^ 3 = 1)).card := by
  unfold a
  refine Finset.card_nbij' (fun p => ((p.1 : ZMod n), (p.2 : ZMod n)))
    (fun q => (q.1.val, q.2.val)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have h := (ZMod.natCast_eq_natCast_iff' (p.1 ^ 3 + p.2 ^ 3) 1 n).mpr hp.2
    push_cast at h
    exact h
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_range] at hq ⊢
    refine ⟨⟨ZMod.val_lt q.1, ZMod.val_lt q.2⟩, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    simpa only [ZMod.natCast_val, ZMod.cast_id', id] using hq
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    ext
    · exact ZMod.val_cast_of_lt hp.1.1
    · exact ZMod.val_cast_of_lt hp.1.2
  · intro q _
    ext
    · exact ZMod.natCast_zmod_val q.1
    · exact ZMod.natCast_zmod_val q.2

/-- **Howroyd's conjecture, `ZMod` form.** For `e ≥ 2` the curve `x^3 + y^3 = 1` has
exactly `2 * 3^e` points over `ℤ/3^eℤ`. -/
theorem card_zmod_three_pow (e : ℕ) (he : 2 ≤ e) :
    (Finset.univ.filter (fun p : ZMod (3 ^ e) × ZMod (3 ^ e) => p.1 ^ 3 + p.2 ^ 3 = 1)).card
      = 2 * 3 ^ e := by
  rw [← a_eq_card_zmod, a_three_pow e he]

-- Satisfiability of the hypothesis `2 ≤ e` at `e = 2`: `a 9 = 18 = 2 * 9`.
example : a (3 ^ 2) = 2 * 3 ^ 2 := a_three_pow 2 le_rfl

end Candidates.A087412PairsCount
