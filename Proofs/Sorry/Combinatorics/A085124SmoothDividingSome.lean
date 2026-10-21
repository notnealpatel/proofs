/-
# A085124 — Bala/Israel: 7-smooth `n` with `10 ∤ n` has a multiple whose digit product is a positive multiple of `n`

## OEIS source (retrieved with `oeis show A085124`, 2026-10-21)

```
NAME:     Smallest multiple of n whose digital product is also a positive
          multiple of n, or 0 if no such number exists.
TERMS:    1,2,3,4,5,6,7,8,9,0,0,168,0,378,135,48,0,36,0,0,273,0,0,168,525,0,
          999,476,0,0,0,288,0,0,175,1296,0,0,0,0,0,378,0,0,495,0,0,384,3577,...
COMMENT:  a(n) = 0 if n is not a term of A002473 (i.e., not a 7-smooth number).
COMMENT:  a(n) = 0 if n is a multiple of 10.
COMMENT:  Conjecture: otherwise, a(n) is positive.
PROGRAM:  (Maple) ... # _Robert Israel_, Dec 28 2025
```

The conjecture line carries no separate signature in the entry; the
surrounding comments and the Maple program are by Robert Israel
(Dec 28 2025).

## Status

Triage status: open (no proof in the entry or the literature as far as the
triage could tell; the Israel b-file to 10000 is consistent).  A brute-force
re-check (2026-10-21) found a witness for every 7-smooth `n ≤ 30000` with
`10 ∤ n` (264 values), agreeing with the DATA line.

This module proves the conjecture (`a085124_conjecture`) by an explicit
concatenation construction:

* write `n = p ^ e * Q` with `p ∈ {2, 5}` and `gcd(Q, 10) = 1`, and let
  `T = φ(Q)`, so `10 ^ T ≡ 1 (mod Q)`;
* the low `e * T` digits form a zero-free block divisible by `p ^ (e * T)`
  (digit-by-digit 2-adic / 5-adic lifting);
* a block of digits in `{2,3,5,7}` with product exactly `n`, padded with
  `1`s to a multiple of `T`, supplies the digit product;
* `k` blocks `[2,1,…,1]` and `k (Q - 1)` blocks `[1,…,1]` (each of length
  `T`) shift the residue mod `Q` by exactly `k`, which fixes divisibility
  by `Q`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A085124SmoothDividingSome

/-! ## Definition layer -/

/-- The decimal digit product ("digital product") of `m`: the product of the
base-10 digits of `m`.  `Nat.digits 10 0 = []`, so `digitProd 0 = 1`; the
conjecture below always requires `0 < m`, so this junk value is never used. -/
def digitProd (m : ℕ) : ℕ := (Nat.digits 10 m).prod

-- Ground truth against the DATA line: a(12) = 168, a(16) = 48, a(49) = 3577.
example : digitProd 168 = 48 := by norm_num [digitProd]
example : digitProd 48 = 32 := by norm_num [digitProd]
example : digitProd 3577 = 735 := by norm_num [digitProd]
example : 12 ∣ 168 ∧ 12 ∣ digitProd 168 := by norm_num [digitProd]
example : 49 ∣ 3577 ∧ 49 ∣ digitProd 3577 := by norm_num [digitProd]
example : 16 ∣ 48 ∧ 16 ∣ digitProd 48 := by norm_num [digitProd]

/-! ## Helper lemmas -/

/-- Every `7`-smooth positive `n` is the product of a list of decimal digits in `[1, 9]`
(peel off `minFac n ∈ {2, 3, 5, 7}` and recurse). -/
theorem exists_digitList_prod_eq (n : ℕ) (hn : n ≠ 0)
    (hsmooth : ∀ p, p.Prime → p ∣ n → p ≤ 7) :
    ∃ L : List ℕ, (∀ x ∈ L, 1 ≤ x ∧ x ≤ 9) ∧ L.prod = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n = 1
    · exact ⟨[], by simp, by simp [h1]⟩
    · have hp : n.minFac.Prime := Nat.minFac_prime h1
      have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hle : n.minFac ≤ 7 := hsmooth _ hp hdvd
      have h2 : 2 ≤ n.minFac := hp.two_le
      obtain ⟨c, hc⟩ := hdvd
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp at hc
        exact hn hc
      have hclt : c < n := by
        rw [hc]
        have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
        nlinarith
      obtain ⟨L, hL, hLprod⟩ := ih c hclt hc0 (fun p hpp hpc =>
        hsmooth p hpp (hc ▸ Dvd.dvd.mul_left hpc _))
      refine ⟨n.minFac :: L, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hL x hx
      · rw [List.prod_cons, hLprod, ← hc]

/-- Digit choice for the `p`-adic lifting: for `p ∈ {2, 5}`, `c` not divisible by
`p` and any `w`, some digit `d ∈ [1, 9]` makes `w + c * d` divisible by `p`. -/
theorem exists_digit_dvd (p : ℕ) (hp : p = 2 ∨ p = 5) (w c : ℕ) (hc : ¬ p ∣ c) :
    ∃ d, 1 ≤ d ∧ d ≤ 9 ∧ p ∣ w + c * d := by
  have key : ∀ a < p, ∀ b < p, b ≠ 0 → ∃ d < 10, 1 ≤ d ∧ (a + b * d) % p = 0 := by
    rcases hp with rfl | rfl <;> decide
  have hcp : c % p ≠ 0 := fun h => hc (Nat.dvd_of_mod_eq_zero h)
  have hp0 : 0 < p := by omega
  obtain ⟨d, hd10, hd1, hd⟩ := key (w % p) (Nat.mod_lt _ hp0) (c % p) (Nat.mod_lt _ hp0) hcp
  refine ⟨d, hd1, by omega, Nat.dvd_of_mod_eq_zero ?_⟩
  have hmod : w + c * d ≡ w % p + c % p * d [MOD p] :=
    Nat.ModEq.add (Nat.mod_modEq w p).symm ((Nat.mod_modEq c p).symm.mul_right d)
  rw [hmod]
  exact hd

/-- Zero-free `p`-adic block: for `p ∈ {2, 5}` and every `k` there is a list of
`k` digits in `[1, 9]` whose value is divisible by `p ^ k`. -/
theorem exists_low_block (p : ℕ) (hp : p = 2 ∨ p = 5) (k : ℕ) :
    ∃ S : List ℕ, S.length = k ∧ (∀ x ∈ S, 1 ≤ x ∧ x ≤ 9) ∧ p ^ k ∣ Nat.ofDigits 10 S := by
  induction k with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨S, hlen, hS, w, hw⟩ := ih
    obtain ⟨q, hq, hpq⟩ : ∃ q, 10 = p * q ∧ ¬ p ∣ q ^ k := by
      rcases hp with rfl | rfl
      · refine ⟨5, rfl, fun h => ?_⟩
        have := (Nat.prime_two.dvd_of_dvd_pow h)
        omega
      · refine ⟨2, rfl, fun h => ?_⟩
        have := (Nat.prime_five.dvd_of_dvd_pow h)
        omega
    obtain ⟨d, hd1, hd9, hd⟩ := exists_digit_dvd p hp w (q ^ k) hpq
    refine ⟨S ++ [d], by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hS x hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨hd1, hd9⟩
    · rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hw, hlen, hq, mul_pow]
      obtain ⟨t, ht⟩ := hd
      refine ⟨t, ?_⟩
      calc p ^ k * w + p ^ k * q ^ k * d = p ^ k * (w + q ^ k * d) := by ring
        _ = p ^ (k + 1) * t := by rw [ht]; ring

/-- Residue of a repeated block: if `10 ^ |B| ≡ 1 (mod Q)`, then `j` concatenated
copies of `B` have value `≡ j * value(B) (mod Q)`. -/
theorem ofDigits_flatten_replicate (Q : ℕ) (B : List ℕ)
    (hB : (10 : ZMod Q) ^ B.length = 1) (j : ℕ) :
    ((Nat.ofDigits 10 (List.replicate j B).flatten : ℕ) : ZMod Q) =
      (j : ZMod Q) * (Nat.ofDigits 10 B : ℕ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hB, ih]
    push_cast
    ring

/-- Core construction: if `n = p ^ e * Q` with `p ∈ {2, 5}`, `gcd(10, Q) = 1`, and
`Y₀` is a zero-free digit list with product `n`, then there is a nonempty
zero-free digit list `M` with `n ∣ ofDigits 10 M` and `n ∣ M.prod`. -/
theorem exists_list_of_decomp (p e Q n : ℕ) (hp : p = 2 ∨ p = 5) (hQ : Nat.Coprime 10 Q)
    (hn : n = p ^ e * Q) (Y₀ : List ℕ) (hY₀ : ∀ x ∈ Y₀, 1 ≤ x ∧ x ≤ 9)
    (hY₀prod : Y₀.prod = n) :
    ∃ M : List ℕ, M ≠ [] ∧ (∀ x ∈ M, 1 ≤ x ∧ x ≤ 9) ∧
      n ∣ Nat.ofDigits 10 M ∧ n ∣ M.prod := by
  have hQpos : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with rfl | h
    · simp at hQ
    · exact h
  set T := Nat.totient Q with hTdef
  have hT1 : 1 ≤ T := Nat.totient_pos.mpr hQpos
  have hTmod : (10 : ZMod Q) ^ T = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient hQ)
    push_cast at h
    exact h
  have hTmul : ∀ l, (10 : ZMod Q) ^ (T * l) = 1 := fun l => by rw [pow_mul, hTmod, one_pow]
  obtain ⟨S, hSlen, hS, hSdvd⟩ := exists_low_block p hp (e * T)
  let Y : List ℕ := Y₀ ++ List.replicate (T * Y₀.length - Y₀.length) 1
  have hYlen : Y.length = T * Y₀.length := by
    have hle : Y₀.length ≤ T * Y₀.length := Nat.le_mul_of_pos_left _ hT1
    simp only [Y, List.length_append, List.length_replicate]
    omega
  have hYprod : Y.prod = n := by simp [Y, hY₀prod]
  let B₁ : List ℕ := List.replicate T 1
  let B₂ : List ℕ := 2 :: List.replicate (T - 1) 1
  have hB₁len : B₁.length = T := List.length_replicate
  have hB₂len : B₂.length = T := by
    simp only [B₂, List.length_cons, List.length_replicate]
    omega
  have hB₂val : Nat.ofDigits 10 B₂ = Nat.ofDigits 10 B₁ + 1 := by
    have hB₁ : B₁ = 1 :: List.replicate (T - 1) 1 := by
      simp only [B₁]
      rw [← List.replicate_succ]
      congr 1
      omega
    rw [hB₁]
    simp only [B₂, Nat.ofDigits_cons]
    ring
  set s := Nat.ofDigits 10 S with hs
  set y := Nat.ofDigits 10 Y with hy
  set b := Nat.ofDigits 10 B₁ with hb
  set k := Q - (s + y) % Q with hk
  have hmodlt : (s + y) % Q < Q := Nat.mod_lt (s + y) hQpos
  have hk1 : 1 ≤ k := by omega
  let Z₂ : List ℕ := (List.replicate k B₂).flatten
  let Z₁ : List ℕ := (List.replicate (k * (Q - 1)) B₁).flatten
  have hZ₂len : Z₂.length = T * k := by simp [Z₂, hB₂len, mul_comm]
  have hZ₂val : ((Nat.ofDigits 10 Z₂ : ℕ) : ZMod Q) = (k : ZMod Q) * ((b : ℕ) + 1) := by
    rw [ofDigits_flatten_replicate Q B₂ (by rw [hB₂len]; exact hTmod) k, hB₂val]
    push_cast
    ring
  have hZ₁val : ((Nat.ofDigits 10 Z₁ : ℕ) : ZMod Q) = -((k : ZMod Q) * (b : ℕ)) := by
    rw [ofDigits_flatten_replicate Q B₁ (by rw [hB₁len]; exact hTmod) _]
    rw [Nat.cast_mul, Nat.cast_sub hQpos, ZMod.natCast_self]
    ring
  let M : List ℕ := S ++ (Y ++ (Z₂ ++ Z₁))
  have hMval : ((Nat.ofDigits 10 M : ℕ) : ZMod Q) = (s : ZMod Q) + y + k := by
    simp only [M, Nat.ofDigits_append, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, hSlen, hYlen, hZ₂len, hTmul, hZ₂val, hZ₁val]
    rw [mul_comm e T, hTmul]
    ring
  have hkcast : (k : ZMod Q) = -((s : ZMod Q) + y) := by
    rw [hk, Nat.cast_sub hmodlt.le, ZMod.natCast_self, ZMod.natCast_mod]
    push_cast
    ring
  have hQdvd : Q ∣ Nat.ofDigits 10 M := by
    rw [← ZMod.natCast_eq_zero_iff, hMval, hkcast]
    ring
  have hp10 : p ∣ 10 := by rcases hp with rfl | rfl <;> norm_num
  have hele : e ≤ e * T := Nat.le_mul_of_pos_right e hT1
  have hPdvd : p ^ e ∣ Nat.ofDigits 10 M := by
    simp only [M, Nat.ofDigits_append, hSlen]
    refine Nat.dvd_add ((pow_dvd_pow p hele).trans hSdvd) (Dvd.dvd.mul_right ?_ _)
    exact (pow_dvd_pow_of_dvd hp10 e).trans (pow_dvd_pow 10 hele)
  have hcop : Nat.Coprime (p ^ e) Q :=
    Nat.Coprime.pow_left e (Nat.Coprime.coprime_dvd_left hp10 hQ)
  have hdig : ∀ x ∈ M, 1 ≤ x ∧ x ≤ 9 := by
    intro x hx
    simp only [M, Z₂, Z₁, List.mem_append] at hx
    rcases hx with hx | hx | hx | hx
    · exact hS x hx
    · simp only [Y, List.mem_append, List.mem_replicate] at hx
      rcases hx with hx | ⟨_, rfl⟩
      · exact hY₀ x hx
      · omega
    · simp only [List.mem_flatten, List.mem_replicate] at hx
      obtain ⟨l, ⟨_, rfl⟩, hxl⟩ := hx
      simp only [B₂, List.mem_cons, List.mem_replicate] at hxl
      omega
    · simp only [List.mem_flatten, List.mem_replicate] at hx
      obtain ⟨l, ⟨_, rfl⟩, hxl⟩ := hx
      simp only [B₁, List.mem_replicate] at hxl
      omega
  have hMne : M ≠ [] := by
    intro hM
    have hlen := congrArg List.length hM
    simp only [M, List.length_append, hZ₂len, List.length_nil] at hlen
    have : 1 ≤ T * k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  refine ⟨M, hMne, hdig, hn ▸ hcop.mul_dvd_of_dvd_of_dvd hPdvd hQdvd, ?_⟩
  refine Dvd.intro_left (S.prod * (Z₂ ++ Z₁).prod) ?_
  simp only [M, List.prod_append, hYprod]
  ring

/-- Converting a nonempty zero-free digit list into a number: if `M` is a
nonempty list of digits in `[1, 9]` with `n ∣ ofDigits 10 M` and
`n ∣ M.prod`, then `m = ofDigits 10 M` is a witness for `n`. -/
theorem witness_of_list (n : ℕ) (M : List ℕ) (hMne : M ≠ [])
    (hdig : ∀ x ∈ M, 1 ≤ x ∧ x ≤ 9) (hdvd : n ∣ Nat.ofDigits 10 M) (hprod : n ∣ M.prod) :
    ∃ m, 0 < m ∧ n ∣ m ∧ 0 < digitProd m ∧ n ∣ digitProd m := by
  have hdigits : Nat.digits 10 (Nat.ofDigits 10 M) = M :=
    Nat.digits_ofDigits 10 (by norm_num) M (fun l hl => by have := hdig l hl; omega)
      (fun h => by have := hdig _ (List.getLast_mem h); omega)
  refine ⟨Nat.ofDigits 10 M, ?_, hdvd, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.ofDigits 10 M) with h | h
    · rw [h, Nat.digits_zero] at hdigits
      exact absurd hdigits.symm hMne
    · exact h
  · rw [digitProd, hdigits]
    exact List.prod_pos (fun x hx => (hdig x hx).1)
  · rw [digitProd, hdigits]
    exact hprod

/-- Decomposition of an admissible `n`: if `n ≠ 0` and `10 ∤ n`, then
`n = p ^ e * Q` with `p ∈ {2, 5}` and `Q` coprime to `10`. -/
theorem exists_decomp (n : ℕ) (hn0 : n ≠ 0) (h10 : ¬ 10 ∣ n) :
    ∃ p e Q, (p = 2 ∨ p = 5) ∧ Nat.Coprime 10 Q ∧ n = p ^ e * Q := by
  have h10eq : (10 : ℕ) = 2 * 5 := by norm_num
  by_cases h2 : 2 ∣ n
  · have h5 : ¬ 5 ∣ n := fun h5 =>
      h10 (h10eq ▸ Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h5)
    refine ⟨2, n.factorization 2, ordCompl[2] n, Or.inl rfl, ?_,
      (Nat.ordProj_mul_ordCompl_eq_self n 2).symm⟩
    have hc2 : Nat.Coprime 2 (ordCompl[2] n) := Nat.coprime_ordCompl Nat.prime_two hn0
    have hc5 : Nat.Coprime 5 (ordCompl[2] n) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5).coprime_dvd_right
        (Nat.ordCompl_dvd n 2)
    exact h10eq ▸ Nat.Coprime.mul_left hc2 hc5
  · refine ⟨5, n.factorization 5, ordCompl[5] n, Or.inr rfl, ?_,
      (Nat.ordProj_mul_ordCompl_eq_self n 5).symm⟩
    have hc5 : Nat.Coprime 5 (ordCompl[5] n) := Nat.coprime_ordCompl Nat.prime_five hn0
    have hc2 : Nat.Coprime 2 (ordCompl[5] n) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).coprime_dvd_right
        (Nat.ordCompl_dvd n 5)
    exact h10eq ▸ Nat.Coprime.mul_left hc2 hc5

/-! ## The conjecture -/

/-- **A085124 conjecture (comment after Robert Israel's comments, Dec 28 2025).**

Verbatim: "Conjecture: otherwise, a(n) is positive", where "otherwise" means
`n` is 7-smooth (a term of A002473) and `n` is not a multiple of `10`; a(n)
is the smallest multiple of `n` whose digital product is also a positive
multiple of `n`.

Formal reading: if every prime factor of `n` is at most `7` and `10 ∤ n`,
then some positive multiple `m` of `n` has a positive digit product divisible
by `n`.  (The smoothness hypothesis already excludes `n = 0`, since `11 ∣ 0`.) -/
theorem a085124_conjecture (n : ℕ) (hsmooth : ∀ p, p.Prime → p ∣ n → p ≤ 7)
    (h10 : ¬ 10 ∣ n) :
    ∃ m, 0 < m ∧ n ∣ m ∧ 0 < digitProd m ∧ n ∣ digitProd m := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h11 := hsmooth 11 (by norm_num) (dvd_zero 11)
    omega
  obtain ⟨Y₀, hY₀, hY₀prod⟩ := exists_digitList_prod_eq n hn0 hsmooth
  obtain ⟨p, e, Q, hp, hQ, hn⟩ := exists_decomp n hn0 h10
  obtain ⟨M, hMne, hdig, hdvd, hprod⟩ :=
    exists_list_of_decomp p e Q n hp hQ hn Y₀ hY₀ hY₀prod
  exact witness_of_list n M hMne hdig hdvd hprod

/-! ## Sanity layer -/

/-- The guard `10 ∤ n` is load-bearing (entry comment "a(n) = 0 if n is a
multiple of 10"): every positive multiple of a multiple of `10` ends in the
digit `0`, so its digit product is `0`. -/
theorem digitProd_eq_zero_of_ten_dvd (n m : ℕ) (h10 : 10 ∣ n) (hm : 0 < m) (hnm : n ∣ m) :
    digitProd m = 0 := by
  have hmod : m % 10 = 0 := Nat.mod_eq_zero_of_dvd (h10.trans hnm)
  rw [digitProd, Nat.digits_def' (by norm_num) hm, hmod]
  simp

-- Satisfiability of the hypotheses at `n = 12` (where a(12) = 168).
example : (∀ p, p.Prime → p ∣ 12 → p ≤ 7) ∧ ¬ 10 ∣ 12 := by
  refine ⟨fun p hp hd => ?_, by norm_num⟩
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hd
  interval_cases p <;> first | omega | (norm_num at hp)

end Candidates.A085124SmoothDividingSome
