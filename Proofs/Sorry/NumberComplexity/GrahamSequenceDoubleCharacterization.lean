/-
# A006255 — Graham's function: `g(n) = 2n` iff `n = 0`, `n = 6`, or `n > 3` prime

## Source

* Sarosh Adenwalla, *On a Generalisation of a Function of Ron Graham's*,
  arXiv:2504.19196v2 (May 2025).  Section 1 (definition of `g_m(n)`),
  Conjecture 1.1 (due to Kagey–Rajesh), and Theorem `conj` at the end of
  Section 3, whose proof uses Lemma `lemma:ab` (Selfridge / Erdős) and the
  Appendix values `g_2(2) = 6`, `g_2(3) = 8`.
* The "if" direction is credited there to C. Kagey and N. Rajesh,
  arXiv:2410.04728 (Lemma 7: `g_2(p) = 2p` for primes `p > 3`;
  `g_2(0) = 0`, `g_2(6) = 12`).
* OEIS A006255 is the sequence `(g_2(n))_{n ≥ 0}`.

Verbatim (arXiv:2504.19196, Section 1):

  "For non-negative integers n, define g(n) to be the smallest integer
  s ≥ n such that there exist distinct integers a_1,…,a_t ∈ [n,s] where
  a_1 = n and ∏ a_i is a square."

  "Definition. A sequence of integers, a_1 ≤ a_2 ≤ … ≤ a_t, is a
  m-product sequence if there exists R ∈ ℕ such that ∏ a_i = R^m and no
  integer appears more than m−1 times in the sequence."

  "Definition. For n ∈ ℕ, we say g_m(n) is the least integer s such that
  there exists an m-product sequence starting at n and ending at s."

  "Theorem (conj). For all n ∈ ℕ, g_2(n) = 2n if and only if:
  1. n > 3 is prime  2. n = 0  3. n = 6."

## Status

Proved in the literature (Kagey–Rajesh for "if", Adenwalla for "only
if").  Recorded 2026-10-21.  This module proves the full characterization
end to end.

## Encoding

An `m`-product sequence `n = a_1 ≤ … ≤ a_t = s` is encoded by its
multiplicity function `c : ℕ → ℕ` on `Finset.Icc n s`: `c i` is the number
of times `i` appears.  The sequence starts at `n` (`0 < c n`), ends at `s`
(`0 < c s`), has `n ≤ s`, every multiplicity is `< m`, and
`∏ i ∈ Icc n s, i ^ c i = R ^ m`.  For `m = 2` a multiplicity function is
the indicator of a set of distinct integers, which is Graham's original
definition (`adm_two_iff`).

Upper bound witnesses used below:
* `p` prime, `p ≥ 5`: `{p, 2l², 2p}` with `p < 2l² < 2p`, product
  `(2pl)²` (simpler than the two-square witness of the triage sketch).
* `n = ab`, `1 < a < b`: `{ab, a(b+1), (a+1)b, (a+1)(b+1)}` (Lemma `ab`).
* `n = 6`: `{6, 8, 12}`, product `24²`.
-/
import Mathlib

set_option autoImplicit false

namespace GrahamSequenceDoubleCharacterization

open Finset

/-- `Adm m n s`: there is an `m`-product sequence starting at `n` and ending
at `s` (Adenwalla, arXiv:2504.19196, Section 1), encoded by the multiplicity
function `c` on `[n, s]`: `n ≤ s`, `n` and `s` both appear, every integer
appears fewer than `m` times, and the product is an `m`-th power. -/
def Adm (m n s : ℕ) : Prop :=
  n ≤ s ∧ ∃ c : ℕ → ℕ, 0 < c n ∧ 0 < c s ∧ (∀ i, c i < m) ∧
    ∃ R : ℕ, ∏ i ∈ Icc n s, i ^ c i = R ^ m

/-- For `m ≥ 2` every `n` admits some `m`-product sequence starting at `n`:
`n = 0` alone, and for `n ≥ 1` the sequence `n, (n 2^m)^{m-1}` with product
`(n 2^{m-1})^m`. -/
theorem adm_exists {m : ℕ} (hm : 2 ≤ m) (n : ℕ) : ∃ s, Adm m n s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, le_rfl, fun _ => 1, Nat.one_pos, Nat.one_pos, fun _ => by simp only; omega, 0, ?_⟩
    simp [zero_pow (by omega : m ≠ 0)]
  · have hlt : n < n * 2 ^ m := by
      have h2 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
      nlinarith
    refine ⟨n * 2 ^ m, hlt.le, fun i => if i = n then 1 else if i = n * 2 ^ m then m - 1 else 0,
      by simp, by simp only [hlt.ne', ↓reduceIte]; omega, fun i => by simp only; split_ifs <;> omega, n * 2 ^ (m - 1), ?_⟩
    rw [Finset.prod_eq_mul n (n * 2 ^ m) hlt.ne]
    · simp only [if_true, hlt.ne', if_false, pow_one]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    · intro i _ hi
      simp [hi.1, hi.2]
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hlt.le⟩) h
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hlt.le, le_rfl⟩) h

open Classical in
/-- Graham's generalized function `g_m(n)` (Adenwalla, arXiv:2504.19196):
the least `s` such that an `m`-product sequence starts at `n` and ends at
`s`.  `g_2` is Graham's `g` (OEIS A006255). -/
noncomputable def gm (m n : ℕ) (hm : 2 ≤ m) : ℕ :=
  Nat.find (adm_exists hm n)

open Classical in
/-- `g_m(n) ≤ s` whenever an `m`-product sequence from `n` ends at `s`. -/
theorem gm_le {m n s : ℕ} (hm : 2 ≤ m) (h : Adm m n s) : gm m n hm ≤ s :=
  Nat.find_min' _ h

open Classical in
/-- `s ≤ g_m(n)` whenever no `m`-product sequence from `n` ends below `s`. -/
theorem le_gm {m n s : ℕ} (hm : 2 ≤ m) (h : ∀ t < s, ¬ Adm m n t) : s ≤ gm m n hm := by
  by_contra hlt
  exact h _ (not_le.mp hlt) (Nat.find_spec (adm_exists hm n))

/-- A product of `i ^ c i` with `c i < 2` is the product over the support. -/
theorem prod_pow_eq_prod_filter (T : Finset ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i < 2) :
    ∏ i ∈ T, i ^ c i = ∏ i ∈ T.filter (fun i => c i = 1), i := by
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := hc i
  rcases (by omega : c i = 0 ∨ c i = 1) with h | h <;> simp [h]

/-- For `m = 2`, admissibility is Graham's original condition: a set `S` of
distinct integers in `[n, s]` containing `n` and `s` whose product is a
square. -/
theorem adm_two_iff (n s : ℕ) :
    Adm 2 n s ↔ n ≤ s ∧ ∃ S ⊆ Icc n s, n ∈ S ∧ s ∈ S ∧ ∃ R : ℕ, ∏ i ∈ S, i = R ^ 2 := by
  constructor
  · rintro ⟨hns, c, hcn, hcs, hc, R, hR⟩
    refine ⟨hns, (Icc n s).filter (fun i => c i = 1), Finset.filter_subset _ _, ?_, ?_, R, ?_⟩
    · have := hc n
      simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    · have := hc s
      simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    · rw [← prod_pow_eq_prod_filter _ _ hc, hR]
  · rintro ⟨hns, S, hS, hn, hs, R, hR⟩
    classical
    refine ⟨hns, fun i => if i ∈ S then 1 else 0, by simp [hn], by simp [hs],
      fun i => by simp only; split_ifs <;> omega, R, ?_⟩
    have hrw : ∀ i ∈ Icc n s, i ^ (if i ∈ S then 1 else 0) = if i ∈ S then i else 1 := by
      intro i _; split_ifs <;> simp
    rw [Finset.prod_congr rfl hrw, Finset.prod_ite_mem, Finset.inter_eq_right.mpr hS, hR]

/-- Lower-bound engine for `m = 2`: if no subset of `[n, k]` containing `n`
has square product, then no `2`-product sequence from `n` ends at any
`t ≤ k`. -/
theorem not_adm_two_of_forall {n k t : ℕ}
    (h : ∀ S ∈ (Icc n k).powerset, n ∈ S → ¬ IsSquare (∏ i ∈ S, i)) (ht : t ≤ k) :
    ¬ Adm 2 n t := by
  rw [adm_two_iff]
  rintro ⟨_, S, hS, hn, _, R, hR⟩
  have hSk : S ⊆ Icc n k := hS.trans (Finset.Icc_subset_Icc le_rfl ht)
  exact h S (Finset.mem_powerset.mpr hSk) hn ⟨R, by rw [hR, sq]⟩

/-- **Prime lower bound.**  For a prime `p` and `s < 2p`, no `2`-product
sequence runs from `p` to `s`: `p` is the only multiple of `p` in
`[p, 2p)`, so the `p`-adic valuation of the product is `1`. -/
theorem not_adm_two_of_prime {p s : ℕ} (hp : p.Prime) (hs : s < 2 * p) : ¬ Adm 2 p s := by
  rw [adm_two_iff]
  rintro ⟨_, S, hS, hpS, _, R, hR⟩
  have hndvd : ¬ p ∣ ∏ i ∈ S.erase p, i := by
    rw [Prime.dvd_finsetProd_iff hp.prime]
    rintro ⟨i, hi, hpi⟩
    have hiS := Finset.mem_of_mem_erase hi
    have hip : i ≠ p := Finset.ne_of_mem_erase hi
    have hiI := Finset.mem_Icc.mp (hS hiS)
    obtain ⟨k, rfl⟩ := hpi
    have hp1 := hp.one_lt
    rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
    · omega
    · exact hip (mul_one p)
    · have : p * 2 ≤ p * k := Nat.mul_le_mul_left p hk
      omega
  have hprod : p * ∏ i ∈ S.erase p, i = R ^ 2 := by
    rw [Finset.mul_prod_erase S (fun i => i) hpS, hR]
  have hpR : p ∣ R := hp.dvd_of_dvd_pow (Dvd.intro _ hprod)
  obtain ⟨r, rfl⟩ := hpR
  apply hndvd
  refine ⟨r ^ 2, ?_⟩
  have hp0 : 0 < p := hp.pos
  have : p * ∏ i ∈ S.erase p, i = p * (p * r ^ 2) := by rw [hprod]; ring
  exact Nat.eq_of_mul_eq_mul_left hp0 this

/-- For `10 ≤ p` there is a square `l²` with `p < 2l² < 2p`
(take `l = ⌊√(p-1)⌋ ≥ 3`). -/
theorem exists_sq_between {p : ℕ} (hp : 10 ≤ p) : ∃ l : ℕ, p < 2 * l ^ 2 ∧ l ^ 2 < p := by
  refine ⟨Nat.sqrt (p - 1), ?_, ?_⟩
  · have h2 : p - 1 < (Nat.sqrt (p - 1) + 1) ^ 2 := Nat.lt_succ_sqrt' (p - 1)
    have h3 : 3 ≤ Nat.sqrt (p - 1) := by rw [Nat.le_sqrt]; omega
    generalize Nat.sqrt (p - 1) = l at h2 h3 ⊢
    have h2' : p ≤ (l + 1) ^ 2 := by omega
    nlinarith
  · have h1 : Nat.sqrt (p - 1) ^ 2 ≤ p - 1 := Nat.sqrt_le' (p - 1)
    omega

/-- **Prime upper bound.**  For a prime `p ≥ 5`, the set `{p, 2l², 2p}` with
`p < 2l² < 2p` has product `(2pl)²`, so a `2`-product sequence runs from
`p` to `2p`. -/
theorem adm_two_prime {p : ℕ} (hp : 5 ≤ p) (hp8 : p ≠ 8) (hp9 : p ≠ 9) : Adm 2 p (2 * p) := by
  obtain ⟨l, hl1, hl2⟩ : ∃ l : ℕ, p < 2 * l ^ 2 ∧ l ^ 2 < p := by
    rcases (by omega : p = 5 ∨ p = 6 ∨ p = 7 ∨ 10 ≤ p) with rfl | rfl | rfl | h10
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact exists_sq_between h10
  set q := l ^ 2 with hq
  rw [adm_two_iff]
  refine ⟨by omega, {p, 2 * q, 2 * p}, ?_, by simp, by simp, 2 * p * l, ?_⟩
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_Icc]; omega
  · rw [Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton, hq]
    ring

/-- **Kagey–Rajesh, Lemma 7.**  For a prime `p > 3`, `g_2(p) = 2p`. -/
theorem gm_two_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : gm 2 p le_rfl = 2 * p := by
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
  have h8 : p ≠ 8 := by rintro rfl; norm_num at hp
  have h9 : p ≠ 9 := by rintro rfl; norm_num at hp
  refine le_antisymm (gm_le _ (adm_two_prime (by omega) h8 h9)) (le_gm _ fun t ht => ?_)
  exact not_adm_two_of_prime hp ht

/-- **Lemma `ab` (Selfridge).**  If `1 ≤ a < b`, the set
`{ab, a(b+1), (a+1)b, (a+1)(b+1)}` has square product, so a `2`-product
sequence runs from `ab` to `(a+1)(b+1)`. -/
theorem adm_two_mul {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    Adm 2 (a * b) ((a + 1) * (b + 1)) := by
  have e1 : a * (b + 1) = a * b + a := by ring
  have e2 : (a + 1) * b = a * b + b := by ring
  have e3 : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
  rw [adm_two_iff]
  refine ⟨by omega, {a * b, a * (b + 1), (a + 1) * b, (a + 1) * (b + 1)}, ?_, by simp, by simp,
    a * b * (a + 1) * (b + 1), ?_⟩
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_Icc]; omega
  · rw [Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
    ring

/-- A square `n = a²` has the one-term `2`-product sequence `n`. -/
theorem adm_two_sq (a : ℕ) : Adm 2 (a ^ 2) (a ^ 2) := by
  rw [adm_two_iff]
  exact ⟨le_rfl, {a ^ 2}, by simp, by simp, by simp, a, by simp⟩

/-- **Adenwalla, Section 3.**  If `n ≥ 1` is not prime and `n ≠ 6`, then
`g_2(n) < 2n`. -/
theorem gm_two_lt_of_not_prime {n : ℕ} (hn : 1 ≤ n) (hnp : ¬ n.Prime) (h6 : n ≠ 6) :
    gm 2 n le_rfl < 2 * n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · have := gm_le le_rfl (adm_two_sq 1)
    simp only [one_pow] at this
    omega
  obtain ⟨a, ha⟩ : ∃ a, a = n.minFac := ⟨_, rfl⟩
  have ha2 : 2 ≤ a := ha ▸ (Nat.minFac_prime (by omega)).two_le
  have hdvd : a ∣ n := ha ▸ Nat.minFac_dvd n
  obtain ⟨b, hb⟩ := hdvd
  have hsq : a ^ 2 ≤ n := ha ▸ Nat.minFac_sq_le_self (by omega) hnp
  have hab : a ≤ b := by
    rw [hb, sq] at hsq
    exact Nat.le_of_mul_le_mul_left hsq (by omega)
  rcases Nat.eq_or_lt_of_le hab with hab' | hab'
  · subst hab'
    have hle := gm_le le_rfl (adm_two_sq a)
    rw [sq, ← hb] at hle
    omega
  · have hle := gm_le le_rfl (adm_two_mul (by omega : 1 ≤ a) hab')
    rw [← hb] at hle
    have hne : ¬ (a = 2 ∧ b = 3) := by
      rintro ⟨h2, h3⟩
      exact h6 (by rw [hb, h2, h3])
    have hlt : (a + 1) * (b + 1) < 2 * (a * b) := by
      rcases (by omega : a = 2 ∨ 3 ≤ a) with h2 | h3
      · have hb4 : 4 ≤ b := by omega
        rw [h2]; nlinarith
      · nlinarith
    rw [← hb] at hlt
    omega

/-! ## Small values (Kagey–Rajesh; Adenwalla, Appendix) -/

/-- `g_2(0) = 0`: the one-term sequence `0` has product `0 = 0²`. -/
theorem gm_two_zero : gm 2 0 le_rfl = 0 := by
  refine Nat.le_zero.mp (gm_le le_rfl ?_)
  rw [adm_two_iff]
  exact ⟨le_rfl, {0}, by simp, by simp, by simp, 0, by simp⟩

/-- `g_2(1) = 1`: `1 = 1²`. -/
theorem gm_two_one : gm 2 1 le_rfl = 1 := by
  refine le_antisymm (by simpa using gm_le le_rfl (adm_two_sq 1)) (le_gm _ fun t ht => ?_)
  rintro ⟨h, -⟩
  omega

/-- Finite checks (one kernel `decide`): no subset of `[2, 5]` containing
`2`, of `[3, 7]` containing `3`, or of `[6, 11]` containing `6` has square
product. -/
theorem not_isSquare_small :
    (∀ S ∈ (Icc 2 5).powerset, 2 ∈ S → ¬ IsSquare (∏ i ∈ S, i)) ∧
    (∀ S ∈ (Icc 3 7).powerset, 3 ∈ S → ¬ IsSquare (∏ i ∈ S, i)) ∧
    (∀ S ∈ (Icc 6 11).powerset, 6 ∈ S → ¬ IsSquare (∏ i ∈ S, i)) := by
  decide +kernel

/-- `g_2(2) = 6`: `2 · 3 · 6 = 6²`, and no subset of `[2, 5]` containing `2`
has square product. -/
theorem gm_two_two : gm 2 2 le_rfl = 6 := by
  refine le_antisymm (gm_le le_rfl ?_) (le_gm _ fun t ht => ?_)
  · rw [adm_two_iff]
    refine ⟨by norm_num, {2, 3, 6}, ?_, by simp, by simp, 6, by decide⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_Icc]; omega
  · exact not_adm_two_of_forall not_isSquare_small.1 (by omega)

/-- `g_2(3) = 8`: `3 · 6 · 8 = 12²`, and no subset of `[3, 7]` containing `3`
has square product. -/
theorem gm_two_three : gm 2 3 le_rfl = 8 := by
  refine le_antisymm (gm_le le_rfl ?_) (le_gm _ fun t ht => ?_)
  · rw [adm_two_iff]
    refine ⟨by norm_num, {3, 6, 8}, ?_, by simp, by simp, 12, by decide⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_Icc]; omega
  · exact not_adm_two_of_forall not_isSquare_small.2.1 (by omega)

/-- `g_2(6) = 12`: `6 · 8 · 12 = 24²`, and no subset of `[6, 11]` containing
`6` has square product. -/
theorem gm_two_six : gm 2 6 le_rfl = 12 := by
  refine le_antisymm (gm_le le_rfl ?_) (le_gm _ fun t ht => ?_)
  · rw [adm_two_iff]
    refine ⟨by norm_num, {6, 8, 12}, ?_, by simp, by simp, 24, by decide⟩
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_Icc]; omega
  · exact not_adm_two_of_forall not_isSquare_small.2.2 (by omega)

/-- Ground truth against OEIS A006255 (`0, 1, 6, 8, 4, 10, 12, …`) at
`n = 4, 5`. -/
example : gm 2 4 le_rfl = 4 := by
  refine le_antisymm (by simpa using gm_le le_rfl (adm_two_sq 2)) (le_gm _ fun t ht => ?_)
  rintro ⟨h, -⟩
  omega

example : gm 2 5 le_rfl = 10 := gm_two_prime (by norm_num) (by norm_num)

/-! ## The characterization -/

/-- **Kagey–Rajesh conjecture, proved by Adenwalla (arXiv:2504.19196,
Theorem `conj`; "if" direction by Kagey–Rajesh, arXiv:2410.04728).**
For every `n ∈ ℕ`, Graham's function satisfies `g(n) = 2n` if and only if
`n = 0`, `n = 6`, or `n` is a prime greater than `3`. -/
theorem gm_two_eq_two_mul_iff (n : ℕ) :
    gm 2 n le_rfl = 2 * n ↔ n = 0 ∨ n = 6 ∨ (n.Prime ∧ 3 < n) := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact Or.inl h0
    by_cases h6 : n = 6
    · exact Or.inr (Or.inl h6)
    by_cases hp : n.Prime
    · refine Or.inr (Or.inr ⟨hp, ?_⟩)
      by_contra h3
      have h2 := hp.two_le
      rcases (by omega : n = 2 ∨ n = 3) with rfl | rfl
      · rw [gm_two_two] at h; omega
      · rw [gm_two_three] at h; omega
    · have := gm_two_lt_of_not_prime hpos hp h6
      omega
  · rintro (rfl | rfl | ⟨hp, h3⟩)
    · exact gm_two_zero
    · exact gm_two_six
    · exact gm_two_prime hp h3

end GrahamSequenceDoubleCharacterization
