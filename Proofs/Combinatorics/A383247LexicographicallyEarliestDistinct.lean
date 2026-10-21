/-
# A383247 — numbers missing from A342044

## OEIS source (retrieved with `oeis show A383247` / `oeis show A342044`, 2026-10-21)

```
A383247
NAME:     Positive integers that contain the digit 9, or an odd digit d
          immediately followed by a digit <= d.
TERMS:    9,10,11,19,29,30,31,32,33,39,49,50,51,52,53,54,55,59,69,70,71,72,73,
          74,75,76,77,79,89,90,91,92,93,94,95,96,97,98,99,100,101,...,133
COMMENT (the conjecture):
  Conjecture: these are the numbers missing from A342044.
PROGRAM (Python):  def ok(n): s = str(n); return "9" in s or any(d in "13579"
          and s[i]<=d for i, d in enumerate(s, 1) if i < len(s))
          # _Michael S. Branicky_, Apr 28 2025

A342044
NAME:     When a digit d is odd, the next digit is > d.
TERMS:    0,1,2,3,4,5,6,7,8,12,13,40,14,15,60,16,17,80,18,20,21,22,23,41,24,
          25,61,26,27,81,28,34,35,62,36,37,82,38,42,43,44,45,63,46,47,83,48,
          56,57,84,58,64,65,66,67,85,68,78,86,87,88,120,121,200,122,123,400,
          124,125,600,126,127,800,128
COMMENT:  The sequence is always extended with the smallest positive integer
          not yet present that doesn't lead to a contradiction.
COMMENT:  No digit 9 is present in the sequence (as 9, being odd, would block it).
```

The conjecture line carries no separate author attribution; the entry
A383247 dates from April 2025 (program by Michael S. Branicky, Apr 28 2025).

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  This module proves it (see `a383247_iff_not_mem_range_a342044`).

## Definition layer

* `decDigits m` is the decimal string of `m`, most significant digit first
  (`[0]` for `m = 0`, which is the first term of A342044).
* `Valid l`: no odd digit `d` of `l` is immediately followed by a digit `≤ d`.
* `Admissible m`: the decimal string of `m` is `Valid` and has no digit 9.
* `a342044` is the greedy sequence: `a 0 = 0`, and `a (n+1)` is the least `m`
  not among `a 0, …, a n` such that `m` is `Admissible` and the junction
  `decDigits (a n) ++ decDigits m` is `Valid`.

Fidelity of the greedy rule.  The concatenated digit string of the sequence is
`Valid` iff every term is `Valid` and every junction is `Valid` (the relation
is between adjacent digits only).  A `Valid` string can contain a 9 only as its
last digit, and a string ending in 9 cannot be continued; conversely a `Valid`
string not ending in 9 can always be continued (e.g. by an unused `8·10^k`).
So "doesn't lead to a contradiction" is exactly "the new term contains no 9",
and the greedy rule below is the entry's rule.  The search in `findFrom` is
bounded by `8·10^(n+1)`, a bound proved sufficient (`exists_cand`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A383247LexicographicallyEarliestDistinct

/-! ## Definitions -/

/-- The decimal digit string of `m`, most significant digit first; `0` is
written `[0]`. -/
def decDigits (m : ℕ) : List ℕ := if m = 0 then [0] else (Nat.digits 10 m).reverse

/-- A digit string is valid when no odd digit `d` is immediately followed by a
digit `≤ d` (equivalently: an odd digit is followed by a larger digit). -/
def Valid (l : List ℕ) : Prop := l.IsChain (fun d e => d % 2 = 1 → d < e)

instance (l : List ℕ) : Decidable (Valid l) := by unfold Valid; infer_instance

/-- A number is admissible when its own decimal string is valid and contains no
digit 9. -/
def Admissible (m : ℕ) : Prop := Valid (decDigits m) ∧ 9 ∉ decDigits m

instance (m : ℕ) : Decidable (Admissible m) := by unfold Admissible; infer_instance

/-- Bounded linear search: the least `m ∈ [k, k + fuel)` with `P m`, or
`k + fuel` when there is none. -/
def findFrom (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ → ℕ
  | k, 0 => k
  | k, f + 1 => if P k then k else findFrom P (k + 1) f

/-- `m` is a legal next term after the terms `L` (latest first): it is unused,
admissible, and the junction with the latest term `L.headD 0` is valid. -/
def Cand (L : List ℕ) (m : ℕ) : Prop :=
  m ∉ L ∧ Admissible m ∧ Valid (decDigits (L.headD 0) ++ decDigits m)

instance (L : List ℕ) : DecidablePred (Cand L) := fun m => by unfold Cand; infer_instance

/-- `terms n = [a n, a (n-1), …, a 0]` for the greedy sequence A342044. -/
def terms : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => findFrom (Cand (terms n)) 0 (8 * 10 ^ (n + 1) + 1) :: terms n

/-- A342044: `a 0 = 0` and `a (n+1)` is the least unused admissible number whose
digits continue the digit string validly. -/
def a342044 (n : ℕ) : ℕ := (terms n).headD 0

/-- A383247: positive integers containing the digit 9, or an odd digit `d`
immediately followed by a digit `≤ d`. -/
def InA383247 (m : ℕ) : Prop :=
  0 < m ∧ (9 ∈ Nat.digits 10 m ∨
    ∃ (l₁ l₂ : List ℕ) (d e : ℕ),
      (Nat.digits 10 m).reverse = l₁ ++ d :: e :: l₂ ∧ d % 2 = 1 ∧ e ≤ d)

/-! ## Basic lemmas -/

/-- A positive number's decimal string is the reversed `Nat.digits`. -/
theorem decDigits_of_pos {m : ℕ} (hm : 0 < m) : decDigits m = (Nat.digits 10 m).reverse := by
  rw [decDigits, if_neg (Nat.pos_iff_ne_zero.mp hm)]

/-- Membership in A383247 is the failure of admissibility, for positive numbers. -/
theorem inA383247_iff (m : ℕ) : InA383247 m ↔ 0 < m ∧ ¬ Admissible m := by
  unfold InA383247
  refine and_congr_right fun hm => ?_
  rw [Admissible, Valid, decDigits_of_pos hm, List.isChain_iff_forall_rel_of_append_cons_cons,
    List.mem_reverse]
  constructor
  · rintro (h9 | ⟨l₁, l₂, d, e, hl, hd, hed⟩) ⟨hch, hn9⟩
    · exact hn9 h9
    · have := hch hl hd
      omega
  · intro h
    by_contra hcon
    push Not at hcon
    refine h ⟨fun d e l₁ l₂ hl hd => ?_, hcon.1⟩
    by_contra hde
    exact absurd (hcon.2 l₁ l₂ d e hl hd) (by omega)

instance : DecidablePred InA383247 := fun m => decidable_of_iff _ (inA383247_iff m).symm

/-- Every entry of a decimal string is a digit `< 10`. -/
theorem lt_ten_of_mem_decDigits {m d : ℕ} (h : d ∈ decDigits m) : d < 10 := by
  unfold decDigits at h
  split_ifs at h with hm
  · simp only [List.mem_singleton] at h
    omega
  · exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp h)

/-- The decimal string of `8 · 10^j` is `8` followed by `j` zeros. -/
theorem decDigits_eight_mul_pow (j : ℕ) :
    decDigits (8 * 10 ^ j) = 8 :: List.replicate j 0 := by
  have hne : 8 * 10 ^ j ≠ 0 := by positivity
  rw [decDigits, if_neg hne, mul_comm, Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
  simp

/-- A string of even digits is valid. -/
theorem valid_of_forall_even {l : List ℕ} (h : ∀ d ∈ l, d % 2 = 0) : Valid l := by
  rw [Valid, List.isChain_iff_forall_rel_of_append_cons_cons]
  intro d e l₁ l₂ hl hd
  have hmem : d ∈ l := by simp [hl]
  have := h d hmem
  omega

/-- All digits of `8 · 10^j` are even. -/
theorem even_of_mem_decDigits_eight_mul_pow {j d : ℕ} (h : d ∈ decDigits (8 * 10 ^ j)) :
    d % 2 = 0 := by
  rw [decDigits_eight_mul_pow, List.mem_cons, List.mem_replicate] at h
  omega

/-- `8 · 10^j` is admissible. -/
theorem admissible_eight_mul_pow (j : ℕ) : Admissible (8 * 10 ^ j) := by
  refine ⟨valid_of_forall_even fun d hd => even_of_mem_decDigits_eight_mul_pow hd, fun h9 => ?_⟩
  have := even_of_mem_decDigits_eight_mul_pow h9
  omega

/-- After an admissible number, `8 · 10^j` may follow. -/
theorem valid_append_eight_mul_pow {p : ℕ} (hp : Admissible p) (j : ℕ) :
    Valid (decDigits p ++ decDigits (8 * 10 ^ j)) := by
  rw [Valid, List.isChain_append]
  refine ⟨hp.1, (admissible_eight_mul_pow j).1, fun x hx y hy hxodd => ?_⟩
  rw [decDigits_eight_mul_pow, List.head?_cons, Option.mem_some_iff] at hy
  have hxmem : x ∈ decDigits p := List.mem_of_mem_getLast? hx
  have hx10 := lt_ten_of_mem_decDigits hxmem
  have hx9 : x ≠ 9 := fun h => hp.2 (h ▸ hxmem)
  omega

/-- After `8 · 10^j` (whose last digit is even), any admissible number may follow. -/
theorem valid_eight_mul_pow_append {m : ℕ} (hm : Admissible m) (j : ℕ) :
    Valid (decDigits (8 * 10 ^ j) ++ decDigits m) := by
  rw [Valid, List.isChain_append]
  refine ⟨(admissible_eight_mul_pow j).1, hm.1, fun x hx y _ hxodd => ?_⟩
  have := even_of_mem_decDigits_eight_mul_pow (List.mem_of_mem_getLast? hx)
  omega

/-- Specification of the bounded search: if some `y ∈ [k, k + fuel)` satisfies
`P`, the search returns a value satisfying `P` that is `≤` every `x ≥ k` with
`P x`. -/
theorem findFrom_spec (P : ℕ → Prop) [DecidablePred P] (fuel : ℕ) :
    ∀ k : ℕ, (∃ y, k ≤ y ∧ y < k + fuel ∧ P y) →
      P (findFrom P k fuel) ∧ ∀ x, k ≤ x → P x → findFrom P k fuel ≤ x := by
  induction fuel with
  | zero =>
    rintro k ⟨y, hky, hyk, _⟩
    omega
  | succ f ih =>
    rintro k ⟨y, hky, hyk, hy⟩
    by_cases hk : P k
    · simp only [findFrom, if_pos hk]
      exact ⟨hk, fun x hx _ => hx⟩
    · simp only [findFrom, if_neg hk]
      have hyne : y ≠ k := fun h => hk (h ▸ hy)
      obtain ⟨hP, hle⟩ := ih (k + 1) ⟨y, by omega, by omega, hy⟩
      refine ⟨hP, fun x hx hPx => hle x ?_ hPx⟩
      have hxne : x ≠ k := fun h => hk (h ▸ hPx)
      omega

/-! ## Structure of the greedy sequence -/

/-- `terms (n+1)` prepends `a (n+1)` to `terms n`. -/
theorem terms_succ (n : ℕ) : terms (n + 1) = a342044 (n + 1) :: terms n := rfl

/-- The head of `terms n` is `a n`. -/
theorem headD_terms (n : ℕ) : (terms n).headD 0 = a342044 n := rfl

/-- `terms n` lists exactly `a 0, …, a n`. -/
theorem mem_terms {n x : ℕ} : x ∈ terms n ↔ ∃ i ≤ n, a342044 i = x := by
  induction n with
  | zero =>
    simp only [terms, List.mem_singleton, Nat.le_zero, exists_eq_left]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  | succ n ih =>
    rw [terms_succ, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨i, hi, hix⟩)
      · exact ⟨n + 1, le_refl _, h.symm⟩
      · exact ⟨i, by omega, hix⟩
    · rintro ⟨i, hi, hix⟩
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact Or.inr ⟨i, by omega, hix⟩
      · left
        rw [← hix, show i = n + 1 by omega]

/-- `terms n` has length `n + 1`. -/
theorem length_terms (n : ℕ) : (terms n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [terms_succ, List.length_cons, ih]

/-- If `a n` is admissible, a legal next term exists below the search bound
(one of `8, 80, …, 8·10^(n+1)` is unused). -/
theorem exists_cand (n : ℕ) (h : Admissible (a342044 n)) :
    ∃ y, 0 ≤ y ∧ y < 0 + (8 * 10 ^ (n + 1) + 1) ∧ Cand (terms n) y := by
  classical
  let t : Finset ℕ := (Finset.range (n + 2)).image (fun j => 8 * 10 ^ j)
  have hinj : Function.Injective (fun j : ℕ => 8 * 10 ^ j) := fun i j hij => by
    have h10 : 10 ^ i = 10 ^ j := by simpa using hij
    exact Nat.pow_right_injective (le_refl _) (by simpa using h10)
  have hcard_t : t.card = n + 2 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hcard_s : (terms n).toFinset.card < t.card := by
    have := List.toFinset_card_le (terms n)
    rw [length_terms] at this
    omega
  obtain ⟨e, het, hes⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_s
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp het
  have hjlt : j < n + 2 := Finset.mem_range.mp hj
  have hjle : 10 ^ j ≤ 10 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨8 * 10 ^ j, Nat.zero_le _, by omega, ?_, admissible_eight_mul_pow j, ?_⟩
  · simpa using hes
  · rw [headD_terms]
    exact valid_append_eight_mul_pow h j

/-- The greedy step: if `a n` is admissible, `a (n+1)` is a legal next term and
is `≤` every legal next term. -/
theorem spec_succ (n : ℕ) (h : Admissible (a342044 n)) :
    Cand (terms n) (a342044 (n + 1)) ∧ ∀ x, Cand (terms n) x → a342044 (n + 1) ≤ x := by
  obtain ⟨hP, hle⟩ := findFrom_spec (Cand (terms n)) _ 0 (exists_cand n h)
  exact ⟨hP, fun x hx => hle x (Nat.zero_le x) hx⟩

/-- Every term of A342044 is admissible. -/
theorem admissible_a342044 (n : ℕ) : Admissible (a342044 n) := by
  induction n with
  | zero => decide
  | succ n ih => exact (spec_succ n ih).1.2.1

/-- `a (n+1)` is a legal next term after `a 0, …, a n`. -/
theorem cand_succ (n : ℕ) : Cand (terms n) (a342044 (n + 1)) :=
  (spec_succ n (admissible_a342044 n)).1

/-- `a (n+1)` is `≤` every legal next term after `a 0, …, a n`. -/
theorem le_of_cand (n : ℕ) {x : ℕ} (hx : Cand (terms n) x) : a342044 (n + 1) ≤ x :=
  (spec_succ n (admissible_a342044 n)).2 x hx

/-- A342044 has distinct terms. -/
theorem a342044_injective : Function.Injective a342044 := by
  have key : ∀ i j, i < j → a342044 i ≠ a342044 j := by
    intro i j hij hEq
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (cand_succ k).1 (mem_terms.mpr ⟨i, by omega, hEq⟩)
  intro i j hEq
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd hEq (key i j hlt)
  · exact heq
  · exact absurd hEq.symm (key j i hgt)

/-- `decDigits m` is never empty. -/
theorem decDigits_ne_nil (m : ℕ) : decDigits m ≠ [] := by
  unfold decDigits
  split_ifs with hm
  · exact List.cons_ne_nil 0 []
  · simpa using Nat.digits_ne_nil_iff_ne_zero.mpr hm

/-- Fidelity check: the concatenated digit string of `a 0, …, a n` never has an
odd digit `d` followed by a digit `≤ d`. -/
theorem valid_concat (n : ℕ) :
    Valid ((List.range (n + 1)).flatMap (fun i => decDigits (a342044 i))) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, Valid, List.isChain_append]
    refine ⟨ih, (admissible_a342044 (n + 1)).1, fun x hx y hy => ?_⟩
    have hjunc := (cand_succ n).2.2
    rw [headD_terms, Valid, List.isChain_append] at hjunc
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.getLast?_append_of_ne_nil _ (decDigits_ne_nil _)] at hx
    exact hjunc.2.2 x hx y hy

/-! ## The pigeonhole argument -/

/-- If an admissible `x` never occurs, then it can follow `a n` for at most `x`
indices `n`: each such step picks a smaller fresh term `a (n+1) < x`. -/
theorem card_le_of_not_mem_range {x : ℕ} (hx : Admissible x) (hxr : x ∉ Set.range a342044)
    (F : Finset ℕ) (hF : ∀ n ∈ F, Valid (decDigits (a342044 n) ++ decDigits x)) :
    F.card ≤ x := by
  have hmaps : Set.MapsTo (fun n => a342044 (n + 1)) (F : Set ℕ) (Finset.range x : Set ℕ) := by
    intro n hn
    have hcand : Cand (terms n) x := by
      refine ⟨fun hmem => ?_, hx, ?_⟩
      · obtain ⟨i, _, hi⟩ := mem_terms.mp hmem
        exact hxr ⟨i, hi⟩
      · rw [headD_terms]
        exact hF n hn
    have hle := le_of_cand n hcand
    have hne : a342044 (n + 1) ≠ x := fun h => hxr ⟨n + 1, h⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  have hinj : Set.InjOn (fun n => a342044 (n + 1)) (F : Set ℕ) := fun i _ j _ hij => by
    have := a342044_injective hij
    omega
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

/-- Every number `8 · 10^j` occurs in A342044. -/
theorem eight_mul_pow_mem_range (j : ℕ) : 8 * 10 ^ j ∈ Set.range a342044 := by
  by_contra hr
  have := card_le_of_not_mem_range (admissible_eight_mul_pow j) hr (Finset.range (8 * 10 ^ j + 1))
    (fun n _ => valid_append_eight_mul_pow (admissible_a342044 n) j)
  rw [Finset.card_range] at this
  omega

/-- Every admissible number occurs in A342044. -/
theorem mem_range_of_admissible {m : ℕ} (hm : Admissible m) : m ∈ Set.range a342044 := by
  classical
  by_contra hr
  choose idx hidx using eight_mul_pow_mem_range
  have hinj : Function.Injective idx := fun i j hij => by
    have h := congrArg a342044 hij
    rw [hidx, hidx] at h
    have h10 : 10 ^ i = 10 ^ j := by omega
    exact Nat.pow_right_injective (le_refl _) (by simpa using h10)
  have := card_le_of_not_mem_range hm hr ((Finset.range (m + 1)).image idx) (by
    intro n hn
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hn
    rw [hidx]
    exact valid_eight_mul_pow_append hm j)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at this
  omega

/-- The range of A342044 is exactly the set of admissible numbers. -/
theorem mem_range_a342044_iff (m : ℕ) : m ∈ Set.range a342044 ↔ Admissible m := by
  constructor
  · rintro ⟨n, rfl⟩
    exact admissible_a342044 n
  · exact mem_range_of_admissible

/-! ## The conjecture -/

/-- **A383247 conjecture (comment in A383247, 2025): A383247 is exactly the set of
positive integers missing from A342044.**

Verbatim: "Conjecture: these are the numbers missing from A342044."  That is, a
positive integer `m` contains the digit 9 or an odd digit `d` immediately
followed by a digit `≤ d` if and only if `m` is not a term of A342044 (the
lexicographically earliest sequence of distinct nonnegative integers, starting
with 0, whose concatenated digit string never has an odd digit `d` followed by
a digit `≤ d`). -/
theorem a383247_iff_not_mem_range_a342044 (m : ℕ) (hm : 0 < m) :
    InA383247 m ↔ m ∉ Set.range a342044 := by
  rw [inA383247_iff, mem_range_a342044_iff]
  exact ⟨fun h => h.2, fun h => ⟨hm, h⟩⟩

/-! ## Ground truth -/

/-- Non-vacuity of the main statement at a member: `10 ∈ A383247` is missing. -/
example : 10 ∉ Set.range a342044 :=
  (a383247_iff_not_mem_range_a342044 10 (by norm_num)).mp (by decide)

/-- Non-vacuity of the main statement at a non-member: `12` occurs. -/
example : 12 ∈ Set.range a342044 := ⟨9, by decide⟩

example : decDigits 0 = [0] := by decide
example : decDigits 120 = [1, 2, 0] := by decide

/-- The first 40 terms of A342044 as listed in the entry. -/
example : (List.range 40).map a342044 =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 40, 14, 15, 60, 16, 17, 80, 18, 20, 21, 22, 23, 41,
      24, 25, 61, 26, 27, 81, 28, 34, 35, 62, 36, 37, 82, 38, 42, 43] := by decide

/-- The listed terms of A383247 (all members up to 133). -/
example : (List.range 134).filter (fun m => decide (InA383247 m)) =
    [9, 10, 11, 19, 29, 30, 31, 32, 33, 39, 49, 50, 51, 52, 53, 54, 55, 59, 69, 70, 71, 72, 73,
      74, 75, 76, 77, 79, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104,
      105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 129, 130, 131,
      132, 133] := by decide

end Candidates.A383247LexicographicallyEarliestDistinct
