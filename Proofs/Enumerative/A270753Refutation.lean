/-
# A270753 — refutation of Mathar's conjecture `a(n) = A066169(n-1)` for `n > 2`

## OEIS source (retrieved with `oeis show A270753`, 2026-10-21)

```
A270753
NAME:     The least prime q > p for which n = p + q - r for some prime r,
          where p = A270003(n).
TERMS:    5,3,3,5,5,7,7,11,11,11,11,13,13,17,17,17,17,19,19,23,23,23,23,29,29,
          29,29,29,29,31,31,37,37,37,37,37,37,41,41,41,41,43,43,47,47,47,47,53,
          53,53,53,53,53,59,59,59,59,59,59,61,61,67,67,67,67,67
FORMULA (the conjecture):
  Conjecture: a(n) = A066169(n-1) for n>2. - _R. J. Mathar_, Jun 21 2025
```

No comment or later formula line on the entry retracts the conjecture.

Auxiliary entries (same retrieval):

* A270003, "Least prime p such that n = p + q - r for some primes q and r
  with q > p."
* A066169, "Least k such that phi(k) >= n."

## Result

The conjecture is **false**; this module refutes it.  At `n = 90` we have
`A270003(90) = 2`, and the least prime `q > 2` with `90 + r = 2 + q` for a
prime `r` is `q = 101` (`r = 13`): `q = 89` gives `r = 1` and `q = 97` gives
`r = 9`.  So `A270753(90) = 101`, while `A066169(89) = 97`.  A Python
recomputation (2026-10-21) reproduces all 66 listed terms and finds the first
mismatches at `n = 90, 91, 114, 115, 120, 121, 142, 143, 184, 185`; the stored
data stop at `n = 66`, which is why the conjecture fit them.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A270753Refutation

/-! ## Definitions -/

/-- `Witness n p q`: there is a prime `r` with `n = p + q - r`.  The equation is
read in `ℤ`, exactly as written in the OEIS names (no truncated subtraction). -/
def Witness (n p q : ℕ) : Prop :=
  ∃ r : ℕ, r.Prime ∧ (n : ℤ) = p + q - r

/-- `IsA270003 n p`: `p = A270003(n)`, the least prime `p` such that
`n = p + q - r` for some primes `q` and `r` with `q > p`.  Stated relationally,
since existence of such a `p` for every `n` is not known. -/
def IsA270003 (n p : ℕ) : Prop :=
  p.Prime ∧ (∃ q : ℕ, q.Prime ∧ p < q ∧ Witness n p q) ∧
    ∀ p' < p, p'.Prime → ¬ ∃ q : ℕ, q.Prime ∧ p' < q ∧ Witness n p' q

/-- `IsA270753 n q`: `q = A270753(n)`, the least prime `q > p` for which
`n = p + q - r` for some prime `r`, where `p = A270003(n)`. -/
def IsA270753 (n q : ℕ) : Prop :=
  ∃ p : ℕ, IsA270003 n p ∧ q.Prime ∧ p < q ∧ Witness n p q ∧
    ∀ q' < q, q'.Prime → p < q' → ¬ Witness n p q'

/-- Some `k` has `n ≤ φ(k)`: any prime `k ≥ n + 1` has `φ(k) = k - 1 ≥ n`. -/
theorem exists_le_totient (n : ℕ) : ∃ k : ℕ, n ≤ Nat.totient k := by
  obtain ⟨k, hk, hkp⟩ := Nat.exists_infinite_primes (n + 1)
  refine ⟨k, ?_⟩
  rw [Nat.totient_prime hkp]
  omega

/-- `A066169(n)`: the least `k` such that `φ(k) ≥ n`. -/
def A066169 (n : ℕ) : ℕ :=
  Nat.find (exists_le_totient n)

/-! ## Decidable bridges -/

/-- The integer equation `n = p + q - r` with `r` prime is equivalent to
`n ≤ p + q` together with primality of the natural difference `p + q - n`. -/
theorem witness_iff (n p q : ℕ) :
    Witness n p q ↔ n ≤ p + q ∧ (p + q - n).Prime := by
  constructor
  · rintro ⟨r, hr, hEq⟩
    have hle : n ≤ p + q := by
      have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
      omega
    have hrEq : r = p + q - n := by omega
    exact ⟨hle, hrEq ▸ hr⟩
  · rintro ⟨hle, hprime⟩
    refine ⟨p + q - n, hprime, ?_⟩
    push_cast [hle]
    ring

/-- `A066169(n) = k` as soon as `n ≤ φ(k)` and `φ(j) < n` for every `j < k`. -/
theorem A066169_eq_of (n k : ℕ) (hk : n ≤ Nat.totient k)
    (hmin : ∀ j < k, Nat.totient j < n) : A066169 n = k := by
  unfold A066169
  rw [Nat.find_eq_iff]
  exact ⟨hk, fun j hj => Nat.not_le.mpr (hmin j hj)⟩

/-- `A270003(n) = 2` whenever some prime `q > 2` gives a witness: no prime lies
below `2`. -/
theorem isA270003_two (n q : ℕ) (hq : q.Prime) (h2q : 2 < q) (hw : Witness n 2 q) :
    IsA270003 n 2 :=
  ⟨Nat.prime_two, ⟨q, hq, h2q, hw⟩, fun p' hp' hprime => absurd hprime.two_le (by omega)⟩

/-- Assemble `IsA270753 n q` from `p = A270003(n)` and decidable conditions on `q`. -/
theorem isA270753_of (n p q : ℕ) (hp : IsA270003 n p) (hq : q.Prime) (hpq : p < q)
    (hw : n ≤ p + q ∧ (p + q - n).Prime)
    (hmin : ∀ q' < q, q'.Prime → p < q' → ¬ (n ≤ p + q' ∧ (p + q' - n).Prime)) :
    IsA270753 n q := by
  refine ⟨p, hp, hq, hpq, (witness_iff n p q).mpr hw, fun q' hq' hq'p hpq' => ?_⟩
  rw [witness_iff]
  exact hmin q' hq' hq'p hpq'

/-! ## Ground truth against the listed terms -/

/-- `A270003(1) = 3` (first listed term): `p = 2` fails because `r = q + 1` is even
and larger than `2` for every odd prime `q`, while `1 = 3 + 5 - 7`. -/
theorem isA270003_one : IsA270003 1 3 := by
  refine ⟨Nat.prime_three, ⟨5, by norm_num, by norm_num, ⟨7, by norm_num, by norm_num⟩⟩, ?_⟩
  intro p' hp' hprime ⟨q, hq, hpq, hw⟩
  have hp'2 : p' = 2 := by
    have := hprime.two_le
    omega
  subst hp'2
  obtain ⟨hle, hr⟩ := (witness_iff 1 2 q).mp hw
  rcases hq.eq_two_or_odd' with hq2 | hqodd
  · omega
  · have hreven : Even (2 + q - 1) := by
      obtain ⟨m, hm⟩ := hqodd
      exact ⟨m + 1, by omega⟩
    rcases hr.eq_two_or_odd' with hr2 | hrodd
    · omega
    · exact (Nat.not_even_iff_odd.mpr hrodd) hreven

-- `A270753(1) = 5`, `A270753(2) = 3`, `A270753(3) = 3`, `A270753(4) = 5`,
-- `A270753(66) = 67` (the last listed term).
example : IsA270753 1 5 :=
  isA270753_of 1 3 5 isA270003_one (by norm_num) (by norm_num) (by decide) (by decide)

example : IsA270753 2 3 :=
  isA270753_of 2 2 3 (isA270003_two 2 3 (by norm_num) (by norm_num) ⟨3, by norm_num, by norm_num⟩)
    (by norm_num) (by norm_num) (by decide) (by decide)

example : IsA270753 3 3 :=
  isA270753_of 3 2 3 (isA270003_two 3 3 (by norm_num) (by norm_num) ⟨2, by norm_num, by norm_num⟩)
    (by norm_num) (by norm_num) (by decide) (by decide)

example : IsA270753 4 5 :=
  isA270753_of 4 2 5 (isA270003_two 4 5 (by norm_num) (by norm_num) ⟨3, by norm_num, by norm_num⟩)
    (by norm_num) (by norm_num) (by decide) (by decide)

example : IsA270753 66 67 :=
  isA270753_of 66 2 67
    (isA270003_two 66 67 (by norm_num) (by norm_num) ⟨3, by norm_num, by norm_num⟩)
    (by norm_num) (by norm_num) (by decide) (by decide)

-- `A066169(1..7) = 1, 3, 5, 5, 7, 7, 11` (listed terms).
example : A066169 1 = 1 := A066169_eq_of 1 1 (by decide) (by decide)
example : A066169 2 = 3 := A066169_eq_of 2 3 (by decide) (by decide)
example : A066169 4 = 5 := A066169_eq_of 4 5 (by decide) (by decide)
example : A066169 7 = 11 := A066169_eq_of 7 11 (by decide) (by decide)

/-! ## The conjecture and its refutation -/

/-- **Mathar's conjecture (A270753, R. J. Mathar, Jun 21 2025).**

Verbatim: "Conjecture: a(n) = A066169(n-1) for n>2."

The statement is relational in `a(n)`: whenever `q = A270753(n)` is defined,
`q = A066169(n - 1)`.  This is the weakest reading (it is vacuous at any `n`
where A270003 or A270753 is undefined), so refuting it refutes every reading.
The truncated `n - 1` is guarded by `2 < n`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 2 < n → ∀ q : ℕ, IsA270753 n q → q = A066169 (n - 1)

/-- `A270753(90) = 101`: `A270003(90) = 2`, `90 = 2 + 101 - 13`, and no prime
`q` with `2 < q < 101` gives a prime `r = 2 + q - 90` (`q = 89` gives `1`,
`q = 97` gives `9`). -/
theorem isA270753_ninety : IsA270753 90 101 :=
  isA270753_of 90 2 101
    (isA270003_two 90 101 (by norm_num) (by norm_num) ⟨13, by norm_num, by norm_num⟩)
    (by norm_num) (by norm_num) (by decide) (by decide)

/-- `A066169(89) = 97`: `φ(97) = 96 ≥ 89`, and `φ(j) < 89` for every `j < 97`. -/
theorem A066169_eighty_nine : A066169 89 = 97 :=
  A066169_eq_of 89 97 (by decide) (by decide)

/-- **Mathar's conjecture is false.** Counterexample `n = 90`:
`A270753(90) = 101` but `A066169(89) = 97`.  The conjectured identity
`A270753(n) = nextprime(n - 1)` (the value of `A066169(n - 1)` for `n > 2`) fails
whenever `r = p + nextprime(n - 1) - n` is not prime; the first failures are
`n = 90, 91, 114, 115, 120`. -/
theorem a270753_mathar_false : ¬ Conjecture := by
  intro hconj
  have hq : (101 : ℕ) = A066169 (90 - 1) := hconj 90 (by norm_num) 101 isA270753_ninety
  have hval : A066169 (90 - 1) = 97 := A066169_eighty_nine
  omega

end Candidates.A270753Refutation
