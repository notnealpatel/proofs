/-
Prime terms of OEIS A071241 (Amarnath Murthy, May 20 2002).

The claim that the only prime means (k+reverse(k))/2 for even-digit k are
2, 11 and 101 is refuted by k=280, reverse(k)=82 and mean 181.
Harvey P. Dale records the refutation in the entry (Sep 02 2016).
The formal relation is k+reverse(k)=2m, without rounding.
The prime values below 1000 are classified as 2, 11, 101, 181, 383, 727 and 787;
no unbounded classification is claimed.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A071241Refutation

/-! ## Definitions -/

/-- `R(k)`, the decimal digit reversal of `k` (OEIS A004086): reverse the
little-endian digit list and read it back, so trailing zeros of `k` are
dropped, e.g. `R(280) = 82`. -/
def digitRev (k : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 k).reverse

/-- `k` uses only even decimal digits (OEIS A014263).  `k = 0` qualifies since
`Nat.digits 10 0 = []`, matching the entry's first term `a(1) = 0`. -/
def AllEvenDigits (k : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 k, Even d

instance : DecidablePred AllEvenDigits := fun k => by
  unfold AllEvenDigits
  infer_instance

/-! ## Examples -/

example : digitRev 280 = 82 := by decide
example : digitRev 1230 = 321 := by decide
example : AllEvenDigits 0 ∧ AllEvenDigits 280 ∧ ¬ AllEvenDigits 281 ∧
    ¬ AllEvenDigits 1000 := by decide

-- The first 59 listed terms of A071241: means `(k + R(k)) / 2` over the
-- even-digit `k` in increasing order (the 59th such `k` is `426`).
example : ((List.range 427).filter (fun k => decide (AllEvenDigits k))).map
      (fun k => (k + digitRev k) / 2) =
    [0, 2, 4, 6, 8, 11, 22, 33, 44, 55, 22, 33, 44, 55, 66, 33, 44, 55, 66, 77,
      44, 55, 66, 77, 88, 101, 202, 303, 404, 505, 121, 222, 323, 424, 525, 141,
      242, 343, 444, 545, 161, 262, 363, 464, 565, 181, 282, 383, 484, 585, 202,
      303, 404, 505, 606, 222, 323, 424, 525] := by
  decide

/-! ## The conjecture -/

/-- Murthy's A071241 conjecture: every prime `m` with `k+R(k)=2m` for an
even-digit `k` belongs to `{2,11,101}`. The equation states the mean without
truncated natural division. -/
def Conjecture : Prop :=
  ∀ k m : ℕ, AllEvenDigits k → k + digitRev k = 2 * m → m.Prime →
    m = 2 ∨ m = 11 ∨ m = 101

-- The hypotheses are jointly satisfiable, at `k = 20`, `m = 11`.
example : AllEvenDigits 20 ∧ 20 + digitRev 20 = 2 * 11 ∧ Nat.Prime 11 := by
  refine ⟨by decide, by decide, by norm_num⟩

/-! ## Refutation -/

/-- Dale's counterexample to A071241: `280` has even digits, reverses to
`82`, and gives the prime mean `181`, outside `{2,11,101}`. -/
theorem a071241_conjecture_false : ¬ Conjecture := by
  intro hconj
  have hdigits : AllEvenDigits 280 := by decide
  have hsum : 280 + digitRev 280 = 2 * 181 := by decide
  have hprime : Nat.Prime 181 := by norm_num
  have hcases := hconj 280 181 hdigits hsum hprime
  omega

/-! ## Corrected bounded form -/

/-- Finite check behind `prime_term_lt_thousand_iff`: for every even-digit
`k < 2000` whose mean `(k + R(k)) / 2` is prime, that mean is one of
`2, 11, 101, 181, 383, 727, 787`. -/
theorem prime_mean_mem_of_lt_two_thousand :
    ∀ k < 2000, AllEvenDigits k → ((k + digitRev k) / 2).Prime →
      (k + digitRev k) / 2 ∈ ({2, 11, 101, 181, 383, 727, 787} : Finset ℕ) := by
  set_option maxRecDepth 100000 in decide

/-- **Corrected classification below 1000.**  The prime terms of A071241 that
are less than `1000` are exactly `2, 11, 101, 181, 383, 727, 787`: a prime
`m < 1000` satisfies `k + R(k) = 2 * m` for some even-digit `k` if and only if
`m` is one of these seven primes. -/
theorem prime_term_lt_thousand_iff (m : ℕ) (hm : m < 1000) (hprime : m.Prime) :
    (∃ k, AllEvenDigits k ∧ k + digitRev k = 2 * m) ↔
      m ∈ ({2, 11, 101, 181, 383, 727, 787} : Finset ℕ) := by
  constructor
  · rintro ⟨k, hk, hsum⟩
    have hk2000 : k < 2000 := by omega
    have hmean : (k + digitRev k) / 2 = m := by omega
    have hmem := prime_mean_mem_of_lt_two_thousand k hk2000 hk (hmean ▸ hprime)
    rwa [hmean] at hmem
  · intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨20, by decide, by decide⟩
    · exact ⟨200, by decide, by decide⟩
    · exact ⟨280, by decide, by decide⟩
    · exact ⟨284, by decide, by decide⟩
    · exact ⟨628, by decide, by decide⟩
    · exact ⟨688, by decide, by decide⟩

end Candidates.A071241Refutation
