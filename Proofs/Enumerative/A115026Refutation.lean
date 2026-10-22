/-
# A counterexample to the bound for A115026

Source: Harvey P. Dale's OEIS A115026 comment (Jun 08 2022), asserting
that no term exceeds 370. Iteration of A101337 sums the decimal digits
raised to the number of digits; the sequence selects the least value in
the eventual cycle.
Here `a(371)=371` and `a(119)=371`, by the fixed point 371 and the orbit
`119 → 731 → 371`. Neither minimality of 119 nor eventual periodicity
of every input orbit is proved here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A115026Refutation

open Function

/-! ## Definitions -/

/-- A101337: the sum of the decimal digits of `n`, each raised to the power
of the number of decimal digits of `n` (with `f 0 = 0`). -/
def f (n : ℕ) : ℕ := ((Nat.digits 10 n).map (· ^ (Nat.digits 10 n).length)).sum

/-- A115026: the least element of the cycle eventually reached by iterating
`f` from `n`, i.e. the infimum of the orbit points of `n` that are periodic
under `f`.  (On an empty set `sInf` returns `0`; this junk value could only
make the conjectured bound easier, and the refutation below exhibits the
cycle explicitly.) -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m | (∃ k, f^[k] n = m) ∧ m ∈ periodicPts f}

/-- Dale's A115026 conjecture: no term at a positive index exceeds 370. -/
def Conjecture : Prop := ∀ n : ℕ, 1 ≤ n → a n ≤ 370

/-! ## Computing `a` from a closed finite cycle -/

/-- A periodic point in the forward orbit of `n` lies in every `f`-closed set
that the orbit enters. -/
theorem mem_of_periodic_of_iterate_mem {n x : ℕ} (C : Set ℕ) (hC : Set.MapsTo f C C)
    {j : ℕ} (hj : f^[j] n ∈ C) {i : ℕ} (hi : f^[i] n = x) (hx : x ∈ periodicPts f) :
    x ∈ C := by
  obtain ⟨q, hq, hqx⟩ := hx
  have hper : IsPeriodicPt f (q * (j + 1)) x := hqx.mul_const (j + 1)
  have hle : j ≤ q * (j + 1) + i := by nlinarith
  have hsplit : q * (j + 1) + i = (q * (j + 1) + i - j) + j := by omega
  have hx_eq : x = f^[(q * (j + 1) + i - j)] (f^[j] n) := by
    rw [← iterate_add_apply, ← hsplit, iterate_add_apply, hi]
    exact hper.eq.symm
  rw [hx_eq]
  exact hC.iterate _ hj

/-- If the orbit of `n` reaches `m`, `m` is periodic, and `m` lies in an
`f`-closed finite set `C` whose minimum is `m`, then `a n = m`. -/
theorem a_eq_of_cycle {n m : ℕ} (C : Finset ℕ) (hC : ∀ y ∈ C, f y ∈ C)
    (hmC : m ∈ C) (hmin : ∀ y ∈ C, m ≤ y) (k : ℕ) (hk : f^[k] n = m)
    (p : ℕ) (hp : 0 < p) (hmp : f^[p] m = m) : a n = m := by
  have hmaps : Set.MapsTo f (C : Set ℕ) (C : Set ℕ) := fun y hy => hC y hy
  have hmem : m ∈ {m | (∃ k, f^[k] n = m) ∧ m ∈ periodicPts f} :=
    ⟨⟨k, hk⟩, ⟨p, hp, hmp⟩⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨m, hmem⟩
  rintro x ⟨⟨i, hi⟩, hx⟩
  have hjC : f^[k] n ∈ (C : Set ℕ) := by rw [hk]; exact hmC
  exact hmin x (mem_of_periodic_of_iterate_mem (C : Set ℕ) hmaps hjC hi hx)

/-! ## Examples -/

-- `f` agrees with the first 74 listed terms of A101337 (offset 1).
example : (List.range 74).map (fun i => f (i + 1)) =
    [1,2,3,4,5,6,7,8,9,1,2,5,10,17,26,37,50,65,82,4,5,8,13,20,29,40,53,68,85,9,10,
     13,18,25,34,45,58,73,90,16,17,20,25,32,41,52,65,80,97,25,26,29,34,41,50,61,74,
     89,106,36,37,40,45,52,61,72,85,100,117,49,50,53,58,65] := by decide

-- `a(1) = 1`: `1` is a fixed point.
example : a 1 = 1 :=
  a_eq_of_cycle {1} (by decide) (by decide) (by decide) 0 rfl 1 one_pos (by decide)

-- `a(13) = 1`: `13 ↦ 10 ↦ 1`.
example : a 13 = 1 :=
  a_eq_of_cycle {1} (by decide) (by decide) (by decide) 2 (by decide) 1 one_pos
    (by decide)

-- `a(25) = 370`: `25 ↦ 29 ↦ 85 ↦ 89 ↦ 145 ↦ 190 ↦ 730 ↦ 370 ↦ 370`.
example : a 25 = 370 :=
  a_eq_of_cycle {370} (by decide) (by decide) (by decide) 7 (by decide) 1 one_pos
    (by decide)

-- `a(59) = 160`, the entry's own cycle example: `59 ↦ 106 ↦ 217 ↦ 352 ↦ 160 ↦ 217`.
example : a 59 = 160 :=
  a_eq_of_cycle {160, 217, 352} (by decide) (by decide) (by decide) 4 (by decide)
    3 (by decide) (by decide)

/-! ## The refutation -/

/-- `371 = 3^3 + 7^3 + 1^3` is a fixed point of A101337, so `a(371) = 371`. -/
theorem a_371 : a 371 = 371 :=
  a_eq_of_cycle {371} (by decide) (by decide) (by decide) 0 rfl 1 one_pos (by decide)

/-- The orbit `119 → 731 → 371 → 371` gives `a(119)=371`.
Minimality as a counterexample is not asserted. -/
theorem a_119 : a 119 = 371 :=
  a_eq_of_cycle {371} (by decide) (by decide) (by decide) 2 (by decide) 1 one_pos
    (by decide)

/-- Dale's bound fails: the fixed point 371 gives `a(371)=371 > 370`.
The orbit from 119 supplies another counterexample (`a_119`). -/
theorem conjecture_false : ¬ Conjecture := fun h => by
  have h371 := h 371 (by norm_num)
  rw [a_371] at h371
  norm_num at h371

end Candidates.A115026Refutation
