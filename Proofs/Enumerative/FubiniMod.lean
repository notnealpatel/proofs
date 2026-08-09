import Mathlib
import Enumerative.Fubini

/-!
# Fubini numbers modulo k: Bala's periodicity conjecture (OEIS A000670)

Peter Bala conjectured (OEIS A000670 comments, Jul 08 2022) that for every
`1 ≤ k` the residue sequence `fubini n % k` is eventually periodic with
period dividing `Nat.totient k`.  This file proves that conjecture in full
(`fubini_mod_eventuallyPeriodic_conjecture`) against the project definition
`A051293.fubini`, after three explicit fixed-modulus warm-ups with closed
forms, `k = 2, 4, 16`.

* `k = 2`  : `fubini` is always odd, so the residues are `1, 1, 1, …`
  (period `1 = totient 2`, from `n = 0`).
* `k = 4`  : the residues are eventually `1, 3, 1, 3, …`
  (period `2 = totient 4`, from `n = 1`).
* `k = 16` : the residues are eventually `13, 11, 13, 11, …`
  (period `2 ∣ 8 = totient 16`, from `n = 3`); concretely
  `(fubini n : ZMod 16) = 12 - (-1)^n` for `3 ≤ n`.

The proofs are strong inductions on the project recurrence
`fubini (n+1) = ∑_{j<n+1} C(n+1,j) · fubini j`, evaluated in `ZMod 16`
(resp. `ZMod 2`) via the binomial row sums `∑_j C(n,j) = 2^n` and
`∑_j (-1)^j C(n,j) = 0`.

The general case follows the elementary route of B. Poonen, *Periodicity of a
combinatorial sequence*, Fibonacci Quarterly 26 (1988), 70–76.  Modulo `k` the
truncated sum `c k n = ∑_{j<k} 2^{k-1-j}·jⁿ` obeys the very same recurrence as
`fubini` and starts at `c k 0 = 2^k - 1`, whence
`(2^k - 1)·fubini n ≡ c k n (mod k)` for every `n`; at a prime power `k = p^m`
the right-hand side is `φ(p^m)`-periodic in `n` once `n ≥ m` (Euler for the
`j` coprime to `p`, nilpotence for the rest) and the left-hand factor is
invertible, and a Chinese-remainder induction over the factorization of `k`
glues the prime-power periods into `φ k`.

Every ground value is kernel-checked (`decide` after rewriting through the
recurrence's equation lemmas); no `native_decide` is used in this file, so
each sorry-free theorem below depends only on the standard axioms.
Ground truth follows the live OEIS A000670 data:
`1, 1, 3, 13, 75, 541, 4683, 47293, …`.
-/

set_option autoImplicit false

open Finset

namespace A000670

open A051293

/-! ## The recurrence in `Finset.range` form, and kernel-checked small values -/

/-- The Fubini recurrence `fubini (n+1) = ∑_{j≤n} C(n+1,j) · fubini j`,
restated as a sum over `Finset.range`. -/
private lemma fubini_succ_eq (n : ℕ) :
    fubini (n + 1) = ∑ j ∈ Finset.range (n + 1), (n + 1).choose j * fubini j := by
  have h : fubini (n + 1) = ∑ k : Fin (n + 1), (n + 1).choose k.val * fubini k.val := by
    simp only [fubini]
  rw [h, Fin.sum_univ_eq_sum_range (fun k => (n + 1).choose k * fubini k)]

/- Kernel-checked small values (OEIS A000670: 1, 1, 3, 13, 75, 541, 4683, 47293).
These duplicate `A051293.fubini_zero … fubini_five` locally and extend the
range to `n = 7`.  The duplication is historical: the imported lemmas were
once `native_decide`-backed, and commit 1637575 made them kernel-checked, so
today both routes carry the standard axiom footprint. -/

private lemma fubini_eval_zero : fubini 0 = 1 := by simp only [fubini]

private lemma fubini_eval_one : fubini 1 = 1 := by
  simp only [fubini_succ_eq, fubini_eval_zero, Finset.sum_range_succ, Finset.sum_range_zero]
  decide

private lemma fubini_eval_two : fubini 2 = 3 := by
  simp only [fubini_succ_eq, fubini_eval_zero, Finset.sum_range_succ, Finset.sum_range_zero]
  decide

private lemma fubini_eval_three : fubini 3 = 13 := by
  simp only [fubini_succ_eq, fubini_eval_zero, Finset.sum_range_succ, Finset.sum_range_zero]
  decide

private lemma fubini_eval_four : fubini 4 = 75 := by
  simp only [fubini_succ_eq, fubini_eval_zero, Finset.sum_range_succ, Finset.sum_range_zero]
  decide

private lemma fubini_eval_five : fubini 5 = 541 := by
  simp only [fubini_succ_eq, fubini_eval_zero, Finset.sum_range_succ, Finset.sum_range_zero]
  decide

private lemma fubini_eval_six : fubini 6 = 4683 := by
  simp only [fubini_succ_eq, fubini_eval_zero, Finset.sum_range_succ, Finset.sum_range_zero]
  decide

private lemma fubini_eval_seven : fubini 7 = 47293 := by
  simp only [fubini_succ_eq, fubini_eval_zero, Finset.sum_range_succ, Finset.sum_range_zero]
  decide

/-- Ground check against the live OEIS A000670 terms. -/
example : (fubini 0, fubini 1, fubini 2, fubini 3, fubini 4, fubini 5, fubini 6, fubini 7)
    = (1, 1, 3, 13, 75, 541, 4683, 47293) := by
  rw [fubini_eval_zero, fubini_eval_one, fubini_eval_two, fubini_eval_three,
    fubini_eval_four, fubini_eval_five, fubini_eval_six, fubini_eval_seven]

/-! ## Arithmetic helper lemmas -/

/-- `2^m = 0` in `ZMod 16` once `4 ≤ m`. -/
private lemma two_pow_zmod16 {m : ℕ} (hm : 4 ≤ m) : (2 : ZMod 16) ^ m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 + k := ⟨m - 4, by omega⟩
  have h4 : (2 : ZMod 16) ^ 4 = 0 := by decide
  rw [pow_add, h4, zero_mul]

/-- Division-free form of `C(n+1,2)`: `C(n+1,2) · 2 = (n+1) · n`. -/
private lemma choose_two_mul_two (n : ℕ) : (n + 1).choose 2 * 2 = (n + 1) * n := by
  have h2 : 2 ∣ (n + 1) * n := by
    have h := Nat.even_mul_succ_self n
    rw [mul_comm] at h
    exact h.two_dvd
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  exact Nat.div_mul_cancel h2

/-- Finite verification (over all 256 pairs of `ZMod 16`) of the even-index
step of the mod-16 pattern; `c` stands for `C(n+1,2)` with `n = x + x`. -/
private lemma key_even : ∀ x c : ZMod 16, c * 2 = (x + x + 1) * (x + x) →
    -34 - 12 * (x + x) - 8 * c - 1 = 13 := by decide

/-- Finite verification (over all 256 pairs of `ZMod 16`) of the odd-index
step of the mod-16 pattern; `c` stands for `C(n+1,2)` with `n = 2x + 1`. -/
private lemma key_odd : ∀ x c : ZMod 16, c * 2 = (2 * x + 1 + 1) * (2 * x + 1) →
    -34 - 12 * (2 * x + 1) - 8 * c + 1 = 11 := by decide

/-! ## Modulus 2: all Fubini numbers are odd -/

/-- In `ZMod 2` every Fubini number is `1`: by strong induction,
`fubini (n+1) ≡ ∑_{j≤n} C(n+1,j) = 2^{n+1} - 1 ≡ 1 (mod 2)`. -/
private lemma fubini_zmod2 (m : ℕ) : (fubini m : ZMod 2) = 1 := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    cases m with
    | zero => rw [fubini_eval_zero, Nat.cast_one]
    | succ n =>
      have h1 : (fubini (n + 1) : ZMod 2)
          = ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 2) * (fubini j : ZMod 2) := by
        rw [fubini_succ_eq, Nat.cast_sum]
        exact Finset.sum_congr rfl fun j _ => Nat.cast_mul _ _
      have h2 : ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 2) * (fubini j : ZMod 2)
          = ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 2) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [ih j (Finset.mem_range.mp hj), mul_one]
      have h_row : ∑ j ∈ Finset.range (n + 1 + 1), ((n + 1).choose j : ZMod 2) = 0 := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        have h20 : (2 : ZMod 2) = 0 := by decide
        rw [h20]
        exact zero_pow (by omega)
      have h_top : ∑ j ∈ Finset.range (n + 1 + 1), ((n + 1).choose j : ZMod 2)
          = (∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 2))
            + ((n + 1).choose (n + 1) : ZMod 2) :=
        Finset.sum_range_succ _ _
      have echoose : ((n + 1).choose (n + 1) : ZMod 2) = 1 := by
        rw [Nat.choose_self, Nat.cast_one]
      have hneg : (-1 : ZMod 2) = 1 := by decide
      rw [h1, h2]
      linear_combination (-1 : ZMod 2) * h_top + h_row - echoose + hneg

/-- Every Fubini number is odd (A000670 residues mod 2 are `1, 1, 1, …`). -/
theorem fubini_odd (n : ℕ) : Odd (fubini n) := by
  have h1 : ((fubini n : ℕ) : ZMod 2) = ((1 : ℕ) : ZMod 2) := by
    rw [fubini_zmod2, Nat.cast_one]
  have h2 : fubini n % 2 = 1 % 2 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  rw [Nat.odd_iff]
  omega

/-- Mod-2 instance of Bala's periodicity: `fubini` is constant `≡ 1 (mod 2)`,
so the residues have period `1 = Nat.totient 2` from `n = 0`. -/
theorem fubini_succ_modEq_two (n : ℕ) : fubini (n + 1) ≡ fubini n [MOD 2] :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mp
    ((fubini_zmod2 (n + 1)).trans (fubini_zmod2 n).symm)

/-! ## Modulus 16: the closed pattern `12 - (-1)^n` for `3 ≤ n` -/

/-- Closed form for the Fubini numbers in `ZMod 16`: for `3 ≤ m`,
`(fubini m : ZMod 16) = 12 - (-1)^m`, i.e. the residues alternate
`13, 11, 13, 11, …` from `m = 3` (matching the live OEIS data).

Proof: strong induction.  Split the recurrence row at `j = 3`, rewrite the
tail by the induction hypothesis, and evaluate both binomial row sums; the
boundary contributes `1 + (n+1) + 3·C(n+1,2)` and the tail collapses to
`-34 - 12n - 8·C(n+1,2) + (-1)^{n+1}`, which equals the pattern by the
finite checks `key_even`/`key_odd`. -/
private lemma fubini_zmod16 : ∀ m : ℕ, 3 ≤ m → (fubini m : ZMod 16) = 12 - (-1 : ZMod 16) ^ m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm
    rcases Nat.lt_or_ge m 4 with h4 | h4
    · -- base case `m = 3`: `fubini 3 = 13 = 12 - (-1)^3` in `ZMod 16`
      have hm3 : m = 3 := by omega
      subst hm3
      rw [fubini_eval_three]
      decide
    · -- step case `m = n + 1` with `3 ≤ n`
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hn3 : 3 ≤ n := by omega
      -- the recurrence, cast into `ZMod 16`
      have h1 : (fubini (n + 1) : ZMod 16)
          = ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 16) * (fubini j : ZMod 16) := by
        rw [fubini_succ_eq, Nat.cast_sum]
        exact Finset.sum_congr rfl fun j _ => Nat.cast_mul _ _
      -- split the row at `j = 3`
      have h2 : ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 16) * (fubini j : ZMod 16)
          = (∑ j ∈ Finset.range 3, ((n + 1).choose j : ZMod 16) * (fubini j : ZMod 16))
            + ∑ j ∈ Finset.Ico 3 (n + 1),
                ((n + 1).choose j : ZMod 16) * (fubini j : ZMod 16) :=
        (Finset.sum_range_add_sum_Ico _ (by omega)).symm
      -- boundary `j = 0, 1, 2` with `fubini = 1, 1, 3`
      have h3 : ∑ j ∈ Finset.range 3, ((n + 1).choose j : ZMod 16) * (fubini j : ZMod 16)
          = 2 + (n : ZMod 16) + 3 * ((n + 1).choose 2 : ZMod 16) := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, fubini_eval_zero,
          fubini_eval_one, fubini_eval_two, Nat.choose_zero_right, Nat.choose_one_right]
        push_cast
        ring
      -- rewrite the tail by the induction hypothesis
      have h4' : ∑ j ∈ Finset.Ico 3 (n + 1), ((n + 1).choose j : ZMod 16) * (fubini j : ZMod 16)
          = ∑ j ∈ Finset.Ico 3 (n + 1),
              ((n + 1).choose j : ZMod 16) * (12 - (-1 : ZMod 16) ^ j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨hj3, hjn⟩ := Finset.mem_Ico.mp hj
        rw [ih j hjn hj3]
      -- expand the pattern sum into the two row sums
      have h5 : ∑ j ∈ Finset.Ico 3 (n + 1),
            ((n + 1).choose j : ZMod 16) * (12 - (-1 : ZMod 16) ^ j)
          = 12 * (∑ j ∈ Finset.Ico 3 (n + 1), ((n + 1).choose j : ZMod 16))
            - ∑ j ∈ Finset.Ico 3 (n + 1), (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      -- full binomial row sum: `∑_j C(n+1,j) = 2^{n+1} = 0` in `ZMod 16`
      have h_row : ∑ j ∈ Finset.range (n + 1 + 1), ((n + 1).choose j : ZMod 16) = 0 := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        exact two_pow_zmod16 (by omega)
      -- alternating binomial row sum: `∑_j (-1)^j C(n+1,j) = 0`
      have h_alt : ∑ j ∈ Finset.range (n + 1 + 1),
          (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16) = 0 := by
        have hz : (∑ m ∈ Finset.range (n + 1 + 1), ((-1) ^ m * ((n + 1).choose m : ℤ))) = 0 := by
          rw [Int.alternating_sum_range_choose]
          simp
        calc ∑ j ∈ Finset.range (n + 1 + 1), (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16)
            = ((∑ m ∈ Finset.range (n + 1 + 1),
                ((-1) ^ m * ((n + 1).choose m : ℤ)) : ℤ) : ZMod 16) := by
              push_cast
              rfl
          _ = 0 := by rw [hz]; rfl
      have echoose : ((n + 1).choose (n + 1) : ZMod 16) = 1 := by
        rw [Nat.choose_self, Nat.cast_one]
      -- tail of the plain row sum
      have h9 : ∑ j ∈ Finset.Ico 3 (n + 1), ((n + 1).choose j : ZMod 16)
          = -3 - (n : ZMod 16) - ((n + 1).choose 2 : ZMod 16) := by
        have e1 : (∑ j ∈ Finset.range 3, ((n + 1).choose j : ZMod 16))
            + ∑ j ∈ Finset.Ico 3 (n + 1), ((n + 1).choose j : ZMod 16)
            = ∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 16) :=
          Finset.sum_range_add_sum_Ico _ (by omega)
        have e2 : ∑ j ∈ Finset.range (n + 1 + 1), ((n + 1).choose j : ZMod 16)
            = (∑ j ∈ Finset.range (n + 1), ((n + 1).choose j : ZMod 16))
              + ((n + 1).choose (n + 1) : ZMod 16) :=
          Finset.sum_range_succ _ _
        have er3 : ∑ j ∈ Finset.range 3, ((n + 1).choose j : ZMod 16)
            = 2 + (n : ZMod 16) + ((n + 1).choose 2 : ZMod 16) := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero,
            Nat.choose_zero_right, Nat.choose_one_right]
          push_cast
          ring
        linear_combination e1 - e2 + h_row - er3 - echoose
      -- tail of the alternating row sum
      have h10 : ∑ j ∈ Finset.Ico 3 (n + 1), (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16)
          = -((-1 : ZMod 16) ^ (n + 1)) + (n : ZMod 16) - ((n + 1).choose 2 : ZMod 16) := by
        have a1 : (∑ j ∈ Finset.range 3, (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16))
            + ∑ j ∈ Finset.Ico 3 (n + 1), (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16)
            = ∑ j ∈ Finset.range (n + 1), (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16) :=
          Finset.sum_range_add_sum_Ico _ (by omega)
        have a2 : ∑ j ∈ Finset.range (n + 1 + 1), (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16)
            = (∑ j ∈ Finset.range (n + 1), (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16))
              + (-1 : ZMod 16) ^ (n + 1) * ((n + 1).choose (n + 1) : ZMod 16) :=
          Finset.sum_range_succ _ _
        have ar3 : ∑ j ∈ Finset.range 3, (-1 : ZMod 16) ^ j * ((n + 1).choose j : ZMod 16)
            = ((n + 1).choose 2 : ZMod 16) - (n : ZMod 16) := by
          simp only [Finset.sum_range_succ, Finset.sum_range_zero,
            Nat.choose_zero_right, Nat.choose_one_right]
          push_cast
          ring
        linear_combination a1 - a2 + h_alt - ar3 - (-1 : ZMod 16) ^ (n + 1) * echoose
      -- collapse the recurrence to a closed expression
      have hmain : (fubini (n + 1) : ZMod 16)
          = -34 - 12 * (n : ZMod 16) - 8 * ((n + 1).choose 2 : ZMod 16)
            + (-1 : ZMod 16) ^ (n + 1) := by
        linear_combination h1 + h2 + h3 + h4' + h5 + 12 * h9 - h10
      rw [hmain]
      -- close by parity, using the division-free `C(n+1,2)` identity
      rcases Nat.even_or_odd n with he | ho
      · obtain ⟨t, rfl⟩ := he
        have hodd : Odd (t + t + 1) := ⟨t, by ring⟩
        rw [hodd.neg_one_pow]
        have hc : ((t + t + 1).choose 2 : ZMod 16) * 2
            = ((t : ZMod 16) + t + 1) * ((t : ZMod 16) + t) := by
          have h := congrArg (fun m : ℕ => (m : ZMod 16)) (choose_two_mul_two (t + t))
          push_cast at h
          exact h
        push_cast
        linear_combination key_even (t : ZMod 16) ((t + t + 1).choose 2 : ZMod 16) hc
      · obtain ⟨t, rfl⟩ := ho
        have heven : Even (2 * t + 1 + 1) := ⟨t + 1, by ring⟩
        rw [heven.neg_one_pow]
        have hc : ((2 * t + 1 + 1).choose 2 : ZMod 16) * 2
            = (2 * (t : ZMod 16) + 1 + 1) * (2 * (t : ZMod 16) + 1) := by
          have h := congrArg (fun m : ℕ => (m : ZMod 16)) (choose_two_mul_two (2 * t + 1))
          push_cast at h
          exact h
        push_cast
        linear_combination key_odd (t : ZMod 16) ((2 * t + 1 + 1).choose 2 : ZMod 16) hc

/-- Mod-16 instance of Bala's periodicity (OEIS A000670 comment): from
`n = 3` the residues mod 16 alternate `13, 11, 13, 11, …`, so the sequence
is eventually periodic with period `2`, which divides `Nat.totient 16 = 8`. -/
theorem fubini_add_two_modEq_sixteen (n : ℕ) (hn : 3 ≤ n) :
    fubini (n + 2) ≡ fubini n [MOD 16] := by
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  rw [fubini_zmod16 (n + 2) (by omega), fubini_zmod16 n hn]
  ring

/-- Mod-4 instance of Bala's periodicity: from `n = 1` the residues mod 4
alternate `1, 3, 1, 3, …`, so the sequence is eventually periodic with
period `2 = Nat.totient 4`. -/
theorem fubini_add_two_modEq_four (n : ℕ) (hn : 1 ≤ n) :
    fubini (n + 2) ≡ fubini n [MOD 4] := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · show fubini 3 ≡ fubini 1 [MOD 4]
      rw [fubini_eval_three, fubini_eval_one]
      decide
    · show fubini 4 ≡ fubini 2 [MOD 4]
      rw [fubini_eval_four, fubini_eval_two]
      decide
  · exact (fubini_add_two_modEq_sixteen n h3).of_dvd (by norm_num)

/-! ## Bala's claim, in the card's existential shape, for k = 2, 4, 16 -/

/-- Bala's periodicity claim at `k = 2`: some positive period `P` dividing
`Nat.totient 2` works from some index `N` on (here `N = 0`, `P = 1`). -/
theorem fubini_mod_two_eventuallyPeriodic :
    ∃ N P : ℕ, P ∣ Nat.totient 2 ∧ 0 < P ∧
      ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD 2] :=
  ⟨0, 1, one_dvd _, one_pos, fun n _ => fubini_succ_modEq_two n⟩

/-- Bala's periodicity claim at `k = 4`: some positive period `P` dividing
`Nat.totient 4` works from some index `N` on (here `N = 1`, `P = 2`). -/
theorem fubini_mod_four_eventuallyPeriodic :
    ∃ N P : ℕ, P ∣ Nat.totient 4 ∧ 0 < P ∧
      ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD 4] :=
  ⟨1, 2, by decide, two_pos, fun n hn => fubini_add_two_modEq_four n hn⟩

/-- Bala's periodicity claim at `k = 16`: some positive period `P` dividing
`Nat.totient 16 = 8` works from some index `N` on (here `N = 3`, `P = 2`). -/
theorem fubini_mod_sixteen_eventuallyPeriodic :
    ∃ N P : ℕ, P ∣ Nat.totient 16 ∧ 0 < P ∧
      ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD 16] :=
  ⟨3, 2, by decide, two_pos, fun n hn => fubini_add_two_modEq_sixteen n hn⟩

/-! ## Poonen's truncated-power congruence

The general case follows B. Poonen, *Periodicity of a combinatorial sequence*,
Fibonacci Quarterly 26 (1988), 70–76 (Corollary to Lemma 1, and Theorems 2, 6).

The engine is the finite sum `c k n = ∑_{j < k} 2^{k-1-j} · jⁿ`, namely `2^k`
times the `j < k` truncation of the series `∑_j jⁿ/2^{j+1} = fubini n`
(`A051293.fubini_polylog`) — but used purely algebraically, so that no
convergence argument enters.  Modulo `k` it satisfies the *same* linear
recurrence as `fubini`, namely
`x n = ∑_{m < n} C(n,m) · x m`, and its value at `n = 0` is `2^k - 1`; hence
`(2^k - 1) · fubini n ≡ c k n (mod k)` for every `n`.  Since `c k n` is a fixed
finite combination of the powers `jⁿ`, it is periodic in `n` as soon as every
`jⁿ` is, which at a prime power `k = p^m` is Euler's theorem for `p ∤ j` and
nilpotence for `p ∣ j`.  This is exactly the step the naive surjection-sum
decomposition `fubini n = ∑_{m ≤ n} m!·S(n,m)` cannot make: its summation range
grows with `n`. -/

/-- The `n = 0` step of the recurrence for Poonen's truncated sum:
`∑_{j < k} 2^{k-1-j} = 2^k - 1`, a geometric sum read backwards. -/
private lemma poonen_zero (k : ℕ) :
    ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) = (2 : ZMod k) ^ k - 1 := by
  have hgeom := geom_sum_mul (2 : ZMod k) k
  rw [show (2 : ZMod k) - 1 = 1 by ring, mul_one] at hgeom
  rw [Finset.sum_range_reflect (fun j => (2 : ZMod k) ^ j) k, hgeom]

/-- Shifting the base `j ↦ j + 1` doubles Poonen's truncated sum modulo `k`
(for `1 ≤ n`): the shift moves the window from `[0, k)` to `[1, k]`, the new
top term `kⁿ` vanishes mod `k`, the dropped bottom term `0ⁿ` vanishes since
`1 ≤ n`, and every remaining weight `2^{k-1-j}` is replaced by `2^{k-j}`. -/
private lemma poonen_shift (k n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * ((j : ZMod k) + 1) ^ n
      = 2 * ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * (j : ZMod k) ^ n := by
  have hzero : (0 : ZMod k) ^ n = 0 := zero_pow (by omega)
  have hk : ((k : ℕ) : ZMod k) = 0 := ZMod.natCast_self k
  -- read the window `[0, k]` with weights `2^{k-j}` from the top …
  have hTop : (∑ j ∈ Finset.range (k + 1), (2 : ZMod k) ^ (k - j) * (j : ZMod k) ^ n)
      = 2 * ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * (j : ZMod k) ^ n := by
    rw [Finset.sum_range_succ, hk, hzero, mul_zero, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    have hidx : k - j = (k - 1 - j) + 1 := by omega
    rw [hidx, pow_succ]
    ring
  -- … and from the bottom
  have hBot : (∑ j ∈ Finset.range (k + 1), (2 : ZMod k) ^ (k - j) * (j : ZMod k) ^ n)
      = ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * ((j : ZMod k) + 1) ^ n := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, hzero, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hidx : k - (j + 1) = k - 1 - j := by omega
    rw [hidx]
  rw [← hBot, hTop]

/-- The binomial transform of Poonen's truncated sum is its base shift:
`∑_{m ≤ n} C(n,m) · c k m = ∑_{j < k} 2^{k-1-j} (j+1)ⁿ`, by the binomial
theorem applied inside the (finite, rectangular) double sum. -/
private lemma poonen_binomial (k n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (n.choose m : ZMod k) *
        ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * (j : ZMod k) ^ m
      = ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * ((j : ZMod k) + 1) ^ n := by
  have hbin : ∀ j : ℕ, ((j : ZMod k) + 1) ^ n
      = ∑ m ∈ Finset.range (n + 1), (n.choose m : ZMod k) * (j : ZMod k) ^ m := by
    intro j
    rw [add_pow]
    exact Finset.sum_congr rfl fun m _ => by rw [one_pow, mul_one]; ring
  simp_rw [hbin, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring

/-- **Poonen's congruence** (Corollary to Lemma 1 of the 1988 paper):
`(2^k - 1) · fubini n ≡ ∑_{j < k} 2^{k-1-j} · jⁿ (mod k)`, for every `k` and
every `n`.  Proved by strong induction on `n`: both sides obey the Fubini
recurrence `x n = ∑_{m < n} C(n,m) · x m` modulo `k` and agree at `n = 0`. -/
private lemma poonen_congr (k : ℕ) : ∀ n : ℕ,
    ((2 : ZMod k) ^ k - 1) * (fubini n : ZMod k)
      = ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * (j : ZMod k) ^ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero =>
      simp only [pow_zero, mul_one, fubini_eval_zero, Nat.cast_one]
      exact (poonen_zero k).symm
    | succ n =>
      -- the truncated sum obeys the Fubini recurrence modulo `k`
      have hrec : ∑ m ∈ Finset.range (n + 1),
            ((n + 1).choose m : ZMod k) *
              ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * (j : ZMod k) ^ m
          = ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * (j : ZMod k) ^ (n + 1) := by
        have hb := poonen_binomial k (n + 1)
        rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul,
          poonen_shift k (n + 1) (by omega)] at hb
        linear_combination hb
      -- and rewriting it by the induction hypothesis reproduces `fubini (n+1)`
      have hih : ∑ m ∈ Finset.range (n + 1),
            ((n + 1).choose m : ZMod k) *
              ∑ j ∈ Finset.range k, (2 : ZMod k) ^ (k - 1 - j) * (j : ZMod k) ^ m
          = ((2 : ZMod k) ^ k - 1) * (fubini (n + 1) : ZMod k) := by
        have hcast : ((fubini (n + 1) : ℕ) : ZMod k)
            = ∑ m ∈ Finset.range (n + 1),
                ((n + 1).choose m : ZMod k) * (fubini m : ZMod k) := by
          rw [fubini_succ_eq, Nat.cast_sum]
          exact Finset.sum_congr rfl fun m _ => Nat.cast_mul _ _
        rw [hcast, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [← ih m (Finset.mem_range.mp hm)]
        ring
      rw [← hih, hrec]

/-! ## The prime-power core -/

/-- Generalized Euler theorem at a prime power: for `m ≤ n` and any `j`,
`j^(n + φ(p^m)) = jⁿ` in `ZMod (p^m)`.  If `p ∤ j` this is Euler's theorem;
if `p ∣ j` both sides are `0`, since `p^m ∣ p^n ∣ jⁿ`. -/
private lemma pow_add_totient_prime_pow {p : ℕ} (hp : p.Prime) {m n : ℕ} (hn : m ≤ n) (j : ℕ) :
    (j : ZMod (p ^ m)) ^ (n + Nat.totient (p ^ m)) = (j : ZMod (p ^ m)) ^ n := by
  by_cases hj : p ∣ j
  · -- `p ∣ j`: both sides vanish, since `p ^ m ∣ p ^ n ∣ j ^ n`
    obtain ⟨t, rfl⟩ := hj
    have hzero : ∀ N : ℕ, m ≤ N → ((p * t : ℕ) : ZMod (p ^ m)) ^ N = 0 := by
      intro N hN
      push_cast
      rw [mul_pow, ZMod.natCast_pow_eq_zero_of_le p hN, zero_mul]
    rw [hzero (n + Nat.totient (p ^ m)) (by omega), hzero n hn]
  · -- `p ∤ j`: Euler's theorem
    have hcop : Nat.Coprime j (p ^ m) :=
      ((hp.coprime_iff_not_dvd).mpr hj).symm.pow_right m
    have heuler : (j : ZMod (p ^ m)) ^ Nat.totient (p ^ m) = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient hcop)
      push_cast at h
      exact h
    rw [pow_add, heuler, mul_one]

/-- `2^(p^m) - 1` is invertible modulo `p^m` — the cancellation that turns
Poonen's congruence into a statement about `fubini` itself.  Iterating Fermat's
little theorem gives `2^(p^i) = 2` in `ZMod p`, so `2^(p^m) - 1 ≡ 1 (mod p)`;
hence `p ∤ 2^(p^m) - 1`, and coprimality to `p^m` follows.  (Note this is where
the prime-power restriction is essential: `gcd (2^k - 1) k = 7` at `k = 21`.) -/
private lemma isUnit_two_pow_prime_pow_sub_one {p : ℕ} (hp : p.Prime) (m : ℕ) :
    IsUnit ((2 : ZMod (p ^ m)) ^ (p ^ m) - 1) := by
  haveI := Fact.mk hp
  -- iterated Fermat: `2 ^ (p ^ i) = 2` in `ZMod p`
  have hfermat : ∀ i : ℕ, (2 : ZMod p) ^ p ^ i = 2 := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_one]
    | succ i ihi => rw [pow_succ, pow_mul, ihi, ZMod.pow_card]
  have hone : 1 ≤ 2 ^ p ^ m := Nat.one_le_two_pow
  have hndvd : ¬ p ∣ (2 ^ p ^ m - 1) := by
    intro hdvd
    have hmod : (1 : ℕ) ≡ 2 ^ p ^ m [MOD p] := (Nat.modEq_iff_dvd' hone).mpr hdvd
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    push_cast at h
    rw [hfermat m] at h
    exact one_ne_zero (α := ZMod p) (by linear_combination (-1 : ZMod p) * h)
  have hcop : Nat.Coprime (2 ^ p ^ m - 1) (p ^ m) :=
    ((hp.coprime_iff_not_dvd).mpr hndvd).symm.pow_right m
  have hcast : ((2 ^ p ^ m - 1 : ℕ) : ZMod (p ^ m)) = (2 : ZMod (p ^ m)) ^ p ^ m - 1 := by
    rw [Nat.cast_sub hone]
    push_cast
    ring
  rw [← hcast]
  exact (ZMod.isUnit_iff_coprime _ _).mpr hcop

/-- **Poonen, Theorem 2**: at a prime power `p^m` the Fubini numbers are
periodic modulo `p^m` with period `φ(p^m)`, from index `m` on. -/
private lemma fubini_modEq_prime_pow {p : ℕ} (hp : p.Prime) {m n : ℕ} (hn : m ≤ n) :
    fubini (n + Nat.totient (p ^ m)) ≡ fubini n [MOD p ^ m] := by
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  refine (isUnit_two_pow_prime_pow_sub_one hp m).mul_left_cancel ?_
  rw [poonen_congr (p ^ m) (n + Nat.totient (p ^ m)), poonen_congr (p ^ m) n]
  exact Finset.sum_congr rfl fun j _ => by rw [pow_add_totient_prime_pow hp hn j]

/-! ## Gluing: multiples of a period, and the Chinese remainder step -/

/-- A period stays a period after iteration: from `fubini (n + P) ≡ fubini n`
for all `n ≥ N` one gets `fubini (n + t·P) ≡ fubini n` for all `n ≥ N`. -/
private lemma fubini_modEq_mul {q N P : ℕ}
    (h : ∀ n, N ≤ n → fubini (n + P) ≡ fubini n [MOD q]) :
    ∀ t n, N ≤ n → fubini (n + t * P) ≡ fubini n [MOD q] := by
  intro t
  induction t with
  | zero => intro n _; simpa using Nat.ModEq.refl (fubini n)
  | succ t iht =>
    intro n hn
    have hstep : fubini (n + t * P + P) ≡ fubini (n + t * P) [MOD q] :=
      h (n + t * P) (le_trans hn (Nat.le_add_right _ _))
    have hidx : n + (t + 1) * P = n + t * P + P := by ring
    rw [hidx]
    exact hstep.trans (iht n hn)

/-- Bala's conjecture in the strengthened form carried by the induction on the
factorization of `k`: *every* multiple of `φ k` is an eventual period. -/
private lemma fubini_eventuallyPeriodic (k : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ P, Nat.totient k ∣ P → fubini (n + P) ≡ fubini n [MOD k] := by
  induction k using Nat.recOnPosPrimePosCoprime with
  | prime_pow p m hp hm =>
    refine ⟨m, fun n hn P hP => ?_⟩
    obtain ⟨t, rfl⟩ := hP
    rw [mul_comm]
    exact fubini_modEq_mul
      (fun n' hn' => fubini_modEq_prime_pow hp hn') t n hn
  | zero =>
    refine ⟨0, fun n _ P hP => ?_⟩
    have hP0 : P = 0 := Nat.eq_zero_of_zero_dvd (by simpa using hP)
    rw [hP0, Nat.add_zero]
  | one => exact ⟨0, fun n _ P _ => Nat.modEq_one⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨Na, hNa⟩ := iha
    obtain ⟨Nb, hNb⟩ := ihb
    refine ⟨max Na Nb, fun n hn P hP => ?_⟩
    rw [Nat.totient_mul hab] at hP
    have hPa : Nat.totient a ∣ P := (Dvd.intro _ rfl).trans hP
    have hPb : Nat.totient b ∣ P := (Dvd.intro_left _ rfl).trans hP
    exact (Nat.modEq_and_modEq_iff_modEq_mul hab).mp
      ⟨hNa n (le_of_max_le_left hn) P hPa, hNb n (le_of_max_le_right hn) P hPb⟩

/-! ## The general conjecture -/

/-- **Bala's conjecture** (OEIS A000670 comments, Peter Bala, Jul 08 2022;
repeated at A354242 and A002050): for every `1 ≤ k` the sequence
`fubini n mod k` is eventually periodic with period dividing
`Nat.totient k`.  The explicit instances `k = 2, 4, 16` are above.

Proof: `fubini_eventuallyPeriodic` supplies the threshold `N` together with
the fact that *every* multiple of `φ k` is a period from `N` on, so `φ k`
itself serves as `P`; `Nat.totient_pos` turns `1 ≤ k` into `0 < P`.

Attribution note (literature sweep, 2026-07-29): the mathematics here is not
new.  Eventual periodicity of `fubini` modulo any positive integer, *with*
the totient bound, is B. Poonen, *Periodicity of a combinatorial sequence*,
Fibonacci Quarterly 26 (1988), 70–76: his Theorem 2 is the prime-power
statement `fubini (n + φ(p^m)) ≡ fubini n (mod p^m)` for `n ≥ m`, and his
Theorem 6 identifies the exact period modulo `r` as an lcm of prime-power
periods, which divides `φ r`.  The prime-power case is also Barsky's theorem,
by p-adic analysis of the e.g.f. `1/(2 - eˣ)`.  The formalization is
self-contained and elementary — in particular `poonen_congr` is proved by
strong induction on `n`, not from the real-analytic series identity Poonen
inherits from Good — but it is a formalization, not a novelty claim. -/
theorem fubini_mod_eventuallyPeriodic_conjecture (k : ℕ) (hk : 1 ≤ k) :
    ∃ N P : ℕ, P ∣ Nat.totient k ∧ 0 < P ∧
      ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD k] := by
  obtain ⟨N, hN⟩ := fubini_eventuallyPeriodic k
  exact ⟨N, Nat.totient k, dvd_rfl, Nat.totient_pos.mpr hk, fun n hn => hN n hn _ dvd_rfl⟩

/-! ## Ground checks and nonvacuity

The congruence instances at concrete indices, checked against the live
OEIS A000670 values, plus sharpness witnesses showing the starting indices
and the mod-16 pattern are not vacuous. -/

-- residues mod 16 from `n = 3`: `13, 11, 13, 11` (OEIS: 13, 75, 541, 4683)
example : fubini 3 % 16 = 13 ∧ fubini 4 % 16 = 11
    ∧ fubini 5 % 16 = 13 ∧ fubini 6 % 16 = 11 := by
  rw [fubini_eval_three, fubini_eval_four, fubini_eval_five, fubini_eval_six]
  decide

-- residues mod 4 from `n = 1`: `1, 3, 1, 3`
example : fubini 1 % 4 = 1 ∧ fubini 2 % 4 = 3
    ∧ fubini 3 % 4 = 1 ∧ fubini 4 % 4 = 3 := by
  rw [fubini_eval_one, fubini_eval_two, fubini_eval_three, fubini_eval_four]
  decide

-- the mod-16 theorem instantiated at its smallest index `n = 3`
example : fubini (3 + 2) ≡ fubini 3 [MOD 16] :=
  fubini_add_two_modEq_sixteen 3 (by omega)

-- sharpness: period 2 mod 16 fails at `n = 2` (`fubini 4 = 75 ≡ 11 ≠ 3`)
example : ¬ fubini (2 + 2) ≡ fubini 2 [MOD 16] := by
  show ¬ fubini 4 ≡ fubini 2 [MOD 16]
  rw [fubini_eval_four, fubini_eval_two]
  decide

-- sharpness: period 2 mod 4 fails at `n = 0` (`fubini 2 = 3 ≢ 1`)
example : ¬ fubini (0 + 2) ≡ fubini 0 [MOD 4] := by
  show ¬ fubini 2 ≡ fubini 0 [MOD 4]
  rw [fubini_eval_two, fubini_eval_zero]
  decide

-- Poonen's congruence at `k = 5, n = 3`, kernel-checked in `ZMod 5`:
-- `31 · 13 ≡ 8·1 + 4·8 + 2·27 + 1·64 = 158 (mod 5)`, both sides `3`
example : ((2 : ZMod 5) ^ 5 - 1) * (fubini 3 : ZMod 5)
    = ∑ j ∈ Finset.range 5, (2 : ZMod 5) ^ (5 - 1 - j) * (j : ZMod 5) ^ 3 := by
  rw [fubini_eval_three]
  decide

-- the general theorem at `k = 21`, where `gcd (2^k - 1) k = 7 ≠ 1`: the
-- cancellation in `poonen_congr` is unavailable at the modulus itself, so the
-- prime-power decomposition carries the proof.  (`k = 6`, with `gcd = 3`, is
-- the smallest such modulus; `21` is the smallest odd one.)
example : ∃ N P : ℕ, P ∣ Nat.totient 21 ∧ 0 < P ∧
    ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD 21] :=
  fubini_mod_eventuallyPeriodic_conjecture 21 (by norm_num)

-- the general theorem at the degenerate modulus `k = 1`
example : ∃ N P : ℕ, P ∣ Nat.totient 1 ∧ 0 < P ∧
    ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD 1] :=
  fubini_mod_eventuallyPeriodic_conjecture 1 (by norm_num)

-- residues mod 5 (period `totient 5 = 4` from `n = 1`): `1, 3, 3, 0, 1`
example : fubini 1 % 5 = 1 ∧ fubini 2 % 5 = 3 ∧ fubini 3 % 5 = 3
    ∧ fubini 4 % 5 = 0 ∧ fubini 5 % 5 = 1 := by
  rw [fubini_eval_one, fubini_eval_two, fubini_eval_three, fubini_eval_four,
    fubini_eval_five]
  decide

-- sharpness of "eventually" at `k = 5`: the period-4 congruence fails at `n = 0`
example : ¬ fubini (0 + 4) ≡ fubini 0 [MOD 5] := by
  show ¬ fubini 4 ≡ fubini 0 [MOD 5]
  rw [fubini_eval_four, fubini_eval_zero]
  decide

end A000670
