import Mathlib
import Enumerative.Fubini

/-!
# Fubini numbers modulo k: Bala's periodicity conjecture (OEIS A000670)

Peter Bala conjectured (OEIS A000670 comments, Jul 08 2022) that for every
`1 ≤ k` the residue sequence `fubini n % k` is eventually periodic with
period dividing `Nat.totient k`.  This file proves the fixed-modulus
instances `k = 2, 4, 16` against the project definition `A051293.fubini`
and states the general conjecture (an intended `sorry`: the general claim
is open).

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
These deliberately avoid the imported `native_decide`-backed lemmas of
`Enumerative.Fubini`, keeping the axiom footprint standard. -/

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

/-! ## The general conjecture (open) -/

/-- **Bala's conjecture** (OEIS A000670 comments, Peter Bala, Jul 08 2022;
repeated at A354242 and A002050): for every `1 ≤ k` the sequence
`fubini n mod k` is eventually periodic with period dividing
`Nat.totient k`.  The instances `k = 2, 4, 16` are proved above; the
general statement is open (the prime-power case is Barsky's theorem, via
p-adic analysis of the e.g.f. `1/(2 - eˣ)`), hence the intended `sorry`.

Attribution note (literature sweep, 2026-07-29): eventual periodicity of
`fubini` modulo any positive integer — without the totient-period
refinement conjectured here — is classical: B. Poonen, *Periodicity of a
combinatorial sequence*, Fibonacci Quarterly 26 (1988), 70–76; the mod-4
and oddness instances above are corollaries of Poonen/Barsky, and the
explicit mod-16 closed form follows from their period bounds plus a
finite check.  The proofs in this file are self-contained formalizations,
not novelty claims. -/
theorem fubini_mod_eventuallyPeriodic_conjecture (k : ℕ) (hk : 1 ≤ k) :
    ∃ N P : ℕ, P ∣ Nat.totient k ∧ 0 < P ∧
      ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD k] := by
  sorry

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

end A000670
