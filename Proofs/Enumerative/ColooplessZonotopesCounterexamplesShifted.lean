/-
# Counterexamples to the Shifted Lonely Runner Conjecture

Mónica Blanco, Francisco Criado and Francisco Santos, *Coloopless zonotopes
and counterexamples to the Shifted Lonely Runner Conjecture*, arXiv:2603.24784:
Conjecture `conj:sLRC`, Theorem `thm:12345`, Figure `fig:12345` and
Propositions `prop:counters5`(1), `prop:counters6`(1),(2).
The conjecture is attributed to Wills via Beck–Hosten–Schymura (2019), Conjecture 10.

For every real time some runner is within the indicated distance of an integer:
* velocities `(1,2,3,4,5)`, shifts `(0,46,38,47,72)/94`: distance at most `15/94`;
* velocities `(2,3,4,5,6,8)`, shifts `(0,29,17,0,16,22)/30`: at most `2/15`;
* velocities `(1,2,3,4,5,6)`, shifts `(0,39,37,51,62,54)/67`: at most `9/67`.
These bounds refute the conjecture for five and six runners. Only upper bounds
are proved, not the paper's optimized-gap equalities or other dimensions.
`distToInt x=|x-round x|` is identified with the norm on `ℝ/ℤ`.
Exact cell certificates cover all real times, using integer velocities and
translation periodicity.
-/
import Mathlib

set_option autoImplicit false
/- The three certificate checks are each a deep kernel reduction.  Elaborated
asynchronously, their kernel threads run concurrently and thread creation fails
under the 14 GB virtual-memory cap; synchronous elaboration avoids this. -/
set_option Elab.async false

namespace ShiftedLonelyRunner

/-! ## Definitions -/

/-- `dist(x, ℤ)`, the distance from a real number to the nearest integer. -/
noncomputable def distToInt (x : ℝ) : ℝ := |x - round x|

/-- `distToInt` is the norm on the circle `ℝ/ℤ`, i.e. the genuine distance from
`x` to the lattice `ℤ`. -/
theorem distToInt_eq_norm_addCircle (x : ℝ) : distToInt x = ‖(x : AddCircle (1 : ℝ))‖ := by
  rw [AddCircle.norm_eq, inv_one, one_mul, mul_one, distToInt]

/-- `dist(x, ℤ) ≤ |x - k|` for every integer `k`. -/
theorem distToInt_le_abs_sub (x : ℝ) (k : ℤ) : distToInt x ≤ |x - k| := round_le x k

example : distToInt (1 / 3) = 1 / 3 := by norm_num [distToInt]
example : distToInt (5 / 2) = 1 / 2 := by norm_num [distToInt, round_eq]
example : distToInt (-7 / 4) = 1 / 4 := by norm_num [distToInt, round_eq]

/-- **Shifted Lonely Runner Conjecture** (Conjecture `conj:sLRC`) for `n` runners: for
non-zero real velocities `v_1, …, v_n` with pairwise distinct `|v_i|` and any
starting positions `s_1, …, s_n`, some time `t` has
`dist(s_i + v_i t, ℤ) ≥ 1/(n+1)` for all `i`. -/
def ShiftedLonelyRunnerConjecture (n : ℕ) : Prop :=
  ∀ v : Fin n → ℝ, (∀ i, v i ≠ 0) → Function.Injective (fun i => |v i|) →
    ∀ s : Fin n → ℝ, ∃ t : ℝ, ∀ i, 1 / ((n : ℝ) + 1) ≤ distToInt (s i + v i * t)

/-- Examples (non-vacuity of the definition): the conjecture holds for one
runner, by running it to the point `1/2`. -/
theorem shiftedLonelyRunnerConjecture_one : ShiftedLonelyRunnerConjecture 1 := by
  intro v hv _ s
  refine ⟨(1 / 2 - s 0) / v 0, fun i => ?_⟩
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have hx : s 0 + v 0 * ((1 / 2 - s 0) / v 0) = 1 / 2 := by
    field_simp [hv 0]
    ring
  rw [hx]
  norm_num [distToInt, round_eq]

/-! ## The finite certificate -/

/-- Cell test.  For the residue `r`, runner `i` with integer velocity `v i` and
shift numerator `c * S i` (over the common denominator `L`), and the largest
integer `k = ⌊(c S_i + v_i r + R) / L⌋` with `k L ≤ c S_i + v_i r + R`, check
`c S_i + v_i (r + 1) ≤ k L + R`.  Then `|L(s_i + v_i t) - k L| ≤ R` on the cell
`L t ∈ [r, r + 1]`. -/
def cellOk {n : ℕ} (v S : Fin n → ℕ) (c L R r : ℕ) (i : Fin n) : Bool :=
  Nat.ble (c * S i + v i * r + v i) ((c * S i + v i * r + R) / L * L + R)

/-- `coverBlock … base k` checks that every residue in `[base, base + k)` passes
the cell test for some runner. -/
def coverBlock {n : ℕ} (v S : Fin n → ℕ) (c L R base : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => (List.finRange n).any (cellOk v S c L R (base + k)) && coverBlock v S c L R base k

/-- `coverBlocks … B Q` checks `Q` consecutive blocks of length `B`, i.e. every
residue in `[0, Q B)`. -/
def coverBlocks {n : ℕ} (v S : Fin n → ℕ) (c L R B : ℕ) : ℕ → Bool
  | 0 => true
  | q + 1 => coverBlock v S c L R (q * B) B && coverBlocks v S c L R B q

/- at `t ∈ [0, 1/5640]` runner `1` (velocity `1`, shift `0`) is
within `15/94` of `0`, while runner `2` (velocity `2`, shift `46/94`) is not
within `15/94` of an integer. -/
example : cellOk ![1, 2, 3, 4, 5] ![0, 46, 38, 47, 72] 60 5640 900 0 0 = true := by decide
example : cellOk ![1, 2, 3, 4, 5] ![0, 46, 38, 47, 72] 60 5640 900 0 1 = false := by decide

/-- Soundness of one block: every residue `base + j` with `j < k` passes the cell
test for some runner. -/
theorem coverBlock_sound {n : ℕ} (v S : Fin n → ℕ) (c L R base : ℕ) :
    ∀ k, coverBlock v S c L R base k = true → ∀ j < k, ∃ i, cellOk v S c L R (base + j) i = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, h, j, hj => by
    simp only [coverBlock, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨i, _, hi⟩, hrest⟩ := h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | rfl
    · exact coverBlock_sound v S c L R base k hrest j hjk
    · exact ⟨i, hi⟩

/-- Soundness of the block check: every residue `r < Q B` passes the cell test. -/
theorem coverBlocks_sound {n : ℕ} (v S : Fin n → ℕ) (c L R B : ℕ) :
    ∀ Q, coverBlocks v S c L R B Q = true → ∀ r < Q * B, ∃ i, cellOk v S c L R r i = true
  | 0, _, r, hr => by simp at hr
  | Q + 1, h, r, hr => by
    simp only [coverBlocks, Bool.and_eq_true] at h
    obtain ⟨hblock, hrest⟩ := h
    by_cases hrQ : r < Q * B
    · exact coverBlocks_sound v S c L R B Q hrest r hrQ
    · obtain ⟨i, hi⟩ := coverBlock_sound v S c L R (Q * B) B hblock (r - Q * B)
        (by rw [Nat.succ_mul] at hr; omega)
      exact ⟨i, by rwa [Nat.add_sub_cancel' (by omega)] at hi⟩


/-! ## From the certificate to the reals -/

/-- One cell.  If runner `i` passes the cell test at residue `r`, then for every
`t` with `q L + r ≤ L t ≤ q L + r + 1` (`q ∈ ℤ`) the runner position
`S_i / D + v_i t` is within `R / L` of the integer `k + v_i q`. -/
theorem abs_sub_le_of_cellOk {n : ℕ} (v S : Fin n → ℕ) (c D L R r : ℕ) (i : Fin n)
    (hcD : c * D = L) (hL : 0 < L) (hcell : cellOk v S c L R r i = true) (q : ℤ) (t : ℝ)
    (hlo : (q : ℝ) * L + r ≤ L * t) (hhi : L * t ≤ (q : ℝ) * L + r + 1) :
    |(S i : ℝ) / D + v i * t - (((c * S i + v i * r + R) / L : ℕ) + v i * q : ℤ)| ≤
      (R : ℝ) / L := by
  set k : ℕ := (c * S i + v i * r + R) / L with hk
  have hk1 : k * L ≤ c * S i + v i * r + R := Nat.div_mul_le_self _ _
  have hk2 : c * S i + v i * r + v i ≤ k * L + R := Nat.le_of_ble_eq_true hcell
  have hD : (D : ℝ) ≠ 0 := by
    rintro hD0
    have hD0' : D = 0 := by exact_mod_cast hD0
    rw [hD0', mul_zero] at hcD
    omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hcDr : (c : ℝ) * D = L := by exact_mod_cast hcD
  have hk1r : (k : ℝ) * L ≤ c * S i + v i * r + R := by exact_mod_cast hk1
  have hk2r : (c : ℝ) * S i + v i * r + v i ≤ k * L + R := by exact_mod_cast hk2
  have hv : (0 : ℝ) ≤ v i := Nat.cast_nonneg _
  have hscale : (L : ℝ) * ((S i : ℝ) / D + v i * t - ((k : ℤ) + v i * q : ℤ)) =
      c * S i + v i * (L * t) - k * L - v i * (q * L) := by
    rw [← hcDr]
    push_cast
    field_simp
    ring
  have hmlo := mul_le_mul_of_nonneg_left hlo hv
  have hmhi := mul_le_mul_of_nonneg_left hhi hv
  rw [le_div_iff₀ hLpos]
  calc |(S i : ℝ) / D + v i * t - ((k : ℤ) + v i * q : ℤ)| * L
      = |(L : ℝ) * ((S i : ℝ) / D + v i * t - ((k : ℤ) + v i * q : ℤ))| := by
        rw [abs_mul, abs_of_pos hLpos, mul_comm]
    _ ≤ R := by
        rw [hscale, abs_le]
        constructor <;> linarith

/-- Generic covering criterion.  If the block certificate passes for all residues
`r < Q B = L`, then at every time `t` some runner with integer velocity `v i` and
start `S i / D` (where `c D = L`) is within `R / L` of an integer. -/
theorem exists_distToInt_le_of_coverBlocks {n : ℕ} (v S : Fin n → ℕ) (c D L R B Q : ℕ)
    (hcD : c * D = L) (hQB : Q * B = L) (hL : 0 < L)
    (hcov : coverBlocks v S c L R B Q = true) (t : ℝ) :
    ∃ i, distToInt ((S i : ℝ) / D + v i * t) ≤ (R : ℝ) / L := by
  set m : ℤ := ⌊(L : ℝ) * t⌋ with hm
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hr0 : 0 ≤ m % L := Int.emod_nonneg m hLz.ne'
  have hrL : m % L < L := Int.emod_lt_of_pos m hLz
  have hdecomp : (L : ℤ) * (m / L) + m % L = m := Int.mul_ediv_add_emod m L
  have hrNat : ((m % L).toNat : ℤ) = m % L := Int.toNat_of_nonneg hr0
  have hcast : ((m / L : ℤ) : ℝ) * L + ((m % L).toNat : ℕ) = m := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hdecomp
    have hrr : (((m % L).toNat : ℕ) : ℝ) = ((m % L : ℤ) : ℝ) := by exact_mod_cast hrNat
    push_cast at h
    rw [hrr, ← h]
    ring
  obtain ⟨i, hi⟩ := coverBlocks_sound v S c L R B Q hcov (m % L).toNat (by omega)
  refine ⟨i, (distToInt_le_abs_sub _ _).trans
    (abs_sub_le_of_cellOk v S c D L R (m % L).toNat i hcD hL hi (m / L) t ?_ ?_)⟩
  · have hfl : (m : ℝ) ≤ L * t := Int.floor_le _
    linarith
  · have hfl : L * t < (m : ℝ) + 1 := Int.lt_floor_add_one _
    linarith

/-- A single instance `(v, s)` whose runners never all reach distance `> ρ` from
`ℤ`, with `ρ < 1/(n+1)`, `v` nonzero and `|v_i|` pairwise distinct, refutes the
conjecture for `n` runners. -/
theorem not_shiftedLonelyRunnerConjecture_of_cover {n : ℕ} (v s : Fin n → ℝ) (ρ : ℝ)
    (hv : ∀ i, v i ≠ 0) (hinj : Function.Injective (fun i => |v i|))
    (hρ : ρ < 1 / ((n : ℝ) + 1)) (hcov : ∀ t : ℝ, ∃ i, distToInt (s i + v i * t) ≤ ρ) :
    ¬ ShiftedLonelyRunnerConjecture n := by
  intro hconj
  obtain ⟨t, ht⟩ := hconj v hv hinj s
  obtain ⟨i, hi⟩ := hcov t
  exact absurd ((ht i).trans hi) (not_le.mpr hρ)

/-! ## `n = 5`: `v = (1,2,3,4,5)`, `s = (0,46,38,47,72)/94` (Theorem `thm:12345`, Figure `fig:12345`) -/

/-- The velocity vector `(1, 2, 3, 4, 5)`. -/
noncomputable def v5 : Fin 5 → ℝ := ![1, 2, 3, 4, 5]

/-- The starting positions `(1/94)(0, 46, 38, 47, 72)`. -/
noncomputable def s5 : Fin 5 → ℝ := ![0, 46 / 94, 38 / 94, 47 / 94, 72 / 94]

/-- Certificate for `(1,2,3,4,5)`, shifts `/94`, radius `15/94`:
`L = 94 · lcm(1,…,5) = 5640`, radius `900 / 5640 = 15/94`, `12` blocks of `470`. -/
theorem coverBlocks_five :
    coverBlocks ![1, 2, 3, 4, 5] ![0, 46, 38, 47, 72] 60 5640 900 470 12 = true := by
  decide +kernel

/-- **Figure `fig:12345` / Proposition `prop:counters5`(1), upper bound.**  For
`v = (1,2,3,4,5)` and `s = (1/94)(0,46,38,47,72)`, at every time `t ∈ ℝ` some runner
satisfies `dist(s_i + v_i t, ℤ) ≤ 15/94`; hence `sgap(1,2,3,4,5) ≤ 15/94`. -/
theorem exists_distToInt_le_fifteen_div_ninetyFour (t : ℝ) :
    ∃ i : Fin 5, distToInt (s5 i + v5 i * t) ≤ 15 / 94 := by
  obtain ⟨i, hi⟩ := exists_distToInt_le_of_coverBlocks ![1, 2, 3, 4, 5] ![0, 46, 38, 47, 72]
    60 94 5640 900 470 12 rfl rfl (by norm_num) coverBlocks_five t
  refine ⟨i, ?_⟩
  have hs : s5 i = ((![0, 46, 38, 47, 72] : Fin 5 → ℕ) i : ℝ) / (94 : ℕ) := by
    fin_cases i <;> norm_num [s5]
  have hv : v5 i = ((![1, 2, 3, 4, 5] : Fin 5 → ℕ) i : ℝ) := by
    fin_cases i <;> norm_num [v5]
  have hρ : ((900 : ℕ) : ℝ) / (5640 : ℕ) = 15 / 94 := by norm_num
  rw [hs, hv, ← hρ]
  exact hi

/-- `15/94 < 1/6`. -/
theorem fifteen_div_ninetyFour_lt : (15 : ℝ) / 94 < 1 / ((5 : ℕ) + 1) := by norm_num

/-- **Theorem `thm:12345`, `n = 5`.**  The Shifted Lonely Runner Conjecture fails for five
runners, witnessed by `v = (1,2,3,4,5)` and `s = (1/94)(0,46,38,47,72)`. -/
theorem not_shiftedLonelyRunnerConjecture_five : ¬ ShiftedLonelyRunnerConjecture 5 := by
  refine not_shiftedLonelyRunnerConjecture_of_cover v5 s5 (15 / 94) ?_ ?_
    fifteen_div_ninetyFour_lt exists_distToInt_le_fifteen_div_ninetyFour
  · intro i
    fin_cases i <;> norm_num [v5]
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [v5] at h)

/-! ## `n = 6`: Proposition `prop:counters6`(1),(2) -/

/-- The velocity vector `(2, 3, 4, 5, 6, 8)`. -/
noncomputable def v6a : Fin 6 → ℝ := ![2, 3, 4, 5, 6, 8]

/-- The starting positions `(1/30)(0, 29, 17, 0, 16, 22)`. -/
noncomputable def s6a : Fin 6 → ℝ := ![0, 29 / 30, 17 / 30, 0, 16 / 30, 22 / 30]

/-- Certificate for `(2,3,4,5,6,8)`, shifts `/30`, radius `2/15`:
`L = 30 · lcm(2,3,4,5,6,8) = 3600`, radius `480 / 3600 = 2/15`, `8` blocks of `450`. -/
theorem coverBlocks_six_a :
    coverBlocks ![2, 3, 4, 5, 6, 8] ![0, 29, 17, 0, 16, 22] 120 3600 480 450 8 = true := by
  decide +kernel

/-- **Proposition `prop:counters6`(1), upper bound.**  For `v = (2,3,4,5,6,8)` and
`s = (1/30)(0,29,17,0,16,22)`, at every time `t ∈ ℝ` some runner satisfies
`dist(s_i + v_i t, ℤ) ≤ 2/15`; hence `sgap(2,3,4,5,6,8) ≤ 2/15`. -/
theorem exists_distToInt_le_two_div_fifteen (t : ℝ) :
    ∃ i : Fin 6, distToInt (s6a i + v6a i * t) ≤ 2 / 15 := by
  obtain ⟨i, hi⟩ := exists_distToInt_le_of_coverBlocks ![2, 3, 4, 5, 6, 8]
    ![0, 29, 17, 0, 16, 22] 120 30 3600 480 450 8 rfl rfl (by norm_num) coverBlocks_six_a t
  refine ⟨i, ?_⟩
  have hs : s6a i = ((![0, 29, 17, 0, 16, 22] : Fin 6 → ℕ) i : ℝ) / (30 : ℕ) := by
    fin_cases i <;> norm_num [s6a]
  have hv : v6a i = ((![2, 3, 4, 5, 6, 8] : Fin 6 → ℕ) i : ℝ) := by
    fin_cases i <;> norm_num [v6a]
  have hρ : ((480 : ℕ) : ℝ) / (3600 : ℕ) = 2 / 15 := by norm_num
  rw [hs, hv, ← hρ]
  exact hi

/-- The velocity vector `(1, 2, 3, 4, 5, 6)`. -/
noncomputable def v6b : Fin 6 → ℝ := ![1, 2, 3, 4, 5, 6]

/-- The starting positions `(1/67)(0, 39, 37, 51, 62, 54)`. -/
noncomputable def s6b : Fin 6 → ℝ := ![0, 39 / 67, 37 / 67, 51 / 67, 62 / 67, 54 / 67]

/-- Certificate for `(1,…,6)`, shifts `/67`, radius `9/67`:
`L = 67 · lcm(1,…,6) = 4020`, radius `540 / 4020 = 9/67`, `12` blocks of `335`. -/
theorem coverBlocks_six_b :
    coverBlocks ![1, 2, 3, 4, 5, 6] ![0, 39, 37, 51, 62, 54] 60 4020 540 335 12 = true := by
  decide +kernel

/-- **Proposition `prop:counters6`(2), upper bound.**  For `v = (1,2,3,4,5,6)` and
`s = (1/67)(0,39,37,51,62,54)`, at every time `t ∈ ℝ` some runner satisfies
`dist(s_i + v_i t, ℤ) ≤ 9/67`; hence `sgap(1,2,3,4,5,6) ≤ 9/67`. -/
theorem exists_distToInt_le_nine_div_sixtySeven (t : ℝ) :
    ∃ i : Fin 6, distToInt (s6b i + v6b i * t) ≤ 9 / 67 := by
  obtain ⟨i, hi⟩ := exists_distToInt_le_of_coverBlocks ![1, 2, 3, 4, 5, 6]
    ![0, 39, 37, 51, 62, 54] 60 67 4020 540 335 12 rfl rfl (by norm_num) coverBlocks_six_b t
  refine ⟨i, ?_⟩
  have hs : s6b i = ((![0, 39, 37, 51, 62, 54] : Fin 6 → ℕ) i : ℝ) / (67 : ℕ) := by
    fin_cases i <;> norm_num [s6b]
  have hv : v6b i = ((![1, 2, 3, 4, 5, 6] : Fin 6 → ℕ) i : ℝ) := by
    fin_cases i <;> norm_num [v6b]
  have hρ : ((540 : ℕ) : ℝ) / (4020 : ℕ) = 9 / 67 := by norm_num
  rw [hs, hv, ← hρ]
  exact hi

/-- **Theorem `thm:12345`, `n = 6`.**  The Shifted Lonely Runner Conjecture fails for six
runners, witnessed by `v = (2,3,4,5,6,8)`, `s = (1/30)(0,29,17,0,16,22)`
(`2/15 < 1/7`). -/
theorem not_shiftedLonelyRunnerConjecture_six : ¬ ShiftedLonelyRunnerConjecture 6 := by
  refine not_shiftedLonelyRunnerConjecture_of_cover v6a s6a (2 / 15) ?_ ?_ (by norm_num)
    exists_distToInt_le_two_div_fifteen
  · intro i
    fin_cases i <;> norm_num [v6a]
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [v6a] at h)

/-- **Theorem `thm:12345`, `n = 6`, second witness.**  `v = (1,2,3,4,5,6)` with
`s = (1/67)(0,39,37,51,62,54)` also refutes the conjecture (`9/67 < 1/7`). -/
theorem not_shiftedLonelyRunnerConjecture_six' : ¬ ShiftedLonelyRunnerConjecture 6 := by
  refine not_shiftedLonelyRunnerConjecture_of_cover v6b s6b (9 / 67) ?_ ?_ (by norm_num)
    exists_distToInt_le_nine_div_sixtySeven
  · intro i
    fin_cases i <;> norm_num [v6b]
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [v6b] at h)

end ShiftedLonelyRunner
