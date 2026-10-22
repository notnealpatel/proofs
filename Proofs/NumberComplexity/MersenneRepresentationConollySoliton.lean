/-
# Mersenne representation: the A055938 difference rule and the A080578 relation

Fumitaka Yura, “Mersenne Representation, the Conolly Sequence, and
Soliton Profiles over Finite Fields”, arXiv:2607.22202, §3.3,
Proposition `prop:A055938-difference`, and §4.1,
Theorem `thm:A080578-A055938`.
The binary side is the set of finite sums of distinct weights `2^k-1`,
`k ≥ 1` (A005187); its complement is A055938. Its successive gaps are
`3-2χ_J(n)` for `n ≥ 1`, and `A080578(n) = A055938(n-1)+2` for `n ≥ 2`
(the relation conjectured by R. Stephan in A080578, 2013).
The proof uses `b(m) = ∑_{i∈bits(m)} (2^(i+1)-1)`, with
`b(2j) = b(j)+2j` and `b(2j+1) = b(2j)+1`. The complement is a union
of blocks `(b(2j+1),b(2j+2))`; its count below `b(k)` is `b(k)-k`,
and block-end indices are the values `b(j+1)`.
-/
import Mathlib

set_option autoImplicit false

namespace MersenneRepresentationConollySoliton

/-! ## Definitions mirroring the paper -/

/-- The binary side `C(J̄)` (OEIS A005187 as a set): all finite sums of distinct
Mersenne weights `2^k - 1` with `k ≥ 1` (the empty sum is `0`). -/
def binarySide : Set ℕ :=
  {n | ∃ s : Finset ℕ, (∀ k ∈ s, 1 ≤ k) ∧ ∑ k ∈ s, (2 ^ k - 1) = n}

/-- The nonbinary side `C(J)`: the complement of the binary side in `ℕ`
(the value set of OEIS A055938). -/
def nonbinarySide : Set ℕ := binarySideᶜ

/-- `mersenneBinaryValue m = ∑_{i ∈ bits(m)} (2^(i+1) - 1)`: the value of the
binary Mersenne word whose `1`-digits sit at the positions `i + 1` for the set
bits `i` of `m`.  It equals `2m - s₂(m)` (OEIS A005187). -/
def mersenneBinaryValue (m : ℕ) : ℕ := (m.bitIndices.map fun i => 2 ^ (i + 1) - 1).sum

/-- `A055938(n)` for `n ≥ 1`: the `n`-th smallest element (1-based) of the
nonbinary side.  The value at `n = 0` is a junk value and is never used. -/
noncomputable def a055938 (n : ℕ) : ℕ := Nat.nth (· ∈ nonbinarySide) (n - 1)

/-- Auxiliary state for A080578: `a080578State n = (a(n), [a(n), …, a(1)])`,
built by the OEIS rule `a(1) = 1`, `a(n) = a(n-1) + (1 if n ∈ {a(1..n-1)} else 3)`. -/
def a080578State : ℕ → ℕ × List ℕ
  | 0 => (0, [])
  | 1 => (1, [1])
  | n + 2 =>
    let st := a080578State (n + 1)
    let v := st.1 + if n + 2 ∈ st.2 then 1 else 3
    (v, v :: st.2)

/-- OEIS A080578 (offset 1): `a(1) = 1`; for `n > 1`, `a(n) = a(n-1) + 1` if `n`
already occurs among `a(1), …, a(n-1)`, else `a(n) = a(n-1) + 3`.
The value at `n = 0` is the junk value `0`. -/
def a080578 (n : ℕ) : ℕ := (a080578State n).1

/-! ## Examples for the definitions -/

/-- First terms of A080578 as listed in the OEIS. -/
example : (List.range 16).map (fun n => a080578 (n + 1)) =
    [1, 4, 7, 8, 11, 14, 15, 16, 19, 22, 23, 26, 29, 30, 31, 32] := by decide

/-- First terms of A005187 (`0, 1, 3, 4, 7, 8, 10, 11, 15, …`). -/
example : (List.range 9).map mersenneBinaryValue = [0, 1, 3, 4, 7, 8, 10, 11, 15] := by
  decide

/-- `mersenneBinaryValue m + s₂(m) = 2m` on an initial range (OEIS formula for A005187). -/
example : (List.range 32).all
    (fun m => mersenneBinaryValue m + (Nat.digits 2 m).sum == 2 * m) := by decide

/-- `4 = (2^1 - 1) + (2^2 - 1)` lies on the binary side. -/
example : 4 ∈ binarySide := ⟨{1, 2}, by decide, by decide⟩

/-! ## Recurrences for `mersenneBinaryValue` -/

/-- `b(2j) = b(j) + 2j`. -/
theorem mersenneBinaryValue_two_mul (j : ℕ) :
    mersenneBinaryValue (2 * j) = mersenneBinaryValue j + 2 * j := by
  have hpt : ∀ i : ℕ, 2 ^ (i + 1 + 1) - 1 = (2 ^ (i + 1) - 1) + 2 * 2 ^ i := by
    intro i
    have h1 : 1 ≤ 2 ^ (i + 1) := Nat.one_le_two_pow
    rw [pow_succ, pow_succ]
    rw [pow_succ] at h1
    omega
  unfold mersenneBinaryValue
  rw [Nat.bitIndices_two_mul, List.map_map]
  have hfun : ((fun i : ℕ => 2 ^ (i + 1) - 1) ∘ (· + 1)) =
      fun i => (2 ^ (i + 1) - 1) + 2 * 2 ^ i := funext hpt
  rw [hfun, List.sum_map_add, List.sum_map_mul_left, Nat.sum_map_two_pow_bitIndices]

/-- `b(2j+1) = b(2j) + 1`. -/
theorem mersenneBinaryValue_two_mul_add_one (j : ℕ) :
    mersenneBinaryValue (2 * j + 1) = mersenneBinaryValue (2 * j) + 1 := by
  unfold mersenneBinaryValue
  rw [Nat.bitIndices_two_mul_add_one, Nat.bitIndices_two_mul, List.map_cons, List.sum_cons]
  omega

/-- Short local name for `mersenneBinaryValue` (the paper's binary-side
enumeration, A005187). -/
local notation "b" => mersenneBinaryValue

/-- `b(m) + 1 ≤ b(m+1)`. -/
theorem mersenneBinaryValue_succ_ge (m : ℕ) : b m + 1 ≤ b (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · rw [mersenneBinaryValue_two_mul_add_one]
    · have hj : j < 2 * j + 1 := by omega
      have h1 := ih j hj
      have h2 : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
      rw [h2, mersenneBinaryValue_two_mul, mersenneBinaryValue_two_mul_add_one,
        mersenneBinaryValue_two_mul]
      omega

/-- `b` is strictly increasing. -/
theorem mersenneBinaryValue_strictMono : StrictMono mersenneBinaryValue :=
  strictMono_nat_of_lt_succ fun m => mersenneBinaryValue_succ_ge m

/-- The gap after an odd index is at least `2`: `b(2j+1) + 2 ≤ b(2j+2)`. -/
theorem mersenneBinaryValue_odd_gap (j : ℕ) : b (2 * j + 1) + 2 ≤ b (2 * j + 2) := by
  have h1 := mersenneBinaryValue_succ_ge j
  have h2 : 2 * j + 2 = 2 * (j + 1) := by ring
  rw [h2, mersenneBinaryValue_two_mul, mersenneBinaryValue_two_mul_add_one,
    mersenneBinaryValue_two_mul]
  omega

/-- The binary side is exactly the range of `b`. -/
theorem binarySide_eq_range : binarySide = Set.range mersenneBinaryValue := by
  ext n
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨∑ i ∈ s.image (· - 1), 2 ^ i, ?_⟩
    unfold mersenneBinaryValue
    rw [← List.sum_toFinset _ Nat.bitIndices_nodup, Finset.toFinset_bitIndices_sum_two_pow,
      Finset.sum_image]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Nat.sub_add_cancel (hs k hk)]
    · intro x hx y hy hxy
      have hx1 := hs x hx
      have hy1 := hs y hy
      simp only at hxy
      omega
  · rintro ⟨m, rfl⟩
    refine ⟨m.bitIndices.toFinset.image (· + 1), ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_image] at hk
      obtain ⟨i, -, rfl⟩ := hk
      omega
    · rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
      unfold mersenneBinaryValue
      rw [List.sum_toFinset _ Nat.bitIndices_nodup]

/-! ## Block structure of the nonbinary side -/

/-- `x` is nonbinary iff it is not a value of `b`. -/
theorem mem_nonbinarySide_iff (x : ℕ) : x ∈ nonbinarySide ↔ ∀ m, b m ≠ x := by
  simp [nonbinarySide, binarySide_eq_range]

/-- Membership in the nonbinary side is decidable (only `m ≤ x` can give `b m = x`). -/
instance instDecidablePredMemNonbinarySide : DecidablePred (· ∈ nonbinarySide) := fun x =>
  decidable_of_iff (∀ m < x + 1, b m ≠ x) (by
    show _ ↔ x ∈ nonbinarySide
    rw [mem_nonbinarySide_iff]
    refine ⟨fun h m => ?_, fun h m _ => h m⟩
    rcases Nat.lt_or_ge m (x + 1) with hm | hm
    · exact h m hm
    · have hid := mersenneBinaryValue_strictMono.id_le m
      simp only [id] at hid
      omega)

/-- The nonbinary values below `30` agree with OEIS A055938. -/
example : (List.range 30).filter (· ∈ nonbinarySide) =
    [2, 5, 6, 9, 12, 13, 14, 17, 20, 21, 24, 27, 28, 29] := by decide

/-- `2` is not a finite sum of distinct Mersenne weights. -/
example : 2 ∉ binarySide := by
  change 2 ∈ nonbinarySide
  decide

/-- Values of `b` are binary. -/
theorem mersenneBinaryValue_not_mem (k : ℕ) : b k ∉ nonbinarySide := by
  rw [mem_nonbinarySide_iff]
  exact fun h => h k rfl

/-- Every integer strictly between consecutive values of `b` is nonbinary. -/
theorem mem_nonbinarySide_of_between {k x : ℕ} (h1 : b k < x) (h2 : x < b (k + 1)) :
    x ∈ nonbinarySide := by
  rw [mem_nonbinarySide_iff]
  rintro m rfl
  have hm1 : k < m := mersenneBinaryValue_strictMono.lt_iff_lt.mp h1
  have hm2 : m < k + 1 := mersenneBinaryValue_strictMono.lt_iff_lt.mp h2
  omega

/-- Every `x` lies in some block `b(k) ≤ x < b(k+1)`. -/
theorem exists_block (x : ℕ) : ∃ k, b k ≤ x ∧ x < b (k + 1) := by
  induction x with
  | zero => exact ⟨0, le_refl _, by decide⟩
  | succ x ih =>
    obtain ⟨k, hk1, hk2⟩ := ih
    rcases Nat.lt_or_ge (x + 1) (b (k + 1)) with h | h
    · exact ⟨k, by omega, h⟩
    · have h3 := mersenneBinaryValue_succ_ge (k + 1)
      exact ⟨k + 1, by omega, by omega⟩

/-- Counting inside a block: if `#N[0, b k) + k = b k` and `b k < x ≤ b (k+1)`,
then `#N[0, x) + (k + 1) = x`. -/
theorem count_nonbinarySide_block {k x : ℕ} (h1 : b k < x) (h2 : x ≤ b (k + 1))
    (hk : Nat.count (· ∈ nonbinarySide) (b k) + k = b k) :
    Nat.count (· ∈ nonbinarySide) x + (k + 1) = x := by
  induction x, (show b k + 1 ≤ x by omega) using Nat.le_induction with
  | base =>
    rw [Nat.count_succ, if_neg (mersenneBinaryValue_not_mem k)]
    omega
  | succ x hx ih =>
    have hxm : x ∈ nonbinarySide := mem_nonbinarySide_of_between (k := k) (by omega) (by omega)
    rw [Nat.count_succ, if_pos hxm]
    have hih := ih (by omega) (by omega)
    omega

/-- The number of nonbinary values below `b(k)` is `b(k) - k`. -/
theorem count_nonbinarySide_mersenneBinaryValue (k : ℕ) :
    Nat.count (· ∈ nonbinarySide) (b k) + k = b k := by
  induction k with
  | zero => simp [mersenneBinaryValue]
  | succ k ih =>
    have h := count_nonbinarySide_block
      (mersenneBinaryValue_strictMono (Nat.lt_succ_self k)) le_rfl ih
    omega

/-- The nonbinary side is infinite. -/
theorem nonbinarySide_infinite : (Set.ofPred (· ∈ nonbinarySide)).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun M => ⟨b (2 * M + 2) - 1, ?_, ?_⟩
  · have h1 := mersenneBinaryValue_odd_gap M
    exact mem_nonbinarySide_of_between (k := 2 * M + 1) (by omega)
      (by rw [show 2 * M + 1 + 1 = 2 * M + 2 by ring]; omega)
  · have h1 := mersenneBinaryValue_odd_gap M
    have h2 : 2 * M + 1 ≤ b (2 * M + 1) := mersenneBinaryValue_strictMono.id_le _
    omega

/-! ## The self-referential difference rule -/

/-- Difference rule in `0`-based form: with `y i` the `i`-th (0-based) nonbinary
value, `y (i+1) = y i + 1` if `i + 1` is nonbinary and `y i + 3` otherwise. -/
theorem nth_nonbinarySide_succ (i : ℕ) :
    Nat.nth (· ∈ nonbinarySide) (i + 1) =
      Nat.nth (· ∈ nonbinarySide) i + if i + 1 ∈ nonbinarySide then 1 else 3 := by
  set x := Nat.nth (· ∈ nonbinarySide) i with hxdef
  have hxN : x ∈ nonbinarySide := Nat.nth_mem_of_infinite nonbinarySide_infinite i
  have hcx : Nat.count (· ∈ nonbinarySide) x = i :=
    Nat.count_nth_of_infinite nonbinarySide_infinite i
  obtain ⟨k, hk1, hk2⟩ := exists_block x
  have hk1' : b k < x :=
    lt_of_le_of_ne hk1 (fun h => mersenneBinaryValue_not_mem k (h ▸ hxN))
  have hcount := count_nonbinarySide_block hk1' hk2.le
    (count_nonbinarySide_mersenneBinaryValue k)
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · -- blocks after an even index are empty
    exfalso
    have hb := mersenneBinaryValue_two_mul_add_one j
    omega
  · have hb1 : b (2 * j + 1) = b j + 2 * j + 1 := by
      rw [mersenneBinaryValue_two_mul_add_one, mersenneBinaryValue_two_mul]
    have hb2 : b (2 * j + 1 + 1) = b (j + 1) + 2 * (j + 1) := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, mersenneBinaryValue_two_mul]
    rcases Nat.lt_or_ge (x + 1) (b (2 * j + 1 + 1)) with hlt | hge
    · -- inside a block: gap `1`, and `i + 1` lies in the block `(b j, b (j+1))`
      have hx1 : x + 1 ∈ nonbinarySide :=
        mem_nonbinarySide_of_between (k := 2 * j + 1) (by omega) hlt
      have hi1 : i + 1 ∈ nonbinarySide :=
        mem_nonbinarySide_of_between (k := j) (by omega) (by omega)
      rw [if_pos hi1]
      have hc1 : Nat.count (· ∈ nonbinarySide) (x + 1) = i + 1 := by
        rw [Nat.count_succ, if_pos hxN, hcx]
      rw [← hc1, Nat.nth_count hx1]
    · -- end of a block: gap `3`, and `i + 1 = b (j+1)` is binary
      have hxeq : x + 1 = b (2 * j + 1 + 1) := by omega
      have hi1 : i + 1 ∉ nonbinarySide := by
        rw [show i + 1 = b (j + 1) by omega]
        exact mersenneBinaryValue_not_mem _
      rw [if_neg hi1]
      have hgap : b (2 * j + 3) + 2 ≤ b (2 * j + 3 + 1) := mersenneBinaryValue_odd_gap (j + 1)
      have h3 : b (2 * j + 3) = b (2 * j + 1 + 1) + 1 := by
        rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, ← mersenneBinaryValue_two_mul_add_one]
        rfl
      have hx2 : x + 1 ∉ nonbinarySide := by
        rw [hxeq]
        exact mersenneBinaryValue_not_mem _
      have hx2' : x + 2 ∉ nonbinarySide := by
        rw [show x + 2 = b (2 * j + 3) by omega]
        exact mersenneBinaryValue_not_mem _
      have hx3 : x + 3 ∈ nonbinarySide :=
        mem_nonbinarySide_of_between (k := 2 * j + 3) (by omega) (by omega)
      have hc3 : Nat.count (· ∈ nonbinarySide) (x + 3) = i + 1 := by
        rw [Nat.count_succ, Nat.count_succ, Nat.count_succ, if_pos hxN, if_neg hx2,
          if_neg hx2', hcx]
      rw [← hc3, Nat.nth_count hx3]

/-- **Proposition `prop:A055938-difference`** (arXiv:2607.22202, §3.3).
For every `n ≥ 1`, `A055938(n+1) - A055938(n) = 3 - 2 χ_J(n)`, i.e. the gap is
`1` when `n` itself is nonbinary (in A055938) and `3` otherwise. -/
theorem a055938_succ (n : ℕ) (hn : 1 ≤ n) :
    a055938 (n + 1) = a055938 n + if n ∈ nonbinarySide then 1 else 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [a055938, Nat.add_sub_cancel]
  exact nth_nonbinarySide_succ k

/-- The smallest nonbinary value is `2`. -/
theorem nth_nonbinarySide_zero : Nat.nth (· ∈ nonbinarySide) 0 = 2 := by
  have h1 : Nat.count (· ∈ nonbinarySide) 1 = 0 := by
    have h := count_nonbinarySide_mersenneBinaryValue 1
    have hb1 : b 1 = 1 := by decide
    rw [hb1] at h
    omega
  have h2 : Nat.count (· ∈ nonbinarySide) 2 = 0 := by
    have hb1 : (1 : ℕ) ∉ nonbinarySide := mersenneBinaryValue_not_mem 1
    rw [Nat.count_succ, if_neg hb1, h1]
  have hmem : (2 : ℕ) ∈ nonbinarySide := by decide
  rw [← h2, Nat.nth_count hmem]

/-- `A055938(1) = 2`. -/
theorem a055938_one : a055938 1 = 2 := nth_nonbinarySide_zero

/-- Examples: `A055938(1..6) = 2, 5, 6, 9, 12, 13`. -/
example : a055938 6 = 13 ∧ a055938 4 = 9 := by
  have h2 : a055938 2 = 5 := by rw [a055938_succ 1 le_rfl, a055938_one]; decide
  have h3 : a055938 3 = 6 := by rw [a055938_succ 2 (by norm_num), h2]; decide
  have h4 : a055938 4 = 9 := by rw [a055938_succ 3 (by norm_num), h3]; decide
  have h5 : a055938 5 = 12 := by rw [a055938_succ 4 (by norm_num), h4]; decide
  have h6 : a055938 6 = 13 := by rw [a055938_succ 5 (by norm_num), h5]; decide
  exact ⟨h6, h4⟩

/-! ## The A080578 – A055938 relation -/

/-- The state list of A080578 holds exactly the values `a(1), …, a(n)`. -/
theorem mem_a080578State_iff (n v : ℕ) :
    v ∈ (a080578State n).2 ↔ v ∈ (Finset.Icc 1 n).image a080578 := by
  induction n with
  | zero => simp [a080578State]
  | succ n ih =>
    rcases n with _ | n
    · simp [a080578State, a080578]
    · have hIcc : Finset.Icc 1 (n + 1 + 1) = insert (n + 1 + 1) (Finset.Icc 1 (n + 1)) := by
        rw [Finset.insert_Icc_right_eq_Icc_add_one (by omega)]
      rw [hIcc, Finset.image_insert, Finset.mem_insert, ← ih]
      simp only [a080578State, List.mem_cons, a080578]

/-- `a080578` satisfies the OEIS defining rule: `a(1) = 1` and, for `n ≥ 1`,
`a(n+1) = a(n) + 1` if `n + 1 ∈ {a(1), …, a(n)}` and `a(n) + 3` otherwise. -/
theorem a080578_one_and_succ :
    a080578 1 = 1 ∧ ∀ n, 1 ≤ n → a080578 (n + 1) =
      a080578 n + if n + 1 ∈ (Finset.Icc 1 n).image a080578 then 1 else 3 := by
  refine ⟨rfl, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hst := mem_a080578State_iff (k + 1) (k + 1 + 1)
  by_cases h : k + 1 + 1 ∈ (Finset.Icc 1 (k + 1)).image a080578
  · rw [if_pos h]
    simp only [a080578, a080578State, if_pos (hst.mpr h)]
  · rw [if_neg h]
    simp only [a080578, a080578State, if_neg (mt hst.mp h)]

/-- `0`-based form of the relation: `A080578(n+2) = y n + 2` where `y n` is the
`n`-th (0-based) nonbinary value. -/
theorem a080578_add_two (n : ℕ) :
    a080578 (n + 2) = Nat.nth (· ∈ nonbinarySide) n + 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [nth_nonbinarySide_zero]
      decide
    · have hrec := a080578_one_and_succ.2 (n + 2) (by omega)
      -- `n + 3` occurred earlier iff `n + 1` is nonbinary
      have hmem : n + 2 + 1 ∈ (Finset.Icc 1 (n + 2)).image a080578 ↔
          n + 1 ∈ nonbinarySide := by
        constructor
        · intro h
          obtain ⟨m, hm, hma⟩ := Finset.mem_image.mp h
          rw [Finset.mem_Icc] at hm
          obtain ⟨c, rfl⟩ : ∃ c, m = c + 2 := by
            refine ⟨m - 2, ?_⟩
            rcases Nat.lt_or_ge m 2 with hlt | hge
            · exfalso
              have hm1 : m = 1 := by omega
              rw [hm1] at hma
              have ha1 : a080578 1 = 1 := rfl
              omega
            · omega
          rw [ih c (by omega)] at hma
          have hy : Nat.nth (· ∈ nonbinarySide) c = n + 1 := by omega
          rw [← hy]
          exact Nat.nth_mem_of_infinite nonbinarySide_infinite c
        · intro h
          set c := Nat.count (· ∈ nonbinarySide) (n + 1) with hc
          have hcn : c ≤ n := by
            have h0 : (0 : ℕ) ∉ nonbinarySide := mersenneBinaryValue_not_mem 0
            rw [hc, Nat.count_succ', if_neg h0, add_zero]
            exact Nat.count_le _
          refine Finset.mem_image.mpr ⟨c + 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          rw [ih c (by omega), hc, Nat.nth_count h]
      rw [show n + 1 + 2 = n + 2 + 1 by ring, hrec, ih n (by omega),
        nth_nonbinarySide_succ n]
      by_cases h : n + 1 ∈ nonbinarySide
      · rw [if_pos h, if_pos (hmem.mpr h)]
      · rw [if_neg h, if_neg (mt hmem.mp h)]

/-- **Theorem `thm:A080578-A055938`** (arXiv:2607.22202, §4.1; conjectured in OEIS
A080578 by R. Stephan, 2013): for every `n ≥ 2`, `A080578(n) = A055938(n-1) + 2`. -/
theorem a080578_eq_a055938_add_two (n : ℕ) (hn : 2 ≤ n) :
    a080578 n = a055938 (n - 1) + 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [a080578_add_two, a055938, show k + 2 - 1 - 1 = k by omega]

end MersenneRepresentationConollySoliton
