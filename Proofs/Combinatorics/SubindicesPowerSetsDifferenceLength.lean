/-
# Difference lengths of sets of powers

M. H. Hooshmand, *Subindices and subfactors of infinite groups and numbers*,
arXiv:2604.08724, Section 3, Problem after `Waringlemma`, parts (ii)–(iii);
Section 1, definitions and `WaringExample`. For `A[k] = {k^m : m ≥ 0}`,
part (ii) asks whether `dl^∞(A[k]) = ∞` and `ℤ = ⟨A[k]⟩^{(∞)}` for `k ≥ 2`.
Here `Dif(B) = -B+B`, `Dif⁰(A) = A` and `Dif^{n+1}(A) = Dif(Dif^n(A))`.
Infinite difference length means no two consecutive stages agree. The
notation `ℤ = ⟨A⟩^{(∞)}` means `⟨A⟩ = ℤ` and `dl^∞(A ∪ {0}) = ∞`.

Part (iii), index stability with infinite index, is not formalized; only
the gap property of `Dif(A[k])` underlying it is established.

Proof: modulo `M = k^L`, every power of `k` is congruent to some `k^r` with
`r ≤ L` (as `k^m ≡ 0 = k^L` for `m ≥ L`), so `Dif^N(A)` has at most
`(L+1)^{2^N}` residues, fewer than `k^L` for large `L`.  If
`Dif^{N+1} = Dif^{N+2}`, the stage is a subgroup containing
`k - 1 = -1 + k`, a unit modulo `k^L`, so it meets every residue class.
The case `N = 0` fails since `0 ∈ Dif(A)` but `0 ∉ A[k]` (resp. `-1 ∈ Dif(A^0)`
but `-1 ∉ A[k]^0`).  This modular argument also replaces the counting step
of Example `WaringExample`, which asserts without justification that
`Dif^n(A')` has at most `m^{2^n}` elements of absolute value `≤ 2^m`.

Supplementary facts: `Dif^∞(A[k]) = (k-1)ℤ` (`iUnion_difIter_powSet`), which
differs from `ℤ = ⟨A[k]⟩` for `k ≥ 3`; this is consistent with the paper,
whose notation `⟨A⟩^{(N)}` refers to `A^0`, not to `A`.  And `Dif(A[k])` has
no element strictly between `k^m` and `k^m + k^{m-1}`, so it has arbitrarily
long gaps (`exists_Icc_disjoint_difIter_powSet`).
-/
import Mathlib

set_option autoImplicit false

namespace Sorry.Combinatorics.SubindicesPowerSetsDifferenceLength

open Pointwise

/-! ## Definitions -/

/-- `difIter A n` is the paper's `Dif^n(A)` in the additive group `ℤ`:
`Dif^0(A) = A` and `Dif^{n+1}(A) = Dif(Dif^n(A))`, where the (left)
difference set `Dif(B) = B⁻¹B` reads `-B + B = {-a + b : a, b ∈ B}`
additively. -/
def difIter (A : Set ℤ) : ℕ → Set ℤ
  | 0 => A
  | n + 1 => -difIter A n + difIter A n

/-- The paper's `A[k] = {k^m : m ∈ ℤ⁺ ∪ {0}}` as a subset of `ℤ`. -/
def powSet (k : ℕ) : Set ℤ := Set.range fun m : ℕ => (k : ℤ) ^ m

/-- The paper's statement `dl^∞(A) = ∞`: there is no `N` with
`Dif^N(A) = Dif^{N+1}(A)`. -/
def DlInfinite (A : Set ℤ) : Prop := ∀ N : ℕ, difIter A N ≠ difIter A (N + 1)

/-! ## Examples -/

example : (8 : ℤ) ∈ powSet 2 := ⟨3, by norm_num⟩
example : (1 : ℤ) ∈ powSet 3 := ⟨0, by norm_num⟩
example : (81 : ℤ) ∈ powSet 3 := ⟨4, by norm_num⟩
example : difIter (powSet 3) 0 = powSet 3 := rfl

/-! ## Generic facts about `Dif^n` -/

/-- Membership in `Dif(B) = -B + B`. -/
theorem mem_difIter_succ {A : Set ℤ} {n : ℕ} {x : ℤ} :
    x ∈ difIter A (n + 1) ↔ ∃ a ∈ difIter A n, ∃ b ∈ difIter A n, -a + b = x := by
  simp only [difIter, Set.mem_add, Set.mem_neg]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨-a, ha, b, hb, by rw [neg_neg]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨-a, by rwa [neg_neg], b, hb, rfl⟩

/-- `-a + b ∈ Dif^{n+1}(A)` whenever `a, b ∈ Dif^n(A)`. -/
theorem neg_add_mem_difIter_succ {A : Set ℤ} {n : ℕ} {a b : ℤ}
    (ha : a ∈ difIter A n) (hb : b ∈ difIter A n) : -a + b ∈ difIter A (n + 1) :=
  mem_difIter_succ.2 ⟨a, ha, b, hb, rfl⟩

/-- `0 ∈ Dif^{n+1}(A)` whenever `Dif^n(A)` is nonempty. -/
theorem zero_mem_difIter_succ {A : Set ℤ} {n : ℕ} (h : (difIter A n).Nonempty) :
    (0 : ℤ) ∈ difIter A (n + 1) := by
  obtain ⟨a, ha⟩ := h
  simpa using neg_add_mem_difIter_succ ha ha

/-- `Dif^n(A)` is nonempty when `A` is. -/
theorem difIter_nonempty {A : Set ℤ} (hA : A.Nonempty) (n : ℕ) : (difIter A n).Nonempty := by
  induction n with
  | zero => exact hA
  | succ n ih => exact ⟨0, zero_mem_difIter_succ ih⟩

/-- For `n ≥ 1` the stages increase: `Dif^{n+1}(A) ⊆ Dif^{n+2}(A)`. -/
theorem difIter_succ_subset_succ_succ {A : Set ℤ} (hA : A.Nonempty) (n : ℕ) :
    difIter A (n + 1) ⊆ difIter A (n + 2) := by
  intro x hx
  have h0 : (0 : ℤ) ∈ difIter A (n + 1) := zero_mem_difIter_succ (difIter_nonempty hA n)
  simpa using neg_add_mem_difIter_succ h0 hx

/-- Monotonicity of the stages from index `1` on. -/
theorem difIter_mono {A : Set ℤ} (hA : A.Nonempty) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    difIter A m ⊆ difIter A n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact ih.trans (difIter_succ_subset_succ_succ hA k)

/-- If `Dif^{N+1}(A) = Dif^{N+2}(A)` then `Dif^{N+1}(A)` contains every integer
multiple `d * c` of each of its elements `d` (the stable stage is a subgroup). -/
theorem mul_mem_difIter_of_eq_succ {A : Set ℤ} {N : ℕ} (hA : A.Nonempty)
    (h : difIter A (N + 1) = difIter A (N + 2)) {d : ℤ} (hd : d ∈ difIter A (N + 1))
    (c : ℤ) : d * c ∈ difIter A (N + 1) := by
  set D := difIter A (N + 1) with hD
  have hclos : ∀ a ∈ D, ∀ b ∈ D, -a + b ∈ D := by
    intro a ha b hb
    rw [h]
    exact neg_add_mem_difIter_succ ha hb
  have h0 : (0 : ℤ) ∈ D := zero_mem_difIter_succ (difIter_nonempty hA N)
  have hneg : ∀ a ∈ D, -a ∈ D := fun a ha => by simpa using hclos a ha 0 h0
  have hadd : ∀ a ∈ D, ∀ b ∈ D, a + b ∈ D := fun a ha b hb => by
    simpa using hclos (-a) (hneg a ha) b hb
  induction c using Int.induction_on with
  | zero => simpa using h0
  | succ j hj => simpa [mul_add] using hadd _ hj d hd
  | pred j hj =>
    have hsum := hadd _ hj (-d) (hneg d hd)
    rwa [show d * (-(j : ℤ)) + -d = d * (-(j : ℤ) - 1) by ring] at hsum

/-- **Counting lemma.** If every element of `A` reduces modulo `M` into a finite set `S`,
then `Dif^N(A)` reduces into a finite set of at most `|S|^{2^N}` residues. -/
theorem exists_finset_difIter_cast {M : ℕ} (A : Set ℤ) (S : Finset (ZMod M))
    (hS : ∀ a ∈ A, (a : ZMod M) ∈ S) (N : ℕ) :
    ∃ T : Finset (ZMod M), T.card ≤ S.card ^ 2 ^ N ∧
      ∀ x ∈ difIter A N, (x : ZMod M) ∈ T := by
  induction N with
  | zero => exact ⟨S, by simp, hS⟩
  | succ n ih =>
    obtain ⟨T, hTcard, hT⟩ := ih
    refine ⟨-T + T, ?_, ?_⟩
    · calc (-T + T).card ≤ (-T).card * T.card := Finset.card_add_le
        _ = T.card ^ 2 := by rw [Finset.card_neg, sq]
        _ ≤ (S.card ^ 2 ^ n) ^ 2 := Nat.pow_le_pow_left hTcard 2
        _ = S.card ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ]
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_difIter_succ.1 hx
      have hneg : -((a : ℤ) : ZMod M) ∈ -T := Finset.neg_mem_neg (hT a ha)
      push_cast
      exact Finset.add_mem_add hneg (hT b hb)

/-- **Modular obstruction.** Suppose `A` reduces modulo `M > 0` into a set `S` with
`|S|^{2^{N+1}} < M`, and `Dif^{N+1}(A)` contains an element `d` that is a unit modulo `M`.
Then `Dif^{N+1}(A) ≠ Dif^{N+2}(A)`. -/
theorem difIter_ne_succ_of_isUnit {M : ℕ} [NeZero M] {A : Set ℤ} (hA : A.Nonempty)
    (S : Finset (ZMod M)) (hS : ∀ a ∈ A, (a : ZMod M) ∈ S) {N : ℕ}
    (hlt : S.card ^ 2 ^ (N + 1) < M) {d : ℤ} (hd : d ∈ difIter A (N + 1))
    (hunit : IsUnit (d : ZMod M)) : difIter A (N + 1) ≠ difIter A (N + 2) := by
  intro h
  obtain ⟨T, hTcard, hT⟩ := exists_finset_difIter_cast A S hS (N + 1)
  obtain ⟨u, hu⟩ := hunit
  have hsub : (Finset.univ : Finset (ZMod M)) ⊆ T := by
    intro r _
    have hmem := hT _ (mul_mem_difIter_of_eq_succ hA h hd (((u⁻¹ : (ZMod M)ˣ) * r).val : ℤ))
    have hcast : (((d * (((u⁻¹ : (ZMod M)ˣ) * r).val : ℤ) : ℤ)) : ZMod M) = r := by
      push_cast
      rw [ZMod.natCast_zmod_val, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
    rwa [hcast] at hmem
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at hcard
  omega

/-! ## Powers of `k` modulo `k^L` -/

/-- Modulo `k^L`, every power `k^m` is congruent to some `k^r` with `r ≤ L`
(for `m ≥ L`, both `k^m` and `k^L` vanish). -/
theorem exists_le_pow_cast_eq (k L m : ℕ) :
    ∃ r < L + 1, ((k : ZMod (k ^ L)) ^ m) = (k : ZMod (k ^ L)) ^ r := by
  by_cases hm : m < L + 1
  · exact ⟨m, hm, rfl⟩
  · refine ⟨L, Nat.lt_succ_self L, ?_⟩
    have hL : (k : ZMod (k ^ L)) ^ L = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hL, show m = L + (m - L) by omega, pow_add, hL, zero_mul]

/-- `k - 1` is a unit modulo `k^L`: `(k - 1) · (-(1 + k + ⋯ + k^{L-1})) = 1 - k^L ≡ 1`. -/
theorem isUnit_sub_one_cast (k L : ℕ) : IsUnit (((k : ℤ) - 1 : ℤ) : ZMod (k ^ L)) := by
  have hL : (k : ZMod (k ^ L)) ^ L = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  refine IsUnit.of_mul_eq_one (-(∑ i ∈ Finset.range L, (k : ZMod (k ^ L)) ^ i)) ?_
  have hgeom := geom_sum_mul (k : ZMod (k ^ L)) L
  push_cast
  rw [hL] at hgeom
  linear_combination -hgeom

/-- For each `N` and `k ≥ 2` there is `L` with `(L+1)^{2^N} < k^L`. -/
theorem exists_pow_lt_pow (k : ℕ) (hk : 2 ≤ k) (N : ℕ) :
    ∃ L : ℕ, (L + 1) ^ 2 ^ N < k ^ L := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 2 * N + 8 := ⟨_, rfl⟩
  refine ⟨2 ^ t, ?_⟩
  have hN : N < 2 ^ N := Nat.lt_two_pow_self
  have hL1 : 2 ^ t + 1 ≤ 2 ^ (t + 1) := by
    have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have hexp : (t + 1) * 2 ^ N < 2 ^ t := by
    have h2 : 2 ^ t = 2 ^ N * 2 ^ (N + 8) := by rw [ht, ← pow_add]; congr 1; ring
    have h3 : 2 ^ (N + 8) = 2 ^ N * 256 := by rw [pow_add]; norm_num
    rw [h2, h3, ht]
    nlinarith
  calc (2 ^ t + 1) ^ 2 ^ N ≤ (2 ^ (t + 1)) ^ 2 ^ N := Nat.pow_le_pow_left hL1 _
    _ = 2 ^ ((t + 1) * 2 ^ N) := by rw [← pow_mul]
    _ < 2 ^ 2 ^ t := Nat.pow_lt_pow_right (by norm_num) hexp
    _ ≤ k ^ 2 ^ t := Nat.pow_le_pow_left hk _

/-- `Dif^{N+1}(A) ≠ Dif^{N+2}(A)` for any `A ⊆ A[k] ∪ {0}` (`k ≥ 2`) whose first difference
set contains `k - 1`. -/
theorem difIter_ne_succ_of_subset (k : ℕ) (hk : 2 ≤ k) {A : Set ℤ}
    (hsub : A ⊆ insert 0 (powSet k)) (hA : A.Nonempty)
    (hd : (k : ℤ) - 1 ∈ difIter A 1) (N : ℕ) : difIter A (N + 1) ≠ difIter A (N + 2) := by
  obtain ⟨L, hL⟩ := exists_pow_lt_pow k hk (N + 1)
  haveI : NeZero (k ^ L) := ⟨pow_ne_zero L (by omega)⟩
  let S : Finset (ZMod (k ^ L)) :=
    (Finset.range (L + 1)).image fun r => (k : ZMod (k ^ L)) ^ r
  have hS : ∀ a ∈ A, (a : ZMod (k ^ L)) ∈ S := by
    intro a ha
    rcases hsub ha with h0 | ⟨m, rfl⟩
    · rw [h0, Int.cast_zero]
      refine Finset.mem_image.2 ⟨L, Finset.mem_range.2 (Nat.lt_succ_self L), ?_⟩
      rw [← Nat.cast_pow, ZMod.natCast_self]
    · obtain ⟨r, hr, heq⟩ := exists_le_pow_cast_eq k L m
      refine Finset.mem_image.2 ⟨r, Finset.mem_range.2 hr, ?_⟩
      rw [heq.symm]
      push_cast
      rfl
  have hcard : S.card ≤ L + 1 := Finset.card_image_le.trans (by simp)
  have hdN : (k : ℤ) - 1 ∈ difIter A (N + 1) := difIter_mono hA le_rfl (by omega) hd
  exact difIter_ne_succ_of_isUnit hA S hS
    (lt_of_le_of_lt (Nat.pow_le_pow_left hcard _) hL) hdN (isUnit_sub_one_cast k L)

/-! ## Problem (ii) -/

/-- `1 = k^0 ∈ A[k]`. -/
theorem one_mem_powSet (k : ℕ) : (1 : ℤ) ∈ powSet k := ⟨0, pow_zero _⟩

/-- `k = k^1 ∈ A[k]`. -/
theorem self_mem_powSet (k : ℕ) : (k : ℤ) ∈ powSet k := ⟨1, pow_one _⟩

/-- `0 ∉ A[k]` for `k ≥ 1`. -/
theorem zero_not_mem_powSet (k : ℕ) (hk : 1 ≤ k) : (0 : ℤ) ∉ powSet k := by
  rintro ⟨m, hm⟩
  have hm' : (k : ℤ) ^ m = 0 := hm
  have hpos : (0 : ℤ) < (k : ℤ) ^ m := pow_pos (by exact_mod_cast hk) m
  rw [hm'] at hpos
  exact lt_irrefl 0 hpos

/-- `k - 1 = -1 + k ∈ Dif(A)` whenever `1, k ∈ A`. -/
theorem sub_one_mem_difIter_one {k : ℕ} {A : Set ℤ} (h1 : (1 : ℤ) ∈ A) (hk : (k : ℤ) ∈ A) :
    (k : ℤ) - 1 ∈ difIter A 1 := by
  have h := neg_add_mem_difIter_succ (n := 0) h1 hk
  rwa [neg_add_eq_sub] at h

/-- **Problem (ii), first claim, arXiv:2604.08724.** For every `k ≥ 2`, the ∞-difference
length of `A[k] = {k^m : m ≥ 0}` is infinite: `Dif^N(A[k]) ≠ Dif^{N+1}(A[k])` for all `N`. -/
theorem dlInfinite_powSet (k : ℕ) (hk : 2 ≤ k) : DlInfinite (powSet k) := by
  intro N h
  rcases N with _ | N
  · apply zero_not_mem_powSet k (by omega)
    have h0 : (0 : ℤ) ∈ difIter (powSet k) 1 := zero_mem_difIter_succ ⟨1, one_mem_powSet k⟩
    rw [← h] at h0
    exact h0
  · exact difIter_ne_succ_of_subset k hk (Set.subset_insert 0 _) ⟨1, one_mem_powSet k⟩
      (sub_one_mem_difIter_one (one_mem_powSet k) (self_mem_powSet k)) N h

/-- `dl^∞(A[k]^0) = ∞` for `k ≥ 2`, where `A[k]^0 = A[k] ∪ {0}`. -/
theorem dlInfinite_insert_zero_powSet (k : ℕ) (hk : 2 ≤ k) :
    DlInfinite (insert 0 (powSet k)) := by
  intro N h
  have hone : (1 : ℤ) ∈ insert 0 (powSet k) := Set.mem_insert_of_mem _ (one_mem_powSet k)
  have hself : (k : ℤ) ∈ insert 0 (powSet k) := Set.mem_insert_of_mem _ (self_mem_powSet k)
  rcases N with _ | N
  · -- `-1 = -1 + 0 ∈ Dif(A[k]^0)`, but every element of `A[k]^0` is nonnegative.
    have hm1 : (-1 : ℤ) ∈ difIter (insert 0 (powSet k)) 1 := by
      have hm := neg_add_mem_difIter_succ (n := 0) hone (Set.mem_insert 0 (powSet k))
      simpa using hm
    rw [← h] at hm1
    rcases hm1 with hm1 | ⟨m, hm⟩
    · norm_num at hm1
    · have hm' : (k : ℤ) ^ m = -1 := hm
      have hnn : (0 : ℤ) ≤ (k : ℤ) ^ m := pow_nonneg (Int.natCast_nonneg k) m
      rw [hm'] at hnn
      norm_num at hnn
  · exact difIter_ne_succ_of_subset k hk le_rfl ⟨1, hone⟩
      (sub_one_mem_difIter_one hone hself) N h

/-- `⟨A[k]⟩ = ℤ`, since `1 ∈ A[k]`. -/
theorem closure_powSet (k : ℕ) : AddSubgroup.closure (powSet k) = ⊤ := by
  rw [eq_top_iff, ← Int.zmultiples_one, AddSubgroup.zmultiples_le]
  exact AddSubgroup.subset_closure (one_mem_powSet k)

/-- **Problem (ii), arXiv:2604.08724.** For every `k ≥ 2`, `ℤ = ⟨A[k]⟩^{(∞)}`: in the paper's
notation this means `⟨A[k]⟩ = ℤ` and `dl^∞(A[k]^0) = ∞` with `A[k]^0 = A[k] ∪ {0}`; together
with `dl^∞(A[k]) = ∞`. -/
theorem problem_ii (k : ℕ) (hk : 2 ≤ k) :
    DlInfinite (powSet k) ∧ AddSubgroup.closure (powSet k) = ⊤ ∧
      DlInfinite (insert 0 (powSet k)) :=
  ⟨dlInfinite_powSet k hk, closure_powSet k, dlInfinite_insert_zero_powSet k hk⟩

/-! ## Supplementary: `Dif^∞(A[k]) = (k-1)ℤ` -/

/-- If `Dif(A)` lies in an additive subgroup `P`, so does every `Dif^{n+1}(A)`. -/
theorem difIter_succ_subset_of_subset {A : Set ℤ} {P : AddSubgroup ℤ}
    (h : difIter A 1 ⊆ P) (n : ℕ) : difIter A (n + 1) ⊆ P := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_difIter_succ.1 hx
    exact P.add_mem (P.neg_mem (ih ha)) (ih hb)

/-- Every integer multiple of an element `d ∈ Dif(A)` lies in some `Dif^{n+1}(A)`. -/
theorem exists_mul_mem_difIter {A : Set ℤ} (hA : A.Nonempty) {d : ℤ}
    (hd : d ∈ difIter A 1) (c : ℤ) : ∃ n : ℕ, d * c ∈ difIter A (n + 1) := by
  induction c using Int.induction_on with
  | zero => exact ⟨0, by simpa using zero_mem_difIter_succ (n := 0) hA⟩
  | succ j hj =>
    obtain ⟨n, hn⟩ := hj
    have hdn : d ∈ difIter A (n + 1) := difIter_mono hA le_rfl (by omega) hd
    have h0 : (0 : ℤ) ∈ difIter A (n + 1) := zero_mem_difIter_succ (difIter_nonempty hA n)
    have hneg : -d ∈ difIter A (n + 2) := by simpa using neg_add_mem_difIter_succ hdn h0
    have hy : d * j ∈ difIter A (n + 2) := difIter_succ_subset_succ_succ hA n hn
    refine ⟨n + 2, ?_⟩
    have hsum := neg_add_mem_difIter_succ hneg hy
    rwa [show -(-d) + d * j = d * (j + 1) by ring] at hsum
  | pred j hj =>
    obtain ⟨n, hn⟩ := hj
    have hdn : d ∈ difIter A (n + 1) := difIter_mono hA le_rfl (by omega) hd
    have hsum := neg_add_mem_difIter_succ hdn hn
    refine ⟨n + 1, ?_⟩
    rwa [show -d + d * -(j : ℤ) = d * (-(j : ℤ) - 1) by ring] at hsum

/-- `Dif(A[k]) ⊆ (k-1)ℤ`: `k^b - k^a = (k^b - 1) - (k^a - 1)`. -/
theorem difIter_one_powSet_subset (k : ℕ) :
    difIter (powSet k) 1 ⊆ (AddSubgroup.zmultiples ((k : ℤ) - 1) : Set ℤ) := by
  intro x hx
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := mem_difIter_succ.1 hx
  rw [SetLike.mem_coe, Int.mem_zmultiples_iff]
  have hb := sub_dvd_pow_sub_pow (k : ℤ) 1 b
  have ha := sub_dvd_pow_sub_pow (k : ℤ) 1 a
  rw [one_pow] at ha hb
  have hdiff := dvd_sub hb ha
  rwa [show (k : ℤ) ^ b - 1 - ((k : ℤ) ^ a - 1) = -(k : ℤ) ^ a + (k : ℤ) ^ b by ring] at hdiff

/-- **Supplement to Problem (ii).** `Dif^∞(A[k]) = ⋃_{n ≥ 1} Dif^n(A[k]) = (k-1)ℤ`.  For
`k ≥ 3` this is a proper subgroup of `ℤ = ⟨A[k]⟩`; the paper's `ℤ = ⟨A[k]⟩^{(∞)}` concerns
`A[k]^0 = A[k] ∪ {0}`, whose `Dif^∞` is `ℤ`. -/
theorem iUnion_difIter_powSet (k : ℕ) :
    (⋃ n : ℕ, difIter (powSet k) (n + 1)) = {x : ℤ | (k : ℤ) - 1 ∣ x} := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn⟩
    have hx := difIter_succ_subset_of_subset (difIter_one_powSet_subset k) n hn
    rwa [SetLike.mem_coe, Int.mem_zmultiples_iff] at hx
  · rintro ⟨c, rfl⟩
    exact exists_mul_mem_difIter ⟨1, one_mem_powSet k⟩
      (sub_one_mem_difIter_one (one_mem_powSet k) (self_mem_powSet k)) c

/-! ## Supplementary: gaps in `Dif(A[k])` -/

/-- For `k ≥ 2`, no element of `Dif(A[k]) = {k^b - k^a}` lies strictly between `k^{m+1}` and
`k^{m+1} + k^m`. -/
theorem not_mem_difIter_one_powSet_of_lt (k : ℕ) (hk : 2 ≤ k) (m : ℕ) {x : ℤ}
    (h1 : (k : ℤ) ^ (m + 1) < x) (h2 : x < (k : ℤ) ^ (m + 1) + (k : ℤ) ^ m) :
    x ∉ difIter (powSet k) 1 := by
  intro hx
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := mem_difIter_succ.1 hx
  set K : ℤ := (k : ℤ) with hK
  have hK2 : (2 : ℤ) ≤ K := by rw [hK]; exact_mod_cast hk
  have hK1 : (1 : ℤ) ≤ K := by linarith
  have hP : (0 : ℤ) < K ^ m := pow_pos (by linarith) m
  have hKa : (0 : ℤ) < K ^ a := pow_pos (by linarith) a
  have hpm1 : K ^ (m + 1) = K ^ m * K := pow_succ K m
  -- the top exponent `b` is at least `m + 2`
  have hb : m + 2 ≤ b := by
    by_contra hbm
    have hle : K ^ b ≤ K ^ (m + 1) := pow_le_pow_right₀ hK1 (by omega)
    linarith
  rcases Nat.lt_or_ge m a with ha | ha
  · -- `k^{m+1}` divides both powers, but no multiple of it lies in `(k^{m+1}, 2k^{m+1})`
    have hda : K ^ (m + 1) ∣ K ^ a := pow_dvd_pow K (by omega)
    have hdb : K ^ (m + 1) ∣ K ^ b := pow_dvd_pow K (by omega)
    obtain ⟨c, hc⟩ := dvd_add (dvd_neg.2 hda) hdb
    rw [hc] at h1 h2
    have hQ : (0 : ℤ) < K ^ (m + 1) := pow_pos (by linarith) (m + 1)
    have hc1 : 1 < c := by
      by_contra hc1
      have hle : K ^ (m + 1) * c ≤ K ^ (m + 1) * 1 :=
        mul_le_mul_of_nonneg_left (by omega) hQ.le
      linarith
    have hc2 : c < 2 := by
      by_contra hc2
      have hle : K ^ (m + 1) * 2 ≤ K ^ (m + 1) * c :=
        mul_le_mul_of_nonneg_left (by omega) hQ.le
      nlinarith
    omega
  · -- `k^a ≤ k^m` and `k^b ≥ k^{m+2}`, so `k^b - k^a ≥ k^{m+2} - k^m ≥ k^{m+1} + k^m`
    have hla : K ^ a ≤ K ^ m := pow_le_pow_right₀ hK1 ha
    have hlb : K ^ (m + 2) ≤ K ^ b := pow_le_pow_right₀ hK1 hb
    have hpm2 : K ^ (m + 2) = K ^ m * K * K := by rw [pow_succ, pow_succ]
    nlinarith [mul_nonneg hP.le (mul_nonneg (by linarith : (0 : ℤ) ≤ K - 2)
      (by linarith : (0 : ℤ) ≤ K + 1))]

/-- **Supplement to Problem (iii).** For `k ≥ 2`, `Dif(A[k])` has arbitrarily long gaps: for
every `B` there is an integer interval `[x, x + B]` disjoint from `Dif(A[k])`, so
`Dif(A[k])` is not syndetic. -/
theorem exists_Icc_disjoint_difIter_powSet (k : ℕ) (hk : 2 ≤ k) (B : ℕ) :
    ∃ x : ℤ, ∀ y ∈ Set.Icc x (x + B), y ∉ difIter (powSet k) 1 := by
  refine ⟨(k : ℤ) ^ (B + 2) + 1, fun y hy => ?_⟩
  have hB : B + 1 < k ^ (B + 1) := Nat.lt_pow_self (by omega)
  have hB' : (B : ℤ) + 1 < (k : ℤ) ^ (B + 1) := by exact_mod_cast hB
  obtain ⟨hy1, hy2⟩ := hy
  exact not_mem_difIter_one_powSet_of_lt k hk (B + 1) (by linarith) (by linarith)

/-! ## Examples -/

/-- The paper's remark `dl^∞(A[1]) = 1`: `A[1] = {1}` and `Dif(A[1]) = Dif²(A[1]) = {0}`,
so `A[1]` does not have infinite difference length (the hypothesis `2 ≤ k` is needed). -/
theorem not_dlInfinite_powSet_one : ¬ DlInfinite (powSet 1) := by
  have h1 : powSet 1 = {1} := by
    ext x
    simp [powSet]
  have hD1 : difIter (powSet 1) 1 = {0} := by
    ext x
    rw [mem_difIter_succ]
    simp [difIter, h1, eq_comm]
  have hD2 : difIter (powSet 1) 2 = {0} := by
    ext x
    rw [mem_difIter_succ, hD1]
    simp [eq_comm]
  intro h
  exact h 1 (hD1.trans hD2.symm)

example : DlInfinite (powSet 3) := dlInfinite_powSet 3 (by norm_num)

example : (6 : ℤ) ∈ difIter (powSet 3) 1 := by
  have h := neg_add_mem_difIter_succ (n := 0) (A := powSet 3) ⟨1, rfl⟩ ⟨2, rfl⟩
  norm_num at h
  exact h

/-- For `k = 3`, `1 ∉ Dif^∞(A[3]) = 2ℤ` although `1 ∈ A[3]`. -/
example : (1 : ℤ) ∉ ⋃ n : ℕ, difIter (powSet 3) (n + 1) := by
  rw [iUnion_difIter_powSet]
  norm_num

end Sorry.Combinatorics.SubindicesPowerSetsDifferenceLength
