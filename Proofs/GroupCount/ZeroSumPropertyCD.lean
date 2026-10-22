/-
# Property C and Property D fail for `C_6^r`, `4 ≤ r`

Guoqing Wang, *Inverse Zero-Sum Problems: The Property C and Property D
Conjectures*, arXiv:2610.25271, Theorem 1.3 (`thm:main`) and Section 3:
Proposition `prop:even`, Lemma `lem:delete`, the sequence `(S)` of
Lemma `lemma:construction`, and the binary product construction `S_r`.

This file proves that `C_6^r` has neither Property C nor Property D for
`4 ≤ r`, with the rank-four bounds `82 ≤ s(C_6^4)` and `77 ≤ η(C_6^4)`.
For `G = C_n^r`, `2 ≤ n` and `1 ≤ r`, Property D (Gao–Geroldinger
[GG06, Conjecture 7.2]) requires every sequence of length `s(G)-1` without an exponent-length zero sum to be `T^(n-1)`.
Property C (Gao–Hou–Schmid–Thangadurai [GHST07, Open Problems 1.2(C3)])
uses `η(G)-1` and excludes nonempty zero sums of length at most `n` instead.

`C_n^r` is `Fin r → ZMod n`, sequences are multisets, and `T^(n-1)` is
`(n-1) • T`. The constants are infima of admissible-length sets; nonemptiness
is proved where used, giving genuine minima and extremal sequences.

The 81-term seed uses CRT coordinates for the source's `𝔽₂⁴ ⊕ 𝔽₃⁴`
construction. Its absence of six-term zero sums is proved by finite
multiplicity enumeration with `decide +kernel` and `checkNoZeroSum_sound`,
rather than the paper's case analysis. Only the upper-bound implication of
Proposition `prop:even` needed for the disproof is formalized; Harborth's
lower bounds and the equality half are not included.
-/
import Mathlib

set_option autoImplicit false

namespace ZeroSumPropertyCD

open Multiset

/-! ## Zero-sum vocabulary -/

/-- `HasZeroSumOfLength k S`: the sequence `S` has a zero-sum subsequence of length exactly
`k` (that is, `0 ∈ Σ_k(S)` in the paper's notation). -/
def HasZeroSumOfLength {G : Type*} [AddCommMonoid G] (k : ℕ) (S : Multiset G) : Prop :=
  ∃ T ≤ S, card T = k ∧ T.sum = 0

/-- `HasShortZeroSum k S`: the sequence `S` has a nonempty zero-sum subsequence of length at
most `k` (a *short* zero-sum subsequence when `k = exp(G)`). -/
def HasShortZeroSum {G : Type*} [AddCommMonoid G] (k : ℕ) (S : Multiset G) : Prop :=
  ∃ T ≤ S, 0 < card T ∧ card T ≤ k ∧ T.sum = 0

/-- `HasZeroSumOfLength` as a decidable search over the (finite) set of subsequences. -/
theorem hasZeroSumOfLength_iff_powerset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (k : ℕ) (S : Multiset G) :
    HasZeroSumOfLength k S ↔ ∃ T ∈ S.powerset.toFinset, card T = k ∧ T.sum = 0 := by
  simp only [HasZeroSumOfLength, Multiset.mem_toFinset, Multiset.mem_powerset]

/-- `HasShortZeroSum` as a decidable search over the (finite) set of subsequences. -/
theorem hasShortZeroSum_iff_powerset {G : Type*} [AddCommMonoid G] [DecidableEq G] (k : ℕ)
    (S : Multiset G) :
    HasShortZeroSum k S ↔
      ∃ T ∈ S.powerset.toFinset, 0 < card T ∧ card T ≤ k ∧ T.sum = 0 := by
  simp only [HasShortZeroSum, Multiset.mem_toFinset, Multiset.mem_powerset]

/-- In `C_3`, the sequence `0^2 1^2` (extremal for `s(C_3) = 5`) has no 3-term
zero sum. -/
example : ¬ HasZeroSumOfLength 3 ({0, 0, 1, 1} : Multiset (ZMod 3)) := by
  rw [hasZeroSumOfLength_iff_powerset]
  decide

/-- In `C_3`, the sequence `0^2 1^3` has the 3-term zero sum `1^3`. -/
example : HasZeroSumOfLength 3 ({0, 0, 1, 1, 1} : Multiset (ZMod 3)) := by
  rw [hasZeroSumOfLength_iff_powerset]
  decide

/-- In `C_3`, `1^2` has no short zero sum, but `1^2 2` has (`1 2`). -/
example : ¬ HasShortZeroSum 3 ({1, 1} : Multiset (ZMod 3)) ∧
    HasShortZeroSum 3 ({1, 1, 2} : Multiset (ZMod 3)) := by
  rw [hasShortZeroSum_iff_powerset, hasShortZeroSum_iff_powerset]
  decide

/-- A zero-sum subsequence of length `0` always exists (the empty one), while
a short zero sum must be nonempty. -/
example : HasZeroSumOfLength 0 (0 : Multiset (ZMod 3)) ∧
    ¬ HasShortZeroSum 3 (0 : Multiset (ZMod 3)) := by
  rw [hasZeroSumOfLength_iff_powerset, hasShortZeroSum_iff_powerset]
  decide

/-- A subsequence of a sum of two sequences splits into subsequences of the summands. -/
theorem exists_split_of_le_add {α : Type*} [DecidableEq α] {T A B : Multiset α}
    (h : T ≤ A + B) : ∃ T₁ T₂, T₁ ≤ A ∧ T₂ ≤ B ∧ T = T₁ + T₂ := by
  refine ⟨T ∩ A, T - T ∩ A, inter_le_right, ?_, ?_⟩
  · rw [Multiset.le_iff_count] at h ⊢
    intro a
    have ha := h a
    simp only [count_sub, count_inter, count_add] at ha ⊢
    omega
  · exact (add_tsub_cancel_of_le inter_le_left).symm

/-! ## A kernel-checkable certificate for "no `k`-term zero sum" -/

/-- `checkNoZeroSum good l k acc` enumerates every choice of multiplicities `c_i ≤ v_i` with
`∑ c_i = k` for the list `l = [(g_1, v_1), …]` and checks `good (acc + ∑ c_i • g_i)`.
It is a computable certificate; `checkNoZeroSum_sound` is its soundness theorem. -/
def checkNoZeroSum {M : Type*} [AddCommMonoid M] (good : M → Bool) :
    List (M × ℕ) → ℕ → M → Bool
  | _, 0, acc => good acc
  | [], _ + 1, _ => true
  | (g, v) :: l, k + 1, acc =>
      (List.range (min v (k + 1) + 1)).all fun j => checkNoZeroSum good l (k + 1 - j) (acc + j • g)

/-- The sequence `∏ π(g_i)^{v_i}` over `G` described by a list `[(g_1, v_1), …]` of
representatives `g_i ∈ M` and multiplicities `v_i`. -/
def seqOfList {M G : Type*} [AddCommMonoid M] [AddCommMonoid G] (π : M →+ G)
    (l : List (M × ℕ)) : Multiset G :=
  (l.map fun p => replicate p.2 (π p.1)).sum

/-- For the certificate: the `C_3` sequence `0^2 1^2` passes the check for
`3`-term zero sums, while `0^2 1^3` fails it. -/
example : checkNoZeroSum (fun x : ZMod 3 => x != 0) [(0, 2), (1, 2)] 3 0 = true ∧
    checkNoZeroSum (fun x : ZMod 3 => x != 0) [(0, 2), (1, 3)] 3 0 = false := by
  decide

/-- `seqOfList` of `[(0, 2), (1, 2)]` is `0^2 1^2`. -/
example : seqOfList (AddMonoidHom.id (ZMod 3)) [(0, 2), (1, 2)] = {0, 0, 1, 1} := by
  decide

/-- Soundness of `checkNoZeroSum`: if the check passes and `good x` certifies `π x ≠ 0`, then
for every subsequence `T` of length `k` of `seqOfList π l`, `π acc + σ(T) ≠ 0`. -/
theorem checkNoZeroSum_sound {M G : Type*} [AddCommMonoid M] [AddCommMonoid G]
    [DecidableEq G] (π : M →+ G) (good : M → Bool)
    (hgood : ∀ x, good x = true → π x ≠ 0) (l : List (M × ℕ)) :
    ∀ (k : ℕ) (acc : M), checkNoZeroSum good l k acc = true →
      ∀ T ≤ seqOfList π l, card T = k → π acc + T.sum ≠ 0 := by
  induction l with
  | nil =>
    intro k acc hcheck T hT hcard
    have hT0 : T = 0 := le_zero.mp (by simpa [seqOfList] using hT)
    subst hT0
    cases k with
    | zero =>
      simpa [checkNoZeroSum] using hgood acc (by simpa [checkNoZeroSum] using hcheck)
    | succ k => simp at hcard
  | cons p l ih =>
    obtain ⟨g, v⟩ := p
    intro k acc hcheck T hT hcard
    cases k with
    | zero =>
      have hT0 : T = 0 := card_eq_zero.mp hcard
      subst hT0
      simpa [checkNoZeroSum] using hgood acc (by simpa [checkNoZeroSum] using hcheck)
    | succ k =>
      have hT' : T ≤ replicate v (π g) + seqOfList π l := by
        simpa [seqOfList] using hT
      obtain ⟨T₁, T₂, hT₁, hT₂, rfl⟩ := exists_split_of_le_add hT'
      obtain ⟨j, hjv, rfl⟩ := le_replicate_iff.mp hT₁
      have hcard' : j + card T₂ = k + 1 := by simpa using hcard
      have hj : j ∈ List.range (min v (k + 1) + 1) := by
        rw [List.mem_range]; omega
      have hcheck' : checkNoZeroSum good l (k + 1 - j) (acc + j • g) = true := by
        simp only [checkNoZeroSum, List.all_eq_true] at hcheck
        simpa using hcheck j hj
      have hsum : π acc + (replicate j (π g) + T₂).sum = π (acc + j • g) + T₂.sum := by
        simp [sum_replicate, add_assoc]
      rw [hsum]
      exact ih (k + 1 - j) (acc + j • g) hcheck' T₂ hT₂ (by omega)

/-! ## Zero-sum constants and the two properties -/

/-- The Erdős–Ginzburg–Ziv-type constant: the least `ℓ` such that every sequence over `G` of
length at least `ℓ` has a zero-sum subsequence of length exactly `k`.  With `k = exp(G)` this is
the paper's `s(G)`.  (For finite `G` with `k • g = 0` the defining set is nonempty, see
`hasZeroSumOfLength_of_le_card`, so the `sInf` is not the junk value.) -/
noncomputable def egzConst (G : Type*) [AddCommMonoid G] (k : ℕ) : ℕ :=
  sInf {ℓ | ∀ S : Multiset G, ℓ ≤ card S → HasZeroSumOfLength k S}

/-- The constant `η`: the least `ℓ` such that every sequence over `G` of length at least `ℓ`
has a nonempty zero-sum subsequence of length at most `k`.  With `k = exp(G)` this is the
paper's `η(G)`. -/
noncomputable def etaConst (G : Type*) [AddCommMonoid G] (k : ℕ) : ℕ :=
  sInf {ℓ | ∀ S : Multiset G, ℓ ≤ card S → HasShortZeroSum k S}

/-- **Property D** for `C_n^r = (ℤ/nℤ)^r` (Gao–Geroldinger 2006, Conjecture 7.2): every
sequence `S` with `|S| = s(C_n^r) - 1` and no zero-sum subsequence of length exactly `n` has
the form `T^{n-1}`.  The length condition is written `|S| + 1 = s(C_n^r)` to avoid truncated
subtraction. -/
def PropertyD (n r : ℕ) : Prop :=
  ∀ S : Multiset (Fin r → ZMod n), card S + 1 = egzConst (Fin r → ZMod n) n →
    ¬ HasZeroSumOfLength n S → ∃ T : Multiset (Fin r → ZMod n), S = (n - 1) • T

/-- **Property C** for `C_n^r = (ℤ/nℤ)^r` (Gao–Hou–Schmid–Thangadurai 2007, Open Problems
1.2(C3)): every sequence `S` with `|S| = η(C_n^r) - 1` and no nonempty zero-sum subsequence of
length at most `n` has the form `T^{n-1}`. -/
def PropertyC (n r : ℕ) : Prop :=
  ∀ S : Multiset (Fin r → ZMod n), card S + 1 = etaConst (Fin r → ZMod n) n →
    ¬ HasShortZeroSum n S → ∃ T : Multiset (Fin r → ZMod n), S = (n - 1) • T

/-! ## Generic facts about the constants -/

/-- Every sequence avoiding `Q` is shorter than `sInf {ℓ | every sequence of length ≥ ℓ has Q}`
when that set is nonempty. -/
theorem card_lt_sInf_of_not {G : Type*} (Q : Multiset G → Prop)
    (hne : {ℓ | ∀ S : Multiset G, ℓ ≤ card S → Q S}.Nonempty) (S : Multiset G) (hS : ¬ Q S) :
    card S < sInf {ℓ | ∀ S : Multiset G, ℓ ≤ card S → Q S} := by
  by_contra hlt
  exact hS (Nat.sInf_mem hne S (not_lt.mp hlt))

/-- If the empty sequence avoids `Q` and the defining set is nonempty, some sequence avoiding
`Q` has length exactly `sInf {ℓ | …} - 1`: an extremal sequence exists. -/
theorem exists_card_add_one_eq_sInf {G : Type*} (Q : Multiset G → Prop) (hQ0 : ¬ Q 0)
    (hne : {ℓ | ∀ S : Multiset G, ℓ ≤ card S → Q S}.Nonempty) :
    ∃ S : Multiset G, ¬ Q S ∧ card S + 1 = sInf {ℓ | ∀ S : Multiset G, ℓ ≤ card S → Q S} := by
  set s := sInf {ℓ | ∀ S : Multiset G, ℓ ≤ card S → Q S} with hs
  have hpos : 0 < s := by
    by_contra h0
    have hs0 : s = 0 := by omega
    exact hQ0 (Nat.sInf_mem hne 0 (by rw [← hs, hs0]; exact le_refl _))
  have hnot : s - 1 ∉ {ℓ | ∀ S : Multiset G, ℓ ≤ card S → Q S} :=
    Nat.notMem_of_lt_sInf (by omega)
  simp only [Set.mem_ofPred_eq, not_forall] at hnot
  obtain ⟨S, hle, hS⟩ := hnot
  have hlt := card_lt_sInf_of_not Q hne S hS
  exact ⟨S, hS, by omega⟩

/-- In a finite group of exponent dividing `k`, every sequence of length at least
`k * |G|` has a zero-sum subsequence of length `k` (some term occurs `k` times). -/
theorem hasZeroSumOfLength_of_le_card {G : Type*} [AddCommMonoid G] [Fintype G] [DecidableEq G]
    (k : ℕ) (hk : ∀ g : G, k • g = 0) (S : Multiset G) (hS : k * Fintype.card G ≤ card S) :
    HasZeroSumOfLength k S := by
  by_cases hrep : ∃ a, k ≤ count a S
  · obtain ⟨a, ha⟩ := hrep
    exact ⟨replicate k a, le_count_iff_replicate_le.mp ha, card_replicate k a,
      by rw [sum_replicate, hk]⟩
  · push Not at hrep
    exfalso
    have hcardG : 0 < Fintype.card G := Fintype.card_pos
    have hsum : card S ≤ ∑ a ∈ S.toFinset, (k - 1) := by
      rw [← toFinset_sum_count_eq]
      exact Finset.sum_le_sum fun a _ => by have := hrep a; omega
    have hfin : S.toFinset.card ≤ Fintype.card G := Finset.card_le_univ _
    rw [Finset.sum_const, smul_eq_mul] at hsum
    have hk0 : 0 < k := by
      by_contra hk0
      have : k = 0 := by omega
      exact absurd (hrep 0) (by omega)
    have h1 : S.toFinset.card * (k - 1) ≤ Fintype.card G * (k - 1) :=
      Nat.mul_le_mul_right _ hfin
    have h2 : Fintype.card G * (k - 1) < k * Fintype.card G := by
      rw [Nat.mul_comm k]
      exact Nat.mul_lt_mul_of_pos_left (by omega) hcardG
    omega

/-- A zero-sum subsequence of length exactly `k ≥ 1` is in particular short. -/
theorem HasZeroSumOfLength.hasShortZeroSum {G : Type*} [AddCommMonoid G] {k : ℕ} (hk : 0 < k)
    {S : Multiset G} (h : HasZeroSumOfLength k S) : HasShortZeroSum k S := by
  obtain ⟨T, hT, hcard, hsum⟩ := h
  exact ⟨T, hT, by omega, by omega, hsum⟩

/-- `n • g = 0` in `C_n^r = (ℤ/nℤ)^r`. -/
theorem nsmul_eq_zero_zmodPow (n r : ℕ) (g : Fin r → ZMod n) : n • g = 0 := by
  funext i
  simp [nsmul_eq_mul]

/-! ## The parity observation (Proposition `prop:even`) -/

/-- For even `n`, if `x, y ∈ ℤ/nℤ` have representatives of the same parity then
`(n/2) • (x + y) = 0`. -/
theorem half_nsmul_add_eq_zero {n : ℕ} [NeZero n] (hn : Even n) (x y : ZMod n)
    (hxy : ((x.val : ℕ) : ZMod 2) = ((y.val : ℕ) : ZMod 2)) : (n / 2) • (x + y) = 0 := by
  rw [ZMod.natCast_eq_natCast_iff'] at hxy
  obtain ⟨m, hm⟩ : 2 ∣ x.val + y.val := by omega
  have hxy' : x + y = ((x.val + y.val : ℕ) : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [hxy', hm, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  obtain ⟨c, hc⟩ := hn
  have hhalf : (c + c) / 2 = c := by omega
  exact ⟨m, by rw [hc, hhalf]; ring⟩

/-- Proposition `prop:even`, first half: if `n` is even and `U^{n-1}` has no `n`-term zero sum
over `C_n^r`, then `U` is squarefree and injective modulo `2`, hence `|U| ≤ 2^r`. -/
theorem card_le_two_pow_of_not_hasZeroSumOfLength {n r : ℕ} [NeZero n] (hn : Even n)
    (U : Multiset (Fin r → ZMod n)) (hU : ¬ HasZeroSumOfLength n ((n - 1) • U)) :
    card U ≤ 2 ^ r := by
  classical
  have hn2 : 2 ≤ n := by
    obtain ⟨c, hc⟩ := hn
    have := NeZero.ne n
    omega
  -- `U` is squarefree.
  have hnodup : U.Nodup := by
    rw [nodup_iff_count_le_one]
    intro a
    by_contra ha
    apply hU
    refine ⟨replicate n a, ?_, card_replicate n a, by rw [sum_replicate, nsmul_eq_zero_zmodPow]⟩
    rw [← le_count_iff_replicate_le, count_nsmul]
    have : 2 * (n - 1) ≤ (n - 1) * count a U := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  -- Reduction modulo `2` is injective on the support of `U`.
  let red : (Fin r → ZMod n) → (Fin r → ZMod 2) := fun a i => ((a i).val : ZMod 2)
  have hinj : Set.InjOn red (U.toFinset : Set (Fin r → ZMod n)) := by
    intro a ha b hb hab
    by_contra hne
    apply hU
    have ha' : a ∈ U := by simpa using ha
    have hb' : b ∈ U := by simpa using hb
    refine ⟨replicate (n / 2) a + replicate (n / 2) b, ?_, ?_, ?_⟩
    · rw [Multiset.le_iff_count]
      intro c
      have hca : 1 ≤ count a U := one_le_count_iff_mem.mpr ha'
      have hcb : 1 ≤ count b U := one_le_count_iff_mem.mpr hb'
      rw [count_add, count_replicate, count_replicate, count_nsmul]
      by_cases hc : c = a
      · subst hc
        rw [if_pos rfl, if_neg (Ne.symm hne)]
        have : n - 1 ≤ (n - 1) * count c U := Nat.le_mul_of_pos_right _ hca
        omega
      · rw [if_neg (Ne.symm hc)]
        by_cases hcb' : c = b
        · subst hcb'
          rw [if_pos rfl]
          have : n - 1 ≤ (n - 1) * count c U := Nat.le_mul_of_pos_right _ hcb
          omega
        · rw [if_neg (Ne.symm hcb')]
          omega
    · rw [card_add, card_replicate, card_replicate]
      obtain ⟨c, hc⟩ := hn
      omega
    · rw [sum_add, sum_replicate, sum_replicate, ← smul_add]
      funext i
      simpa using half_nsmul_add_eq_zero hn (a i) (b i) (congrFun hab i)
  have hcard : U.toFinset.card ≤ (Finset.univ : Finset (Fin r → ZMod 2)).card :=
    Finset.card_le_card_of_injOn red (fun _ _ => Finset.mem_univ _) hinj
  rw [toFinset_card_of_nodup hnodup] at hcard
  simpa [Finset.card_univ, Fintype.card_fun, ZMod.card] using hcard

/-- Proposition `prop:even`, second half: if `n` is even and `V^{n-1}` has no short zero-sum
subsequence over `C_n^r`, then `|V| ≤ 2^r - 1` (stated as `|V| + 1 ≤ 2^r`). -/
theorem card_add_one_le_two_pow_of_not_hasShortZeroSum {n r : ℕ} [NeZero n] (hn : Even n)
    (V : Multiset (Fin r → ZMod n)) (hV : ¬ HasShortZeroSum n ((n - 1) • V)) :
    card V + 1 ≤ 2 ^ r := by
  classical
  have hU : ¬ HasZeroSumOfLength n ((n - 1) • ((0 : Fin r → ZMod n) ::ₘ V)) := by
    rintro ⟨T, hT, hcard, hsum⟩
    rw [nsmul_cons, nsmul_singleton] at hT
    obtain ⟨T₁, T₂, hT₁, hT₂, rfl⟩ := exists_split_of_le_add hT
    obtain ⟨j, hj, rfl⟩ := le_replicate_iff.mp hT₁
    rw [card_add, card_replicate] at hcard
    rw [sum_add, sum_replicate, smul_zero, zero_add] at hsum
    have hn0 : n ≠ 0 := NeZero.ne n
    have hpos : 0 < card T₂ := by omega
    have hle : card T₂ ≤ n := by omega
    exact hV ⟨T₂, hT₂, hpos, hle, hsum⟩
  have := card_le_two_pow_of_not_hasZeroSumOfLength hn _ hU
  simpa using this

/-! ## Translation and deletion of zeros (Lemma `lem:delete`) -/

/-- Lemma `lem:delete`: let `k • g = 0` for all `g`, let `S` have no zero-sum subsequence of
length `k ≥ 1`, and let `g` occur at least `k - 1` times in `S`.  Then
`R = 0^{-(k-1)} · (-g + S)` has no nonempty zero-sum subsequence of length at most `k`. -/
theorem not_hasShortZeroSum_delete {G : Type*} [AddCommGroup G] [DecidableEq G] {k : ℕ}
    (hk : ∀ x : G, k • x = 0) (S : Multiset G) (hS : ¬ HasZeroSumOfLength k S) (g : G)
    (hg : k - 1 ≤ count g S) :
    ¬ HasShortZeroSum k (S.map (fun x => -g + x) - replicate (k - 1) 0) := by
  set M := S.map (fun x => -g + x) with hM
  have hcount : count 0 M = count g S := by
    have h := count_map_eq_count' (fun x => -g + x) S (add_right_injective (-g)) g
    simpa using h
  have hZ : replicate (k - 1) (0 : G) ≤ M := le_count_iff_replicate_le.mp (by omega)
  rintro ⟨T, hT, hpos, hle, hsum⟩
  apply hS
  set T' := T + replicate (k - card T) (0 : G) with hT'
  have hT'M : T' ≤ M := by
    have h1 : replicate (k - card T) (0 : G) ≤ replicate (k - 1) 0 :=
      (replicate_le_replicate 0).mpr (by omega)
    calc T' ≤ (M - replicate (k - 1) 0) + replicate (k - 1) 0 := add_le_add hT h1
      _ = M := tsub_add_cancel_of_le hZ
  refine ⟨T'.map (fun x => g + x), ?_, ?_, ?_⟩
  · have hback : M.map (fun x => g + x) = S := by
      rw [hM, map_map]
      conv_rhs => rw [← map_id S]
      congr 1
      funext x
      simp
    rw [← hback]
    exact map_le_map hT'M
  · rw [card_map, hT', card_add, card_replicate]
    omega
  · rw [sum_map_add, map_const', sum_replicate, map_id', hT', sum_add, sum_replicate,
      smul_zero, add_zero, hsum, add_zero, card_add, card_replicate]
    have hk' : card T + (k - card T) = k := by omega
    rw [hk', hk]

/-- Cardinality of the sequence `R` of Lemma `lem:delete`: `|R| + (k - 1) = |S|`. -/
theorem card_delete {G : Type*} [AddCommGroup G] [DecidableEq G] {k : ℕ} (S : Multiset G)
    (g : G) (hg : k - 1 ≤ count g S) :
    card (S.map (fun x => -g + x) - replicate (k - 1) 0) + (k - 1) = card S := by
  have hcount : count 0 (S.map (fun x => -g + x)) = count g S := by
    have h := count_map_eq_count' (fun x => -g + x) S (add_right_injective (-g)) g
    simpa using h
  have hZ : replicate (k - 1) (0 : G) ≤ S.map (fun x => -g + x) :=
    le_count_iff_replicate_le.mp (by omega)
  have h := card_le_card hZ
  rw [card_sub hZ, card_replicate, card_map]
  rw [card_replicate, card_map] at h
  omega

/-- `seqOfList` of a cons is the corresponding block followed by the rest. -/
theorem seqOfList_cons {M G : Type*} [AddCommMonoid M] [AddCommMonoid G] (π : M →+ G)
    (p : M × ℕ) (l : List (M × ℕ)) :
    seqOfList π (p :: l) = replicate p.2 (π p.1) + seqOfList π l := by
  simp [seqOfList]

/-! ## The counterexample over `C_6^4` (Section 3, equation `(S)`) -/

/-- Reduction of a vector of natural numbers to `C_6^4 = (ℤ/6ℤ)^4`, coordinatewise. -/
def natVecHom : ℕ × ℕ × ℕ × ℕ →+ (Fin 4 → ZMod 6) where
  toFun x := ![(x.1 : ZMod 6), (x.2.1 : ZMod 6), (x.2.2.1 : ZMod 6), (x.2.2.2 : ZMod 6)]
  map_zero' := by
    funext i
    fin_cases i <;> rfl
  map_add' x y := by
    funext i
    fin_cases i <;> simp

/-- `goodSix x` certifies that `x` does not reduce to `0` in `(ℤ/6ℤ)^4`. -/
def goodSix (x : ℕ × ℕ × ℕ × ℕ) : Bool :=
  x.1 % 6 != 0 || x.2.1 % 6 != 0 || x.2.2.1 % 6 != 0 || x.2.2.2 % 6 != 0

/-- `natVecHom` reduces coordinatewise modulo `6`. -/
example : natVecHom (7, 6, 8, 11) = ![1, 0, 2, 5] := by decide

/-- `goodSix` rejects a vector that vanishes modulo `6` and accepts `a`. -/
example : goodSix (6, 12, 0, 18) = false ∧ goodSix (0, 0, 2, 2) = true := by decide

/-- `goodSix` is a sound certificate of nonvanishing. -/
theorem natVecHom_ne_zero_of_goodSix (x : ℕ × ℕ × ℕ × ℕ) (hx : goodSix x = true) :
    natVecHom x ≠ 0 := by
  intro h0
  have h : ∀ i, natVecHom x i = 0 := fun i => congrFun h0 i
  have h1 : 6 ∣ x.1 := by simpa [natVecHom, ZMod.natCast_eq_zero_iff] using h 0
  have h2 : 6 ∣ x.2.1 := by simpa [natVecHom, ZMod.natCast_eq_zero_iff] using h 1
  have h3 : 6 ∣ x.2.2.1 := by simpa [natVecHom, ZMod.natCast_eq_zero_iff] using h 2
  have h4 : 6 ∣ x.2.2.2 := by simpa [natVecHom, ZMod.natCast_eq_zero_iff] using h 3
  simp only [goodSix, Bool.or_eq_true, bne_iff_ne, ne_eq] at hx
  omega

/-- The support of the paper's sequence `S` with multiplicities, written in `(ℤ/6ℤ)^4`
coordinates (obtained by CRT from the paper's `𝔽_2^4 ⊕ 𝔽_3^4` description): the element
`a = (0,0,2,2)` with multiplicity `5`, `b = (0,1,0,2) = g_-(Y)` with multiplicity `1`, and the
fifteen remaining heavy terms `g_±(p)` with multiplicity `5`. -/
def sixFourSupport : List ((ℕ × ℕ × ℕ × ℕ) × ℕ) :=
  [((0, 0, 2, 2), 5), ((0, 1, 0, 2), 1), ((0, 2, 3, 2), 5), ((1, 0, 0, 1), 5),
   ((1, 1, 2, 0), 5), ((1, 2, 5, 0), 5), ((2, 3, 0, 2), 5), ((2, 4, 1, 3), 5),
   ((2, 5, 1, 3), 5), ((3, 4, 0, 4), 5), ((3, 5, 3, 1), 5), ((4, 3, 0, 5), 5),
   ((4, 4, 4, 3), 5), ((4, 5, 1, 0), 5), ((5, 3, 3, 4), 5), ((5, 4, 5, 3), 5),
   ((5, 5, 2, 3), 5)]

/-- The paper's sequence `S = a^5 b ∏ g_+(p)^5 ∏_{p ≠ Y} g_-(p)^5` over `C_6^4`. -/
def sixFourSeq : Multiset (Fin 4 → ZMod 6) := seqOfList natVecHom sixFourSupport

/-- `|S| = 81`. -/
theorem card_sixFourSeq : card sixFourSeq = 81 := by
  simp [sixFourSeq, seqOfList, sixFourSupport]

/-- The heavy term `a = (0,0,2,2)` occurs (at least) five times in `S`. -/
theorem five_le_count_sixFourSeq : 5 ≤ count (natVecHom (0, 0, 2, 2)) sixFourSeq := by
  classical
  rw [sixFourSeq, sixFourSupport, seqOfList_cons, count_add, count_replicate_self]
  omega

/-- The kernel computation: every choice of `6` terms of `S` (counted with multiplicity) has a
sum that is nonzero modulo `6` in some coordinate. -/
theorem checkNoZeroSum_sixFourSupport :
    checkNoZeroSum goodSix sixFourSupport 6 0 = true := by
  decide +kernel

/-- Lemma `lemma:construction`: `S` has no zero-sum subsequence of length six. -/
theorem not_hasZeroSumOfLength_sixFourSeq : ¬ HasZeroSumOfLength 6 sixFourSeq := by
  classical
  rintro ⟨T, hT, hcard, hsum⟩
  have h := checkNoZeroSum_sound natVecHom goodSix natVecHom_ne_zero_of_goodSix
    sixFourSupport 6 0 checkNoZeroSum_sixFourSupport T hT hcard
  rw [_root_.map_zero, zero_add] at h
  exact h hsum

/-- The translated sequence `R = 0^{-5} · (-a + S)` of length `76` over `C_6^4`. -/
def sixFourShortSeq : Multiset (Fin 4 → ZMod 6) :=
  sixFourSeq.map (fun x => -natVecHom (0, 0, 2, 2) + x) - replicate (6 - 1) 0

/-- `|R| = 76`. -/
theorem card_sixFourShortSeq : card sixFourShortSeq = 76 := by
  classical
  have h := card_delete (k := 6) sixFourSeq (natVecHom (0, 0, 2, 2)) five_le_count_sixFourSeq
  rw [card_sixFourSeq] at h
  unfold sixFourShortSeq
  omega

/-- `R` has no nonempty zero-sum subsequence of length at most six. -/
theorem not_hasShortZeroSum_sixFourShortSeq : ¬ HasShortZeroSum 6 sixFourShortSeq := by
  classical
  exact not_hasShortZeroSum_delete (nsmul_eq_zero_zmodPow 6 4) sixFourSeq
    not_hasZeroSumOfLength_sixFourSeq _ five_le_count_sixFourSeq

/-! ## Main results (Theorem `thm:main`, case `r = 4`) -/

/-- The defining set of `s(C_6^4)` is nonempty. -/
theorem egz_set_nonempty_six_four :
    {ℓ | ∀ S : Multiset (Fin 4 → ZMod 6), ℓ ≤ card S → HasZeroSumOfLength 6 S}.Nonempty := by
  classical
  exact ⟨6 * Fintype.card (Fin 4 → ZMod 6),
    fun S hS => hasZeroSumOfLength_of_le_card 6 (nsmul_eq_zero_zmodPow 6 4) S hS⟩

/-- The defining set of `η(C_6^4)` is nonempty. -/
theorem eta_set_nonempty_six_four :
    {ℓ | ∀ S : Multiset (Fin 4 → ZMod 6), ℓ ≤ card S → HasShortZeroSum 6 S}.Nonempty := by
  classical
  exact ⟨6 * Fintype.card (Fin 4 → ZMod 6), fun S hS =>
    (hasZeroSumOfLength_of_le_card 6 (nsmul_eq_zero_zmodPow 6 4) S hS).hasShortZeroSum
      (by norm_num)⟩

/-- `s(C_6^4) ≥ 82 > 2^4 · 5 + 1`: Harborth's lower bound is strict at `C_6^4`. -/
theorem egzConst_six_four_ge : 82 ≤ egzConst (Fin 4 → ZMod 6) 6 := by
  have h := card_lt_sInf_of_not _ egz_set_nonempty_six_four sixFourSeq
    not_hasZeroSumOfLength_sixFourSeq
  rw [card_sixFourSeq] at h
  exact h

/-- `η(C_6^4) ≥ 77 > (2^4 - 1) · 5 + 1`. -/
theorem etaConst_six_four_ge : 77 ≤ etaConst (Fin 4 → ZMod 6) 6 := by
  have h := card_lt_sInf_of_not _ eta_set_nonempty_six_four sixFourShortSeq
    not_hasShortZeroSum_sixFourShortSeq
  rw [card_sixFourShortSeq] at h
  exact h

/-- **Theorem `thm:main` (Property D, `r = 4`).** The group `C_6^4` does not have Property D:
the Gao–Geroldinger Property D conjecture fails for `n = 6`, `r = 4`. -/
theorem not_propertyD_six_four : ¬ PropertyD 6 4 := by
  intro hD
  obtain ⟨S, hS, hcard⟩ := exists_card_add_one_eq_sInf
    (fun S : Multiset (Fin 4 → ZMod 6) => HasZeroSumOfLength 6 S)
    (by rintro ⟨T, hT, hTc, -⟩; rw [le_zero.mp hT] at hTc; simp at hTc)
    egz_set_nonempty_six_four
  obtain ⟨T, rfl⟩ := hD S hcard hS
  have hT : card T ≤ 2 ^ 4 :=
    card_le_two_pow_of_not_hasZeroSumOfLength (n := 6) (by decide) T hS
  have hge := egzConst_six_four_ge
  unfold egzConst at hge
  rw [card_nsmul] at hcard
  omega

/-- **Theorem `thm:main` (Property C, `r = 4`).** The group `C_6^4` does not have Property C:
the Property C problem of Gao–Hou–Schmid–Thangadurai has a negative answer for `n = 6`,
`r = 4`. -/
theorem not_propertyC_six_four : ¬ PropertyC 6 4 := by
  intro hC
  obtain ⟨S, hS, hcard⟩ := exists_card_add_one_eq_sInf
    (fun S : Multiset (Fin 4 → ZMod 6) => HasShortZeroSum 6 S)
    (by rintro ⟨T, hT, hTc, -⟩; rw [le_zero.mp hT] at hTc; simp at hTc)
    eta_set_nonempty_six_four
  obtain ⟨V, rfl⟩ := hC S hcard hS
  have hV : card V + 1 ≤ 2 ^ 4 :=
    card_add_one_le_two_pow_of_not_hasShortZeroSum (n := 6) (by decide) V hS
  have hge := etaConst_six_four_ge
  unfold etaConst at hge
  rw [card_nsmul] at hcard
  omega

/-! ## All ranks `r ≥ 4` (proof of Theorem `thm:main`) -/

/-- An additive equivalence transports sequences without `k`-term zero sums. -/
theorem not_hasZeroSumOfLength_map_addEquiv {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    (e : G ≃+ H) {k : ℕ} (S : Multiset G) (hS : ¬ HasZeroSumOfLength k S) :
    ¬ HasZeroSumOfLength k (S.map e) := by
  rintro ⟨T, hT, hcard, hsum⟩
  apply hS
  refine ⟨T.map e.symm, ?_, by rw [card_map, hcard], ?_⟩
  · have h := map_le_map (f := e.symm) hT
    rwa [map_map, show (e.symm ∘ e : G → G) = id from funext e.symm_apply_apply, map_id] at h
  · rw [← map_multiset_sum, hsum, _root_.map_zero]

/-- The binary doubling step of the paper: if `S` has no `6`-term zero sum over `G`, then
neither has `∏_{ε ∈ {0,1}} ∏_{g} (ε, g)^{v_g(S)}` over `C_6 ⊕ G`.  In the new coordinate the
six entries lie in `{0, 1}` and sum to `0` mod `6`, so they are all equal. -/
theorem not_hasZeroSumOfLength_double {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (S : Multiset G) (hS : ¬ HasZeroSumOfLength 6 S) :
    ¬ HasZeroSumOfLength 6
      (S.map (fun x => ((0 : ZMod 6), x)) + S.map (fun x => ((1 : ZMod 6), x))) := by
  rintro ⟨T, hT, hcard, hsum⟩
  obtain ⟨T₁, T₂, h₁, h₂, rfl⟩ := exists_split_of_le_add hT
  -- first coordinates: `0` on `T₁` and `1` on `T₂`
  have hfst₁ : T₁.map Prod.fst = replicate (card T₁) 0 := by
    rw [eq_replicate, card_map]
    refine ⟨rfl, fun b hb => ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hb
    obtain ⟨x, -, rfl⟩ := mem_map.mp (mem_of_le h₁ ht)
    rfl
  have hfst₂ : T₂.map Prod.fst = replicate (card T₂) 1 := by
    rw [eq_replicate, card_map]
    refine ⟨rfl, fun b hb => ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hb
    obtain ⟨x, -, rfl⟩ := mem_map.mp (mem_of_le h₂ ht)
    rfl
  have hfst : ((card T₂ : ℕ) : ZMod 6) = 0 := by
    have h : AddMonoidHom.fst (ZMod 6) G (T₁ + T₂).sum = 0 := by
      rw [hsum, _root_.map_zero]
    rw [map_multiset_sum] at h
    have e₁ : T₁.map (AddMonoidHom.fst (ZMod 6) G) = T₁.map Prod.fst := rfl
    have e₂ : T₂.map (AddMonoidHom.fst (ZMod 6) G) = T₂.map Prod.fst := rfl
    rw [Multiset.map_add, sum_add, e₁, e₂, hfst₁, hfst₂, sum_replicate,
      sum_replicate, smul_zero, zero_add, nsmul_one] at h
    exact h
  rw [card_add] at hcard
  rw [ZMod.natCast_eq_zero_iff] at hfst
  -- the second coordinates give a `6`-term zero sum of `S`
  have hsnd : ∀ (U : Multiset (ZMod 6 × G)) (c : ZMod 6),
      U ≤ S.map (fun x => (c, x)) → card U = 6 → U.sum.2 = 0 → False := by
    intro U c hU hUc hUs
    apply hS
    refine ⟨U.map Prod.snd, ?_, by rw [card_map, hUc], ?_⟩
    · have h := map_le_map (f := Prod.snd) hU
      rwa [map_map, show (Prod.snd ∘ fun x => (c, x) : G → G) = id from rfl, map_id] at h
    · rw [← hUs]
      exact (map_multiset_sum (AddMonoidHom.snd (ZMod 6) G) U).symm
  have hsum2 : (T₁ + T₂).sum.2 = 0 := by rw [hsum]; rfl
  rcases Nat.lt_or_ge (card T₂) 6 with hlt | hge
  · have h0 : card T₂ = 0 := by omega
    rw [card_eq_zero] at h0
    subst h0
    rw [card_zero, add_zero] at hcard
    rw [add_zero] at hsum2
    exact hsnd T₁ 0 h₁ hcard hsum2
  · have h0 : card T₁ = 0 := by omega
    rw [card_eq_zero] at h0
    subst h0
    rw [card_zero, zero_add] at hcard
    rw [zero_add] at hsum2
    exact hsnd T₂ 1 h₂ hcard hsum2

/-- `(ℤ/6ℤ) ⊕ (ℤ/6ℤ)^m ≃ (ℤ/6ℤ)^{m+1}` via `Fin.cons`. -/
def consAddEquiv (m : ℕ) : (ZMod 6 × (Fin m → ZMod 6)) ≃+ (Fin (m + 1) → ZMod 6) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, Fin.tail f)
  left_inv p := by simp
  right_inv f := by simp
  map_add' p q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The sequences `S_r` of the paper: for every `d`, there is a sequence over `C_6^{4+d}` of
length `81 · 2^d` with no `6`-term zero sum and with a term of multiplicity at least `5`. -/
theorem exists_seq_six (d : ℕ) :
    ∃ S : Multiset (Fin (4 + d) → ZMod 6), card S = 81 * 2 ^ d ∧
      ¬ HasZeroSumOfLength 6 S ∧ ∃ g, 5 ≤ count g S := by
  classical
  induction d with
  | zero =>
    exact ⟨sixFourSeq, card_sixFourSeq, not_hasZeroSumOfLength_sixFourSeq, _,
      five_le_count_sixFourSeq⟩
  | succ d ih =>
    obtain ⟨S, hcard, hS, g, hg⟩ := ih
    let S' : Multiset (ZMod 6 × (Fin (4 + d) → ZMod 6)) :=
      S.map (fun x => ((0 : ZMod 6), x)) + S.map (fun x => ((1 : ZMod 6), x))
    refine ⟨S'.map (consAddEquiv (4 + d)), ?_, ?_, consAddEquiv (4 + d) (0, g), ?_⟩
    · simp only [S', card_map, card_add, hcard, pow_succ]
      ring
    · exact not_hasZeroSumOfLength_map_addEquiv _ S' (not_hasZeroSumOfLength_double S hS)
    · rw [count_map_eq_count' _ _ (consAddEquiv (4 + d)).injective, count_add,
        count_map_eq_count' _ _ (Prod.mk_right_injective (0 : ZMod 6))]
      omega

/-- The defining set of `s(C_n^r)` is nonempty (`n ≥ 1`). -/
theorem egz_set_nonempty (n r : ℕ) [NeZero n] :
    {ℓ | ∀ S : Multiset (Fin r → ZMod n), ℓ ≤ card S → HasZeroSumOfLength n S}.Nonempty := by
  classical
  exact ⟨n * Fintype.card (Fin r → ZMod n),
    fun S hS => hasZeroSumOfLength_of_le_card n (nsmul_eq_zero_zmodPow n r) S hS⟩

/-- The defining set of `η(C_n^r)` is nonempty (`n ≥ 1`). -/
theorem eta_set_nonempty (n r : ℕ) [NeZero n] :
    {ℓ | ∀ S : Multiset (Fin r → ZMod n), ℓ ≤ card S → HasShortZeroSum n S}.Nonempty := by
  classical
  exact ⟨n * Fintype.card (Fin r → ZMod n), fun S hS =>
    (hasZeroSumOfLength_of_le_card n (nsmul_eq_zero_zmodPow n r) S hS).hasShortZeroSum
      (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-- **Theorem `thm:main`.** For every `r ≥ 4`, the group `C_6^r` has neither Property C nor
Property D.  In particular the Property C problem (Gao–Hou–Schmid–Thangadurai 2007) and the
Property D conjecture (Gao–Geroldinger 2006) fail in general. -/
theorem thm_main (r : ℕ) (hr : 4 ≤ r) : ¬ PropertyD 6 r ∧ ¬ PropertyC 6 r := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨S, hcardS, hS, g, hg⟩ := exists_seq_six d
  have hpow : 2 ^ (4 + d) = 16 * 2 ^ d := by rw [pow_add]; norm_num
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  constructor
  · intro hD
    have hlt := card_lt_sInf_of_not _ (egz_set_nonempty 6 (4 + d)) S hS
    obtain ⟨S₀, hS₀, hcard₀⟩ := exists_card_add_one_eq_sInf
      (fun S : Multiset (Fin (4 + d) → ZMod 6) => HasZeroSumOfLength 6 S)
      (by rintro ⟨T, hT, hTc, -⟩; rw [le_zero.mp hT] at hTc; simp at hTc)
      (egz_set_nonempty 6 (4 + d))
    obtain ⟨T, rfl⟩ := hD S₀ hcard₀ hS₀
    have hT : card T ≤ 2 ^ (4 + d) :=
      card_le_two_pow_of_not_hasZeroSumOfLength (n := 6) (by decide) T hS₀
    rw [card_nsmul] at hcard₀
    omega
  · intro hC
    have hR := not_hasShortZeroSum_delete (nsmul_eq_zero_zmodPow 6 (4 + d)) S hS g hg
    have hRc := card_delete (k := 6) S g hg
    have hlt := card_lt_sInf_of_not _ (eta_set_nonempty 6 (4 + d)) _ hR
    obtain ⟨S₀, hS₀, hcard₀⟩ := exists_card_add_one_eq_sInf
      (fun S : Multiset (Fin (4 + d) → ZMod 6) => HasShortZeroSum 6 S)
      (by rintro ⟨T, hT, hTc, -⟩; rw [le_zero.mp hT] at hTc; simp at hTc)
      (eta_set_nonempty 6 (4 + d))
    obtain ⟨V, rfl⟩ := hC S₀ hcard₀ hS₀
    have hV : card V + 1 ≤ 2 ^ (4 + d) :=
      card_add_one_le_two_pow_of_not_hasShortZeroSum (n := 6) (by decide) V hS₀
    rw [card_nsmul] at hcard₀
    omega

end ZeroSumPropertyCD

