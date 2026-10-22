/-
# A003278: Jeffery's identities for Szekeres's sequence

OEIS A003278, L. Edson Jeffery (Nov 26 2015), with A191107 and A055246.
For `n ≥ 1`, `3*a(n) = A191107(n) + 2` and `6*a(n) = A055246(n) + 5`.
The three increasing enumerations are affine images of the binary-to-ternary
map: `t + 1`, `3t + 1`, and `6t + 1`.
A003278 uses its direct digit characterization; its alternative greedy
three-term-progression characterization is not formalized.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A003278JefferySzekeres

/-! ## Definitions -/

/-- Read the binary digits of `m` as ternary digits: `binToTer m` is the number
whose ternary representation is the binary representation of `m`. -/
def binToTer (m : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 m)

/-- **A003278** (offset 1), by the first clause of the entry's name:
"a(n)-1 in ternary = n-1 in binary", i.e. `a(n) = 1 + binToTer (n - 1)`.
The value at the junk index `n = 0` is irrelevant. -/
def a003278 (n : ℕ) : ℕ := 1 + binToTer (n - 1)

/-- Membership in **A191107**: the least set containing `1` and closed under
`x ↦ 3x - 2` and `x ↦ 3x + 1`.  (Every member is `≥ 1`, so the truncated
subtraction `3 * x - 2` never meets its junk value on members.) -/
inductive InA191107 : ℕ → Prop
  /-- `a(1) = 1`. -/
  | one : InA191107 1
  /-- If `x` is in the sequence then so is `3x - 2`. -/
  | left {x : ℕ} : InA191107 x → InA191107 (3 * x - 2)
  /-- If `x` is in the sequence then so is `3x + 1`. -/
  | right {x : ℕ} : InA191107 x → InA191107 (3 * x + 1)

/-- **A191107** (offset 1): the `n`-th smallest member of `InA191107`. -/
noncomputable def a191107 (n : ℕ) : ℕ := Nat.nth InA191107 (n - 1)

/-- The Cantor middle-third construction: after `k` steps the closed intervals
that remain are `[c / 3^k, (c + 1) / 3^k]` for `c ∈ cantorKept k`.  Each step
replaces `[c / 3^k, (c+1) / 3^k]` by its outer thirds, with left numerators
`3c` and `3c + 2` over `3^(k+1)`. -/
def cantorKept : ℕ → Finset ℕ
  | 0 => {0}
  | k + 1 => (cantorKept k).image (fun c => 3 * c) ∪ (cantorKept k).image (fun c => 3 * c + 2)

/-- At step `k ≥ 1` the open intervals erased are the middle thirds
`((3c + 1) / 3^k, (3c + 2) / 3^k)` of the intervals kept after `k - 1` steps;
`erasedNumerators k` is the set of their left numerators `a` in
`I(k, n) = (a / 3^k, (1 + a) / 3^k)`. -/
def erasedNumerators (k : ℕ) : Finset ℕ := (cantorKept (k - 1)).image (fun c => 3 * c + 1)

/-- `x` is a left numerator of an interval erased at some step `k ≥ 1` of the
Cantor construction. -/
def IsErasedNumerator (x : ℕ) : Prop := ∃ k, 1 ≤ k ∧ x ∈ erasedNumerators k

/-- **A055246** (offset 1): the `n`-th smallest erased numerator.  The entry
lists, for each `k`, the `2^(k-1)` numerators of step `k` in increasing order as
`a(1), …, a(2^(k-1))`; as integers the numerator sets of successive steps are
nested initial segments, so this is the increasing enumeration of their union. -/
noncomputable def a055246 (n : ℕ) : ℕ := Nat.nth IsErasedNumerator (n - 1)

/-! ## Examples for the explicit definitions -/

example : (List.range 16).map (fun i => a003278 (i + 1)) =
    [1, 2, 4, 5, 10, 11, 13, 14, 28, 29, 31, 32, 37, 38, 40, 41] := by decide

example : cantorKept 2 = {0, 2, 6, 8} := by decide

example : erasedNumerators 1 = {1} := by decide

example : erasedNumerators 3 = {1, 7, 19, 25} := by decide

example : InA191107 28 := by
  have h4 : InA191107 4 := InA191107.right InA191107.one
  have h10 : InA191107 10 := InA191107.left h4
  exact InA191107.left h10

/-! ## The binary-to-ternary map -/

/-- Appending a binary digit `b` to `m` appends the ternary digit `b`. -/
theorem binToTer_bit (m b : ℕ) (hb : b < 2) :
    binToTer (2 * m + b) = 3 * binToTer m + b := by
  rcases Nat.eq_zero_or_pos (2 * m + b) with h | h
  · have hm : m = 0 := by omega
    have hb0 : b = 0 := by omega
    subst hm hb0
    simp [binToTer]
  · unfold binToTer
    rw [Nat.digits_def' (by norm_num) h, Nat.ofDigits_cons]
    have h1 : (2 * m + b) % 2 = b := by omega
    have h2 : (2 * m + b) / 2 = m := by omega
    rw [h1, h2]
    ring

/-- `binToTer 0 = 0`. -/
theorem binToTer_zero : binToTer 0 = 0 := by simp [binToTer]

/-- `binToTer` increases at every step. -/
theorem binToTer_lt_succ (m : ℕ) : binToTer m < binToTer (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · have h0 := binToTer_bit k 0 (by norm_num)
      have h1 := binToTer_bit k 1 (by norm_num)
      simp only [add_zero] at h0
      rw [h0, h1]
      omega
    · have h1 := binToTer_bit k 1 (by norm_num)
      have h2 := binToTer_bit (k + 1) 0 (by norm_num)
      have hk : binToTer k < binToTer (k + 1) := ih k (by omega)
      have he : 2 * k + 1 + 1 = 2 * (k + 1) + 0 := by ring
      rw [he, h1, h2]
      omega

/-- `binToTer` is strictly increasing. -/
theorem binToTer_strictMono : StrictMono binToTer :=
  strictMono_nat_of_lt_succ binToTer_lt_succ

/-- If a predicate holds exactly on the range of a strictly increasing
`g : ℕ → ℕ`, then its `n`-th member (from `0`) is `g n`. -/
theorem nth_eq_of_strictMono {p : ℕ → Prop} {g : ℕ → ℕ} (hg : StrictMono g)
    (hp : ∀ x, p x ↔ ∃ m, g m = x) (n : ℕ) : Nat.nth p n = g n := by
  have hinf : ∀ hfi : (Set.ofPred p).Finite, n < hfi.toFinset.card := by
    intro hfi
    exfalso
    have hsub : Set.range g ⊆ Set.ofPred p := by
      rintro x ⟨m, rfl⟩
      exact (hp (g m)).2 ⟨m, rfl⟩
    exact Set.infinite_range_of_injective hg.injective (hfi.subset hsub)
  have hcomp := Nat.nth_comp_of_strictMono hg (fun k hk => (hp k).1 hk) hinf
  have htrue : Nat.nth (fun i => p (g i)) n = n :=
    Nat.nth_of_forall (fun i _ => (hp (g i)).2 ⟨i, rfl⟩)
  rw [htrue] at hcomp
  exact hcomp.symm

/-! ## A191107 as an affine image -/

/-- The members of A191107 are exactly the numbers `3 t + 1` with `t` having
only ternary digits `0, 1`. -/
theorem inA191107_iff (x : ℕ) : InA191107 x ↔ ∃ m, 3 * binToTer m + 1 = x := by
  constructor
  · intro hx
    induction hx with
    | one => exact ⟨0, by simp [binToTer_zero]⟩
    | @left x _ ih =>
      obtain ⟨m, rfl⟩ := ih
      refine ⟨2 * m, ?_⟩
      have h0 := binToTer_bit m 0 (by norm_num)
      simp only [add_zero] at h0
      rw [h0]
      omega
    | @right x _ ih =>
      obtain ⟨m, rfl⟩ := ih
      refine ⟨2 * m + 1, ?_⟩
      rw [binToTer_bit m 1 (by norm_num)]
  · rintro ⟨m, rfl⟩
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
      · rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          simpa [binToTer_zero] using InA191107.one
        · have hmem := InA191107.left (ih k (by omega))
          have h0 := binToTer_bit k 0 (by norm_num)
          simp only [add_zero] at h0
          have he : 3 * (3 * binToTer k + 1) - 2 = 3 * binToTer (2 * k) + 1 := by
            rw [h0]
            omega
          rwa [he] at hmem
      · have hmem := InA191107.right (ih k (by omega))
        have he : 3 * (3 * binToTer k + 1) + 1 = 3 * binToTer (2 * k + 1) + 1 := by
          rw [binToTer_bit k 1 (by norm_num)]
        rwa [he] at hmem

/-- Closed form: `A191107(n) = 3 · binToTer (n - 1) + 1`. -/
theorem a191107_eq (n : ℕ) : a191107 n = 3 * binToTer (n - 1) + 1 := by
  have hg : StrictMono (fun m => 3 * binToTer m + 1) := by
    intro a b hab
    have h := binToTer_strictMono hab
    simp only
    omega
  exact nth_eq_of_strictMono hg inA191107_iff (n - 1)

/-! ## A055246 as an affine image -/

/-- The intervals kept after `j` steps have left numerators `2 t` with `t`
ranging over the `2^j` numbers below `3^j` with ternary digits `0, 1`. -/
theorem mem_cantorKept_iff (j c : ℕ) :
    c ∈ cantorKept j ↔ ∃ m < 2 ^ j, 2 * binToTer m = c := by
  induction j generalizing c with
  | zero =>
    simp only [cantorKept, Finset.mem_singleton, pow_zero, Nat.lt_one_iff]
    constructor
    · rintro rfl
      exact ⟨0, rfl, by simp [binToTer_zero]⟩
    · rintro ⟨m, rfl, rfl⟩
      simp [binToTer_zero]
  | succ j ih =>
    simp only [cantorKept, Finset.mem_union, Finset.mem_image, ih]
    have h0 (m : ℕ) : binToTer (2 * m) = 3 * binToTer m := by
      simpa using binToTer_bit m 0 (by norm_num)
    have h1 (m : ℕ) : binToTer (2 * m + 1) = 3 * binToTer m + 1 :=
      binToTer_bit m 1 (by norm_num)
    constructor
    · rintro (⟨c', ⟨m, hm, rfl⟩, rfl⟩ | ⟨c', ⟨m, hm, rfl⟩, rfl⟩)
      · refine ⟨2 * m, by rw [pow_succ]; omega, ?_⟩
        rw [h0]
        ring
      · refine ⟨2 * m + 1, by rw [pow_succ]; omega, ?_⟩
        rw [h1]
        ring
    · rintro ⟨m', hm', rfl⟩
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m'
      · left
        refine ⟨2 * binToTer k, ⟨k, by rw [pow_succ] at hm'; omega, rfl⟩, ?_⟩
        rw [h0]
        ring
      · right
        refine ⟨2 * binToTer k, ⟨k, by rw [pow_succ] at hm'; omega, rfl⟩, ?_⟩
        rw [h1]
        ring

/-- The erased numerators are exactly the numbers `6 t + 1` with `t` having
only ternary digits `0, 1`. -/
theorem isErasedNumerator_iff (x : ℕ) :
    IsErasedNumerator x ↔ ∃ m, 6 * binToTer m + 1 = x := by
  constructor
  · rintro ⟨k, _, hx⟩
    simp only [erasedNumerators, Finset.mem_image, mem_cantorKept_iff] at hx
    obtain ⟨c, ⟨m, _, rfl⟩, rfl⟩ := hx
    exact ⟨m, by ring⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m + 1, by omega, ?_⟩
    simp only [erasedNumerators, Finset.mem_image, mem_cantorKept_iff, add_tsub_cancel_right]
    exact ⟨2 * binToTer m, ⟨m, Nat.lt_two_pow_self, rfl⟩, by ring⟩

/-- Closed form: `A055246(n) = 6 · binToTer (n - 1) + 1`. -/
theorem a055246_eq (n : ℕ) : a055246 n = 6 * binToTer (n - 1) + 1 := by
  have hg : StrictMono (fun m => 6 * binToTer m + 1) := by
    intro a b hab
    have h := binToTer_strictMono hab
    simp only
    omega
  exact nth_eq_of_strictMono hg isErasedNumerator_iff (n - 1)

/-! ## Examples for the `Nat.nth`-defined sequences -/

example : (List.range 16).map (fun i => a191107 (i + 1)) =
    [1, 4, 10, 13, 28, 31, 37, 40, 82, 85, 91, 94, 109, 112, 118, 121] := by
  simp only [a191107_eq]
  decide

example : (List.range 16).map (fun i => a055246 (i + 1)) =
    [1, 7, 19, 25, 55, 61, 73, 79, 163, 169, 181, 187, 217, 223, 235, 241] := by
  simp only [a055246_eq]
  decide

/-! ## The conjecture -/

/-- **Jeffery's conjecture (A003278, L. Edson Jeffery, Nov 26 2015)**, in
multiplicative form: for every `n ≥ 1`,
`3 · a(n) = A191107(n) + 2` and `6 · a(n) = A055246(n) + 5`, where `a` is
Szekeres's sequence A003278.  This is stronger than the division form: it also
gives that `A191107(n) + 2` and `A055246(n) + 5` are divisible by `3` and `6`. -/
theorem jeffery_conjecture (n : ℕ) (_hn : 1 ≤ n) :
    3 * a003278 n = a191107 n + 2 ∧ 6 * a003278 n = a055246 n + 5 := by
  rw [a003278, a191107_eq, a055246_eq]
  constructor <;> ring

/-- **Jeffery's conjecture (A003278, L. Edson Jeffery, Nov 26 2015)**, verbatim
form: "Conjecture: a(n) = (A191107(n) + 2)/3 = (A055246(n) + 5)/6", for every
`n ≥ 1` (the offset of all three entries), with natural-number division that is
exact by `jeffery_conjecture`. -/
theorem jeffery_conjecture_div (n : ℕ) (hn : 1 ≤ n) :
    a003278 n = (a191107 n + 2) / 3 ∧ a003278 n = (a055246 n + 5) / 6 := by
  obtain ⟨h3, h6⟩ := jeffery_conjecture n hn
  constructor
  · rw [← h3]
    omega
  · rw [← h6]
    omega

end Candidates.A003278JefferySzekeres
