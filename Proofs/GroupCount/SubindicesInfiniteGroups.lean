/-
# Subindices and subfactors of infinite groups and numbers — Conjecture II

## Source

arXiv:2604.08724, M. H. Hooshmand et al., *Subindices and subfactors of
infinite groups and numbers*.  Section 3, paragraph "Index stability and
∞-difference length of Fibonacci numbers", bold **Conjecture II** (just after
the theorem that the Fibonacci set is index stable with `|ℤ : {F_n}| = ℵ₀`).
The notions `Dif`, `Dif^n`, `Dif^∞`, `dl^∞` and `⟨A⟩^{(N)}` are defined in
Section 1.

Definitions (verbatim, Section 1): "we also define left and right difference
sets, `Dif_ℓ(A) = A⁻¹A` and `Dif_r(A) = AA⁻¹`. ... we often use `Dif` instead
of `Dif_ℓ`. Denoting the `n`-iteration of `Dif` by `Dif^n` ... `Dif^0(A) := A`.
... For every `A ⊆ G`, either there exists the least non-negative integer `N`
such that `Dif^N(A) = Dif^{N+1}(A)` ... or the sequence `{Dif^n(A)}` is
strictly increasing. In the first case, we define `dl^∞(A) := N` ... also we
put `dl^∞(A) := ∞` for the second case. ... put `A^0 := A ∪ {0}` (additive
notation). By `H = ⟨A⟩^{(N)}` we mean `H = ⟨A⟩` and `dl^∞(A^1) = N`."

Claim (verbatim): "Let `{F_n}_{n=1}^∞` be the Fibonacci sequence (defined by
`F_n = F_{n-1} + F_{n-2}` with `F_1 = F_2 = 1`), and denote by `F` the set of
all Fibonacci numbers. ... **Conjecture II.** The ∞-difference length of
Fibonacci numbers is infinite (i.e., `dl^∞(F) = ∞`), and so
`ℤ = ⟨F⟩^{(∞)}`."

Date recorded: 2026-10-21.

## Status

Stated as an open conjecture in the paper (no proof given there).  This file
proves it.  Proof: reduce modulo `M = F_L`.  The addition formula gives
`F_{n+L} ≡ F_{L+1} F_n (mod F_L)` and Cassini gives `F_{L+1}^2 ≡ ±1`, so
`F_{n+4L} ≡ F_n (mod F_L)` and `F` has at most `4L` residues mod `F_L`.
Hence `Dif^N(F)` has at most `(4L)^{2^N}` residues mod `F_L`, which is fewer
than `F_L` for large `L`, so `Dif^N(F) ≠ ℤ`.  On the other hand, if
`Dif^N(F) = Dif^{N+1}(F)` with `N ≥ 1` then `Dif^N(F)` is a subgroup
containing `1 = 2 - 1`, so it would be `ℤ`.  The case `N = 0` fails since
`0 ∉ F`.
-/
import Mathlib

set_option autoImplicit false

namespace Sorry.GroupCount.SubindicesInfiniteGroups

open Pointwise

/-! ## Definitions -/

/-- `difIter A n` is the paper's `Dif^n(A)` in the additive group `ℤ`:
`Dif^0(A) = A` and `Dif^{n+1}(A) = Dif(Dif^n(A))`, where the (left)
difference set `Dif(B) = B⁻¹B` reads `-B + B = {-a + b : a, b ∈ B}`
additively. -/
def difIter (A : Set ℤ) : ℕ → Set ℤ
  | 0 => A
  | n + 1 => -difIter A n + difIter A n

/-- The paper's `F`: the set of all Fibonacci numbers `{F_n : n ≥ 1}`, with
`F_1 = F_2 = 1`; Mathlib's `Nat.fib` has `fib 0 = 0`, `fib 1 = fib 2 = 1`,
so `F_n = Nat.fib n` and `F = {Nat.fib (n + 1) : n ∈ ℕ}`. -/
def fibSet : Set ℤ := Set.range fun n : ℕ => (Nat.fib (n + 1) : ℤ)

/-- The paper's statement `dl^∞(A) = ∞`: there is no `N` with
`Dif^N(A) = Dif^{N+1}(A)`. -/
def DlInfinite (A : Set ℤ) : Prop := ∀ N : ℕ, difIter A N ≠ difIter A (N + 1)

/-! ## Ground truth -/

example : (1 : ℤ) ∈ fibSet := ⟨0, rfl⟩
example : (2 : ℤ) ∈ fibSet := ⟨2, rfl⟩
example : (3 : ℤ) ∈ fibSet := ⟨3, rfl⟩
example : (5 : ℤ) ∈ fibSet := ⟨4, rfl⟩
example : (8 : ℤ) ∈ fibSet := ⟨5, rfl⟩

example : difIter fibSet 0 = fibSet := rfl

/-- `4 = -1 + 5 ∈ Dif(F)`. -/
example : (4 : ℤ) ∈ difIter fibSet 1 :=
  Set.mem_add.2 ⟨-1, Set.mem_neg.2 (by rw [neg_neg]; exact ⟨0, rfl⟩),
    5, ⟨4, rfl⟩, by norm_num⟩

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

/-- If `Dif^{N+1}(A) = Dif^{N+2}(A)` and `1 ∈ Dif^{N+1}(A)`, then `Dif^{N+1}(A) = ℤ`
(the stable stage is a subgroup containing `1`). -/
theorem difIter_eq_univ_of_eq_succ {A : Set ℤ} {N : ℕ} (hA : A.Nonempty)
    (h : difIter A (N + 1) = difIter A (N + 2)) (h1 : (1 : ℤ) ∈ difIter A (N + 1)) :
    difIter A (N + 1) = Set.univ := by
  set D := difIter A (N + 1) with hD
  have hclos : ∀ a ∈ D, ∀ b ∈ D, -a + b ∈ D := by
    intro a ha b hb
    rw [h]
    exact neg_add_mem_difIter_succ ha hb
  have h0 : (0 : ℤ) ∈ D := zero_mem_difIter_succ (difIter_nonempty hA N)
  have hneg : ∀ a ∈ D, -a ∈ D := fun a ha => by simpa using hclos a ha 0 h0
  have hadd : ∀ a ∈ D, ∀ b ∈ D, a + b ∈ D := fun a ha b hb => by
    simpa using hclos (-a) (hneg a ha) b hb
  refine Set.eq_univ_of_forall fun z => ?_
  induction z using Int.induction_on with
  | zero => exact h0
  | succ k hk => exact hadd _ hk 1 h1
  | pred k hk => simpa [sub_eq_add_neg] using hadd _ hk (-1) (hneg 1 h1)

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

/-- **Modular obstruction.** If `A` reduces modulo `M > 0` into a set `S` with
`|S|^{2^N} < M`, then `Dif^N(A) ≠ ℤ`. -/
theorem difIter_ne_univ_of_card_lt {M : ℕ} [NeZero M] (A : Set ℤ) (S : Finset (ZMod M))
    (hS : ∀ a ∈ A, (a : ZMod M) ∈ S) (N : ℕ) (hlt : S.card ^ 2 ^ N < M) :
    difIter A N ≠ Set.univ := by
  intro huniv
  obtain ⟨T, hTcard, hT⟩ := exists_finset_difIter_cast A S hS N
  have hsub : (Finset.univ : Finset (ZMod M)) ⊆ T := by
    intro r _
    have hr := hT ((r.val : ℕ) : ℤ) (by rw [huniv]; trivial)
    simpa using hr
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at hcard
  omega

/-! ## Fibonacci numbers modulo a Fibonacci number -/

/-- Addition formula mod `F_L`: `F_{n+L} ≡ F_{L+1} F_n (mod F_L)`. -/
theorem fib_add_cast (L n : ℕ) :
    ((Nat.fib (n + L) : ℕ) : ZMod (Nat.fib L)) =
      (Nat.fib (L + 1) : ZMod (Nat.fib L)) * Nat.fib n := by
  rcases n with _ | k
  · simp
  · rw [show k + 1 + L = L + k + 1 by ring, Nat.fib_add]
    push_cast
    rw [ZMod.natCast_self]
    ring

/-- Cassini mod `F_{l+1}`: `F_{l+2}^2 ≡ (-1)^{l+1} (mod F_{l+1})`. -/
theorem fib_cassini_cast (l : ℕ) :
    ((Nat.fib (l + 2) : ZMod (Nat.fib (l + 1)))) ^ 2 = (-1) ^ (l + 1) := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq ((l + 1 : ℕ) : ℤ)
  have e1 : ((l + 1 : ℕ) : ℤ) + 1 = ((l + 2 : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((l + 1 : ℕ) : ℤ) - 1 = ((l : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, Int.fib_natCast, Int.fib_natCast, Int.fib_natCast, Int.natAbs_natCast] at h
  have h' := congrArg (fun z : ℤ => (z : ZMod (Nat.fib (l + 1)))) h
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_neg,
    Int.cast_one, ZMod.natCast_self] at h'
  have hfib : ((Nat.fib (l + 2) : ℕ) : ZMod (Nat.fib (l + 1))) = Nat.fib l := by
    rw [Nat.fib_add_two]; push_cast; rw [ZMod.natCast_self]; ring
  rw [← h', pow_two]
  nth_rewrite 2 [hfib]
  ring

/-- Periodicity mod `F_L` (`L ≥ 1`): `F_{n+4L} ≡ F_n (mod F_L)`. -/
theorem fib_add_four_mul_cast (l n : ℕ) :
    ((Nat.fib (n + 4 * (l + 1)) : ℕ) : ZMod (Nat.fib (l + 1))) = Nat.fib n := by
  set L := l + 1 with hL
  have hshift : ∀ m : ℕ, ((Nat.fib (m + L) : ℕ) : ZMod (Nat.fib L)) =
      (Nat.fib (l + 2) : ZMod (Nat.fib L)) * Nat.fib m := fun m => fib_add_cast L m
  have hx4 : (Nat.fib (l + 2) : ZMod (Nat.fib L)) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, fib_cassini_cast, ← pow_mul, mul_comm,
      pow_mul, neg_one_sq, one_pow]
  rw [show n + 4 * L = n + L + L + L + L by ring, hshift, hshift, hshift, hshift]
  linear_combination (Nat.fib n : ZMod (Nat.fib L)) * hx4

/-- Every Fibonacci number is congruent mod `F_L` (`L ≥ 1`) to some `F_i` with `i < 4L`. -/
theorem exists_lt_fib_cast_eq (l j : ℕ) :
    ∃ i < 4 * (l + 1), ((Nat.fib j : ℕ) : ZMod (Nat.fib (l + 1))) = Nat.fib i := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < 4 * (l + 1)
    · exact ⟨j, hj, rfl⟩
    · obtain ⟨i, hi, heq⟩ := ih (j - 4 * (l + 1)) (by omega)
      refine ⟨i, hi, ?_⟩
      rw [← heq, ← fib_add_four_mul_cast l (j - 4 * (l + 1)), Nat.sub_add_cancel (by omega)]

/-- `2^m ≤ F_{2m+1}`. -/
theorem two_pow_le_fib (m : ℕ) : 2 ^ m ≤ Nat.fib (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmono : Nat.fib (2 * m + 1) ≤ Nat.fib (2 * m + 2) := Nat.fib_mono (by omega)
    have hrec : Nat.fib (2 * (m + 1) + 1) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := by
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, Nat.fib_add_two]
    rw [hrec, pow_succ]
    omega

/-- For each `N` there is a Fibonacci modulus `F_L` (`L = l + 1`) exceeding `(4L)^{2^N}`. -/
theorem exists_pow_lt_fib (N : ℕ) : ∃ l : ℕ, (4 * (l + 1)) ^ 2 ^ N < Nat.fib (l + 1) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 2 * N + 8 := ⟨_, rfl⟩
  refine ⟨2 * 2 ^ t, ?_⟩
  have hN : N < 2 ^ N := Nat.lt_two_pow_self
  have h4L : 4 * (2 * 2 ^ t + 1) ≤ 2 ^ (t + 4) := by
    have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    have h16 : 2 ^ (t + 4) = 2 ^ t * 16 := by rw [pow_add]; norm_num
    omega
  have hexp : (t + 4) * 2 ^ N < 2 ^ t := by
    have h2 : 2 ^ t = 2 ^ N * 2 ^ (N + 8) := by rw [ht, ← pow_add]; congr 1; ring
    have h3 : 2 ^ (N + 8) = 2 ^ N * 256 := by rw [pow_add]; norm_num
    rw [h2, h3, ht]
    nlinarith
  calc (4 * (2 * 2 ^ t + 1)) ^ 2 ^ N ≤ (2 ^ (t + 4)) ^ 2 ^ N := Nat.pow_le_pow_left h4L _
    _ = 2 ^ ((t + 4) * 2 ^ N) := by rw [← pow_mul]
    _ < 2 ^ 2 ^ t := Nat.pow_lt_pow_right (by norm_num) hexp
    _ ≤ Nat.fib (2 * 2 ^ t + 1) := two_pow_le_fib _

/-! ## The Fibonacci set -/

/-- `Dif^N(F) ≠ ℤ` for every `N`. -/
theorem difIter_fibSet_ne_univ (N : ℕ) : difIter fibSet N ≠ Set.univ := by
  obtain ⟨l, hl⟩ := exists_pow_lt_fib N
  haveI : NeZero (Nat.fib (l + 1)) := ⟨(Nat.fib_pos.2 (Nat.succ_pos l)).ne'⟩
  let S : Finset (ZMod (Nat.fib (l + 1))) :=
    (Finset.range (4 * (l + 1))).image fun i => (Nat.fib i : ZMod (Nat.fib (l + 1)))
  have hS : ∀ a ∈ fibSet, (a : ZMod (Nat.fib (l + 1))) ∈ S := by
    rintro a ⟨j, rfl⟩
    obtain ⟨i, hi, heq⟩ := exists_lt_fib_cast_eq l (j + 1)
    rw [Int.cast_natCast, heq]
    exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  have hcard : S.card ≤ 4 * (l + 1) := Finset.card_image_le.trans (by simp)
  exact difIter_ne_univ_of_card_lt fibSet S hS N
    (lt_of_le_of_lt (Nat.pow_le_pow_left hcard _) hl)

/-- `0 ∉ F`. -/
theorem zero_not_mem_fibSet : (0 : ℤ) ∉ fibSet := by
  rintro ⟨n, hn⟩
  have hn' : (Nat.fib (n + 1) : ℤ) = 0 := hn
  have hpos : 0 < Nat.fib (n + 1) := Nat.fib_pos.2 (by omega)
  omega

/-- `F` is nonempty. -/
theorem fibSet_nonempty : fibSet.Nonempty := ⟨1, 0, rfl⟩

/-- `1 = -1 + 2 ∈ Dif(F)`. -/
theorem one_mem_difIter_fibSet_one : (1 : ℤ) ∈ difIter fibSet 1 := by
  have h := neg_add_mem_difIter_succ (A := fibSet) (n := 0) (a := 1) (b := 2) ⟨0, rfl⟩ ⟨2, rfl⟩
  simpa using h

/-- **Conjecture II (first part), arXiv:2604.08724.** The ∞-difference length of the set
of Fibonacci numbers is infinite: `dl^∞(F) = ∞`, i.e. `Dif^N(F) ≠ Dif^{N+1}(F)` for every
`N`. -/
theorem conjecture_II : DlInfinite fibSet := by
  intro N h
  rcases N with _ | N
  · apply zero_not_mem_fibSet
    have h0 : (0 : ℤ) ∈ difIter fibSet 1 := zero_mem_difIter_succ fibSet_nonempty
    rw [← h] at h0
    exact h0
  · have h1 : (1 : ℤ) ∈ difIter fibSet (N + 1) :=
      difIter_mono fibSet_nonempty le_rfl (by omega) one_mem_difIter_fibSet_one
    exact difIter_fibSet_ne_univ (N + 1) (difIter_eq_univ_of_eq_succ fibSet_nonempty h h1)

/-! ## The second part: `ℤ = ⟨F⟩^{(∞)}` -/

/-- Each stage `Dif^{n+1}(A)` is symmetric. -/
theorem neg_mem_difIter_succ {A : Set ℤ} {n : ℕ} {x : ℤ} (hx : x ∈ difIter A (n + 1)) :
    -x ∈ difIter A (n + 1) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_difIter_succ.1 hx
  simpa [add_comm] using neg_add_mem_difIter_succ hb ha

/-- `F ⊆ Dif(F)`: `F_1 = -F_1 + F_3` and `F_{k+2} = -F_{k+1} + F_{k+3}`. -/
theorem fibSet_subset_difIter_one : fibSet ⊆ difIter fibSet 1 := by
  rintro _ ⟨n, rfl⟩
  rcases n with _ | k
  · exact one_mem_difIter_fibSet_one
  · have h := neg_add_mem_difIter_succ (A := fibSet) (n := 0)
      (a := (Nat.fib (k + 1) : ℤ)) (b := (Nat.fib (k + 3) : ℤ)) ⟨k, rfl⟩ ⟨k + 2, rfl⟩
    have hrec : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      rw [show k + 3 = k + 1 + 2 by ring, Nat.fib_add_two]; push_cast; ring
    rw [hrec, neg_add_cancel_left] at h
    exact h

/-- Adjoining `0` does not change `Dif^{n+1}`: `Dif^{n+1}(F ∪ {0}) = Dif^{n+1}(F)`. -/
theorem difIter_insert_zero_fibSet_succ (n : ℕ) :
    difIter (insert 0 fibSet) (n + 1) = difIter fibSet (n + 1) := by
  induction n with
  | zero =>
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_difIter_succ.1 hx
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · simpa using zero_mem_difIter_succ (A := fibSet) (n := 0) fibSet_nonempty
      · simpa using fibSet_subset_difIter_one hb
      · simpa using neg_mem_difIter_succ (fibSet_subset_difIter_one ha)
      · exact neg_add_mem_difIter_succ ha hb
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_difIter_succ.1 hx
      exact neg_add_mem_difIter_succ (Set.mem_insert_of_mem 0 ha) (Set.mem_insert_of_mem 0 hb)
  | succ n ih =>
    change -difIter (insert 0 fibSet) (n + 1) + difIter (insert 0 fibSet) (n + 1) =
      -difIter fibSet (n + 1) + difIter fibSet (n + 1)
    rw [ih]

/-- `dl^∞(F^0) = ∞` where `F^0 = F ∪ {0}`. -/
theorem dlInfinite_insert_zero_fibSet : DlInfinite (insert 0 fibSet) := by
  intro N h
  rcases N with _ | N
  · have hm1 : (-1 : ℤ) ∈ difIter (insert 0 fibSet) 1 := by
      rw [difIter_insert_zero_fibSet_succ]
      exact neg_mem_difIter_succ one_mem_difIter_fibSet_one
    rw [← h] at hm1
    rcases hm1 with hm1 | ⟨n, hn⟩
    · norm_num at hm1
    · have hn' : (Nat.fib (n + 1) : ℤ) = -1 := hn
      omega
  · rw [difIter_insert_zero_fibSet_succ, difIter_insert_zero_fibSet_succ] at h
    exact conjecture_II (N + 1) h

/-- `F` generates `ℤ`: `⟨F⟩ = ℤ` (since `1 ∈ F`). -/
theorem closure_fibSet : AddSubgroup.closure fibSet = ⊤ := by
  rw [eq_top_iff]
  intro z _
  have h1 : (1 : ℤ) ∈ AddSubgroup.closure fibSet := AddSubgroup.subset_closure ⟨0, rfl⟩
  simpa using AddSubgroup.zsmul_mem _ h1 z

/-- `Dif^∞(F) = ⋃_{n ≥ 1} Dif^n(F) = ℤ`; more precisely `±k ∈ Dif^{k+1}(F)`. -/
theorem iUnion_difIter_fibSet : (⋃ n : ℕ, difIter fibSet (n + 1)) = Set.univ := by
  have hm1 : ∀ m : ℕ, (-1 : ℤ) ∈ difIter fibSet (m + 1) ∧ (1 : ℤ) ∈ difIter fibSet (m + 1) :=
    fun m => ⟨difIter_mono fibSet_nonempty le_rfl (by omega)
        (neg_mem_difIter_succ one_mem_difIter_fibSet_one),
      difIter_mono fibSet_nonempty le_rfl (by omega) one_mem_difIter_fibSet_one⟩
  have key : ∀ k : ℕ, (k : ℤ) ∈ difIter fibSet (k + 1) ∧ -(k : ℤ) ∈ difIter fibSet (k + 1) := by
    intro k
    induction k with
    | zero => simpa using zero_mem_difIter_succ (A := fibSet) (n := 0) fibSet_nonempty
    | succ k ih =>
      constructor
      · simpa [add_comm] using neg_add_mem_difIter_succ (hm1 k).1 ih.1
      · have h := neg_add_mem_difIter_succ (hm1 k).2 ih.2
        rw [show -(1 : ℤ) + -(k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring] at h
        exact h
  refine Set.eq_univ_of_forall fun z => Set.mem_iUnion.2 ?_
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · exact ⟨k, (key k).1⟩
  · exact ⟨k, (key k).2⟩

/-- **Conjecture II, arXiv:2604.08724 (Hooshmand et al.), full statement.**
"The ∞-difference length of Fibonacci numbers is infinite (i.e., `dl^∞(F) = ∞`), and so
`ℤ = ⟨F⟩^{(∞)}`."  Here `ℤ = ⟨F⟩^{(∞)}` means `ℤ = ⟨F⟩` and `dl^∞(F ∪ {0}) = ∞`; we also
record `Dif^∞(F) = ⋃_{n ≥ 1} Dif^n(F) = ℤ`. -/
theorem conjecture_II_full :
    DlInfinite fibSet ∧ AddSubgroup.closure fibSet = ⊤ ∧ DlInfinite (insert 0 fibSet) ∧
      (⋃ n : ℕ, difIter fibSet (n + 1)) = Set.univ :=
  ⟨conjecture_II, closure_fibSet, dlInfinite_insert_zero_fibSet, iUnion_difIter_fibSet⟩

/-! ## Non-vacuity of `DlInfinite`

The paper's example `ℤ = ⟨ℕ⟩^{(1)}`: for `ℕ ∪ {0} ⊆ ℤ` the length is finite, so
`DlInfinite` is not a trivially true predicate. -/

/-- `Dif(ℕ) = ℤ` for `ℕ = {0, 1, 2, …} ⊆ ℤ`, hence `dl^∞(ℕ) ≠ ∞`. -/
example : ¬ DlInfinite (Set.range ((↑) : ℕ → ℤ)) := by
  have h1 : difIter (Set.range ((↑) : ℕ → ℤ)) 1 = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg z
    · simpa using neg_add_mem_difIter_succ (A := Set.range ((↑) : ℕ → ℤ)) (n := 0)
        ⟨0, rfl⟩ ⟨k, rfl⟩
    · simpa using neg_add_mem_difIter_succ (A := Set.range ((↑) : ℕ → ℤ)) (n := 0)
        ⟨k, rfl⟩ ⟨0, rfl⟩
  intro h
  apply h 1
  rw [h1]
  refine (Set.eq_univ_of_forall fun z => ?_).symm
  have hz := neg_add_mem_difIter_succ (A := Set.range ((↑) : ℕ → ℤ)) (n := 1)
    (h1 ▸ Set.mem_univ 0) (h1 ▸ Set.mem_univ z)
  rwa [neg_zero, zero_add] at hz

end Sorry.GroupCount.SubindicesInfiniteGroups
