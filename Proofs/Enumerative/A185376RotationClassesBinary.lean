/-
# A185376: binary necklaces with a palindromic cut

OEIS A185376, with A185333; the conjecture comment is unattributed.
For `n > 0`, the number of rotation classes of binary words of length `2n`
with a palindromic representative is
`2^(n-1) + 2^((n-2^t)/2^(t+1))`, where `t` is the exponent of `2` in `n`.
Writing `n = 2^t m` with odd `m`, double counting palindromes by necklace
reduces the count to the `m`-periodic palindromes. The positive-length
restriction excludes the different `ZMod 0 = ℤ` model.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A185376RotationClassesBinary

/-! ## Definitions

A binary word of length `N` is a function `ZMod N → Bool` (letter `i` at position `i`).
Cutting a necklace at position `k` reads the word `rotate k w`.  A necklace is a rotation
class of words, and it has a palindromic cut when some representative is a palindrome. -/

/-- Rotation of a binary word of length `N` (indexed by `ZMod N`) by `k` places:
the word read starting at position `k`. -/
def rotate {N : ℕ} (k : ZMod N) (w : ZMod N → Bool) : ZMod N → Bool :=
  fun i => w (i + k)

/-- A word `w₀ w₁ … w_{N-1}` is a palindrome: `w_{N-1-i} = w_i` for every `i`. -/
def IsPalindrome {N : ℕ} (w : ZMod N → Bool) : Prop :=
  ∀ i : ZMod N, w (-1 - i) = w i

/-- Rotating by `b` and then by `a` is rotating by `a + b`. -/
theorem rotate_rotate {N : ℕ} (a b : ZMod N) (w : ZMod N → Bool) :
    rotate a (rotate b w) = rotate (a + b) w := by
  funext i
  simp only [rotate, add_assoc]

/-- Rotation by `0` is the identity. -/
theorem rotate_zero {N : ℕ} (w : ZMod N → Bool) : rotate 0 w = w := by
  funext i
  simp only [rotate, add_zero]

/-- Two words are equivalent when one is a rotation of the other. -/
def rotSetoid (N : ℕ) : Setoid (ZMod N → Bool) where
  r w v := ∃ k : ZMod N, rotate k w = v
  iseqv := by
    refine ⟨fun w => ⟨0, rotate_zero w⟩, ?_, ?_⟩
    · rintro w v ⟨k, rfl⟩
      exact ⟨-k, by rw [rotate_rotate, neg_add_cancel, rotate_zero]⟩
    · rintro w v u ⟨k, rfl⟩ ⟨l, rfl⟩
      exact ⟨l + k, by rw [rotate_rotate]⟩

/-- The binary necklaces of length `N`: binary words up to rotation. -/
abbrev Necklace (N : ℕ) := Quotient (rotSetoid N)

/-- A necklace has a palindromic cut: some cut of it (some representative word) reads
as a palindrome. -/
def HasPalindromicCut {N : ℕ} (c : Necklace N) : Prop :=
  ∃ w : ZMod N → Bool, IsPalindrome w ∧ Quotient.mk (rotSetoid N) w = c

/-! ## Proofs -/

/-- The periods of a word `w`: the rotations fixing `w`, an additive subgroup of `ZMod N`. -/
def periods {N : ℕ} (w : ZMod N → Bool) : AddSubgroup (ZMod N) where
  carrier := {p | rotate p w = w}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [← rotate_rotate, hb, ha]
  zero_mem' := rotate_zero w
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [rotate_rotate, neg_add_cancel, rotate_zero]

/-- Membership in `periods w` unfolds to invariance of `w` under that rotation. -/
theorem mem_periods {N : ℕ} (w : ZMod N → Bool) (p : ZMod N) :
    p ∈ periods w ↔ rotate p w = w := Iff.rfl

/-- For a palindrome `v`, the rotation of `v` by `k` is again a palindrome iff `2k` is a
period of `v`. -/
theorem isPalindrome_rotate_iff {N : ℕ} {v : ZMod N → Bool} (hv : IsPalindrome v)
    (k : ZMod N) : IsPalindrome (rotate k v) ↔ k + k ∈ periods v := by
  rw [mem_periods]
  constructor
  · intro h
    funext j
    have h1 := h (j + k)
    have h2 := hv j
    simp only [rotate] at h1 ⊢
    rw [show -1 - (j + k) + k = -1 - j by ring, h2] at h1
    rw [← add_assoc]
    exact h1.symm
  · intro h i
    have h1 := congrFun h (i - k)
    have h2 := hv (-1 - i + k)
    simp only [rotate] at h1 ⊢
    rw [← h2]
    rw [show -1 - (-1 - i + k) = i - k by ring]
    rw [← h1]
    congr 1
    ring

/-- If `m` is odd and `m ∈ H`, then `k + k ∈ H` implies `k ∈ H`. -/
theorem mem_of_add_self_mem_of_odd {N : ℕ} [NeZero N] (H : AddSubgroup (ZMod N)) {m : ℕ}
    (hm : Odd m) (hmH : (m : ZMod N) ∈ H) {k : ZMod N} (hk : k + k ∈ H) : k ∈ H := by
  obtain ⟨r, rfl⟩ := hm
  have h1 : k.val • ((2 * r + 1 : ℕ) : ZMod N) ∈ H := AddSubgroup.nsmul_mem H hmH _
  have h2 : r • (k + k) ∈ H := AddSubgroup.nsmul_mem H hk _
  have hk' : k = k.val • ((2 * r + 1 : ℕ) : ZMod N) - r • (k + k) := by
    rw [nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    push_cast
    ring
  rw [hk']
  exact H.sub_mem h1 h2

/-- If a subgroup `H` of `ZMod N` is closed under halving (`k + k ∈ H → k ∈ H`), then
`2 ^ j * m ∈ H` forces `m ∈ H`. -/
theorem mem_of_halving_closed {N : ℕ} (H : AddSubgroup (ZMod N))
    (hH : ∀ k : ZMod N, k + k ∈ H → k ∈ H) (m : ℕ) :
    ∀ j : ℕ, ((2 ^ j * m : ℕ) : ZMod N) ∈ H → (m : ZMod N) ∈ H := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    apply ih
    apply hH
    have : ((2 ^ (j + 1) * m : ℕ) : ZMod N) = ((2 ^ j * m : ℕ) : ZMod N) + ((2 ^ j * m : ℕ) : ZMod N) := by
      push_cast; ring
    rw [← this]
    exact hj

open Classical in
/-- **Load-bearing bound.** A palindrome `v` has at most two palindromic rotations: they are
indexed by the elements `x` of the cyclic group `ZMod N ⧸ periods v` with `2 • x = 0`, and a
cyclic group has at most two such elements. -/
theorem card_fiber_le_two {N : ℕ} [NeZero N] {v : ZMod N → Bool} (hv : IsPalindrome v) :
    (Finset.univ.filter (fun u => IsPalindrome u ∧ ∃ k, rotate k v = u)).card ≤ 2 := by
  set H := periods v with hH
  haveI : IsAddCyclic (ZMod N ⧸ H) :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' H) (QuotientAddGroup.mk'_surjective H)
  let g : ZMod N ⧸ H → (ZMod N → Bool) := fun x =>
    Quotient.liftOn' x (fun k => rotate k v) (by
      intro a b hab
      rw [QuotientAddGroup.leftRel_apply] at hab
      have hb : b = a + (-a + b) := by abel
      show rotate a v = rotate b v
      rw [hb, ← rotate_rotate, (mem_periods v _).1 hab])
  have hS := IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod N ⧸ H) (n := 2) (by norm_num)
  refine le_trans ?_ hS
  refine le_trans (Finset.card_le_card (t := (Finset.univ.filter
    (fun x : ZMod N ⧸ H => 2 • x = 0)).image g) ?_) Finset.card_image_le
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨hpal, k, rfl⟩ := hu
  rw [Finset.mem_image]
  refine ⟨(k : ZMod N ⧸ H), ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, two_nsmul]
  exact (isPalindrome_rotate_iff hv k).1 hpal

/-- Fold an index `r < M` onto the first half `[0, (M+1)/2)` using `r ↦ M - 1 - r`. -/
def fold (M r : ℕ) : ℕ := if r < (M + 1) / 2 then r else M - 1 - r

/-- `fold M` lands in the first half. -/
theorem fold_lt {M r : ℕ} (hr : r < M) : fold M r < (M + 1) / 2 := by
  unfold fold; split_ifs <;> omega

/-- `fold M` identifies `r` with its mirror index `M - 1 - r`. -/
theorem fold_reflect {M r : ℕ} (hr : r < M) : fold M (M - 1 - r) = fold M r := by
  unfold fold; split_ifs <;> omega

/-- `fold M` fixes the first half. -/
theorem fold_of_lt {M r : ℕ} (hr : r < (M + 1) / 2) : fold M r = r := by
  unfold fold; rw [if_pos hr]

/-- Adding `M` does not change the residue mod `M` of a `ZMod N` value when `M ∣ N`. -/
theorem val_add_natCast_mod {N M : ℕ} [NeZero N] (hMN : M ∣ N) (x : ZMod N) :
    (x + (M : ZMod N)).val % M = x.val % M := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hMN, Nat.add_mod,
    Nat.mod_mod_of_dvd _ hMN, Nat.mod_self, add_zero, Nat.mod_mod]

/-- The mirror index `-1 - x` in `ZMod N` is the cast of `N - 1 - x.val`. -/
theorem neg_one_sub_eq_natCast {N : ℕ} [NeZero N] (x : ZMod N) :
    -1 - x = ((N - 1 - x.val : ℕ) : ZMod N) := by
  have hx := ZMod.val_lt x
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self,
    ZMod.natCast_zmod_val]
  push_cast
  ring

/-- Residue mod `M` of the mirror index, for `M ∣ N`. -/
theorem val_neg_one_sub_mod {N M : ℕ} [NeZero N] (hM : 0 < M) (hMN : M ∣ N) (x : ZMod N) :
    (-1 - x).val % M = M - 1 - x.val % M := by
  have hx := ZMod.val_lt x
  rw [neg_one_sub_eq_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (a := N - 1 - x.val) (b := N) (by omega)]
  obtain ⟨c, hc⟩ := hMN
  set r := x.val % M with hr
  set q := x.val / M with hq
  have hdiv : M * q + r = x.val := Nat.div_add_mod x.val M
  have hrM : r < M := Nat.mod_lt _ hM
  have hqc : q < c := by
    by_contra hcq
    replace hcq := not_lt.mp hcq
    have : M * c ≤ M * q := Nat.mul_le_mul_left M hcq
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hqc
  have hN : N = M * q + M + M * d := by rw [hc, hd]; ring
  have : N - 1 - x.val = (M - 1 - r) + M * d := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Small naturals cast into `ZMod N` and read back mod `M ∣ N` unchanged. -/
theorem natCast_val_lt {N M i : ℕ} [NeZero N] (hMN : M ∣ N) (hi : i < M) :
    ((i : ZMod N)).val % M = i := by
  have hMle : M ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hMN
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show i < N by omega), Nat.mod_eq_of_lt hi]

/-- An `M`-periodic word is invariant under translation by any multiple of `M`. -/
theorem apply_add_mul_of_mem_periods {N M : ℕ} {w : ZMod N → Bool}
    (hw : (M : ZMod N) ∈ periods w) (y : ZMod N) (j : ℕ) :
    w (y + ((j * M : ℕ) : ZMod N)) = w y := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := congrFun ((mem_periods w _).1 hw) (y + ((j * M : ℕ) : ZMod N))
    simp only [rotate] at h1
    rw [← ih, ← h1]
    congr 1
    push_cast
    ring

/-- The `M`-periodic palindromes of length `N` (`M ∣ N`) are determined by their first
`(M + 1) / 2` letters. -/
def periodicPalEquiv {N M : ℕ} [NeZero N] (hM : 0 < M) (hMN : M ∣ N) :
    {w : ZMod N → Bool // IsPalindrome w ∧ (M : ZMod N) ∈ periods w} ≃
      (Fin ((M + 1) / 2) → Bool) where
  toFun w := fun i => w.1 ((i : ℕ) : ZMod N)
  invFun f := ⟨fun x => f ⟨fold M (x.val % M), fold_lt (Nat.mod_lt _ hM)⟩, by
    constructor
    · intro x
      simp only [val_neg_one_sub_mod hM hMN, fold_reflect (Nat.mod_lt _ hM)]
    · rw [mem_periods]
      funext x
      simp only [rotate, val_add_natCast_mod hMN]⟩
  left_inv w := by
    obtain ⟨w, hpal, hper⟩ := w
    apply Subtype.ext
    funext x
    simp only
    have hx : x = ((x.val % M : ℕ) : ZMod N) + (((x.val / M) * M : ℕ) : ZMod N) := by
      rw [← Nat.cast_add, mul_comm, Nat.mod_add_div, ZMod.natCast_zmod_val]
    have hr : x.val % M < M := Nat.mod_lt _ hM
    conv_rhs => rw [hx, apply_add_mul_of_mem_periods hper]
    unfold fold
    split_ifs with h
    · rfl
    · have hcast : ((M - 1 - x.val % M : ℕ) : ZMod N) =
          (-1 - ((x.val % M : ℕ) : ZMod N)) + (M : ZMod N) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      have hrot := congrFun ((mem_periods w _).1 hper) (-1 - ((x.val % M : ℕ) : ZMod N))
      simp only [rotate] at hrot
      rw [hcast, hrot, hpal]
  right_inv f := by
    funext i
    simp only
    congr 1
    apply Fin.ext
    simp only
    rw [natCast_val_lt hMN (by omega), fold_of_lt i.2]

open Classical in
/-- There are `2 ^ ((M + 1) / 2)` palindromes of length `N` with period `M`, for `M ∣ N`. -/
theorem card_periodic_pal {N M : ℕ} [NeZero N] (hM : 0 < M) (hMN : M ∣ N) :
    (Finset.univ.filter (fun w : ZMod N → Bool =>
      IsPalindrome w ∧ (M : ZMod N) ∈ periods w)).card = 2 ^ ((M + 1) / 2) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (periodicPalEquiv hM hMN)]
  simp

/-- Periods are invariant under rotation. -/
theorem mem_periods_rotate {N : ℕ} {u : ZMod N → Bool} {p : ZMod N} (hp : p ∈ periods u)
    (k : ZMod N) : p ∈ periods (rotate k u) := by
  rw [mem_periods] at hp ⊢
  rw [rotate_rotate, add_comm, ← rotate_rotate, hp]

/-- `2 ^ (t + 1) * m` vanishes in `ZMod (2 ^ (t + 1) * m)`. -/
theorem natCast_two_pow_mul_eq_zero {N t m : ℕ} (hN : N = 2 ^ (t + 1) * m) :
    ((2 ^ (t + 1) * m : ℕ) : ZMod N) = 0 := by
  rw [← hN, ZMod.natCast_self]

open Classical in
/-- For `N = 2 ^ (t + 1) * m` with `m` odd, a palindrome `v` has exactly one palindromic
rotation (itself) if `m` is a period of `v`, and exactly two otherwise. -/
theorem card_fiber_eq {N t m : ℕ} [NeZero N] (hN : N = 2 ^ (t + 1) * m) (hm : Odd m)
    {v : ZMod N → Bool} (hv : IsPalindrome v) :
    (Finset.univ.filter (fun u => IsPalindrome u ∧ ∃ k, rotate k v = u)).card =
      if (m : ZMod N) ∈ periods v then 1 else 2 := by
  split_ifs with hQ
  · rw [Finset.card_eq_one]
    refine ⟨v, ?_⟩
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hpal, k, rfl⟩
      have hk : k ∈ periods v :=
        mem_of_add_self_mem_of_odd _ hm hQ ((isPalindrome_rotate_iff hv k).1 hpal)
      exact (mem_periods v k).1 hk
    · rintro rfl
      exact ⟨hv, 0, rotate_zero _⟩
  · refine le_antisymm (card_fiber_le_two hv) ?_
    have hex : ∃ k : ZMod N, k + k ∈ periods v ∧ k ∉ periods v := by
      by_contra hcon
      push Not at hcon
      apply hQ
      exact mem_of_halving_closed _ hcon m (t + 1) (by
        rw [natCast_two_pow_mul_eq_zero hN]; exact (periods v).zero_mem)
    obtain ⟨k, hkk, hk⟩ := hex
    rw [Nat.succ_le_iff, Finset.one_lt_card]
    refine ⟨v, ?_, rotate k v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hv, 0, rotate_zero v⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(isPalindrome_rotate_iff hv k).2 hkk, k, rfl⟩
    · intro hvk
      exact hk ((mem_periods v k).2 hvk.symm)

/-- Two words give the same necklace iff one is a rotation of the other. -/
theorem mk_eq_mk_iff {N : ℕ} (u v : ZMod N → Bool) :
    Quotient.mk (rotSetoid N) u = Quotient.mk (rotSetoid N) v ↔ ∃ k, rotate k u = v :=
  Quotient.eq

open Classical in
/-- The number of necklaces with a palindromic cut equals the number of necklaces of
palindromes. -/
theorem card_hasPalindromicCut_eq_card_image {N : ℕ} [NeZero N] :
    Nat.card {c : Necklace N // HasPalindromicCut c} =
      ((Finset.univ.filter (fun w : ZMod N → Bool => IsPalindrome w)).image
        (Quotient.mk (rotSetoid N))).card := by
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro c
  simp only [HasPalindromicCut, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
/-- Double count of palindromes by necklace, for `N = 2 ^ (t + 1) * m` with `m` odd:
`#palindromes + #(m-periodic palindromes) = 2 * #(necklaces with a palindromic cut)`. -/
theorem card_pal_add_card_palQ {N t m : ℕ} [NeZero N] (hN : N = 2 ^ (t + 1) * m)
    (hm : Odd m) :
    (Finset.univ.filter (fun w : ZMod N → Bool => IsPalindrome w)).card +
      (Finset.univ.filter (fun w : ZMod N → Bool =>
        IsPalindrome w ∧ (m : ZMod N) ∈ periods w)).card =
    2 * ((Finset.univ.filter (fun w : ZMod N → Bool => IsPalindrome w)).image
        (Quotient.mk (rotSetoid N))).card := by
  set Pal := Finset.univ.filter (fun w : ZMod N → Bool => IsPalindrome w) with hPal
  set PalQ := Finset.univ.filter (fun w : ZMod N → Bool =>
        IsPalindrome w ∧ (m : ZMod N) ∈ periods w) with hPalQ
  set mk := Quotient.mk (rotSetoid N) with hmk
  set A := Pal.image mk with hA
  set B := PalQ.image mk with hB
  have hBcard : B.card = PalQ.card := by
    apply Finset.card_image_of_injOn
    intro u hu u' hu' huu'
    simp only [hPalQ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hu'
    obtain ⟨k, rfl⟩ := (mk_eq_mk_iff u u').1 huu'
    have hk : k ∈ periods u :=
      mem_of_add_self_mem_of_odd _ hm hu.2 ((isPalindrome_rotate_iff hu.1 k).1 hu'.1)
    exact ((mem_periods u k).1 hk).symm
  have hBA : B ⊆ A := by
    intro c hc
    simp only [hB, hA, Finset.mem_image, hPalQ, hPal, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc ⊢
    obtain ⟨u, hu, rfl⟩ := hc
    exact ⟨u, hu.1, rfl⟩
  have hfib : ∀ c ∈ A, (Pal.filter (fun u => mk u = c)).card = if c ∈ B then 1 else 2 := by
    intro c hc
    simp only [hA, Finset.mem_image, hPal, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨v, hv, rfl⟩ := hc
    have hset : Pal.filter (fun u => mk u = mk v) =
        Finset.univ.filter (fun u => IsPalindrome u ∧ ∃ k, rotate k v = u) := by
      ext u
      simp only [hPal, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [eq_comm, hmk, mk_eq_mk_iff]
    have hiff : mk v ∈ B ↔ (m : ZMod N) ∈ periods v := by
      simp only [hB, Finset.mem_image, hPalQ, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨u, hu, huv⟩
        obtain ⟨k, rfl⟩ := (mk_eq_mk_iff u v).1 huv
        exact mem_periods_rotate hu.2 k
      · intro hQ
        exact ⟨v, ⟨hv, hQ⟩, rfl⟩
    rw [hset, card_fiber_eq hN hm hv]
    exact if_congr hiff.symm rfl rfl
  rw [Finset.card_eq_sum_card_image mk Pal, Finset.sum_congr rfl hfib, ← hBcard]
  have hsumB : ∑ c ∈ A, (if c ∈ B then 1 else 0) = B.card := by
    rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 hBA]
  rw [← hsumB, ← Finset.sum_add_distrib]
  have h2 : ∀ c ∈ A, ((if c ∈ B then 1 else 2) + (if c ∈ B then 1 else 0) : ℕ) = 2 := by
    intro c _
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

open Classical in
/-- **A185376, odd-part form.** For `n = 2 ^ t * m` with `m` odd, the number of binary
necklaces of `2n` beads with a palindromic cut is `2 ^ (n - 1) + 2 ^ ((m - 1) / 2)`. -/
theorem card_hasPalindromicCut_two_pow_mul_odd (t m : ℕ) (hm : Odd m) :
    Nat.card {c : Necklace (2 * (2 ^ t * m)) // HasPalindromicCut c} =
      2 ^ (2 ^ t * m - 1) + 2 ^ ((m - 1) / 2) := by
  set n := 2 ^ t * m with hn
  have hm0 : 0 < m := hm.pos
  have hn0 : 0 < n := Nat.mul_pos (Nat.two_pow_pos t) hm0
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hN : 2 * n = 2 ^ (t + 1) * m := by rw [hn, pow_succ]; ring
  have key := card_pal_add_card_palQ hN hm
  rw [card_hasPalindromicCut_eq_card_image]
  have hPal : (Finset.univ.filter (fun w : ZMod (2 * n) → Bool => IsPalindrome w)).card =
      2 ^ n := by
    have h := card_periodic_pal (N := 2 * n) (M := 2 * n) (by omega) dvd_rfl
    have hfilt : (Finset.univ.filter (fun w : ZMod (2 * n) → Bool =>
        IsPalindrome w ∧ ((2 * n : ℕ) : ZMod (2 * n)) ∈ periods w)) =
        Finset.univ.filter (fun w : ZMod (2 * n) → Bool => IsPalindrome w) := by
      apply Finset.filter_congr
      intro w _
      rw [ZMod.natCast_self]
      exact and_iff_left (periods w).zero_mem
    rw [hfilt] at h
    rw [h]
    congr 1
    omega
  have hPalQ := card_periodic_pal (N := 2 * n) (M := m) hm0 (by rw [hN]; exact dvd_mul_left m _)
  rw [hPal, hPalQ] at key
  obtain ⟨r, rfl⟩ := hm
  have h1 : (2 * r + 1 + 1) / 2 = r + 1 := by omega
  have h2 : (2 * r + 1 - 1) / 2 = r := by omega
  rw [h1] at key
  rw [h2]
  have h3 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h3, pow_succ] at key
  omega

/-- The A185376 count for `n > 0`, with `t = n.factorization 2`.
Binary necklaces of length `2n` with a palindromic cut number
`2^(n-1) + 2^((n-2^t)/2^(t+1))`. The subtraction is untruncated since
`2^t ∣ n`, and the division is exact. The positive-length guard excludes
`ZMod 0 = ℤ`. -/
theorem card_hasPalindromicCut (n : ℕ) (hn : 0 < n) :
    Nat.card {c : Necklace (2 * n) // HasPalindromicCut c} =
      2 ^ (n - 1) + 2 ^ ((n - 2 ^ n.factorization 2) / 2 ^ (n.factorization 2 + 1)) := by
  obtain ⟨t, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.1 hn)
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : ¬ 2 ∣ m := by
    have := Nat.odd_iff.1 hm
    omega
  have hfac : (2 ^ t * m).factorization 2 = t := by
    rw [Nat.factorization_mul (pow_ne_zero t two_ne_zero) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm2, add_zero]
  rw [hfac, card_hasPalindromicCut_two_pow_mul_odd t m hm]
  congr 2
  rw [show 2 ^ t * m - 2 ^ t = 2 ^ t * (m - 1) by rw [Nat.mul_sub_one], pow_succ,
    Nat.mul_div_mul_left _ _ (Nat.two_pow_pos t)]

/-! ## Examples

Decidable checks of the definitions against the first OEIS terms `2, 3, 6`
(`a(1), a(2), a(3)`), computed directly from the definitions, independently of the proof. -/

section GroundTruth

local instance decidablePredIsPalindrome {N : ℕ} [NeZero N] :
    DecidablePred (IsPalindrome (N := N)) :=
  fun w => inferInstanceAs (Decidable (∀ i : ZMod N, w (-1 - i) = w i))

local instance decidableEqNecklace {N : ℕ} [NeZero N] : DecidableEq (Necklace N) :=
  fun a b => Quotient.recOnSubsingleton₂ a b
    (fun w v => decidable_of_iff (∃ k : ZMod N, rotate k w = v) (mk_eq_mk_iff w v).symm)

example : IsPalindrome (fun i : ZMod 4 => ![false, true, true, false] i) := by decide
example : ¬ IsPalindrome (fun i : ZMod 4 => ![false, true, false, false] i) := by decide
example : rotate 1 (fun i : ZMod 4 => ![false, true, true, false] i) =
    (fun i : ZMod 4 => ![true, true, false, false] i) := by
  decide

example : ((Finset.univ.filter (fun w : ZMod 2 → Bool => IsPalindrome w)).image
    (Quotient.mk (rotSetoid 2))).card = 2 := by decide
example : ((Finset.univ.filter (fun w : ZMod 4 → Bool => IsPalindrome w)).image
    (Quotient.mk (rotSetoid 4))).card = 3 := by decide
example : ((Finset.univ.filter (fun w : ZMod 6 → Bool => IsPalindrome w)).image
    (Quotient.mk (rotSetoid 6))).card = 6 := by decide

example : Nat.card {c : Necklace (2 * 2) // HasPalindromicCut c} = 3 := by
  have h : ((Finset.univ.filter (fun w : ZMod 4 → Bool => IsPalindrome w)).image
      (Quotient.mk (rotSetoid 4))).card = 3 := by decide
  rw [card_hasPalindromicCut_eq_card_image]
  convert h using 4

-- The formula reproduces `a(6) = 34` through the odd-part form (`6 = 2 ^ 1 * 3`).
example : Nat.card {c : Necklace (2 * (2 ^ 1 * 3)) // HasPalindromicCut c} = 34 := by
  rw [card_hasPalindromicCut_two_pow_mul_odd 1 3 (by decide)]
  norm_num

-- Non-vacuity of the main statement: its only hypothesis holds at `n = 1`.
example : Nat.card {c : Necklace (2 * 1) // HasPalindromicCut c} =
    2 ^ (1 - 1) + 2 ^ ((1 - 2 ^ (1 : ℕ).factorization 2) / 2 ^ ((1 : ℕ).factorization 2 + 1)) :=
  card_hasPalindromicCut 1 Nat.one_pos

end GroundTruth

end Candidates.A185376RotationClassesBinary
