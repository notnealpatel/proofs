/-
  Erdős Problem #142 — the cardinality-cap obstruction from the carry summit.

  This file formalizes one finite, explicitly constructive obstruction: for every
  `N ≥ 3` there is a set `G ⊆ [0,N) × [0,N)` whose row and column fibres are
  *ordinarily* 3-AP-free subsets of `ℕ` (Mathlib's `ThreeAPFree (· : Set ℕ)`),
  whose common fibre size `b` satisfies the pair-size cap `2 * b ≤ N`, which
  satisfies the cardinality-cap inequality `N * rothNumberNat N ≤ 2 * G.card`,
  and whose base-`N` scalar image contains the explicit nontrivial progression
  `0, N + 1, 2 * (N + 1)`.

  Construction (independently reviewed).  Take a maximum ordinary 3-AP-free
  `C ⊆ [0,N)` of size `r = rothNumberNat N`.  Splitting `range N` into
  `range (N / 2)` and `Ico (N / 2) N` and applying pigeonhole, some end interval
  of length `N - N / 2` contains at least `r / 2` points of `C` in the sense
  `r ≤ 2 * |·|`; translate it down into `range (N - N / 2)`, obtaining a
  3-AP-free `D` with `2 * D.card ≥ r`.  Shrink `D` to a sub-finset `B₀` of size
  `min (D.card) (N / 2)`; this keeps `2 * B₀.card ≥ r` precisely because
  `rothNumberNat N < N` for `N ≥ 3`.  Since `2 * ((N - N / 2) - 1) < N`, the
  image of `B₀` in `ZMod N` is 3-AP-free modulo `N` (a modular progression of
  representatives below `N - N / 2` is an ordinary progression by magnitude);
  translating it modulo `N` produces a 3-AP-free `B : Finset (ZMod N)` with
  `0 ∈ B`, `2 * B.card ≤ N` and `r ≤ 2 * B.card`.  Finally
  `G = {(x,y) : x < N, y < N, (x : ZMod N) - (y : ZMod N) ∈ B}`; rows are lifts
  of `x - B`, columns are lifts of `y + B`, hence all fibres have cardinality
  `B.card` and are ordinarily 3-AP-free, `G.card = N * B.card`, and the whole
  diagonal lies in `G` because `0 ∈ B`.

  This is a finite obstruction statement, not an asymptotic solution of
  Erdős Problem #142, and it does not claim any new Roth-type estimate.  The
  relevant Mathlib (`ThreeAPFree`, `addRothNumber`, `rothNumberNat`) and
  `ZMod` API is reused throughout; no parallel notions are introduced.

  Edge cases.  All row and column fibres of `G` for indices `x ≥ N` (resp.
  `y ≥ N`) are empty and are therefore honestly 3-AP-free; the common *size*
  `b` is asserted only for indices `< N`, the only indices for which `G` can
  have non-empty fibres.  For `N ≥ 3` the fibres are in fact non-empty, since
  `rothNumberNat N ≥ 1` and `2 * B.card ≥ rothNumberNat N`.  The hypothesis
  `3 ≤ N` is used only to force `rothNumberNat N < N` (via the progression
  `0,1,2 ∈ range N`); at `N = 1` the half-slicing lower bound
  `2 * b ≥ rothNumberNat N = 1` and the pair-size cap `2 * b ≤ N = 1` are
  mutually contradictory, which is recorded formally below.
-/

import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-! ## 3-AP-freeness under translation, negation, and the `ZMod` lift -/

section GroupFree

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- 3-AP-freeness is preserved by translation in an additive commutative group. -/
lemma threeAPFree_image_add (a : ZMod N) {S : Set (ZMod N)} (hS : ThreeAPFree S) :
    ThreeAPFree ((fun z : ZMod N => a + z) '' S) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
  have h' : (a + b) + (a + d) = (a + c) + (a + c) := h
  have h1 : (c + c) + (a + a) = (a + c) + (a + c) := by ac_rfl
  have h2 : (b + d) + (a + a) = (a + b) + (a + d) := by ac_rfl
  have h3 : (b + d) + (a + a) = (c + c) + (a + a) := by rw [h2, h', h1]
  exact congrArg (fun z : ZMod N => a + z) (hS hb hc hd (add_right_cancel h3))

omit [NeZero N] in
/-- 3-AP-freeness is preserved by reflection `z ↦ a - z` in an additive
commutative group. -/
lemma threeAPFree_image_sub (a : ZMod N) {S : Set (ZMod N)} (hS : ThreeAPFree S) :
    ThreeAPFree ((fun z : ZMod N => a - z) '' S) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
  have h' : (a - b) + (a - d) = (a - c) + (a - c) := h
  have h'' : (a + -b) + (a + -d) = (a + -c) + (a + -c) := by
    simpa only [sub_eq_add_neg] using h'
  have h1 : (-b + -d) + (a + a) = (a + -b) + (a + -d) := by ac_rfl
  have h2 : (-c + -c) + (a + a) = (a + -c) + (a + -c) := by ac_rfl
  have h3 : (-b + -d) + (a + a) = (-c + -c) + (a + a) := by rw [h1, h'', h2]
  have hbd : b + d = c + c := by
    have h4 : -b + -d = -c + -c := add_right_cancel h3
    have h5 := congrArg (fun t : ZMod N => -t) h4
    simpa only [neg_add, neg_neg] using h5
  exact congrArg (fun z : ZMod N => a - z) (hS hb hc hd hbd)

/-- Lifting a 3-AP-free subset of `ZMod N` to natural representatives in
`[0,N)` via `ZMod.val` preserves ordinary 3-AP-freeness in `ℕ`. -/
lemma threeAPFree_image_val {S : Finset (ZMod N)}
    (hS : ThreeAPFree (S : Set (ZMod N))) :
    ThreeAPFree (((S.image ZMod.val : Finset ℕ) : Set ℕ)) := by
  rw [Finset.coe_image]
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ _ ⟨u, hu, rfl⟩ h
  have hcast : z + u = w + w := by
    have h' := congr_arg (fun t : ℕ => (t : ZMod N)) h
    push_cast at h'
    simpa only [ZMod.natCast_zmod_val] using h'
  rw [hS hz hw hu hcast]

end GroupFree

/-! ## Ordinary 3-AP-freeness of a short interval implies modular 3-AP-freeness -/

/-- If a 3-AP-free `D ⊆ [0,L)` has `2 * (L - 1) < N`, then its image in
`ZMod N` is 3-AP-free: a modular relation `x + z ≡ y + y` between
representatives below `L` has both sides below `N`, hence is an ordinary
relation, to which the hypothesis applies. -/
lemma threeAPFree_image_natCast {N L : ℕ} {D : Finset ℕ}
    (hD : ThreeAPFree (D : Set ℕ)) (hsub : ∀ x ∈ D, x < L) (hL : 2 * (L - 1) < N) :
    ThreeAPFree (((D.image (fun x : ℕ => (x : ZMod N)) : Finset (ZMod N)) : Set (ZMod N))) := by
  rw [Finset.coe_image]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ h
  have hmod : x + z ≡ y + y [MOD N] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact h
  have hxL : x ≤ L - 1 := Nat.le_sub_one_of_lt (hsub x hx)
  have hyL : y ≤ L - 1 := Nat.le_sub_one_of_lt (hsub y hy)
  have hzL : z ≤ L - 1 := Nat.le_sub_one_of_lt (hsub z hz)
  have hxz : x + z < N := by omega
  have hyy : y + y < N := by omega
  have hEq : x + z = y + y := hmod.eq_of_lt_of_lt hxz hyy
  rw [hD hx hy hz hEq]

/-- Ordinary 3-AP-freeness is preserved by the truncated translation
`x ↦ x - k` on a set of elements all of which are at least `k`. -/
lemma threeAPFree_image_sub_nat {k : ℕ} {D : Finset ℕ}
    (hD : ThreeAPFree (D : Set ℕ)) (hk : ∀ x ∈ D, k ≤ x) :
    ThreeAPFree (((D.image (fun x : ℕ => x - k) : Finset ℕ) : Set ℕ)) := by
  rw [Finset.coe_image]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ h
  have h' : (x - k) + (z - k) = (y - k) + (y - k) := h
  have hx' : k ≤ x := hk x hx
  have hy' : k ≤ y := hk y hy
  have hz' : k ≤ z := hk z hz
  have hxyz : x + z = y + y := by omega
  exact congrArg (fun t : ℕ => t - k) (hD hx hy hz hxyz)

/-! ## Elementary arithmetic of the half-slicing bound -/

/-- `2 * (N / 2) ≤ N`. -/
lemma two_mul_div_two_le (N : ℕ) : 2 * (N / 2) ≤ N :=
  Nat.mul_div_le N 2

/-- `N - N / 2 = N / 2 + N % 2`, i.e. `N - N / 2` is the ceiling of `N / 2`. -/
lemma sub_div_two_eq_div_two_add_mod (N : ℕ) : N - N / 2 = N / 2 + N % 2 := by
  have h1 := Nat.div_add_mod N 2
  have h2 := Nat.mul_div_le N 2
  omega

/-- The lower half-interval does not exceed the upper one: `N / 2 ≤ N - N / 2`. -/
lemma div_two_le_sub_div_two (N : ℕ) : N / 2 ≤ N - N / 2 := by
  have h2 := Nat.mul_div_le N 2
  omega

/-- A short interval of length `L = N - N / 2` has `2 * (L - 1) < N`. -/
lemma two_mul_sub_div_two_sub_one_lt {N : ℕ} (hN : 3 ≤ N) :
    2 * ((N - N / 2) - 1) < N := by
  have h1 := Nat.div_add_mod N 2
  have h2 := Nat.mul_div_le N 2
  have h3 : N % 2 ≤ 1 := by have := Nat.mod_lt N (show 0 < 2 by norm_num); omega
  omega

/-- `range N` is not 3-AP-free for `N ≥ 3`, because `0 + 2 = 1 + 1` with
`0 ≠ 1`. -/
lemma not_threeAPFree_range {N : ℕ} (hN : 3 ≤ N) :
    ¬ ThreeAPFree ((Finset.range N : Finset ℕ) : Set ℕ) := by
  intro h
  have h0 : (0 : ℕ) ∈ (Finset.range N : Set ℕ) := Finset.mem_range.mpr (by omega)
  have h1 : (1 : ℕ) ∈ (Finset.range N : Set ℕ) := Finset.mem_range.mpr (by omega)
  have h2 : (2 : ℕ) ∈ (Finset.range N : Set ℕ) := Finset.mem_range.mpr (by omega)
  have := h h0 h1 h2 (by norm_num : (0 : ℕ) + 2 = 1 + 1)
  omega

/-- `rothNumberNat N < N` for `N ≥ 3`: the full interval is not 3-AP-free. -/
lemma rothNumberNat_lt_self {N : ℕ} (hN : 3 ≤ N) : rothNumberNat N < N := by
  rw [rothNumberNat_def]
  refine addRothNumber_lt_of_forall_not_threeAPFree (s := Finset.range N) (n := N) ?_
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  obtain ⟨hts, htcard⟩ := ht
  intro hfree
  have hEq : t = Finset.range N := by
    refine Finset.eq_of_subset_of_card_le hts ?_
    rw [htcard, Finset.card_range]
  exact not_threeAPFree_range hN (by simpa only [hEq] using hfree)

/-- The half-slicing lower bound is compatible with the pair-size cap:
`rothNumberNat N ≤ 2 * (N / 2)` for `N ≥ 3`. -/
lemma rothNumberNat_le_two_mul_div_two {N : ℕ} (hN : 3 ≤ N) :
    rothNumberNat N ≤ 2 * (N / 2) := by
  have hlt := rothNumberNat_lt_self hN
  have h1 := Nat.div_add_mod N 2
  have h3 : N % 2 ≤ 1 := by have := Nat.mod_lt N (show 0 < 2 by norm_num); omega
  omega

/-- `1 ≤ rothNumberNat N` for `N ≥ 1`, via the singleton `{0}`. -/
lemma one_le_rothNumberNat {N : ℕ} (hN : 1 ≤ N) : 1 ≤ rothNumberNat N := by
  have hfree : ThreeAPFree (({0} : Finset ℕ) : Set ℕ) := by
    rw [Finset.coe_singleton]
    exact threeAPFree_singleton 0
  have h := ThreeAPFree.le_rothNumberNat ({0} : Finset ℕ) hfree (n := N) (k := 1)
    (fun x hx => by
      rw [Finset.mem_singleton] at hx
      omega) (by simp)
  simpa using h

/-- Edge case `N = 1`: the half-slicing lower bound `2 * b ≥ rothNumberNat 1`
is incompatible with the pair-size cap `2 * b ≤ 1`.  So the hypothesis `3 ≤ N`
of the main construction is not vacuous. -/
theorem two_mul_lt_rothNumberNat_one (b : ℕ) (hb : 2 * b ≤ 1) :
    2 * b < rothNumberNat 1 := by
  have h1 : rothNumberNat 1 ≤ 1 := rothNumberNat_le 1
  have h2 : 1 ≤ rothNumberNat 1 := one_le_rothNumberNat le_rfl
  omega

/-! ## Half-slicing a maximum 3-AP-free set -/

/-- Shrinking step: a 3-AP-free `D` with `rothNumberNat N ≤ 2 * D.card` has a
3-AP-free sub-finset `B` that keeps the lower bound and additionally satisfies
the pair-size cap `2 * B.card ≤ N`.  This is where the compatibility
`rothNumberNat N ≤ 2 * (N / 2)` (for `N ≥ 3`) is used. -/
lemma exists_capped_subset {N : ℕ} (hN : 3 ≤ N) {D : Finset ℕ}
    (hD : ThreeAPFree (D : Set ℕ)) (hlow : rothNumberNat N ≤ 2 * D.card) :
    ∃ B ⊆ D, ThreeAPFree (B : Set ℕ) ∧ rothNumberNat N ≤ 2 * B.card ∧ 2 * B.card ≤ N := by
  rcases lt_or_ge D.card (N / 2) with h | h
  · exact ⟨D, Subset.rfl, hD, hlow, by have := two_mul_div_two_le N; omega⟩
  · obtain ⟨B, hBD, hBcard⟩ := Finset.exists_subset_card_eq (s := D) (n := N / 2) h
    refine ⟨B, hBD, hD.mono (Finset.coe_subset.mpr hBD), ?_, ?_⟩
    · rw [hBcard]
      exact rothNumberNat_le_two_mul_div_two hN
    · rw [hBcard]
      exact two_mul_div_two_le N

/-- **Half-slicing.**  A maximum ordinary 3-AP-free subset of `[0,N)` has a
3-AP-free sub-finset `B ⊆ [0, N - N / 2)` with
`2 * B.card ≤ N ≤ 2 * (N - N / 2)` and the half-slicing lower bound
`rothNumberNat N ≤ 2 * B.card`. -/
lemma exists_halfSlice {N : ℕ} (hN : 3 ≤ N) :
    ∃ B : Finset ℕ, B ⊆ Finset.range (N - N / 2) ∧ ThreeAPFree (B : Set ℕ) ∧
      2 * B.card ≤ N ∧ rothNumberNat N ≤ 2 * B.card := by
  obtain ⟨C, hCsub, hCcard, hCfree⟩ := rothNumberNat_spec N
  have hcover : C ⊆ Finset.range (N / 2) ∪ Finset.Ico (N / 2) N := by
    intro x hx
    have hxN : x < N := Finset.mem_range.mp (hCsub hx)
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    rcases lt_or_ge x (N / 2) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hxN⟩
  have hunion : (C ∩ Finset.range (N / 2)) ∪ (C ∩ Finset.Ico (N / 2) N) = C := by
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hcover]
  have hsum : C.card ≤
      (C ∩ Finset.range (N / 2)).card + (C ∩ Finset.Ico (N / 2) N).card :=
    calc C.card = ((C ∩ Finset.range (N / 2)) ∪ (C ∩ Finset.Ico (N / 2) N)).card := by
          rw [hunion]
      _ ≤ _ := Finset.card_union_le _ _
  have hpigeon : rothNumberNat N ≤ 2 * (C ∩ Finset.range (N / 2)).card ∨
      rothNumberNat N ≤ 2 * (C ∩ Finset.Ico (N / 2) N).card := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [not_le] at h1 h2
    omega
  have hD : ∃ D : Finset ℕ, D ⊆ Finset.range (N - N / 2) ∧
      ThreeAPFree (D : Set ℕ) ∧ rothNumberNat N ≤ 2 * D.card := by
    rcases hpigeon with hpigeon | hpigeon
    · refine ⟨C ∩ Finset.range (N / 2), ?_, hCfree.mono (Finset.coe_subset.mpr
        Finset.inter_subset_left), hpigeon⟩
      intro x hx
      rw [Finset.mem_inter, Finset.mem_range] at hx
      have := div_two_le_sub_div_two N
      exact Finset.mem_range.mpr (by omega)
    · refine ⟨(C ∩ Finset.Ico (N / 2) N).image (fun x : ℕ => x - N / 2), ?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Finset.mem_inter, Finset.mem_Ico] at hy
        have h2 := two_mul_div_two_le N
        exact Finset.mem_range.mpr (by omega)
      · exact threeAPFree_image_sub_nat (k := N / 2)
          (D := C ∩ Finset.Ico (N / 2) N)
          (hCfree.mono (Finset.coe_subset.mpr Finset.inter_subset_left)) (by
            intro x hx
            rw [Finset.mem_inter, Finset.mem_Ico] at hx
            exact hx.2.1)
      · have hc : ((C ∩ Finset.Ico (N / 2) N).image (fun x : ℕ => x - N / 2)).card
            = (C ∩ Finset.Ico (N / 2) N).card := by
          refine Finset.card_image_of_injOn ?_
          intro x hx y hy h
          rw [Finset.mem_coe, Finset.mem_inter, Finset.mem_Ico] at hx hy
          have hx' : N / 2 ≤ x := hx.2.1
          have hy' : N / 2 ≤ y := hy.2.1
          have h' : x - N / 2 = y - N / 2 := h
          omega
        rw [hc]
        exact hpigeon
  obtain ⟨D, hDsub, hDfree, hDlow⟩ := hD
  obtain ⟨B, hBD, hBfree, hBlow, hBcap⟩ := exists_capped_subset hN hDfree hDlow
  exact ⟨B, hBD.trans hDsub, hBfree, hBcap, hBlow⟩

/-- **The difference set.**  There is a 3-AP-free `B : Finset (ZMod N)`
containing `0`, of common fibre size satisfying `2 * B.card ≤ N`, and meeting
the half-slicing lower bound `rothNumberNat N ≤ 2 * B.card`. -/
lemma exists_zmod_free_with_zero {N : ℕ} (hN : 3 ≤ N) :
    ∃ B : Finset (ZMod N), 0 ∈ B ∧ ThreeAPFree (B : Set (ZMod N)) ∧
      2 * B.card ≤ N ∧ rothNumberNat N ≤ 2 * B.card := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨B₀, hB₀sub, hB₀free, hB₀cap, hB₀low⟩ := exists_halfSlice hN
  have hB₀lt : ∀ x ∈ B₀, x < N := by
    intro x hx
    have hx' := Finset.mem_range.mp (hB₀sub hx)
    have h2 := div_two_le_sub_div_two N
    omega
  have hB₀cast : ThreeAPFree (((B₀.image (fun x : ℕ => (x : ZMod N)) : Finset (ZMod N))
      : Set (ZMod N))) :=
    threeAPFree_image_natCast hB₀free
      (fun x hx => Finset.mem_range.mp (hB₀sub hx)) (two_mul_sub_div_two_sub_one_lt hN)
  have hB₀card : (B₀.image (fun x : ℕ => (x : ZMod N))).card = B₀.card := by
    refine Finset.card_image_of_injOn ?_
    intro x hx y hy h
    rw [ZMod.natCast_eq_natCast_iff] at h
    exact h.eq_of_lt_of_lt (hB₀lt x (by simpa using hx)) (hB₀lt y (by simpa using hy))
  have hne : B₀.Nonempty := by
    rcases Finset.eq_empty_or_nonempty B₀ with h | h
    · rw [h] at hB₀low
      simp only [card_empty, mul_zero] at hB₀low
      have := one_le_rothNumberNat (show 1 ≤ N by omega)
      omega
    · exact h
  obtain ⟨b₀, hb₀⟩ := hne
  have hcard_shift : ∀ t : ZMod N,
      ((B₀.image (fun x : ℕ => (x : ZMod N))).image (fun z : ZMod N => t + z)).card = B₀.card := by
    intro t
    rw [Finset.card_image_of_injective _ (fun p q h => add_left_cancel h), hB₀card]
  refine ⟨(B₀.image (fun x : ℕ => (x : ZMod N))).image
      (fun z : ZMod N => -(b₀ : ZMod N) + z), ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(b₀ : ZMod N),
      Finset.mem_image.mpr ⟨b₀, hb₀, rfl⟩, by simp⟩
  · rw [Finset.coe_image]
    exact threeAPFree_image_add _ hB₀cast
  · rw [hcard_shift]
    exact hB₀cap
  · rw [hcard_shift]
    exact hB₀low

/-! ## The graph, its fibres, and its scalar image -/

/-- The bipartite "difference graph" of a difference set `B` in `ZMod N`:
`(x,y) ∈ G` exactly when `x < N`, `y < N` and `x - y ∈ B`.  Rows are the lifts
of `x - B` and columns are the lifts of `y + B`, so at the level of `ZMod N`
the row and column fibres are translates of `-B` and `B`. -/
def carryGraph (N : ℕ) (B : Finset (ZMod N)) : Finset (ℕ × ℕ) :=
  ((Finset.range N) ×ˢ (Finset.range N)).filter
    (fun p : ℕ × ℕ => (p.1 : ZMod N) - (p.2 : ZMod N) ∈ B)

/-- Membership in `carryGraph` unwinds to the defining difference condition. -/
lemma mem_carryGraph {N : ℕ} {B : Finset (ZMod N)} {x y : ℕ} :
    (x, y) ∈ carryGraph N B ↔ x < N ∧ y < N ∧ (x : ZMod N) - (y : ZMod N) ∈ B := by
  simp [carryGraph, and_assoc]

/-- The row fibre of `G` over the index `x`. -/
def rowFiber (G : Finset (ℕ × ℕ)) (x : ℕ) : Finset ℕ :=
  (G.filter (fun p : ℕ × ℕ => p.1 = x)).image Prod.snd

/-- The column fibre of `G` over the index `y`. -/
def colFiber (G : Finset (ℕ × ℕ)) (y : ℕ) : Finset ℕ :=
  (G.filter (fun p : ℕ × ℕ => p.2 = y)).image Prod.fst

/-- The base-`N` scalar image `(x,y) ↦ x * N + y` of `G`. -/
def scalarImage (N : ℕ) (G : Finset (ℕ × ℕ)) : Finset ℕ :=
  G.image (fun p : ℕ × ℕ => p.1 * N + p.2)

/-- Membership description of the row fibre of a `carryGraph`. -/
lemma mem_rowFiber {N : ℕ} {B : Finset (ZMod N)} {x y : ℕ} :
    y ∈ rowFiber (carryGraph N B) x ↔ x < N ∧ y < N ∧ (x : ZMod N) - (y : ZMod N) ∈ B := by
  rw [rowFiber, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hp2⟩
    rw [Finset.mem_filter, mem_carryGraph] at hp
    obtain ⟨hpG, hpx⟩ := hp
    rw [hpx, hp2] at hpG
    exact hpG
  · rintro ⟨hx, hy, hmem⟩
    exact ⟨(x, y), by rw [Finset.mem_filter, mem_carryGraph]; exact ⟨⟨hx, hy, hmem⟩, rfl⟩, rfl⟩

/-- Membership description of the column fibre of a `carryGraph`. -/
lemma mem_colFiber {N : ℕ} {B : Finset (ZMod N)} {x y : ℕ} :
    x ∈ colFiber (carryGraph N B) y ↔ x < N ∧ y < N ∧ (x : ZMod N) - (y : ZMod N) ∈ B := by
  rw [colFiber, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hp1⟩
    rw [Finset.mem_filter, mem_carryGraph] at hp
    obtain ⟨hpG, hpy⟩ := hp
    rw [hpy, hp1] at hpG
    exact hpG
  · rintro ⟨hx, hy, hmem⟩
    exact ⟨(x, y), by rw [Finset.mem_filter, mem_carryGraph]; exact ⟨⟨hx, hy, hmem⟩, rfl⟩, rfl⟩

/-- Every row fibre of `G` that can be non-empty is a `ZMod.val`-lift of the
translate `x - B`. -/
lemma rowFiber_eq_carryGraph {N : ℕ} [NeZero N] {B : Finset (ZMod N)} {x : ℕ} (hx : x < N) :
    rowFiber (carryGraph N B) x =
      (B.image (fun b : ZMod N => (x : ZMod N) - b)).image ZMod.val := by
  ext y
  rw [mem_rowFiber, Finset.mem_image]
  constructor
  · rintro ⟨-, hy, hmem⟩
    refine ⟨(y : ZMod N), ?_, ZMod.val_natCast_of_lt hy⟩
    rw [Finset.mem_image]
    exact ⟨(x : ZMod N) - (y : ZMod N), hmem, by abel⟩
  · rintro ⟨z, hz, hzval⟩
    rw [Finset.mem_image] at hz
    obtain ⟨b, hb, rfl⟩ := hz
    have hy : y < N := by rw [← hzval]; exact ZMod.val_lt _
    refine ⟨hx, hy, ?_⟩
    rw [← hzval, ZMod.natCast_zmod_val]
    have : (x : ZMod N) - ((x : ZMod N) - b) = b := by abel
    rw [this]
    exact hb

/-- Every column fibre of `G` that can be non-empty is a `ZMod.val`-lift of the
translate `y + B`. -/
lemma colFiber_eq_carryGraph {N : ℕ} [NeZero N] {B : Finset (ZMod N)} {y : ℕ} (hy : y < N) :
    colFiber (carryGraph N B) y =
      (B.image (fun b : ZMod N => (y : ZMod N) + b)).image ZMod.val := by
  ext x
  rw [mem_colFiber, Finset.mem_image]
  constructor
  · rintro ⟨hx, -, hmem⟩
    refine ⟨(x : ZMod N), ?_, ZMod.val_natCast_of_lt hx⟩
    rw [Finset.mem_image]
    exact ⟨(x : ZMod N) - (y : ZMod N), hmem, by abel⟩
  · rintro ⟨z, hz, hzval⟩
    rw [Finset.mem_image] at hz
    obtain ⟨b, hb, rfl⟩ := hz
    have hx : x < N := by rw [← hzval]; exact ZMod.val_lt _
    refine ⟨hx, hy, ?_⟩
    rw [← hzval, ZMod.natCast_zmod_val]
    have : (y : ZMod N) + b - (y : ZMod N) = b := by abel
    rw [this]
    exact hb

/-- Cardinality of a `fst`-fibre equals the cardinality of the corresponding
row fibre. -/
lemma card_filter_fst_eq (G : Finset (ℕ × ℕ)) (x : ℕ) :
    (G.filter (fun p : ℕ × ℕ => p.1 = x)).card = (rowFiber G x).card := by
  rw [rowFiber]
  refine (Finset.card_image_of_injOn ?_).symm
  intro p hp q hq h
  rw [Finset.mem_coe, Finset.mem_filter] at hp hq
  exact Prod.ext (by rw [hp.2, hq.2]) h

/-- Cardinality of a `snd`-fibre equals the cardinality of the corresponding
column fibre. -/
lemma card_filter_snd_eq (G : Finset (ℕ × ℕ)) (y : ℕ) :
    (G.filter (fun p : ℕ × ℕ => p.2 = y)).card = (colFiber G y).card := by
  rw [colFiber]
  refine (Finset.card_image_of_injOn ?_).symm
  intro p hp q hq h
  rw [Finset.mem_coe, Finset.mem_filter] at hp hq
  exact Prod.ext h (by rw [hp.2, hq.2])

/-- Each non-empty row fibre has cardinality `B.card`. -/
lemma card_rowFiber {N : ℕ} [NeZero N] {B : Finset (ZMod N)} {x : ℕ} (hx : x < N) :
    (rowFiber (carryGraph N B) x).card = B.card := by
  rw [rowFiber_eq_carryGraph hx, Finset.card_image_of_injective _ (ZMod.val_injective N)]
  refine Finset.card_image_of_injOn ?_
  intro p _ q _ h
  have h' : (x : ZMod N) - p = (x : ZMod N) - q := h
  exact neg_inj.mp (add_left_cancel (by simpa only [sub_eq_add_neg] using h'))

/-- Each non-empty column fibre has cardinality `B.card`. -/
lemma card_colFiber {N : ℕ} [NeZero N] {B : Finset (ZMod N)} {y : ℕ} (hy : y < N) :
    (colFiber (carryGraph N B) y).card = B.card := by
  rw [colFiber_eq_carryGraph hy, Finset.card_image_of_injective _ (ZMod.val_injective N)]
  refine Finset.card_image_of_injOn ?_
  intro p _ q _ h
  exact add_left_cancel h

/-- The graph has exactly `N * B.card` elements: it is the union of its `N`
row fibres, each of cardinality `B.card`. -/
lemma card_carryGraph {N : ℕ} [NeZero N] {B : Finset (ZMod N)} :
    (carryGraph N B).card = N * B.card := by
  have hH : Set.MapsTo Prod.fst ((carryGraph N B : Finset (ℕ × ℕ)) : Set (ℕ × ℕ))
      (Finset.range N : Set ℕ) := by
    intro p hp
    exact Finset.mem_range.mpr (mem_carryGraph.mp hp).1
  rw [Finset.card_eq_sum_card_fiberwise hH]
  have hsum : ∀ x ∈ Finset.range N,
      ((carryGraph N B).filter (fun p : ℕ × ℕ => p.1 = x)).card = B.card := by
    intro x hx
    rw [card_filter_fst_eq, card_rowFiber (Finset.mem_range.mp hx)]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ## The scalar progression in the base-`N` image -/

/-- The three explicit scalars `0, N + 1, 2 * (N + 1)` form a nontrivial
three-term arithmetic progression: `0 + 2 * (N + 1) = (N + 1) + (N + 1)` and
they are pairwise distinct. -/
theorem scalarTriple_nontrivial_threeAP (N : ℕ) :
    0 + 2 * (N + 1) = (N + 1) + (N + 1) ∧ 0 ≠ N + 1 ∧ (N + 1) ≠ 2 * (N + 1) ∧
      0 ≠ 2 * (N + 1) :=
  ⟨by ring, by omega, by omega, by omega⟩

/-! ## The main finite theorem -/

/-- **Cardinality-cap obstruction from the carry summit.**  For every `N ≥ 3`
there is a bounded `G ⊆ [0,N) × [0,N)` such that

* every row fibre and every column fibre of `G` is an ordinarily 3-AP-free
  subset of `ℕ` (all indices, including the indices `≥ N`, whose fibres are
  empty);
* some `b` is the common cardinality of every row and column fibre with index
  `< N`, and the pair-size cap `2 * b ≤ N` holds;
* the cardinality-cap inequality `N * rothNumberNat N ≤ 2 * G.card` holds;
* the diagonal triple `(0,0), (1,1), (2,2)` lies in `G`, so the base-`N`
  scalar image of `G` contains `0, N + 1, 2 * (N + 1)`, a nontrivial
  three-term arithmetic progression. -/
theorem exists_carryCardinalityCap (N : ℕ) (hN : 3 ≤ N) :
    ∃ G : Finset (ℕ × ℕ),
      (∀ p ∈ G, p.1 < N ∧ p.2 < N) ∧
      (∀ x, ThreeAPFree (((rowFiber G x : Finset ℕ) : Set ℕ))) ∧
      (∀ y, ThreeAPFree (((colFiber G y : Finset ℕ) : Set ℕ))) ∧
      (∃ b : ℕ, (∀ x < N, (rowFiber G x).card = b) ∧
        (∀ y < N, (colFiber G y).card = b) ∧ 2 * b ≤ N) ∧
      N * rothNumberNat N ≤ 2 * G.card ∧
      (0, 0) ∈ G ∧ (1, 1) ∈ G ∧ (2, 2) ∈ G ∧
      ({0, N + 1, 2 * (N + 1)} : Finset ℕ) ⊆ scalarImage N G := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨B, hB0, hBfree, hBcap, hBlow⟩ := exists_zmod_free_with_zero hN
  have hG00 : (0, 0) ∈ carryGraph N B :=
    mem_carryGraph.mpr ⟨by omega, by omega, by simpa using hB0⟩
  have hG11 : (1, 1) ∈ carryGraph N B :=
    mem_carryGraph.mpr ⟨by omega, by omega, by simpa using hB0⟩
  have hG22 : (2, 2) ∈ carryGraph N B :=
    mem_carryGraph.mpr ⟨by omega, by omega, by simpa using hB0⟩
  refine ⟨carryGraph N B, ?_, ?_, ?_, ?_, ?_, hG00, hG11, hG22, ?_⟩
  · intro p hp
    exact ⟨(mem_carryGraph.mp hp).1, (mem_carryGraph.mp hp).2.1⟩
  · intro x
    by_cases hx : x < N
    · rw [rowFiber_eq_carryGraph hx]
      refine threeAPFree_image_val ?_
      rw [Finset.coe_image]
      exact threeAPFree_image_sub (x : ZMod N) hBfree
    · have hemp : rowFiber (carryGraph N B) x = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨y, hy⟩
        exact hx (mem_rowFiber.mp hy).1
      rw [hemp]
      simp
  · intro y
    by_cases hy : y < N
    · rw [colFiber_eq_carryGraph hy]
      refine threeAPFree_image_val ?_
      rw [Finset.coe_image]
      exact threeAPFree_image_add (y : ZMod N) hBfree
    · have hemp : colFiber (carryGraph N B) y = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨x, hx'⟩
        exact hy (mem_colFiber.mp hx').2.1
      rw [hemp]
      simp
  · exact ⟨B.card, fun x hx => card_rowFiber hx, fun y hy => card_colFiber hy, hBcap⟩
  · rw [card_carryGraph]
    calc N * rothNumberNat N ≤ N * (2 * B.card) := Nat.mul_le_mul_left N hBlow
      _ = 2 * (N * B.card) := by ring
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨(0, 0), hG00, by ring⟩
    · exact Finset.mem_image.mpr ⟨(1, 1), hG11, by ring⟩
    · exact Finset.mem_image.mpr ⟨(2, 2), hG22, by ring⟩

/-- The main theorem specialized to `N = 3`, exhibiting a concrete nonvacuous
instance: non-empty fibres, the pair-size cap `2 * b ≤ 3`, and the
cardinality-cap inequality `3 * rothNumberNat 3 ≤ 2 * G.card`. -/
example : ∃ G : Finset (ℕ × ℕ),
    (∀ p ∈ G, p.1 < 3 ∧ p.2 < 3) ∧ (0, 0) ∈ G ∧ (1, 1) ∈ G ∧ (2, 2) ∈ G ∧
      (∃ b : ℕ, (∀ x < 3, (rowFiber G x).card = b) ∧ 2 * b ≤ 3) ∧
      3 * rothNumberNat 3 ≤ 2 * G.card := by
  obtain ⟨G, h1, -, -, ⟨b, hb1, -, hb2⟩, hcard, h00, h11, h22, -⟩ :=
    exists_carryCardinalityCap 3 (by norm_num)
  exact ⟨G, h1, h00, h11, h22, ⟨b, hb1, hb2⟩, hcard⟩

/-- Ground truth for the concrete `N = 3` difference set `B = {0} ⊂ ZMod 3`:
the associated difference graph is exactly the diagonal. -/
example : carryGraph 3 ({(0 : ZMod 3)} : Finset (ZMod 3)) = {(0, 0), (1, 1), (2, 2)} := by
  decide

#check @exists_carryCardinalityCap
#check @scalarTriple_nontrivial_threeAP
#check @exists_zmod_free_with_zero
#check @exists_halfSlice

#print axioms exists_carryCardinalityCap
#print axioms scalarTriple_nontrivial_threeAP
#print axioms exists_zmod_free_with_zero
#print axioms exists_halfSlice
#print axioms threeAPFree_image_natCast
#print axioms two_mul_lt_rothNumberNat_one

end Erdos142