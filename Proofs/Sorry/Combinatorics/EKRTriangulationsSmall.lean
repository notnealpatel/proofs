/-
# EKR for triangulations of a convex `n`-gon (Kalai–Meagher): rotation bound and small cases

## Source

* MathOverflow question 114646, "Intersecting family of triangulations", asked by
  Gil Kalai (2012): https://mathoverflow.net/questions/114646/intersecting-family-of-triangulations
  (the conjecture was posed independently by Karen Meagher, 2012).
* D. Ellis, "Intersection problems in extremal combinatorics: theorems, techniques and
  questions old and new", arXiv:2107.06371, §"Triangulations, and a conjecture of Kalai and
  Meagher" (Conjecture `conj:kalai` there), quoted verbatim:

  > Let P_n be a fixed, convex, n-vertex polygon, and let F be an intersecting family of
  > triangulations of P_n. Then |F| ≤ C_{n-3}, with equality iff F consists of all
  > triangulations containing some fixed diagonal that forms a triangle with two consecutive
  > edges of P_n.

  and, on the trivial bound:

  > It is easy to show that an intersecting family F of triangulations of P_n has size at
  > most C_{n-2}/2. (Take P_n to be a regular polygon, and observe that a triangulation T
  > shares no diagonal in common with σ(T), where σ is the rotation by 2π/n about the centre
  > of P_n.) [...] To our knowledge, no significant improvement on this `trivial' bound, is
  > known.

* A. Olarte, F. Santos, J. Spreer, C. Stump, "The EKR-module property of pseudomanifolds"
  (JCTA 2020), arXiv:1710.02518: flag pure complexes without boundary of dimension ≤ 3 are
  pure-EKR; the simplicial associahedron of the `n`-gon has dimension `n - 4`, so the
  conjecture holds for `n ≤ 7`.

Date of this card: 2026-10-21.

## Status

The conjecture is **open** for `n ≥ 8` (proved for `n ≤ 7` by OSSS; computer-verified to the
9-gon). This module proves, kernel-checked and `sorry`-free:

* `two_mul_ncard_le_ncard_setOf_isTriang` — the rotation bound `2 |S| ≤ |T_n|` for every
  `n ≥ 4` (the "trivial" bound recorded by Ellis);
* `ncard_le_catalan_of_le_six` — the conjecture's bound `|S| ≤ C_{n-3}` for `n = 4, 5, 6`,
  by finite enumeration (`decide +kernel`, no `native_decide`);
* `ncard_earStar_six` — the ear star at `n = 6` has `C_3 = 5` members, so the bound is attained;
* ground truth: the numbers of triangulations of the 4-, 5- and 6-gon are `C_2, C_3, C_4`.

The general bound `kalai_meagher_conjecture` is the single remaining `sorry`. The equality
characterisation ("iff F is the star of an ear") is not formalised here.

## Encoding

Vertices are `ZMod n`. A chord is a `Sym2 (ZMod n)`; it is a diagonal when its cyclic gap lies
in `[2, n - 2]`. Two chords cross when their endpoints strictly interleave cyclically. A
triangulation is a *maximal* family of pairwise non-crossing diagonals (no Catalan counting is
built into the definition; the counts are ground-truth checks). Families of triangulations are
`Set`s measured by `Set.ncard`; the ambient type is finite, so `ncard` is the true cardinality.
"Every two triangulations share a diagonal" is stated for distinct members; for `n ≥ 4` this is
equivalent to the all-pairs version since triangulations are nonempty (`IsTriang.nonempty`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.EKRTriangulationsSmall

/-! ## Definitions -/

/-- A diagonal of the convex `n`-gon with vertices `ZMod n`: an unordered pair `{a, b}` whose
cyclic gap `(b - a).val` lies in `[2, n - 2]`, i.e. the endpoints are neither equal nor
adjacent. -/
def IsDiag (n : ℕ) (d : Sym2 (ZMod n)) : Prop :=
  ∃ a b : ZMod n, d = s(a, b) ∧ 2 ≤ (b - a).val ∧ (b - a).val + 2 ≤ n

/-- Strict cyclic interleaving of representatives: `a, c, b, c'` are distinct and occur in this
cyclic order around `ZMod n`. -/
def Interleave (n : ℕ) (a b c c' : ZMod n) : Prop :=
  0 < (c - a).val ∧ (c - a).val < (b - a).val ∧ (b - a).val < (c' - a).val

/-- Two chords `{a, b}` and `{c, c'}` cross when their endpoints strictly interleave around the
polygon: `a, c, b, c'` are distinct and occur in this cyclic order. -/
def Crosses (n : ℕ) (d e : Sym2 (ZMod n)) : Prop :=
  ∃ a b c c' : ZMod n, d = s(a, b) ∧ e = s(c, c') ∧ Interleave n a b c c'

/-- A triangulation of the convex `n`-gon: a maximal family of pairwise non-crossing
diagonals. -/
def IsTriang (n : ℕ) (T : Finset (Sym2 (ZMod n))) : Prop :=
  (∀ d ∈ T, IsDiag n d) ∧ (∀ d ∈ T, ∀ e ∈ T, ¬ Crosses n d e) ∧
    ∀ d, IsDiag n d → d ∉ T → ∃ e ∈ T, Crosses n d e

/-- The star of the ear `{0, 2}`: all triangulations containing the diagonal `{0, 2}`, which
cuts off the triangle `0, 1, 2` formed with two consecutive edges. -/
def earStar (n : ℕ) : Set (Finset (Sym2 (ZMod n))) :=
  {T | IsTriang n T ∧ s(0, 2) ∈ T}

/-- Rotation of the polygon by `t`, acting on chords. -/
def shift (n : ℕ) (t : ZMod n) : Sym2 (ZMod n) → Sym2 (ZMod n) :=
  Sym2.map (· + t)

/-! ## Decidability (via representatives) -/

instance (n : ℕ) (a b c c' : ZMod n) : Decidable (Interleave n a b c c') := by
  unfold Interleave; infer_instance

/-- `IsDiag` on a representative pair: one of the two orientations has gap in `[2, n - 2]`. -/
lemma isDiag_mk_iff (n : ℕ) (p q : ZMod n) : IsDiag n s(p, q) ↔
    (2 ≤ (q - p).val ∧ (q - p).val + 2 ≤ n) ∨ (2 ≤ (p - q).val ∧ (p - q).val + 2 ≤ n) := by
  simp only [IsDiag, Sym2.eq_iff]
  aesop

/-- `Crosses` on representative pairs: one of the four orientations interleaves. -/
lemma crosses_mk_iff (n : ℕ) (p q r t : ZMod n) : Crosses n s(p, q) s(r, t) ↔
    Interleave n p q r t ∨ Interleave n p q t r ∨ Interleave n q p r t ∨
      Interleave n q p t r := by
  simp only [Crosses, Sym2.eq_iff]
  aesop

instance (n : ℕ) (d : Sym2 (ZMod n)) : Decidable (IsDiag n d) :=
  Sym2.recOnSubsingleton d fun p q => decidable_of_iff _ (isDiag_mk_iff n p q).symm

instance (n : ℕ) (d e : Sym2 (ZMod n)) : Decidable (Crosses n d e) :=
  Sym2.recOnSubsingleton d fun p q => Sym2.recOnSubsingleton e fun r t =>
    decidable_of_iff _ (crosses_mk_iff n p q r t).symm

instance (n : ℕ) [NeZero n] (T : Finset (Sym2 (ZMod n))) : Decidable (IsTriang n T) := by
  unfold IsTriang; infer_instance

/-! ## Ground truth for the definitions -/

example : IsDiag 6 s(0, 2) := by decide
example : IsDiag 6 s(4, 1) := by decide
example : ¬ IsDiag 6 s(0, 1) := by decide
example : ¬ IsDiag 6 s(5, 0) := by decide
example : ¬ IsDiag 6 s(3, 3) := by decide
example : Crosses 6 s(0, 3) s(1, 4) := by decide
example : Crosses 6 s(1, 4) s(3, 0) := by decide
example : ¬ Crosses 6 s(0, 2) s(2, 4) := by decide
example : ¬ Crosses 6 s(0, 2) s(3, 5) := by decide
example : ¬ Crosses 6 s(0, 3) s(0, 3) := by decide
example : IsTriang 5 {s(0, 2), s(0, 3)} := by decide
example : IsTriang 6 {s(0, 2), s(2, 4), s(4, 0)} := by decide
example : ¬ IsTriang 6 {s(0, 2), s(0, 3)} := by decide
example : ¬ IsTriang 6 {s(0, 3), s(1, 4), s(0, 2)} := by decide
example : shift 6 1 s(0, 5) = s(1, 0) := by decide

/-! ## The rotation bound (Kalai; Ellis survey, arXiv:2107.06371) -/

/-- Rotation is injective on chords. -/
lemma shift_injective (n : ℕ) (t : ZMod n) : Function.Injective (shift n t) :=
  Sym2.map.injective (add_left_injective t)

/-- Rotating by `-t` and then by `t` is the identity. -/
lemma shift_shift_neg (n : ℕ) (t : ZMod n) (d : Sym2 (ZMod n)) :
    shift n t (shift n (-t) d) = d := by
  induction d using Sym2.ind with
  | h a b => simp [shift]

/-- Rotation preserves diagonals. -/
lemma isDiag_shift {n : ℕ} (t : ZMod n) {d : Sym2 (ZMod n)} (hd : IsDiag n d) :
    IsDiag n (shift n t d) := by
  obtain ⟨a, b, rfl, h1, h2⟩ := hd
  refine ⟨a + t, b + t, by simp [shift], ?_⟩
  simp only [add_sub_add_right_eq_sub]
  exact ⟨h1, h2⟩

/-- Rotation preserves crossing. -/
lemma crosses_shift {n : ℕ} (t : ZMod n) {d e : Sym2 (ZMod n)} (h : Crosses n d e) :
    Crosses n (shift n t d) (shift n t e) := by
  obtain ⟨a, b, c, c', rfl, rfl, hil⟩ := h
  refine ⟨a + t, b + t, c + t, c' + t, by simp [shift], by simp [shift], ?_⟩
  simp only [Interleave, add_sub_add_right_eq_sub] at hil ⊢
  exact hil

/-- Key lemma: every diagonal crosses its rotation by one step. -/
lemma crosses_shift_one {n : ℕ} {d : Sym2 (ZMod n)} (hd : IsDiag n d) :
    Crosses n d (shift n 1 d) := by
  obtain ⟨a, b, rfl, h1, h2⟩ := hd
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hone : (a + 1 - a).val = 1 := by
    rw [add_sub_cancel_left, ZMod.val_one]
  have hval : (b + 1 - a).val = (b - a).val + 1 := by
    rw [show b + 1 - a = (b - a) + 1 by ring, ZMod.val_add, ZMod.val_one,
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨a, b, a + 1, b + 1, rfl, by simp [shift], ?_⟩
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Rotation by `t` maps triangulations to triangulations. -/
lemma isTriang_image_shift {n : ℕ} (t : ZMod n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriang n T) : IsTriang n (T.image (shift n t)) := by
  classical
  obtain ⟨hdiag, hnc, hmax⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd
    exact isDiag_shift t (hdiag d₀ hd₀)
  · intro d hd e he hcross
    obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
    have hback := crosses_shift (-t) hcross
    rw [show shift n (-t) (shift n t d₀) = d₀ by simpa using shift_shift_neg n (-t) d₀,
      show shift n (-t) (shift n t e₀) = e₀ by simpa using shift_shift_neg n (-t) e₀] at hback
    exact hnc d₀ hd₀ e₀ he₀ hback
  · intro d hd hdT
    have hd₀ : IsDiag n (shift n (-t) d) := isDiag_shift (-t) hd
    have hd₀T : shift n (-t) d ∉ T := by
      intro hmem
      exact hdT (Finset.mem_image.mpr ⟨_, hmem, shift_shift_neg n t d⟩)
    obtain ⟨e, he, hcross⟩ := hmax _ hd₀ hd₀T
    refine ⟨shift n t e, Finset.mem_image_of_mem _ he, ?_⟩
    simpa [shift_shift_neg] using crosses_shift t hcross

/-- A triangulation and its rotation by one step share no diagonal. -/
lemma not_mem_of_mem_image_shift_one {n : ℕ} {T : Finset (Sym2 (ZMod n))} (hT : IsTriang n T)
    {d : Sym2 (ZMod n)} (hd : d ∈ T.image (shift n 1)) : d ∉ T := by
  classical
  intro hdT
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
  exact hT.2.1 e he _ hdT (crosses_shift_one (hT.1 e he))

/-- For `n ≥ 4` every triangulation of the `n`-gon is nonempty (the ear `{0, 2}` is a
diagonal). -/
lemma IsTriang.nonempty {n : ℕ} (hn : 4 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriang n T) : T.Nonempty := by
  haveI : NeZero n := ⟨by omega⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  subst hne
  have hdiag : IsDiag n s(0, 2) := by
    have hval : ((2 : ZMod n) - 0).val = 2 := by
      rw [sub_zero, show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_cast,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    refine ⟨0, 2, rfl, ?_, ?_⟩ <;> omega
  obtain ⟨e, he, -⟩ := hT.2.2 _ hdiag (Finset.notMem_empty _)
  exact Finset.notMem_empty e he

/-- **The rotation bound** (Kalai, MathOverflow 114646; recorded as the "trivial" bound
`|F| ≤ C_{n-2}/2` in Ellis, arXiv:2107.06371). If `S` is a family of triangulations of the
convex `n`-gon (`n ≥ 4`) in which every two distinct members share a diagonal, then
`2 * |S| ≤ |T_n|`, where `T_n` is the set of all triangulations. Proof: rotation by one step
is a bijection of `T_n`, and a triangulation shares no diagonal with its rotation, so `S` and
its rotation are disjoint subfamilies of `T_n` of equal size. -/
theorem two_mul_ncard_le_ncard_setOf_isTriang {n : ℕ} (hn : 4 ≤ n) (S : Set (Finset (Sym2 (ZMod n))))
    (hS : ∀ T ∈ S, IsTriang n T)
    (hI : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → (T ∩ T').Nonempty) :
    2 * S.ncard ≤ {T | IsTriang n T}.ncard := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  set R : Finset (Sym2 (ZMod n)) → Finset (Sym2 (ZMod n)) := fun T => T.image (shift n 1)
    with hR
  have hRinj : Function.Injective R := Finset.image_injective (shift_injective n 1)
  have hdisj : Disjoint S (R '' S) := by
    rw [Set.disjoint_left]
    rintro T hTS ⟨T', hT'S, hRT'⟩
    have hcommon : (T ∩ T').Nonempty := by
      by_cases hTT' : T = T'
      · subst hTT'
        simpa using (hS T hTS).nonempty hn
      · exact hI T hTS T' hT'S hTT'
    obtain ⟨d, hd⟩ := hcommon
    rw [Finset.mem_inter] at hd
    have hdR : d ∈ R T' := hRT' ▸ hd.1
    exact not_mem_of_mem_image_shift_one (hS T' hT'S) hdR hd.2
  have hsub : S ∪ R '' S ⊆ {T | IsTriang n T} := by
    rintro T (hT | ⟨T', hT', rfl⟩)
    · exact hS T hT
    · exact isTriang_image_shift 1 (hS T' hT')
  calc 2 * S.ncard = S.ncard + (R '' S).ncard := by
        rw [Set.ncard_image_of_injective S hRinj]; ring
    _ = (S ∪ R '' S).ncard := (Set.ncard_union_eq hdisj).symm
    _ ≤ {T | IsTriang n T}.ncard := Set.ncard_le_ncard hsub


/-- Every member of the ear star contains `{0, 2}`, so the ear star is intersecting. -/
lemma earStar_inter_nonempty (n : ℕ) {T T' : Finset (Sym2 (ZMod n))} (hT : T ∈ earStar n)
    (hT' : T' ∈ earStar n) : (T ∩ T').Nonempty :=
  ⟨s(0, 2), Finset.mem_inter.mpr ⟨hT.2, hT'.2⟩⟩

/-! ## The Kalai–Meagher conjecture (open) -/

/-- **Kalai–Meagher conjecture (2012), bound part** (MathOverflow 114646; Ellis,
arXiv:2107.06371, Conjecture "conj:kalai"). For `n ≥ 4`, every family `S` of triangulations of
the convex `n`-gon in which every two (distinct) members share a diagonal has
`|S| ≤ C_{n-3}`. Open for `n ≥ 8`; proved for `n ≤ 7` by Olarte–Santos–Spreer–Stump
(arXiv:1710.02518). Here it is proved for `n ≤ 6` in `ncard_le_catalan_of_le_six`. The
`4 ≤ n` hypothesis keeps `n - 3` off its truncated value. -/
theorem kalai_meagher_conjecture {n : ℕ} (hn : 4 ≤ n) (S : Set (Finset (Sym2 (ZMod n))))
    (hS : ∀ T ∈ S, IsTriang n T)
    (hI : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → (T ∩ T').Nonempty) :
    S.ncard ≤ catalan (n - 3) := by
  -- Open for `n ≥ 8` (OSSS settle `n ≤ 7`; this file checks `n ≤ 6`).
  sorry

/-! ## Finite enumeration machinery

A triangulation is recorded by its indicator vector on an indexed list `dg : Fin m → Sym2 _`
of all diagonals. A Boolean branch-and-bound `hasClique` then bounds intersecting families. -/

/-- `hasClique r k l` searches `l` for `k` members at distinct positions that are pairwise
`r`-related (branching on the first member of the clique). Structural in `k`, so it reduces in
the kernel. Only its soundness direction `hasClique_of_subset` is used. -/
def hasClique {α : Type*} (r : α → α → Bool) : ℕ → List α → Bool
  | 0, _ => true
  | k + 1, l => l.tails.any fun t => match t with
    | [] => false
    | v :: vs => hasClique r k (vs.filter (r v))

/-- Equation for `hasClique` at a positive size and empty list. -/
lemma hasClique_succ_nil {α : Type*} (r : α → α → Bool) (k : ℕ) :
    hasClique r (k + 1) [] = false := by
  simp [hasClique]

/-- Equation for `hasClique` at a positive size and a cons list. -/
lemma hasClique_succ_cons {α : Type*} (r : α → α → Bool) (k : ℕ) (v : α) (vs : List α) :
    hasClique r (k + 1) (v :: vs) =
      (hasClique r k (vs.filter (r v)) || hasClique r (k + 1) vs) := by
  simp [hasClique, List.tails]

/-- Soundness of `hasClique`: a finset `I` of members of `l`, pairwise `r`-related, with at
least `k` elements forces `hasClique r k l = true`. -/
lemma hasClique_of_subset {α : Type*} [DecidableEq α] (r : α → α → Bool) :
    ∀ (k : ℕ) (l : List α) (I : Finset α), (∀ x ∈ I, x ∈ l) →
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y → r x y = true) → k ≤ I.card → hasClique r k l = true := by
  intro k
  induction k with
  | zero => intro l I _ _ _; cases l <;> simp [hasClique]
  | succ k ihk =>
    intro l
    induction l with
    | nil =>
      intro I hI _ hk
      have hempty : I = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => by simpa using hI x hx
      simp [hempty] at hk
    | cons v vs ihl =>
      intro I hI hr hk
      rw [hasClique_succ_cons, Bool.or_eq_true]
      by_cases hv : v ∈ I
      · left
        refine ihk (vs.filter (r v)) (I.erase v) (fun x hx => ?_) (fun x hx y hy hxy => ?_) ?_
        · obtain ⟨hxv, hxI⟩ := Finset.mem_erase.mp hx
          rw [List.mem_filter]
          refine ⟨?_, hr v hv x hxI (Ne.symm hxv)⟩
          rcases List.mem_cons.mp (hI x hxI) with h | h
          · exact absurd h hxv
          · exact h
        · exact hr x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
        · rw [Finset.card_erase_of_mem hv]
          omega
      · right
        refine ihl I (fun x hx => ?_) hr hk
        rcases List.mem_cons.mp (hI x hx) with h | h
        · exact absurd (h ▸ hx) hv
        · exact h

/-- Two indicator vectors share a coordinate. -/
def meets {m : ℕ} (p q : Fin m → Bool) : Bool := (List.finRange m).any fun i => p i && q i

/-- `meets` is the Boolean form of "some coordinate is set in both". -/
lemma meets_eq_true_iff {m : ℕ} (p q : Fin m → Bool) :
    meets p q = true ↔ ∃ i, p i = true ∧ q i = true := by
  simp [meets]

/-- Indicator vector of a chord family on the indexed diagonals `dg`. -/
def maskOf {n m : ℕ} (dg : Fin m → Sym2 (ZMod n)) (T : Finset (Sym2 (ZMod n))) : Fin m → Bool :=
  fun i => decide (dg i ∈ T)

/-- The chord family with indicator vector `p` on the indexed diagonals `dg`. -/
def ofMask {n m : ℕ} (dg : Fin m → Sym2 (ZMod n)) (p : Fin m → Bool) : Finset (Sym2 (ZMod n)) :=
  (Finset.univ.filter fun i => p i = true).image dg

/-- A triangulation is recovered from its indicator vector when `dg` lists every diagonal. -/
lemma ofMask_maskOf {n m : ℕ} {dg : Fin m → Sym2 (ZMod n)}
    (hsurj : ∀ d, IsDiag n d → ∃ i, dg i = d) {T : Finset (Sym2 (ZMod n))} (hT : IsTriang n T) :
    ofMask dg (maskOf dg T) = T := by
  ext d
  simp only [ofMask, maskOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hd
    obtain ⟨i, rfl⟩ := hsurj d (hT.1 d hd)
    exact ⟨i, hd, rfl⟩

/-- If `pats` contains every Boolean vector that is pairwise non-crossing and maximal on the
diagonals `dg`, then every triangulation's indicator vector lies in `pats`. -/
lemma maskOf_mem {n m : ℕ} {dg : Fin m → Sym2 (ZMod n)} {pats : List (Fin m → Bool)}
    (hdiag : ∀ i, IsDiag n (dg i)) (hsurj : ∀ d, IsDiag n d → ∃ i, dg i = d)
    (hcomplete : ∀ p : Fin m → Bool,
      (∀ i j, p i = true → p j = true → ¬ Crosses n (dg i) (dg j)) →
      (∀ i, p i = false → ∃ j, p j = true ∧ Crosses n (dg i) (dg j)) → p ∈ pats)
    {T : Finset (Sym2 (ZMod n))} (hT : IsTriang n T) : maskOf dg T ∈ pats := by
  apply hcomplete
  · intro i j hi hj
    simp only [maskOf, decide_eq_true_eq] at hi hj
    exact hT.2.1 _ hi _ hj
  · intro i hi
    simp only [maskOf, decide_eq_false_iff_not] at hi
    obtain ⟨e, he, hcross⟩ := hT.2.2 _ (hdiag i) hi
    obtain ⟨j, rfl⟩ := hsurj e (hT.1 e he)
    exact ⟨j, by simpa [maskOf] using he, hcross⟩

/-- Under the enumeration certificates, the set of triangulations is exactly the image of the
pattern list. -/
lemma setOf_isTriang_eq {n m : ℕ} {dg : Fin m → Sym2 (ZMod n)} {pats : List (Fin m → Bool)}
    (hdiag : ∀ i, IsDiag n (dg i)) (hsurj : ∀ d, IsDiag n d → ∃ i, dg i = d)
    (hcomplete : ∀ p : Fin m → Bool,
      (∀ i j, p i = true → p j = true → ¬ Crosses n (dg i) (dg j)) →
      (∀ i, p i = false → ∃ j, p j = true ∧ Crosses n (dg i) (dg j)) → p ∈ pats)
    (hpats : ∀ p ∈ pats, IsTriang n (ofMask dg p)) :
    {T | IsTriang n T} = ↑(pats.map (ofMask dg)).toFinset := by
  ext T
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map]
  constructor
  · intro hT
    exact ⟨maskOf dg T, maskOf_mem hdiag hsurj hcomplete hT, ofMask_maskOf hsurj hT⟩
  · rintro ⟨p, hp, rfl⟩
    exact hpats p hp

/-- Clique bound: if the pattern list has no `k + 1` pairwise-meeting members, then every
family of triangulations in which distinct members share a diagonal has at most `k`
members. -/
lemma ncard_le_of_hasClique_eq_false {n m : ℕ} {dg : Fin m → Sym2 (ZMod n)}
    {pats : List (Fin m → Bool)}
    (hdiag : ∀ i, IsDiag n (dg i)) (hsurj : ∀ d, IsDiag n d → ∃ i, dg i = d)
    (hcomplete : ∀ p : Fin m → Bool,
      (∀ i j, p i = true → p j = true → ¬ Crosses n (dg i) (dg j)) →
      (∀ i, p i = false → ∃ j, p j = true ∧ Crosses n (dg i) (dg j)) → p ∈ pats)
    (k : ℕ) (hcl : hasClique meets (k + 1) pats = false)
    (S : Set (Finset (Sym2 (ZMod n)))) (hS : ∀ T ∈ S, IsTriang n T)
    (hI : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → (T ∩ T').Nonempty) (hfin : S.Finite) :
    S.ncard ≤ k := by
  classical
  by_contra hlt
  push Not at hlt
  set F : Finset (Finset (Sym2 (ZMod n))) := hfin.toFinset with hF
  have hmemF : ∀ T, T ∈ F ↔ T ∈ S := fun T => Set.Finite.mem_toFinset _
  have hinj : Set.InjOn (maskOf dg) (F : Set (Finset (Sym2 (ZMod n)))) := by
    intro T hT T' hT' h
    rw [← ofMask_maskOf hsurj (hS T ((hmemF T).mp hT)),
      ← ofMask_maskOf hsurj (hS T' ((hmemF T').mp hT')), h]
  have hcard : (F.image (maskOf dg)).card = S.ncard := by
    rw [Finset.card_image_of_injOn hinj, Set.ncard_eq_toFinset_card S hfin]
  have hclique : hasClique meets (k + 1) pats = true := by
    refine hasClique_of_subset meets (k + 1) pats (F.image (maskOf dg)) ?_ ?_ (by omega)
    · intro p hp
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hp
      exact maskOf_mem hdiag hsurj hcomplete (hS T ((hmemF T).mp hT))
    · intro p hp q hq hpq
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hq
      have hTT' : T ≠ T' := fun h => hpq (h ▸ rfl)
      obtain ⟨d, hd⟩ := hI T ((hmemF T).mp hT) T' ((hmemF T').mp hT') hTT'
      rw [Finset.mem_inter] at hd
      obtain ⟨i, rfl⟩ := hsurj d ((hS T ((hmemF T).mp hT)).1 d hd.1)
      exact (meets_eq_true_iff _ _).mpr
        ⟨i, by simpa [maskOf] using hd.1, by simpa [maskOf] using hd.2⟩
  rw [hcl] at hclique
  exact Bool.false_ne_true hclique

/-! ### The 4-gon -/

/-- The 2 diagonals of the 4-gon, indexed. -/
def dg4 : Fin 2 → Sym2 (ZMod 4) :=
  ![s(0, 2), s(1, 3)]

/-- Indicator vectors of the 2 triangulations of the 4-gon (from enumeration). -/
def pats4 : List (Fin 2 → Bool) :=
  [![true, false],
   ![false, true]]

/-- Each listed chord is a diagonal of the 4-gon. -/
lemma isDiag_dg4 : ∀ i, IsDiag 4 (dg4 i) := by decide

/-- The list `dg4` contains every diagonal of the 4-gon. -/
lemma dg4_surj : ∀ d : Sym2 (ZMod 4), IsDiag 4 d → ∃ i, dg4 i = d := by decide +kernel

/-- Enumeration certificate: every maximal non-crossing indicator vector is listed. -/
lemma pats4_complete : ∀ p : Fin 2 → Bool,
    (∀ i j, p i = true → p j = true → ¬ Crosses 4 (dg4 i) (dg4 j)) →
    (∀ i, p i = false → ∃ j, p j = true ∧ Crosses 4 (dg4 i) (dg4 j)) → p ∈ pats4 := by
  decide +kernel

/-- Every listed pattern is a triangulation of the 4-gon. -/
lemma isTriang_ofMask_pats4 : ∀ p ∈ pats4, IsTriang 4 (ofMask dg4 p) := by decide +kernel

/-- No 2 listed triangulations of the 4-gon pairwise share a diagonal. -/
lemma hasClique_pats4 : hasClique meets 2 pats4 = false := by decide +kernel

/-- The triangulations of the 4-gon, as a finset. -/
def triangs4 : Finset (Finset (Sym2 (ZMod 4))) := (pats4.map (ofMask dg4)).toFinset

/-- The set of triangulations of the 4-gon is `triangs4`. -/
lemma setOf_isTriang_4 : {T | IsTriang 4 T} = ↑triangs4 :=
  setOf_isTriang_eq isDiag_dg4 dg4_surj pats4_complete isTriang_ofMask_pats4

/-- Ground truth: the 4-gon has `C_2 = 2` triangulations. -/
theorem ncard_setOf_isTriang_4 : {T | IsTriang 4 T}.ncard = catalan 2 := by
  rw [setOf_isTriang_4, Set.ncard_coe_finset]
  decide +kernel

/-- **Kalai–Meagher bound for the 4-gon**: an intersecting family of triangulations of the
4-gon has at most `C_1 = 1` members. -/
theorem ncard_le_of_4 (S : Set (Finset (Sym2 (ZMod 4)))) (hS : ∀ T ∈ S, IsTriang 4 T)
    (hI : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → (T ∩ T').Nonempty) : S.ncard ≤ catalan 1 := by
  have hbound := ncard_le_of_hasClique_eq_false isDiag_dg4 dg4_surj pats4_complete 1
    hasClique_pats4 S hS hI (Set.toFinite S)
  rw [show catalan 1 = 1 by decide +kernel]
  exact hbound

/-- The ear star of the 4-gon has `C_1 = 1` members. -/
theorem ncard_earStar_4 : (earStar 4).ncard = catalan 1 := by
  have hset : earStar 4 = ↑(triangs4.filter fun T => s(0, 2) ∈ T) := by
    have hT : ∀ T, IsTriang 4 T ↔ T ∈ triangs4 := fun T => by
      rw [← Finset.mem_coe, ← setOf_isTriang_4]
      rfl
    ext T
    simp only [earStar, Set.mem_ofPred_eq, Finset.coe_filter, hT]
  rw [hset, Set.ncard_coe_finset]
  decide +kernel

/-! ### The 5-gon -/

/-- The 5 diagonals of the 5-gon, indexed. -/
def dg5 : Fin 5 → Sym2 (ZMod 5) :=
  ![s(0, 2), s(0, 3), s(1, 3), s(1, 4), s(2, 4)]

/-- Indicator vectors of the 5 triangulations of the 5-gon (from enumeration). -/
def pats5 : List (Fin 5 → Bool) :=
  [![true, true, false, false, false],
   ![true, false, false, false, true],
   ![false, true, true, false, false],
   ![false, false, true, true, false],
   ![false, false, false, true, true]]

/-- Each listed chord is a diagonal of the 5-gon. -/
lemma isDiag_dg5 : ∀ i, IsDiag 5 (dg5 i) := by decide

/-- The list `dg5` contains every diagonal of the 5-gon. -/
lemma dg5_surj : ∀ d : Sym2 (ZMod 5), IsDiag 5 d → ∃ i, dg5 i = d := by decide +kernel

/-- Enumeration certificate: every maximal non-crossing indicator vector is listed. -/
lemma pats5_complete : ∀ p : Fin 5 → Bool,
    (∀ i j, p i = true → p j = true → ¬ Crosses 5 (dg5 i) (dg5 j)) →
    (∀ i, p i = false → ∃ j, p j = true ∧ Crosses 5 (dg5 i) (dg5 j)) → p ∈ pats5 := by
  decide +kernel

/-- Every listed pattern is a triangulation of the 5-gon. -/
lemma isTriang_ofMask_pats5 : ∀ p ∈ pats5, IsTriang 5 (ofMask dg5 p) := by decide +kernel

/-- No 3 listed triangulations of the 5-gon pairwise share a diagonal. -/
lemma hasClique_pats5 : hasClique meets 3 pats5 = false := by decide +kernel

/-- The triangulations of the 5-gon, as a finset. -/
def triangs5 : Finset (Finset (Sym2 (ZMod 5))) := (pats5.map (ofMask dg5)).toFinset

/-- The set of triangulations of the 5-gon is `triangs5`. -/
lemma setOf_isTriang_5 : {T | IsTriang 5 T} = ↑triangs5 :=
  setOf_isTriang_eq isDiag_dg5 dg5_surj pats5_complete isTriang_ofMask_pats5

/-- Ground truth: the 5-gon has `C_3 = 5` triangulations. -/
theorem ncard_setOf_isTriang_5 : {T | IsTriang 5 T}.ncard = catalan 3 := by
  rw [setOf_isTriang_5, Set.ncard_coe_finset]
  decide +kernel

/-- **Kalai–Meagher bound for the 5-gon**: an intersecting family of triangulations of the
5-gon has at most `C_2 = 2` members. -/
theorem ncard_le_of_5 (S : Set (Finset (Sym2 (ZMod 5)))) (hS : ∀ T ∈ S, IsTriang 5 T)
    (hI : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → (T ∩ T').Nonempty) : S.ncard ≤ catalan 2 := by
  have hbound := ncard_le_of_hasClique_eq_false isDiag_dg5 dg5_surj pats5_complete 2
    hasClique_pats5 S hS hI (Set.toFinite S)
  rw [show catalan 2 = 2 by decide +kernel]
  exact hbound

/-- The ear star of the 5-gon has `C_2 = 2` members. -/
theorem ncard_earStar_5 : (earStar 5).ncard = catalan 2 := by
  have hset : earStar 5 = ↑(triangs5.filter fun T => s(0, 2) ∈ T) := by
    have hT : ∀ T, IsTriang 5 T ↔ T ∈ triangs5 := fun T => by
      rw [← Finset.mem_coe, ← setOf_isTriang_5]
      rfl
    ext T
    simp only [earStar, Set.mem_ofPred_eq, Finset.coe_filter, hT]
  rw [hset, Set.ncard_coe_finset]
  decide +kernel

/-! ### The 6-gon -/

/-- The 9 diagonals of the 6-gon, indexed. -/
def dg6 : Fin 9 → Sym2 (ZMod 6) :=
  ![s(0, 2), s(0, 3), s(0, 4), s(1, 3), s(1, 4), s(1, 5), s(2, 4), s(2, 5), s(3, 5)]

/-- Indicator vectors of the 14 triangulations of the 6-gon (from enumeration). -/
def pats6 : List (Fin 9 → Bool) :=
  [![true, true, true, false, false, false, false, false, false],
   ![true, true, false, false, false, false, false, false, true],
   ![true, false, true, false, false, false, true, false, false],
   ![true, false, false, false, false, false, true, true, false],
   ![true, false, false, false, false, false, false, true, true],
   ![false, true, true, true, false, false, false, false, false],
   ![false, true, false, true, false, false, false, false, true],
   ![false, false, true, true, true, false, false, false, false],
   ![false, false, true, false, true, false, true, false, false],
   ![false, false, false, true, true, true, false, false, false],
   ![false, false, false, true, false, true, false, false, true],
   ![false, false, false, false, true, true, true, false, false],
   ![false, false, false, false, false, true, true, true, false],
   ![false, false, false, false, false, true, false, true, true]]

/-- Each listed chord is a diagonal of the 6-gon. -/
lemma isDiag_dg6 : ∀ i, IsDiag 6 (dg6 i) := by decide

/-- The list `dg6` contains every diagonal of the 6-gon. -/
lemma dg6_surj : ∀ d : Sym2 (ZMod 6), IsDiag 6 d → ∃ i, dg6 i = d := by decide +kernel

/-- Enumeration certificate: every maximal non-crossing indicator vector is listed. -/
lemma pats6_complete : ∀ p : Fin 9 → Bool,
    (∀ i j, p i = true → p j = true → ¬ Crosses 6 (dg6 i) (dg6 j)) →
    (∀ i, p i = false → ∃ j, p j = true ∧ Crosses 6 (dg6 i) (dg6 j)) → p ∈ pats6 := by
  decide +kernel

/-- Every listed pattern is a triangulation of the 6-gon. -/
lemma isTriang_ofMask_pats6 : ∀ p ∈ pats6, IsTriang 6 (ofMask dg6 p) := by decide +kernel

/-- No 6 listed triangulations of the 6-gon pairwise share a diagonal. -/
lemma hasClique_pats6 : hasClique meets 6 pats6 = false := by decide +kernel

/-- The triangulations of the 6-gon, as a finset. -/
def triangs6 : Finset (Finset (Sym2 (ZMod 6))) := (pats6.map (ofMask dg6)).toFinset

/-- The set of triangulations of the 6-gon is `triangs6`. -/
lemma setOf_isTriang_6 : {T | IsTriang 6 T} = ↑triangs6 :=
  setOf_isTriang_eq isDiag_dg6 dg6_surj pats6_complete isTriang_ofMask_pats6

/-- Ground truth: the 6-gon has `C_4 = 14` triangulations. -/
theorem ncard_setOf_isTriang_6 : {T | IsTriang 6 T}.ncard = catalan 4 := by
  rw [setOf_isTriang_6, Set.ncard_coe_finset]
  decide +kernel

/-- **Kalai–Meagher bound for the 6-gon**: an intersecting family of triangulations of the
6-gon has at most `C_3 = 5` members. -/
theorem ncard_le_of_6 (S : Set (Finset (Sym2 (ZMod 6)))) (hS : ∀ T ∈ S, IsTriang 6 T)
    (hI : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → (T ∩ T').Nonempty) : S.ncard ≤ catalan 3 := by
  have hbound := ncard_le_of_hasClique_eq_false isDiag_dg6 dg6_surj pats6_complete 5
    hasClique_pats6 S hS hI (Set.toFinite S)
  rw [show catalan 3 = 5 by decide +kernel]
  exact hbound

/-- The ear star of the 6-gon has `C_3 = 5` members. -/
theorem ncard_earStar_6 : (earStar 6).ncard = catalan 3 := by
  have hset : earStar 6 = ↑(triangs6.filter fun T => s(0, 2) ∈ T) := by
    have hT : ∀ T, IsTriang 6 T ↔ T ∈ triangs6 := fun T => by
      rw [← Finset.mem_coe, ← setOf_isTriang_6]
      rfl
    ext T
    simp only [earStar, Set.mem_ofPred_eq, Finset.coe_filter, hT]
  rw [hset, Set.ncard_coe_finset]
  decide +kernel

/-! ## Main small-case theorems -/

/-- **Kalai–Meagher conjecture for `n ≤ 6`.** For `4 ≤ n ≤ 6`, every family of triangulations
of the convex `n`-gon in which every two distinct members share a diagonal has at most
`C_{n-3}` members (the literature settles `n ≤ 7`, Olarte–Santos–Spreer–Stump,
arXiv:1710.02518). -/
theorem ncard_le_catalan_of_le_six {n : ℕ} (h4 : 4 ≤ n) (h6 : n ≤ 6)
    (S : Set (Finset (Sym2 (ZMod n)))) (hS : ∀ T ∈ S, IsTriang n T)
    (hI : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → (T ∩ T').Nonempty) :
    S.ncard ≤ catalan (n - 3) := by
  interval_cases n
  · exact ncard_le_of_4 S hS hI
  · exact ncard_le_of_5 S hS hI
  · exact ncard_le_of_6 S hS hI

/-- **The hexagon, exactly.** The largest family of pairwise diagonal-sharing triangulations of
the hexagon has `C_3 = 5` members: every such family has at most `5`, and the ear star of
`{0, 2}` attains `5`. -/
theorem hexagon_max_intersecting :
    (∀ S : Set (Finset (Sym2 (ZMod 6))), (∀ T ∈ S, IsTriang 6 T) →
      (∀ T ∈ S, ∀ T' ∈ S, T ≠ T' → (T ∩ T').Nonempty) → S.ncard ≤ 5) ∧
    ((∀ T ∈ earStar 6, IsTriang 6 T) ∧
      (∀ T ∈ earStar 6, ∀ T' ∈ earStar 6, T ≠ T' → (T ∩ T').Nonempty) ∧
      (earStar 6).ncard = 5) := by
  have h5 : catalan 3 = 5 := catalan_three
  refine ⟨fun S hS hI => h5 ▸ ncard_le_of_6 S hS hI, fun T hT => hT.1,
    fun T hT T' hT' _ => earStar_inter_nonempty 6 hT hT', h5 ▸ ncard_earStar_6⟩

/-- Non-vacuity of the rotation bound's hypotheses: the ear star of the hexagon is a nonempty
intersecting family of triangulations, and the bound reads `2 * 5 ≤ 14`. -/
example : 2 * (earStar 6).ncard ≤ {T | IsTriang 6 T}.ncard ∧ (earStar 6).Nonempty := by
  refine ⟨two_mul_ncard_le_ncard_setOf_isTriang (by norm_num) (earStar 6) (fun T hT => hT.1)
    (fun T hT T' hT' _ => earStar_inter_nonempty 6 hT hT'), ?_⟩
  refine ⟨{s(0, 2), s(0, 3), s(0, 4)}, ?_, by decide⟩
  decide

end Candidates.EKRTriangulationsSmall
