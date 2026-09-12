/-
  Erdős Problem #142 — exact comparison of bounded natural and cyclic
  three-term progression counts.
-/

import Erdos.Erdos142.AffineWindows
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos142

/-- The image of a finite set of natural numbers in the cyclic group
`ZMod p`. -/
def natCyclicImage (p : ℕ) (A : Finset ℕ) : Finset (ZMod p) :=
  A.image fun a : ℕ => (a : ZMod p)

/-- The number of oriented cyclic progressions `(x,d)` whose three terms
`x`, `x+d`, and `x+2d` lie in `B`.  The case `d = 0` is included. -/
def cyclicThreeAPCount (p : ℕ) [NeZero p] (B : Finset (ZMod p)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).product Finset.univ).filter
    (fun xd => xd.1 ∈ B ∧ xd.1 + xd.2 ∈ B ∧ xd.1 + 2 * xd.2 ∈ B) |>.card

/-- Natural ordered endpoint pairs which admit a midpoint in `A`. -/
def naturalThreeAPPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A.product A).filter fun xz => ∃ y ∈ A, xz.1 + xz.2 = 2 * y

/-- The trivial ordered natural progression pairs are exactly the diagonal. -/
def trivialThreeAPPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  A.image fun x => (x, x)

/-- The nontrivial ordered natural progression pairs have distinct endpoints. -/
def nontrivialThreeAPPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (naturalThreeAPPairs A).filter fun xz => xz.1 ≠ xz.2

/-- Membership in the natural ordered-pair family records both endpoints and
one midpoint. -/
theorem mem_naturalThreeAPPairs {A : Finset ℕ} {xz : ℕ × ℕ} :
    xz ∈ naturalThreeAPPairs A ↔
      xz.1 ∈ A ∧ xz.2 ∈ A ∧ ∃ y ∈ A, xz.1 + xz.2 = 2 * y := by
  rw [naturalThreeAPPairs, mem_filter]
  constructor
  · rintro ⟨hprod, hmid⟩
    exact ⟨(mem_product.mp hprod).1, (mem_product.mp hprod).2, hmid⟩
  · rintro ⟨hx, hz, hmid⟩
    exact ⟨mem_product.mpr ⟨hx, hz⟩, hmid⟩

/-- The natural ordered-pair count is the number of trivial progressions plus
twice the canonical unoriented nontrivial count. -/
theorem card_naturalThreeAPPairs (A : Finset ℕ) :
    (naturalThreeAPPairs A).card = A.card + 2 * threeAPCount A := by
  classical
  have htrivial :
      (naturalThreeAPPairs A).filter (fun xz => ¬xz.1 ≠ xz.2) =
        trivialThreeAPPairs A := by
    ext xz
    simp only [mem_filter, mem_naturalThreeAPPairs, not_not,
      trivialThreeAPPairs, mem_image]
    constructor
    · rcases xz with ⟨x, z⟩
      simp only [Prod.fst, Prod.snd]
      rintro ⟨⟨hx, hz, y, hy, hsum⟩, hxz⟩
      subst z
      refine ⟨y, ?_, ?_⟩
      · omega
      · have hyx : y = x := by omega
        subst y
        rfl
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨hx, hx, x, hx, by omega⟩, rfl⟩
  have htrivialCard : (trivialThreeAPPairs A).card = A.card := by
    rw [trivialThreeAPPairs, card_image_of_injective]
    intro x y hxy
    exact Prod.mk.inj hxy |>.1
  have hnontrivial :
      (nontrivialThreeAPPairs A).card = 2 * (threeAPEdges A).card := by
    let orient : ℕ × ℕ → Finset ℕ × Bool := fun xz =>
      ({xz.1, (xz.1 + xz.2) / 2, xz.2}, xz.1 < xz.2)
    have hcard := Finset.card_bij
      (s := nontrivialThreeAPPairs A)
      (t := (threeAPEdges A).product Finset.univ)
      (fun xz _ => orient xz)
      (by
        intro xz hxz
        rw [nontrivialThreeAPPairs, mem_filter] at hxz
        obtain ⟨hnat, hne⟩ := hxz
        obtain ⟨hx, hz, y, hy, hsum⟩ := mem_naturalThreeAPPairs.mp hnat
        have hmid : (xz.1 + xz.2) / 2 = y := by omega
        dsimp only [orient]
        apply mem_product.mpr
        constructor
        · rw [mem_threeAPEdges]
          refine ⟨?_, ?_, ?_⟩
          · simp only [hmid, insert_subset_iff, singleton_subset_iff]
            exact ⟨hx, hy, hz⟩
          · have hxy : xz.1 ≠ y := by omega
            have hyz : y ≠ xz.2 := by omega
            simp [hmid, hne, hxy, hyz]
          · change ¬ThreeAPFree
              (({xz.1, (xz.1 + xz.2) / 2, xz.2} : Finset ℕ) : Set ℕ)
            intro hfree
            have hxy' : xz.1 ≠ y := by omega
            apply hxy'
            apply hfree (a := xz.1) (b := y) (c := xz.2)
            · simp
            · simp only [hmid]
              simp
            · simp
            · simpa only [two_mul] using hsum
        · exact mem_univ _)
      (by
        intro a ha b hb hab
        rw [nontrivialThreeAPPairs, mem_filter] at ha hb
        obtain ⟨hana, hnea⟩ := ha
        obtain ⟨hanb, hneb⟩ := hb
        obtain ⟨hxa, hza, ya, hya, hsuma⟩ := mem_naturalThreeAPPairs.mp hana
        obtain ⟨hxb, hzb, yb, hyb, hsumb⟩ := mem_naturalThreeAPPairs.mp hanb
        have hmida : (a.1 + a.2) / 2 = ya := by omega
        have hmidb : (b.1 + b.2) / 2 = yb := by omega
        have hset : ({a.1, ya, a.2} : Finset ℕ) = {b.1, yb, b.2} := by
          simpa only [orient, hmida, hmidb] using congrArg Prod.fst hab
        have horddec : decide (a.1 < a.2) = decide (b.1 < b.2) := by
          simpa only [orient] using congrArg Prod.snd hab
        have hord : (a.1 < a.2) = (b.1 < b.2) := by
          simpa only [decide_eq_true_eq] using congrArg (fun z => z = true) horddec
        have ha_mem : a.1 ∈ ({b.1, yb, b.2} : Finset ℕ) := by
          rw [← hset]
          simp
        have hb_mem : b.1 ∈ ({a.1, ya, a.2} : Finset ℕ) := by
          rw [hset]
          simp
        have hz_mem : a.2 ∈ ({b.1, yb, b.2} : Finset ℕ) := by
          rw [← hset]
          simp
        have hw_mem : b.2 ∈ ({a.1, ya, a.2} : Finset ℕ) := by
          rw [hset]
          simp
        simp only [mem_insert, mem_singleton] at ha_mem hb_mem hz_mem hw_mem
        have horient :
            (a.1 < a.2 ∧ b.1 < b.2) ∨ (a.2 < a.1 ∧ b.2 < b.1) := by
          by_cases haorder : a.1 < a.2
          · left
            exact ⟨haorder, by simpa only [← hord] using haorder⟩
          · right
            have hborder : ¬b.1 < b.2 := by simpa only [← hord] using haorder
            exact ⟨lt_of_le_of_ne (Nat.le_of_not_gt haorder) hnea.symm,
              lt_of_le_of_ne (Nat.le_of_not_gt hborder) hneb.symm⟩
        apply Prod.ext
        · rcases horient with ⟨haorder, hborder⟩ | ⟨haorder, hborder⟩ <;>
            rcases ha_mem with h | h | h <;>
            rcases hb_mem with h' | h' | h' <;> omega
        · rcases horient with ⟨haorder, hborder⟩ | ⟨haorder, hborder⟩ <;>
            rcases hz_mem with h | h | h <;>
            rcases hw_mem with h' | h' | h' <;> omega)
      (by
        intro eb heb
        have heb' : eb.1 ∈ threeAPEdges A ∧
            eb.2 ∈ (Finset.univ : Finset Bool) :=
          mem_product.mp heb
        obtain ⟨he, -⟩ := heb'
        obtain ⟨x, q, hq, hedge⟩ := exists_ordered_threeAP_of_mem_threeAPEdges he
        by_cases hb : eb.2 = true
        · let xz : ℕ × ℕ := (x, x + 2 * q)
          have hxzmem : xz ∈ nontrivialThreeAPPairs A := by
            dsimp only [xz]
            rw [nontrivialThreeAPPairs, mem_filter]
            have hedata := mem_threeAPEdges.mp he
            have hx : x ∈ A := hedata.1 (by rw [hedge]; simp)
            have hmid : x + q ∈ A := hedata.1 (by rw [hedge]; simp)
            have hz : x + 2 * q ∈ A := hedata.1 (by rw [hedge]; simp)
            exact ⟨mem_naturalThreeAPPairs.mpr ⟨hx, hz, x + q, hmid, by omega⟩, by omega⟩
          refine ⟨xz, hxzmem, ?_⟩
          apply Prod.ext
          · dsimp only [orient, xz]
            have hdiv : (x + (x + 2 * q)) / 2 = x + q := by omega
            rw [hdiv, hedge]
          · dsimp only [orient, xz]
            rw [hb]
            exact decide_eq_true (by omega)
        · have hbfalse : eb.2 = false := Bool.eq_false_of_not_eq_true hb
          let xz : ℕ × ℕ := (x + 2 * q, x)
          have hxzmem : xz ∈ nontrivialThreeAPPairs A := by
            dsimp only [xz]
            rw [nontrivialThreeAPPairs, mem_filter]
            have hedata := mem_threeAPEdges.mp he
            have hx : x ∈ A := hedata.1 (by rw [hedge]; simp)
            have hmid : x + q ∈ A := hedata.1 (by rw [hedge]; simp)
            have hz : x + 2 * q ∈ A := hedata.1 (by rw [hedge]; simp)
            exact ⟨mem_naturalThreeAPPairs.mpr ⟨hz, hx, x + q, hmid, by omega⟩, by omega⟩
          refine ⟨xz, hxzmem, ?_⟩
          apply Prod.ext
          · dsimp only [orient, xz]
            have hdiv : (x + 2 * q + x) / 2 = x + q := by omega
            rw [hdiv, hedge]
            ext z
            simp only [mem_insert, mem_singleton]
            tauto
          · dsimp only [orient, xz]
            rw [hbfalse]
            exact decide_eq_false (by omega))
    calc
      (nontrivialThreeAPPairs A).card =
          ((threeAPEdges A).product (Finset.univ : Finset Bool)).card := hcard
      _ = (threeAPEdges A).card * 2 := by
        calc
          ((threeAPEdges A).product (Finset.univ : Finset Bool)).card =
              (threeAPEdges A).card * (Finset.univ : Finset Bool).card :=
            Finset.card_product _ _
          _ = (threeAPEdges A).card * 2 := by rw [card_univ, Fintype.card_bool]
      _ = 2 * (threeAPEdges A).card := Nat.mul_comm _ _
  rw [threeAPCount, ← htrivialCard, ← hnontrivial]
  change (naturalThreeAPPairs A).card =
    (trivialThreeAPPairs A).card + (nontrivialThreeAPPairs A).card
  rw [← htrivial]
  simpa only [nontrivialThreeAPPairs, Nat.add_comm] using
    (card_filter_add_card_filter_not
      (s := naturalThreeAPPairs A) (fun xz => xz.1 ≠ xz.2)).symm

/-- Below the modulus, membership in a cast image is detected by the canonical
natural representative. -/
theorem mem_natCyclicImage_iff_val_mem {p : ℕ} [NeZero p]
    {A : Finset ℕ} (hA : ∀ a ∈ A, a < p) (x : ZMod p) :
    x ∈ natCyclicImage p A ↔ x.val ∈ A := by
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := mem_image.mp hx
    rw [← hax, ZMod.val_natCast_of_lt (hA a ha)]
    exact ha
  · intro hx
    apply mem_image.mpr
    exact ⟨x.val, hx, ZMod.natCast_zmod_val x⟩

/-- With no wrap-around, cyclic oriented progressions in the cast image are
in bijection with natural ordered endpoint pairs. -/
theorem cyclicThreeAPCount_eq_card_naturalThreeAPPairs
    (p N : ℕ) [NeZero p] (A : Finset ℕ) (hA : A ⊆ Finset.range N)
    (hnoWrap : 2 * N < p) (hpOdd : Odd p) :
    cyclicThreeAPCount p (natCyclicImage p A) =
      (naturalThreeAPPairs A).card := by
  classical
  have hAp : ∀ a ∈ A, a < p := by
    intro a ha
    have haN : a < N := mem_range.mp (hA ha)
    omega
  let C := ((Finset.univ : Finset (ZMod p)).product Finset.univ).filter
    (fun xd => xd.1 ∈ natCyclicImage p A ∧
      xd.1 + xd.2 ∈ natCyclicImage p A ∧
      xd.1 + 2 * xd.2 ∈ natCyclicImage p A)
  let endpoints : ZMod p × ZMod p → ℕ × ℕ := fun xd =>
    (xd.1.val, (xd.1 + 2 * xd.2).val)
  have hcard := Finset.card_bij
    (s := C) (t := naturalThreeAPPairs A)
    (fun xd _ => endpoints xd)
    (by
      intro xd hxd
      dsimp only [C] at hxd
      rw [mem_filter] at hxd
      obtain ⟨-, hx, hy, hz⟩ := hxd
      let y := (xd.1 + xd.2).val
      have hxA : xd.1.val ∈ A :=
        (mem_natCyclicImage_iff_val_mem hAp xd.1).mp hx
      have hyA : y ∈ A :=
        (mem_natCyclicImage_iff_val_mem hAp (xd.1 + xd.2)).mp hy
      have hzA : (xd.1 + 2 * xd.2).val ∈ A :=
        (mem_natCyclicImage_iff_val_mem hAp (xd.1 + 2 * xd.2)).mp hz
      apply mem_naturalThreeAPPairs.mpr
      refine ⟨hxA, hzA, y, hyA, ?_⟩
      have hxN : xd.1.val < N := mem_range.mp (hA hxA)
      have hyN : y < N := mem_range.mp (hA hyA)
      have hzN : (xd.1 + 2 * xd.2).val < N := mem_range.mp (hA hzA)
      have hcast :
          ((xd.1.val + (xd.1 + 2 * xd.2).val : ℕ) : ZMod p) =
            ((2 * y : ℕ) : ZMod p) := by
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        ring
      have hval := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt (by omega),
        ZMod.val_natCast_of_lt (by omega)] at hval
      dsimp only [endpoints]
      exact hval)
    (by
      intro a ha b hb hab
      dsimp only [endpoints] at hab
      have hxval : a.1.val = b.1.val := congrArg Prod.fst hab
      have hzval : (a.1 + 2 * a.2).val = (b.1 + 2 * b.2).val :=
        congrArg Prod.snd hab
      have hx : a.1 = b.1 := by
        rw [← ZMod.natCast_zmod_val a.1, ← ZMod.natCast_zmod_val b.1, hxval]
      have hz : a.1 + 2 * a.2 = b.1 + 2 * b.2 := by
        rw [← ZMod.natCast_zmod_val (a.1 + 2 * a.2),
          ← ZMod.natCast_zmod_val (b.1 + 2 * b.2), hzval]
      have htwo : (2 : ZMod p) * a.2 = 2 * b.2 := by
        rw [hx] at hz
        exact add_left_cancel hz
      have hunit : IsUnit (2 : ZMod p) :=
        (ZMod.isUnit_iff_coprime 2 p).mpr (Nat.coprime_two_left.mpr hpOdd)
      have hd : a.2 = b.2 := hunit.mul_left_cancel htwo
      exact Prod.ext hx hd)
    (by
      intro ac hac
      let a := ac.1
      obtain ⟨ha, hc, b, hb, habc⟩ := mem_naturalThreeAPPairs.mp hac
      let xd : ZMod p × ZMod p := ((a : ZMod p), (b : ZMod p) - a)
      have haN : a < N := mem_range.mp (hA ha)
      have hbN : b < N := mem_range.mp (hA hb)
      have hcN : ac.2 < N := mem_range.mp (hA hc)
      have habcCast : (a : ZMod p) + (ac.2 : ZMod p) = 2 * (b : ZMod p) := by
        dsimp only [a]
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
          congrArg (fun n : ℕ => (n : ZMod p)) habc
      have hxd : xd ∈ C := by
        dsimp only [C]
        rw [mem_filter]
        refine ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_, ?_, ?_⟩
        · exact mem_image.mpr ⟨a, ha, rfl⟩
        · have hmid : xd.1 + xd.2 = (b : ZMod p) := by
            dsimp only [xd]
            ring
          rw [hmid]
          exact mem_image.mpr ⟨b, hb, rfl⟩
        · have hlast : xd.1 + 2 * xd.2 = (ac.2 : ZMod p) := by
            dsimp only [xd]
            linear_combination -habcCast
          rw [hlast]
          exact mem_image.mpr ⟨ac.2, hc, rfl⟩
      refine ⟨xd, hxd, ?_⟩
      apply Prod.ext
      · dsimp only [endpoints, xd]
        exact ZMod.val_natCast_of_lt (by omega)
      · dsimp only [endpoints, xd]
        have hlast : (a : ZMod p) + 2 * ((b : ZMod p) - a) =
            (ac.2 : ZMod p) := by
          linear_combination -habcCast
        rw [hlast, ZMod.val_natCast_of_lt (by omega)])
  exact hcard

/-- The exact no-wrap bridge from cyclic oriented progressions to canonical
unoriented natural progressions. -/
theorem cyclicThreeAPCount_natCyclicImage
    (p N : ℕ) [NeZero p] (A : Finset ℕ) (hA : A ⊆ Finset.range N)
    (hnoWrap : 2 * N < p) (hpOdd : Odd p) :
    cyclicThreeAPCount p (natCyclicImage p A) =
      A.card + 2 * threeAPCount A := by
  rw [cyclicThreeAPCount_eq_card_naturalThreeAPPairs p N A hA hnoWrap hpOdd,
    card_naturalThreeAPPairs]

/-- For a full interval, the ordered progression count is the sum of the
squares of the numbers of even and odd elements. -/
theorem card_naturalThreeAPPairs_range (N : ℕ) :
    (naturalThreeAPPairs (Finset.range N)).card =
      ((Finset.range N).filter Even).card ^ 2 +
        ((Finset.range N).filter (fun n => ¬Even n)).card ^ 2 := by
  classical
  let E := (Finset.range N).filter Even
  let O := (Finset.range N).filter (fun n => ¬Even n)
  have hpairs : naturalThreeAPPairs (Finset.range N) =
      E.product E ∪ O.product O := by
    ext ac
    rw [mem_union]
    constructor
    · intro hac
      obtain ⟨ha, hc, b, hb, habc⟩ := mem_naturalThreeAPPairs.mp hac
      have hevenSum : Even (ac.1 + ac.2) := ⟨b, by omega⟩
      have hsame : Even ac.1 ↔ Even ac.2 := Nat.even_add.mp hevenSum
      by_cases hea : Even ac.1
      · apply Or.inl
        apply mem_product.mpr
        exact ⟨mem_filter.mpr ⟨ha, hea⟩,
          mem_filter.mpr ⟨hc, hsame.mp hea⟩⟩
      · apply Or.inr
        apply mem_product.mpr
        exact ⟨mem_filter.mpr ⟨ha, hea⟩,
          mem_filter.mpr ⟨hc, fun hec => hea (hsame.mpr hec)⟩⟩
    · rintro (hEE | hOO)
      · obtain ⟨haE, hcE⟩ := mem_product.mp hEE
        obtain ⟨ha, hea⟩ := mem_filter.mp haE
        obtain ⟨hc, hec⟩ := mem_filter.mp hcE
        have hevenSum : Even (ac.1 + ac.2) :=
          Nat.even_add.mpr ⟨fun _ => hec, fun _ => hea⟩
        obtain ⟨b, hb⟩ := hevenSum
        have haN : ac.1 < N := mem_range.mp ha
        have hcN : ac.2 < N := mem_range.mp hc
        apply mem_naturalThreeAPPairs.mpr
        refine ⟨ha, hc, b, mem_range.mpr ?_, by omega⟩
        omega
      · obtain ⟨haO, hcO⟩ := mem_product.mp hOO
        obtain ⟨ha, hea⟩ := mem_filter.mp haO
        obtain ⟨hc, hec⟩ := mem_filter.mp hcO
        have hevenSum : Even (ac.1 + ac.2) :=
          Nat.even_add.mpr ⟨fun h => (hea h).elim, fun h => (hec h).elim⟩
        obtain ⟨b, hb⟩ := hevenSum
        have haN : ac.1 < N := mem_range.mp ha
        have hcN : ac.2 < N := mem_range.mp hc
        apply mem_naturalThreeAPPairs.mpr
        refine ⟨ha, hc, b, mem_range.mpr ?_, by omega⟩
        omega
  have hdisjoint : Disjoint (E.product E) (O.product O) := by
    rw [disjoint_left]
    intro ac hEE hOO
    obtain ⟨haE, -⟩ := mem_product.mp hEE
    obtain ⟨haO, -⟩ := mem_product.mp hOO
    exact (mem_filter.mp haO).2 (mem_filter.mp haE).2
  rw [hpairs, card_union_of_disjoint hdisjoint]
  calc
    (E.product E).card + (O.product O).card =
        E.card * E.card + O.card * O.card := by
      congr 1
      · exact Finset.card_product E E
      · exact Finset.card_product O O
    _ = ((Finset.range N).filter Even).card ^ 2 +
        ((Finset.range N).filter (fun n => ¬Even n)).card ^ 2 := by
      dsimp only [E, O]
      simp only [pow_two]

/-- At least half of all ordered endpoint pairs in `range N` have an integral
midpoint in the same interval.  This includes the `N = 0` boundary. -/
theorem sq_le_two_mul_card_naturalThreeAPPairs_range (N : ℕ) :
    N ^ 2 ≤ 2 * (naturalThreeAPPairs (Finset.range N)).card := by
  let e := ((Finset.range N).filter Even).card
  let o := ((Finset.range N).filter (fun n => ¬Even n)).card
  have heo : e + o = N := by
    simpa only [e, o, card_range] using
      card_filter_add_card_filter_not (s := Finset.range N) Even
  have hamgmInt : 2 * (e : ℤ) * (o : ℤ) ≤ (e : ℤ) ^ 2 + (o : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((e : ℤ) - (o : ℤ))]
  have hamgm : 2 * e * o ≤ e ^ 2 + o ^ 2 := by
    exact_mod_cast hamgmInt
  rw [card_naturalThreeAPPairs_range]
  dsimp only [e, o] at heo hamgm ⊢
  nlinarith

/-- The full interval cast into an odd cyclic group of modulus greater than
`2N` has at least `N²/2` oriented cyclic progressions. -/
theorem sq_le_two_mul_cyclicThreeAPCount_range
    (p N : ℕ) [NeZero p] (hnoWrap : 2 * N < p) (hpOdd : Odd p) :
    N ^ 2 ≤ 2 * cyclicThreeAPCount p (natCyclicImage p (Finset.range N)) := by
  rw [cyclicThreeAPCount_eq_card_naturalThreeAPPairs p N (Finset.range N)
    (fun _ h => h) hnoWrap hpOdd]
  exact sq_le_two_mul_card_naturalThreeAPPairs_range N

/-- Ground truth for reduction modulo `19` on the requested interval. -/
example : (7 : ZMod 19) ∈ natCyclicImage 19 (Finset.range 8) := by
  rw [natCyclicImage, mem_image]
  exact ⟨7, by simp, rfl⟩

/-- Ground truth: `range 8` has twelve unoriented nontrivial 3-APs. -/
example : threeAPCount (Finset.range 8) = 12 := by decide

/-- Ground truth: the cyclic oriented count for `range 8` inside `ZMod 19`
is `8 + 2 * 12 = 32`. -/
example : cyclicThreeAPCount 19 (natCyclicImage 19 (Finset.range 8)) = 32 := by
  decide

/-- Ground truth for the natural ordered-pair representation. -/
example : naturalThreeAPPairs {0, 1, 2} =
    ({(0, 0), (0, 2), (1, 1), (2, 0), (2, 2)} : Finset (ℕ × ℕ)) := by decide

/-- Ground truth for the diagonal representation. -/
example : trivialThreeAPPairs {0, 2} = ({(0, 0), (2, 2)} : Finset (ℕ × ℕ)) := by decide

/-- Ground truth for the nontrivial ordered-pair representation. -/
example : nontrivialThreeAPPairs {0, 1, 2} = ({(0, 2), (2, 0)} : Finset (ℕ × ℕ)) := by decide

/-- Boundary ground truth: the empty interval has no ordered progressions. -/
example : (naturalThreeAPPairs (Finset.range 0)).card = 0 := by decide

/-- Joint satisfiability check for the no-wrap and odd-modulus hypotheses at
the requested nontrivial model. -/
example : 8 ^ 2 ≤
    2 * cyclicThreeAPCount 19 (natCyclicImage 19 (Finset.range 8)) := by
  exact sq_le_two_mul_cyclicThreeAPCount_range 19 8 (by norm_num) (by norm_num)

#check @natCyclicImage
#check @cyclicThreeAPCount
#check @card_naturalThreeAPPairs
#check @cyclicThreeAPCount_eq_card_naturalThreeAPPairs
#check @cyclicThreeAPCount_natCyclicImage
#check @card_naturalThreeAPPairs_range
#check @sq_le_two_mul_card_naturalThreeAPPairs_range
#check @sq_le_two_mul_cyclicThreeAPCount_range

#print axioms card_naturalThreeAPPairs
#print axioms cyclicThreeAPCount_natCyclicImage
#print axioms card_naturalThreeAPPairs_range
#print axioms sq_le_two_mul_cyclicThreeAPCount_range

end Erdos142
