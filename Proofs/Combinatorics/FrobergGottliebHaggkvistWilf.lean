/-
# Fröberg–Gottlieb–Häggkvist: `f(S) + 1 ≤ n(S) (t(S) + 1)` and two Wilf consequences

A. Sammartano, *Numerical semigroups with large embedding dimension
satisfy Wilf's conjecture*, arXiv:1111.1863, Section 1, Proposition `where`,
cites R. Fröberg, C. Gottlieb and R. Häggkvist, *On numerical semigroups*,
Semigroup Forum 35 (1987), Theorem 22: `f(S)+1 ≤ n(S)(t(S)+1)`.
Here `f` is the Frobenius number, `n` counts semigroup elements below `f`,
`t` counts pseudo-Frobenius numbers, and `ν` counts minimal generators.
The following sentence gives Wilf's inequality when `t+1 ≤ ν`.

## Conventions

We work with `S : AddSubmonoid ℕ` and a natural number `f` with
`IsGreatest (ℕ \ S) f`; this hypothesis forces `ℕ \ S` to be nonempty and bounded,
hence `S` is a numerical semigroup different from `ℕ`.  (For `S = ℕ`, the
Frobenius number is `-1`, `n = 0` and both inequalities read `0 ≤ 0`.)  For
`S ≠ ℕ` every pseudo-Frobenius number is a positive gap (a negative `x` would need
`x + m = 0` and then `x + w_1 ∈ S` fails for the Apéry element `w_1`), so the set of
pseudo-Frobenius numbers is taken inside `ℕ`.

## Results

* `succ_frobenius_le_mul_type_succ`: [FGH, Theorem 22], `f + 1 ≤ n (t + 1)`;
* `wilf_of_type_succ_le`: Wilf's inequality when `t + 1 ≤ ν`;
* `wilf_of_type_eq_one`: Wilf's inequality for symmetric semigroups (`t = 1`);
* `type_succ_le_embeddingDimension` and
  `wilf_of_multiplicity_le_embeddingDimension_add_two`: the paper's Lemma `unfor`
  (`m - ν ≤ 2` ⟹ `t + 1 ≤ ν` ⟹ Wilf), via Apéry-set counting.

Not formalized: Corollary `frag` ([FGH], `ν ≤ 3` ⟹ Wilf) and hence Corollary
`ten` (`m ≤ 6` ⟹ Wilf).

Proof of the main inequality (injection): each gap `g ≤ f` maps to `(s, g + s)`
where `s` is the largest element of `S` with `g + s ∉ S`; then `g + s` is
pseudo-Frobenius and `s < f`, and `g ↦ (s, g + s)` is injective, so the number of
gaps is at most `n t`, while `f + 1 = n + #gaps`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.FrobergGottliebHaggkvistWilf

/-! ## Definitions -/

/-- The pseudo-Frobenius numbers of `S`: the `x ∉ S` with `x + s ∈ S` for every
nonzero `s ∈ S` (paper, Section 1; restricted to `ℕ`, see the module header). -/
def pseudoFrobenius (S : AddSubmonoid ℕ) : Set ℕ :=
  {x | x ∉ S ∧ ∀ s ∈ S, s ≠ 0 → x + s ∈ S}

/-- The type `t(S)`: the number of pseudo-Frobenius numbers. -/
noncomputable def type (S : AddSubmonoid ℕ) : ℕ := (pseudoFrobenius S).ncard

/-- `n(S) = |{s ∈ S, s < f}|` for the Frobenius number `f` of `S`. -/
noncomputable def smallElementCount (S : AddSubmonoid ℕ) (f : ℕ) : ℕ :=
  {s : ℕ | s ∈ S ∧ s < f}.ncard

/-- The minimal generators of `S`: the minimal elements of `S \ {0}` for the order
`a ≼ b ⇔ b - a ∈ S`, i.e. the nonzero elements of `S` that are not a sum of two
nonzero elements of `S`. -/
def minimalGenerators (S : AddSubmonoid ℕ) : Set ℕ :=
  {x | x ∈ S ∧ x ≠ 0 ∧ ∀ a ∈ S, ∀ b ∈ S, a + b = x → a = 0 ∨ b = 0}

/-- The embedding dimension `ν(S)`: the number of minimal generators. -/
noncomputable def embeddingDimension (S : AddSubmonoid ℕ) : ℕ :=
  (minimalGenerators S).ncard

/-! ## The Fröberg–Gottlieb–Häggkvist inequality -/

section Main

variable {S : AddSubmonoid ℕ} {f : ℕ}

/-- Every element of `ℕ \ S` is at most `f`. -/
theorem le_of_notMem (hf : IsGreatest ((S : Set ℕ)ᶜ) f) {x : ℕ} (hx : x ∉ S) : x ≤ f :=
  hf.2 hx

/-- The Frobenius number is not in `S`. -/
theorem frobenius_notMem (hf : IsGreatest ((S : Set ℕ)ᶜ) f) : f ∉ S := hf.1

open Classical in
/-- For a gap `g`, the largest `s ≤ f` with `s ∈ S` and `g + s ∉ S`. -/
noncomputable def gapLift (S : AddSubmonoid ℕ) (f g : ℕ) : ℕ :=
  Nat.findGreatest (fun s => s ∈ S ∧ g + s ∉ S) f

/-- Properties of `gapLift`: for a gap `g`, `s = gapLift S f g` lies in `S`, `s < f`,
and `g + s` is pseudo-Frobenius. -/
theorem gapLift_spec (hf : IsGreatest ((S : Set ℕ)ᶜ) f) {g : ℕ} (hg : g ∉ S) :
    gapLift S f g ∈ S ∧ gapLift S f g < f ∧ g + gapLift S f g ∈ pseudoFrobenius S := by
  classical
  have hP : gapLift S f g ∈ S ∧ g + gapLift S f g ∉ S :=
    Nat.findGreatest_spec (P := fun s => s ∈ S ∧ g + s ∉ S) (Nat.zero_le f)
      ⟨S.zero_mem, by simpa using hg⟩
  have hg0 : g ≠ 0 := fun h => hg (h ▸ S.zero_mem)
  have hle : g + gapLift S f g ≤ f := le_of_notMem hf hP.2
  refine ⟨hP.1, by omega, hP.2, fun s hs hs0 => ?_⟩
  by_contra hcon
  have hle' : g + (gapLift S f g + s) ≤ f := by
    have := le_of_notMem hf hcon
    omega
  have hnot := Nat.findGreatest_is_greatest (P := fun s => s ∈ S ∧ g + s ∉ S)
    (n := f) (k := gapLift S f g + s) (by unfold gapLift at hP ⊢; omega) (by omega)
  exact hnot ⟨S.add_mem hP.1 hs, by rwa [← add_assoc]⟩

/-- **[FGH, Theorem 22]** (arXiv:1111.1863, Proposition `where`): for a numerical
semigroup `S ≠ ℕ` with Frobenius number `f`, `f + 1 ≤ n(S) (t(S) + 1)`. -/
theorem succ_frobenius_le_mul_type_succ (hf : IsGreatest ((S : Set ℕ)ᶜ) f) :
    f + 1 ≤ smallElementCount S f * (type S + 1) := by
  classical
  set N : Finset ℕ := (Finset.range f).filter (· ∈ S) with hNdef
  set G : Finset ℕ := (Finset.range (f + 1)).filter (· ∉ S) with hGdef
  set P : Finset ℕ := (Finset.range (f + 1)).filter (· ∈ pseudoFrobenius S) with hPdef
  have hN : smallElementCount S f = N.card := by
    rw [smallElementCount, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [N, and_comm]
  have hP : type S = P.card := by
    rw [type, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, P]
    constructor
    · intro hx
      exact ⟨Nat.lt_succ_of_le (le_of_notMem hf hx.1), hx⟩
    · exact fun hx => hx.2
  have hsplit : f + 1 = N.card + G.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.range (f + 1)) (fun x => x ∈ S)
    rw [Finset.card_range] at h
    rw [← h]
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, N]
    constructor
    · rintro ⟨hx, hxS⟩
      refine ⟨?_, hxS⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hxS) (frobenius_notMem hf)
    · rintro ⟨hx, hxS⟩
      exact ⟨by omega, hxS⟩
  have hinj : G.card ≤ (N ×ˢ P).card := by
    refine Finset.card_le_card_of_injOn (fun g => (gapLift S f g, g + gapLift S f g)) ?_ ?_
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, G] at hg
      obtain ⟨h1, h2, h3⟩ := gapLift_spec hf hg.2
      simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_range, Set.mem_prod,
        Set.mem_ofPred_eq, N, P]
      exact ⟨⟨h2, h1⟩, Nat.lt_succ_of_le (le_of_notMem hf h3.1), h3⟩
    · intro g _ g' _ hgg
      simp only [Prod.mk.injEq] at hgg
      omega
  rw [Finset.card_product] at hinj
  rw [hN, hP, hsplit]
  nlinarith

/-- Every natural number above the Frobenius number lies in `S`. -/
theorem mem_of_lt (hf : IsGreatest ((S : Set ℕ)ᶜ) f) {x : ℕ} (hx : f < x) : x ∈ S := by
  by_contra h
  have := le_of_notMem hf h
  omega

/-- The minimal generators of `S` are at most `2 f + 2`, so there are finitely many. -/
theorem minimalGenerators_finite (hf : IsGreatest ((S : Set ℕ)ᶜ) f) :
    (minimalGenerators S).Finite := by
  refine (Set.finite_Iic (2 * f + 2)).subset fun x hx => ?_
  simp only [Set.mem_Iic]
  by_contra hlt
  have hsplit := hx.2.2 (f + 1) (mem_of_lt hf (by omega)) (x - (f + 1))
    (mem_of_lt hf (by omega)) (by omega)
  omega

/-- A numerical semigroup `S ≠ ℕ` has embedding dimension at least `2`: the
multiplicity `m` and the least element of `S` not divisible by `m` are distinct
minimal generators. -/
theorem two_le_embeddingDimension (hf : IsGreatest ((S : Set ℕ)ᶜ) f) :
    2 ≤ embeddingDimension S := by
  classical
  have hex : ∃ m, 0 < m ∧ m ∈ S := ⟨f + 1, by omega, mem_of_lt hf (by omega)⟩
  set m := Nat.find hex with hmdef
  have hm : 0 < m ∧ m ∈ S := Nat.find_spec hex
  have hmmin : ∀ k, 0 < k → k < m → k ∉ S := fun k hk hkm hkS =>
    Nat.find_min hex hkm ⟨hk, hkS⟩
  have hm1 : m ≠ 1 := by
    intro h1
    have hall : ∀ n, n ∈ S := fun n => by
      induction n with
      | zero => exact S.zero_mem
      | succ n ih => exact S.add_mem ih (h1 ▸ hm.2)
    exact frobenius_notMem hf (hall f)
  have hex2 : ∃ x, x ∈ S ∧ ¬ m ∣ x := by
    by_cases h : m ∣ f + 1
    · refine ⟨f + 2, mem_of_lt hf (by omega), fun h2 => hm1 (Nat.dvd_one.mp ?_)⟩
      exact (Nat.dvd_add_right h).mp h2
    · exact ⟨f + 1, mem_of_lt hf (by omega), h⟩
  set x := Nat.find hex2 with hxdef
  have hx : x ∈ S ∧ ¬ m ∣ x := Nat.find_spec hex2
  have hxmin : ∀ k, k < x → k ∈ S → m ∣ k := fun k hk hkS => by
    by_contra hdvd
    exact Nat.find_min hex2 hk ⟨hkS, hdvd⟩
  have hmgen : m ∈ minimalGenerators S := by
    refine ⟨hm.2, hm.1.ne', fun a ha b hb hab => ?_⟩
    by_contra hcon
    push Not at hcon
    exact hmmin a (Nat.pos_of_ne_zero hcon.1) (by omega) ha
  have hx0 : x ≠ 0 := fun h0 => hx.2 (h0 ▸ dvd_zero m)
  have hxgen : x ∈ minimalGenerators S := by
    refine ⟨hx.1, hx0, fun a ha b hb hab => ?_⟩
    by_contra hcon
    push Not at hcon
    have hda := hxmin a (by omega) ha
    have hdb := hxmin b (by omega) hb
    exact hx.2 (hab ▸ dvd_add hda hdb)
  have hne : m ≠ x := fun h => hx.2 (h ▸ dvd_refl m)
  have hsub : ({m, x} : Set ℕ) ⊆ minimalGenerators S := by
    intro y hy
    rcases hy with rfl | rfl
    · exact hmgen
    · exact hxgen
  have hcard := Set.ncard_le_ncard hsub (minimalGenerators_finite hf)
  rwa [Set.ncard_pair hne] at hcard

/-- Wilf's inequality `f + 1 ≤ n(S) ν(S)` holds whenever `t(S) + 1 ≤ ν(S)`
(arXiv:1111.1863, the sentence after Proposition `where`). -/
theorem wilf_of_type_succ_le (hf : IsGreatest ((S : Set ℕ)ᶜ) f)
    (ht : type S + 1 ≤ embeddingDimension S) :
    f + 1 ≤ smallElementCount S f * embeddingDimension S :=
  (succ_frobenius_le_mul_type_succ hf).trans (Nat.mul_le_mul_left _ ht)

/-- Wilf's inequality holds for symmetric numerical semigroups, i.e. those of type
`t(S) = 1` (using `ν(S) ≥ 2` for `S ≠ ℕ`). -/
theorem wilf_of_type_eq_one (hf : IsGreatest ((S : Set ℕ)ᶜ) f) (ht : type S = 1) :
    f + 1 ≤ smallElementCount S f * embeddingDimension S :=
  wilf_of_type_succ_le hf (by rw [ht]; exact two_le_embeddingDimension hf)

end Main

/-! ## Lemma `unfor`: Wilf's inequality when `m(S) - ν(S) ≤ 2`

Following the paper, write `Ap(S) = {w ∈ S, w - m ∉ S}`.  Its nonzero part `A` has
at most `m - 1` elements (distinct nonzero residues mod `m`), contains the
minimal generators other than `m`, and `x ↦ x + m` maps the pseudo-Frobenius
numbers into the elements of `A` that are maximal for `≼`.  Every summand of a
non-generator of `A` is a non-maximal element of `A`; when at most two elements
of `A` are non-generators this yields enough non-maximal elements to force
`t(S) ≤ ν(S) - 1`. -/

section Unfor

variable {S : AddSubmonoid ℕ} {f m : ℕ}

/-- The nonzero Apéry elements `{w ∈ S, m ≤ w, w - m ∉ S}` of `S` with respect to
`m`, as a finset (they are at most `f + m`). -/
noncomputable def aperyPos (S : AddSubmonoid ℕ) (f m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (f + m + 1)).filter fun w => w ∈ S ∧ m ≤ w ∧ w - m ∉ S

/-- Membership in `aperyPos`. -/
theorem mem_aperyPos (hf : IsGreatest ((S : Set ℕ)ᶜ) f) {w : ℕ} :
    w ∈ aperyPos S f m ↔ w ∈ S ∧ m ≤ w ∧ w - m ∉ S := by
  classical
  unfold aperyPos
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have := le_of_notMem hf h.2.2
    exact ⟨by omega, h⟩

/-- `t(S)` is the number of pseudo-Frobenius numbers up to `f`. -/
theorem type_eq_card (hf : IsGreatest ((S : Set ℕ)ᶜ) f) [DecidablePred (· ∈ pseudoFrobenius S)] :
    type S = ((Finset.range (f + 1)).filter (· ∈ pseudoFrobenius S)).card := by
  rw [type, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
  constructor
  · intro hx
    exact ⟨Nat.lt_succ_of_le (le_of_notMem hf hx.1), hx⟩
  · exact fun hx => hx.2

/-- Multiples of an element of `S` lie in `S`. -/
theorem mul_mem_of_mem {m : ℕ} (hm : m ∈ S) (k : ℕ) : k * m ∈ S := by
  have := S.nsmul_mem hm k
  rwa [smul_eq_mul] at this

/-- `|Ap(S) \ {0}| ≤ m - 1`: the residue mod `m` is injective on `aperyPos` and
never `0`. -/
theorem card_aperyPos_le (hf : IsGreatest ((S : Set ℕ)ᶜ) f)
    (hm : IsLeast {x | x ∈ S ∧ 0 < x} m) : (aperyPos S f m).card ≤ m - 1 := by
  have hm0 : 0 < m := hm.1.2
  have key : ∀ w ∈ aperyPos S f m, ∀ w' ∈ aperyPos S f m, w < w' → w % m = w' % m → False := by
    intro w hw w' hw' hlt hmod
    rw [mem_aperyPos hf] at hw hw'
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod.symm)
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk; omega
      · exact h0
    have hmem := S.add_mem hw.1 (mul_mem_of_mem hm.1.1 (k - 1))
    have heq : w + (k - 1) * m = w' - m := by
      have : m * k = m * (k - 1) + m := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hk1]
      rw [mul_comm (k - 1) m]
      omega
    rw [heq] at hmem
    exact hw'.2.2 hmem
  have hrange : Set.MapsTo (· % m) (aperyPos S f m : Set ℕ) ((Finset.range m).erase 0 : Finset ℕ) := by
    intro w hw
    simp only [Finset.coe_erase, Finset.coe_range, Set.mem_sdiff, Set.mem_Iio,
      Set.mem_singleton_iff]
    refine ⟨Nat.mod_lt _ hm0, fun h0 => ?_⟩
    have hw' := (mem_aperyPos hf).1 (Finset.mem_coe.1 hw)
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    have hmem := mul_mem_of_mem hm.1.1 (k - 1)
    have heq : (k - 1) * m = w - m := by
      rw [hk, mul_comm (k - 1) m, Nat.mul_sub_one]
    rw [heq] at hmem
    exact hw'.2.2 hmem
  have hcard := Finset.card_le_card_of_injOn (· % m) hrange (by
    intro w hw w' hw' hmod
    rcases lt_trichotomy w w' with h | h | h
    · exact (key w hw w' hw' h hmod).elim
    · exact h
    · exact (key w' hw' w hw h hmod.symm).elim)
  rwa [Finset.card_erase_of_mem (by simpa using hm0), Finset.card_range] at hcard

/-- The multiplicity `m` is a minimal generator. -/
theorem mem_minimalGenerators_of_isLeast (hm : IsLeast {x | x ∈ S ∧ 0 < x} m) :
    m ∈ minimalGenerators S := by
  refine ⟨hm.1.1, hm.1.2.ne', fun a ha b hb hab => ?_⟩
  by_contra hcon
  push Not at hcon
  have := hm.2 ⟨ha, Nat.pos_of_ne_zero hcon.1⟩
  omega

/-- A minimal generator other than `m` is a nonzero Apéry element
(paper, Proposition [Br, Lemma 3.2](i)). -/
theorem mem_aperyPos_of_mem_minimalGenerators (hf : IsGreatest ((S : Set ℕ)ᶜ) f)
    (hm : IsLeast {x | x ∈ S ∧ 0 < x} m) {x : ℕ} (hx : x ∈ minimalGenerators S)
    (hxm : x ≠ m) : x ∈ aperyPos S f m := by
  have hmx : m ≤ x := hm.2 ⟨hx.1, Nat.pos_of_ne_zero hx.2.1⟩
  refine (mem_aperyPos hf).2 ⟨hx.1, hmx, fun hsub => ?_⟩
  rcases hx.2.2 m hm.1.1 (x - m) hsub (by omega) with h | h
  · exact hm.1.2.ne' h
  · omega

/-- `w` is a non-maximal nonzero Apéry element: `w ≺ w + s` for some nonzero `s ∈ S`
with `w + s` again a nonzero Apéry element. -/
def IsNonMaximal (S : AddSubmonoid ℕ) (f m w : ℕ) : Prop :=
  w ∈ aperyPos S f m ∧ ∃ s ∈ S, s ≠ 0 ∧ w + s ∈ aperyPos S f m

/-- If `u ∈ Ap(S) \ {0}` is not a minimal generator, it is a sum `a + b` of two
non-maximal nonzero Apéry elements (paper, Lemma `easy` = [FGH, Lemma 6]). -/
theorem exists_nonMaximal_add (hf : IsGreatest ((S : Set ℕ)ᶜ) f)
    (hm : IsLeast {x | x ∈ S ∧ 0 < x} m) {u : ℕ} (hu : u ∈ aperyPos S f m)
    (hgen : u ∉ minimalGenerators S) :
    ∃ a b, IsNonMaximal S f m a ∧ IsNonMaximal S f m b ∧ a + b = u := by
  have hu' := (mem_aperyPos hf).1 hu
  have hu0 : u ≠ 0 := by have := hm.1.2; omega
  have hdec : ∃ a ∈ S, ∃ b ∈ S, a + b = u ∧ a ≠ 0 ∧ b ≠ 0 := by
    by_contra hno
    apply hgen
    refine ⟨hu'.1, hu0, fun a ha b hb hab => ?_⟩
    by_contra hcon
    push Not at hcon
    exact hno ⟨a, ha, b, hb, hab, hcon.1, hcon.2⟩
  obtain ⟨a, ha, b, hb, hab, ha0, hb0⟩ := hdec
  -- a summand `a` of `u` with cofactor `b` is a non-maximal Apéry element
  have summand : ∀ a ∈ S, ∀ b ∈ S, a + b = u → a ≠ 0 → b ≠ 0 → IsNonMaximal S f m a := by
    intro a ha b hb hab ha0 hb0
    have hma : m ≤ a := hm.2 ⟨ha, Nat.pos_of_ne_zero ha0⟩
    have hA : a ∈ aperyPos S f m := by
      refine (mem_aperyPos hf).2 ⟨ha, hma, fun hsub => hu'.2.2 ?_⟩
      have := S.add_mem hsub hb
      rwa [show a - m + b = u - m by omega] at this
    exact ⟨hA, b, hb, hb0, hab ▸ hu⟩
  exact ⟨a, b, summand a ha b hb hab ha0 hb0,
    summand b hb a ha (by rw [add_comm]; exact hab) hb0 ha0, hab⟩

/-- `x ↦ x + m` maps pseudo-Frobenius numbers to maximal nonzero Apéry elements
(paper, Proposition [Br, Lemma 3.2](ii), one inclusion). -/
theorem add_mem_aperyPos_of_mem_pseudoFrobenius (hf : IsGreatest ((S : Set ℕ)ᶜ) f)
    (hm : IsLeast {x | x ∈ S ∧ 0 < x} m) {x : ℕ} (hx : x ∈ pseudoFrobenius S) :
    x + m ∈ aperyPos S f m ∧ ¬ IsNonMaximal S f m (x + m) := by
  have hxm : x + m ∈ S := hx.2 m hm.1.1 hm.1.2.ne'
  refine ⟨(mem_aperyPos hf).2 ⟨hxm, by omega, by simpa using hx.1⟩, ?_⟩
  rintro ⟨_, s, hs, hs0, hA⟩
  have hA' := (mem_aperyPos hf).1 hA
  apply hA'.2.2
  rw [show x + m + s - m = x + s by omega]
  exact hx.2 s hs hs0

/-- **Lemma `unfor`** (arXiv:1111.1863): if `m(S) - ν(S) ≤ 2` (stated without
truncated subtraction as `m ≤ ν + 2`), then `t(S) + 1 ≤ ν(S)`. -/
theorem type_succ_le_embeddingDimension (hf : IsGreatest ((S : Set ℕ)ᶜ) f)
    (hm : IsLeast {x | x ∈ S ∧ 0 < x} m) (hmν : m ≤ embeddingDimension S + 2) :
    type S + 1 ≤ embeddingDimension S := by
  classical
  set A := aperyPos S f m with hAdef
  set N := A.filter (IsNonMaximal S f m) with hNdef
  have hfin := minimalGenerators_finite hf
  set Gall := hfin.toFinset with hGall
  set G := Gall.erase m with hGdef
  have hGcard : G.card + 1 = embeddingDimension S := by
    rw [embeddingDimension, Set.ncard_eq_toFinset_card _ hfin, ← hGall, hGdef,
      Finset.card_erase_add_one]
    exact hfin.mem_toFinset.2 (mem_minimalGenerators_of_isLeast hm)
  have hGA : G ⊆ A := by
    intro x hx
    rw [hGdef, Finset.mem_erase, hGall, Set.Finite.mem_toFinset] at hx
    exact mem_aperyPos_of_mem_minimalGenerators hf hm hx.2 hx.1
  have hNA : N ⊆ A := Finset.filter_subset _ _
  -- the pseudo-Frobenius numbers inject into the maximal elements `A \ N`
  have hPF : type S ≤ (A \ N).card := by
    rw [type_eq_card hf]
    refine Finset.card_le_card_of_injOn (· + m) (fun x hx => ?_) (fun x _ y _ hxy => by
      simpa using hxy)
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
    obtain ⟨h1, h2⟩ := add_mem_aperyPos_of_mem_pseudoFrobenius hf hm hx.2
    simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, hNdef, Finset.mem_filter]
    exact ⟨h1, fun h => h2 h.2⟩
  have hAN : (A \ N).card + N.card = A.card := Finset.card_sdiff_add_card_eq_card hNA
  have hAG : (A \ G).card + G.card = A.card := Finset.card_sdiff_add_card_eq_card hGA
  have hAcard : A.card ≤ m - 1 := card_aperyPos_le hf hm
  -- non-generators of `A` produce non-maximal elements
  have hnongen : ∀ u ∈ A \ G, u ∈ A ∧ u ∉ minimalGenerators S := by
    intro u hu
    rw [Finset.mem_sdiff, hGdef, Finset.mem_erase, hGall, Set.Finite.mem_toFinset] at hu
    refine ⟨hu.1, fun hgen => hu.2 ⟨fun hum => ?_, hgen⟩⟩
    have := (mem_aperyPos hf).1 hu.1
    rw [hum, Nat.sub_self] at this
    exact this.2.2 S.zero_mem
  have hN1 : 1 ≤ (A \ G).card → 1 ≤ N.card := by
    intro h
    obtain ⟨u, hu⟩ := Finset.card_pos.1 h
    obtain ⟨huA, hug⟩ := hnongen u hu
    obtain ⟨a, b, ha, hb, hab⟩ := exists_nonMaximal_add hf hm huA hug
    exact Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨ha.1, ha⟩⟩
  have hN2 : 2 ≤ (A \ G).card → 2 ≤ N.card := by
    intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h
    obtain ⟨huA, hug⟩ := hnongen u hu
    obtain ⟨hvA, hvg⟩ := hnongen v hv
    obtain ⟨a, b, ha, hb, hab⟩ := exists_nonMaximal_add hf hm huA hug
    obtain ⟨c, d, hc, hd, hcd⟩ := exists_nonMaximal_add hf hm hvA hvg
    have memN : ∀ x, IsNonMaximal S f m x → x ∈ N := fun x hx =>
      Finset.mem_filter.2 ⟨hx.1, hx⟩
    refine Finset.one_lt_card.2 ?_
    by_cases hab' : a = b
    · by_cases hcd' : c = d
      · exact ⟨a, memN a ha, c, memN c hc, fun hac => huv (by omega)⟩
      · exact ⟨c, memN c hc, d, memN d hd, hcd'⟩
    · exact ⟨a, memN a ha, b, memN b hb, hab'⟩
  have hm1 : 1 ≤ m := hm.1.2
  omega

/-- **Lemma `unfor`** (arXiv:1111.1863): every numerical semigroup with
`m(S) - ν(S) ≤ 2` (i.e. `m ≤ ν + 2`) satisfies Wilf's inequality
`f(S) + 1 ≤ n(S) ν(S)`. -/
theorem wilf_of_multiplicity_le_embeddingDimension_add_two (hf : IsGreatest ((S : Set ℕ)ᶜ) f)
    (hm : IsLeast {x | x ∈ S ∧ 0 < x} m) (hmν : m ≤ embeddingDimension S + 2) :
    f + 1 ≤ smallElementCount S f * embeddingDimension S :=
  wilf_of_type_succ_le hf (type_succ_le_embeddingDimension hf hm hmν)

end Unfor

/-! ## Examples on the paper's examples

`closure_eq_of_step` identifies an explicitly described submonoid with the
submonoid generated by a set, so the examples below are the semigroups
`⟨3, 5⟩`, `⟨3, 4, 5⟩` and `⟨7, 8, 10, 19⟩` (the last is the paper's Example after
Lemma `unfor`, with `t = ν = 4`). -/

/-- If every nonzero `x ∈ S` has a positive generator `g ≤ x` with `x - g ∈ S`,
then `S` is generated by `gens`. -/
theorem closure_eq_of_step (S : AddSubmonoid ℕ) (gens : Set ℕ) (hgens : gens ⊆ S)
    (hstep : ∀ x ∈ S, x ≠ 0 → ∃ g ∈ gens, 0 < g ∧ g ≤ x ∧ x - g ∈ S) :
    AddSubmonoid.closure gens = S := by
  refine le_antisymm (AddSubmonoid.closure_le.2 hgens) fun x hx => ?_
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · exact AddSubmonoid.zero_mem _
    · obtain ⟨g, hg, hg0, hgx, hxg⟩ := hstep x hx hpos.ne'
      have hrec := ih (x - g) (by omega) hxg
      have hsum := AddSubmonoid.add_mem _ hrec (AddSubmonoid.subset_closure hg)
      rwa [Nat.sub_add_cancel hgx] at hsum

/-- The numerical semigroup `⟨3, 5⟩ = ℕ \ {1, 2, 4, 7}`. -/
def S35 : AddSubmonoid ℕ where
  carrier := {x | x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 4 ∧ x ≠ 7}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega
  zero_mem' := by simp

/-- Membership in `S35`. -/
theorem mem_S35 {x : ℕ} : x ∈ S35 ↔ x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 4 ∧ x ≠ 7 := Iff.rfl

example : AddSubmonoid.closure {3, 5} = S35 := by
  refine closure_eq_of_step _ _ (fun x hx => ?_) fun x hx hx0 => ?_
  · rcases hx with rfl | rfl <;> simp [mem_S35]
  · rw [mem_S35] at hx
    by_cases h3 : x - 3 ∈ S35 ∧ 3 ≤ x
    · exact ⟨3, by simp, by omega, h3.2, h3.1⟩
    · refine ⟨5, by simp, by omega, ?_, ?_⟩ <;> rw [mem_S35] at h3 <;> [omega; (rw [mem_S35]; omega)]

/-- The Frobenius number of `⟨3, 5⟩` is `7`. -/
theorem isGreatest_compl_S35 : IsGreatest ((S35 : Set ℕ)ᶜ) 7 := by
  refine ⟨by simp [mem_S35], fun x hx => ?_⟩
  simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_S35] at hx
  omega

example : pseudoFrobenius S35 = {7} := by
  ext x
  simp only [pseudoFrobenius, mem_S35, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hs⟩
    have h3 := hs 3 (by omega) (by omega)
    have h5 := hs 5 (by omega) (by omega)
    omega
  · rintro rfl
    exact ⟨by omega, fun s _ hs0 => by omega⟩

/-- `⟨3, 5⟩` is symmetric: its type is `1`. -/
theorem type_S35 : type S35 = 1 := by
  have h : pseudoFrobenius S35 = {7} := by
    ext x
    simp only [pseudoFrobenius, mem_S35, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hs⟩
      have h3 := hs 3 (by omega) (by omega)
      have h5 := hs 5 (by omega) (by omega)
      omega
    · rintro rfl
      exact ⟨by omega, fun s _ hs0 => by omega⟩
  rw [type, h, Set.ncard_singleton]

example : smallElementCount S35 7 = 4 := by
  have h : {s : ℕ | s ∈ S35 ∧ s < 7} = ↑({0, 3, 5, 6} : Finset ℕ) := by
    ext x
    simp only [mem_S35, Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [smallElementCount, h, Set.ncard_coe_finset]
  rfl

/-- `ν(⟨3, 5⟩) = 2`. -/
theorem embeddingDimension_S35 : embeddingDimension S35 = 2 := by
  have h : minimalGenerators S35 = ↑({3, 5} : Finset ℕ) := by
    ext x
    simp only [minimalGenerators, mem_S35, Set.mem_ofPred_eq, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hx0, hsum⟩
      by_contra hne
      by_cases h10 : x = 10
      · have h5 := hsum 5 (by omega) 5 (by omega) (by omega)
        omega
      · have h3 := hsum 3 (by omega) (x - 3) (by omega) (by omega)
        omega
    · intro hx
      refine ⟨by omega, by omega, fun a ha b hb hab => ?_⟩
      omega
  rw [embeddingDimension, h, Set.ncard_coe_finset]
  rfl

/-- The paper's example `⟨7, 8, 10, 19⟩ = {0, 7, 8, 10} ∪ [14, ∞)`. -/
def S7 : AddSubmonoid ℕ where
  carrier := {x | x = 0 ∨ x = 7 ∨ x = 8 ∨ x = 10 ∨ 14 ≤ x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega
  zero_mem' := by simp

/-- Membership in `S7`. -/
theorem mem_S7 {x : ℕ} : x ∈ S7 ↔ x = 0 ∨ x = 7 ∨ x = 8 ∨ x = 10 ∨ 14 ≤ x := Iff.rfl

example : AddSubmonoid.closure {7, 8, 10, 19} = S7 := by
  refine closure_eq_of_step _ _ (fun x hx => ?_) fun x hx hx0 => ?_
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    exact mem_S7.2 (by omega)
  · rw [mem_S7] at hx
    by_cases h7 : x - 7 ∈ S7 ∧ 7 ≤ x
    · exact ⟨7, by simp, by omega, h7.2, h7.1⟩
    by_cases h8 : x - 8 ∈ S7 ∧ 8 ≤ x
    · exact ⟨8, by simp, by omega, h8.2, h8.1⟩
    by_cases h10 : x - 10 ∈ S7 ∧ 10 ≤ x
    · exact ⟨10, by simp, by omega, h10.2, h10.1⟩
    rw [mem_S7] at h7 h8 h10
    refine ⟨19, by simp, by omega, by omega, ?_⟩
    rw [mem_S7]
    omega

/-- The Frobenius number of `⟨7, 8, 10, 19⟩` is `13`. -/
theorem isGreatest_compl_S7 : IsGreatest ((S7 : Set ℕ)ᶜ) 13 := by
  refine ⟨by simp [mem_S7], fun x hx => ?_⟩
  simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_S7] at hx
  omega

/-- The paper: `t(⟨7, 8, 10, 19⟩) = 4` (pseudo-Frobenius numbers `9, 11, 12, 13`). -/
example : pseudoFrobenius S7 = ↑({9, 11, 12, 13} : Finset ℕ) ∧ type S7 = 4 := by
  have h : pseudoFrobenius S7 = ↑({9, 11, 12, 13} : Finset ℕ) := by
    ext x
    simp only [pseudoFrobenius, mem_S7, Set.mem_ofPred_eq, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hs⟩
      have h7 := hs 7 (by omega) (by omega)
      have h8 := hs 8 (by omega) (by omega)
      have h10 := hs 10 (by omega) (by omega)
      omega
    · intro hx
      exact ⟨by omega, fun s hs hs0 => by omega⟩
  refine ⟨h, ?_⟩
  rw [type, h, Set.ncard_coe_finset]
  rfl

/-- The paper: `ν(⟨7, 8, 10, 19⟩) = 4`. -/
example : embeddingDimension S7 = 4 := by
  have h : minimalGenerators S7 = ↑({7, 8, 10, 19} : Finset ℕ) := by
    ext x
    simp only [minimalGenerators, mem_S7, Set.mem_ofPred_eq, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hx0, hsum⟩
      by_contra hne
      by_cases h16 : x = 16
      · have := hsum 8 (by omega) 8 (by omega) (by omega)
        omega
      by_cases h18 : x = 18
      · have := hsum 8 (by omega) 10 (by omega) (by omega)
        omega
      by_cases h20 : x = 20
      · have := hsum 10 (by omega) 10 (by omega) (by omega)
        omega
      have := hsum 7 (by omega) (x - 7) (by omega) (by omega)
      omega
    · intro hx
      refine ⟨by omega, by omega, fun a ha b hb hab => ?_⟩
      omega
  rw [embeddingDimension, h, Set.ncard_coe_finset]
  rfl

/-- The paper: `n(⟨7, 8, 10, 19⟩) = 4` (elements `0, 7, 8, 10` below `f = 13`). -/
example : smallElementCount S7 13 = 4 := by
  have h : {s : ℕ | s ∈ S7 ∧ s < 13} = ↑({0, 7, 8, 10} : Finset ℕ) := by
    ext x
    simp only [mem_S7, Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [smallElementCount, h, Set.ncard_coe_finset]
  rfl

/-! ## the main theorems instantiated at the examples -/

/-- The multiplicity of `⟨3, 5⟩` is `3`. -/
theorem isLeast_S35 : IsLeast {x | x ∈ S35 ∧ 0 < x} 3 := by
  refine ⟨⟨mem_S35.2 (by omega), by omega⟩, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, mem_S35] at hx
  omega

/-- [FGH, Theorem 22] at the paper's example: `13 + 1 ≤ 4 · (4 + 1)`. -/
example : 13 + 1 ≤ smallElementCount S7 13 * (type S7 + 1) :=
  succ_frobenius_le_mul_type_succ isGreatest_compl_S7

/-- The symmetric case at `⟨3, 5⟩`: `7 + 1 ≤ 4 · 2`. -/
example : 7 + 1 ≤ smallElementCount S35 7 * embeddingDimension S35 :=
  wilf_of_type_eq_one isGreatest_compl_S35 type_S35

/-- Lemma `unfor` at `⟨3, 5⟩` (`m = 3 ≤ ν + 2 = 4`). -/
example : type S35 + 1 ≤ embeddingDimension S35 :=
  type_succ_le_embeddingDimension isGreatest_compl_S35 isLeast_S35
    (by rw [embeddingDimension_S35]; omega)

end Candidates.FrobergGottliebHaggkvistWilf
