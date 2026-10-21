/-
# A064414 — Kleinwaks: every j divides some term of every Fibonacci-type sequence

## OEIS source (pulled with `oeis show A064414`, retrieved 2026-10-21)

```
NAME:     Numbers that divide at least one term in every Fibonacci sequence.
TERMS:    1,2,3,4,6,7,9,14,23,27,43,49,67,81,83,86,98,103,127,134,163,167,
          206,223,227,243,254,283,326,343,367,383,443,446,463,467,487,503,...
KEYWORDS: easy,nonn,nice
COMMENT (previous name — the definition used here):
  Fix a > 0, b > 0, k > 0 and define G_1 = a, G_2 = b, G_k = G_(k-1) + G_(k-2);
  sequence gives m such that for any (a,b), some G_k is divisible by m.
COMMENT (the conjecture):
  From _Logan J. Kleinwaks_, Oct 29 2017: (Start)
  The squares of this sequence are the squares in A232656.
  Conjecture: these are the numbers j such that j^2 = Sum_{d|j} phi(d)*A001177(d),
  where phi = Euler's totient function (A000010). See A232656. (End)
```

A232656 (number of residue pairs mod `n` whose Fibonacci-like orbit contains
zero) carries the companion formula, conjectured by Kleinwaks (Oct 28 2017)
and restated without proof by Richard L. Ollerton (May 09 2021):
`a(n) = Sum_{d|n} phi(d)*A001177(d)`.  A001177 is the Fibonacci entry point
"least k >= 1 such that n divides F_k".

## Status

Triage literature status: unclear (no proof in the entry; the count might be
implicit in M. Renault's 1996 thesis "The Fibonacci Sequence Under Various
Moduli", but a reading of that thesis found only the classical zero-counting
for the standard Fibonacci sequence, not for generalized sequences).
Computation (Python cycle enumeration, this campaign): the orbit count equals
`Sum_{d|j} phi(d) alpha(d)` for every `1 ≤ j ≤ 600`, and the members up to 600
match the DATA line.

**This file proves both conjectures** (`card_hitsZero` for A232656 and
`kleinwaks_A064414` for A064414), transitively sorry-free.

## Proof outline

`T (x, y) = (y, x + y)` is a permutation of `(ℤ/j)²`.  The pairs whose forward
orbit meets first coordinate `0` are exactly the `T^k (0, c)` =
`(c F_k, c F_{k+1})` with `k < α(ord c)`, each represented once: `c F_k = 0`
iff `α(ord c) ∣ k` (rank-of-apparition law from `Nat.fib_gcd`), which gives
injectivity, and stepping back to the nearest zero (finite order of `T`) gives
surjectivity.  Grouping `c` by additive order (`φ(d)` elements of order `d`)
gives the count.  Membership in A064414 is "every residue pair hits zero",
since positive integers realise every residue pair.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A064414FibonacciTypeDivisor

/-! ## Definition layer -/

/-- The Fibonacci-type sequence with `G 0 = a`, `G 1 = b` and
`G (n + 2) = G n + G (n + 1)` (OEIS indexes it from `G_1 = a`, `G_2 = b`;
the shift is immaterial for "some term"). -/
def fibType (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | n + 2 => fibType a b n + fibType a b (n + 1)

/-- The Fibonacci entry point (OEIS A001177): the least `k ≥ 1` with
`d ∣ F_k`; junk value `0` when no such `k` exists (only for `d = 0`). -/
noncomputable def fibEntry (d : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, 0 < k ∧ d ∣ Nat.fib k then Nat.find h else 0

/-! ## Ground truth for the definitions -/

-- `fibType 1 1` is the Fibonacci sequence (A000045 shifted) and `fibType 2 1`
-- the Lucas sequence (A000032).
example : (List.range 8).map (fibType 1 1) = [1, 1, 2, 3, 5, 8, 13, 21] := by decide
example : (List.range 6).map (fibType 2 1) = [2, 1, 3, 4, 7, 11] := by decide

/-! ## Orbits of the Fibonacci step -/

/-- The Fibonacci step `(x, y) ↦ (y, x + y)` on `ZMod j × ZMod j`, as a
permutation with inverse `(x, y) ↦ (y - x, x)`. -/
def fibStep (j : ℕ) : Equiv.Perm (ZMod j × ZMod j) where
  toFun p := (p.2, p.1 + p.2)
  invFun p := (p.2 - p.1, p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- Iterating the step from `(a, b)` tracks consecutive terms of `fibType a b`. -/
theorem fibStep_pow_apply_natCast (j a b n : ℕ) :
    (fibStep j ^ n) ((a : ZMod j), (b : ZMod j)) =
      ((fibType a b n : ZMod j), (fibType a b (n + 1) : ZMod j)) := by
  induction n with
  | zero => simp [fibType]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    simp [fibStep, fibType, Nat.cast_add]

/-- Iterating the step from `(0, c)` gives `(c * F_n, c * F_{n+1})`. -/
theorem fibStep_pow_apply_zero (j : ℕ) (c : ZMod j) (n : ℕ) :
    (fibStep j ^ n) (0, c) = (c * (Nat.fib n : ZMod j), c * (Nat.fib (n + 1) : ZMod j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    simp only [fibStep, Equiv.coe_fn_mk, Prod.mk.injEq, true_and, Nat.fib_add_two,
      Nat.cast_add]
    ring

/-- Every positive modulus divides some Fibonacci number of positive index:
the step permutation has finite order `P > 0` and fixes `(0, 1)` after `P`
steps, so `d ∣ F_P`. -/
theorem exists_pos_fib_dvd (d : ℕ) (hd : 0 < d) : ∃ k, 0 < k ∧ d ∣ Nat.fib k := by
  haveI : NeZero d := ⟨hd.ne'⟩
  refine ⟨orderOf (fibStep d), orderOf_pos _, ?_⟩
  have hP := congrArg (fun σ : Equiv.Perm (ZMod d × ZMod d) => (σ (0, 1)).1)
    (pow_orderOf_eq_one (fibStep d))
  simp only [fibStep_pow_apply_zero, one_mul, Equiv.Perm.one_apply] at hP
  exact (CharP.cast_eq_zero_iff (ZMod d) d _).mp hP

/-- For `0 < d`, the entry point is positive, `d ∣ F_{fibEntry d}`, and no
smaller positive index works. -/
theorem fibEntry_spec (d : ℕ) (hd : 0 < d) :
    0 < fibEntry d ∧ d ∣ Nat.fib (fibEntry d) ∧
      ∀ k, 0 < k → k < fibEntry d → ¬ d ∣ Nat.fib k := by
  classical
  have h := exists_pos_fib_dvd d hd
  have hdef : fibEntry d = Nat.find h := by
    unfold fibEntry
    rw [dif_pos h]
  rw [hdef]
  refine ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun k hk hlt hdvd => ?_⟩
  exact Nat.find_min h hlt ⟨hk, hdvd⟩

/-- Characterisation used for ground-truth checks: if `k` is a positive index
with `d ∣ F_k` and no smaller positive index works, then `fibEntry d = k`. -/
theorem fibEntry_eq_of (d k : ℕ) (hk : 0 < k) (hdvd : d ∣ Nat.fib k)
    (hmin : ∀ i < k, 0 < i → ¬ d ∣ Nat.fib i) : fibEntry d = k := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      have hfibpos := Nat.fib_pos.mpr hk
      rw [zero_dvd_iff] at hdvd
      omega
    · exact h0
  obtain ⟨hpos, hdvd', hmin'⟩ := fibEntry_spec d hd
  rcases lt_trichotomy (fibEntry d) k with hlt | heq | hgt
  · exact absurd hdvd' (hmin _ hlt hpos)
  · exact heq
  · exact absurd hdvd (hmin' _ hk hgt)

/-- The rank-of-apparition law: for `0 < d`, `d ∣ F_m ↔ fibEntry d ∣ m`. -/
theorem dvd_fib_iff_fibEntry_dvd (d m : ℕ) (hd : 0 < d) :
    d ∣ Nat.fib m ↔ fibEntry d ∣ m := by
  obtain ⟨hpos, hdvd, hmin⟩ := fibEntry_spec d hd
  constructor
  · intro hm
    have hg : d ∣ Nat.fib (Nat.gcd m (fibEntry d)) := by
      rw [Nat.fib_gcd]
      exact Nat.dvd_gcd hm hdvd
    have hgpos : 0 < Nat.gcd m (fibEntry d) := Nat.gcd_pos_of_pos_right _ hpos
    have hgle : Nat.gcd m (fibEntry d) ≤ fibEntry d := Nat.le_of_dvd hpos (Nat.gcd_dvd_right _ _)
    have hgeq : Nat.gcd m (fibEntry d) = fibEntry d := by
      by_contra hne
      exact hmin _ hgpos (lt_of_le_of_ne hgle hne) hg
    rw [← hgeq]
    exact Nat.gcd_dvd_left _ _
  · intro hm
    exact hdvd.trans (Nat.fib_dvd _ _ hm)

/-- In `ZMod j`, `c * F_m = 0` iff the entry point of the additive order of
`c` divides `m`. -/
theorem mul_fib_eq_zero_iff (j : ℕ) [NeZero j] (c : ZMod j) (m : ℕ) :
    c * (Nat.fib m : ZMod j) = 0 ↔ fibEntry (addOrderOf c) ∣ m := by
  rw [← dvd_fib_iff_fibEntry_dvd _ _ (addOrderOf_pos c), addOrderOf_dvd_iff_nsmul_eq_zero,
    nsmul_eq_mul, mul_comm]

/-! ## Ground truth for `fibEntry` against the A001177 DATA line `1,3,4,6,5,12,8,6,12,15` -/

example : fibEntry 1 = 1 := fibEntry_eq_of 1 1 (by norm_num) (by decide) (by decide)
example : fibEntry 2 = 3 := fibEntry_eq_of 2 3 (by norm_num) (by decide) (by decide)
example : fibEntry 3 = 4 := fibEntry_eq_of 3 4 (by norm_num) (by decide) (by decide)
example : fibEntry 4 = 6 := fibEntry_eq_of 4 6 (by norm_num) (by decide) (by decide)
example : fibEntry 5 = 5 := fibEntry_eq_of 5 5 (by norm_num) (by decide) (by decide)
example : fibEntry 6 = 12 := fibEntry_eq_of 6 12 (by norm_num) (by decide) (by decide)
example : fibEntry 7 = 8 := fibEntry_eq_of 7 8 (by norm_num) (by decide) (by decide)
example : fibEntry 8 = 6 := fibEntry_eq_of 8 6 (by norm_num) (by decide) (by decide)
example : fibEntry 9 = 12 := fibEntry_eq_of 9 12 (by norm_num) (by decide) (by decide)
example : fibEntry 10 = 15 := fibEntry_eq_of 10 15 (by norm_num) (by decide) (by decide)

/-! ## Counting residue pairs whose orbit meets zero -/

/-- A residue pair `p` *hits zero* when some forward iterate of the
Fibonacci step from `p` has first coordinate `0`. -/
def HitsZero (j : ℕ) (p : ZMod j × ZMod j) : Prop :=
  ∃ k, ((fibStep j ^ k) p).1 = 0

/-- The parametrisation `(c, k) ↦ T^k (0, c)` with `k < fibEntry (addOrderOf c)`. -/
def zeroParam (j : ℕ) [NeZero j] :
    (Σ c : ZMod j, Fin (fibEntry (addOrderOf c))) → {p : ZMod j × ZMod j // HitsZero j p} :=
  fun s => ⟨(fibStep j ^ (s.2 : ℕ)) (0, s.1), fibEntry (addOrderOf s.1) - s.2, by
    have hk : (s.2 : ℕ) ≤ fibEntry (addOrderOf s.1) := s.2.isLt.le
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hk, fibStep_pow_apply_zero]
    exact (mul_fib_eq_zero_iff j s.1 _).mpr dvd_rfl⟩

/-- One half of injectivity of `zeroParam`: equal images with `k' ≤ k` force
`k = k'` and `c = c'`. -/
theorem zeroParam_inj_aux (j : ℕ) [NeZero j] (c c' : ZMod j) (k k' : ℕ)
    (hk : k < fibEntry (addOrderOf c)) (hle : k' ≤ k)
    (h : (fibStep j ^ k) (0, c) = (fibStep j ^ k') (0, c')) : k = k' ∧ c = c' := by
  have hsplit : (fibStep j ^ k) (0, c) = (fibStep j ^ k') ((fibStep j ^ (k - k')) (0, c)) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
  rw [hsplit] at h
  have h' : (fibStep j ^ (k - k')) (0, c) = (0, c') := (fibStep j ^ k').injective h
  rw [fibStep_pow_apply_zero, Prod.mk.injEq] at h'
  have hdvd : fibEntry (addOrderOf c) ∣ k - k' := (mul_fib_eq_zero_iff j c _).mp h'.1
  have hzero : k - k' = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  have hkk : k = k' := by omega
  refine ⟨hkk, ?_⟩
  have h2 := h'.2
  rw [hzero] at h2
  simpa using h2

/-- `zeroParam` is injective. -/
theorem zeroParam_injective (j : ℕ) [NeZero j] : Function.Injective (zeroParam j) := by
  rintro ⟨c, k⟩ ⟨c', k'⟩ h
  have h' : (fibStep j ^ (k : ℕ)) (0, c) = (fibStep j ^ (k' : ℕ)) (0, c') :=
    congrArg Subtype.val h
  rcases le_total (k' : ℕ) k with hle | hle
  · obtain ⟨hkk, rfl⟩ := zeroParam_inj_aux j c c' k k' k.isLt hle h'
    have hfin : k = k' := Fin.ext hkk
    subst hfin
    rfl
  · obtain ⟨hkk, rfl⟩ := zeroParam_inj_aux j c' c k' k k'.isLt hle h'.symm
    have hfin : k = k' := Fin.ext hkk.symm
    subst hfin
    rfl

/-- Backward reachability: if a forward iterate of `p` hits zero, so does a
backward iterate, since the step has finite order. -/
theorem exists_inv_pow_fst_eq_zero (j : ℕ) [NeZero j] (p : ZMod j × ZMod j)
    (hp : HitsZero j p) : ∃ m, (((fibStep j)⁻¹ ^ m) p).1 = 0 := by
  obtain ⟨n, hn⟩ := hp
  set P := orderOf (fibStep j) with hP
  have hPpos : 0 < P := orderOf_pos _
  refine ⟨(P - 1) * n, ?_⟩
  have hback : ((fibStep j)⁻¹ ^ ((P - 1) * n)) p = (fibStep j ^ n) p := by
    rw [inv_pow, Equiv.Perm.inv_eq_iff_eq, ← Equiv.Perm.mul_apply, ← pow_add]
    have hsum : (P - 1) * n + n = P * n := by
      obtain ⟨Q, hQ⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
      rw [hQ]
      simp only [Nat.add_sub_cancel]
      ring
    rw [hsum, pow_mul, hP, pow_orderOf_eq_one, one_pow, Equiv.Perm.one_apply]
  rw [hback]
  exact hn

/-- `zeroParam` is surjective: go back to the *nearest* earlier zero. -/
theorem zeroParam_surjective (j : ℕ) [NeZero j] : Function.Surjective (zeroParam j) := by
  classical
  rintro ⟨p, hp⟩
  have hex := exists_inv_pow_fst_eq_zero j p hp
  set n := Nat.find hex with hn
  have hspec : (((fibStep j)⁻¹ ^ n) p).1 = 0 := Nat.find_spec hex
  set c := (((fibStep j)⁻¹ ^ n) p).2 with hc
  have hbase : ((fibStep j)⁻¹ ^ n) p = (0, c) := Prod.ext hspec rfl
  have hp' : p = (fibStep j ^ n) (0, c) := by
    rw [← hbase, inv_pow, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have hlt : n < fibEntry (addOrderOf c) := by
    by_contra hge'
    have hge : fibEntry (addOrderOf c) ≤ n := not_lt.mp hge'
    set α := fibEntry (addOrderOf c)
    have hαpos : 0 < α := (fibEntry_spec _ (addOrderOf_pos c)).1
    have hmin : ¬ (((fibStep j)⁻¹ ^ (n - α)) p).1 = 0 :=
      Nat.find_min hex (by omega)
    apply hmin
    have hshift : ((fibStep j)⁻¹ ^ (n - α)) p = (fibStep j ^ α) (0, c) := by
      rw [← hbase, inv_pow, inv_pow, Equiv.Perm.inv_eq_iff_eq, ← Equiv.Perm.mul_apply,
        ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hge,
        mul_inv_cancel, Equiv.Perm.one_apply]
    rw [hshift, fibStep_pow_apply_zero]
    exact (mul_fib_eq_zero_iff j c α).mpr dvd_rfl
  refine ⟨⟨c, ⟨n, hlt⟩⟩, ?_⟩
  exact Subtype.ext hp'.symm

/-- Grouping residues by additive order: `∑_c g(ord c) = ∑_{d ∣ j} φ(d) g(d)`. -/
theorem sum_addOrderOf_eq_sum_divisors (j : ℕ) [NeZero j] (g : ℕ → ℕ) :
    ∑ c : ZMod j, g (addOrderOf c) = ∑ d ∈ j.divisors, d.totient * g d := by
  classical
  have hmaps : ∀ c ∈ (Finset.univ : Finset (ZMod j)), addOrderOf c ∈ j.divisors := by
    intro c _
    rw [Nat.mem_divisors]
    refine ⟨?_, NeZero.ne j⟩
    have h := addOrderOf_dvd_card (x := c)
    rwa [ZMod.card] at h
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdj : d ∣ Fintype.card (ZMod j) := by
    rw [ZMod.card]
    exact Nat.dvd_of_mem_divisors hd
  have hinner : ∑ c ∈ (Finset.univ : Finset (ZMod j)) with addOrderOf c = d, g (addOrderOf c) =
      ∑ c ∈ (Finset.univ : Finset (ZMod j)) with addOrderOf c = d, g d :=
    Finset.sum_congr rfl fun c hc => by rw [(Finset.mem_filter.mp hc).2]
  rw [hinner, Finset.sum_const, smul_eq_mul, IsAddCyclic.card_addOrderOf_eq_totient hdj]

/-- **Kleinwaks' formula (A232656), proved.**  For `0 < j`, the number of
residue pairs `(x, y) ∈ (ℤ/j)²` whose Fibonacci orbit contains a term
`≡ 0 (mod j)` equals `∑_{d ∣ j} φ(d) · α(d)`, with `α = fibEntry` (A001177). -/
theorem card_hitsZero (j : ℕ) (hj : 0 < j) :
    Nat.card {p : ZMod j × ZMod j // HitsZero j p} =
      ∑ d ∈ j.divisors, d.totient * fibEntry d := by
  haveI : NeZero j := ⟨hj.ne'⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨zeroParam_injective j, zeroParam_surjective j⟩),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_addOrderOf_eq_sum_divisors j fibEntry

/-- `j` divides a term of `fibType a b` iff the residue pair `(a, b)` hits zero. -/
theorem exists_dvd_fibType_iff_hitsZero (j a b : ℕ) :
    (∃ k, j ∣ fibType a b k) ↔ HitsZero j ((a : ZMod j), (b : ZMod j)) := by
  unfold HitsZero
  simp only [fibStep_pow_apply_natCast, CharP.cast_eq_zero_iff (ZMod j) j]

/-- The divisibility property of A064414 is equivalent to every residue pair
hitting zero: positive representatives `x.val + j` realise every residue. -/
theorem forall_exists_dvd_iff_forall_hitsZero (j : ℕ) (hj : 0 < j) :
    (∀ a b : ℕ, 0 < a → 0 < b → ∃ k, j ∣ fibType a b k) ↔
      ∀ p : ZMod j × ZMod j, HitsZero j p := by
  haveI : NeZero j := ⟨hj.ne'⟩
  constructor
  · rintro h ⟨x, y⟩
    have hx : (((x.val + j : ℕ)) : ZMod j) = x := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
    have hy : (((y.val + j : ℕ)) : ZMod j) = y := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
    have hdiv := h (x.val + j) (y.val + j) (by omega) (by omega)
    rw [exists_dvd_fibType_iff_hitsZero, hx, hy] at hdiv
    exact hdiv
  · intro h a b _ _
    exact (exists_dvd_fibType_iff_hitsZero j a b).mpr (h _)

/-- A predicate on a finite type holds everywhere iff its subtype has full
cardinality. -/
theorem forall_iff_natCard_subtype_eq {α : Type*} [Finite α] (P : α → Prop) :
    (∀ x, P x) ↔ Nat.card {x // P x} = Nat.card α := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  constructor
  · intro h
    exact Nat.card_congr (Equiv.subtypeUnivEquiv h)
  · intro h x
    by_contra hx
    have hlt := Fintype.card_subtype_lt (p := P) hx
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hlt
    omega

/-! ## The conjecture -/

/-- **Kleinwaks' conjecture for A064414 (Logan J. Kleinwaks, Oct 29 2017),
proved.**  For `j ≥ 1`: `j` divides at least one term of every Fibonacci-type
sequence `G₀ = a`, `G₁ = b` (`a, b > 0`), `G_{k+2} = G_k + G_{k+1}`, if and only
if `j² = ∑_{d ∣ j} φ(d) · α(d)`, where `α(d) = fibEntry d` is the Fibonacci
entry point (A001177). -/
theorem kleinwaks_A064414 (j : ℕ) (hj : 0 < j) :
    (∀ a b : ℕ, 0 < a → 0 < b → ∃ k, j ∣ fibType a b k) ↔
      j ^ 2 = ∑ d ∈ j.divisors, d.totient * fibEntry d := by
  haveI : NeZero j := ⟨hj.ne'⟩
  have hcardAll : Nat.card (ZMod j × ZMod j) = j ^ 2 := by
    rw [Nat.card_prod, Nat.card_zmod, sq]
  rw [forall_exists_dvd_iff_forall_hitsZero j hj, forall_iff_natCard_subtype_eq,
    card_hitsZero j hj, hcardAll, eq_comm]

/-! ## Sanity layer: both sides of the equivalence are realised -/

-- PROVED: `7` (a DATA term) satisfies the formula, `49 = 1·1 + 6·8`, hence
-- divides some term of every Fibonacci-type sequence.
example : ∀ a b : ℕ, 0 < a → 0 < b → ∃ k, 7 ∣ fibType a b k := by
  rw [kleinwaks_A064414 7 (by norm_num), show Nat.divisors 7 = {1, 7} by decide,
    Finset.sum_pair (by norm_num), fibEntry_eq_of 1 1 (by norm_num) (by decide) (by decide),
    fibEntry_eq_of 7 8 (by norm_num) (by decide) (by decide)]
  decide

-- PROVED: `5` (not a DATA term) fails the formula, `25 ≠ 1·1 + 4·5 = 21`, hence
-- some Fibonacci-type sequence (e.g. Lucas) avoids multiples of `5`.
example : ¬ ∀ a b : ℕ, 0 < a → 0 < b → ∃ k, 5 ∣ fibType a b k := by
  rw [kleinwaks_A064414 5 (by norm_num), show Nat.divisors 5 = {1, 5} by decide,
    Finset.sum_pair (by norm_num), fibEntry_eq_of 1 1 (by norm_num) (by decide) (by decide),
    fibEntry_eq_of 5 5 (by norm_num) (by decide) (by decide)]
  decide

end Candidates.A064414FibonacciTypeDivisor
