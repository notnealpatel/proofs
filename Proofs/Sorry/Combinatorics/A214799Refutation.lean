/-
# A214799 — refutation of R. Israel's conjecture `a(n) = 15 * 2^(n-3)` for `n ≥ 6`

## OEIS source (retrieved 2026-10-21 with `oeis show A214799` and the live
## entry `https://oeis.org/A214799/internal`)

```
%N A214799 Let S be a set of n positive numbers such that all n choose 2
           pairwise GCD's are distinct, and let max(S) denote the largest
           element of S; a(n) is the minimal value of max(S) over all choices
           for S.
%S A214799 1,2,6,18,54,120,240,480,960,1920
%F A214799 Conjecture: a(n) = 15 * 2^(n-3) for n >= 6 (_Robert Israel_)
%O A214799 1,2
%A A214799 _N. J. A. Sloane_, Mar 07 2013
%E A214799 a(4)-a(8) from _Robert Israel_, Mar 05 2013.
%E A214799 a(9)-a(10) from _Giovanni Resta_, Mar 06 2013.
```

The conjecture line carries no date of its own; it was entered with the
sequence (Mar 2013, `a(4)`–`a(8)` from Robert Israel, Mar 05 2013). The entry
has no comment retracting or qualifying it.

## Status

This module **refutes** the conjecture. The 27-element set `witness27` below
consists of positive integers, its `C(27,2) = 351` pairwise gcds are distinct,
and its maximum is `233757342 < 251658240 = 15 * 2^24 = 15 * 2^(27-3)`.
Hence `a(27) ≤ 233757342 < 15 * 2^24`. The witness was found by a randomized
greedy search over smooth products (triage) and re-validated in Python
before formalization; all facts used here are kernel-checked by `decide`.

The search was not exhaustive: the least `n` at which the conjecture fails
(somewhere in `11 ≤ n ≤ 27`) is not determined here. The listed data
`a(6..10) = 120, …, 1920` agree with the formula; the doubling pattern holds
only for small `n`, while sets built from products of a few small primes beat
`15 * 2^(n-3)` once `n` is moderately large.
-/
import Mathlib

set_option autoImplicit false
-- Under the repository's 14 GB virtual-memory cap, asynchronous elaboration of
-- this file aborts with "failed to create thread"; elaborate sequentially.
set_option Elab.async false

namespace Candidates.A214799Refutation

/-! ## Definition layer -/

/-- The `C(|S|, 2)` unordered pairs `{x, y}` of distinct elements of `S`, each
encoded once as the ordered pair `(x, y)` with `x < y`. -/
def pairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter (fun p => p.1 < p.2)

/-- "All `n` choose `2` pairwise GCD's are distinct": the map
`{x, y} ↦ gcd x y` is injective on the unordered pairs of distinct elements
of `S` (each pair written as `(x, y)` with `x < y`). -/
def DistinctPairGcds (S : Finset ℕ) : Prop :=
  Set.InjOn (fun p : ℕ × ℕ => Nat.gcd p.1 p.2) {p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2}

/-- `S` is an admissible set for `A214799` at size `n`: a set of `n` positive
integers all of whose `C(n, 2)` pairwise gcds are distinct. -/
def Admissible (n : ℕ) (S : Finset ℕ) : Prop :=
  S.card = n ∧ (∀ x ∈ S, 0 < x) ∧ DistinctPairGcds S

/-- `A214799(n)`: the minimal value of `max(S)` over all admissible sets `S`
of size `n`. (`Finset.max` takes values in `WithBot ℕ`; `S.max = M` says that
the largest element of `S` is `M`.) For `n ≥ 1` the infimum is over a nonempty
set; the junk value at `n = 0` (offset of the entry is `1`) is never used. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {M : ℕ | ∃ S : Finset ℕ, Admissible n S ∧ S.max = (M : WithBot ℕ)}

/-! ## Decidable bridge -/

/-- The defining set of `DistinctPairGcds` is the finset `pairs S`. -/
theorem coe_pairs (S : Finset ℕ) :
    ({p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2} : Set (ℕ × ℕ)) = ↑(pairs S) := by
  ext p
  simp [pairs, and_assoc]

/-- Pairwise gcds are distinct iff the image of `pairs S` under `gcd` has as
many elements as `pairs S`. This is the decidable form used by the kernel. -/
theorem distinctPairGcds_iff_card (S : Finset ℕ) :
    DistinctPairGcds S ↔
      ((pairs S).image (fun p : ℕ × ℕ => Nat.gcd p.1 p.2)).card = (pairs S).card := by
  rw [Finset.card_image_iff, DistinctPairGcds, coe_pairs]

/-- Any admissible set of size `n` bounds `a n` above by its maximum. -/
theorem a_le_of_admissible {n M : ℕ} {S : Finset ℕ} (hS : Admissible n S)
    (hM : S.max = (M : WithBot ℕ)) : a n ≤ M :=
  Nat.sInf_le ⟨S, hS, hM⟩

/-! ## Ground truth against the listed terms `1, 2, 6, 18, 54` -/

/-- `a(1) = 1`, the first listed term. -/
theorem a_one : a 1 = 1 := by
  apply le_antisymm
  · refine a_le_of_admissible (S := {1}) ⟨rfl, by decide +kernel, ?_⟩ rfl
    rw [distinctPairGcds_iff_card]
    decide +kernel
  · refine le_csInf ⟨1, {1}, ⟨rfl, by decide +kernel, ?_⟩, rfl⟩ ?_
    · rw [distinctPairGcds_iff_card]
      decide +kernel
    · rintro M ⟨S, ⟨hcard, hpos, -⟩, hM⟩
      exact (hpos M (Finset.mem_of_max hM))

/-- `a(2) = 2`, the second listed term. -/
theorem a_two : a 2 = 2 := by
  have hadm : Admissible 2 {1, 2} := ⟨rfl, by decide +kernel, by rw [distinctPairGcds_iff_card]; decide⟩
  apply le_antisymm
  · exact a_le_of_admissible hadm rfl
  · refine le_csInf ⟨2, {1, 2}, hadm, rfl⟩ ?_
    rintro M ⟨S, ⟨hcard, hpos, -⟩, hM⟩
    by_contra hlt
    have hsub : S ⊆ {1} := by
      intro x hx
      have hxM : x ≤ M := Finset.le_max_of_eq hx hM
      have hx0 : 0 < x := hpos x hx
      rw [Finset.mem_singleton]
      omega
    have hle := Finset.card_le_card hsub
    rw [hcard, Finset.card_singleton] at hle
    omega

/-- No `3`-element set of positive integers `≤ 5` has distinct pairwise gcds. -/
theorem no_admissible_three_le_five :
    ∀ T ∈ (Finset.Icc 1 5).powersetCard 3,
      ((pairs T).image (fun p : ℕ × ℕ => Nat.gcd p.1 p.2)).card ≠ (pairs T).card := by
  decide +kernel

/-- `a(3) = 6`, the third listed term (witness `{2, 3, 6}`). -/
theorem a_three : a 3 = 6 := by
  have hadm : Admissible 3 {2, 3, 6} :=
    ⟨rfl, by decide +kernel, by rw [distinctPairGcds_iff_card]; decide⟩
  apply le_antisymm
  · exact a_le_of_admissible hadm rfl
  · refine le_csInf ⟨6, {2, 3, 6}, hadm, rfl⟩ ?_
    rintro M ⟨S, ⟨hcard, hpos, hdist⟩, hM⟩
    by_contra hlt
    have hsub : S ⊆ Finset.Icc 1 5 := by
      intro x hx
      have hxM : x ≤ M := Finset.le_max_of_eq hx hM
      have hx0 : 0 < x := hpos x hx
      rw [Finset.mem_Icc]
      omega
    have hmem : S ∈ (Finset.Icc 1 5).powersetCard 3 :=
      Finset.mem_powersetCard.2 ⟨hsub, hcard⟩
    exact no_admissible_three_le_five S hmem ((distinctPairGcds_iff_card S).1 hdist)

/-- `a(4) ≤ 18` and `a(5) ≤ 54`: the sets `{4, 9, 12, 18}` and
`{8, 24, 27, 36, 54}` are admissible (the listed values are `18` and `54`). -/
theorem a_four_le : a 4 ≤ 18 ∧ a 5 ≤ 54 := by
  constructor
  · refine a_le_of_admissible (S := {4, 9, 12, 18}) ⟨rfl, by decide +kernel, ?_⟩ rfl
    rw [distinctPairGcds_iff_card]
    decide +kernel
  · refine a_le_of_admissible (S := {8, 24, 27, 36, 54}) ⟨rfl, by decide +kernel, ?_⟩ rfl
    rw [distinctPairGcds_iff_card]
    decide +kernel

/-! ## The conjecture -/

/-- **Robert Israel's conjecture (A214799, 2013).** Verbatim from the entry:
"Conjecture: a(n) = 15 * 2^(n-3) for n >= 6 (_Robert Israel_)".

The `6 ≤ n` guard keeps the natural-number subtraction `n - 3` off its
truncated values. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 6 ≤ n → a n = 15 * 2 ^ (n - 3)

/-! ## The refutation -/
/-! ## A linear-size certificate for distinct pairwise gcds

Checking `distinctPairGcds_iff_card` directly on a 27-element set makes the
kernel deduplicate 351 values (quadratically many comparisons), which exceeds
the memory budget. Instead we list the 351 pairs sorted by gcd: a strictly
increasing gcd sequence is checked by 350 comparisons, and a length count shows
that the list exhausts `pairs S`. -/

/-- **Certificate criterion.** If `cert` lists pairs `(x, y)` of elements of
`S` with `x < y`, their gcds strictly increase along the list, and `cert` has
at least as many entries as `pairs S`, then the pairwise gcds of `S` are
distinct. -/
theorem distinctPairGcds_of_cert (S : Finset ℕ) (cert : List (ℕ × ℕ))
    (hmem : ∀ p ∈ cert, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2)
    (hchain : (cert.map (fun p : ℕ × ℕ => Nat.gcd p.1 p.2)).IsChain (· < ·))
    (hlen : (pairs S).card ≤ cert.length) : DistinctPairGcds S := by
  have hnodupMap : (cert.map (fun p : ℕ × ℕ => Nat.gcd p.1 p.2)).Nodup :=
    (List.isChain_iff_pairwise.1 hchain).imp (fun hlt => ne_of_lt hlt)
  have hnodup : cert.Nodup := List.Nodup.of_map _ hnodupMap
  have hsub : cert.toFinset ⊆ pairs S := by
    intro p hp
    rw [List.mem_toFinset] at hp
    obtain ⟨h1, h2, h3⟩ := hmem p hp
    simp [pairs, h1, h2, h3]
  have hcard : (pairs S).card ≤ cert.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup]
    exact hlen
  have heq : cert.toFinset = pairs S := Finset.eq_of_subset_of_card_le hsub hcard
  have hmemCert : ∀ p ∈ ({p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2} : Set (ℕ × ℕ)), p ∈ cert := by
    intro p hp
    rw [coe_pairs, Finset.mem_coe, ← heq, List.mem_toFinset] at hp
    exact hp
  intro p hp q hq hpq
  exact List.inj_on_of_nodup_map hnodupMap (hmemCert p hp) (hmemCert q hq) hpq

/-! ## The refutation -/

/-- The 27-element counterexample set; its maximum is `233757342`. -/
def witness27 : Finset ℕ :=
  {8748740, 13226850, 13247850, 15782844, 30643314, 37238058, 42592550, 45403995,
    47536860, 48141450, 58035348, 60195300, 61193132, 63059100, 65448708, 81550755,
    112190364, 117858900, 154381612, 154421540, 167481314, 173475225, 196903707,
    207619555, 213349955, 226770225, 233757342}

/-- The 351 pairs `(x, y)`, `x < y`, of elements of `witness27`, listed in
strictly increasing order of `gcd x y`. -/
def witness27Cert : List (ℕ × ℕ) :=
    [(47536860, 61193132), (117858900, 167481314), (65448708, 173475225), (61193132, 63059100),
    (15782844, 37238058), (8748740, 48141450), (47536860, 207619555), (37238058, 117858900),
    (48141450, 63059100), (15782844, 42592550), (13247850, 81550755), (30643314, 60195300),
    (13247850, 30643314), (61193132, 226770225), (58035348, 60195300), (47536860, 48141450),
    (8748740, 60195300), (13247850, 65448708), (15782844, 63059100), (13247850, 196903707),
    (48141450, 167481314), (13226850, 154381612), (37238058, 48141450), (42592550, 58035348),
    (60195300, 154421540), (15782844, 65448708), (42592550, 48141450), (48141450, 154381612),
    (8748740, 45403995), (30643314, 167481314), (45403995, 226770225), (48141450, 112190364),
    (30643314, 42592550), (15782844, 226770225), (45403995, 58035348), (173475225, 213349955),
    (42592550, 207619555), (63059100, 196903707), (8748740, 13247850), (13226850, 15782844),
    (15782844, 154421540), (42592550, 196903707), (48141450, 213349955), (13226850, 13247850),
    (42592550, 117858900), (8748740, 65448708), (173475225, 233757342), (63059100, 207619555),
    (154421540, 233757342), (48141450, 226770225), (13247850, 213349955), (13247850, 58035348),
    (48141450, 81550755), (30643314, 226770225), (13226850, 65448708), (13226850, 45403995),
    (63059100, 173475225), (37238058, 45403995), (154381612, 196903707), (13226850, 30643314),
    (81550755, 154421540), (13247850, 233757342), (15782844, 47536860), (112190364, 154421540),
    (60195300, 154381612), (117858900, 196903707), (37238058, 173475225),
    (13247850, 207619555), (30643314, 173475225), (30643314, 37238058), (42592550, 173475225),
    (154421540, 226770225), (47536860, 173475225), (42592550, 61193132),
    (226770225, 233757342), (13247850, 154421540), (47536860, 60195300), (58035348, 233757342),
    (37238058, 207619555), (13247850, 37238058), (13226850, 60195300), (30643314, 47536860),
    (61193132, 213349955), (81550755, 167481314), (47536860, 196903707), (13226850, 117858900),
    (15782844, 167481314), (48141450, 65448708), (58035348, 213349955), (13226850, 61193132),
    (45403995, 173475225), (117858900, 233757342), (45403995, 167481314),
    (65448708, 154381612), (8748740, 233757342), (61193132, 117858900), (48141450, 233757342),
    (15782844, 60195300), (15782844, 213349955), (45403995, 47536860), (58035348, 81550755),
    (13226850, 37238058), (13226850, 47536860), (8748740, 61193132), (61193132, 81550755),
    (13226850, 112190364), (58035348, 167481314), (13226850, 42592550), (13247850, 117858900),
    (58035348, 65448708), (13247850, 61193132), (60195300, 81550755), (81550755, 154381612),
    (37238058, 61193132), (60195300, 112190364), (37238058, 47536860), (58035348, 63059100),
    (61193132, 233757342), (60195300, 213349955), (30643314, 48141450), (13247850, 63059100),
    (45403995, 81550755), (13247850, 167481314), (65448708, 112190364), (8748740, 15782844),
    (63059100, 154421540), (65448708, 207619555), (60195300, 233757342),
    (154381612, 207619555), (47536860, 81550755), (8748740, 37238058), (42592550, 233757342),
    (58035348, 196903707), (37238058, 58035348), (112190364, 117858900),
    (207619555, 233757342), (45403995, 63059100), (37238058, 196903707), (8748740, 173475225),
    (13247850, 47536860), (45403995, 196903707), (65448708, 117858900), (45403995, 154381612),
    (112190364, 196903707), (47536860, 112190364), (13226850, 213349955),
    (37238058, 233757342), (60195300, 117858900), (8748740, 117858900), (112190364, 213349955),
    (81550755, 173475225), (61193132, 154381612), (154381612, 233757342),
    (58035348, 207619555), (37238058, 154421540), (47536860, 65448708), (48141450, 196903707),
    (154421540, 213349955), (42592550, 112190364), (196903707, 226770225),
    (154421540, 196903707), (8748740, 112190364), (37238058, 213349955), (60195300, 63059100),
    (13226850, 81550755), (8748740, 30643314), (8748740, 58035348), (45403995, 117858900),
    (8748740, 207619555), (60195300, 167481314), (60195300, 173475225), (45403995, 154421540),
    (117858900, 154421540), (13247850, 15782844), (58035348, 61193132), (13226850, 154421540),
    (45403995, 60195300), (60195300, 196903707), (65448708, 167481314), (42592550, 81550755),
    (42592550, 45403995), (8748740, 13226850), (61193132, 112190364), (207619555, 226770225),
    (15782844, 81550755), (63059100, 167481314), (154421540, 173475225), (30643314, 154421540),
    (37238058, 154381612), (15782844, 45403995), (8748740, 196903707), (65448708, 196903707),
    (154381612, 154421540), (65448708, 154421540), (42592550, 60195300), (42592550, 154421540),
    (13226850, 207619555), (58035348, 112190364), (30643314, 196903707),
    (154421540, 167481314), (60195300, 61193132), (42592550, 65448708), (58035348, 226770225),
    (47536860, 154421540), (15782844, 233757342), (112190364, 226770225), (30643314, 61193132),
    (8748740, 226770225), (13226850, 226770225), (81550755, 112190364), (167481314, 173475225),
    (61193132, 65448708), (65448708, 81550755), (47536860, 117858900), (30643314, 154381612),
    (60195300, 207619555), (37238058, 81550755), (13247850, 226770225), (13226850, 233757342),
    (13247850, 48141450), (117858900, 226770225), (61193132, 167481314), (30643314, 63059100),
    (154421540, 207619555), (30643314, 45403995), (207619555, 213349955), (47536860, 58035348),
    (48141450, 154421540), (13226850, 63059100), (15782844, 48141450), (8748740, 167481314),
    (61193132, 173475225), (13226850, 58035348), (37238058, 60195300), (45403995, 65448708),
    (8748740, 154421540), (30643314, 233757342), (65448708, 226770225), (117858900, 173475225),
    (45403995, 112190364), (154381612, 173475225), (30643314, 112190364),
    (167481314, 207619555), (15782844, 58035348), (196903707, 213349955), (30643314, 65448708),
    (13226850, 48141450), (117858900, 154381612), (63059100, 233757342),
    (112190364, 173475225), (45403995, 207619555), (13226850, 167481314), (42592550, 47536860),
    (13247850, 60195300), (8748740, 47536860), (117858900, 213349955), (167481314, 213349955),
    (81550755, 233757342), (63059100, 154381612), (37238058, 63059100), (48141450, 58035348),
    (47536860, 167481314), (81550755, 226770225), (48141450, 60195300), (42592550, 167481314),
    (173475225, 196903707), (13247850, 112190364), (48141450, 207619555),
    (15782844, 112190364), (213349955, 226770225), (30643314, 58035348), (45403995, 61193132),
    (65448708, 233757342), (112190364, 207619555), (63059100, 81550755),
    (117858900, 207619555), (13226850, 196903707), (45403995, 48141450), (37238058, 112190364),
    (15782844, 30643314), (154381612, 167481314), (63059100, 112190364),
    (154381612, 213349955), (8748740, 63059100), (13247850, 45403995), (15782844, 196903707),
    (42592550, 154381612), (63059100, 117858900), (167481314, 226770225), (63059100, 65448708),
    (8748740, 154381612), (48141450, 117858900), (15782844, 173475225), (13247850, 42592550),
    (58035348, 117858900), (112190364, 233757342), (30643314, 213349955),
    (13247850, 154381612), (154381612, 226770225), (13247850, 173475225),
    (37238058, 167481314), (15782844, 154381612), (15782844, 207619555), (81550755, 117858900),
    (61193132, 154421540), (8748740, 213349955), (112190364, 167481314), (15782844, 117858900),
    (47536860, 233757342), (48141450, 61193132), (60195300, 65448708), (30643314, 207619555),
    (8748740, 42592550), (42592550, 226770225), (81550755, 196903707), (47536860, 226770225),
    (37238058, 42592550), (173475225, 226770225), (15782844, 61193132), (45403995, 233757342),
    (8748740, 81550755), (65448708, 213349955), (58035348, 154421540), (58035348, 154381612),
    (42592550, 213349955), (81550755, 207619555), (47536860, 154381612), (37238058, 226770225),
    (45403995, 213349955), (61193132, 196903707), (30643314, 81550755), (13226850, 173475225),
    (60195300, 226770225), (173475225, 207619555), (42592550, 63059100), (47536860, 213349955),
    (58035348, 173475225), (81550755, 213349955), (48141450, 173475225),
    (167481314, 233757342), (112190364, 154381612), (47536860, 63059100),
    (63059100, 213349955), (196903707, 233757342), (37238058, 65448708), (63059100, 226770225),
    (196903707, 207619555), (213349955, 233757342), (61193132, 207619555),
    (167481314, 196903707), (30643314, 117858900)]

/-- `witness27` has `27` elements. -/
theorem witness27_card : witness27.card = 27 := by
  decide +kernel

/-- Every element of `witness27` is positive. -/
theorem witness27_pos : ∀ x ∈ witness27, 0 < x := by
  decide +kernel

/-- Every certificate entry is a pair `(x, y)` of elements of `witness27`
with `x < y`. -/
theorem witness27Cert_mem : ∀ p ∈ witness27Cert, p.1 ∈ witness27 ∧ p.2 ∈ witness27 ∧ p.1 < p.2 := by
  decide +kernel

/-- The gcds along the certificate strictly increase. -/
theorem witness27Cert_chain :
    (witness27Cert.map (fun p : ℕ × ℕ => Nat.gcd p.1 p.2)).IsChain (· < ·) := by
  decide +kernel

/-- `witness27` has `351 = C(27, 2)` unordered pairs. -/
theorem pairs_witness27_card : (pairs witness27).card = 351 := by
  decide +kernel

/-- The certificate has `351` entries. -/
theorem witness27Cert_length : witness27Cert.length = 351 := by
  decide +kernel

/-- The `351 = C(27, 2)` pairwise gcds of `witness27` are distinct. -/
theorem witness27_distinctPairGcds : DistinctPairGcds witness27 :=
  distinctPairGcds_of_cert witness27 witness27Cert witness27Cert_mem witness27Cert_chain
    (by rw [pairs_witness27_card, witness27Cert_length])

/-- The largest element of `witness27` is `233757342`. -/
theorem witness27_max : witness27.max = ((233757342 : ℕ) : WithBot ℕ) := by
  decide +kernel

/-- `witness27` is admissible at size `27`. -/
theorem witness27_admissible : Admissible 27 witness27 :=
  ⟨witness27_card, witness27_pos, witness27_distinctPairGcds⟩

/-- `a(27) ≤ 233757342`. -/
theorem a_27_le : a 27 ≤ 233757342 :=
  a_le_of_admissible witness27_admissible witness27_max

/-- `a(27) < 15 * 2^(27 - 3) = 251658240`. -/
theorem a_27_lt : a 27 < 15 * 2 ^ (27 - 3) :=
  lt_of_le_of_lt a_27_le (by norm_num)

/-- **Israel's conjecture `a(n) = 15 * 2^(n-3)` for `n ≥ 6` is false.**

Counterexample at `n = 27`: the set `witness27` of 27 positive integers has
351 distinct pairwise gcds and maximum `233757342 < 15 * 2^24 = 251658240`,
so `a(27) < 15 * 2^(27-3)`. The formula fits the listed data `n = 6, …, 10`
(extremal sets there are built around powers of `2`); the author presumably
intended it only as a description of that small range, since sets assembled
from products of a few small primes beat `15 * 2^(n-3)` for larger `n`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have h27 : a 27 = 15 * 2 ^ (27 - 3) := hconj 27 (by norm_num)
  exact (ne_of_lt a_27_lt) h27

end Candidates.A214799Refutation
