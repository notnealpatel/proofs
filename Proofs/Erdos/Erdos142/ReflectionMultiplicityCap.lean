/-
  Erdős Problem #142 — fixed-target cap-fiber multiplicity bounds.

  The *reflection multiplicity* `reflectionMultiplicityNat A c` (defined in
  `Erdos.Erdos142.ReflectionMassEnergy`) counts the ordered nontrivial
  representations `c = 2 * a - b` with `a, b ∈ A`, equivalently the number of
  admissible centres `a ∈ A` with `2 * a - c ∈ A` and `a ≠ c`.

  This file proves the *fixed-target cap-fiber* bound.  If `A ⊆ [0,L)` is
  scalar 3-AP-free and `c : ℤ` is any target, then the admissible centres form a
  3-AP-free set of naturals contained in an interval of `⌈L/2⌉` consecutive
  integers: the two constraints `c ≤ 2*a` and `2*a - c < L` squeeze the centre
  `a` into `[⌈c/2⌉, ⌊(c+L-1)/2⌋]`, an interval of at most `⌈L/2⌉` integers.  The
  Mathlib Roth number of an interval of length `m` is `rothNumberNat m`, so

    `reflectionMultiplicityNat A c ≤ rothNumberNat ((L + 1) / 2)`.

  Partitioning a length-`N^2` interval into `⌈N/2⌉` blocks of `N` consecutive
  integers and using subadditivity of `rothNumberNat` gives the square-scale
  cap

    `reflectionMultiplicityNat A c ≤ (N + 1) / 2 * rothNumberNat N`

  for `A ⊆ [0,N^2)`, and summing the squared multiplicities with the mass
  identity `reflectionMassNat_eq_sum_multiplicity` gives the corresponding
  energy bound `∑_{c ∈ [0,L)} ν(c)^2 ≤ rothNumberNat ⌈L/2⌉ * M`.

  The same block decomposition is isolated in the abstract form
  `card_le_mul_of_local_bound`: a finite set of naturals contained in `[lo,lo+L)`
  with at most `B` elements in every length-`N` interval has at most `k * B`
  elements whenever `L ≤ k * N`.

  Scope.  Nothing here is asymptotic and nothing here uses, assumes or claims
  the open estimate `(O)`, the candidate estimate `(C)`, or Erdős Problem #142
  itself.  All statements are exact finite combinatorics; the only arithmetic
  input is Mathlib's `rothNumberNat`.

  Boundary behaviour.  `L = 0` forces `A = ∅` (the range hypothesis is then
  `a < 0`), `L = 1` and `N = 0`, `N = 1` are all allowed, and the sharp endpoint
  is stated with no hypothesis on `L` at all; the examples at the end of the
  file pin these degenerate cases.  Truncated subtraction and the `ℕ`-valued
  `(L + 1) / 2` are the ceiling `⌈L/2⌉`, which is correct at `L = 0`.
-/

import Erdos.Erdos142.ReflectionMassEnergy
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-! ## The admissible centres of a fixed target, as a set of naturals

`reflectionMultiplicityNat A c` is defined through the image of `A` in `ℤ`.  For
the interval argument it is convenient to have the centres themselves as a
`Finset ℕ`; `reflectionCentersNat` is the filter of `A` by the two conditions
`2 * a - c ∈ A` and `a ≠ c`, expressed through the image in `ℤ`. -/

/-- The admissible centres of the target `c` in `A`: the elements `a ∈ A` whose
reflection `2 * a - c` also lies in `A` and which are not the target itself,
`a ≠ c`.  Membership of `2 * a - c` in `A` is expressed through the image of `A`
in `ℤ`, so the target `c` may be any integer. -/
def reflectionCentersNat (A : Finset ℕ) (c : ℤ) : Finset ℕ :=
  A.filter (fun a : ℕ => 2 * (a : ℤ) - c ∈ A.image (fun n : ℕ => (n : ℤ)) ∧ (a : ℤ) ≠ c)

/-- Membership in the set of admissible centres. -/
theorem mem_reflectionCentersNat {A : Finset ℕ} {c : ℤ} {a : ℕ} :
    a ∈ reflectionCentersNat A c ↔
      a ∈ A ∧ 2 * (a : ℤ) - c ∈ A.image (fun n : ℕ => (n : ℤ)) ∧ (a : ℤ) ≠ c :=
  Finset.mem_filter

/-- The admissible centres of `c` form a subset of `A`. -/
theorem reflectionCentersNat_subset (A : Finset ℕ) (c : ℤ) : reflectionCentersNat A c ⊆ A :=
  Finset.filter_subset _ _

/-- **The multiplicity is the number of admissible centres.**  The `ℕ`-indexed
reflection multiplicity of the target `c` equals the cardinality of
`reflectionCentersNat A c`; this is the substitution `b = 2 * a - c` made
explicit, transported from `reflectionMultiplicity_eq_card_filter` along the
injective image `ℕ → ℤ`. -/
theorem reflectionMultiplicityNat_eq_card_reflectionCentersNat (A : Finset ℕ) (c : ℤ) :
    reflectionMultiplicityNat A c = (reflectionCentersNat A c).card := by
  rw [reflectionMultiplicityNat, reflectionMultiplicity_eq_card_filter, reflectionCentersNat,
    Finset.filter_image]
  exact Finset.card_image_of_injective _ fun _ _ h => by exact_mod_cast h

/-- **The admissible centres of a 3-AP-free set are 3-AP-free.**  They are a
subset of `A`, and a subset of a 3-AP-free set is 3-AP-free. -/
theorem reflectionCentersNat_threeAPFree (A : Finset ℕ) (c : ℤ)
    (hA : ThreeAPFree (A : Set ℕ)) :
    ThreeAPFree ((reflectionCentersNat A c : Finset ℕ) : Set ℕ) :=
  hA.mono fun _ hx => (mem_reflectionCentersNat.mp hx).1

/-! ## The interval of admissible centres

Write `b = 2 * a - c ∈ A`.  Since `A ⊆ [0,L)`, the centre `a` of a target `c`
satisfies `c ≤ 2 * a` and `2 * a - c < L`, i.e. `2 * a ∈ [c, c + L - 1]`; the
centres therefore lie in `[⌈c/2⌉, ⌊(c+L-1)/2⌋]`, an interval of at most `⌈L/2⌉`
integers.  `centerOffset c` is the clamped lower endpoint `max 0 ⌈c/2⌉`; the
clamping is harmless because centres are naturals. -/

/-- The clamped lower endpoint `max 0 ⌈c/2⌉` of the interval of centres of the
target `c`.  For `c ≥ 0` this is `(c + 1) / 2 = ⌈c/2⌉`, and for `c < 0` it is
`0`, the smallest possible centre. -/
def centerOffset (c : ℤ) : ℕ := if 0 ≤ c then (c.toNat + 1) / 2 else 0

/-- Unfolding `centerOffset` at a nonnegative target. -/
theorem centerOffset_of_nonneg {c : ℤ} (hc : 0 ≤ c) : centerOffset c = (c.toNat + 1) / 2 :=
  if_pos hc

/-- Unfolding `centerOffset` at a negative target. -/
theorem centerOffset_of_neg {c : ℤ} (hc : c < 0) : centerOffset c = 0 :=
  if_neg (by omega)

/-- **Internal integer helper.**  Every admissible centre `a` of the target `c`
in a set `A ⊆ [0,L)` satisfies the two integer bounds `c ≤ 2 * a` and
`2 * a - c < L`; these are the two constraints that confine the centres to an
interval of length `⌈L/2⌉`. -/
theorem center_int_bounds (A : Finset ℕ) (c : ℤ) (L : ℕ) (hA : ∀ a ∈ A, a < L)
    {a : ℕ} (ha : a ∈ reflectionCentersNat A c) :
    c ≤ 2 * (a : ℤ) ∧ 2 * (a : ℤ) - c < (L : ℤ) := by
  obtain ⟨-, hmem, -⟩ := mem_reflectionCentersNat.mp ha
  obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp hmem
  have hbL : (b : ℤ) < (L : ℤ) := by exact_mod_cast hA b hb
  constructor <;> omega

/-- **The cap-fiber interval.**  For `A ⊆ [0,L)` and any target `c : ℤ`, all
admissible centres of `c` lie in the interval
`[centerOffset c, centerOffset c + ⌈L/2⌉)` of `⌈L/2⌉` consecutive integers. -/
theorem reflectionCentersNat_subset_Ico (A : Finset ℕ) (c : ℤ) (L : ℕ)
    (hA : ∀ a ∈ A, a < L) :
    ∀ a ∈ reflectionCentersNat A c,
      centerOffset c ≤ a ∧ a < centerOffset c + (L + 1) / 2 := by
  intro a ha
  obtain ⟨haA, hmem, -⟩ := mem_reflectionCentersNat.mp ha
  obtain ⟨b, hbA, hbeq⟩ := Finset.mem_image.mp hmem
  have hbL : b < L := hA b hbA
  by_cases hc : 0 ≤ c
  · have hkey : 2 * a = b + c.toNat := by
      have hcast : ((2 * a : ℕ) : ℤ) = ((b + c.toNat : ℕ) : ℤ) := by
        push_cast
        have := Int.toNat_of_nonneg hc
        omega
      exact_mod_cast hcast
    rw [centerOffset, if_pos hc]
    omega
  · have hc' : c < 0 := by omega
    have hlt : 2 * (a : ℤ) < (b : ℤ) := by omega
    have hlt' : 2 * a < b := by exact_mod_cast hlt
    rw [centerOffset, if_neg hc]
    omega

/-! ## The sharp fixed-target cap bound -/

/-- **Sharp fixed-target cap bound.**  For a 3-AP-free `A ⊆ [0,L)` and every
target `c : ℤ`, the reflection multiplicity of `c` is at most the Roth number of
`⌈L/2⌉`:

  `reflectionMultiplicityNat A c ≤ rothNumberNat ((L + 1) / 2)`.

The admissible centres are 3-AP-free and lie in an interval of `⌈L/2⌉`
consecutive integers, and the Roth number of `Ico a (a + m)` is `rothNumberNat m`
(Mathlib's `addRothNumber_Ico`).  No hypothesis is imposed on `L`, so `L = 0`
(where `A = ∅`), `L = 1` and all larger scales are covered. -/
theorem reflectionMultiplicityNat_le_rothNumberNat_half (A : Finset ℕ) (L : ℕ)
    (hA : ∀ a ∈ A, a < L) (hfree : ThreeAPFree (A : Set ℕ)) (c : ℤ) :
    reflectionMultiplicityNat A c ≤ rothNumberNat ((L + 1) / 2) := by
  rw [reflectionMultiplicityNat_eq_card_reflectionCentersNat]
  have hsub := reflectionCentersNat_subset_Ico A c L hA
  have hle : (reflectionCentersNat A c).card
      ≤ addRothNumber (Finset.Ico (centerOffset c) (centerOffset c + (L + 1) / 2)) :=
    (reflectionCentersNat_threeAPFree A c hfree).le_addRothNumber fun x hx => by
      obtain ⟨h1, h2⟩ := hsub x hx
      exact Finset.mem_Ico.mpr ⟨h1, by omega⟩
  rw [addRothNumber_Ico, Nat.add_sub_cancel_left] at hle
  exact hle

/-! ## The abstract local cap bound

The block decomposition underlying the square-scale corollary is isolated here
in the form in which it is used: a set with at most `B` elements in every
length-`N` interval has at most `k * B` elements in an interval of `k * N`
consecutive integers. -/

/-- **Abstract local cap bound.**  Let `T : Finset ℕ` be contained in the
interval `[lo, lo + L)` of `L` consecutive integers, and suppose every
length-`N` interval `[lo + i * N, lo + i * N + N)` contains at most `B` elements
of `T`.  If `L ≤ k * N` then `#T ≤ k * B`.  The proof partitions `T` by the
block index `(x - lo) / N`, which takes at most `k` values. -/
theorem card_le_mul_of_local_bound {T : Finset ℕ} {lo L B k N : ℕ}
    (hsub : ∀ x ∈ T, lo ≤ x ∧ x < lo + L) (hL : L ≤ k * N)
    (hloc : ∀ i : ℕ,
      (T.filter (fun x : ℕ => x ∈ Finset.Ico (lo + i * N) (lo + i * N + N))).card ≤ B) :
    T.card ≤ k * B := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have hL0 : L = 0 := by omega
    have hT : T = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      obtain ⟨h1, h2⟩ := hsub x hx
      omega
    rw [hT, Finset.card_empty]
    exact Nat.zero_le _
  · have hfiber : ∀ i : ℕ, (T.filter (fun x : ℕ => (x - lo) / N = i)).card ≤ B := by
      intro i
      refine le_trans (Finset.card_le_card ?_) (hloc i)
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      obtain ⟨hxT, hxi⟩ := hx
      obtain ⟨hlo, hlt⟩ := hsub x hxT
      refine ⟨hxT, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
      · have h1 : i * N ≤ x - lo := by
          rw [← hxi]
          exact Nat.div_mul_le_self _ _
        have h2 : lo + i * N ≤ lo + (x - lo) := Nat.add_le_add_left h1 lo
        rwa [Nat.add_sub_of_le hlo] at h2
      · have h2 : (x - lo) / N * N + (x - lo) % N = x - lo := Nat.div_add_mod' _ _
        have h3 : (x - lo) % N < N := Nat.mod_lt _ hN
        have h4 : x - lo < i * N + N := by
          rw [← h2, hxi]
          omega
        have hx_eq : x = lo + (x - lo) := (Nat.add_sub_of_le hlo).symm
        rw [hx_eq]
        omega
    have hmem : (T : Set ℕ).MapsTo (fun x : ℕ => (x - lo) / N) (Finset.range k) := by
      intro x hx
      change (x - lo) / N ∈ Finset.range k
      rw [Finset.mem_range]
      obtain ⟨hlo, hlt⟩ := hsub x hx
      have hxlt : x < lo + k * N := by omega
      have hx_eq : x = lo + (x - lo) := (Nat.add_sub_of_le hlo).symm
      rw [hx_eq] at hxlt
      exact (Nat.div_lt_iff_lt_mul hN).mpr (by omega)
    calc T.card
        = ∑ i ∈ Finset.range k, (T.filter (fun x : ℕ => (x - lo) / N = i)).card :=
          Finset.card_eq_sum_card_fiberwise hmem
      _ ≤ ∑ _i ∈ Finset.range k, B := Finset.sum_le_sum fun i _ => hfiber i
      _ = k * B := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Local cap bound from 3-AP-freeness.**  A 3-AP-free `T ⊆ [lo, lo + L)` with
`L ≤ k * N` has at most `k * rothNumberNat N` elements: each length-`N` block
meets `T` in a 3-AP-free subset of an interval of `N` consecutive integers, and
the Roth number of such an interval is `rothNumberNat N`. -/
theorem card_le_mul_rothNumberNat_of_local_bound {T : Finset ℕ} {lo L k N : ℕ}
    (hsub : ∀ x ∈ T, lo ≤ x ∧ x < lo + L) (hL : L ≤ k * N)
    (hfree : ThreeAPFree (T : Set ℕ)) : T.card ≤ k * rothNumberNat N := by
  refine card_le_mul_of_local_bound hsub hL fun i => ?_
  have hfiber : ThreeAPFree
      (((T.filter (fun x : ℕ => x ∈ Finset.Ico (lo + i * N) (lo + i * N + N)) :
        Finset ℕ)) : Set ℕ) :=
    hfree.mono fun _ hx => (Finset.mem_filter.mp hx).1
  have h := hfiber.le_addRothNumber (t := Finset.Ico (lo + i * N) (lo + i * N + N))
    fun _ hx => (Finset.mem_filter.mp hx).2
  rwa [addRothNumber_Ico, Nat.add_sub_cancel_left] at h

/-! ## The square-scale corollary

At `L = N^2` the sharp endpoint gives `rothNumberNat ⌈N^2/2⌉`, and
`⌈N^2/2⌉ ≤ ⌈N/2⌉ * N` turns this into `⌈N/2⌉` blocks of `N` consecutive
integers, each contributing at most `rothNumberNat N`. -/

/-- **Subadditivity of the Roth number over multiples.**  `k` consecutive blocks
of `N` integers contain at most `k * rothNumberNat N` points of any 3-AP-free
set; equivalently `rothNumberNat (k * N) ≤ k * rothNumberNat N`.  This is the
iteration of Mathlib's `rothNumberNat_add_le`. -/
theorem rothNumberNat_mul_le (k N : ℕ) : rothNumberNat (k * N) ≤ k * rothNumberNat N := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc rothNumberNat ((k + 1) * N)
        = rothNumberNat (k * N + N) := by congr 1; ring
      _ ≤ rothNumberNat (k * N) + rothNumberNat N := rothNumberNat_add_le _ _
      _ ≤ k * rothNumberNat N + rothNumberNat N := Nat.add_le_add_right ih _
      _ = (k + 1) * rothNumberNat N := by ring

/-- **The ceiling-half square inequality.**  `⌈N^2/2⌉ = (N^2 + 1) / 2` is at most
`⌈N/2⌉ * N = (N + 1) / 2 * N`: the `N^2` integers `[0, N^2)` are covered by
`⌈N/2⌉` blocks of `N` consecutive integers.  Valid for every `N : ℕ`, including
`N = 0`. -/
theorem ceil_half_sq_le_mul (N : ℕ) : (N * N + 1) / 2 ≤ (N + 1) / 2 * N := by
  rw [Nat.div_le_iff_le_mul_add_pred (show 0 < 2 by norm_num)]
  have h : N ≤ 2 * ((N + 1) / 2) := by omega
  have h2 : N * N ≤ 2 * ((N + 1) / 2) * N := Nat.mul_le_mul_right N h
  have h3 : N * N + 1 ≤ 2 * ((N + 1) / 2) * N + 1 := Nat.add_le_add_right h2 1
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h3

/-- **Fixed-target cap bound at the square scale.**  For a 3-AP-free
`A ⊆ [0,N^2)` and every target `c : ℤ`,

  `reflectionMultiplicityNat A c ≤ ⌈N/2⌉ * rothNumberNat N`,

i.e. `(N + 1) / 2 * rothNumberNat N`.  The admissible centres of `c` lie in
`⌈N^2/2⌉ ≤ ⌈N/2⌉ * N` consecutive integers, which split into `⌈N/2⌉` blocks of
`N`.  Valid at `N = 0` (where `A = ∅`) and `N = 1`. -/
theorem reflectionMultiplicityNat_le_ceil_half_mul_rothNumberNat (A : Finset ℕ) (N : ℕ)
    (hA : ∀ a ∈ A, a < N ^ 2) (hfree : ThreeAPFree (A : Set ℕ)) (c : ℤ) :
    reflectionMultiplicityNat A c ≤ (N + 1) / 2 * rothNumberNat N := by
  have h1 : reflectionMultiplicityNat A c ≤ rothNumberNat ((N ^ 2 + 1) / 2) :=
    reflectionMultiplicityNat_le_rothNumberNat_half A (N ^ 2) hA hfree c
  have h2 : rothNumberNat ((N ^ 2 + 1) / 2) ≤ rothNumberNat ((N + 1) / 2 * N) :=
    rothNumberNat.monotone (by simpa [pow_two] using ceil_half_sq_le_mul N)
  have h3 : rothNumberNat ((N + 1) / 2 * N) ≤ (N + 1) / 2 * rothNumberNat N :=
    rothNumberNat_mul_le _ _
  exact h1.trans (h2.trans h3)

/-- **Cap-fiber energy bound.**  For a 3-AP-free `A ⊆ [0,L)` the sum of the
squared multiplicities of the targets in `[0,L)` is at most the cap
`rothNumberNat ⌈L/2⌉` times the reflection mass:

  `∑_{c ∈ [0,L)} ν(c)^2 ≤ rothNumberNat ((L + 1) / 2) * reflectionMassNat A L`.

This is the termwise bound `ν(c)^2 ≤ rothNumberNat ⌈L/2⌉ * ν(c)` summed against
the mass identity `reflectionMassNat_eq_sum_multiplicity`. -/
theorem sum_sq_multiplicityNat_le_rothNumberNat_half (A : Finset ℕ) (L : ℕ)
    (hA : ∀ a ∈ A, a < L) (hfree : ThreeAPFree (A : Set ℕ)) :
    ∑ c ∈ Finset.Ico (0 : ℤ) (L : ℤ), (reflectionMultiplicityNat A c) ^ 2
      ≤ rothNumberNat ((L + 1) / 2) * reflectionMassNat A L := by
  have hterm : ∀ c ∈ Finset.Ico (0 : ℤ) (L : ℤ),
      (reflectionMultiplicityNat A c) ^ 2
        ≤ rothNumberNat ((L + 1) / 2) * reflectionMultiplicityNat A c := by
    intro c _
    calc (reflectionMultiplicityNat A c) ^ 2
        = reflectionMultiplicityNat A c * reflectionMultiplicityNat A c := by ring
      _ ≤ rothNumberNat ((L + 1) / 2) * reflectionMultiplicityNat A c :=
          Nat.mul_le_mul_right _ (reflectionMultiplicityNat_le_rothNumberNat_half A L hA hfree c)
  calc ∑ c ∈ Finset.Ico (0 : ℤ) (L : ℤ), (reflectionMultiplicityNat A c) ^ 2
      ≤ ∑ c ∈ Finset.Ico (0 : ℤ) (L : ℤ),
          rothNumberNat ((L + 1) / 2) * reflectionMultiplicityNat A c :=
        Finset.sum_le_sum hterm
    _ = rothNumberNat ((L + 1) / 2)
          * ∑ c ∈ Finset.Ico (0 : ℤ) (L : ℤ), reflectionMultiplicityNat A c := by
        rw [Finset.mul_sum]
    _ = rothNumberNat ((L + 1) / 2) * reflectionMassNat A L := by
        rw [reflectionMassNat_eq_sum_multiplicity]

/-! ## Ground truth, satisfiability, and boundary audit -/

/-- `centerOffset` at a positive even target: `⌈2/2⌉ = 1`. -/
example : centerOffset 2 = 1 := by decide

/-- `centerOffset` at a positive odd target: `⌈5/2⌉ = 3`. -/
example : centerOffset 5 = 3 := by decide

/-- `centerOffset` clamps negative targets to `0`. -/
example : centerOffset (-3) = 0 ∧ centerOffset 0 = 0 := by decide

/-- The admissible centres of the target `2` in `{0,1,3,4}` are `{1,3}`:
`2 * 1 - 2 = 0 ∈ A` and `2 * 3 - 2 = 4 ∈ A`, while `0` and `4` have reflections
`-2` and `6` outside `A`. -/
example : reflectionCentersNat ({0, 1, 3, 4} : Finset ℕ) 2 = ({1, 3} : Finset ℕ) := by decide

/-- Ground truth for the multiplicity at the same input: `ν(2) = 2`, matching the
two admissible centres above. -/
example : reflectionMultiplicityNat ({0, 1, 3, 4} : Finset ℕ) 2 = 2 := by decide

/-- Satisfiability: `{0,1,3,4}` is 3-AP-free, and it satisfies the range
hypothesis for `N = 3` (`L = 9`). -/
example : ThreeAPFree (({0, 1, 3, 4} : Finset ℕ) : Set ℕ) ∧
    (∀ a ∈ ({0, 1, 3, 4} : Finset ℕ), a < 3 ^ 2) := by decide

/-- The sharp endpoint at a concrete input: `ν(2) = 2 ≤ rothNumberNat 5`, the
interval `[centerOffset 2, centerOffset 2 + ⌈9/2⌉) = [1, 6)` having `5` points. -/
example : reflectionMultiplicityNat ({0, 1, 3, 4} : Finset ℕ) 2 ≤ rothNumberNat 5 :=
  reflectionMultiplicityNat_le_rothNumberNat_half _ 9 (by decide) (by decide) 2

/-- The square-scale cap at a concrete input: `ν(2) ≤ ⌈3/2⌉ * rothNumberNat 3`. -/
example : reflectionMultiplicityNat ({0, 1, 3, 4} : Finset ℕ) 2
    ≤ (3 + 1) / 2 * rothNumberNat 3 :=
  reflectionMultiplicityNat_le_ceil_half_mul_rothNumberNat _ 3 (by decide) (by decide) 2

/-- Tightness of the sharp endpoint: for `A = {1,2,4}` (3-AP-free inside
`[0,5)`) the target `0` has `ν(0) = 2` admissible centres, `1` and `2`, and the
cap `rothNumberNat ⌈5/2⌉ = rothNumberNat 3` is exactly `2`. -/
example : reflectionMultiplicityNat ({1, 2, 4} : Finset ℕ) 0 = 2 ∧ rothNumberNat 3 = 2 := by
  decide

/-- The sharp endpoint is attained at `A = {1,2,4}` inside `[0,5)`: the bound
`ν(0) ≤ rothNumberNat ((5 + 1) / 2)` is an equality. -/
example : reflectionMultiplicityNat ({1, 2, 4} : Finset ℕ) 0 = rothNumberNat ((5 + 1) / 2) := by
  decide

/-- The cap-fiber interval at a concrete input: the centres `{1,3}` of the target
`2` in `{0,1,3,4}` lie in `[centerOffset 2, centerOffset 2 + ⌈9/2⌉) = [1, 6)`. -/
example : ∀ a ∈ reflectionCentersNat ({0, 1, 3, 4} : Finset ℕ) 2,
    centerOffset 2 ≤ a ∧ a < centerOffset 2 + (9 + 1) / 2 :=
  reflectionCentersNat_subset_Ico _ 2 9 (by decide)

/-- The internal integer helper at a concrete input: the centre `1` of the target
`2` in `{0,1,3,4} ⊆ [0,9)` satisfies `2 ≤ 2 * 1` and `2 * 1 - 2 < 9`. -/
example : (2 : ℤ) ≤ 2 * (1 : ℤ) ∧ 2 * (1 : ℤ) - 2 < (9 : ℤ) :=
  center_int_bounds ({0, 1, 3, 4} : Finset ℕ) 2 9 (by decide) (a := 1) (by decide)

/-- The boundary case `L = 0`: the range hypothesis forces `A = ∅`, and the cap
`rothNumberNat ⌈0/2⌉ = rothNumberNat 0 = 0` is attained. -/
example : reflectionMultiplicityNat (∅ : Finset ℕ) 7 ≤ rothNumberNat 0 :=
  reflectionMultiplicityNat_le_rothNumberNat_half _ 0 (by simp) (by simp) 7

/-- The boundary case `L = 1`: `A ⊆ {0}`, and the target `c = 0` is excluded as
a centre (`a ≠ c`), so `ν(0) = 0 ≤ rothNumberNat 1`. -/
example : reflectionMultiplicityNat ({0} : Finset ℕ) 0 = 0 ∧
    reflectionMultiplicityNat ({0} : Finset ℕ) 0 ≤ rothNumberNat 1 := by
  refine ⟨by decide, ?_⟩
  exact reflectionMultiplicityNat_le_rothNumberNat_half _ 1 (by decide) (by decide) 0

/-- The boundary case `N = 0` of the square-scale cap: `A ⊆ [0,0)` is empty and
`(0 + 1) / 2 * rothNumberNat 0 = 0`. -/
example : reflectionMultiplicityNat (∅ : Finset ℕ) 0 ≤ (0 + 1) / 2 * rothNumberNat 0 :=
  reflectionMultiplicityNat_le_ceil_half_mul_rothNumberNat _ 0 (by simp) (by simp) 0

/-- The boundary case `N = 1`: `A ⊆ {0}` and the cap is
`(1 + 1) / 2 * rothNumberNat 1 = 1`. -/
example : reflectionMultiplicityNat ({0} : Finset ℕ) 1 ≤ (1 + 1) / 2 * rothNumberNat 1 :=
  reflectionMultiplicityNat_le_ceil_half_mul_rothNumberNat _ 1 (by decide) (by decide) 1

/-- The ceiling-half square inequality at a concrete scale: `⌈25/2⌉ = 13 ≤ 3 * 5`. -/
example : (5 * 5 + 1) / 2 ≤ (5 + 1) / 2 * 5 := by decide

/-- The multiple subadditivity at a concrete scale: `rothNumberNat 6 ≤ 2 * rothNumberNat 3`. -/
example : rothNumberNat 6 ≤ 2 * rothNumberNat 3 := rothNumberNat_mul_le 2 3

/-- The abstract local cap bound at a concrete input with a non-Roth cap: `range 4`
sits in `[0,4)`, every length-`2` window contains at most `#(range 4) = 4` of its
points (trivially, by `card_filter_le`), and `4 ≤ 2 * 2`. -/
example : (Finset.range 4).card ≤ 2 * (Finset.range 4).card :=
  card_le_mul_of_local_bound (T := Finset.range 4) (lo := 0) (L := 4) (B := 4) (k := 2) (N := 2)
    (by decide) (by decide) fun _ => Finset.card_filter_le _ _

/-- The local cap bound from 3-AP-freeness at a concrete input: `{0,1,3,4}` sits in
`[0,9)`, every length-`3` window contains at most `rothNumberNat 3` of its
points, and `9 ≤ 3 * 3`. -/
example : ({0, 1, 3, 4} : Finset ℕ).card ≤ 3 * rothNumberNat 3 :=
  card_le_mul_rothNumberNat_of_local_bound
    (T := {0, 1, 3, 4}) (lo := 0) (L := 9) (k := 3) (N := 3)
    (by decide) (by decide) (by decide)

/-- The energy bound at a concrete input: for `A = {0,1,3,4}` inside `[0,9)` the
squared multiplicities of the nine targets sum to at most
`rothNumberNat 5 * reflectionMassNat A 9`. -/
example : (∑ c ∈ Finset.Ico (0 : ℤ) (9 : ℤ),
      (reflectionMultiplicityNat ({0, 1, 3, 4} : Finset ℕ) c) ^ 2)
    ≤ rothNumberNat 5 * reflectionMassNat ({0, 1, 3, 4} : Finset ℕ) 9 :=
  sum_sq_multiplicityNat_le_rothNumberNat_half _ 9 (by decide) (by decide)

end Erdos142
