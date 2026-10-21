/-
# Cyclic Hamilton decompositions of carousel tournaments: negative cases

## Source

Hongci Liao, Yongju Peng, Guang Li, Yingbin Ma, *Cyclic Hamilton Cycle
Decompositions of Carousel Tournaments of Order pq*, arXiv:2610.07102.
Recorded 2026-10-21.

Problem 1.2 (`prob:carousel`, Section 1), verbatim:

> For which odd integers $n$ does the carousel tournament $T_n$ admit a cyclic
> Hamilton cycle decomposition?

Here `T_n = Cay(ℤ_n, S_n)`, `S_n = {1, 2, …, (n-1)/2}`, and a Hamilton cycle
decomposition `𝒞` is *cyclic* if `C + 1 ∈ 𝒞` for every `C ∈ 𝒞`.  The paper proves
existence for `n = pq` with primes `7 ≤ p < q` (Theorem 1.3) and notes the prime
case is immediate.  Concluding remarks, verbatim: "The remaining products $pq$ with
$p\in\{3,5\}$, and more generally all odd composite orders, remain open."

## Status of the statements below

Open in the paper.  This module proves three *negative* answers to Problem 1.2:

* `carousel15_no_cyclic`: `T_15` has no cyclic Hamilton cycle decomposition;
* `carousel21_no_cyclic`: `T_21` has none;
* `carousel_primePow_no_cyclic`: `T_{p^a}` has none for odd primes `p`, `a ≥ 2`.

Reportedly (triage, from the abstract of Buratti–Del Fra, Discrete Math. 279
(2004); the paper itself was not checked) the cases `15` and `p^a` also follow
after forgetting orientations, while `21` does not (`K_21` has a cyclic Hamilton
cycle system).  `carousel5_cyclic` instantiates the definition positively
(the paper's prime construction at `n = 5`).

## Encoding

A Hamilton cycle is encoded by its successor permutation `σ` of `ZMod n` (a single
cycle moving every vertex; arcs `x → σ x`).  A decomposition is a set `D` of such
permutations whose arcs are arcs of `T_n` and such that each arc of `T_n` lies in
exactly one member of `D`.  Translation of a cycle by `t` is conjugation by
`x ↦ x + t`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.CarouselTournamentCyclicDecomposition

open Equiv

/-- Arc relation of the carousel tournament `T_n = Cay(ℤ_n, {1, …, (n-1)/2})`:
there is an arc `x → y` iff the difference `y - x` lies in `{1, …, (n-1)/2}`. -/
def carouselArc (n : ℕ) (x y : ZMod n) : Prop :=
  1 ≤ (y - x).val ∧ (y - x).val ≤ (n - 1) / 2

/-- Translation of a cyclic permutation `σ` (read as the directed cycle with arcs
`x → σ x`) by `t`: the arc `(x, y)` becomes `(x + t, y + t)`. -/
def translate {n : ℕ} (t : ZMod n) (σ : Perm (ZMod n)) : Perm (ZMod n) :=
  ((Equiv.addRight t).symm.trans σ).trans (Equiv.addRight t)

/-- A Hamilton cycle on `ZMod n`, encoded as its successor permutation: a single
cycle moving every vertex. -/
def IsHamiltonCycle {n : ℕ} (σ : Perm (ZMod n)) : Prop :=
  σ.IsCycle ∧ ∀ x, σ x ≠ x

/-- A cyclic Hamilton cycle decomposition of `T_n`: a family `D` of Hamilton cycles
of `T_n` such that every arc of `T_n` lies in exactly one member of `D`, and `D` is
closed under translation by `1`. -/
def IsCyclicHamDecomp (n : ℕ) (D : Set (Perm (ZMod n))) : Prop :=
  (∀ σ ∈ D, IsHamiltonCycle σ ∧ ∀ x, carouselArc n x (σ x)) ∧
  (∀ x y, carouselArc n x y → ∃! σ, σ ∈ D ∧ σ x = y) ∧
  (∀ σ ∈ D, translate 1 σ ∈ D)

/-- Ground truth: in `T_7` (`S_7 = {1,2,3}`) there are arcs `0 → 3` and `5 → 1`
(difference `3`), but no arc `0 → 4`. -/
example : carouselArc 7 0 3 ∧ carouselArc 7 5 1 ∧ ¬ carouselArc 7 0 4 := by
  unfold carouselArc; decide

/-- Translating a cycle by `t` sends `x ↦ σ (x - t) + t`. -/
theorem translate_apply {n : ℕ} (t : ZMod n) (σ : Perm (ZMod n)) (x : ZMod n) :
    translate t σ x = σ (x - t) + t := by
  simp [translate, sub_eq_add_neg]

/-- `σ` commutes with translation by `u`. -/
def Commutes {n : ℕ} (σ : Perm (ZMod n)) (u : ZMod n) : Prop :=
  ∀ x, σ (x + u) = σ x + u

section general

variable {n : ℕ} {D : Set (Perm (ZMod n))}

/-- Translation by `0` is the identity. -/
theorem translate_zero (σ : Perm (ZMod n)) : translate 0 σ = σ := by
  ext x; simp [translate_apply]

/-- Translating by `t` then by `1` is translating by `t + 1`. -/
theorem translate_add_one (t : ZMod n) (σ : Perm (ZMod n)) :
    translate 1 (translate t σ) = translate (t + 1) σ := by
  ext x; simp only [translate_apply]; ring_nf

/-- A cyclic decomposition is closed under every translation. -/
theorem translate_mem [NeZero n] (hD : IsCyclicHamDecomp n D) {σ : Perm (ZMod n)}
    (hσ : σ ∈ D) (t : ZMod n) : translate t σ ∈ D := by
  have key : ∀ k : ℕ, translate (k : ZMod n) σ ∈ D := by
    intro k
    induction k with
    | zero => simpa [translate_zero] using hσ
    | succ k ih =>
      have h := hD.2.2 _ ih
      rw [translate_add_one] at h
      simpa using h
  simpa using key t.val

/-- Two members of a decomposition sharing an arc `x → σ x` coincide. -/
theorem eq_of_apply_eq (hD : IsCyclicHamDecomp n D) {σ τ : Perm (ZMod n)} (hσ : σ ∈ D)
    (hτ : τ ∈ D) {x : ZMod n} (h : σ x = τ x) : σ = τ := by
  obtain ⟨ρ, -, hρ⟩ := hD.2.1 x (σ x) ((hD.1 σ hσ).2 x)
  exact (hρ σ ⟨hσ, rfl⟩).trans (hρ τ ⟨hτ, h.symm⟩).symm

/-- If `σ ∈ D` satisfies `σ (x + u) = σ x + u` at a single point, it commutes with
translation by `u` everywhere (uniqueness of the cycle through an arc). -/
theorem commutes_of_apply [NeZero n] (hD : IsCyclicHamDecomp n D) {σ : Perm (ZMod n)}
    (hσ : σ ∈ D)    {x u : ZMod n} (h : σ (x + u) = σ x + u) : Commutes σ u := by
  have hmem := translate_mem hD hσ u
  have heq : translate u σ = σ := by
    refine eq_of_apply_eq hD hmem hσ (x := x + u) ?_
    rw [translate_apply, add_sub_cancel_right, h]
  intro y
  have hy := congrArg (fun ρ : Perm (ZMod n) => ρ (y + u)) heq
  simp only [translate_apply, add_sub_cancel_right] at hy
  exact hy.symm

/-- Commuting translations are closed under addition. -/
theorem Commutes.add {σ : Perm (ZMod n)} {u v : ZMod n} (hu : Commutes σ u)
    (hv : Commutes σ v) : Commutes σ (u + v) := by
  intro x
  rw [← add_assoc, hv, hu, add_assoc]

/-- Commuting translations are closed under natural multiples. -/
theorem Commutes.nsmul {σ : Perm (ZMod n)} {u : ZMod n} (hu : Commutes σ u) (k : ℕ) :
    Commutes σ (k • u) := by
  induction k with
  | zero => intro x; simp
  | succ k ih => rw [succ_nsmul]; exact ih.add hu

/-- Commuting translations are closed under multiplication by elements of `ZMod n`. -/
theorem Commutes.mul_left [NeZero n] {σ : Perm (ZMod n)} {u : ZMod n} (hu : Commutes σ u)
    (k : ZMod n) :
    Commutes σ (k * u) := by
  have h := hu.nsmul k.val
  rwa [nsmul_eq_mul, ZMod.natCast_zmod_val] at h

/-- Commuting translations form a subgroup: closed under `ZMod n`-linear combinations. -/
theorem Commutes.lin [NeZero n] {σ : Perm (ZMod n)} {u v : ZMod n} (hu : Commutes σ u)
    (hv : Commutes σ v) (k l : ZMod n) : Commutes σ (k * u + l * v) :=
  (hu.mul_left k).add (hv.mul_left l)

/-- Along a cycle commuting with `u` whose step at `x` is `u`, the orbit of `x` is
`x, x + u, x + 2u, …`. -/
theorem pow_apply_of_commutes {σ : Perm (ZMod n)} {u x : ZMod n} (hu : Commutes σ u)
    (hx : σ x = x + u) (k : ℕ) : (σ ^ k) x = x + k • u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih, hu.nsmul k, hx, succ_nsmul]; abel

/-- A Hamilton cycle on `ZMod n` returns to no vertex in fewer than `n` steps. -/
theorem IsHamiltonCycle.pow_apply_ne [NeZero n] {σ : Perm (ZMod n)} (hσ : IsHamiltonCycle σ)
    {m : ℕ} (hm0 : 0 < m) (hmn : m < n) (x : ZMod n) : (σ ^ m) x ≠ x := by
  intro hfix
  have hone : σ ^ m = 1 := hσ.1.pow_eq_one_iff.2 ⟨x, hσ.2 x, hfix⟩
  have hsupp : σ.support = Finset.univ := by
    ext y; simpa [Perm.mem_support] using hσ.2 y
  have hord : orderOf σ = n := by
    rw [hσ.1.orderOf, hsupp, Finset.card_univ, ZMod.card]
  have hdvd : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one hone
  rw [hord] at hdvd
  exact absurd (Nat.le_of_dvd hm0 hdvd) (by omega)

/-- A cycle of `D` whose step at `x` is `u`, where `m • u = 0` for some `0 < m < n`,
cannot commute with translation by `u`. -/
theorem not_commutes_step [NeZero n] (hD : IsCyclicHamDecomp n D) {σ : Perm (ZMod n)} (hσ : σ ∈ D)
    {x u : ZMod n} (hx : σ x = x + u) {m : ℕ} (hm0 : 0 < m) (hmn : m < n)
    (hmu : m • u = 0) : ¬ Commutes σ u := by
  intro hu
  apply (hD.1 σ hσ).1.pow_apply_ne hm0 hmn x
  rw [pow_apply_of_commutes hu hx, hmu, add_zero]

/-- Equal steps at two vertices force commutation with their difference. -/
theorem commutes_of_step_eq [NeZero n] (hD : IsCyclicHamDecomp n D) {σ : Perm (ZMod n)} (hσ : σ ∈ D)
    {x y : ZMod n} (h : σ x - x = σ y - y) : Commutes σ (x - y) := by
  refine commutes_of_apply hD hσ (x := y) ?_
  rw [add_sub_cancel]
  linear_combination h

/-- Two cycles of `D` sharing a step value are translates of each other, so they
commute with the same translations. -/
theorem commutes_of_shared_step [NeZero n] (hD : IsCyclicHamDecomp n D) {σ τ : Perm (ZMod n)}
    (hσ : σ ∈ D) (hτ : τ ∈ D) {x y : ZMod n} (h : σ x - x = τ y - y) {u : ZMod n}
    (hu : Commutes τ u) : Commutes σ u := by
  have heq : translate (y - x) σ = τ := by
    refine eq_of_apply_eq hD (translate_mem hD hσ _) hτ (x := y) ?_
    rw [translate_apply, sub_sub_cancel]
    linear_combination h
  intro z
  have hz : ∀ w, σ w = τ (w + (y - x)) - (y - x) := by
    intro w
    rw [← heq, translate_apply, add_sub_cancel_right, add_sub_cancel_right]
  rw [hz, hz, add_right_comm, hu]
  ring

/-- Pigeonhole: every cycle of `D` commutes with some nonzero translation, since its
`n` steps take at most `(n-1)/2 < n` values. -/
theorem exists_commutes [NeZero n] (hD : IsCyclicHamDecomp n D) {σ : Perm (ZMod n)} (hσ : σ ∈ D) :
    ∃ u : ZMod n, u ≠ 0 ∧ Commutes σ u := by
  have hlt : (Finset.Icc 1 ((n - 1) / 2)).card < (Finset.univ : Finset (ZMod n)).card := by
    rw [Nat.card_Icc, Finset.card_univ, ZMod.card]
    have := NeZero.pos n
    omega
  have hmaps : Set.MapsTo (fun x : ZMod n => (σ x - x).val)
      (Finset.univ : Finset (ZMod n)) (Finset.Icc 1 ((n - 1) / 2)) := by
    intro x _
    have hx := (hD.1 σ hσ).2 x
    simpa [carouselArc, Finset.mem_Icc] using hx
  obtain ⟨x, -, y, -, hxy, hval⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  exact ⟨x - y, sub_ne_zero.2 hxy, commutes_of_step_eq hD hσ (ZMod.val_injective n hval)⟩

/-- Dichotomy step: if every nonzero `u` generates (a subgroup containing) `v` or `w`,
and `σ` cannot commute with `v`, then `σ` commutes with `w`. -/
theorem commutes_of_dichotomy [NeZero n] (hD : IsCyclicHamDecomp n D) {σ : Perm (ZMod n)}
    (hσ : σ ∈ D) {v w : ZMod n} (hv : ¬ Commutes σ v)
    (hfact : ∀ u : ZMod n, u ≠ 0 → (∃ k : ZMod n, k * u = v) ∨ ∃ k : ZMod n, k * u = w) :
    Commutes σ w := by
  obtain ⟨u, hu0, hu⟩ := exists_commutes hD hσ
  rcases hfact u hu0 with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact absurd (hk ▸ hu.mul_left k) hv
  · exact hk ▸ hu.mul_left k

/-- The steps `σ i - i`, `i < m`, of a cycle commuting with `w` but not with `v` are
pairwise distinct, provided every difference `i - j` together with `w` generates `v`. -/
theorem injOn_steps [NeZero n] (hD : IsCyclicHamDecomp n D) {σ : Perm (ZMod n)}
    (hσ : σ ∈ D) {v w : ZMod n} (hw : Commutes σ w) (hv : ¬ Commutes σ v) {m : ℕ}
    (hfact : ∀ i < m, ∀ j < m, i ≠ j →
      ∃ k l : ZMod n, k * ((i : ZMod n) - j) + l * w = v) :
    Set.InjOn (fun i : ℕ => σ (i : ZMod n) - i) (Finset.range m) := by
  intro i hi j hj hij
  by_contra hne
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  obtain ⟨k, l, hkl⟩ := hfact i hi j hj hne
  exact hv (hkl ▸ (commutes_of_step_eq hD hσ hij).lin hw k l)

/-- Iterated periodicity of a function on `ℕ`. -/
theorem periodic_mul {M : Type*} (g : ℕ → M) (m : ℕ) (hg : ∀ t, g (t + m) = g t)
    (k t : ℕ) : g (m * k + t) = g t := by
  induction k with
  | zero => simp
  | succ k ih => rw [mul_add, mul_one, add_right_comm, hg, ih]

/-- Sum of an `m`-periodic function over `range (m * k)`. -/
theorem sum_range_periodic {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m : ℕ)
    (hg : ∀ t, g (t + m) = g t) (k : ℕ) :
    ∑ t ∈ Finset.range (m * k), g t = k • ∑ i ∈ Finset.range m, g i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [mul_add, mul_one, Finset.sum_range_add, ih, succ_nsmul]
    simp only [periodic_mul g m hg]

/-- Sum over `ZMod n` as a sum over `range n`. -/
theorem sum_zmod_eq_sum_range [NeZero n] {M : Type*} [AddCommMonoid M] (f : ZMod n → M) :
    ∑ x, f x = ∑ t ∈ Finset.range n, f t := by
  refine Finset.sum_bij' (fun x _ => x.val) (fun t _ => (t : ZMod n)) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro t _; exact Finset.mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro t ht; exact ZMod.val_cast_of_lt (Finset.mem_range.1 ht)
  · intro x _; rw [ZMod.natCast_zmod_val]

/-- Winding: the steps of a permutation sum to `0`; if `σ` commutes with translation
by `m` and `n = m * k`, then `k` times the sum of the first `m` steps vanishes. -/
theorem winding [NeZero n] {σ : Perm (ZMod n)} {m k : ℕ} (hn : n = m * k)
    (hm : Commutes σ (m : ZMod n)) :
    k • ∑ i ∈ Finset.range m, (σ (i : ZMod n) - i) = 0 := by
  have htot : ∑ x, (σ x - x) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp σ (fun x => x), sub_self]
  have hr : Finset.range n = Finset.range (m * k) := by rw [hn]
  rw [sum_zmod_eq_sum_range, hr,
    sum_range_periodic (fun t : ℕ => σ (t : ZMod n) - t) m ?_ k] at htot
  · exact htot
  · intro t
    simp only [Nat.cast_add]
    rw [hm]; ring

end general

/-! ## Non-vacuity: the prime case `n = 5` -/

/-- Powers of a translation. -/
theorem pow_addRight_apply {n : ℕ} (c x : ZMod n) (k : ℕ) :
    ((Equiv.addRight c) ^ k) x = x + k • c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih, succ_nsmul, coe_addRight]
    exact add_assoc _ _ _

/-- Translation by a generator `c` of `ZMod n` is a Hamilton cycle. -/
theorem isHamiltonCycle_addRight {n : ℕ} (c : ZMod n) (hc0 : c ≠ 0)
    (hgen : ∀ y : ZMod n, ∃ k : ℕ, k • c = y) : IsHamiltonCycle (Equiv.addRight c) := by
  refine ⟨⟨0, by simpa using hc0, fun y _ => ?_⟩, fun x => by simpa using hc0⟩
  obtain ⟨k, hk⟩ := hgen y
  exact ⟨k, by rw [zpow_natCast, pow_addRight_apply, zero_add, hk]⟩

/-- The paper's prime-order construction at `n = 5`: the two translations `x ↦ x + 1`
and `x ↦ x + 2` form a cyclic Hamilton cycle decomposition of `T_5`.  This exhibits
`IsCyclicHamDecomp` as satisfiable. -/
theorem carousel5_cyclic :
    IsCyclicHamDecomp 5 {Equiv.addRight 1, Equiv.addRight 2} := by
  have hS : ∀ c : ZMod 5, 1 ≤ c.val ∧ c.val ≤ 2 ↔ c = 1 ∨ c = 2 := by decide
  have hgen : ∀ c : ZMod 5, c ≠ 0 → ∀ y : ZMod 5, ∃ k : ℕ, k < 5 ∧ k • c = y := by decide
  have hmem : ∀ σ : Perm (ZMod 5), σ ∈ ({Equiv.addRight 1, Equiv.addRight 2} :
      Set (Perm (ZMod 5))) ↔ ∃ c : ZMod 5, (c = 1 ∨ c = 2) ∧ σ = Equiv.addRight c := by
    intro σ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact ⟨1, Or.inl rfl, h⟩
      · exact ⟨2, Or.inr rfl, h⟩
    · rintro ⟨c, hc | hc, rfl⟩ <;> subst hc <;> simp
  refine ⟨?_, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨c, hc, rfl⟩ := (hmem σ).1 hσ
    have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> decide
    refine ⟨isHamiltonCycle_addRight c hc0 fun y => ?_, fun x => ?_⟩
    · obtain ⟨k, -, hk⟩ := hgen c hc0 y
      exact ⟨k, hk⟩
    · show 1 ≤ (x + c - x).val ∧ (x + c - x).val ≤ (5 - 1) / 2
      rw [add_sub_cancel_left]
      exact (hS c).2 hc
  · intro x y hxy
    refine ⟨Equiv.addRight (y - x), ⟨(hmem _).2 ⟨y - x, (hS _).1 hxy, rfl⟩, ?_⟩, ?_⟩
    · simp
    · rintro σ ⟨hσ, hσx⟩
      obtain ⟨c, -, rfl⟩ := (hmem σ).1 hσ
      have hc : c = y - x := by rw [← hσx, coe_addRight]; ring
      rw [hc]
  · intro σ hσ
    obtain ⟨c, hc, rfl⟩ := (hmem σ).1 hσ
    have htr : translate 1 (Equiv.addRight c) = Equiv.addRight c := by
      ext x
      rw [translate_apply, coe_addRight]
      show x - 1 + c + 1 = x + c
      ring
    rw [htr]
    exact (hmem _).2 ⟨c, hc, rfl⟩

/-! ## Order 15 -/

/-- **`T_15` has no cyclic Hamilton cycle decomposition.**  Difference `5` (of additive
order 3) forces its cycle to commute with `+3`, giving a block of 3 distinct steps;
difference `3` (order 5) forces its cycle to commute with `+5`, giving a block of 5
distinct steps; the blocks are disjoint, but `3 + 5 = 8 > 7 = |S_15|`.  This settles
the case `n = 15 = 3 · 5` of Problem 1.2 of arXiv:2610.07102 (left open there). -/
theorem carousel15_no_cyclic : ¬ ∃ D, IsCyclicHamDecomp 15 D := by
  rintro ⟨D, hD⟩
  obtain ⟨σ, ⟨hσ, hσ0⟩, -⟩ := hD.2.1 0 5 (by unfold carouselArc; decide)
  obtain ⟨τ, ⟨hτ, hτ0⟩, -⟩ := hD.2.1 0 3 (by unfold carouselArc; decide)
  have hσ5 : ¬ Commutes σ 5 :=
    not_commutes_step hD hσ (x := 0) (by rw [hσ0, zero_add]) (m := 3) (by norm_num)
      (by norm_num) (by decide)
  have hτ3 : ¬ Commutes τ 3 :=
    not_commutes_step hD hτ (x := 0) (by rw [hτ0, zero_add]) (m := 5) (by norm_num)
      (by norm_num) (by decide)
  have hσ3 : Commutes σ 3 := commutes_of_dichotomy hD hσ hσ5 (by decide)
  have hτ5 : Commutes τ 5 := commutes_of_dichotomy hD hτ hτ3 (by decide)
  let a : ℕ → ZMod 15 := fun i => σ (i : ZMod 15) - i
  let b : ℕ → ZMod 15 := fun i => τ (i : ZMod 15) - i
  have hA : ((Finset.range 3).image a).card = 3 := by
    rw [Finset.card_image_of_injOn (injOn_steps hD hσ hσ3 hσ5 (by decide)),
      Finset.card_range]
  have hB : ((Finset.range 5).image b).card = 5 := by
    rw [Finset.card_image_of_injOn (injOn_steps hD hτ hτ5 hτ3 (by decide)),
      Finset.card_range]
  have hdisj : Disjoint ((Finset.range 3).image a) ((Finset.range 5).image b) := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hyA
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hyB
    exact hσ5 (commutes_of_shared_step hD hσ hτ hj.symm hτ5)
  let S : Finset (ZMod 15) := Finset.univ.filter fun y => 1 ≤ y.val ∧ y.val ≤ 7
  have hS : S.card = 7 := by decide
  have hsub : (Finset.range 3).image a ∪ (Finset.range 5).image b ⊆ S := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hD.1 σ hσ).2 _⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hD.1 τ hτ).2 _⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hA, hB, hS] at hcard
  omega

/-! ## Order 21 -/

/-- Converting the winding identity in `ZMod n` to divisibility of the natural sum of
step values. -/
theorem dvd_sum_val_of_winding {n : ℕ} [NeZero n] (f : ℕ → ZMod n) (m k : ℕ)
    (h : k • ∑ i ∈ Finset.range m, f i = 0) : n ∣ k * ∑ i ∈ Finset.range m, (f i).val := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [ZMod.natCast_val, ZMod.cast_id', id]
  rw [← nsmul_eq_mul]
  exact h

/-- **`T_21` has no cyclic Hamilton cycle decomposition.**  Difference `7` forces its
cycle to commute with `+3` (a block `A` of 3 distinct steps containing `7`, with
`3 ∣ ΣA` by winding); difference `3` forces its cycle to commute with `+7` (a block
`B` of 7 distinct steps with `7 ∣ ΣB`).  The blocks are disjoint, hence partition
`S_21 = {1, …, 10}`, so `ΣA + ΣB = 55`; no admissible `A` exists.  This settles the
case `n = 21 = 3 · 7` of Problem 1.2 of arXiv:2610.07102 (left open there). -/
theorem carousel21_no_cyclic : ¬ ∃ D, IsCyclicHamDecomp 21 D := by
  rintro ⟨D, hD⟩
  obtain ⟨σ, ⟨hσ, hσ0⟩, -⟩ := hD.2.1 0 7 (by unfold carouselArc; decide)
  obtain ⟨τ, ⟨hτ, hτ0⟩, -⟩ := hD.2.1 0 3 (by unfold carouselArc; decide)
  have hσ7 : ¬ Commutes σ 7 :=
    not_commutes_step hD hσ (x := 0) (by rw [hσ0, zero_add]) (m := 3) (by norm_num)
      (by norm_num) (by decide)
  have hτ3 : ¬ Commutes τ 3 :=
    not_commutes_step hD hτ (x := 0) (by rw [hτ0, zero_add]) (m := 7) (by norm_num)
      (by norm_num) (by decide)
  have hσ3 : Commutes σ 3 := commutes_of_dichotomy hD hσ hσ7 (by decide)
  have hτ7 : Commutes τ 7 := commutes_of_dichotomy hD hτ hτ3 (by decide)
  let a : ℕ → ZMod 21 := fun i => σ (i : ZMod 21) - i
  let b : ℕ → ZMod 21 := fun i => τ (i : ZMod 21) - i
  have hinjA := injOn_steps hD hσ hσ3 hσ7 (m := 3) (by decide)
  have hinjB := injOn_steps hD hτ hτ7 hτ3 (m := 7) (by decide)
  have hA : ((Finset.range 3).image a).card = 3 := by
    rw [Finset.card_image_of_injOn hinjA, Finset.card_range]
  have hB : ((Finset.range 7).image b).card = 7 := by
    rw [Finset.card_image_of_injOn hinjB, Finset.card_range]
  have hdisj : Disjoint ((Finset.range 3).image a) ((Finset.range 7).image b) := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hyA
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hyB
    exact hσ7 (commutes_of_shared_step hD hσ hτ hj.symm hτ7)
  let S : Finset (ZMod 21) := Finset.univ.filter fun y => 1 ≤ y.val ∧ y.val ≤ 10
  have hS : S.card = 10 := by decide
  have hSsum : ∑ y ∈ S, y.val = 55 := by decide
  have hsub : (Finset.range 3).image a ∪ (Finset.range 7).image b ⊆ S := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hD.1 σ hσ).2 _⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hD.1 τ hτ).2 _⟩
  have hunion : (Finset.range 3).image a ∪ (Finset.range 7).image b = S := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_union_of_disjoint hdisj, hA, hB, hS]
  -- the two block sums add up to `55`
  have hsplit : ∑ i ∈ Finset.range 3, (a i).val + ∑ j ∈ Finset.range 7, (b j).val = 55 := by
    rw [← Finset.sum_image (f := ZMod.val) hinjA, ← Finset.sum_image (f := ZMod.val) hinjB,
      ← Finset.sum_union hdisj, hunion, hSsum]
  -- winding congruences
  have hwA : 21 ∣ 7 * ∑ i ∈ Finset.range 3, (a i).val :=
    dvd_sum_val_of_winding a 3 7 (winding (by norm_num) (by exact_mod_cast hσ3))
  have hwB : 21 ∣ 3 * ∑ j ∈ Finset.range 7, (b j).val :=
    dvd_sum_val_of_winding b 7 3 (winding (by norm_num) (by exact_mod_cast hτ7))
  -- the block `A = {7, a 1, a 2}`
  have ha0 : (a 0).val = 7 := by
    show (σ ((0 : ℕ) : ZMod 21) - ((0 : ℕ) : ZMod 21)).val = 7
    rw [Nat.cast_zero, hσ0, sub_zero]
    rfl
  have hval : ∀ i, 1 ≤ (a i).val ∧ (a i).val ≤ 10 := fun i => (hD.1 σ hσ).2 _
  have ha12 : (a 1).val ≠ (a 2).val := by
    intro h
    have := hinjA (by simp) (by simp) (ZMod.val_injective _ h)
    omega
  have hAsum : ∑ i ∈ Finset.range 3, (a i).val = 7 + (a 1).val + (a 2).val := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, ha0]
  rw [hAsum] at hsplit hwA
  have h1 := hval 1
  have h2 := hval 2
  omega

/-! ## Prime powers -/

/-- In `ZMod (p ^ a)` every nonzero element has a multiple equal to `p ^ (a - 1)`:
every nontrivial subgroup of `ℤ_{p^a}` contains `p ^ (a - 1)`. -/
theorem exists_mul_eq_prime_pow_pred {p a : ℕ} (hp : p.Prime) (u : ZMod (p ^ a))
    (hu : u ≠ 0) : ∃ k : ZMod (p ^ a), k * u = ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) := by
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hv0 : u.val ≠ 0 := fun h => hu ((ZMod.val_eq_zero u).1 h)
  have hvlt : u.val < p ^ a := ZMod.val_lt u
  obtain ⟨b, hb, hg⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right u.val (p ^ a))
  have hba : b < a := by
    rcases lt_or_eq_of_le hb with h | h
    · exact h
    · exfalso
      have hdvd := Nat.gcd_dvd_left u.val (p ^ a)
      rw [hg, h] at hdvd
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) hdvd) (by omega)
  obtain ⟨c, hc⟩ : p ^ b ∣ p ^ (a - 1) := pow_dvd_pow p (by omega)
  refine ⟨(Nat.gcdA u.val (p ^ a) : ZMod (p ^ a)) * c, ?_⟩
  have hbez := congrArg (Int.cast : ℤ → ZMod (p ^ a)) (Nat.gcd_eq_gcd_ab u.val (p ^ a))
  have hpa0 : ((p : ZMod (p ^ a))) ^ a = 0 := by exact_mod_cast ZMod.natCast_self (p ^ a)
  push_cast [ZMod.natCast_val, ZMod.cast_id', id] at hbez
  rw [hpa0, zero_mul, add_zero] at hbez
  rw [hc, Nat.cast_mul, ← hg, hbez]
  ring

/-- **`T_{p^a}` has no cyclic Hamilton cycle decomposition** for an odd prime `p` and
`a ≥ 2`.  The difference `d = p^(a-1)` lies in `S_{p^a}`; the cycle through the arc
`0 → d` commutes with some nonzero translation (pigeonhole), hence with `d` (every
nontrivial subgroup of `ℤ_{p^a}` contains `d`), so it closes up after `p < p^a`
steps.  This settles the proper prime-power orders in Problem 1.2 of
arXiv:2610.07102 (left open there). -/
theorem carousel_primePow_no_cyclic (p a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a) :
    ¬ ∃ D, IsCyclicHamDecomp (p ^ a) D := by
  rintro ⟨D, hD⟩
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpa : p ^ a = p * p ^ (a - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hlt : p ^ (a - 1) < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  set d : ZMod (p ^ a) := ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) with hd
  have hdval : d.val = p ^ (a - 1) := ZMod.val_cast_of_lt hlt
  have harc : carouselArc (p ^ a) 0 d := by
    unfold carouselArc
    rw [sub_zero, hdval]
    have hq : 1 ≤ p ^ (a - 1) := Nat.one_le_pow _ _ hp.pos
    have h3 : 3 * p ^ (a - 1) ≤ p * p ^ (a - 1) := Nat.mul_le_mul_right _ hp3
    refine ⟨hq, ?_⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  obtain ⟨σ, ⟨hσ, hσ0⟩, -⟩ := hD.2.1 0 d harc
  obtain ⟨u, hu0, hu⟩ := exists_commutes hD hσ
  obtain ⟨k, hk⟩ := exists_mul_eq_prime_pow_pred hp u hu0
  have hcd : Commutes σ d := by
    have h := hu.mul_left k
    rwa [hk] at h
  have hpd : p • d = 0 := by
    rw [hd, nsmul_eq_mul, ← Nat.cast_mul, ← hpa, ZMod.natCast_self]
  have hplt : p < p ^ a := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  exact not_commutes_step hD hσ (x := 0) (by rw [hσ0, zero_add]) hp.pos hplt hpd hcd

/-- Instances of the prime-power theorem: `T_9`, `T_25`, `T_27` have no cyclic
Hamilton cycle decomposition. -/
example : (¬ ∃ D, IsCyclicHamDecomp 9 D) ∧ (¬ ∃ D, IsCyclicHamDecomp 25 D) ∧
    ¬ ∃ D, IsCyclicHamDecomp 27 D :=
  ⟨carousel_primePow_no_cyclic 3 2 Nat.prime_three (by norm_num) le_rfl,
    carousel_primePow_no_cyclic 5 2 Nat.prime_five (by norm_num) le_rfl,
    carousel_primePow_no_cyclic 3 3 Nat.prime_three (by norm_num) (by norm_num)⟩

end Candidates.CarouselTournamentCyclicDecomposition
