/-
# `(6,6,6,10,15)` is `A₅`-harmonic but not `ℤ`-harmonic

## Source

Murali Menon, *Two Questions on G-Harmonic Tuples*, arXiv:2608.15873.
Theorem 3.1 (with Lemma 2.1(i) for the `ℤ` side), Section 3; the
explicit subgroups and coset representatives are in the proof of
Theorem 3.1 and in the appendix GAP code.  Recorded 2026-10-21.

Definitions (Introduction, after Margolis–Schnabel, Definition 1.1):

> An `n`-tuple of positive integers `(a₁,…,aₙ)` is called *`G`-harmonic* if
> there exist subgroups `Uᵢ ≤ G` of index `aᵢ` and elements `gᵢ ∈ G` such
> that the cosets `g₁U₁,…,gₙUₙ` are pairwise disjoint.  The same tuple is
> *`ℤ`-harmonic* if there exist integers `rᵢ` with
> `rᵢ ≢ rⱼ (mod gcd(aᵢ,aⱼ))` for `i ≠ j`.

Claim (Theorem 3.1, verbatim):

> The tuple `(6,6,6,10,15)` is `A₅`-harmonic but not `ℤ`-harmonic.

This answers Ginosar's Question 1 ("Is every `G`-harmonic tuple also
`ℤ`-harmonic?", recorded by Margolis–Schnabel) negatively.

Also formalized here: Lemma 2.1(i) in general (three entries `6`, an entry
`x` with `gcd(6,x) = 2`, an entry `y` with `gcd(6,y) = 3` ⇒ not `ℤ`-harmonic),
and Corollary 3.2 (the five cosets extend to a coset partition of `A₅` with
index tuple `(6,6,6,10,15,15,15,10,10)`, which is `A₅`-harmonic but not
`ℤ`-harmonic).

## Status

Proved in the paper (the `A₅` side by a finite GAP computation, the `ℤ`
side by the residue argument of Lemma 2.1(i)).  Every statement in this file
is proved; the finite group checks are kernel `decide` over explicit
permutation tables (no `native_decide`).

## Conventions

Mathlib multiplies permutations right-to-left, `(σ * τ) x = σ (τ x)`, while
GAP multiplies left-to-right.  GAP's `{u * g : u ∈ H}` is therefore Mathlib's
`{g * u : u ∈ H} = g • H`, the same left coset as in the paper.  Points
`1,…,5` of the paper are `0,…,4 : Fin 5` here.
-/
import Mathlib

set_option autoImplicit false

namespace HarmonicTupleA5

open Equiv Pointwise

/-! ## Definitions -/

/-- A tuple `a : Fin n → ℕ` is *`ℤ`-harmonic* if there are integers `rᵢ` with
`rᵢ ≢ rⱼ (mod gcd(aᵢ, aⱼ))` whenever `i ≠ j` (arXiv:2608.15873, Introduction). -/
def ZHarmonic {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∃ r : Fin n → ℤ, ∀ i j, i ≠ j → ¬ ((Nat.gcd (a i) (a j) : ℤ) ∣ r i - r j)

/-- A tuple `a : Fin n → ℕ` is *`G`-harmonic* if there are subgroups `Uᵢ ≤ G`
with `[G : Uᵢ] = aᵢ` and elements `gᵢ ∈ G` such that the left cosets `gᵢ Uᵢ`
are pairwise disjoint (arXiv:2608.15873, Introduction; Margolis–Schnabel,
Definition 1.1).  For positive `aᵢ` the condition `index = aᵢ` forces finite
index, since `Subgroup.index` is `0` on infinite-index subgroups. -/
def GHarmonic (G : Type*) [Group G] {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∃ (U : Fin n → Subgroup G) (g : Fin n → G), (∀ i, (U i).index = a i) ∧
    Pairwise fun i j => Disjoint (g i • (U i : Set G)) (g j • (U j : Set G))

/-! ### Ground truth for `ZHarmonic`

The paper's appendix states that every 4-subtuple of `(6,6,6,10,15)` is
`ℤ`-harmonic; we check two of them with explicit witnesses. -/

/-- `(6,6,6,10)` is `ℤ`-harmonic, witnessed by residues `(1,3,5,0)`. -/
example : ZHarmonic ![6, 6, 6, 10] :=
  ⟨![1, 3, 5, 0], by decide⟩

/-- `(6,6,6,15)` is `ℤ`-harmonic, witnessed by residues `(0,1,3,2)`. -/
example : ZHarmonic ![6, 6, 6, 15] :=
  ⟨![0, 1, 3, 2], by decide⟩

/-- `(6,6,10,15)` is `ℤ`-harmonic, witnessed by residues `(1,3,0,2)`. -/
example : ZHarmonic ![6, 6, 10, 15] :=
  ⟨![1, 3, 0, 2], by decide⟩

/-- A residue choice that collides modulo `gcd` is not a witness. -/
example : ¬ ∀ i j : Fin 2, i ≠ j →
    ¬ ((Nat.gcd ((![6, 10] : Fin 2 → ℕ) i) (![6, 10] j) : ℤ) ∣ (![1, 3] : Fin 2 → ℤ) i - ![1, 3] j) := by
  decide

/-! ### Ground truth for `GHarmonic` -/

/-- The single-entry tuple `(1)` is `G`-harmonic in every group, via `U = ⊤`. -/
example (G : Type*) [Group G] : GHarmonic G ![1] :=
  ⟨fun _ => ⊤, fun _ => 1, fun i => by fin_cases i; simp,
    fun i j hij => absurd (Subsingleton.elim i j) hij⟩

/-! ## The `ℤ` side: Lemma 2.1(i) -/

/-- **Lemma 2.1(i)** (arXiv:2608.15873): if three entries of a tuple equal `6`, some
entry `x` has `gcd(6, x) = 2` and some entry `y` has `gcd(6, y) = 3`, then the tuple
is not `ℤ`-harmonic.  The three `6`-residues are distinct mod `6`, the `x`-entry
forces them to share a parity, so they meet every class mod `3`, which the
`y`-entry forbids. -/
theorem not_zHarmonic_of_three_six {n : ℕ} (a : Fin n → ℕ) (i₁ i₂ i₃ x y : Fin n)
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (ha₁ : a i₁ = 6) (ha₂ : a i₂ = 6) (ha₃ : a i₃ = 6)
    (hx : Nat.gcd 6 (a x) = 2) (hy : Nat.gcd 6 (a y) = 3) : ¬ ZHarmonic a := by
  rintro ⟨r, hr⟩
  -- read off a pairwise condition with its `gcd` evaluated
  have hd : ∀ (i j : Fin n) (d : ℕ), Nat.gcd (a i) (a j) = d → i ≠ j →
      ¬ (d : ℤ) ∣ r i - r j := by
    rintro i j d rfl hij
    exact hr i j hij
  -- a `6`-entry is neither the `x`-entry nor the `y`-entry
  have hne : ∀ k, a k = 6 → k ≠ x ∧ k ≠ y := by
    intro k hk
    constructor
    · rintro rfl
      rw [hk] at hx
      exact absurd hx (by decide)
    · rintro rfl
      rw [hk] at hy
      exact absurd hy (by decide)
  have h6 : Nat.gcd 6 6 = 6 := by decide
  -- the three `6`-residues are pairwise distinct mod `6`
  have h01 : ¬ (6 : ℤ) ∣ r i₁ - r i₂ := hd _ _ 6 (by rw [ha₁, ha₂, h6]) h₁₂
  have h02 : ¬ (6 : ℤ) ∣ r i₁ - r i₃ := hd _ _ 6 (by rw [ha₁, ha₃, h6]) h₁₃
  have h12 : ¬ (6 : ℤ) ∣ r i₂ - r i₃ := hd _ _ 6 (by rw [ha₂, ha₃, h6]) h₂₃
  -- each differs in parity from the `x`-residue
  have h03 : ¬ (2 : ℤ) ∣ r i₁ - r x := hd _ _ 2 (by rw [ha₁, hx]) (hne i₁ ha₁).1
  have h13 : ¬ (2 : ℤ) ∣ r i₂ - r x := hd _ _ 2 (by rw [ha₂, hx]) (hne i₂ ha₂).1
  have h23 : ¬ (2 : ℤ) ∣ r i₃ - r x := hd _ _ 2 (by rw [ha₃, hx]) (hne i₃ ha₃).1
  -- each differs mod `3` from the `y`-residue
  have h04 : ¬ (3 : ℤ) ∣ r i₁ - r y := hd _ _ 3 (by rw [ha₁, hy]) (hne i₁ ha₁).2
  have h14 : ¬ (3 : ℤ) ∣ r i₂ - r y := hd _ _ 3 (by rw [ha₂, hy]) (hne i₂ ha₂).2
  have h24 : ¬ (3 : ℤ) ∣ r i₃ - r y := hd _ _ 3 (by rw [ha₃, hy]) (hne i₃ ha₃).2
  -- the `x`-entry forces a common parity on the three `6`-residues
  have p01 : (2 : ℤ) ∣ r i₁ - r i₂ := by omega
  have p02 : (2 : ℤ) ∣ r i₁ - r i₃ := by omega
  have p12 : (2 : ℤ) ∣ r i₂ - r i₃ := by omega
  -- same parity and distinct mod `6` means distinct mod `3`
  have t01 : ¬ (3 : ℤ) ∣ r i₁ - r i₂ := by omega
  have t02 : ¬ (3 : ℤ) ∣ r i₁ - r i₃ := by omega
  have t12 : ¬ (3 : ℤ) ∣ r i₂ - r i₃ := by omega
  -- four pairwise distinct classes mod `3` are impossible
  clear hr hd hne h01 h02 h12 h03 h13 h23 p01 p02 p12
  omega

/-- **Theorem 3.1, `ℤ` side** (arXiv:2608.15873): `(6,6,6,10,15)` is not
`ℤ`-harmonic, by Lemma 2.1(i) since `gcd(6,10) = 2` and `gcd(6,15) = 3`. -/
theorem not_zHarmonic : ¬ ZHarmonic ![6, 6, 6, 10, 15] :=
  not_zHarmonic_of_three_six _ 0 1 2 3 4 (by decide) (by decide) (by decide) rfl rfl rfl
    (by decide) (by decide)

/-! ## The `A₅` side: explicit subgroups and cosets -/

/-- A permutation of `Fin 5` given by its value table `f` and the table `g` of
its inverse. -/
def mk5 (f g : Fin 5 → Fin 5) (h : ∀ x, g (f x) = x ∧ f (g x) = x) : Perm (Fin 5) :=
  ⟨f, g, fun x => (h x).1, fun x => (h x).2⟩

/-- `mk5` evaluates as its value table. -/
example : mk5 ![1, 2, 0, 3, 4] ![2, 0, 1, 3, 4] (by decide) 0 = 1 := rfl

/-- The subgroup of `Perm (Fin 5)` with a given finite carrier `S`, once `S` is
checked to contain `1` and to be closed under products and inverses. -/
def ofFinset (S : Finset (Perm (Fin 5))) (one_mem : 1 ∈ S)
    (mul_mem : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (inv_mem : ∀ a ∈ S, a⁻¹ ∈ S) :
    Subgroup (Perm (Fin 5)) where
  carrier := ↑S
  one_mem' := one_mem
  mul_mem' := fun {a b} ha hb => mul_mem a ha b hb
  inv_mem' := fun {a} ha => inv_mem a ha

/-- The carrier of the dihedral subgroup `D = ⟨(1 2 5 3 4), (1 2)(4 5)⟩ ≅ D₁₀` (order 10), listed
element by element (points `1,…,5` of the paper are `0,…,4` here). -/
def dSet : Finset (Perm (Fin 5)) :=
  {mk5 ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide),
   mk5 ![0, 3, 4, 1, 2] ![0, 3, 4, 1, 2] (by decide),
   mk5 ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide),
   mk5 ![1, 4, 3, 0, 2] ![3, 0, 4, 2, 1] (by decide),
   mk5 ![2, 3, 1, 4, 0] ![4, 2, 0, 1, 3] (by decide),
   mk5 ![2, 4, 0, 3, 1] ![2, 4, 0, 3, 1] (by decide),
   mk5 ![3, 0, 4, 2, 1] ![1, 4, 3, 0, 2] (by decide),
   mk5 ![3, 2, 1, 0, 4] ![3, 2, 1, 0, 4] (by decide),
   mk5 ![4, 1, 3, 2, 0] ![4, 1, 3, 2, 0] (by decide),
   mk5 ![4, 2, 0, 1, 3] ![2, 3, 1, 4, 0] (by decide)}

/-- The carrier of the subgroup `T = ⟨(2 3 5), (1 4)(2 3)⟩ ≅ S₃` (order 6), listed
element by element (points `1,…,5` of the paper are `0,…,4` here). -/
def tSet : Finset (Perm (Fin 5)) :=
  {mk5 ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide),
   mk5 ![0, 2, 4, 3, 1] ![0, 4, 1, 3, 2] (by decide),
   mk5 ![0, 4, 1, 3, 2] ![0, 2, 4, 3, 1] (by decide),
   mk5 ![3, 1, 4, 0, 2] ![3, 1, 4, 0, 2] (by decide),
   mk5 ![3, 2, 1, 0, 4] ![3, 2, 1, 0, 4] (by decide),
   mk5 ![3, 4, 2, 0, 1] ![3, 4, 2, 0, 1] (by decide)}

/-- The carrier of the Klein four-group `V = ⟨(1 2)(3 4), (1 3)(2 4)⟩` (order 4), listed
element by element (points `1,…,5` of the paper are `0,…,4` here). -/
def vSet : Finset (Perm (Fin 5)) :=
  {mk5 ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide),
   mk5 ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide),
   mk5 ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide),
   mk5 ![3, 2, 1, 0, 4] ![3, 2, 1, 0, 4] (by decide)}

/-- The carrier of `D` contains `1`. -/
theorem dSet_one_mem : 1 ∈ dSet := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `D` is closed under products (finite check). -/
theorem dSet_mul_mem : ∀ a ∈ dSet, ∀ b ∈ dSet, a * b ∈ dSet := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `D` is closed under inverses (finite check). -/
theorem dSet_inv_mem : ∀ a ∈ dSet, a⁻¹ ∈ dSet := by decide

set_option maxRecDepth 20000 in
/-- Every element of the carrier of `D` is an even permutation (finite check). -/
theorem dSet_sign : ∀ a ∈ dSet, Perm.sign a = 1 := by decide

/-- The carrier of `D` has `10` elements. -/
theorem dSet_card : dSet.card = 10 := by decide

/-- `D` as a subgroup of `Perm (Fin 5)`. -/
def dSub : Subgroup (Perm (Fin 5)) :=
  ofFinset dSet dSet_one_mem dSet_mul_mem dSet_inv_mem

/-- The carrier of `T` contains `1`. -/
theorem tSet_one_mem : 1 ∈ tSet := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `T` is closed under products (finite check). -/
theorem tSet_mul_mem : ∀ a ∈ tSet, ∀ b ∈ tSet, a * b ∈ tSet := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `T` is closed under inverses (finite check). -/
theorem tSet_inv_mem : ∀ a ∈ tSet, a⁻¹ ∈ tSet := by decide

set_option maxRecDepth 20000 in
/-- Every element of the carrier of `T` is an even permutation (finite check). -/
theorem tSet_sign : ∀ a ∈ tSet, Perm.sign a = 1 := by decide

/-- The carrier of `T` has `6` elements. -/
theorem tSet_card : tSet.card = 6 := by decide

/-- `T` as a subgroup of `Perm (Fin 5)`. -/
def tSub : Subgroup (Perm (Fin 5)) :=
  ofFinset tSet tSet_one_mem tSet_mul_mem tSet_inv_mem

/-- The carrier of `V` contains `1`. -/
theorem vSet_one_mem : 1 ∈ vSet := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `V` is closed under products (finite check). -/
theorem vSet_mul_mem : ∀ a ∈ vSet, ∀ b ∈ vSet, a * b ∈ vSet := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `V` is closed under inverses (finite check). -/
theorem vSet_inv_mem : ∀ a ∈ vSet, a⁻¹ ∈ vSet := by decide

set_option maxRecDepth 20000 in
/-- Every element of the carrier of `V` is an even permutation (finite check). -/
theorem vSet_sign : ∀ a ∈ vSet, Perm.sign a = 1 := by decide

/-- The carrier of `V` has `4` elements. -/
theorem vSet_card : vSet.card = 4 := by decide

/-- `V` as a subgroup of `Perm (Fin 5)`. -/
def vSub : Subgroup (Perm (Fin 5)) :=
  ofFinset vSet vSet_one_mem vSet_mul_mem vSet_inv_mem

/-! ### Ground truth: the paper's generators lie in the listed carriers -/

example : c[(0 : Fin 5), 1, 4, 2, 3] ∈ dSet ∧ swap (0 : Fin 5) 1 * swap 3 4 ∈ dSet := by decide
example : c[(1 : Fin 5), 2, 4] ∈ tSet ∧ swap (0 : Fin 5) 3 * swap 1 2 ∈ tSet := by decide
example : swap (0 : Fin 5) 1 * swap 2 3 ∈ vSet ∧ swap (0 : Fin 5) 2 * swap 1 3 ∈ vSet := by decide

/-- The paper's coset representative `g1 = (1 5 3)`. -/
def g1Perm : Perm (Fin 5) := mk5 ![4, 1, 0, 3, 2] ![2, 1, 4, 3, 0] (by decide)

/-- The paper's coset representative `g2 = (1 4 2 3 5)`. -/
def g2Perm : Perm (Fin 5) := mk5 ![3, 2, 4, 1, 0] ![4, 3, 1, 0, 2] (by decide)

/-- The paper's coset representative `g3 = (1 5 2 3 4)`. -/
def g3Perm : Perm (Fin 5) := mk5 ![4, 2, 3, 0, 1] ![3, 4, 1, 2, 0] (by decide)

/-- The paper's coset representative `g4 = (1 2 4)`. -/
def g4Perm : Perm (Fin 5) := mk5 ![1, 3, 2, 0, 4] ![3, 0, 2, 1, 4] (by decide)

/-- The paper's coset representative `g5 = (3 4 5)`. -/
def g5Perm : Perm (Fin 5) := mk5 ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide)

/-- Ground truth: the representatives match the paper's cycle notation. -/
example : g1Perm = c[(0 : Fin 5), 4, 2] ∧ g2Perm = c[(0 : Fin 5), 3, 1, 2, 4] ∧
    g3Perm = c[(0 : Fin 5), 4, 1, 2, 3] ∧ g4Perm = c[(0 : Fin 5), 1, 3] ∧
    g5Perm = c[(2 : Fin 5), 3, 4] := by decide

/-! ### Indices inside `A₅` -/

/-- `Perm (Fin 5)` has `5! = 120` elements. -/
theorem natCard_perm_fin_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

/-- If every element of the finite carrier `S` is even, the subgroup `ofFinset S`
viewed inside `A₅` has index `60 / |S|`, stated division-free as
`[A₅ : S] * |S| = 60`. -/
theorem index_subgroupOf_mul_card (S : Finset (Perm (Fin 5))) (one_mem : 1 ∈ S)
    (mul_mem : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (inv_mem : ∀ a ∈ S, a⁻¹ ∈ S)
    (sign_eq : ∀ x ∈ S, Perm.sign x = 1) :
    ((ofFinset S one_mem mul_mem inv_mem).subgroupOf (alternatingGroup (Fin 5))).index *
      S.card = 60 := by
  set H := ofFinset S one_mem mul_mem inv_mem with hH
  have hle : H ≤ alternatingGroup (Fin 5) := fun x hx => Perm.mem_alternatingGroup.2 (sign_eq x hx)
  have hrel : H.relIndex (alternatingGroup (Fin 5)) * 2 = H.index := by
    rw [← alternatingGroup.index_eq_two (α := Fin 5)]
    exact Subgroup.relIndex_mul_index hle
  have hcardH : Nat.card H = S.card := Nat.card_eq_finsetCard S
  have hidx : H.index * S.card = 120 := by
    rw [← hcardH, ← natCard_perm_fin_five]
    exact H.index_mul_card
  change H.relIndex (alternatingGroup (Fin 5)) * S.card = 60
  rw [← hrel] at hidx
  have h2 : H.relIndex (alternatingGroup (Fin 5)) * S.card * 2 = 120 := by
    rw [mul_right_comm]
    exact hidx
  omega

/-- `D` viewed as a subgroup of `A₅`. -/
def dA : Subgroup (alternatingGroup (Fin 5)) := dSub.subgroupOf (alternatingGroup (Fin 5))

/-- `T` viewed as a subgroup of `A₅`. -/
def tA : Subgroup (alternatingGroup (Fin 5)) := tSub.subgroupOf (alternatingGroup (Fin 5))

/-- `V` viewed as a subgroup of `A₅`. -/
def vA : Subgroup (alternatingGroup (Fin 5)) := vSub.subgroupOf (alternatingGroup (Fin 5))

/-- `[A₅ : D] = 6`. -/
theorem index_dA : dA.index = 6 := by
  have h : dA.index * 10 = 60 := by
    rw [← dSet_card]
    exact index_subgroupOf_mul_card dSet dSet_one_mem dSet_mul_mem dSet_inv_mem dSet_sign
  omega

/-- `[A₅ : T] = 10`. -/
theorem index_tA : tA.index = 10 := by
  have h : tA.index * 6 = 60 := by
    rw [← tSet_card]
    exact index_subgroupOf_mul_card tSet tSet_one_mem tSet_mul_mem tSet_inv_mem tSet_sign
  omega

/-- `[A₅ : V] = 15`. -/
theorem index_vA : vA.index = 15 := by
  have h : vA.index * 4 = 60 := by
    rw [← vSet_card]
    exact index_subgroupOf_mul_card vSet vSet_one_mem vSet_mul_mem vSet_inv_mem vSet_sign
  omega

/-! ### Disjointness of the cosets -/

/-- Two left cosets `g₁ (H₁ ∩ K)` and `g₂ (H₂ ∩ K)` inside `K` are disjoint as
soon as `g₁ u ≠ g₂ v` for all `u ∈ H₁`, `v ∈ H₂` in the ambient group. -/
theorem disjoint_smul_subgroupOf {G : Type*} [Group G] {K H₁ H₂ : Subgroup G} (g₁ g₂ : K)
    (h : ∀ u ∈ H₁, ∀ v ∈ H₂, (g₁ : G) * u ≠ g₂ * v) :
    Disjoint (g₁ • (H₁.subgroupOf K : Set K)) (g₂ • (H₂.subgroupOf K : Set K)) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hx⟩
  exact h u (Subgroup.mem_subgroupOf.1 hu) v (Subgroup.mem_subgroupOf.1 hv)
    (congrArg Subtype.val hx.symm)

/-- The paper's representatives `g₁, …, g₅` as elements of `A₅`. -/
def reps : Fin 5 → alternatingGroup (Fin 5) :=
  ![⟨g1Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g2Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g3Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g4Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g5Perm, Perm.mem_alternatingGroup.2 (by decide)⟩]

/-- The ambient subgroups `D, D, D, T, V` of `Perm (Fin 5)` attached to the five cosets. -/
def subs : Fin 5 → Subgroup (Perm (Fin 5)) := ![dSub, dSub, dSub, tSub, vSub]

set_option maxRecDepth 20000 in
/-- Finite check: for `i ≠ j`, no element of `gᵢ Uᵢ` equals an element of `gⱼ Uⱼ`,
computed in `Perm (Fin 5)` over the listed carriers. -/
theorem reps_mul_ne : ∀ i j : Fin 5, i ≠ j →
    ∀ u ∈ (![dSet, dSet, dSet, tSet, vSet] : Fin 5 → Finset (Perm (Fin 5))) i,
    ∀ v ∈ (![dSet, dSet, dSet, tSet, vSet] : Fin 5 → Finset (Perm (Fin 5))) j,
      ((reps i : Perm (Fin 5))) * u ≠ (reps j : Perm (Fin 5)) * v := by
  decide

/-- **Theorem 3.1, `A₅` side** (arXiv:2608.15873): `(6,6,6,10,15)` is
`A₅`-harmonic, realised by the pairwise disjoint left cosets
`g₁D, g₂D, g₃D, g₄T, g₅V` with `[A₅:D] = 6`, `[A₅:T] = 10`, `[A₅:V] = 15`. -/
theorem gHarmonic_alternatingGroup : GHarmonic (alternatingGroup (Fin 5)) ![6, 6, 6, 10, 15] := by
  refine ⟨fun i => (subs i).subgroupOf (alternatingGroup (Fin 5)), reps, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact index_dA
    · exact index_dA
    · exact index_dA
    · exact index_tA
    · exact index_vA
  · intro i j hij
    refine disjoint_smul_subgroupOf (reps i) (reps j) ?_
    intro u hu v hv
    have hsub : ∀ k : Fin 5, ∀ w ∈ subs k,
        w ∈ (![dSet, dSet, dSet, tSet, vSet] : Fin 5 → Finset (Perm (Fin 5))) k := by
      intro k w hw
      fin_cases k <;> exact hw
    exact reps_mul_ne i j hij u (hsub i u hu) v (hsub j v hv)

/-- **Negative answer to Ginosar's Question 1** (arXiv:2608.15873, Theorem 3.1):
there is a finite group `G` and a tuple of positive integers that is `G`-harmonic
but not `ℤ`-harmonic, namely `G = A₅` and `(6,6,6,10,15)`. -/
theorem exists_gHarmonic_not_zHarmonic :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (a : Fin 5 → ℕ),
      (∀ i, 0 < a i) ∧ GHarmonic G a ∧ ¬ ZHarmonic a :=
  ⟨alternatingGroup (Fin 5), inferInstance, inferInstance, ![6, 6, 6, 10, 15],
    by decide, gHarmonic_alternatingGroup, not_zHarmonic⟩


/-! ## Corollary 3.2: extension to a coset partition of `A₅` -/

/-- The carrier of `T₂ = ⟨(1 3 4), (1 3)(2 5)⟩ ≅ S₃` (order 6), listed element by element. -/
def t2Set : Finset (Perm (Fin 5)) :=
  {mk5 ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide),
   mk5 ![0, 4, 3, 2, 1] ![0, 4, 3, 2, 1] (by decide),
   mk5 ![2, 1, 3, 0, 4] ![3, 1, 0, 2, 4] (by decide),
   mk5 ![2, 4, 0, 3, 1] ![2, 4, 0, 3, 1] (by decide),
   mk5 ![3, 1, 0, 2, 4] ![2, 1, 3, 0, 4] (by decide),
   mk5 ![3, 4, 2, 0, 1] ![3, 4, 2, 0, 1] (by decide)}

/-- The carrier of `T₂` contains `1`. -/
theorem t2Set_one_mem : 1 ∈ t2Set := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `T₂` is closed under products (finite check). -/
theorem t2Set_mul_mem : ∀ a ∈ t2Set, ∀ b ∈ t2Set, a * b ∈ t2Set := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `T₂` is closed under inverses (finite check). -/
theorem t2Set_inv_mem : ∀ a ∈ t2Set, a⁻¹ ∈ t2Set := by decide

set_option maxRecDepth 20000 in
/-- Every element of the carrier of `T₂` is an even permutation (finite check). -/
theorem t2Set_sign : ∀ a ∈ t2Set, Perm.sign a = 1 := by decide

/-- The carrier of `T₂` has `6` elements. -/
theorem t2Set_card : t2Set.card = 6 := by decide

/-- `T₂` as a subgroup of `Perm (Fin 5)`. -/
def t2Sub : Subgroup (Perm (Fin 5)) :=
  ofFinset t2Set t2Set_one_mem t2Set_mul_mem t2Set_inv_mem

/-- `T₂` viewed as a subgroup of `A₅`. -/
def t2A : Subgroup (alternatingGroup (Fin 5)) := t2Sub.subgroupOf (alternatingGroup (Fin 5))

/-- `[A₅ : T₂] = 10`. -/
theorem index_t2A : t2A.index = 10 := by
  have h : t2A.index * 6 = 60 := by
    rw [← t2Set_card]
    exact index_subgroupOf_mul_card t2Set t2Set_one_mem t2Set_mul_mem t2Set_inv_mem t2Set_sign
  omega

/-- The carrier of `T₃ = ⟨(1 2 4), (1 2)(3 5)⟩ ≅ S₃` (order 6), listed element by element. -/
def t3Set : Finset (Perm (Fin 5)) :=
  {mk5 ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide),
   mk5 ![0, 3, 4, 1, 2] ![0, 3, 4, 1, 2] (by decide),
   mk5 ![1, 0, 4, 3, 2] ![1, 0, 4, 3, 2] (by decide),
   mk5 ![1, 3, 2, 0, 4] ![3, 0, 2, 1, 4] (by decide),
   mk5 ![3, 0, 2, 1, 4] ![1, 3, 2, 0, 4] (by decide),
   mk5 ![3, 1, 4, 0, 2] ![3, 1, 4, 0, 2] (by decide)}

/-- The carrier of `T₃` contains `1`. -/
theorem t3Set_one_mem : 1 ∈ t3Set := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `T₃` is closed under products (finite check). -/
theorem t3Set_mul_mem : ∀ a ∈ t3Set, ∀ b ∈ t3Set, a * b ∈ t3Set := by decide

set_option maxRecDepth 20000 in
/-- The carrier of `T₃` is closed under inverses (finite check). -/
theorem t3Set_inv_mem : ∀ a ∈ t3Set, a⁻¹ ∈ t3Set := by decide

set_option maxRecDepth 20000 in
/-- Every element of the carrier of `T₃` is an even permutation (finite check). -/
theorem t3Set_sign : ∀ a ∈ t3Set, Perm.sign a = 1 := by decide

/-- The carrier of `T₃` has `6` elements. -/
theorem t3Set_card : t3Set.card = 6 := by decide

/-- `T₃` as a subgroup of `Perm (Fin 5)`. -/
def t3Sub : Subgroup (Perm (Fin 5)) :=
  ofFinset t3Set t3Set_one_mem t3Set_mul_mem t3Set_inv_mem

/-- `T₃` viewed as a subgroup of `A₅`. -/
def t3A : Subgroup (alternatingGroup (Fin 5)) := t3Sub.subgroupOf (alternatingGroup (Fin 5))

/-- `[A₅ : T₃] = 10`. -/
theorem index_t3A : t3A.index = 10 := by
  have h : t3A.index * 6 = 60 := by
    rw [← t3Set_card]
    exact index_subgroupOf_mul_card t3Set t3Set_one_mem t3Set_mul_mem t3Set_inv_mem t3Set_sign
  omega

/-- The paper's additional coset representative `(1 2)(3 4)` (Corollary 3.2). -/
def g6Perm : Perm (Fin 5) := mk5 ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide)

/-- The paper's additional coset representative `(1 2)(4 5)` (Corollary 3.2). -/
def g7Perm : Perm (Fin 5) := mk5 ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide)

/-- The paper's additional coset representative `(1 4 5)` (Corollary 3.2). -/
def g8Perm : Perm (Fin 5) := mk5 ![3, 1, 2, 4, 0] ![4, 1, 2, 0, 3] (by decide)

/-- The paper's additional coset representative `(1 4 3 2 5)` (Corollary 3.2). -/
def g9Perm : Perm (Fin 5) := mk5 ![3, 4, 1, 2, 0] ![4, 2, 3, 0, 1] (by decide)

/-- Ground truth: the subgroup generators and representatives match the paper's
cycle notation. -/
example : c[(0 : Fin 5), 2, 3] ∈ t2Set ∧ swap (0 : Fin 5) 2 * swap 1 4 ∈ t2Set ∧
    c[(0 : Fin 5), 1, 3] ∈ t3Set ∧ swap (0 : Fin 5) 1 * swap 2 4 ∈ t3Set ∧
    g6Perm = swap 0 1 * swap 2 3 ∧ g7Perm = swap 0 1 * swap 3 4 ∧
    g8Perm = c[(0 : Fin 5), 3, 4] ∧ g9Perm = c[(0 : Fin 5), 3, 2, 1, 4] := by decide

/-- The nine representatives of Corollary 3.2 as elements of `A₅`, in the paper's
order `g₁, …, g₅, (1 2)(3 4), (1 2)(4 5), (1 4 5), (1 4 3 2 5)`. -/
def reps9 : Fin 9 → alternatingGroup (Fin 5) :=
  ![⟨g1Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g2Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g3Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g4Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g5Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g6Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g7Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g8Perm, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨g9Perm, Perm.mem_alternatingGroup.2 (by decide)⟩]

/-- The carriers `D, D, D, T, V, V, V, T₂, T₃` of the nine cosets. -/
def sets9 : Fin 9 → Finset (Perm (Fin 5)) :=
  ![dSet, dSet, dSet, tSet, vSet, vSet, vSet, t2Set, t3Set]

/-- The subgroups `D, D, D, T, V, V, V, T₂, T₃` of `Perm (Fin 5)`. -/
def subs9 : Fin 9 → Subgroup (Perm (Fin 5)) :=
  ![dSub, dSub, dSub, tSub, vSub, vSub, vSub, t2Sub, t3Sub]

/-- The nine subgroups of `A₅` of Corollary 3.2. -/
def cosetSubgroups9 (i : Fin 9) : Subgroup (alternatingGroup (Fin 5)) :=
  (subs9 i).subgroupOf (alternatingGroup (Fin 5))

/-- Membership in `subs9 i` is membership in the listed carrier `sets9 i`. -/
theorem mem_sets9_of_mem_subs9 (i : Fin 9) (w : Perm (Fin 5)) (hw : w ∈ subs9 i) :
    w ∈ sets9 i := by
  fin_cases i <;> exact hw

set_option maxRecDepth 40000 in
/-- Finite check: for `i ≠ j`, the cosets `gᵢ Uᵢ` and `gⱼ Uⱼ` of Corollary 3.2 share
no element, computed in `Perm (Fin 5)` over the listed carriers. -/
theorem reps9_mul_ne : ∀ i j : Fin 9, i ≠ j → ∀ u ∈ sets9 i, ∀ v ∈ sets9 j,
    ((reps9 i : Perm (Fin 5))) * u ≠ (reps9 j : Perm (Fin 5)) * v := by
  decide

set_option maxRecDepth 40000 in
/-- Finite check: every even permutation of `Fin 5` lies in one of the nine cosets
of Corollary 3.2. -/
theorem reps9_cover : ∀ x : Perm (Fin 5), Perm.sign x = 1 →
    ∃ i : Fin 9, ∃ u ∈ sets9 i, x = (reps9 i : Perm (Fin 5)) * u := by
  decide

/-- An element `x = g u` of `K` with `u ∈ H` lies in the left coset `g (H ∩ K)`
inside `K`. -/
theorem mem_smul_subgroupOf {G : Type*} [Group G] {K H : Subgroup G} (g x : K) (u : G)
    (hu : u ∈ H) (hx : (x : G) = g * u) : x ∈ g • (H.subgroupOf K : Set K) := by
  refine ⟨g⁻¹ * x, ?_, by simp⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  have hval : ((g⁻¹ * x : K) : G) = u := by simp [hx]
  rw [hval]
  exact hu

/-- **Corollary 3.2** (arXiv:2608.15873): the nine cosets
`g₁D, g₂D, g₃D, g₄T, g₅V, (1 2)(3 4)V, (1 2)(4 5)V, (1 4 5)T₂, (1 4 3 2 5)T₃`
have indices `6,6,6,10,15,15,15,10,10`, are pairwise disjoint, and cover `A₅`:
they form a coset partition of `A₅` extending the five cosets of Theorem 3.1. -/
theorem cosetPartition_alternatingGroup :
    (∀ i, (cosetSubgroups9 i).index = (![6, 6, 6, 10, 15, 15, 15, 10, 10] : Fin 9 → ℕ) i) ∧
    (Pairwise fun i j => Disjoint (reps9 i • (cosetSubgroups9 i : Set (alternatingGroup (Fin 5))))
      (reps9 j • (cosetSubgroups9 j : Set (alternatingGroup (Fin 5))))) ∧
    ∀ x : alternatingGroup (Fin 5), ∃ i, x ∈ reps9 i • (cosetSubgroups9 i : Set _) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact index_dA
    · exact index_dA
    · exact index_dA
    · exact index_tA
    · exact index_vA
    · exact index_vA
    · exact index_vA
    · exact index_t2A
    · exact index_t3A
  · intro i j hij
    refine disjoint_smul_subgroupOf (reps9 i) (reps9 j) ?_
    intro u hu v hv
    exact reps9_mul_ne i j hij u (mem_sets9_of_mem_subs9 i u hu) v
      (mem_sets9_of_mem_subs9 j v hv)
  · intro x
    obtain ⟨i, u, hu, hx⟩ := reps9_cover x (Perm.mem_alternatingGroup.1 x.2)
    have hsub : u ∈ subs9 i := by
      fin_cases i <;> exact hu
    exact ⟨i, mem_smul_subgroupOf (reps9 i) x u hsub hx⟩

/-- **Corollary 3.2, consequence** (arXiv:2608.15873): the index tuple
`(6,6,6,10,15,15,15,10,10)` of the coset partition is `A₅`-harmonic. -/
theorem gHarmonic_nine :
    GHarmonic (alternatingGroup (Fin 5)) ![6, 6, 6, 10, 15, 15, 15, 10, 10] :=
  ⟨cosetSubgroups9, reps9, cosetPartition_alternatingGroup.1,
    cosetPartition_alternatingGroup.2.1⟩

/-- **Corollary 3.2, consequence** (arXiv:2608.15873): the index tuple
`(6,6,6,10,15,15,15,10,10)` of the coset partition is not `ℤ`-harmonic, by
Lemma 2.1(i). -/
theorem not_zHarmonic_nine : ¬ ZHarmonic ![6, 6, 6, 10, 15, 15, 15, 10, 10] :=
  not_zHarmonic_of_three_six _ 0 1 2 3 4 (by decide) (by decide) (by decide) rfl rfl rfl
    (by decide) (by decide)

end HarmonicTupleA5
