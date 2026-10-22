/-
# Cameron–Dey, Question 31: the abelian hypothesis is necessary

Peter J. Cameron and Hiranya Kishore Dey, *On the order sequence of a group*,
arXiv:2310.06516; Electron. J. Combin. 32(2) (2025) #P2.9, Question 31.

For groups of equal finite order, ordinary domination compares their sorted
element-order sequences entrywise. By Proposition 3 (`p:bijection`), this is
equivalent to a bijection `f : G → H` with `o(f g) ≤ o(g)`. Strong domination
requires `o(f g) ∣ o(g)`. Theorem 8 (`t:extension`) says that `G × H` strongly
dominates every extension of an abelian `G` by `H` when their orders are
coprime. Question 31 asks whether abelianness is necessary.

This module gives a counterexample without abelianness, even for ordinary
domination. Let `V = (ZMod 5)²`; the matrices `r = [[0,-1],[1,-1]]` and
`s = [[0,1],[1,0]]` generate `S₃ ≅ DihedralGroup 3` in `GL(2,5)`.
Then `K = V ⋊ S₃` has order 150, and `N = V ⋊ ⟨r⟩` is nonabelian and normal
of order 75 and index 2. The group `K` has 60 elements of order at least 10,
whereas `N × (K ⧸ N)` has at most 24, excluding a dominating bijection.
-/
import Mathlib

set_option autoImplicit false

namespace CameronDeyQuestion31

open DihedralGroup

/-! ## Domination of order sequences -/

/-- `OrderDominates G H`: there is a bijection `f : G ≃ H` with
`orderOf (f g) ≤ orderOf g` for every `g`.  By Cameron–Dey Proposition
`p:bijection` (EJC Prop. 3) this is equivalent to `os(G)` dominating `os(H)`
(sorted element-order sequences compared entrywise). -/
def OrderDominates (G H : Type*) [Monoid G] [Monoid H] : Prop :=
  ∃ f : G ≃ H, ∀ g, orderOf (f g) ≤ orderOf g

/-- `StronglyDominates G H`: there is a bijection `f : G ≃ H` with
`orderOf (f g) ∣ orderOf g` for every `g` (Cameron–Dey, strong domination). -/
def StronglyDominates (G H : Type*) [Monoid G] [Monoid H] : Prop :=
  ∃ f : G ≃ H, ∀ g, orderOf (f g) ∣ orderOf g

/-- Every group order-dominates itself (non-vacuity of `OrderDominates`). -/
theorem orderDominates_refl (G : Type*) [Monoid G] : OrderDominates G G :=
  ⟨Equiv.refl G, fun _ => le_rfl⟩

/-- Every group strongly dominates itself (non-vacuity of `StronglyDominates`). -/
theorem stronglyDominates_refl (G : Type*) [Monoid G] : StronglyDominates G G :=
  ⟨Equiv.refl G, fun _ => dvd_rfl⟩

/-- In finite groups, strong domination implies domination: a divisor of a
positive element order is at most that order. -/
theorem OrderDominates.of_stronglyDominates {G H : Type*} [Group G] [Group H] [Finite G]
    (h : StronglyDominates G H) : OrderDominates G H := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun g => Nat.le_of_dvd (orderOf_pos g) (hf g)⟩

/-- Counting consequence of domination: if `os(G)` dominates `os(H)` then, for
every threshold `d`, `H` has at most as many elements of order `≥ d` as `G`. -/
theorem OrderDominates.card_le {G H : Type*} [Monoid G] [Monoid H] [Finite G]
    (h : OrderDominates G H) (d : ℕ) :
    Nat.card {x : H // d ≤ orderOf x} ≤ Nat.card {x : G // d ≤ orderOf x} := by
  obtain ⟨f, hf⟩ := h
  refine Nat.card_le_card_of_injective
    (fun y => ⟨f.symm y.1, le_trans y.2 (by simpa using hf (f.symm y.1))⟩) ?_
  intro y z hyz
  exact Subtype.ext (f.symm.injective (congrArg Subtype.val hyz))

/-! ## The witness group `K = (ZMod 5)² ⋊ S₃` -/

/-- The module `V = (ZMod 5)²`, written multiplicatively. -/
abbrev V := Multiplicative (ZMod 5 × ZMod 5)

/-- Matrix entries `(a, b, c, d)` of `[[a, b], [c, d]]` representing an element
of `DihedralGroup 3 ≅ S₃` in `GL(2,5)`: `r i ↦ R^i` and `sr i ↦ S R^i`, with
`R = [[0,-1],[1,-1]]` and `S = [[0,1],[1,0]]`. -/
def coeffs : DihedralGroup 3 → ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5
  | r i => if i = 0 then (1, 0, 0, 1) else if i = 1 then (0, -1, 1, -1) else (-1, 1, -1, 0)
  | sr i => if i = 0 then (0, 1, 1, 0) else if i = 1 then (1, -1, 0, -1) else (-1, 0, -1, 1)

/-- The rotation `r 1` acts by `R = [[0,-1],[1,-1]]` and the reflection `sr 0`
by `S = [[0,1],[1,0]]`. -/
example : coeffs (r 1) = (0, -1, 1, -1) ∧ coeffs (sr 0) = (0, 1, 1, 0) := by decide

/-- The linear action of `DihedralGroup 3` on `V` through `coeffs`. -/
def act (g : DihedralGroup 3) (v : V) : V :=
  Multiplicative.ofAdd
    ((coeffs g).1 * v.toAdd.1 + (coeffs g).2.1 * v.toAdd.2,
     (coeffs g).2.2.1 * v.toAdd.1 + (coeffs g).2.2.2 * v.toAdd.2)

/-- `R (1, 0) = (0, 1)`. -/
example : act (r 1) (Multiplicative.ofAdd (1, 0)) = Multiplicative.ofAdd (0, 1) := by decide

/-- `act` is a left action. -/
theorem act_mul (g h : DihedralGroup 3) (v : V) : act (g * h) v = act g (act h v) := by
  revert g h v
  decide

/-- The identity acts trivially. -/
theorem act_one (v : V) : act 1 v = v := by
  revert v
  decide

/-- Each `act g` is additive (a group endomorphism of `V`). -/
theorem act_map_mul (g : DihedralGroup 3) (v w : V) : act g (v * w) = act g v * act g w := by
  simp only [act]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  ext <;> ring

/-- `act g` packaged as an automorphism of `V`. -/
def actAut (g : DihedralGroup 3) : MulAut V where
  toFun := act g
  invFun := act g⁻¹
  left_inv v := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv v := by rw [← act_mul, mul_inv_cancel, act_one]
  map_mul' := act_map_mul g

/-- The representation `S₃ → Aut(V)` defining the semidirect product. -/
def rep : DihedralGroup 3 →* MulAut V where
  toFun := actAut
  map_one' := MulEquiv.ext act_one
  map_mul' g h := MulEquiv.ext (act_mul g h)

/-- The witness group `K = (ZMod 5)² ⋊ S₃` of order 150. -/
abbrev K := V ⋊[rep] DihedralGroup 3

/-- `K` is finite, via the underlying bijection with `V × S₃`. -/
instance : Fintype K := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

/-- `g` is a rotation of the triangle, i.e. lies in `⟨r 1⟩ ≅ C₃`. -/
def IsRot : DihedralGroup 3 → Prop
  | r _ => True
  | sr _ => False

instance : DecidablePred IsRot := fun g => match g with
  | r _ => isTrue trivial
  | sr _ => isFalse id

/-- Rotations are closed under multiplication. -/
theorem isRot_mul : ∀ g h : DihedralGroup 3, IsRot g → IsRot h → IsRot (g * h) := by
  decide

/-- Rotations are closed under inversion. -/
theorem isRot_inv : ∀ g : DihedralGroup 3, IsRot g → IsRot g⁻¹ := by
  decide

/-- The normal Hall subgroup `N = V ⋊ ⟨r⟩` of `K` (order 75). -/
def N : Subgroup K where
  carrier := {k | IsRot k.right}
  mul_mem' {a b} ha hb := isRot_mul a.right b.right ha hb
  one_mem' := trivial
  inv_mem' {a} ha := isRot_inv a.right ha

instance : DecidablePred (· ∈ N) := fun k => inferInstanceAs (Decidable (IsRot k.right))

/-! ## Finite computations on the witness -/

/-- `|K| = 150`. -/
theorem card_K : Nat.card K = 150 := by
  rw [SemidirectProduct.card, DihedralGroup.nat_card, Nat.card_eq_fintype_card]
  rfl

/-- `|N| = 75`. -/
theorem card_N : Nat.card N = 75 := by
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  decide

/-- `[K : N] = 2`. -/
theorem index_N : N.index = 2 := by
  have h := N.card_mul_index
  rw [card_N, card_K] at h
  omega

/-- `N` is normal in `K`, having index 2. -/
instance N_normal : N.Normal := Subgroup.normal_of_index_eq_two index_N

/-- `N` is not abelian: the translation by `(1,0)` and the rotation `r 1` do not
commute. -/
theorem N_not_comm : ¬ ∀ a b : N, a * b = b * a := by
  intro h
  have hc : (⟨Multiplicative.ofAdd (1, 0), 1⟩ : K) * ⟨1, r 1⟩ =
      ⟨1, r 1⟩ * ⟨Multiplicative.ofAdd (1, 0), 1⟩ :=
    congrArg Subtype.val
      (h (⟨⟨Multiplicative.ofAdd (1, 0), 1⟩, trivial⟩ : N) (⟨⟨1, r 1⟩, trivial⟩ : N))
  exact absurd hc (by decide)

/-- Exactly 60 elements `k` of `K` satisfy `k⁵ ≠ 1` and `k⁶ ≠ 1`. -/
theorem card_filter_K : (Finset.univ.filter (fun k : K => k ^ 5 ≠ 1 ∧ k ^ 6 ≠ 1)).card = 60 := by
  decide

/-- Exactly 24 elements `a` of `N` satisfy `a³ ≠ 1` (the elements of order 5). -/
theorem card_filter_N : (Finset.univ.filter (fun a : N => a ^ 3 ≠ 1)).card = 24 := by
  decide

/-- Every element of `N` has order dividing 3 or 5. -/
theorem pow_three_or_pow_five_N : ∀ a : N, a ^ 3 = 1 ∨ a ^ 5 = 1 := by
  decide

/-! ## Order counts -/

/-- In `K`, an element has order `≥ 10` iff `k⁵ ≠ 1` and `k⁶ ≠ 1`
(its order divides 150). -/
theorem le_orderOf_iff_K (k : K) : 10 ≤ orderOf k ↔ k ^ 5 ≠ 1 ∧ k ^ 6 ≠ 1 := by
  constructor
  · intro hk
    refine ⟨fun h5 => ?_, fun h6 => ?_⟩
    · have := orderOf_le_of_pow_eq_one (by norm_num) h5
      omega
    · have := orderOf_le_of_pow_eq_one (by norm_num) h6
      omega
  · rintro ⟨h5, h6⟩
    have hdvd : orderOf k ∣ 150 := card_K ▸ orderOf_dvd_natCard k
    have hn5 : ¬ orderOf k ∣ 5 := fun h => h5 (orderOf_dvd_iff_pow_eq_one.mp h)
    have hn6 : ¬ orderOf k ∣ 6 := fun h => h6 (orderOf_dvd_iff_pow_eq_one.mp h)
    have hdiv : orderOf k ∈ Nat.divisors 150 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have key : ∀ d ∈ Nat.divisors 150, ¬ d ∣ 5 → ¬ d ∣ 6 → 10 ≤ d := by decide
    exact key _ hdiv hn5 hn6

/-- `K` has exactly 60 elements of order at least 10. -/
theorem card_large_K : Nat.card {k : K // 10 ≤ orderOf k} = 60 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← card_filter_K]
  congr 1
  exact Finset.filter_congr (fun k _ => le_orderOf_iff_K k)

/-- In a group with exactly two elements, any two non-identity elements are
equal. -/
theorem eq_of_ne_one_of_card_eq_two {Q : Type*} [Group Q] (hQ : Nat.card Q = 2)
    {b c : Q} (hb : b ≠ 1) (hc : c ≠ 1) : b = c := by
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hQ
  have hmem : ∀ z : Q, z = x ∨ z = y := fun z => by
    have hz : z ∈ ({x, y} : Set Q) := huniv ▸ Set.mem_univ z
    simpa using hz
  rcases hmem 1 with h1 | h1 <;> rcases hmem b with hb' | hb' <;>
    rcases hmem c with hc' | hc' <;> simp_all

/-- `N × (K ⧸ N)` has at most 24 elements of order at least 10: such an element
`(a, b)` must have `a` of order 5 and `b` the non-identity coset. -/
theorem card_large_prod_le : Nat.card {x : N × (K ⧸ N) // 10 ≤ orderOf x} ≤ 24 := by
  have hQ : Nat.card (K ⧸ N) = 2 := index_N
  -- the key structural facts about a large-order element `(a, b)`
  have hlarge : ∀ x : N × (K ⧸ N), 10 ≤ orderOf x → x.1 ^ 3 ≠ 1 ∧ x.2 ≠ 1 := by
    rintro ⟨a, b⟩ hx
    have hb2 : b ^ 2 = 1 := hQ ▸ pow_card_eq_one'
    have hb6 : b ^ 6 = 1 := by
      rw [show 6 = 2 * 3 from rfl, pow_mul, hb2, one_pow]
    have h6 : (a, b) ^ 6 ≠ 1 := fun h => by
      have := orderOf_le_of_pow_eq_one (by norm_num) h
      omega
    have h5 : (a, b) ^ 5 ≠ 1 := fun h => by
      have := orderOf_le_of_pow_eq_one (by norm_num) h
      omega
    have ha3 : a ^ 3 ≠ 1 := fun h => h6 (by
      rw [Prod.pow_mk, show 6 = 3 * 2 from rfl, pow_mul, h, one_pow, hb6, Prod.mk_one_one])
    have ha5 : a ^ 5 = 1 := (pow_three_or_pow_five_N a).resolve_left ha3
    refine ⟨ha3, fun (hb : b = 1) => h5 ?_⟩
    rw [Prod.pow_mk, ha5, hb, one_pow, Prod.mk_one_one]
  calc Nat.card {x : N × (K ⧸ N) // 10 ≤ orderOf x}
      ≤ Nat.card {a : N // a ^ 3 ≠ 1} := by
        refine Nat.card_le_card_of_injective
          (fun x => ⟨x.1.1, (hlarge x.1 x.2).1⟩) ?_
        intro x y hxy
        have h1 : x.1.1 = y.1.1 := congrArg Subtype.val hxy
        have h2 : x.1.2 = y.1.2 :=
          eq_of_ne_one_of_card_eq_two hQ (hlarge x.1 x.2).2 (hlarge y.1 y.2).2
        exact Subtype.ext (Prod.ext h1 h2)
    _ = 24 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_filter_N]

/-- The concrete witness: `N ◁ K` with `gcd(|N|, [K : N]) = 1`, `N` nonabelian,
and `N × (K ⧸ N)` has fewer elements of order `≥ 10` (at most 24) than
`K` (exactly 60). -/
theorem witness_card_lt :
    Nat.card {x : N × (K ⧸ N) // 10 ≤ orderOf x} < Nat.card {k : K // 10 ≤ orderOf k} := by
  rw [card_large_K]
  exact lt_of_le_of_lt card_large_prod_le (by norm_num)

/-- `os(N × (K ⧸ N))` does not dominate `os(K)` for the concrete witness. -/
theorem not_orderDominates_witness : ¬ OrderDominates (N × (K ⧸ N)) K := by
  intro h
  have hle := h.card_le 10
  have hlt := witness_card_lt
  omega

/-! ## Answer to Question 31 -/

/-- **Cameron–Dey, Question 31 (arXiv:2310.06516, Sec. "Open questions"):
the abelian hypothesis in Theorem `t:extension` is necessary.**
There is a finite group `K` with a normal subgroup `N` of order coprime to its
index such that `N` is nonabelian and `os(N × (K ⧸ N))` neither dominates nor
strongly dominates `os(K)`.  (Theorem `t:extension` asserts strong domination
whenever, in addition, `N` is abelian.) -/
theorem question31_abelian_necessary :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (N : Subgroup K) (_ : N.Normal),
      (Nat.card N).Coprime N.index ∧ (¬ ∀ a b : N, a * b = b * a) ∧
      ¬ OrderDominates (N × (K ⧸ N)) K ∧ ¬ StronglyDominates (N × (K ⧸ N)) K :=
  ⟨K, inferInstance, inferInstance, N, N_normal,
    by rw [card_N, index_N]; norm_num, N_not_comm, not_orderDominates_witness,
    fun h => not_orderDominates_witness (OrderDominates.of_stronglyDominates h)⟩

end CameronDeyQuestion31
