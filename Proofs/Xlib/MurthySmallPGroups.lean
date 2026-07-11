import Xlib.TPP

/-!
# Murthy's Proposition 2.14: small `p`-groups have `ρ₀ = 1`

This file formalizes **Murthy's Proposition 2.14** (arXiv:2602.15796,
`PropRho0p4`): every `p`-group `G` of order at most `p⁴` has subgroup TPP ratio
`ρ₀(G) = 1`, equivalently `β₀(G) = |G|`, equivalently every subgroup TPP triple
`(H, K, L)` satisfies `|H| · |K| · |L| ≤ |G|`.

## The proof

Murthy's paper proof routes through external structure theorems (every
nonabelian group of order `p³`/`p⁴` has an abelian subgroup of index `p`).
We instead give the **self-contained elementary** argument, which Murthy also
attributes to "combinatorial constraints" from Neumann
[Neunhöffer, S1461157010000288, Observation 3.1]:

* **Neumann's inequality** (the engine, `card_mul_card_union_le`): for *any*
  basic TPP triple `(S, T, U)` of finsets in *any* finite group,
  `|S| · |T ∪ U| ≤ |G|`. The map `(s, x) ↦ x * s⁻¹` from `S × (T ∪ U)` to `G`
  is injective (the orientation `x * s⁻¹` matches the left-quotient convention
  of `TripleProductProperty`). No commutativity is needed — this is what makes
  it stronger than the abelian barrier.

* Since a basic triple has `T ∩ U = {1}`, this reads
  `|S| · (|T| + |U| - 1) ≤ |G|`, and (by permutation invariance of the subgroup
  TPP, `subgroupTPP_iff` + `STPPCond.swap12`) likewise with `T` outer.

* **The arithmetic kill** (`exp_sum_le_four`): if `|H| = p^a`, `|K| = p^b`,
  `|L| = p^c` are subgroup orders in a group of order `p^N` with `N ≤ 4`, the
  `S`-outer and `T`-outer Neumann inequalities force `a + b + c ≤ N`, hence
  `|H| · |K| · |L| ≤ |G|`. (At `N = 5` this fails — `(p², p², p²)` survives —
  which is exactly why the proposition stops at `p⁴`.)

## Main result

* `Xlib.MurthySmallPGroups.stppCapacity_eq_card_of_card_le_pow_four` —
  `stppCapacity G = Fintype.card G` for a `p`-group of order `≤ p⁴`.
-/

open scoped BigOperators

namespace Xlib.MurthySmallPGroups

open Xlib.TPP

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Lower bound: the trivial subgroup triple -/

/-- The subgroup capacity is at least `|G|`, witnessed by `(⊤, ⊥, ⊥)`. -/
theorem card_le_stppCapacity : Fintype.card G ≤ stppCapacity G := by
  classical
  -- carriers of the trivial triple
  have hbot : ((⊥ : Subgroup G) : Set G).toFinset = {1} := by
    rw [Subgroup.coe_bot]; ext; simp
  have htop : ((⊤ : Subgroup G) : Set G).toFinset = Finset.univ := by
    rw [Subgroup.coe_top]; ext; simp
  have hTPP : TripleProductProperty ((⊤ : Subgroup G) : Set G).toFinset
      ((⊥ : Subgroup G) : Set G).toFinset ((⊥ : Subgroup G) : Set G).toFinset := by
    rw [htop, hbot]; exact tpp_trivial
  -- the summand value at `(⊤, ⊥, ⊥)`
  have hval : (if TripleProductProperty ((⊤ : Subgroup G) : Set G).toFinset
        ((⊥ : Subgroup G) : Set G).toFinset ((⊥ : Subgroup G) : Set G).toFinset
      then Nat.card (⊤ : Subgroup G) * Nat.card (⊥ : Subgroup G) * Nat.card (⊥ : Subgroup G)
      else 0) = Fintype.card G := by
    rw [if_pos hTPP, Subgroup.card_bot, mul_one, mul_one,
      Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv, Nat.card_eq_fintype_card]
  have hle := Finset.le_sup (s := (Finset.univ : Finset (Subgroup G × Subgroup G × Subgroup G)))
    (f := fun p => if TripleProductProperty (p.1 : Set G).toFinset (p.2.1 : Set G).toFinset
        (p.2.2 : Set G).toFinset
      then Nat.card p.1 * Nat.card p.2.1 * Nat.card p.2.2 else 0)
    (Finset.mem_univ ((⊤ : Subgroup G), (⊥ : Subgroup G), (⊥ : Subgroup G)))
  simp only at hle
  rw [hval] at hle
  exact hle

/-! ### Neumann's inequality (the engine)

For a basic TPP triple `(S, T, U)`, the map `(s, x) ↦ s⁻¹ * x` from
`S × (T ∪ U)` into `G` is injective. This is Neumann's
[S1461157010000288, Observation 3.1] sharpening of the abelian barrier; unlike
the abelian barrier it uses no commutativity. -/

omit [Fintype G] in
/-- **Neumann injectivity.** Under the TPP with `1 ∈ T` and `1 ∈ U`, the map
`(s, x) ↦ x * s⁻¹` is injective on `S ×ˢ (T ∪ U)`. (The orientation `x * s⁻¹`
is what matches the left-quotient convention of `TripleProductProperty`.) -/
theorem injOn_inv_mul {S T U : Finset G} (h : TripleProductProperty S T U)
    (hT : (1 : G) ∈ T) (hU : (1 : G) ∈ U) :
    Set.InjOn (fun p : G × G => p.2 * p.1⁻¹)
      ((S ×ˢ (T ∪ U) : Finset (G × G)) : Set (G × G)) := by
  intro p hp q hq heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_union] at hp hq
  obtain ⟨hpS, hpx⟩ := hp
  obtain ⟨hqS, hqx⟩ := hq
  simp only at heq
  obtain ⟨s, x⟩ := p
  obtain ⟨s', x'⟩ := q
  simp only at hpS hpx hqS hqx heq ⊢
  -- `heq : x * s⁻¹ = x' * s'⁻¹`; goal `(s, x) = (s', x')`
  -- the clean relation behind the map `x * s⁻¹`
  have hrel : s'⁻¹ * s = x'⁻¹ * x := by
    -- `s'⁻¹ * s = x'⁻¹ * x` ↔ `x' * s'⁻¹ * s = x`, and `x' * s'⁻¹ = x * s⁻¹` is heq.symm
    have h2 : x' * s'⁻¹ * s = x := by rw [← heq]; group
    rw [← h2]; group
  -- the swapped relation, for the cases where the U-element is on the left
  have hrel2 : s⁻¹ * s' = x⁻¹ * x' := by
    have := congrArg (·⁻¹) hrel
    simpa only [mul_inv_rev, inv_inv] using this
  rcases hpx with hxT | hxU <;> rcases hqx with hx'T | hx'U
  · -- both in T: T-pair (x', x), U trivial
    have key : s'⁻¹ * s * x⁻¹ * x' * (1:G)⁻¹ * 1 = 1 := by
      rw [inv_one, mul_one, mul_one, hrel]; group
    obtain ⟨hss, hxx, -⟩ := h s hpS s' hqS x' hx'T x hxT 1 hU 1 hU key
    exact Prod.ext hss hxx.symm
  · -- x ∈ T, x' ∈ U : forces x = 1 = x'. T-pair (x,1), U-pair (1,x')
    have key : s'⁻¹ * s * x⁻¹ * 1 * (1:G)⁻¹ * x' = 1 := by
      rw [inv_one, mul_one, mul_one, hrel]; group
    obtain ⟨hss, hx1, hx'1⟩ := h s hpS s' hqS 1 hT x hxT x' hx'U 1 hU key
    exact Prod.ext hss (hx1.symm.trans hx'1.symm)
  · -- x ∈ U, x' ∈ T : forces x = 1 = x'. swap S-args; T-pair (1,x'), U-pair (x,1)
    have key : s⁻¹ * s' * x'⁻¹ * 1 * (1:G)⁻¹ * x = 1 := by
      rw [inv_one, mul_one, mul_one, hrel2]; group
    obtain ⟨hss, hx'1, hx1⟩ := h s' hqS s hpS 1 hT x' hx'T x hxU 1 hU key
    exact Prod.ext hss.symm (hx1.trans hx'1)
  · -- both in U: U-pair (x', x), T trivial
    have key : s'⁻¹ * s * (1:G)⁻¹ * 1 * x⁻¹ * x' = 1 := by
      rw [inv_one, mul_one, mul_one, hrel]; group
    obtain ⟨hss, -, hxx⟩ := h s hpS s' hqS 1 hT 1 hT x' hx'U x hxU key
    exact Prod.ext hss hxx.symm

/-- **Neumann's inequality.** For a basic TPP triple, `|S| · |T ∪ U| ≤ |G|`. -/
theorem card_mul_card_union_le {S T U : Finset G}
    (h : TripleProductProperty S T U) (hT : (1 : G) ∈ T) (hU : (1 : G) ∈ U) :
    S.card * (T ∪ U).card ≤ Fintype.card G := by
  have hcard :
      (S ×ˢ (T ∪ U) : Finset (G × G)).card ≤ (Finset.univ : Finset G).card :=
    Finset.card_le_card_of_injOn (fun p => p.2 * p.1⁻¹)
      (fun _ _ => Finset.mem_univ _) (injOn_inv_mul h hT hU)
  rw [Finset.card_product] at hcard
  simpa using hcard

/-- The three Neumann inequalities in the form Murthy uses,
`|S| · (|T| + |U| - 1) ≤ |G|` (and cyclic), phrased without `ℕ`-subtraction as
`|S| · (|T| + |U|) ≤ |G| + |S|`, for a *basic* TPP triple. -/
theorem neumann_ineq {S T U : Finset G} (h : TripleProductProperty S T U)
    (hS : (1 : G) ∈ S) (hT : (1 : G) ∈ T) (hU : (1 : G) ∈ U) :
    S.card * (T.card + U.card) ≤ Fintype.card G + S.card := by
  have hbase := card_mul_card_union_le h hT hU
  -- `T ∩ U = {1}`, so `|T ∪ U| + 1 = |T| + |U|`
  have hinter : T ∩ U = {1} := inter_TU_eq_one_of_basic h hS hT hU
  have hcard : (T ∪ U).card + 1 = T.card + U.card := by
    have := Finset.card_union_add_card_inter T U
    rw [hinter, Finset.card_singleton] at this
    omega
  -- `|S|·(|T|+|U|) = |S|·(|T∪U|+1) = |S|·|T∪U| + |S| ≤ |G| + |S|`
  calc S.card * (T.card + U.card)
      = S.card * ((T ∪ U).card + 1) := by rw [hcard]
    _ = S.card * (T ∪ U).card + S.card := by ring
    _ ≤ Fintype.card G + S.card := by omega

/-! ### The subgroup TPP as a symmetric condition

For *subgroups* `H, K, L`, the TPP on the carrier finsets is equivalent to the
symmetric condition `∀ α ∈ H, β ∈ K, γ ∈ L, α·β·γ = 1 → α = β = γ = 1`
(Murthy [2602.15796], the subgroup form of Theorem [HM]). This condition is
manifestly closed under cyclic rotation (conjugation) and reversal (inversion +
subgroup closure), giving full permutation invariance — which lets us read off
Neumann's inequality with *any* of `H, K, L` in the outer position. -/

/-- The subgroup TPP condition `α·β·γ = 1 → α = β = γ = 1`. -/
def STPPCond (H K L : Subgroup G) : Prop :=
  ∀ α ∈ H, ∀ β ∈ K, ∀ γ ∈ L, α * β * γ = 1 → α = 1 ∧ β = 1 ∧ γ = 1

omit [DecidableEq G] in
open scoped Classical in
/-- The carrier TPP for subgroups is equivalent to `STPPCond`. -/
theorem subgroupTPP_iff {H K L : Subgroup G} :
    TripleProductProperty (H : Set G).toFinset (K : Set G).toFinset
      (L : Set G).toFinset ↔ STPPCond H K L := by
  constructor
  · intro h α hα β hβ γ hγ hprod
    -- instantiate TPP at `(α,1), (β,1), (γ,1)`; memberships unify the Fintype with `h`
    have key : (1:G)⁻¹ * α * (1:G)⁻¹ * β * (1:G)⁻¹ * γ = 1 := by
      rw [inv_one]; rw [one_mul, mul_one, mul_one]; exact hprod
    exact h α (Set.mem_toFinset.mpr hα) 1 (Set.mem_toFinset.mpr H.one_mem)
      β (Set.mem_toFinset.mpr hβ) 1 (Set.mem_toFinset.mpr K.one_mem)
      γ (Set.mem_toFinset.mpr hγ) 1 (Set.mem_toFinset.mpr L.one_mem) key
  · intro h s hs s' hs' t ht t' ht' u hu u' hu' heq
    have hsm : s ∈ H := Set.mem_toFinset.mp hs
    have hs'm : s' ∈ H := Set.mem_toFinset.mp hs'
    have htm : t ∈ K := Set.mem_toFinset.mp ht
    have ht'm : t' ∈ K := Set.mem_toFinset.mp ht'
    have hum : u ∈ L := Set.mem_toFinset.mp hu
    have hu'm : u' ∈ L := Set.mem_toFinset.mp hu'
    have hαH : s'⁻¹ * s ∈ H := H.mul_mem (H.inv_mem hs'm) hsm
    have hβK : t'⁻¹ * t ∈ K := K.mul_mem (K.inv_mem ht'm) htm
    have hγL : u'⁻¹ * u ∈ L := L.mul_mem (L.inv_mem hu'm) hum
    have hprod : (s'⁻¹ * s) * (t'⁻¹ * t) * (u'⁻¹ * u) = 1 := by
      rw [← heq]; group
    obtain ⟨h1, h2, h3⟩ := h _ hαH _ hβK _ hγL hprod
    refine ⟨?_, ?_, ?_⟩
    · have := h1; rwa [inv_mul_eq_one, eq_comm] at this
    · have := h2; rwa [inv_mul_eq_one, eq_comm] at this
    · have := h3; rwa [inv_mul_eq_one, eq_comm] at this

omit [Fintype G] [DecidableEq G] in
/-- `STPPCond` is invariant under cyclic rotation `(H,K,L) ↦ (K,L,H)`. -/
theorem STPPCond.rotate {H K L : Subgroup G} (h : STPPCond H K L) :
    STPPCond K L H := by
  intro β hβ γ hγ α hα hprod
  -- `β*γ*α = 1` rotates to `α*β*γ = 1` (conjugate by `α`)
  have hcyc : α * β * γ = 1 := by
    have hconj : α * β * γ = α * (β * γ * α) * α⁻¹ := by group
    rw [hconj, hprod]; group
  obtain ⟨ha, hb, hc⟩ := h α hα β hβ γ hγ hcyc
  exact ⟨hb, hc, ha⟩

omit [Fintype G] [DecidableEq G] in
/-- `STPPCond` is invariant under reversal `(H,K,L) ↦ (L,K,H)`. -/
theorem STPPCond.reverse {H K L : Subgroup G} (h : STPPCond H K L) :
    STPPCond L K H := by
  intro γ hγ β hβ α hα hprod
  -- `γ*β*α = 1` reverses to `α⁻¹*β⁻¹*γ⁻¹ = 1` (take inverse)
  have hrev : α⁻¹ * β⁻¹ * γ⁻¹ = 1 := by
    have : α⁻¹ * β⁻¹ * γ⁻¹ = (γ * β * α)⁻¹ := by group
    rw [this, hprod, inv_one]
  obtain ⟨ha, hb, hc⟩ := h α⁻¹ (H.inv_mem hα) β⁻¹ (K.inv_mem hβ) γ⁻¹ (L.inv_mem hγ) hrev
  exact ⟨inv_eq_one.mp hc, inv_eq_one.mp hb, inv_eq_one.mp ha⟩

omit [Fintype G] [DecidableEq G] in
/-- `STPPCond` invariance under the transposition `(H,K,L) ↦ (K,H,L)`. -/
theorem STPPCond.swap12 {H K L : Subgroup G} (h : STPPCond H K L) :
    STPPCond K H L :=
  h.reverse.rotate

/-! ### The arithmetic kill for `p`-groups of order `≤ p⁴`

If `s, t, u` are powers of a prime `p`, each dividing `n = p^N` with `N ≤ 4`,
and they satisfy the three Neumann inequalities
`s(t+u-1) ≤ n`, `t(s+u-1) ≤ n`, `u(s+t-1) ≤ n`, then `s·t·u ≤ n`. -/

/-- Pure arithmetic core: nonnegative integer exponents `a, b, c` whose
Neumann constraints hold for `N ≤ 4` force `a + b + c ≤ N`. The constraints are
expressed multiplicatively to match the group statement. Only the `S`-outer and
`T`-outer Neumann inequalities (`h1`, `h2`) are needed. -/
theorem exp_sum_le_four {p a b c N : ℕ} (hp : 2 ≤ p) (hN : N ≤ 4)
    (h1 : p ^ a * (p ^ b + p ^ c) ≤ p ^ N + p ^ a)
    (h2 : p ^ b * (p ^ a + p ^ c) ≤ p ^ N + p ^ b) :
    a + b + c ≤ N := by
  have hp1 : 1 < p := hp
  -- expand the products into sums of powers
  rw [mul_add, ← pow_add, ← pow_add] at h1 h2
  -- monotonicity helpers
  have mono_le : ∀ {x y : ℕ}, p ^ x ≤ p ^ y → x ≤ y := fun h =>
    (Nat.pow_le_pow_iff_right hp1).mp h
  have mono_lt : ∀ {x y : ℕ}, p ^ x < p ^ y → x < y := fun h =>
    (Nat.pow_lt_pow_iff_right hp1).mp h
  have hpow_le : ∀ {x y : ℕ}, x ≤ y → p ^ x ≤ p ^ y := fun h =>
    Nat.pow_le_pow_right (le_of_lt hp1) h
  -- unconditional pairwise bounds (drop a nonneg power term)
  have hab : a + b ≤ N := by
    apply mono_le; have : p ^ a ≤ p ^ (a + c) := hpow_le (Nat.le_add_right a c)
    omega
  have hac : a + c ≤ N := by
    apply mono_le; have : p ^ a ≤ p ^ (a + b) := hpow_le (Nat.le_add_right a b)
    omega
  have hbc : b + c ≤ N := by
    apply mono_le; have : p ^ b ≤ p ^ (b + a) := hpow_le (Nat.le_add_right b a)
    omega
  -- if any exponent is zero, two pairwise bounds already give the result
  rcases Nat.eq_zero_or_pos a with ha | ha
  · omega
  rcases Nat.eq_zero_or_pos b with hb | hb
  · omega
  rcases Nat.eq_zero_or_pos c with hc | hc
  · omega
  -- proper case: all exponents ≥ 1, get the strict `≤ N - 1` bounds
  have hstrict_ab : a + b < N := by
    apply mono_lt
    have : p ^ a < p ^ (a + c) := Nat.pow_lt_pow_right hp1 (by omega)
    omega
  have hstrict_ac : a + c < N := by
    apply mono_lt
    have : p ^ a < p ^ (a + b) := Nat.pow_lt_pow_right hp1 (by omega)
    omega
  have hstrict_bc : b + c < N := by
    apply mono_lt
    have : p ^ b < p ^ (b + a) := Nat.pow_lt_pow_right hp1 (by omega)
    omega
  omega

/-! ### Main theorem -/

/-- **Murthy Proposition 2.14.** A `p`-group of order at most `p⁴` has
`β₀(G) = |G|`, i.e. `ρ₀(G) = 1`. -/
theorem stppCapacity_eq_card_of_card_le_pow_four {p N : ℕ} (hp : p.Prime)
    (hN : N ≤ 4) (hG : Fintype.card G = p ^ N) :
    stppCapacity G = Fintype.card G := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  -- `G` is a `p`-group, hence so is every subgroup; each subgroup order is `p^?`
  have hGcard : Nat.card G = p ^ N := by rw [Nat.card_eq_fintype_card]; exact hG
  have hPG : IsPGroup p G := IsPGroup.of_card hGcard
  have hsub_pow : ∀ H : Subgroup G, ∃ a, Nat.card H = p ^ a := fun H =>
    (IsPGroup.iff_card).mp (hPG.to_subgroup H)
  -- the order of a subgroup equals the cardinality of its carrier finset
  have hcard_eq : ∀ H : Subgroup G, Nat.card H = (H : Set G).toFinset.card := fun H =>
    Nat.card_eq_card_toFinset (H : Set G)
  -- one ∈ every subgroup carrier
  have hone : ∀ H : Subgroup G, (1 : G) ∈ (H : Set G).toFinset := fun H => by
    simp [H.one_mem]
  refine le_antisymm ?_ card_le_stppCapacity
  -- bound the capacity sup termwise
  refine Finset.sup_le ?_
  rintro ⟨H, K, L⟩ _
  by_cases hTPP : TripleProductProperty (H : Set G).toFinset (K : Set G).toFinset
      (L : Set G).toFinset
  · simp only [hTPP, if_true]
    -- pull out the three subgroup orders as prime powers
    obtain ⟨a, ha⟩ := hsub_pow H
    obtain ⟨b, hb⟩ := hsub_pow K
    obtain ⟨c, hc⟩ := hsub_pow L
    -- carrier cards as prime powers
    have hHf : (H : Set G).toFinset.card = p ^ a := by rw [← hcard_eq H, ha]
    have hKf : (K : Set G).toFinset.card = p ^ b := by rw [← hcard_eq K, hb]
    have hLf : (L : Set G).toFinset.card = p ^ c := by rw [← hcard_eq L, hc]
    -- the `K`-outer permutation of the TPP
    have hTPPK : TripleProductProperty (K : Set G).toFinset (H : Set G).toFinset
        (L : Set G).toFinset := subgroupTPP_iff.mpr (subgroupTPP_iff.mp hTPP).swap12
    -- the two Neumann inequalities (S-outer and T-outer), in prime-power form
    have h1 := neumann_ineq hTPP (hone H) (hone K) (hone L)
    have h2 := neumann_ineq hTPPK (hone K) (hone H) (hone L)
    rw [hHf, hKf, hLf, hG] at h1
    rw [hHf, hKf, hLf, hG] at h2
    -- apply the arithmetic kill
    have hsum : a + b + c ≤ N := exp_sum_le_four hp2 hN h1 h2
    -- convert back: `|H||K||L| = p^(a+b+c) ≤ p^N = |G|`
    calc Nat.card H * Nat.card K * Nat.card L
        = p ^ a * p ^ b * p ^ c := by rw [ha, hb, hc]
      _ = p ^ (a + b + c) := by rw [← pow_add, ← pow_add]
      _ ≤ p ^ N := Nat.pow_le_pow_right (le_of_lt hp.one_lt) hsum
      _ = Fintype.card G := hG.symm
  · simp only [hTPP, if_false]; exact Nat.zero_le _

end Xlib.MurthySmallPGroups
