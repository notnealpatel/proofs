import Xlib.TPP

/-!
# Murthy's prime-index bound `ρ₀(G) ≤ p²/(2p-1)`

This file formalizes the main theorem of Murthy
[arXiv:2512.16730, Theorem 4.1 (`MABQuoPrime`)]:

> If `G` is a finite group with an **abelian normal subgroup `N` of prime index
> `p`**, then `ρ₀(G) ≤ p²/(2p-1)`.

Equivalently, clearing denominators over `ℕ`, every subgroup TPP triple
`(S, T, U)` of `G` satisfies
`(2p-1) · |S| · |T| · |U| ≤ p² · |G|`, hence
`(2p-1) · β₀(G) ≤ p² · |G|`.

For `p = 2` (dihedral-type groups) this is the bound `ρ₀ ≤ 4/3`.

## Proof outline (Murthy, coset counting inside `N`)

Fix a subgroup TPP triple `(S, T, U)`. Write `S₀ = S ⊓ N`, `T₀ = T ⊓ N`,
`U₀ = U ⊓ N`, and `K = S₀ ⊔ T₀ ⊔ U₀` (a subgroup of the abelian `N`; as a *set*
`K = S₀·T₀·U₀`). Let `σ = |S : S₀|`, `τ = |T : T₀|`, `υ = |U : U₀|`.

* Each of `σ, τ, υ` is `1` or `p` (the image `S·N/N ≤ G/N` of prime order).
* `|S|·|T|·|U| = σ·τ·υ·|K|` (coset counting `|S| = σ·|S₀|` plus the abelian
  barrier equality `|K| = |S₀|·|T₀|·|U₀|`).
* `|G| = p·|N|` and `|N| = |N : K|·|K|` (Lagrange).

So the whole theorem reduces to the **index bound**
`(2p-1)·σ·τ·υ ≤ p³·|N : K|`, which splits by `σ·τ·υ`:

* `σ·τ·υ ≤ p`: trivial (`2p-1 ≤ p²`).
* `σ·τ·υ = p²` (two of them `= p`): needs `|N : K| ≥ 2`.
* `σ·τ·υ = p³` (all three `= p`): needs `|N : K| ≥ 2p-1`. This is the crux,
  Murthy's Lemma 3.3 (`DisjTPPSets`): the `2p-1` cosets
  `K`, `{Sₓ⁻¹Tₓ}`, `{Sᵧ⁻¹Uᵧ}` (`x, y` ranging over the `p-1` nontrivial
  cosets of `N`) are pairwise distinct in `N ⧸ K`.

## References

* I. Murthy, *A note on the triple product property for finite groups with
  abelian normal subgroups of prime index*, [arXiv:2512.16730], Thm 4.1.
-/

open scoped BigOperators Pointwise

namespace Xlib.MurthyPrimeIndex

open Xlib.TPP

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- In a commutative group, `a * b * c = a' * b' * c'` rearranges into the TPP
hypothesis `a'⁻¹ * a * b'⁻¹ * b * c'⁻¹ * c = 1`. (A copy of TPP.lean's private
`prod_eq_imp_quot_eq_one` for use through subgroup lifting.) -/
private theorem comm_prod_quot {H : Type*} [CommGroup H]
    (a b c a' b' c' : H) (heq : a * b * c = a' * b' * c') :
    a'⁻¹ * a * b'⁻¹ * b * c'⁻¹ * c = 1 := by
  have key : a'⁻¹ * a * b'⁻¹ * b * c'⁻¹ * c = (a * b * c) * (a' * b' * c')⁻¹ := by
    simp only [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  rw [key, heq, mul_inv_cancel]

/-- Membership in the join `A ⊔ B ⊔ C` of three subgroups of a **commutative**
group: `g ∈ A ⊔ B ⊔ C ↔ ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, g = a * b * c`. -/
theorem mem_sup3 {H : Type*} [CommGroup H] {A B C : Subgroup H} {g : H} :
    g ∈ A ⊔ B ⊔ C ↔ ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, g = a * b * c := by
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨ab, hab, c, hc, rfl⟩
    rw [Subgroup.mem_sup] at hab
    obtain ⟨a, ha, b, hb, rfl⟩ := hab
    exact ⟨a, ha, b, hb, c, hc, rfl⟩
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    exact ⟨a * b, Subgroup.mem_sup.mpr ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩

/-! ### Abelian product-card bound

Inside the abelian normal subgroup `N`, the restricted triple
`(S₀, T₀, U₀) = (S ⊓ N, T ⊓ N, U ⊓ N)` is a subgroup TPP triple of `N`, so the
product map `(s, t, u) ↦ s * t * u` injects `S₀ × T₀ × U₀` into any subgroup
`K` containing `S₀, T₀, U₀`. This is the only place the abelian barrier
(`TPP.injOn_mul`) is used. -/

omit [DecidableEq G] in
/-- The product map `(s, t, u) ↦ s * t * u` from the carriers of three subgroups
`A, B, C` of an abelian subgroup `N`, all contained in a subgroup `K`, is
injective into `K`, provided the full triple `(S, T, U)` has the (subgroup) TPP
and `A ≤ S`, `B ≤ T`, `C ≤ U`. Hence `|A| · |B| · |C| ≤ |K|`. -/
theorem card_mul_card_mul_card_le_of_le_abelian
    {S T U : Subgroup G} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    [DecidablePred (· ∈ U)]
    (hTPP : SubgroupTripleProductProperty S T U)
    {N : Subgroup G} (hAb : ∀ a b : N, (a : G) * b = b * a)
    {A B C K : Subgroup G} (hAS : A ≤ S) (hBT : B ≤ T) (hCU : C ≤ U)
    (hKN : K ≤ N) (hAK : A ≤ K) (hBK : B ≤ K) (hCK : C ≤ K) :
    Nat.card A * Nat.card B * Nat.card C ≤ Nat.card K := by
  -- The element-wise TPP on the carriers of `S, T, U`.
  have hTPP' : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset := hTPP
  -- `↥N` is commutative.
  letI : CommGroup N :=
    { mul_comm := fun a b => Subtype.ext (hAb a b) }
  -- Membership helpers: `A, B, C ≤ N`.
  have hAN : A ≤ N := le_trans hAK hKN
  have hBN : B ≤ N := le_trans hBK hKN
  have hCN : C ≤ N := le_trans hCK hKN
  -- The injection `↥A × ↥B × ↥C → ↥K`.
  set f : A × B × C → K := fun p =>
    ⟨(p.1 : G) * (p.2.1 : G) * (p.2.2 : G),
      mul_mem (mul_mem (hAK p.1.2) (hBK p.2.1.2)) (hCK p.2.2.2)⟩ with hf
  have hinj : Function.Injective f := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ heq
    -- Extract the `G`-level product equality.
    have hG : (a : G) * (b : G) * (c : G) = (a' : G) * (b' : G) * (c' : G) :=
      congrArg Subtype.val heq
    -- Lift the six elements into `↥N` and rearrange there.
    set aN : N := ⟨(a : G), hAN a.2⟩
    set bN : N := ⟨(b : G), hBN b.2⟩
    set cN : N := ⟨(c : G), hCN c.2⟩
    set aN' : N := ⟨(a' : G), hAN a'.2⟩
    set bN' : N := ⟨(b' : G), hBN b'.2⟩
    set cN' : N := ⟨(c' : G), hCN c'.2⟩
    have hGN : aN * bN * cN = aN' * bN' * cN' := Subtype.ext hG
    have hquotN : aN'⁻¹ * aN * bN'⁻¹ * bN * cN'⁻¹ * cN = 1 :=
      comm_prod_quot aN bN cN aN' bN' cN' hGN
    -- Map down to `G` via the subgroup inclusion.
    have hquot : (a' : G)⁻¹ * (a : G) * (b' : G)⁻¹ * (b : G) * (c' : G)⁻¹ * (c : G)
        = 1 := by
      have := congrArg (N.subtype) hquotN
      simpa using this
    -- Apply the TPP for `(S, T, U)`.
    have memS : ∀ {x : G}, x ∈ A → x ∈ (S : Set G).toFinset := fun hx =>
      Set.mem_toFinset.mpr (hAS hx)
    have memT : ∀ {x : G}, x ∈ B → x ∈ (T : Set G).toFinset := fun hx =>
      Set.mem_toFinset.mpr (hBT hx)
    have memU : ∀ {x : G}, x ∈ C → x ∈ (U : Set G).toFinset := fun hx =>
      Set.mem_toFinset.mpr (hCU hx)
    obtain ⟨ha, hb, hc⟩ := hTPP' (a : G) (memS a.2) (a' : G) (memS a'.2)
      (b : G) (memT b.2) (b' : G) (memT b'.2)
      (c : G) (memU c.2) (c' : G) (memU c'.2) hquot
    -- Conclude equality of the subtype triples.
    refine Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hc))
  -- Card inequality from the injection.
  have hcard := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_prod, Nat.card_prod, ← mul_assoc] at hcard

/-! ### Support sizes are `1` or `p`

The `N`-support size `σ = |X : X ⊓ N| = N.relIndex X` divides the prime index
`p = N.index` (`N` normal), hence is `1` or `p`. -/

omit [Fintype G] [DecidableEq G] in
/-- `|X| = (N.relIndex X) · |X ⊓ N|`: Lagrange for `X ⊓ N ≤ X`, with the
relative index identified via `inf_relIndex_right`. -/
theorem card_eq_relIndex_mul_card_inf (N X : Subgroup G) :
    Nat.card X = N.relIndex X * Nat.card (N ⊓ X : Subgroup G) := by
  have h := Subgroup.relIndex_mul_relIndex (H := (⊥ : Subgroup G))
    (K := N ⊓ X) (L := X) bot_le inf_le_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    Subgroup.inf_relIndex_right] at h
  rw [← h]; ring

omit [Fintype G] [DecidableEq G] in
/-- The support size `N.relIndex X` divides the prime index `N.index = p`,
hence equals `1` or `p`. -/
theorem relIndex_eq_one_or_eq_of_prime_index {N : Subgroup G} [N.Normal]
    {p : ℕ} (hp : p.Prime) (hpN : N.index = p) (X : Subgroup G) :
    N.relIndex X = 1 ∨ N.relIndex X = p := by
  have hdvd : N.relIndex X ∣ p := hpN ▸ Subgroup.relIndex_dvd_index_of_normal N X
  exact (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd).imp id id

/-! ### The simplified subgroup TPP and its permutation invariance

For subgroups, the TPP reduces to: `s ∈ S, t ∈ T, u ∈ U, s * t * u = 1`
implies `s = t = u = 1`. This form is fully symmetric under the `S₃`-action,
which the coset-counting argument uses repeatedly. -/

/-- The simplified subgroup-TPP predicate: `s * t * u = 1 → s = t = u = 1`. -/
def SimpleTPP (S T U : Subgroup G) : Prop :=
  ∀ s ∈ S, ∀ t ∈ T, ∀ u ∈ U, s * t * u = 1 → s = 1 ∧ t = 1 ∧ u = 1

omit [DecidableEq G] in
/-- The subgroup TPP implies its simplified form (specialize the primed
elements to `1`). -/
theorem SubgroupTripleProductProperty.simpleTPP {S T U : Subgroup G}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
    (h : SubgroupTripleProductProperty S T U) : SimpleTPP S T U := by
  intro s hs t ht u hu hstu
  have h1S : (1 : G) ∈ (S : Set G).toFinset := Set.mem_toFinset.mpr (one_mem S)
  have h1T : (1 : G) ∈ (T : Set G).toFinset := Set.mem_toFinset.mpr (one_mem T)
  have h1U : (1 : G) ∈ (U : Set G).toFinset := Set.mem_toFinset.mpr (one_mem U)
  have hsF : s ∈ (S : Set G).toFinset := Set.mem_toFinset.mpr hs
  have htF : t ∈ (T : Set G).toFinset := Set.mem_toFinset.mpr ht
  have huF : u ∈ (U : Set G).toFinset := Set.mem_toFinset.mpr hu
  have key : (1 : G)⁻¹ * s * (1 : G)⁻¹ * t * (1 : G)⁻¹ * u = 1 := by
    simpa using hstu
  obtain ⟨h1, h2, h3⟩ := h s hsF 1 h1S t htF 1 h1T u huF 1 h1U key
  exact ⟨h1, h2, h3⟩

omit [Fintype G] [DecidableEq G] in
/-- Cyclic permutation invariance of the simplified TPP:
`SimpleTPP S T U → SimpleTPP T U S`. From `t * u * s = 1` we get
`s * t * u = 1`, since `t * u = s⁻¹`. -/
theorem SimpleTPP.cyc {S T U : Subgroup G} (h : SimpleTPP S T U) :
    SimpleTPP T U S := by
  intro t ht u hu s hs htus
  have htu : t * u = s⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]; exact htus
  have hstu : s * t * u = 1 := by rw [mul_assoc, htu, mul_inv_cancel]
  obtain ⟨h1, h2, h3⟩ := h s hs t ht u hu hstu
  exact ⟨h2, h3, h1⟩

omit [Fintype G] [DecidableEq G] in
/-- Swap invariance of the simplified TPP: `SimpleTPP S T U → SimpleTPP S U T`.
From `s * u * t = 1`, take inverses: `t⁻¹ * u⁻¹ * s⁻¹ = 1`, then use the cyclic
version applied in `(T, U, S)` order. -/
theorem SimpleTPP.swap23 {S T U : Subgroup G} (h : SimpleTPP S T U) :
    SimpleTPP S U T := by
  intro s hs u hu t ht hsut
  -- inverse equation `t⁻¹ * u⁻¹ * s⁻¹ = 1` lives in `(T, U, S)` order
  have hinv : t⁻¹ * u⁻¹ * s⁻¹ = 1 := by
    have := congrArg (·⁻¹) hsut
    simpa [mul_assoc] using this
  obtain ⟨h1, h2, h3⟩ :=
    (h.cyc) t⁻¹ (inv_mem ht) u⁻¹ (inv_mem hu) s⁻¹ (inv_mem hs) hinv
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (·⁻¹) h3
  · simpa using congrArg (·⁻¹) h2
  · simpa using congrArg (·⁻¹) h1

/-! ### Coset distinctness (Murthy Lemma 3.3, element level)

These are the three element-level facts behind Murthy's Lemma 3.3
(`DisjTPPSets`), phrased over `G`: the witnessing products land in the abelian
`N`, and the assumption that two of them lie in the same coset of
`K = (S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N)` (unfolded to a product `s₀ * t₀ * u₀`) is
refuted by the simplified TPP. Commutativity in `N` is used to regroup. -/

omit [Fintype G] [DecidableEq G] in
/-- **Lemma 3.3(1): nontriviality.** If `sx ∈ S` lies outside `N`, `tx ∈ T`, and
`sx⁻¹ * tx = s₀ * t₀ * u₀` with `s₀, t₀, u₀` in the respective intersections with
`N`, then `False`. (The coset `Sₓ⁻¹Tₓ U₀` is nontrivial.) -/
theorem distinct_nontriv {S T U N : Subgroup G} (hN : ∀ a b : N, (a : G) * b = b * a)
    (hTPP : SimpleTPP S T U) {sx tx s₀ t₀ u₀ : G}
    (hsx : sx ∈ S) (hsxN : sx ∉ N) (htx : tx ∈ T)
    (hs₀ : s₀ ∈ S) (hs₀N : s₀ ∈ N) (ht₀ : t₀ ∈ T) (ht₀N : t₀ ∈ N)
    (hu₀ : u₀ ∈ U) (hu₀N : u₀ ∈ N) (heq : sx⁻¹ * tx = s₀ * t₀ * u₀) : False := by
  -- Regroup using `t₀ * u₀ = u₀ * t₀` in the abelian `N`.
  have hcomm : t₀ * u₀ = u₀ * t₀ := by
    have := hN ⟨t₀, ht₀N⟩ ⟨u₀, hu₀N⟩
    simpa using this
  have heq' : sx⁻¹ * tx = s₀ * u₀ * t₀ := by rw [heq]; rw [mul_assoc, hcomm, ← mul_assoc]
  -- The product `(s₀⁻¹ * sx⁻¹) * (tx * t₀⁻¹) * u₀⁻¹ = 1`.
  have hABC : (s₀⁻¹ * sx⁻¹) * (tx * t₀⁻¹) * u₀⁻¹ = 1 := by
    have : (s₀⁻¹ * sx⁻¹) * (tx * t₀⁻¹) * u₀⁻¹
        = s₀⁻¹ * (sx⁻¹ * tx) * t₀⁻¹ * u₀⁻¹ := by group
    rw [this, heq']; group
  obtain ⟨hA, _, _⟩ := hTPP _ (mul_mem (inv_mem hs₀) (inv_mem hsx)) _
    (mul_mem htx (inv_mem ht₀)) _ (inv_mem hu₀) hABC
  -- `A = 1` forces `sx = s₀⁻¹ ∈ N`, contradicting `sx ∉ N`.
  apply hsxN
  have hsx_eq : sx = s₀⁻¹ := by
    have := mul_eq_one_iff_eq_inv.mp hA
    simpa using this.symm
  rw [hsx_eq]
  exact inv_mem hs₀N

omit [Fintype G] [DecidableEq G] in
/-- **Lemma 3.3(2): within-family distinctness.** With `S₀, T₀, U₀` (the
intersections with `N`) all normal in `G`, distinct nontrivial cosets give
distinct `K`-cosets of the products `sₓ⁻¹tₓ`. Concretely: if `sx, sy ∈ S` lie in
*different* `N`-cosets (`sx⁻¹ * sy ∉ N`), `tx, ty ∈ T`, and
`sx⁻¹ * tx = (sy⁻¹ * ty) * (s₀ * t₀ * u₀)` with the `…₀` in the normal
intersections, then `False`. -/
theorem distinct_within {S T U : Subgroup G} {N S₀ T₀ U₀ : Subgroup G}
    (hN : N.Normal) (hS₀ : S₀.Normal) (hU₀ : U₀.Normal)
    (hS₀S : S₀ ≤ S) (hS₀N : S₀ ≤ N) (hT₀T : T₀ ≤ T)
    (hU₀U : U₀ ≤ U)
    (hTPP : SimpleTPP S T U) {sx tx sy ty s₀ t₀ u₀ : G}
    (hsx : sx ∈ S) (hsy : sy ∈ S) (hxy : sx⁻¹ * sy ∉ N) (htx : tx ∈ T) (hty : ty ∈ T)
    (hs₀ : s₀ ∈ S₀) (ht₀ : t₀ ∈ T₀) (hu₀ : u₀ ∈ U₀)
    (heq : sx⁻¹ * tx = (sy⁻¹ * ty) * (s₀ * t₀ * u₀)) : False := by
  -- Move `s₀` left past `ty` (normality of `S₀`): `s₀' := ty * s₀ * ty⁻¹ ∈ S₀`.
  set s₀' : G := ty * s₀ * ty⁻¹ with hs₀'
  have hs₀'mem : s₀' ∈ S₀ := hS₀.conj_mem s₀ hs₀ ty
  -- Move `u₀⁻¹` right past `t₀⁻¹ * ty⁻¹` (normality of `U₀`):
  -- `û := (t₀⁻¹ * ty⁻¹)⁻¹ * u₀⁻¹ * (t₀⁻¹ * ty⁻¹) ∈ U₀`.
  set w : G := t₀⁻¹ * ty⁻¹ with hw
  set û : G := w⁻¹ * u₀⁻¹ * w with hû
  have hûmem : û ∈ U₀ := by
    have : û = w⁻¹ * u₀⁻¹ * w⁻¹⁻¹ := by rw [hû]; group
    rw [this]; exact hU₀.conj_mem u₀⁻¹ (inv_mem hu₀) w⁻¹
  -- The grouped product `A * B * C = 1`.
  set A : G := s₀'⁻¹ * sy * sx⁻¹ with hA
  set B : G := tx * t₀⁻¹ * ty⁻¹ with hB
  have hABC : A * B * û = 1 := by
    -- `A * B * û` rewrites (via the conjugation defs) to a word in `sx⁻¹ * tx`.
    have hexp : A * B * û = s₀'⁻¹ * (sy * (sx⁻¹ * tx) * t₀⁻¹ * ty⁻¹) * (w⁻¹ * u₀⁻¹ * w) := by
      rw [hA, hB, hû]; group
    rw [hexp, heq]
    rw [hs₀', hw]; group
  obtain ⟨hAeq, _, _⟩ :=
    hTPP A (mul_mem (mul_mem (inv_mem (hS₀S hs₀'mem)) hsy) (inv_mem hsx))
      B (mul_mem (mul_mem htx (inv_mem (hT₀T ht₀))) (inv_mem hty))
      û (hU₀U hûmem) hABC
  -- `A = 1` forces `sy = s₀' * sx`, so `sx⁻¹ * sy = sx⁻¹ * s₀' * sx ∈ N`.
  apply hxy
  -- From `A = 1`: `sy * sx⁻¹ = s₀'`, i.e. `sy = s₀' * sx`.
  have hsy_eq : sy = s₀' * sx := by
    have h1 : s₀'⁻¹ * (sy * sx⁻¹) = 1 := by rw [hA] at hAeq; group; rw [← hAeq]; group
    have h2 : sy * sx⁻¹ = s₀' := (inv_mul_eq_one.mp h1).symm
    have := congrArg (· * sx) h2
    simpa using this
  rw [hsy_eq]
  -- `sx⁻¹ * (s₀' * sx) = (sx⁻¹ * s₀' * sx) ∈ N` since `s₀' ∈ S₀ ≤ N` and `N` normal.
  have hs₀'N : s₀' ∈ N := hS₀N hs₀'mem
  have : sx⁻¹ * (s₀' * sx) = sx⁻¹ * s₀' * sx⁻¹⁻¹ := by group
  rw [this]
  exact hN.conj_mem s₀' hs₀'N sx⁻¹

omit [Fintype G] [DecidableEq G] in
/-- **Lemma 3.3(3): cross-family distinctness.** With `S₀, U₀` normal in `G`,
the `K`-coset of an `S,T`-product `sₓ⁻¹tₓ` (with `xH` nontrivial, so `tx ∉ N`)
is never equal to the `K`-coset of an `S,U`-product `sᵧ⁻¹uᵧ`. Concretely: if
`sx⁻¹ * tx = (sy⁻¹ * uy) * (s₀ * t₀ * u₀)` with the `…₀` in the normal
intersections, then `False`. (No assumption relating `x` and `y`.) -/
theorem distinct_cross {S T U : Subgroup G} {N S₀ T₀ U₀ : Subgroup G}
    (hS₀ : S₀.Normal) (hU₀ : U₀.Normal)
    (hS₀S : S₀ ≤ S) (hT₀T : T₀ ≤ T) (hT₀N : T₀ ≤ N)
    (hU₀U : U₀ ≤ U)
    (hTPP : SimpleTPP S T U) {sx tx sy uy s₀ t₀ u₀ : G}
    (hsx : sx ∈ S) (htx : tx ∈ T) (htxN : tx ∉ N) (hsy : sy ∈ S) (huy : uy ∈ U)
    (hs₀ : s₀ ∈ S₀) (ht₀ : t₀ ∈ T₀) (hu₀ : u₀ ∈ U₀)
    (heq : sx⁻¹ * tx = (sy⁻¹ * uy) * (s₀ * t₀ * u₀)) : False := by
  -- `sc := (tx * u₀⁻¹ * t₀⁻¹) * s₀⁻¹ * (tx * u₀⁻¹ * t₀⁻¹)⁻¹ ∈ S₀` (move `s₀⁻¹` to front).
  set v : G := tx * u₀⁻¹ * t₀⁻¹ with hv
  set sc : G := v * s₀⁻¹ * v⁻¹ with hsc
  have hscmem : sc ∈ S₀ := hS₀.conj_mem s₀⁻¹ (inv_mem hs₀) v
  -- `û := t₀ * u₀⁻¹ * t₀⁻¹ ∈ U₀` (move `u₀⁻¹` right past `t₀⁻¹`).
  set û : G := t₀ * u₀⁻¹ * t₀⁻¹ with hû
  have hûmem : û ∈ U₀ := hU₀.conj_mem u₀⁻¹ (inv_mem hu₀) t₀
  -- Express `tx` from `heq` and substitute, so `group` can close `A * B * C = 1`.
  have htx_val : tx = sx * ((sy⁻¹ * uy) * (s₀ * t₀ * u₀)) := by
    rw [← heq]; group
  -- Grouped product `A * B * C = 1` with `A ∈ S, B ∈ T, C ∈ U`.
  set A : G := sy * sx⁻¹ * sc with hA
  set B : G := tx * t₀⁻¹ with hB
  set C : G := û * uy⁻¹ with hC
  have hABC : A * B * C = 1 := by
    rw [hA, hB, hC, hsc, hû, hv, htx_val]; group
  obtain ⟨_, hBeq, _⟩ :=
    hTPP A (mul_mem (mul_mem hsy (inv_mem hsx)) (hS₀S hscmem))
      B (mul_mem htx (inv_mem (hT₀T ht₀)))
      C (mul_mem (hU₀U hûmem) (inv_mem huy)) hABC
  -- `B = 1` forces `tx = t₀ ∈ T₀ ≤ N`, contradicting `tx ∉ N`.
  apply htxN
  have htx_eq : tx = t₀ := by
    have := mul_eq_one_iff_eq_inv.mp hBeq
    simpa using this
  rw [htx_eq]
  exact hT₀N ht₀

/-! ### Normality of the intersections in the all-crossing case

When every member of the triple crosses `N` (`σ = τ = υ = p`), the prime-index
maximality of `N` forces `X ⊔ N = ⊤` for each `X ∈ {S, T, U}`, and then
`X ⊓ N` is normal in `G` (normalized by `X` since `N ◁ G`, and by `N` since `N`
is abelian). These give the `Sᵢ ◁ G` hypotheses that Lemma 3.3(2)/(3) need. -/

omit [Fintype G] [DecidableEq G] in
/-- A subgroup `N` of prime index is maximal: if `X ⊄ N` then `X ⊔ N = ⊤`. -/
theorem sup_eq_top_of_not_le {N : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hpN : N.index = p) {X : Subgroup G} (hXN : ¬ X ≤ N) : X ⊔ N = ⊤ := by
  have hle : N ≤ X ⊔ N := le_sup_right
  -- `(X ⊔ N).index ∣ N.index = p`.
  have hmul := Subgroup.relIndex_mul_index hle
  have hdvd : (X ⊔ N).index ∣ p := hpN ▸ Dvd.intro_left _ hmul
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hpp
  · -- index one ⇒ `X ⊔ N = ⊤`.
    exact Subgroup.index_eq_one.mp h1
  · -- index `p` ⇒ `N.relIndex (X ⊔ N) = 1` ⇒ `X ⊔ N ≤ N`, contradicting `X ⊄ N`.
    exfalso
    rw [hpN, hpp] at hmul
    have hrel : N.relIndex (X ⊔ N) = 1 := by
      have hp0 : 0 < p := hp.pos
      have : N.relIndex (X ⊔ N) * p = 1 * p := by rw [hmul, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hp0 this
    have hsub : X ⊔ N ≤ N := Subgroup.relIndex_eq_one.mp hrel
    exact hXN (le_trans le_sup_left hsub)

omit [Fintype G] [DecidableEq G] in
/-- If `N ◁ G` is abelian (pairwise-commuting) and `X ⊔ N = ⊤`, then `X ⊓ N` is
normal in `G`. -/
theorem inf_normal_of_sup_eq_top {N : Subgroup G} (hN : N.Normal)
    (hAb : ∀ a b : N, (a : G) * b = b * a) {X : Subgroup G} (hsup : X ⊔ N = ⊤) :
    (X ⊓ N).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  rw [Subgroup.eq_top_iff']
  -- It suffices that `X ⊔ N ≤ normalizer (X ⊓ N)`.
  -- `x ∈ X` normalizes `X ⊓ N`: conjugation preserves `X` (closure) and `N` (◁).
  have hconj : ∀ {g y : G}, g ∈ X → y ∈ X ⊓ N → g * y * g⁻¹ ∈ X ⊓ N := by
    intro g y hg hy
    rw [Subgroup.mem_inf] at hy ⊢
    exact ⟨mul_mem (mul_mem hg hy.1) (inv_mem hg), hN.conj_mem y hy.2 g⟩
  have hXnorm : X ≤ Subgroup.normalizer ((X ⊓ N : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj hx hh, fun hh => ?_⟩
    have hkey : x⁻¹ * (x * h * x⁻¹) * (x⁻¹)⁻¹ ∈ X ⊓ N := hconj (inv_mem hx) hh
    have : x⁻¹ * (x * h * x⁻¹) * (x⁻¹)⁻¹ = h := by group
    rwa [this] at hkey
  -- `n ∈ N` normalizes `X ⊓ N`: conjugation by `n` fixes `X ⊓ N ⊆ N` (abelian).
  have hNnorm : N ≤ Subgroup.normalizer ((X ⊓ N : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hfix : ∀ {y : G}, y ∈ N → n * y * n⁻¹ = y := by
      intro y hy
      have hnh : n * y = y * n := by simpa using hAb ⟨n, hn⟩ ⟨y, hy⟩
      rw [hnh]; group
    constructor
    · intro hh
      rw [hfix (Subgroup.mem_inf.mp hh).2]; exact hh
    · intro hh
      have hmemN : n * h * n⁻¹ ∈ N := (Subgroup.mem_inf.mp hh).2
      have hhN : h ∈ N := by
        have heq2 : h = n⁻¹ * (n * h * n⁻¹) * (n⁻¹)⁻¹ := by group
        rw [heq2]; exact hN.conj_mem _ hmemN n⁻¹
      rwa [hfix hhN] at hh
  intro g
  have hg : g ∈ X ⊔ N := hsup ▸ Subgroup.mem_top g
  -- `N` normal ⇒ `↑(X ⊔ N) = X * N`, so `g = x * n` for `x ∈ X, n ∈ N`.
  have hgmem : g ∈ (X : Set G) * (N : Set G) := by
    rw [← Subgroup.mul_normal X N]; exact hg
  obtain ⟨x, hx, n, hn, rfl⟩ := Set.mem_mul.mp hgmem
  exact mul_mem (hXnorm hx) (hNnorm hn)

/-! ### Representatives in every coset

If `N.relIndex X = N.index` (i.e. `σ = p`, `X` crosses `N` fully), then the
image `X · N / N` is all of `G ⧸ N`, so `X` meets every coset of `N`. -/

omit [DecidableEq G] in
/-- If `N.relIndex X` equals the index `N.index`, then `X` meets every coset of
`N`: for each `c : G ⧸ N` there is `s ∈ X` with `↑s = c`. -/
theorem exists_rep_of_relIndex_eq_index {N : Subgroup G} [N.Normal] {X : Subgroup G}
    (hful : N.relIndex X = N.index) (c : G ⧸ N) :
    ∃ s ∈ X, (QuotientGroup.mk s : G ⧸ N) = c := by
  have hmap : X.map (QuotientGroup.mk' N) = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    have hcard : Nat.card (X.map (QuotientGroup.mk' N)) = N.relIndex X := by
      have := Subgroup.relIndex_ker (QuotientGroup.mk' N) (K := X)
      rw [QuotientGroup.ker_mk'] at this
      rw [← this]
    rw [hcard, hful, Subgroup.index_eq_card]
  have hc : c ∈ X.map (QuotientGroup.mk' N) := hmap ▸ Subgroup.mem_top c
  obtain ⟨s, hs, hsc⟩ := Subgroup.mem_map.mp hc
  exact ⟨s, hs, by rwa [QuotientGroup.mk'_apply] at hsc⟩

/-! ### Bridge: coset equality in `↥N ⧸ K'` to a product equation

Membership in `K' = Ŝ ⊔ T̂ ⊔ Û` (subgroups of the abelian `↥N`) unfolds, via
`mem_sup3`, to a product `s₀ * t₀ * u₀`. This translates "two products lie in the
same `K'`-coset" into exactly the hypothesis shape of the distinctness lemmas. -/

/-- The abelian-group instance on `↥N` from the commutativity hypothesis. -/
@[reducible] private def commGroupN {N : Subgroup G}
    (hAb : ∀ a b : N, (a : G) * b = b * a) : CommGroup N :=
  { mul_comm := fun a b => Subtype.ext (hAb a b) }

omit [Fintype G] [DecidableEq G] in
/-- Coset equality `mk a = mk b` in `↥N ⧸ K'` (where
`K' = S.subgroupOf N ⊔ T.subgroupOf N ⊔ U.subgroupOf N`) yields a witnessing
product `(↑a)⁻¹ * ↑b = s₀ * t₀ * u₀`. -/
theorem coset_eq_imp_prod {S T U N : Subgroup G}
    (hAb : ∀ a b : N, (a : G) * b = b * a) {a b : N}
    (heq : @QuotientGroup.mk _ _
        (S.subgroupOf N ⊔ T.subgroupOf N ⊔ U.subgroupOf N) a
      = @QuotientGroup.mk _ _
        (S.subgroupOf N ⊔ T.subgroupOf N ⊔ U.subgroupOf N) b) :
    ∃ s₀, s₀ ∈ S ∧ s₀ ∈ N ∧ ∃ t₀, t₀ ∈ T ∧ t₀ ∈ N ∧ ∃ u₀, u₀ ∈ U ∧ u₀ ∈ N ∧
      (a : G)⁻¹ * (b : G) = s₀ * t₀ * u₀ := by
  letI : CommGroup N := commGroupN hAb
  rw [QuotientGroup.eq] at heq
  obtain ⟨x, hx, y, hy, z, hz, hxyz⟩ := mem_sup3.mp heq
  have hx' : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
  have hy' : (y : G) ∈ T := Subgroup.mem_subgroupOf.mp hy
  have hz' : (z : G) ∈ U := Subgroup.mem_subgroupOf.mp hz
  refine ⟨(x : G), hx', x.2, (y : G), hy', y.2, (z : G), hz', z.2, ?_⟩
  have := congrArg (Subgroup.subtype N) hxyz
  simpa using this

/-! ### Crux B: the all-crossing index bound `2p - 1 ≤ |N : K|`

When `σ = τ = υ = p`, the `1 + 2(p-1)` cosets `K`, `{sₓ⁻¹tₓ K}`, `{sᵧ⁻¹uᵧ K}`
(`x, y` nontrivial) are pairwise distinct in `↥N ⧸ K'`. -/

set_option maxHeartbeats 1000000 in
omit [DecidableEq G] in
/-- **Crux B.** With `N` abelian normal of prime index `p`, and all of
`S, T, U` crossing `N` (`N.relIndex · = p`), the subgroup
`K = (S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N)` has relative index `≥ 2p - 1` in `N`. -/
theorem cruxB {S T U : Subgroup G} (hsimp : SimpleTPP S T U)
    {N : Subgroup G} (hN : N.Normal) (hAb : ∀ a b : N, (a : G) * b = b * a)
    {p : ℕ} (hp : p.Prime) (hpN : N.index = p)
    (hσS : N.relIndex S = p) (hσT : N.relIndex T = p) (hσU : N.relIndex U = p) :
    2 * p - 1 ≤ ((S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N)).relIndex N := by
  classical
  letI : CommGroup N := commGroupN hAb
  -- `S₀, T₀, U₀` and their normality (all members cross `N`).
  have hSsupN : S ⊔ N = ⊤ := sup_eq_top_of_not_le hp hpN
    (by rw [← Subgroup.relIndex_eq_one, hσS]; exact hp.ne_one)
  have hTsupN : T ⊔ N = ⊤ := sup_eq_top_of_not_le hp hpN
    (by rw [← Subgroup.relIndex_eq_one, hσT]; exact hp.ne_one)
  have hUsupN : U ⊔ N = ⊤ := sup_eq_top_of_not_le hp hpN
    (by rw [← Subgroup.relIndex_eq_one, hσU]; exact hp.ne_one)
  have hS₀norm : (S ⊓ N).Normal := inf_normal_of_sup_eq_top hN hAb hSsupN
  have hT₀norm : (T ⊓ N).Normal := inf_normal_of_sup_eq_top hN hAb hTsupN
  have hU₀norm : (U ⊓ N).Normal := inf_normal_of_sup_eq_top hN hAb hUsupN
  -- Reps in every coset.
  have hSrep := exists_rep_of_relIndex_eq_index (X := S) (hσS.trans hpN.symm)
  have hTrep := exists_rep_of_relIndex_eq_index (X := T) (hσT.trans hpN.symm)
  have hUrep := exists_rep_of_relIndex_eq_index (X := U) (hσU.trans hpN.symm)
  -- Choice of representatives for each coset.
  set srep : (G ⧸ N) → G := fun c => (hSrep c).choose with hsrepdef
  set trep : (G ⧸ N) → G := fun c => (hTrep c).choose with htrepdef
  set urep : (G ⧸ N) → G := fun c => (hUrep c).choose with hurepdef
  have hsrepS : ∀ c, srep c ∈ S := fun c => (hSrep c).choose_spec.1
  have htrepT : ∀ c, trep c ∈ T := fun c => (hTrep c).choose_spec.1
  have hurepU : ∀ c, urep c ∈ U := fun c => (hUrep c).choose_spec.1
  have hsrepC : ∀ c, (QuotientGroup.mk (srep c) : G ⧸ N) = c := fun c => (hSrep c).choose_spec.2
  have htrepC : ∀ c, (QuotientGroup.mk (trep c) : G ⧸ N) = c := fun c => (hTrep c).choose_spec.2
  have hurepC : ∀ c, (QuotientGroup.mk (urep c) : G ⧸ N) = c := fun c => (hUrep c).choose_spec.2
  -- `srep c⁻¹ * trep c ∈ N` (both reps in coset `c`); likewise for `urep`.
  have hstN : ∀ c, (srep c)⁻¹ * trep c ∈ N := fun c => by
    rw [← QuotientGroup.eq, hsrepC, htrepC]
  have hsuN : ∀ c, (srep c)⁻¹ * urep c ∈ N := fun c => by
    rw [← QuotientGroup.eq, hsrepC, hurepC]
  -- `srep c ∉ N` for nontrivial `c` (else `c = mk (srep c) = 1`).
  have hsrepNotN : ∀ c : G ⧸ N, c ≠ 1 → srep c ∉ N := by
    intro c hc hmem
    exact hc (by rw [← hsrepC c]; exact (QuotientGroup.eq_one_iff _).mpr hmem)
  have htrepNotN : ∀ c : G ⧸ N, c ≠ 1 → trep c ∉ N := by
    intro c hc hmem
    exact hc (by rw [← htrepC c]; exact (QuotientGroup.eq_one_iff _).mpr hmem)
  -- Abbreviations for the target quotient subgroup `K'`.
  set K' : Subgroup N := S.subgroupOf N ⊔ T.subgroupOf N ⊔ U.subgroupOf N with hK'
  -- The injection from a `(2p-1)`-element index type into `↥N ⧸ K'`.
  set st : (G ⧸ N) → N := fun c => ⟨(srep c)⁻¹ * trep c, hstN c⟩ with hstdef
  set su : (G ⧸ N) → N := fun c => ⟨(srep c)⁻¹ * urep c, hsuN c⟩ with hsudef
  set φ : Option (Bool × {c : G ⧸ N // c ≠ 1}) → N ⧸ K' := fun o =>
    match o with
    | none => QuotientGroup.mk 1
    | some (false, c) => QuotientGroup.mk (st c.1)
    | some (true, c) => QuotientGroup.mk (su c.1) with hφ
  -- Coordinates of the products as `G`-elements.
  have hst_coe : ∀ c, ((st c : N) : G) = (srep c)⁻¹ * trep c := fun c => rfl
  have hsu_coe : ∀ c, ((su c : N) : G) = (srep c)⁻¹ * urep c := fun c => rfl
  -- Different cosets give products outside `N`.
  have hcoset_ne : ∀ {c c' : G ⧸ N}, c ≠ c' → (srep c)⁻¹ * srep c' ∉ N := by
    intro c c' hcc' hmem
    exact hcc' (by rw [← hsrepC c, ← hsrepC c', QuotientGroup.eq]; exact hmem)
  have hinj : Function.Injective φ := by
    rintro (_ | ⟨(_ | _), c₁⟩) (_ | ⟨(_ | _), c₂⟩) heq <;>
      simp only [hφ] at heq
    -- none vs none.
    · rfl
    -- none vs some(false, c₂): ST-family nontriviality.
    · exfalso
      obtain ⟨s₀, hs₀S, hs₀N, t₀, ht₀T, ht₀N, u₀, hu₀U, hu₀N, hprod⟩ :=
        coset_eq_imp_prod hAb heq
      rw [hst_coe] at hprod
      refine distinct_nontriv hAb hsimp (hsrepS c₂.1) (hsrepNotN c₂.1 c₂.2)
        (htrepT c₂.1) hs₀S hs₀N ht₀T ht₀N hu₀U hu₀N ?_
      simpa using hprod
    -- none vs some(true, c₂): SU-family nontriviality (permute to `(S, U, T)`).
    · exfalso
      obtain ⟨s₀, hs₀S, hs₀N, t₀, ht₀T, ht₀N, u₀, hu₀U, hu₀N, hprod⟩ :=
        coset_eq_imp_prod hAb heq
      rw [hsu_coe] at hprod
      have hcomm : t₀ * u₀ = u₀ * t₀ := by simpa using hAb ⟨t₀, ht₀N⟩ ⟨u₀, hu₀N⟩
      refine distinct_nontriv hAb hsimp.swap23 (hsrepS c₂.1) (hsrepNotN c₂.1 c₂.2)
        (hurepU c₂.1) hs₀S hs₀N hu₀U hu₀N ht₀T ht₀N ?_
      rw [show s₀ * u₀ * t₀ = s₀ * t₀ * u₀ by rw [mul_assoc, ← hcomm, ← mul_assoc]]
      simpa using hprod
    -- some(false, c₁) vs none.
    · exfalso
      obtain ⟨s₀, hs₀S, hs₀N, t₀, ht₀T, ht₀N, u₀, hu₀U, hu₀N, hprod⟩ :=
        coset_eq_imp_prod hAb heq.symm
      rw [hst_coe] at hprod
      refine distinct_nontriv hAb hsimp (hsrepS c₁.1) (hsrepNotN c₁.1 c₁.2)
        (htrepT c₁.1) hs₀S hs₀N ht₀T ht₀N hu₀U hu₀N ?_
      simpa using hprod
    -- some(false, c₁) vs some(false, c₂): ST vs ST — `distinct_within`.
    · by_cases hcc : c₁ = c₂
      · rw [hcc]
      · exfalso
        obtain ⟨s₀, hs₀S, hs₀N, t₀, ht₀T, ht₀N, u₀, hu₀U, hu₀N, hprod⟩ :=
          coset_eq_imp_prod hAb heq
        rw [hst_coe, hst_coe] at hprod
        have hcc' : c₁.1 ≠ c₂.1 := fun h => hcc (Subtype.ext h)
        refine distinct_within hN hS₀norm hU₀norm inf_le_left inf_le_right inf_le_left
          inf_le_left hsimp (hsrepS c₂.1) (hsrepS c₁.1) (hcoset_ne (Ne.symm hcc'))
          (htrepT c₂.1) (htrepT c₁.1) (Subgroup.mem_inf.mpr ⟨hs₀S, hs₀N⟩)
          (Subgroup.mem_inf.mpr ⟨ht₀T, ht₀N⟩) (Subgroup.mem_inf.mpr ⟨hu₀U, hu₀N⟩) ?_
        rw [← hprod]; group
    -- some(false, c₁) vs some(true, c₂): ST vs SU — `distinct_cross`.
    · exfalso
      obtain ⟨s₀, hs₀S, hs₀N, t₀, ht₀T, ht₀N, u₀, hu₀U, hu₀N, hprod⟩ :=
        coset_eq_imp_prod hAb heq.symm
      rw [hsu_coe, hst_coe] at hprod
      refine distinct_cross hS₀norm hU₀norm inf_le_left inf_le_left inf_le_right
        inf_le_left hsimp (hsrepS c₁.1) (htrepT c₁.1) (htrepNotN c₁.1 c₁.2)
        (hsrepS c₂.1) (hurepU c₂.1) (Subgroup.mem_inf.mpr ⟨hs₀S, hs₀N⟩)
        (Subgroup.mem_inf.mpr ⟨ht₀T, ht₀N⟩) (Subgroup.mem_inf.mpr ⟨hu₀U, hu₀N⟩) ?_
      rw [← hprod]; group
    -- some(true, c₁) vs none.
    · exfalso
      obtain ⟨s₀, hs₀S, hs₀N, t₀, ht₀T, ht₀N, u₀, hu₀U, hu₀N, hprod⟩ :=
        coset_eq_imp_prod hAb heq.symm
      rw [hsu_coe] at hprod
      have hcomm : t₀ * u₀ = u₀ * t₀ := by simpa using hAb ⟨t₀, ht₀N⟩ ⟨u₀, hu₀N⟩
      refine distinct_nontriv hAb hsimp.swap23 (hsrepS c₁.1) (hsrepNotN c₁.1 c₁.2)
        (hurepU c₁.1) hs₀S hs₀N hu₀U hu₀N ht₀T ht₀N ?_
      rw [show s₀ * u₀ * t₀ = s₀ * t₀ * u₀ by rw [mul_assoc, ← hcomm, ← mul_assoc]]
      simpa using hprod
    -- some(true, c₁) vs some(false, c₂): SU vs ST — `distinct_cross` swapped.
    · exfalso
      obtain ⟨s₀, hs₀S, hs₀N, t₀, ht₀T, ht₀N, u₀, hu₀U, hu₀N, hprod⟩ :=
        coset_eq_imp_prod hAb heq
      rw [hsu_coe, hst_coe] at hprod
      refine distinct_cross hS₀norm hU₀norm inf_le_left inf_le_left inf_le_right
        inf_le_left hsimp (hsrepS c₂.1) (htrepT c₂.1) (htrepNotN c₂.1 c₂.2)
        (hsrepS c₁.1) (hurepU c₁.1) (Subgroup.mem_inf.mpr ⟨hs₀S, hs₀N⟩)
        (Subgroup.mem_inf.mpr ⟨ht₀T, ht₀N⟩) (Subgroup.mem_inf.mpr ⟨hu₀U, hu₀N⟩) ?_
      rw [← hprod]; group
    -- some(true, c₁) vs some(true, c₂): SU vs SU — `distinct_within` `(S, U, T)`.
    · by_cases hcc : c₁ = c₂
      · rw [hcc]
      · exfalso
        obtain ⟨s₀, hs₀S, hs₀N, t₀, ht₀T, ht₀N, u₀, hu₀U, hu₀N, hprod⟩ :=
          coset_eq_imp_prod hAb heq
        rw [hsu_coe, hsu_coe] at hprod
        have hcc' : c₁.1 ≠ c₂.1 := fun h => hcc (Subtype.ext h)
        have hcomm : t₀ * u₀ = u₀ * t₀ := by simpa using hAb ⟨t₀, ht₀N⟩ ⟨u₀, hu₀N⟩
        refine distinct_within hN hS₀norm hT₀norm inf_le_left inf_le_right inf_le_left
          inf_le_left hsimp.swap23 (hsrepS c₂.1) (hsrepS c₁.1) (hcoset_ne (Ne.symm hcc'))
          (hurepU c₂.1) (hurepU c₁.1) (Subgroup.mem_inf.mpr ⟨hs₀S, hs₀N⟩)
          (Subgroup.mem_inf.mpr ⟨hu₀U, hu₀N⟩) (Subgroup.mem_inf.mpr ⟨ht₀T, ht₀N⟩) ?_
        rw [show s₀ * u₀ * t₀ = s₀ * t₀ * u₀ by rw [mul_assoc, ← hcomm, ← mul_assoc],
          ← hprod]
        group
  -- Counting: `2p - 1 = Nat.card (index type) ≤ Nat.card (↥N ⧸ K') = K.relIndex N`.
  have hcardI : Nat.card (Option (Bool × {c : G ⧸ N // c ≠ 1})) = 2 * p - 1 := by
    haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
    have hcardQ : Nat.card (G ⧸ N) = p := by rw [← Subgroup.index_eq_card, hpN]
    have hp1 : 1 ≤ p := hp.one_le
    have key : Nat.card (Option (Bool × {c : G ⧸ N // c ≠ (1 : G ⧸ N)}))
        = 2 * (Nat.card (G ⧸ N) - 1) + 1 := by
      rw [Finite.card_option, Nat.card_prod]
      congr 1
      rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
      congr 1
      rw [Nat.card_eq_fintype_card]
      have h : Fintype.card {c : G ⧸ N // c ≠ (1 : G ⧸ N)}
          = Fintype.card {c : G ⧸ N // ¬ (c = (1 : G ⧸ N))} := rfl
      rw [h, Fintype.card_subtype_compl (p := fun c : G ⧸ N => c = (1 : G ⧸ N)),
        Fintype.card_subtype_eq, Nat.card_eq_fintype_card]
    rw [key, hcardQ]; omega
  have hKK' : ((S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N)).subgroupOf N = K' := by
    rw [hK']
    rw [Subgroup.subgroupOf_sup (sup_le inf_le_right inf_le_right) inf_le_right,
      Subgroup.subgroupOf_sup inf_le_right inf_le_right,
      Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right,
      Subgroup.inf_subgroupOf_right]
  have hle := Nat.card_le_card_of_injective φ hinj
  rw [hcardI] at hle
  calc 2 * p - 1 ≤ Nat.card (N ⧸ K') := hle
    _ = K'.index := (Subgroup.index_eq_card K').symm
    _ = ((S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N)).relIndex N := by
        rw [Subgroup.relIndex, hKK']

/-! ### Crux A: the two-crossing index bound `2 ≤ |N : K|`

When two members (say `S, T`) cross `N` (`σ = τ = p`), a single nontrivial
coset produces an element of `N` outside `K`, so `K < N` and `|N : K| ≥ 2`. -/

omit [DecidableEq G] in
/-- **Crux A.** With `N` abelian normal of prime index `p` and `S, T` both
crossing `N`, the subgroup `K = (S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N)` has relative index
`≥ 2` in `N`. -/
theorem cruxA {S T U : Subgroup G} (hsimp : SimpleTPP S T U)
    {N : Subgroup G} (hN : N.Normal) (hAb : ∀ a b : N, (a : G) * b = b * a)
    {p : ℕ} (hp : p.Prime) (hpN : N.index = p)
    (hσS : N.relIndex S = p) (hσT : N.relIndex T = p) :
    2 ≤ ((S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N)).relIndex N := by
  classical
  letI : CommGroup N := commGroupN hAb
  set K : Subgroup G := (S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N) with hKdef
  -- A nontrivial coset exists (`p ≥ 2`).
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hp2 : 1 < Nat.card (G ⧸ N) := by
    rw [← Subgroup.index_eq_card, hpN]; exact hp.one_lt
  haveI : Nontrivial (G ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp hp2
  obtain ⟨c, hc⟩ := exists_ne (1 : G ⧸ N)
  -- Reps in coset `c`.
  obtain ⟨sc, hscS, hscC⟩ := exists_rep_of_relIndex_eq_index (X := S) (hσS.trans hpN.symm) c
  obtain ⟨tc, htcT, htcC⟩ := exists_rep_of_relIndex_eq_index (X := T) (hσT.trans hpN.symm) c
  have hscN : sc ∉ N := by
    intro hmem
    exact hc (by rw [← hscC]; exact (QuotientGroup.eq_one_iff _).mpr hmem)
  have hstN : sc⁻¹ * tc ∈ N := by rw [← QuotientGroup.eq, hscC, htcC]
  -- `g := sc⁻¹ * tc ∈ N` but `g ∉ K`.
  have hgK : sc⁻¹ * tc ∉ K := by
    intro hg
    have hg' : (⟨sc⁻¹ * tc, hstN⟩ : N) ∈ K.subgroupOf N := Subgroup.mem_subgroupOf.mpr hg
    have hKK' : K.subgroupOf N
        = S.subgroupOf N ⊔ T.subgroupOf N ⊔ U.subgroupOf N := by
      rw [hKdef, Subgroup.subgroupOf_sup (sup_le inf_le_right inf_le_right) inf_le_right,
        Subgroup.subgroupOf_sup inf_le_right inf_le_right,
        Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right,
        Subgroup.inf_subgroupOf_right]
    rw [hKK'] at hg'
    obtain ⟨x, hx, y, hy, z, hz, hxyz⟩ := mem_sup3.mp hg'
    have hx' : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
    have hy' : (y : G) ∈ T := Subgroup.mem_subgroupOf.mp hy
    have hz' : (z : G) ∈ U := Subgroup.mem_subgroupOf.mp hz
    have hprod : sc⁻¹ * tc = (x : G) * (y : G) * (z : G) := by
      have := congrArg (Subgroup.subtype N) hxyz
      simpa using this
    exact distinct_nontriv hAb hsimp hscS hscN htcT hx' x.2 hy' y.2 hz' z.2 hprod
  -- `K < N`, hence `K.relIndex N ≥ 2`.
  have hKleN : K ≤ N := sup_le (sup_le inf_le_right inf_le_right) inf_le_right
  have hKneN : K ≠ N := by
    intro hKN
    exact hgK (hKN ▸ hstN)
  -- `relIndex ≠ 0` (finite) and `≠ 1` (proper).
  have hcardN : Nat.card N = Nat.card K * K.relIndex N := by
    have h := Subgroup.relIndex_mul_relIndex (H := (⊥ : Subgroup G)) (K := K) (L := N)
      bot_le hKleN
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h
    rw [← h]
  have hcardN_pos : 0 < Nat.card N := Nat.card_pos
  have hrel_ne0 : K.relIndex N ≠ 0 := by
    intro h0; rw [h0, Nat.mul_zero] at hcardN; omega
  have hrel_ne1 : K.relIndex N ≠ 1 := by
    intro h1
    exact hKneN (le_antisymm hKleN (Subgroup.relIndex_eq_one.mp h1))
  omega

/-! ### The per-triple bound and the main theorem -/

/-- Pure-`ℕ` arithmetic core. With `σ, τ, υ ∈ {1, p}`, `1 ≤ p`, `1 ≤ m`, and the
case-appropriate lower bound on `m` (`m ≥ 2p-1` when all three are `p`, `m ≥ 2`
when exactly two are `p`), the inequality `(2p-1)·σ·τ·υ ≤ p³·m` holds. -/
private theorem arith_core {p m σ τ υ : ℕ} (hp : 1 ≤ p) (hm : 1 ≤ m)
    (hσ : σ = 1 ∨ σ = p) (hτ : τ = 1 ∨ τ = p) (hυ : υ = 1 ∨ υ = p)
    (h3 : σ = p → τ = p → υ = p → 2 * p - 1 ≤ m)
    (h2ST : σ = p → τ = p → 2 ≤ m) (h2SU : σ = p → υ = p → 2 ≤ m)
    (h2TU : τ = p → υ = p → 2 ≤ m) :
    (2 * p - 1) * (σ * τ * υ) ≤ p ^ 3 * m := by
  obtain ⟨d, hd⟩ : ∃ d, 2 * p = d + 1 := ⟨2 * p - 1, by omega⟩
  have hsub : 2 * p - 1 = d := by omega
  rw [hsub]
  -- Useful nonlinear facts to feed `nlinarith` (subtraction-free).
  have hp3m : p ^ 3 ≤ p ^ 3 * m := Nat.le_mul_of_pos_right _ hm
  have hkey2 : 2 * p ≤ p * p + 1 := by
    rcases Nat.lt_or_ge p 2 with h | h
    · interval_cases p
      omega
    · have : 2 * p ≤ p * p := Nat.mul_le_mul_right p h
      omega
  -- `d ≤ p²` (so `d * p ≤ p³`) and `d ≤ p³`.
  have hd2 : d ≤ p ^ 2 := by nlinarith [hkey2, hd]
  have hd3 : d ≤ p ^ 3 := by nlinarith [hd2, hp, Nat.le_self_pow (n := 3) (by norm_num) p]
  have hdp : d * p ≤ p ^ 3 := by nlinarith [hd2, hp]
  -- For the two-`p` cases: `2 · p³ ≤ m · p³` and `d · p² ≤ 2 · p³`.
  rcases hσ with hσ1 | hσp <;> rcases hτ with hτ1 | hτp <;> rcases hυ with hυ1 | hυp
  · rw [hσ1, hτ1, hυ1]; nlinarith [hd3, hp3m]
  · rw [hσ1, hτ1, hυp]; nlinarith [hdp, hp3m]
  · rw [hσ1, hτp, hυ1]; nlinarith [hdp, hp3m]
  · rw [hσ1, hτp, hυp]
    have h := h2TU hτp hυp
    have h2 : 2 * p ^ 3 ≤ m * p ^ 3 := Nat.mul_le_mul_right _ h
    nlinarith [h2, hp, hd]
  · rw [hσp, hτ1, hυ1]; nlinarith [hdp, hp3m]
  · rw [hσp, hτ1, hυp]
    have h := h2SU hσp hυp
    have h2 : 2 * p ^ 3 ≤ m * p ^ 3 := Nat.mul_le_mul_right _ h
    nlinarith [h2, hp, hd]
  · rw [hσp, hτp, hυ1]
    have h := h2ST hσp hτp
    have h2 : 2 * p ^ 3 ≤ m * p ^ 3 := Nat.mul_le_mul_right _ h
    nlinarith [h2, hp, hd]
  · rw [hσp, hτp, hυp]
    have h := h3 hσp hτp hυp
    have hmd : d ≤ m := by omega
    calc d * (p * p * p) ≤ m * (p * p * p) := Nat.mul_le_mul_right _ hmd
      _ = p ^ 3 * m := by ring

omit [Fintype G] [DecidableEq G] in
/-- The relative index `((A) ⊔ (B) ⊔ (C)).relIndex N` is invariant under
permuting `A, B, C` (the join is the same subgroup). -/
private theorem relIndex_sup_comm (A B C N : Subgroup G) :
    (A ⊔ B ⊔ C).relIndex N = (A ⊔ C ⊔ B).relIndex N := by
  rw [sup_assoc, sup_assoc, sup_comm B C]

set_option maxHeartbeats 1000000 in
omit [DecidableEq G] in
/-- **Per-triple bound.** For a subgroup TPP triple `(S, T, U)` of a group with
an abelian normal subgroup `N` of prime index `p`,
`(2p - 1) · |S| · |T| · |U| ≤ p² · |G|`. -/
theorem subgroup_tpp_size_bound {S T U : Subgroup G}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
    (hTPP : SubgroupTripleProductProperty S T U)
    {N : Subgroup G} (hN : N.Normal) (hAb : ∀ a b : N, (a : G) * b = b * a)
    {p : ℕ} (hp : p.Prime) (hpN : N.index = p) :
    (2 * p - 1) * (Nat.card S * Nat.card T * Nat.card U) ≤ p ^ 2 * Nat.card G := by
  have hsimp : SimpleTPP S T U := SubgroupTripleProductProperty.simpleTPP hTPP
  set K : Subgroup G := (S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N) with hKdef
  set σ := N.relIndex S with hσdef
  set τ := N.relIndex T with hτdef
  set υ := N.relIndex U with hυdef
  set a := Nat.card (N ⊓ S : Subgroup G) with hadef
  set b := Nat.card (N ⊓ T : Subgroup G) with hbdef
  set c := Nat.card (N ⊓ U : Subgroup G) with hcdef
  set k := Nat.card K with hkdef
  set m := K.relIndex N with hmdef
  -- Card factorizations.
  have hcardS : Nat.card S = σ * a := card_eq_relIndex_mul_card_inf N S
  have hcardT : Nat.card T = τ * b := card_eq_relIndex_mul_card_inf N T
  have hcardU : Nat.card U = υ * c := card_eq_relIndex_mul_card_inf N U
  -- Abelian product bound `a * b * c ≤ k`.
  have hNS_le : (N ⊓ S : Subgroup G) ≤ K := by
    rw [hKdef, inf_comm]; exact le_sup_left.trans le_sup_left
  have hNT_le : (N ⊓ T : Subgroup G) ≤ K := by
    rw [hKdef, inf_comm]; exact le_sup_right.trans le_sup_left
  have hNU_le : (N ⊓ U : Subgroup G) ≤ K := by
    rw [hKdef, inf_comm]; exact le_sup_right
  have habc : a * b * c ≤ k := by
    rw [hadef, hbdef, hcdef, hkdef]
    refine card_mul_card_mul_card_le_of_le_abelian hTPP hAb inf_le_right inf_le_right
      inf_le_right ?_ hNS_le hNT_le hNU_le
    exact sup_le (sup_le inf_le_right inf_le_right) inf_le_right
  -- `|N| = k * m` (Lagrange) and `|G| = p * |N|`.
  have hcardN : Nat.card N = k * m := by
    have h := Subgroup.relIndex_mul_relIndex (H := (⊥ : Subgroup G)) (K := K) (L := N)
      bot_le (sup_le (sup_le inf_le_right inf_le_right) inf_le_right)
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h
    rw [hkdef, hmdef, ← h]
  have hcardG : Nat.card G = p * Nat.card N := by
    have := Subgroup.index_mul_card N
    rw [hpN] at this; rw [← this]
  -- σ, τ, υ ∈ {1, p}.
  have hσ : σ = 1 ∨ σ = p := relIndex_eq_one_or_eq_of_prime_index hp hpN S
  have hτ : τ = 1 ∨ τ = p := relIndex_eq_one_or_eq_of_prime_index hp hpN T
  have hυ : υ = 1 ∨ υ = p := relIndex_eq_one_or_eq_of_prime_index hp hpN U
  have hk0 : 0 < k := by rw [hkdef]; exact Nat.card_pos
  have hN0 : 0 < Nat.card N := Nat.card_pos
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, Nat.mul_zero] at hcardN; omega
    · exact hpos
  -- The core index inequality `(2p - 1) * σ * τ * υ ≤ p^3 * m` via `arith_core`,
  -- supplying the crux index bounds (all permutations reduce to `cruxA`/`cruxB`).
  have hcore : (2 * p - 1) * (σ * τ * υ) ≤ p ^ 3 * m :=
    arith_core hp.one_le hm1 hσ hτ hυ
      (fun _ _ _ => by rw [hmdef, hKdef]; exact cruxB hsimp hN hAb hp hpN ‹_› ‹_› ‹_›)
      (fun hSp hTp => by rw [hmdef, hKdef]; exact cruxA hsimp hN hAb hp hpN hSp hTp)
      (fun hSp hUp => by
        rw [hmdef, hKdef, relIndex_sup_comm (S ⊓ N) (T ⊓ N) (U ⊓ N)]
        exact cruxA hsimp.swap23 hN hAb hp hpN hSp hUp)
      (fun hTp hUp => by
        have hKeq : (S ⊓ N) ⊔ (T ⊓ N) ⊔ (U ⊓ N)
            = (T ⊓ N) ⊔ (U ⊓ N) ⊔ (S ⊓ N) := by
          rw [sup_assoc, sup_comm]
        rw [hmdef, hKdef, hKeq]
        exact cruxA hsimp.cyc hN hAb hp hpN hTp hUp)
  -- Assemble.
  have hSTU : Nat.card S * Nat.card T * Nat.card U = (σ * τ * υ) * (a * b * c) := by
    rw [hcardS, hcardT, hcardU]; ring
  calc (2 * p - 1) * (Nat.card S * Nat.card T * Nat.card U)
      = (2 * p - 1) * ((σ * τ * υ) * (a * b * c)) := by rw [hSTU]
    _ ≤ (2 * p - 1) * ((σ * τ * υ) * k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ habc)
    _ = ((2 * p - 1) * (σ * τ * υ)) * k := by ring
    _ ≤ (p ^ 3 * m) * k := Nat.mul_le_mul_right _ hcore
    _ = p ^ 2 * (p * (k * m)) := by ring
    _ = p ^ 2 * Nat.card G := by rw [← hcardN, ← hcardG]

/-- **Murthy's prime-index bound (Theorem 4.1).** If `G` is a finite group with
an abelian normal subgroup `N` of prime index `p`, then the subgroup TPP
capacity satisfies `(2p - 1) · β₀(G) ≤ p² · |G|`, i.e. `ρ₀(G) ≤ p²/(2p-1)`.

For `p = 2` (dihedral-type groups) this is `ρ₀(G) ≤ 4/3`. -/
theorem stppCapacity_bound {N : Subgroup G} (hN : N.Normal)
    (hAb : ∀ a b : N, (a : G) * b = b * a) {p : ℕ} (hp : p.Prime)
    (hpN : N.index = p) :
    (2 * p - 1) * stppCapacity G ≤ p ^ 2 * Nat.card G := by
  classical
  -- The capacity is the sup of a per-triple quantity over the finite type of
  -- subgroup triples; pick the maximizing triple.
  obtain ⟨⟨S, T, U⟩, -, hmax⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Subgroup G × Subgroup G × Subgroup G))
      ⟨(⊥, ⊥, ⊥), Finset.mem_univ _⟩
      (fun q =>
        if TripleProductProperty (q.1 : Set G).toFinset (q.2.1 : Set G).toFinset
            (q.2.2 : Set G).toFinset
        then Nat.card q.1 * Nat.card q.2.1 * Nat.card q.2.2
        else 0)
  rw [stppCapacity, hmax]
  by_cases hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset
  · simp only [hTPP, if_true]
    exact subgroup_tpp_size_bound (S := S) (T := T) (U := U) hTPP hN hAb hp hpN
  · simp only [hTPP, if_false, Nat.mul_zero]
    exact Nat.zero_le _

/-- **Dihedral-type case `p = 2`.** If `G` has an abelian subgroup `N` of index
`2` (automatically normal), then `3 · β₀(G) ≤ 4 · |G|`, i.e. `ρ₀(G) ≤ 4/3`.
This is Murthy's bound for dihedral groups (Hedtke–Murthy Conjecture 7.5). -/
theorem stppCapacity_bound_index_two {N : Subgroup G}
    (hAb : ∀ a b : N, (a : G) * b = b * a) (hpN : N.index = 2) :
    3 * stppCapacity G ≤ 4 * Nat.card G := by
  have hN : N.Normal := Subgroup.normal_of_index_eq_two hpN
  have h := stppCapacity_bound hN hAb (p := 2) (by norm_num) hpN
  have e1 : (2 * 2 - 1) = 3 := by norm_num
  have e2 : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [e1, e2] at h
  exact h

/-- **Trivial lower bound `|G| ≤ β₀(G)`**, witnessed by the subgroup triple
`(⊤, ⊥, ⊥)`. -/
theorem card_le_stppCapacity : Nat.card G ≤ stppCapacity G := by
  classical
  -- The triple `(⊤, ⊥, ⊥)` has the subgroup TPP and value `|G|`.
  have hTPP : TripleProductProperty ((⊤ : Subgroup G) : Set G).toFinset
      ((⊥ : Subgroup G) : Set G).toFinset ((⊥ : Subgroup G) : Set G).toFinset := by
    intro s _ s' _ t ht t' ht' u hu u' hu' heq
    simp only [Subgroup.coe_bot, Set.toFinset_singleton, Finset.mem_singleton] at ht ht' hu hu'
    subst ht ht' hu hu'
    refine ⟨?_, rfl, rfl⟩
    have : s'⁻¹ * s = 1 := by simpa using heq
    exact (inv_mul_eq_one.mp this).symm
  have hmem :
      (if TripleProductProperty ((⊤ : Subgroup G) : Set G).toFinset
          ((⊥ : Subgroup G) : Set G).toFinset ((⊥ : Subgroup G) : Set G).toFinset
        then Nat.card (⊤ : Subgroup G) * Nat.card (⊥ : Subgroup G) *
          Nat.card (⊥ : Subgroup G)
        else 0) ≤ stppCapacity G := by
    rw [stppCapacity]
    exact Finset.le_sup
      (f := fun q =>
        if TripleProductProperty (q.1 : Set G).toFinset (q.2.1 : Set G).toFinset
            (q.2.2 : Set G).toFinset
        then Nat.card q.1 * Nat.card q.2.1 * Nat.card q.2.2 else 0)
      (Finset.mem_univ ((⊤, ⊥, ⊥) : Subgroup G × Subgroup G × Subgroup G))
  rw [if_pos hTPP, Subgroup.card_top, Subgroup.card_bot] at hmem
  simpa using hmem

/-- **Murthy Corollary 4.3.** If `G` is a finite `p`-group with an abelian
subgroup `N` of index `p`, then `β₀(G) = |G|`, i.e. `ρ₀(G) = 1`. -/
theorem stppCapacity_eq_card_of_pgroup {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    {N : Subgroup G} (hAb : ∀ a b : N, (a : G) * b = b * a) (hpN : N.index = p) :
    stppCapacity G = Nat.card G := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  -- `|G| = p ^ n` with `n ≥ 1`.
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hG
  have hpn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hn
      have hdvd : N.index ∣ Nat.card G := Subgroup.index_dvd_card N
      rw [hn, hpN] at hdvd
      exact hp.one_lt.ne' (Nat.le_antisymm (Nat.le_of_dvd one_pos hdvd) hp.one_le)
    · exact hpos
  -- `N` is normal (index = the unique prime `p = minFac`).
  have hminFac : (Nat.card G).minFac = p := by rw [hn]; exact hp.pow_minFac (by omega)
  have hN : N.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hpN, hminFac])
  refine le_antisymm ?_ card_le_stppCapacity
  -- Pick the maximizing subgroup triple.
  obtain ⟨⟨S, T, U⟩, -, hmax⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Subgroup G × Subgroup G × Subgroup G))
      ⟨(⊥, ⊥, ⊥), Finset.mem_univ _⟩
      (fun q =>
        if TripleProductProperty (q.1 : Set G).toFinset (q.2.1 : Set G).toFinset
            (q.2.2 : Set G).toFinset
        then Nat.card q.1 * Nat.card q.2.1 * Nat.card q.2.2
        else 0)
  rw [stppCapacity, hmax]
  by_cases hTPP : TripleProductProperty (S : Set G).toFinset (T : Set G).toFinset
      (U : Set G).toFinset
  · simp only [hTPP, if_true]
    -- Each subgroup order is a power of `p`; so is the product.
    have hdvdS : Nat.card S ∣ p ^ n := hn ▸ Subgroup.card_subgroup_dvd_card S
    have hdvdT : Nat.card T ∣ p ^ n := hn ▸ Subgroup.card_subgroup_dvd_card T
    have hdvdU : Nat.card U ∣ p ^ n := hn ▸ Subgroup.card_subgroup_dvd_card U
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp hdvdS
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvdT
    obtain ⟨l, _, hl⟩ := (Nat.dvd_prime_pow hp).mp hdvdU
    have hprod : Nat.card S * Nat.card T * Nat.card U = p ^ (i + j + l) := by
      rw [hi, hj, hl, ← pow_add, ← pow_add]
    -- The size bound `(2p-1)·pᵏ ≤ p²·|G| = p^(n+2)` forces `k ≤ n`.
    have hbound := subgroup_tpp_size_bound (S := S) (T := T) (U := U) hTPP hN hAb hp hpN
    rw [hprod, hn] at hbound
    rw [hprod, hn]
    -- Suppose `i + j + l > n`; derive a contradiction.
    by_contra hlt
    have hlt' : p ^ n < p ^ (i + j + l) := not_le.mp hlt
    have hk : n + 1 ≤ i + j + l := by
      have : n < i + j + l := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt'
      omega
    have h1 : p ^ (n + 1) ≤ p ^ (i + j + l) := Nat.pow_le_pow_right hp.one_le hk
    -- `(2p-1) ≥ p+1` (as `p ≥ 2`), so `(2p-1)·p^(i+j+l) ≥ (p+1)·p^(n+1) > p^(n+2)`.
    have hple : p + 1 ≤ 2 * p - 1 := by omega
    have h2 : (p + 1) * p ^ (n + 1) ≤ (2 * p - 1) * p ^ (i + j + l) :=
      Nat.mul_le_mul hple h1
    have h3 : p ^ (n + 2) < (p + 1) * p ^ (n + 1) := by
      have : (p + 1) * p ^ (n + 1) = p ^ (n + 2) + p ^ (n + 1) := by ring
      have hpos : 0 < p ^ (n + 1) := pow_pos hp.pos _
      omega
    -- `p^2 * p^n = p^(n+2)`.
    have he : p ^ 2 * p ^ n = p ^ (n + 2) := by rw [← pow_add]; ring_nf
    rw [he] at hbound
    omega
  · -- The maximizing triple is not TPP ⇒ value `0 ≤ |G|`.
    simp only [hTPP, if_false]
    exact Nat.zero_le _

end Xlib.MurthyPrimeIndex
