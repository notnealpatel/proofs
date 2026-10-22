/-
# Cameron–Dey, Theorem 8: abelian normal Hall subgroups and strong domination

## Source

Peter J. Cameron and Hiranya Kishore Dey, "On the order sequence of a group",
arXiv:2310.06516 (Electron. J. Combin. 32(2) (2025) #P2.9).  Section 2,
Theorem `t:extension` (Theorem 8 of the published version).

Definition (Section 2, verbatim): "For groups $G$ and $H$ of the same order,
we say that $\os(G)$ *strongly dominates* $\os(H)$ if there is a bijection
$f:G\to H$ such that $o(f(g))\mid o(g)$ for all $g\in G$."

Theorem (verbatim): "Let $G$ and $H$ be groups of coprime order, and suppose
that $G$ is abelian. Let $K$ be any extension of $G$ by $H$. Then
$\os(G\times H)=\os(G)\os(H)$ strongly dominates $\os(K)$."

The proof uses a Schur–Zassenhaus complement and the identity
$(gh)^{o(g)o(h)} = 1$: the conjugates $h^i g h^{-i}$ lie in the abelian
normal subgroup and all have order $o(g)$. The companion
`CameronDeyQuestion31Refutation` gives a counterexample without abelianness.

## Formalization

* `CameronDey.StronglyDominates G H`: a bijection `G ≃ H` whose image orders
  divide source orders (the same-order condition is implied by the bijection).
* `CameronDey.thm8_subgroup`: the theorem with the extension presented as a
  normal subgroup `N ≤ K` (playing `G`) and the quotient `K ⧸ N` (playing `H`).
* `CameronDey.thm8`: the theorem for an abstract extension
  `1 → G → K → H → 1` given by an injective `ι : G →* K`, a surjective
  `π : K →* H` with `ι.range = π.ker`.

No finiteness hypothesis is needed in Lean: Mathlib's Schur–Zassenhaus
theorem and `orderOf_dvd_natCard` hold with the `Nat.card = 0` convention, so
the statements below specialise to the paper's finite case.
-/
import Mathlib

set_option autoImplicit false

namespace CameronDey

/-- Cameron–Dey: for groups `G` and `H`, `os(G)` *strongly dominates* `os(H)`
if there is a bijection `f : G → H` with `o(f g) ∣ o(g)` for every `g : G`. -/
def StronglyDominates (G H : Type*) [Group G] [Group H] : Prop :=
  ∃ f : G ≃ H, ∀ g : G, orderOf (f g) ∣ orderOf g

/-- Every group strongly dominates itself (identity bijection). -/
theorem StronglyDominates.refl (G : Type*) [Group G] : StronglyDominates G G :=
  ⟨Equiv.refl G, fun _ => dvd_rfl⟩

/-- Strong domination is invariant under replacing the dominating group by an
isomorphic copy. -/
theorem StronglyDominates.of_mulEquiv_left {G G' H : Type*} [Group G] [Group G']
    [Group H] (e : G' ≃* G) (hGH : StronglyDominates G H) : StronglyDominates G' H := by
  obtain ⟨f, hf⟩ := hGH
  refine ⟨e.toEquiv.trans f, fun g => ?_⟩
  have hg : orderOf (e g) = orderOf g := MulEquiv.orderOf_eq e g
  simpa only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, hg]
    using hf (e g)

/-- `ℤ/2 × ℤ/2` does not strongly dominate `ℤ/4`
(every element of the Klein group has order dividing `2`, but `ℤ/4` has an
element of order `4`). -/
example : ¬ StronglyDominates (Multiplicative (ZMod 2 × ZMod 2)) (Multiplicative (ZMod 4)) := by
  rintro ⟨f, hf⟩
  have h2 : ∀ g : Multiplicative (ZMod 2 × ZMod 2), orderOf g ∣ 2 := fun g =>
    orderOf_dvd_of_pow_eq_one (by revert g; decide)
  have h4 : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hdvd := (hf (f.symm (Multiplicative.ofAdd 1))).trans (h2 _)
  rw [Equiv.apply_symm_apply, h4] at hdvd
  exact absurd (Nat.le_of_dvd two_pos hdvd) (by norm_num)

/-- If `g` lies in an abelian normal subgroup
`N`, then for every `k` we have `(g h)^k = P h^k` with `P ∈ N` and
`P ^ o(g) = 1`; namely `P = ∏_{i<k} h^i g h^{-i}`. -/
theorem exists_pow_mul_eq {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (hab : ∀ a b : N, a * b = b * a) {g : K} (hg : g ∈ N) (h : K) (k : ℕ) :
    ∃ P ∈ N, P ^ orderOf g = 1 ∧ (g * h) ^ k = P * h ^ k := by
  induction k with
  | zero => exact ⟨1, N.one_mem, one_pow _, by simp⟩
  | succ k ih =>
    obtain ⟨P, hPN, hPm, hPk⟩ := ih
    set c : K := h ^ k * g * (h ^ k)⁻¹ with hc_def
    have hcN : c ∈ N := Subgroup.Normal.conj_mem inferInstance g hg (h ^ k)
    have hcm : c ^ orderOf g = 1 := by
      rw [hc_def, conj_pow, pow_orderOf_eq_one]; group
    have hcomm : Commute P c := congrArg Subtype.val (hab ⟨P, hPN⟩ ⟨c, hcN⟩)
    refine ⟨P * c, N.mul_mem hPN hcN, by rw [hcomm.mul_pow, hPm, hcm, one_mul], ?_⟩
    rw [pow_succ, hPk, hc_def]
    group

/-- If `g` lies in an abelian normal subgroup, then `o(g h) ∣ o(g) o(h)` for every
`h`. -/
theorem orderOf_mul_dvd_mul_orderOf {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (hab : ∀ a b : N, a * b = b * a) {g : K} (hg : g ∈ N) (h : K) :
    orderOf (g * h) ∣ orderOf g * orderOf h := by
  obtain ⟨P, -, hPm, hPk⟩ := exists_pow_mul_eq N hab hg h (orderOf h)
  apply orderOf_dvd_of_pow_eq_one
  rw [mul_comm, pow_mul, hPk, pow_orderOf_eq_one, mul_one, hPm]

/-- **Cameron–Dey, Theorem 8 (subgroup form).**  Let `N` be an abelian normal
subgroup of `K` with `gcd(|N|, [K : N]) = 1`.  Then `os(N × K/N)` strongly
dominates `os(K)`: there is a bijection `f : N × (K ⧸ N) ≃ K` with
`o(f x) ∣ o(x)` for all `x`.  (arXiv:2310.06516, Theorem `t:extension`.) -/
theorem thm8_subgroup {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (hab : ∀ a b : N, a * b = b * a) (hcop : Nat.Coprime (Nat.card N) N.index) :
    StronglyDominates (N × (K ⧸ N)) K := by
  obtain ⟨H, hc⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  let e : K ⧸ N ≃* H := hc.symm.QuotientMulEquiv
  let f : N × (K ⧸ N) ≃ K :=
    (Equiv.prodCongr (Equiv.refl N) e.toEquiv).trans (Equiv.ofBijective _ hc)
  refine ⟨f, fun x => ?_⟩
  have hfx : f x = (x.1 : K) * (e x.2 : K) := rfl
  have h1 : orderOf (x.1 : K) ∣ Nat.card N := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (e x.2 : K) ∣ N.index := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.index]
    exact orderOf_dvd_natCard _
  have hcop' : Nat.Coprime (orderOf (x.1 : K)) (orderOf (e x.2 : K)) :=
    Nat.Coprime.of_dvd h1 h2 hcop
  rw [hfx, Prod.orderOf, ← Subgroup.orderOf_coe x.1, ← MulEquiv.orderOf_eq e x.2,
    ← Subgroup.orderOf_coe (e x.2), hcop'.lcm_eq_mul]
  exact orderOf_mul_dvd_mul_orderOf N hab x.1.2 _

/-- **Cameron–Dey, Theorem 8.**  Let `G` and `H` be groups of coprime order
with `G` abelian, and let `K` be an extension of `G` by `H`, i.e. there are an
injective `ι : G →* K` and a surjective `π : K →* H` with `ι.range = π.ker`.
Then `os(G × H)` strongly dominates `os(K)`.
(arXiv:2310.06516, Theorem `t:extension`.) -/
theorem thm8 {G H K : Type*} [CommGroup G] [Group H] [Group K]
    (ι : G →* K) (π : K →* H) (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hex : ι.range = π.ker) (hcop : Nat.Coprime (Nat.card G) (Nat.card H)) :
    StronglyDominates (G × H) K := by
  let eG : G ≃* π.ker := (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hex)
  let eH : H ≃* K ⧸ π.ker := (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm
  have hab : ∀ a b : π.ker, a * b = b * a := by
    intro a b
    exact eG.symm.injective (by rw [map_mul, map_mul, mul_comm])
  have hcardN : Nat.card π.ker = Nat.card G := (Nat.card_congr eG.toEquiv).symm
  have hindex : π.ker.index = Nat.card H := by
    rw [Subgroup.index]
    exact (Nat.card_congr eH.toEquiv).symm
  have hcopN : Nat.Coprime (Nat.card π.ker) π.ker.index := by
    rw [hcardN, hindex]
    exact hcop
  exact (thm8_subgroup π.ker hab hcopN).of_mulEquiv_left (MulEquiv.prodCongr eG eH)

/-- Non-vacuity of `thm8`: the split extension `ℤ/3 → ℤ/3 × ℤ/2 → ℤ/2` satisfies
every hypothesis jointly. -/
example : StronglyDominates (Multiplicative (ZMod 3) × Multiplicative (ZMod 2))
    (Multiplicative (ZMod 3) × Multiplicative (ZMod 2)) := by
  refine thm8 (MonoidHom.inl _ _) (MonoidHom.snd _ _) ?_ ?_ ?_ ?_
  · exact fun a b hab => congrArg Prod.fst hab
  · exact fun b => ⟨(1, b), rfl⟩
  · rw [MonoidHom.ker_snd]
    ext x
    simp [Subgroup.mem_prod, Prod.ext_iff, eq_comm]
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide

/-- Non-vacuity of `thm8_subgroup` with nonabelian `K`: `A₃ ◁ S₃`
is abelian of order `3` and index `2`. -/
example : StronglyDominates (alternatingGroup (Fin 3) × (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)))
    (Equiv.Perm (Fin 3)) := by
  refine thm8_subgroup _ (by decide) ?_
  rw [alternatingGroup.index_eq_two, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

end CameronDey
