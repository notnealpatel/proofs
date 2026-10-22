/-
# Complete mappings of `ℤ/2 × ℤ/2k`: the base family of Hall's abelian theorem

## Source

* arXiv:1710.09321, D. López-Aguayo and S. López-Aguayo, *Antiautomorphisms and
  biantiautomorphisms of some finite abelian groups*, Sections 2–3.  The paper's notion
  (Definition 2.1), verbatim:

  > Let $G$ be an abelian group and let $f: G \rightarrow G$ be any function. We say that
  > $f$ is an \emph{antimorphism} if the map $id_{G}-f$ is injective. We say that an
  > antimorphism $f$ is an \emph{antiautomorphism} of $G$ if $f$ is a bijection.

  The paper's summary theorem (Theorem 3.8, a *partial* classification) covers groups
  without involutions, groups with exactly one involution, and `ℤ_{2^m}^n` (`n ≥ 2`);
  Proposition 3.2 exhibits, by computer, an antiautomorphism of `ℤ_2 ⊕ ℤ_4`, and the
  paper closes with Questions 1–2.  Mixed-exponent 2-groups such as `ℤ_2 ⊕ ℤ_{2^m}`
  (`m ≥ 3`) are left uncovered by the paper.

* The full classification is classical: M. Hall Jr., *A combinatorial problem on abelian
  groups*, Proc. AMS 3 (1952) 584–587 — a finite abelian group has a complete mapping iff
  it does not have exactly one element of order `2`.

## Claim formalized (date 2026-10-21)

For every `k ≥ 1`, the group `ℤ/2 × ℤ/2k` admits a complete mapping in the sense of
`Candidates.HallPaigeNecessity.IsCompleteMapping` (a bijection `φ` with `g ↦ g * φ g`
bijective), and an antiautomorphism in the paper's sense.  Complete mappings are closed
under direct products and transport along group isomorphisms; hence
`ℤ/2 × ℤ/2k × H` has a complete mapping for every finite group `H` of odd order.

Status: known (a special case of Hall 1952; `k = 2` is the paper's Prop 3.2).  The
paper itself does not prove the general family.  The explicit construction below is
not taken from a source.

## Construction

Write `n = 2k` and elements as `(t, x)` with `t < 2`, `x < n` (via `ZMod.val`).  Let
`σ(x) = x` for `x < k`, `σ(x) = x + 1` for `k ≤ x < n - 1`, `σ(n - 1) = k` (a
permutation of `ℤ/n`), and let the label `e(x) ∈ {0,1}` be `[x mod k ≥ k/2]` for `k`
even and `[x ≥ k]` for `k` odd.  With `s = t + e(x) (mod 2)` the complete mapping is
`φ(t, x) = (s, σ(x) + s k)`; then `(t, x) * φ(t, x) = (e(x), x + σ(x) + s k)`.
Modulo `k`, `x + σ(x)` is `2a` on the lower half and `2a + 1` on the upper half
(`a = x mod k`), so the label `e` separates the two preimages of every residue.
Both injectivity statements reduce to linear arithmetic over `ℕ` (`omega`).
-/
import Mathlib
import Sorry.GroupCount.HallPaigeNecessity

set_option autoImplicit false

namespace Candidates.HallCompleteMappingZ2Z2k

open Candidates.HallPaigeNecessity

/-! ## Arithmetic layer over `ℕ` -/

/-- Reduction of `v < 2n` modulo `n` by one conditional subtraction. -/
def red (n v : ℕ) : ℕ := if v < n then v else v - n

/-- The permutation `σ` of `[0, 2k)`: identity on the lower half, a cyclic shift
`k + a ↦ k + ((a + 1) mod k)` on the upper half. -/
def sig (k x : ℕ) : ℕ := if x < k then x else if x + 1 < 2 * k then x + 1 else k

/-- The label `e(x) ∈ {0, 1}`: for `k` even, `[x mod k ≥ k/2]`; for `k` odd, `[x ≥ k]`. -/
def lab (k x : ℕ) : ℕ :=
  if k % 2 = 0 then
    (if x < k then (if x < k / 2 then 0 else 1) else (if x < k + k / 2 then 0 else 1))
  else (if x < k then 0 else 1)

/-- First coordinate of `φ(t, x)`: `s = t + e(x) (mod 2)`. -/
def sw (k t x : ℕ) : ℕ := if t = lab k x then 0 else 1

/-- Second coordinate of `φ(t, x)`: `σ(x) + s k (mod 2k)`. -/
def snd (k t x : ℕ) : ℕ := if sw k t x = 0 then sig k x else red (2 * k) (sig k x + k)

/-- `sig 2` on `[0, 4)` is `0, 1, 3, 2`. -/
example : (sig 2 0, sig 2 1, sig 2 2, sig 2 3) = (0, 1, 3, 2) := rfl

/-- `lab 2` on `[0, 4)` is `0, 1, 0, 1`; `lab 3` on `[0, 6)` is `0, 0, 0, 1, 1, 1`. -/
example : (lab 2 0, lab 2 1, lab 2 2, lab 2 3) = (0, 1, 0, 1) ∧
    (lab 3 0, lab 3 2, lab 3 3, lab 3 5) = (0, 0, 1, 1) := ⟨rfl, rfl⟩

/-- The label takes values in `{0, 1}`. -/
theorem lab_lt (k x : ℕ) : lab k x < 2 := by
  unfold lab; split_ifs <;> omega

/-- `σ` is injective on `[0, 2k)`. -/
theorem sig_inj (k x x' : ℕ) (hx : x < 2 * k) (hx' : x' < 2 * k) (h : sig k x = sig k x') :
    x = x' := by
  unfold sig at h; split_ifs at h <;> omega

/-- `σ` maps `[0, 2k)` into itself. -/
theorem sig_lt (k x : ℕ) (hx : x < 2 * k) : sig k x < 2 * k := by
  unfold sig; split_ifs <;> omega

/-- `snd` differs from `σ` by `0`, `-k` or `+k`. -/
theorem snd_cases (k t x : ℕ) (hx : x < 2 * k) :
    snd k t x = sig k x ∨ snd k t x + k = sig k x ∨ snd k t x = sig k x + k := by
  have := sig_lt k x hx
  unfold snd red; split_ifs <;> omega

/-- `red n v` is `v` or `v - n`. -/
theorem red_cases (n v : ℕ) : red n v = v ∨ red n v + n = v := by
  unfold red; split_ifs <;> omega

/-- Key separation lemma: if `x + σ(x) ≡ x' + σ(x') (mod k)` (expressed as a difference
in `{0, ±k, ±2k, ±3k}`) and the labels agree, then `x = x'`. -/
theorem lab_collision (k x x' : ℕ) (hx : x < 2 * k) (hx' : x' < 2 * k)
    (he : lab k x = lab k x')
    (hz : x + sig k x = x' + sig k x' ∨ x + sig k x = x' + sig k x' + k ∨
      x + sig k x + k = x' + sig k x' ∨ x + sig k x = x' + sig k x' + 2 * k ∨
      x + sig k x + 2 * k = x' + sig k x' ∨ x + sig k x = x' + sig k x' + 3 * k ∨
      x + sig k x + 3 * k = x' + sig k x') : x = x' := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · have h2 : 2 * m % 2 = 0 := Nat.mul_mod_right 2 m
    have h3 : 2 * m / 2 = m := by omega
    simp only [lab, h2, h3, if_true] at he
    unfold sig at hz
    split_ifs at he hz <;> omega
  · have h2 : (2 * m + 1) % 2 = 1 := by omega
    simp only [lab, h2, one_ne_zero, if_false] at he
    unfold sig at hz
    split_ifs at he hz <;> omega

/-- `sw` takes values in `{0, 1}`. -/
theorem sw_lt (k t x : ℕ) : sw k t x < 2 := by
  unfold sw; split_ifs <;> omega

/-- `snd` maps into `[0, 2k)`. -/
theorem snd_lt (k t x : ℕ) (hx : x < 2 * k) : snd k t x < 2 * k := by
  have := sig_lt k x hx
  unfold snd red; split_ifs <;> omega

/-- First coordinate of `(t, x) * φ(t, x)` is the label: `t + s ≡ e(x) (mod 2)`. -/
theorem add_sw_mod_two (k t x : ℕ) (ht : t < 2) : (t + sw k t x) % 2 = lab k x := by
  have := lab_lt k x
  unfold sw; split_ifs <;> omega

/-- `φ` is injective at the level of representatives. -/
theorem phi_inj (k t x t' x' : ℕ) (ht : t < 2) (hx : x < 2 * k) (ht' : t' < 2)
    (hx' : x' < 2 * k) (h1 : sw k t x = sw k t' x') (h2 : snd k t x = snd k t' x') :
    t = t' ∧ x = x' := by
  have hs := sig_lt k x hx
  have hs' := sig_lt k x' hx'
  have hsig : sig k x = sig k x' := by
    unfold snd red at h2
    rw [h1] at h2
    split_ifs at h2 <;> omega
  have hxx : x = x' := sig_inj k x x' hx hx' hsig
  subst hxx
  have hl := lab_lt k x
  unfold sw at h1
  refine ⟨?_, rfl⟩
  split_ifs at h1 <;> omega

/-- Distinct `t ≠ t'` give complementary switches `s`. -/
theorem sw_ne_of_ne (k t t' x : ℕ) (ht : t < 2) (ht' : t' < 2) (h : t ≠ t') :
    sw k t x + sw k t' x = 1 := by
  have := lab_lt k x
  unfold sw; split_ifs <;> omega

/-- `g ↦ g * φ g` is injective at the level of representatives. -/
theorem psi_inj (k t x t' x' : ℕ) (ht : t < 2) (hx : x < 2 * k) (ht' : t' < 2)
    (hx' : x' < 2 * k) (h1 : (t + sw k t x) % 2 = (t' + sw k t' x') % 2)
    (h2 : red (2 * k) (x + snd k t x) = red (2 * k) (x' + snd k t' x')) :
    t = t' ∧ x = x' := by
  rw [add_sw_mod_two k t x ht, add_sw_mod_two k t' x' ht'] at h1
  have hs := sig_lt k x hx
  have hs' := sig_lt k x' hx'
  have hsx := snd_lt k t x hx
  have hsx' := snd_lt k t' x' hx'
  have hxx : x = x' := by
    refine lab_collision k x x' hx hx' h1 ?_
    rcases snd_cases k t x hx with ha | ha | ha <;>
    rcases snd_cases k t' x' hx' with hb | hb | hb <;>
    rcases red_cases (2 * k) (x + snd k t x) with hc | hc <;>
    rcases red_cases (2 * k) (x' + snd k t' x') with hd | hd <;> omega
  subst hxx
  refine ⟨?_, rfl⟩
  by_contra hne
  have hsum := sw_ne_of_ne k t t' x ht ht' hne
  have hsw := sw_lt k t x
  unfold snd at h2 hsx hsx'
  unfold red at h2 hsx hsx'
  split_ifs at h2 hsx hsx' <;> omega

/-- For `v < 2n`, `v % n = red n v`. -/
theorem mod_eq_red (n v : ℕ) (hv : v < 2 * n) : v % n = red n v := by
  unfold red
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## The complete mapping of `ℤ/2 × ℤ/2k` -/

/-- The explicit complete mapping `φ(t, x) = (s, σ(x) + s k)` of `ℤ/2 × ℤ/2k`, written
multiplicatively. -/
def phiZ (k : ℕ) (g : Multiplicative (ZMod 2 × ZMod (2 * k))) :
    Multiplicative (ZMod 2 × ZMod (2 * k)) :=
  Multiplicative.ofAdd ((sw k g.toAdd.1.val g.toAdd.2.val : ZMod 2),
    (snd k g.toAdd.1.val g.toAdd.2.val : ZMod (2 * k)))

/-- Ground truth: `phiZ 2` is a complete mapping of `ℤ/2 × ℤ/4` (paper, Prop 3.2). -/
example : IsCompleteMapping (phiZ 2) := by
  unfold IsCompleteMapping
  decide

/-- Ground truth: `phiZ 1` is a complete mapping of `ℤ/2 × ℤ/2` (paper, Prop 2.6 with r = 2). -/
example : IsCompleteMapping (phiZ 1) := by
  unfold IsCompleteMapping
  decide

/-- `phiZ k` is injective for `k ≥ 1`. -/
theorem phiZ_injective (k : ℕ) (hk : 0 < k) : Function.Injective (phiZ k) := by
  haveI : NeZero (2 * k) := ⟨by omega⟩
  intro g g' h
  have h1 := congrArg (fun p => (Multiplicative.toAdd p).1.val) h
  have h2 := congrArg (fun p => (Multiplicative.toAdd p).2.val) h
  simp only [phiZ, toAdd_ofAdd] at h1 h2
  rw [ZMod.val_natCast_of_lt (sw_lt _ _ _), ZMod.val_natCast_of_lt (sw_lt _ _ _)] at h1
  rw [ZMod.val_natCast_of_lt (snd_lt _ _ _ (ZMod.val_lt _)),
    ZMod.val_natCast_of_lt (snd_lt _ _ _ (ZMod.val_lt _))] at h2
  obtain ⟨ht, hx⟩ := phi_inj k _ _ _ _ (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (ZMod.val_lt _) h1 h2
  apply Multiplicative.toAdd.injective
  exact Prod.ext (ZMod.val_injective _ ht) (ZMod.val_injective _ hx)

/-- `g ↦ g * phiZ k g` is injective for `k ≥ 1`. -/
theorem mul_phiZ_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun g => g * phiZ k g) := by
  haveI : NeZero (2 * k) := ⟨by omega⟩
  intro g g' h
  have h1 := congrArg (fun p => (Multiplicative.toAdd p).1.val) h
  have h2 := congrArg (fun p => (Multiplicative.toAdd p).2.val) h
  simp only [phiZ, toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, ZMod.val_add] at h1 h2
  rw [ZMod.val_natCast_of_lt (sw_lt _ _ _), ZMod.val_natCast_of_lt (sw_lt _ _ _)] at h1
  rw [ZMod.val_natCast_of_lt (snd_lt _ _ _ (ZMod.val_lt _)),
    ZMod.val_natCast_of_lt (snd_lt _ _ _ (ZMod.val_lt _))] at h2
  set t := (Multiplicative.toAdd g).1.val with ht_def
  set x := (Multiplicative.toAdd g).2.val with hx_def
  set t' := (Multiplicative.toAdd g').1.val with ht'_def
  set x' := (Multiplicative.toAdd g').2.val with hx'_def
  have ht : t < 2 := ZMod.val_lt _
  have ht' : t' < 2 := ZMod.val_lt _
  have hx : x < 2 * k := ZMod.val_lt _
  have hx' : x' < 2 * k := ZMod.val_lt _
  rw [mod_eq_red _ _ (by have := snd_lt k t x hx; omega),
    mod_eq_red _ _ (by have := snd_lt k t' x' hx'; omega)] at h2
  obtain ⟨htt, hxx⟩ := psi_inj k t x t' x' ht hx ht' hx' h1 h2
  apply Multiplicative.toAdd.injective
  exact Prod.ext (ZMod.val_injective _ htt) (ZMod.val_injective _ hxx)

/-- `phiZ k` is a complete mapping of `ℤ/2 × ℤ/2k` for `k ≥ 1`. -/
theorem isCompleteMapping_phiZ (k : ℕ) (hk : 0 < k) : IsCompleteMapping (phiZ k) := by
  haveI : NeZero (2 * k) := ⟨by omega⟩
  exact ⟨Finite.injective_iff_bijective.mp (phiZ_injective k hk),
    Finite.injective_iff_bijective.mp (mul_phiZ_injective k hk)⟩

/-- **Main theorem.** For every `k ≥ 1`, the group `ℤ/2 × ℤ/2k` admits a complete mapping
(a special case of M. Hall, Proc. AMS 3 (1952); `k = 2` is Prop 3.2 of
arXiv:1710.09321). -/
theorem exists_isCompleteMapping_zmod_two_prod (k : ℕ) (hk : 0 < k) :
    ∃ φ : Multiplicative (ZMod 2 × ZMod (2 * k)) → Multiplicative (ZMod 2 × ZMod (2 * k)),
      IsCompleteMapping φ :=
  ⟨phiZ k, isCompleteMapping_phiZ k hk⟩

/-! ## The paper's notion: antiautomorphisms -/

/-- An *antiautomorphism* of an abelian group `G` (arXiv:1710.09321, Definition 2.1): a
bijection `f : G → G` such that `id_G - f` is injective. -/
def IsAntiautomorphism {G : Type*} [AddCommGroup G] (f : G → G) : Prop :=
  Function.Bijective f ∧ Function.Injective (fun g => g - f g)

/-- Ground truth: `id` is not an antiautomorphism of `ℤ/3` (`id - id = 0`), while
`x ↦ 2x` is. -/
example : ¬ IsAntiautomorphism (id : ZMod 3 → ZMod 3) ∧
    IsAntiautomorphism (fun x : ZMod 3 => 2 * x) := by
  unfold IsAntiautomorphism
  decide

/-- A complete mapping `φ` of `Multiplicative G` yields the antiautomorphism
`g ↦ g + φ g` of the additive group `G`. -/
theorem isAntiautomorphism_of_isCompleteMapping {G : Type*} [AddCommGroup G]
    {φ : Multiplicative G → Multiplicative G} (hφ : IsCompleteMapping φ) :
    IsAntiautomorphism (fun g : G => g + (φ (Multiplicative.ofAdd g)).toAdd) := by
  refine ⟨?_, ?_⟩
  · have h2 := hφ.2
    have heq : (fun g : G => g + (φ (Multiplicative.ofAdd g)).toAdd) =
        Multiplicative.toAdd ∘ (fun g => g * φ g) ∘ Multiplicative.ofAdd := by
      funext g; rfl
    rw [heq]
    exact Multiplicative.toAdd.bijective.comp (h2.comp Multiplicative.ofAdd.bijective)
  · intro g g' h
    have h' : (φ (Multiplicative.ofAdd g)).toAdd = (φ (Multiplicative.ofAdd g')).toAdd := by
      have := congrArg Neg.neg h
      simpa using this
    exact Multiplicative.ofAdd.injective (hφ.1.1 (Multiplicative.toAdd.injective h'))

/-- **Paper-notion form.** For every `k ≥ 1`, `ℤ/2 ⊕ ℤ/2k` admits an antiautomorphism in
the sense of arXiv:1710.09321 (answering the paper's open cases `ℤ_2 ⊕ ℤ_{2^m}`). -/
theorem exists_isAntiautomorphism_zmod_two_prod (k : ℕ) (hk : 0 < k) :
    ∃ f : ZMod 2 × ZMod (2 * k) → ZMod 2 × ZMod (2 * k), IsAntiautomorphism f :=
  ⟨_, isAntiautomorphism_of_isCompleteMapping (isCompleteMapping_phiZ k hk)⟩

/-! ## Closure properties -/

/-- Complete mappings are closed under direct products (paper, Lemma 2.4). -/
theorem IsCompleteMapping.prod {G H : Type*} [Group G] [Group H] {φ : G → G} {ψ : H → H}
    (hφ : IsCompleteMapping φ) (hψ : IsCompleteMapping ψ) :
    IsCompleteMapping (Prod.map φ ψ) := by
  refine ⟨hφ.1.prodMap hψ.1, ?_⟩
  have heq : (fun g : G × H => g * Prod.map φ ψ g) =
      Prod.map (fun a => a * φ a) (fun b => b * ψ b) := by
    funext g; rfl
  rw [heq]
  exact hφ.2.prodMap hψ.2

/-- Complete mappings transport along group isomorphisms. -/
theorem IsCompleteMapping.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {φ : G → G} (hφ : IsCompleteMapping φ) : IsCompleteMapping (e ∘ φ ∘ e.symm) := by
  refine ⟨e.bijective.comp (hφ.1.comp e.symm.bijective), ?_⟩
  have heq : (fun h : H => h * (e ∘ φ ∘ e.symm) h) =
      e ∘ (fun g => g * φ g) ∘ e.symm := by
    funext h
    simp only [Function.comp_apply, map_mul, MulEquiv.apply_symm_apply]
  rw [heq]
  exact e.bijective.comp (hφ.2.comp e.symm.bijective)

/-- **Corollary.** For every `k ≥ 1` and every finite group `H` of odd order,
`ℤ/2 × ℤ/2k × H` admits a complete mapping. -/
theorem exists_isCompleteMapping_zmod_two_prod_prod {H : Type*} [Group H] [Finite H]
    (hH : Odd (Nat.card H)) (k : ℕ) (hk : 0 < k) :
    ∃ φ : Multiplicative (ZMod 2 × ZMod (2 * k)) × H →
      Multiplicative (ZMod 2 × ZMod (2 * k)) × H, IsCompleteMapping φ :=
  ⟨_, IsCompleteMapping.prod (isCompleteMapping_phiZ k hk) (isCompleteMapping_id_of_odd_card hH)⟩

end Candidates.HallCompleteMappingZ2Z2k
