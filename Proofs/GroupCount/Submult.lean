import GroupCount.Gnu

/-!
# The coprime case of Lopes's submultiplicativity conjecture for A000001

OEIS A000001 carries the comment (pulled live with `oeis show A000001`):

> I conjecture that `a(i) * a(j) <= a(i*j)` for all nonnegative integers `i` and `j`.
> — *Jorge R. F. F. Lopes*, Apr 21 2024

Here `a = gnu` is the group-counting function of `GroupCount/Gnu.lean`.  This file proves
the conjecture **whenever `i` and `j` are coprime** (`GroupCount.mul_gnu_le_gnu_of_coprime`).
The general case is open and is deliberately *not* stated anywhere in this file.

## Attribution and novelty status (literature sweep 2026-07-30)

The coprime case proved here is **folklore** in the group-enumeration community: Ren
(arXiv:2405.04794, Section 1) states it as "clear", without proof or citation, and no
source located by the sweep states it as a standalone theorem (checked: Conway–Dietrich–
O'Brien 2008; Blackburn–Neumann–Venkataraman 2007, whose Lemma 21.19 characterises the
*equality* case for arithmetically independent factors; Pyber 1993; Eick's survey; the
OEIS entry itself).  The underlying cancellation fact — coprime direct-product factors
are the unique Hall subgroups for their prime sets, hence recoverable — is well known.
We are not aware of a prior formal proof.  Verdict: LIKELY-KNOWN; sweep record at
`.tasks/main/docs/novelty-Submult.md`.

## The argument

`GroupCount.mul_gnu_le_gnu_of_injective` already reduces the inequality to injectivity of
the descended direct-product map `IsoClass i × IsoClass j → IsoClass (i * j)`.  Injectivity
is the statement that a direct-product decomposition into factors of coprime orders is
unique up to isomorphism, and that is elementary:

Let `φ : G × H ≃* G' × H'` with `|G| = |G'| = i`, `|H| = |H'| = j` and `gcd (i, j) = 1`.
The composite `G →* G × H →* G' × H' →* H'` sends `g` to `(φ (g, 1)).2`, and its image has
order dividing `i` (because `g ^ i = 1`, so `(g, 1) ^ i = 1`) and dividing `j` (Lagrange in
`H'`); coprimality forces it to be trivial
(`GroupCount.snd_apply_mk_one_eq_one_of_coprime`).  Hence `φ (g, 1) = ((φ (g, 1)).1, 1)`,
so `g ↦ (φ (g, 1)).1` is an *injective* monoid hom `G →* G'`, and equal finite
cardinalities upgrade it to an isomorphism
(`GroupCount.nonempty_mulEquiv_fst_of_coprime`).  Swapping the two factors gives
`H ≃* H'` (`GroupCount.nonempty_mulEquiv_snd_of_coprime`).

## Main results

* `GroupCount.snd_apply_mk_one_eq_one_of_coprime` — the coprime order argument in its
  sharpest form: `(φ (g, 1)).2 = 1`.
* `GroupCount.nonempty_mulEquiv_fst_of_coprime`,
  `GroupCount.nonempty_mulEquiv_snd_of_coprime` — coprime cancellation for direct
  products, one factor at a time (only the target factor being recovered carries a
  `[Finite]` instance; see the docstrings for the precise finiteness surface).
* `GroupCount.GroupStructure.prod_iso_prod_iff_of_coprime` — the same statement descended
  to the explicit `Fin n` structures: for coprime orders, `S.prod T` and `S'.prod T'` are
  isomorphic iff both factors are.
* `GroupCount.IsoClass.prod_injective_of_coprime` — the injectivity hypothesis of
  `GroupCount.mul_gnu_le_gnu_of_injective`, discharged under coprimality.
* `GroupCount.mul_gnu_le_gnu_of_coprime` — **the theorem**: `gnu i * gnu j ≤ gnu (i * j)`
  for `Nat.Coprime i j`.

## Trust policy (USER decision, binding for this file)

**Zero `native_decide` anywhere in this module.**  The only kernel evaluations used are
the cheap ones identified in `GroupCount/Gnu.lean` — deciding `Iso` between two *given*
structures, deciding equality of two given structures, and `powOneCount` — plus the
group-axiom fields of the explicit witness structures (`alt3`, `c3sq`) and `Nat.Coprime`
on literals; all far inside the measured kernel wall (which for *values* of `gnu` stops
at `n = 2`).  No value of `gnu` is asserted here; the values consumed (`gnu 3 = 1`,
`gnu 4 = 2`) are the certified ones from `GroupCount/Gnu.lean`.  The axiom sweep at the
end of the file is the check.

## Ground truth

A000001 begins `0, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5, …` at `n = 0, 1, 2, …`, so
`a(4) * a(3) = 2 * 1 = 2 ≤ 5 = a(12)`.  The theorem is exercised at the coprime pair
`(4, 3)` — yielding `2 ≤ gnu 12`, which is *also* reachable upstream by applying the
`powOneCount` invariant directly to the order-twelve product structures, so it is a
demonstration of the descent rather than a bound unreachable without it — and, with
**both** factors nontrivial, at `(4, 9)`: `gnu 4 = 2` and `2 ≤ gnu 9` give
`4 ≤ gnu 36` (`GroupCount.four_le_gnu_thirtysix`), the strongest instance certifiable
in-repo (A000001: `a(36) = 14`).
-/

set_option autoImplicit false

namespace GroupCount

/-! ## Coprime cancellation for direct products of finite groups

Everything in this section is ordinary Mathlib group theory; nothing refers to `gnu` or to
the explicit `Fin n` structures. -/

/-- **The coprime order argument.**  If `φ : G × H ≃* G' × H'` with `|G| = i`, `|H'| = j`
and `i`, `j` coprime, then the `H'`-component of `φ (g, 1)` is trivial: its order divides
`i` (as `(g, 1) ^ i = 1`) and divides `j` (Lagrange in `H'`), hence is `1`. -/
theorem snd_apply_mk_one_eq_one_of_coprime {i j : ℕ} {G H G' H' : Type*}
    [Group G] [Group H] [Group G'] [Group H'] (hG : Nat.card G = i) (hH' : Nat.card H' = j)
    (hij : Nat.Coprime i j) (φ : G × H ≃* G' × H') (g : G) : (φ (g, 1)).2 = 1 := by
  have hmk : ((g, (1 : H)) : G × H) ^ i = 1 := by
    have hinl : (MonoidHom.inl G H) g ^ i = 1 := by
      rw [← map_pow, ← hG, pow_card_eq_one', map_one]
    rwa [MonoidHom.inl_apply] at hinl
  have himg : (φ (g, 1)) ^ i = 1 := by rw [← map_pow, hmk, map_one]
  have hpow : ((φ (g, 1)).2) ^ i = 1 := by rw [← Prod.pow_snd, himg, Prod.snd_one]
  have hdvdi : orderOf ((φ (g, 1)).2) ∣ i := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hdvdj : orderOf ((φ (g, 1)).2) ∣ j := by
    rw [← hH']
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf ((φ (g, 1)).2)) j := Nat.Coprime.coprime_dvd_left hdvdi hij
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvdj)

/-- **Coprime cancellation, first factor.**  If `φ : G × H ≃* G' × H'` where `G` and `G'`
share the finite order `i`, `H'` has order `j`, and `i`, `j` are coprime, then `G ≃* G'`.
The precise finiteness surface: only `G'` carries a `[Finite]` instance; `H` carries no
hypothesis at all, and `H'` only its `Nat.card` value — at the junk value `j = 0` (which
coprimality collapses to `i = 1`) an infinite `H'` satisfies `Nat.card H' = 0` and the
conclusion holds degenerately, both `G` and `G'` being trivial. -/
theorem nonempty_mulEquiv_fst_of_coprime {i j : ℕ} {G H G' H' : Type*}
    [Group G] [Group H] [Group G'] [Group H'] [Finite G'] (hG : Nat.card G = i)
    (hG' : Nat.card G' = i) (hH' : Nat.card H' = j) (hij : Nat.Coprime i j)
    (φ : G × H ≃* G' × H') : Nonempty (G ≃* G') := by
  let ψ : G →* G' := (MonoidHom.fst G' H').comp (φ.toMonoidHom.comp (MonoidHom.inl G H))
  have hψ : ∀ a : G, ψ a = (φ (a, 1)).1 := fun _ => rfl
  have hker : ∀ a : G, ψ a = 1 → a = 1 := by
    intro a ha
    rw [hψ] at ha
    have hsnd : (φ (a, 1)).2 = 1 := snd_apply_mk_one_eq_one_of_coprime hG hH' hij φ a
    have hone : φ ((a, 1) : G × H) = 1 :=
      Prod.ext (by rw [Prod.fst_one]; exact ha) (by rw [Prod.snd_one]; exact hsnd)
    have hmk : ((a, (1 : H)) : G × H) = 1 := φ.map_eq_one_iff.mp hone
    exact (Prod.mk_eq_one.mp hmk).1
  have hinj : Function.Injective ψ := (injective_iff_map_eq_one ψ).mpr hker
  have hcard : Nat.card G = Nat.card G' := by rw [hG, hG']
  have hbij : Function.Bijective ψ :=
    (Nat.bijective_iff_injective_and_card ψ).mpr ⟨hinj, hcard⟩
  exact ⟨MulEquiv.ofBijective ψ hbij⟩

/-- **Coprime cancellation, second factor** — `GroupCount.nonempty_mulEquiv_fst_of_coprime`
applied to the two factors swapped.  Note that `G` needs no cardinality hypothesis. -/
theorem nonempty_mulEquiv_snd_of_coprime {i j : ℕ} {G H G' H' : Type*}
    [Group G] [Group H] [Group G'] [Group H'] [Finite H'] (hH : Nat.card H = j)
    (hG' : Nat.card G' = i) (hH' : Nat.card H' = j) (hij : Nat.Coprime i j)
    (φ : G × H ≃* G' × H') : Nonempty (H ≃* H') :=
  nonempty_mulEquiv_fst_of_coprime hH hH' hG' hij.symm
    ((MulEquiv.prodComm : H × G ≃* G × H).trans
      (φ.trans (MulEquiv.prodComm : G' × H' ≃* H' × G')))

/-! ## Descent to the explicit structures and to `gnu` -/

/-- **Unique coprime factorisation of explicit structures.**  For coprime `i` and `j`, two
direct products of explicit structures are isomorphic exactly when their factors are.  The
`←` direction is `GroupCount.GroupStructure.prod_iso_prod` and needs no coprimality; the
`→` direction is the content. -/
theorem GroupStructure.prod_iso_prod_iff_of_coprime {i j : ℕ} (hij : Nat.Coprime i j)
    (S S' : GroupStructure i) (T T' : GroupStructure j) :
    (S.prod T).Iso (S'.prod T') ↔ S.Iso S' ∧ T.Iso T' := by
  refine ⟨fun hprod => ?_, fun hfac => GroupStructure.prod_iso_prod hfac.1 hfac.2⟩
  obtain ⟨k⟩ := (GroupStructure.iso_iff_nonempty_mulEquiv _ _).mp hprod
  let φ : S.Carrier × T.Carrier ≃* S'.Carrier × T'.Carrier :=
    (GroupStructure.prodMulEquiv S T).symm.trans (k.trans (GroupStructure.prodMulEquiv S' T'))
  have hfst : Nonempty (S.Carrier ≃* S'.Carrier) :=
    nonempty_mulEquiv_fst_of_coprime S.natCard_carrier S'.natCard_carrier
      T'.natCard_carrier hij φ
  have hsnd : Nonempty (T.Carrier ≃* T'.Carrier) :=
    nonempty_mulEquiv_snd_of_coprime T.natCard_carrier S'.natCard_carrier
      T'.natCard_carrier hij φ
  exact ⟨GroupStructure.iso_of_mulEquiv hfst.some, GroupStructure.iso_of_mulEquiv hsnd.some⟩

/-- **The Lopes injectivity, coprime case.**  For coprime `i` and `j` the descended
direct-product map on isomorphism classes is injective — this is precisely the hypothesis
of `GroupCount.mul_gnu_le_gnu_of_injective`. -/
theorem IsoClass.prod_injective_of_coprime {i j : ℕ} (hij : Nat.Coprime i j) :
    Function.Injective fun p : IsoClass i × IsoClass j => IsoClass.prod p.1 p.2 := by
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab
  obtain ⟨S, rfl⟩ := GroupStructure.isoClass_surjective i a₁
  obtain ⟨T, rfl⟩ := GroupStructure.isoClass_surjective j a₂
  obtain ⟨S', rfl⟩ := GroupStructure.isoClass_surjective i b₁
  obtain ⟨T', rfl⟩ := GroupStructure.isoClass_surjective j b₂
  have hcls : (S.prod T).isoClass = (S'.prod T').isoClass := hab
  obtain ⟨h₁, h₂⟩ := (GroupStructure.prod_iso_prod_iff_of_coprime hij S S' T T').mp
    ((GroupStructure.isoClass_eq_iff _ _).mp hcls)
  exact Prod.ext ((GroupStructure.isoClass_eq_iff S S').mpr h₁)
    ((GroupStructure.isoClass_eq_iff T T').mpr h₂)

/-- **Lopes's conjecture for coprime arguments** (OEIS A000001, comment of Jorge R. F. F.
Lopes, 2024-04-21): `gnu i * gnu j ≤ gnu (i * j)` whenever `i` and `j` are coprime.  The
general case is open and is not stated here. -/
theorem mul_gnu_le_gnu_of_coprime {i j : ℕ} (hij : Nat.Coprime i j) :
    gnu i * gnu j ≤ gnu (i * j) :=
  mul_gnu_le_gnu_of_injective (IsoClass.prod_injective_of_coprime hij)

/-! ## Ground truth, satisfiability, and nondegenerate witnesses

Checked against `oeis show A000001`, whose terms at `n = 0, 1, 2, …` are
`0, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5, …`.  Two instances are exercised: the coprime
pair `(4, 3)` — both entries exceed `1`, though `gnu 3 = 1` keeps the counting content
one-sided, and its bound `2 ≤ gnu 12` is also reachable upstream via `powOneCount` at
order twelve — and `(4, 9)`, where both factors are nontrivial and the yield
`4 ≤ gnu 36` is counting content with no single-invariant shortcut in-repo (A000001
gives `a(12) = 5`, `a(36) = 14`).  No value of `gnu` is asserted here; `gnu 3 = 1` and
`gnu 4 = 2` are imported as already certified. -/

section GroundTruth

open GroupStructure

/-! ### The parameters are nondegenerate -/

-- The coprime hypothesis is satisfiable away from the degenerate `i = 1` / `j = 1`
-- collapse, and both quantified domains are inhabited there.
example : Nat.Coprime 4 3 := by decide

example : 1 < 4 ∧ 1 < 3 := by omega

example : Nonempty (GroupStructure 4) ∧ Nonempty (GroupStructure 3) :=
  ⟨⟨cyclic 4⟩, ⟨cyclic 3⟩⟩

/-! ### The abstract cancellation lemmas, every hypothesis discharged -/

-- `snd_apply_mk_one_eq_one_of_coprime` at the concrete model `G = G' = C₄`,
-- `H = H' = C₃`, `i = 4`, `j = 3`.
example (g : (cyclic 4).Carrier) :
    ((MulEquiv.refl ((cyclic 4).Carrier × (cyclic 3).Carrier)) (g, 1)).2 = 1 :=
  snd_apply_mk_one_eq_one_of_coprime (i := 4) (j := 3) (cyclic 4).natCard_carrier
    (cyclic 3).natCard_carrier (by decide) (MulEquiv.refl _) g

example : Nonempty ((cyclic 4).Carrier ≃* (cyclic 4).Carrier) :=
  nonempty_mulEquiv_fst_of_coprime (i := 4) (j := 3) (cyclic 4).natCard_carrier
    (cyclic 4).natCard_carrier (cyclic 3).natCard_carrier (by decide)
    (MulEquiv.refl ((cyclic 4).Carrier × (cyclic 3).Carrier))

example : Nonempty ((cyclic 3).Carrier ≃* (cyclic 3).Carrier) :=
  nonempty_mulEquiv_snd_of_coprime (i := 4) (j := 3) (cyclic 3).natCard_carrier
    (cyclic 4).natCard_carrier (cyclic 3).natCard_carrier (by decide)
    (MulEquiv.refl ((cyclic 4).Carrier × (cyclic 3).Carrier))

-- …and once more at genuinely *different* source and target types, so that the recovered
-- isomorphism is not the identity in disguise: from a product isomorphism at order twelve
-- the first-factor isomorphism `C₄ ≃* Multiplicative (ZMod 4)` is read off.
example : Nonempty ((cyclic 4).Carrier ≃* Multiplicative (ZMod 4)) :=
  nonempty_mulEquiv_fst_of_coprime (i := 4) (j := 3) (cyclic 4).natCard_carrier
    (by simp) (cyclic 3).natCard_carrier (by decide)
    ((mulEquivOfCyclicCardEq (G := (cyclic 4).Carrier) (G' := Multiplicative (ZMod 4))
      (by simp)).prodCongr (MulEquiv.refl (cyclic 3).Carrier))

/-! ### A second structure on `Fin 3`, so the descent is instantiated at distinct data -/

/-- A second group structure on `Fin 3`: addition modulo `3` re-based so that the identity
element is `1` rather than `0`.  A034383 counts three labeled groups of order three;
`alt3` is one of the two that `GroupCount.GroupStructure.cyclic 3` is not, and it is
isomorphic to it, so it instantiates the descent at genuinely distinct structures. -/
private def alt3 : GroupStructure 3 where
  mul a b := a + b + 2
  one := 1
  inv a := -a + 2
  mul_assoc := by decide
  one_mul := by decide
  inv_mul_cancel := by decide

-- Ground-truth checks for `alt3`: its tables, and its position relative to `cyclic 3`.
example : alt3.one = 1 := by decide

example : alt3.mul 1 2 = 2 := by decide

example : alt3.mul 0 0 = 2 := by decide

example : alt3.inv 0 = 2 := by decide

example : alt3 ≠ cyclic 3 := by decide

example : (cyclic 3).Iso alt3 := by decide

-- The hard direction of `prod_iso_prod_iff_of_coprime`, applied *positively* at distinct
-- structures: `C₄ × C₃` and `C₄ × alt3` are isomorphic structures on `Fin 12`, and the
-- theorem recovers both factor isomorphisms.
example : (cyclic 4).Iso (cyclic 4) ∧ (cyclic 3).Iso alt3 :=
  (prod_iso_prod_iff_of_coprime (by decide) (cyclic 4) (cyclic 4) (cyclic 3) alt3).mp
    (prod_iso_prod (.refl _) (by decide))

/-! ### New content at order twelve -/

/-- `C₄ × C₃` and `V₄ × C₃` are non-isomorphic groups of order twelve, recovered here
through the coprime descent from the `powOneCount` invariant that separates `C₄` from the
Klein four-group at order *four*.  (The same invariant also separates the two product
structures directly at order twelve, so this is a demonstration that the descent
transports a factor-level distinction — not a fact unreachable without it.) -/
private theorem not_iso_prod_cyclic_four_klein :
    ¬ ((cyclic 4).prod (cyclic 3)).Iso (klein.prod (cyclic 3)) := by
  intro hiso
  have hfac : (cyclic 4).Iso klein ∧ (cyclic 3).Iso (cyclic 3) :=
    (prod_iso_prod_iff_of_coprime (by decide) (cyclic 4) klein (cyclic 3) (cyclic 3)).mp hiso
  exact not_iso_of_powOneCount_ne (k := 2) (by decide) hfac.1

-- …so the descended product map genuinely separates two order-twelve classes.
example : IsoClass.prod (cyclic 4).isoClass (cyclic 3).isoClass ≠
    IsoClass.prod klein.isoClass (cyclic 3).isoClass := by
  rw [← isoClass_prod, ← isoClass_prod]
  intro hcls
  exact not_iso_prod_cyclic_four_klein ((isoClass_eq_iff _ _).mp hcls)

-- The theorem at the nondegenerate coprime pair `(4, 3)`, and the bound it yields.
example : gnu 4 * gnu 3 ≤ gnu (4 * 3) := mul_gnu_le_gnu_of_coprime (by decide)

example : gnu 4 * gnu 3 = 2 := by rw [gnu_four, gnu_three]

example : 2 ≤ gnu 12 := by
  have hle : gnu 4 * gnu 3 ≤ gnu (4 * 3) := mul_gnu_le_gnu_of_coprime (by decide)
  rw [gnu_four, gnu_three, show (4 : ℕ) * 3 = 12 from rfl] at hle
  omega

-- At `(1, 4)` the theorem reproduces the reduction witness of `GroupCount/Gnu.lean`.
-- (The whole `i = 1` family is contentless — `gnu 1 * gnu j = gnu (1 * j)` syntactically —
-- which is why the load-bearing witnesses are `(4, 3)` above and `(4, 9)` below.)
example : gnu 1 * gnu 4 ≤ gnu (1 * 4) := mul_gnu_le_gnu_of_coprime (by decide)

/-! ### The strongest instance in reach: both factors nontrivial -/

/-- `C₃ × C₃` as an explicit structure on `Fin 9` (note `3 * 3` reduces to `9`), the
non-cyclic group of order nine — the witness that `2 ≤ gnu 9`. -/
private def c3sq : GroupStructure 9 := (cyclic 3).prod (cyclic 3)

-- The `x³ = 1` counts separate `C₉` from `C₃ × C₃` — kernel-cheap (`powOneCount` is
-- `O(k · n)`, far inside the wall).
example : (cyclic 9).powOneCount 3 = 3 := by decide

example : c3sq.powOneCount 3 = 9 := by decide

private theorem not_iso_cyclic_nine_c3sq : ¬ (cyclic 9).Iso c3sq :=
  not_iso_of_powOneCount_ne (k := 3) (by decide)

/-- `2 ≤ gnu 9` — A000001 gives `a(9) = 2`, so this lower bound is exact; it is certified
by the `powOneCount` invariant alone, no classification input. -/
theorem two_le_gnu_nine : 2 ≤ gnu 9 := two_le_gnu_of_not_iso not_iso_cyclic_nine_c3sq

/-- `4 ≤ gnu 36`: the theorem's counting content with **both** factors nontrivial —
`gnu 4 = 2` (certified upstream) and `2 ≤ gnu 9` (`GroupCount.two_le_gnu_nine`) at the
coprime pair `(4, 9)`.  A000001 gives `a(36) = 14`, so the bound is true and not tight. -/
theorem four_le_gnu_thirtysix : 4 ≤ gnu 36 := by
  have hle : gnu 4 * gnu 9 ≤ gnu (4 * 9) := mul_gnu_le_gnu_of_coprime (by decide)
  rw [gnu_four, show (4 : ℕ) * 9 = 36 from rfl] at hle
  have h9 : 2 ≤ gnu 9 := two_le_gnu_nine
  omega

end GroundTruth

/-! ## Axiom audit

Every declaration above is `sorry`-free; the sweep below confirms each rests only on
`{propext, Classical.choice, Quot.sound}`.  The subset is the sound `native_decide`
detector: a use would appear as a per-declaration `*._native.native_decide.ax_*` axiom
on this toolchain (`Lean.ofReduceBool` is never emitted, so grepping for it detects
nothing).  There is no `native_decide` in this file. -/

#print axioms snd_apply_mk_one_eq_one_of_coprime
#print axioms nonempty_mulEquiv_fst_of_coprime
#print axioms nonempty_mulEquiv_snd_of_coprime
#print axioms GroupStructure.prod_iso_prod_iff_of_coprime
#print axioms IsoClass.prod_injective_of_coprime
#print axioms mul_gnu_le_gnu_of_coprime
#print axioms alt3
#print axioms not_iso_prod_cyclic_four_klein
#print axioms c3sq
#print axioms not_iso_cyclic_nine_c3sq
#print axioms two_le_gnu_nine
#print axioms four_le_gnu_thirtysix

end GroupCount
