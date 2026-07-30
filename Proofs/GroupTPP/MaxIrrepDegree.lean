import GroupTPP.CharDegreesMul
import GroupTPP.CharDegreesComm
import GroupCount.Structures

/-!
# The maximal irreducible character degree of a group of order `n` (OEIS A060938)

OEIS [A060938](https://oeis.org/A060938) is

  `a(n)` = *maximal degree of an irreducible representation of a group with `n` elements*,

`a(1..12) = 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3`.  Eric M. Schmidt's comment of
2012-10-17 on that entry asserts, without proof or reference,

  `a(m) * a(n) ≤ a(m*n)`.

This file formalizes both the sequence and the comment.

## Novelty status (literature sweep 2026-07-30, `.tasks/main/docs/novelty-MaxIrrepDegree.md`)

LIKELY-KNOWN.  The inequality is an immediate corollary of the standard
classification of irreducible representations of direct products (Serre,
*Linear Representations of Finite Groups*, Theorem 10; Isaacs, *Character Theory
of Finite Groups*, Theorem 4.21 / Problem 4.4): if `G` and `H` witness the maxima
`a(m)` and `a(n)`, then `G × H` has order `m*n` and top character degree
`a(m) * a(n)`.  Folklore-grade to a character theorist, but no published source
states it for the cross-order function `a(n)`; Schmidt's 2012 comment is the
earliest explicit statement found, and this file provides the first recorded
formal proof.  Not a novel result.

## The definition

Following the `Fin n`-carrier convention of `GroupCount.Structures`, `a(n)` is the
supremum, over **all** group structures on the carrier `Fin n`, of the largest entry
of the character-degree multiset:

  `maxIrrepDegree n = ⨆ (G : Group (Fin n)), (charDegrees (Fin n)).sup`.

The index type `Group (Fin n)` is a `Fintype`
(`GroupCount.instFintypeGroupFin`, via the explicit multiplication-table
representation `GroupCount.GroupStructure`), so the supremum is a `Finset.sup`
over `Finset.univ` and needs no completeness hypothesis.  Every group of order `n`
occurs, up to isomorphism, as one of these structures
(`maxCharDegree_le_maxIrrepDegree`), and `charDegrees` is an isomorphism invariant
(`GroupTPP.CharDegreesMul.charDegrees_eq_of_mulEquiv`), so the supremum really is
the maximum over isomorphism classes of groups of order `n` — but no quotient by
isomorphism is needed to state it.

**The `n = 0` convention is pinned explicitly** by `maxIrrepDegree_zero`:
there is no group structure on the empty carrier, so `Finset.univ` is empty and
the `Finset.sup` returns `⊥ = 0`.  A060938 has offset `1` and says nothing about
`n = 0`; the main theorem therefore carries `0 < m` and `0 < n`.

## Main results

* `GroupTPP.MaxIrrepDegree.maxCharDegree` — the largest irreducible complex
  character degree of a fixed finite group.
* `GroupTPP.MaxIrrepDegree.maxCharDegree_prod` — **the top degree is multiplicative
  over direct products**: `maxCharDegree (G × H) = maxCharDegree G * maxCharDegree H`.
  (Not just `≥`: the multiset of degrees of `G × H` is exactly the multiset of
  pairwise products, `GroupTPP.CharDegreesMul.charDegrees_prod`.)
* `GroupTPP.MaxIrrepDegree.maxIrrepDegree` — `a(n)`.
* `GroupTPP.MaxIrrepDegree.maxIrrepDegree_mul_le` — **Schmidt's comment**:
  `a(m) * a(n) ≤ a(m * n)` for `0 < m`, `0 < n`.
* `GroupTPP.MaxIrrepDegree.maxIrrepDegree_sq_le` — `a(n)^2 ≤ n` (from `Σ dᵢ² = |G|`).
* `GroupTPP.MaxIrrepDegree.one_le_maxIrrepDegree` — `1 ≤ a(n)` for `0 < n`.
* `GroupTPP.MaxIrrepDegree.maxIrrepDegree_prime`,
  `GroupTPP.MaxIrrepDegree.maxIrrepDegree_prime_sq` — `a(p) = a(p²) = 1` for `p`
  prime (the prime and prime-square cases of the other A060938 comment,
  "`a(n) = 1` iff every group of order `n` is Abelian", A051532).
* `GroupTPP.MaxIrrepDegree.two_le_maxCharDegree_of_mul_ne` — a nonabelian finite
  group has an irreducible representation of degree at least `2`.

## Ground truth

The whole initial segment of A060938 through `n = 6` is proved:

  `a(0) = 0` (pinned convention), `a(1) = a(2) = a(3) = a(4) = a(5) = 1`, `a(6) = 2`,

matching the OEIS terms `1, 1, 1, 1, 1, 2` at `n = 1, …, 6`.  In addition
`maxIrrepDegree_mul_le` instantiated at `m = n = 6` reproduces the OEIS value
`a(36) = 4` as a lower bound (`four_le_maxIrrepDegree_36`).

## References

* OEIS [A060938](https://oeis.org/A060938), comment of Eric M. Schmidt, 2012-10-17.
* `GroupTPP.CharDegrees` (the degree multiset, `Σ dᵢ² = |G|`, `#irreps = #classes`),
  `GroupTPP.CharDegreesMul` (`charDegrees_prod`, `charDegrees_eq_of_mulEquiv`).
-/

set_option autoImplicit false

open scoped BigOperators
open GroupTPP.CharDegrees GroupTPP.CharDegreesMul GroupTPP.CharDegreesComm

namespace GroupTPP.MaxIrrepDegree

/-! ### Multiset suprema over `ℕ`

`Multiset.sup` is the fold of `⊔` with unit `⊥ = 0`.  Two facts about it are
needed and absent from Mathlib: a nonempty `ℕ`-multiset attains its supremum,
and the supremum of the multiset of pairwise products is the product of the
suprema. -/

/-- A nonempty multiset of naturals contains its own supremum. -/
private theorem sup_mem_of_ne_zero : ∀ {s : Multiset ℕ}, s ≠ 0 → s.sup ∈ s := by
  intro s
  induction s using Multiset.induction with
  | empty => intro h; exact absurd rfl h
  | cons a s ih =>
    intro _
    rw [Multiset.sup_cons]
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · rcases max_choice a s.sup with h | h
      · rw [h]; exact Multiset.mem_cons_self a s
      · rw [h]; exact Multiset.mem_cons_of_mem (ih hs)

/-- Scaling a multiset of naturals scales its supremum. -/
private theorem sup_map_mul_left (a : ℕ) (t : Multiset ℕ) :
    (t.map (fun e => a * e)).sup = a * t.sup := by
  induction t using Multiset.induction with
  | empty => simp
  | cons e t ih =>
    rw [Multiset.map_cons, Multiset.sup_cons, ih, Multiset.sup_cons]
    exact (mul_max_of_nonneg e t.sup (Nat.zero_le a)).symm

/-- **The supremum of all pairwise products is the product of the suprema.**
This is the multiset-level content of `maxCharDegree_prod`. -/
theorem sup_bind_map_mul (s t : Multiset ℕ) :
    (s.bind (fun d => t.map (fun e => d * e))).sup = s.sup * t.sup := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_bind, Multiset.sup_add, ih, sup_map_mul_left, Multiset.sup_cons]
    exact (max_mul_of_nonneg a s.sup (Nat.zero_le t.sup)).symm

/-! ### The top character degree of a fixed finite group -/

/-- **The top irreducible character degree** of a finite group `G`: the largest
entry of `GroupTPP.CharDegrees.charDegrees G`.  Total, since `Multiset.sup`
returns `⊥ = 0` on the empty multiset — but `charDegrees G` is never empty
(`charDegrees_ne_zero`), so the junk value is never taken. -/
noncomputable def maxCharDegree (G : Type*) [Group G] [Fintype G] : ℕ :=
  (charDegrees G).sup

/-- A finite group has at least one irreducible representation, so its
character-degree multiset is nonempty.  (Otherwise `Σ dᵢ² = |G|` would read
`0 = |G|`.) -/
theorem charDegrees_ne_zero (G : Type*) [Group G] [Fintype G] : charDegrees G ≠ 0 := by
  intro h
  have h2 : charDegreeSum G 2 = Fintype.card G := charDegreeSum_two G
  unfold charDegreeSum at h2
  rw [h] at h2
  simp only [Multiset.map_zero, Multiset.sum_zero] at h2
  exact Fintype.card_ne_zero h2.symm

/-- The top character degree is itself a character degree. -/
theorem maxCharDegree_mem (G : Type*) [Group G] [Fintype G] :
    maxCharDegree G ∈ charDegrees G :=
  sup_mem_of_ne_zero (charDegrees_ne_zero G)

/-- Every finite group has an irreducible representation, so `1 ≤ maxCharDegree G`. -/
theorem one_le_maxCharDegree (G : Type*) [Group G] [Fintype G] : 1 ≤ maxCharDegree G :=
  one_le_of_mem_charDegrees (maxCharDegree_mem G)

/-- **The top degree squared is at most the group order**, since it is one term of
`Σᵢ dᵢ² = |G|` (`GroupTPP.CharDegrees.charDegreeSum_two`). -/
theorem maxCharDegree_sq_le_card (G : Type*) [Group G] [Fintype G] :
    maxCharDegree G ^ 2 ≤ Fintype.card G := by
  rw [← charDegreeSum_two G]
  unfold charDegreeSum
  exact Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
    (Multiset.mem_map_of_mem (fun d => d ^ 2) (maxCharDegree_mem G))

/-- **The top character degree is multiplicative over direct products.**
The degrees of `G × H` are exactly the pairwise products of the degrees of `G`
and of `H` (`GroupTPP.CharDegreesMul.charDegrees_prod`), and the supremum of the
pairwise products is the product of the suprema. -/
theorem maxCharDegree_prod (G H : Type*) [Group G] [Fintype G] [Group H] [Fintype H] :
    maxCharDegree (G × H) = maxCharDegree G * maxCharDegree H := by
  unfold maxCharDegree
  rw [charDegrees_prod, sup_bind_map_mul]

/-- **An abelian group has top character degree `1`**: all of its irreducible
complex representations are one-dimensional
(`GroupTPP.CharDegreesComm.charDegrees_of_commGroup`), and there is at least one
of them. -/
theorem maxCharDegree_of_commGroup (H : Type*) [CommGroup H] [Fintype H] :
    maxCharDegree H = 1 := by
  unfold maxCharDegree
  rw [charDegrees_of_commGroup H]
  refine le_antisymm (Multiset.sup_le.mpr fun b hb => le_of_eq ?_)
    (Multiset.le_sup ?_)
  · exact Multiset.eq_of_mem_replicate hb
  · exact Multiset.mem_replicate.mpr ⟨Fintype.card_ne_zero, rfl⟩

/-! ### `a(n)`: the maximum over all group structures on `Fin n` -/

/-- The top character degree of the carrier `Fin n` equipped with the group
structure `G`.  Written with explicit instance arguments so that the group
structure being maximized over is visible in the statement. -/
noncomputable def maxDegreeOn {n : ℕ} (G : Group (Fin n)) : ℕ :=
  @maxCharDegree (Fin n) G (Fin.fintype n)

/-- **OEIS A060938**: `a(n)` is the maximal degree of a complex irreducible
representation of a group with `n` elements, realized here as the supremum of
`maxDegreeOn` over the (finite) type `Group (Fin n)` of all group structures on
the carrier `Fin n`.

At `n = 0` the index type is empty and the `Finset.sup` convention returns `0`
(`maxIrrepDegree_zero`); A060938 has offset `1`, so statements about the
sequence carry `0 < n`. -/
noncomputable def maxIrrepDegree (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Group (Fin n))).sup maxDegreeOn

/-- **The `n = 0` convention, pinned.** There is no group structure on the empty
carrier `Fin 0` (a group has an identity element), so the supremum is over the
empty `Finset` and equals `⊥ = 0`. -/
theorem maxIrrepDegree_zero : maxIrrepDegree 0 = 0 := by
  haveI : IsEmpty (Group (Fin 0)) := ⟨fun G => G.one.elim0⟩
  unfold maxIrrepDegree
  rw [Finset.univ_eq_empty, Finset.sup_empty]
  rfl

/-- **Every group of order `n` is one of the structures maximized over.**
Transporting `K` along an equivalence `Fin n ≃ K` produces a group structure on
`Fin n` with the same character degrees (`charDegrees_eq_of_mulEquiv`), so the
top degree of `K` is bounded by `a(n)`. -/
theorem maxCharDegree_le_maxIrrepDegree (K : Type*) [Group K] [Fintype K] (n : ℕ)
    (hK : Fintype.card K = n) : maxCharDegree K ≤ maxIrrepDegree n := by
  subst hK
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  letI GF : Group (Fin (Fintype.card K)) := e.group
  have hchar : @charDegrees (Fin (Fintype.card K)) GF (Fin.fintype _) = charDegrees K :=
    charDegrees_eq_of_mulEquiv (Equiv.mulEquiv e)
  have hdeg : maxDegreeOn GF = maxCharDegree K := by
    unfold maxDegreeOn maxCharDegree
    rw [hchar]
  rw [← hdeg]
  exact Finset.le_sup (Finset.mem_univ GF)

/-- **The supremum defining `a(n)` is attained** for `0 < n`: the index type
`Group (Fin n)` is a nonempty `Fintype` (the cyclic structure witnesses
nonemptiness). -/
theorem exists_maxDegreeOn_eq (n : ℕ) (hn : 0 < n) :
    ∃ G : Group (Fin n), maxIrrepDegree n = maxDegreeOn G := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Nonempty (Group (Fin n)) := ⟨(GroupCount.GroupStructure.cyclic n).toGroup⟩
  obtain ⟨G, -, hG⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Group (Fin n))) Finset.univ_nonempty
      maxDegreeOn
  exact ⟨G, hG⟩

/-- `1 ≤ a(n)` for `0 < n`: some group structure exists on `Fin n`, and every
group has an irreducible representation. -/
theorem one_le_maxIrrepDegree (n : ℕ) (hn : 0 < n) : 1 ≤ maxIrrepDegree n := by
  obtain ⟨G, hG⟩ := exists_maxDegreeOn_eq n hn
  rw [hG]
  exact @one_le_maxCharDegree (Fin n) G (Fin.fintype n)

/-- **`a(n)^2 ≤ n`.** Each character degree of a group of order `n` satisfies
`d² ≤ Σᵢ dᵢ² = n`.  This is the basic sanity bound tying `maxIrrepDegree` to the
group order; e.g. it forces `a(1) = 1` and `a(6) ≤ 2`. -/
theorem maxIrrepDegree_sq_le (n : ℕ) : maxIrrepDegree n ^ 2 ≤ n := by
  have hb : maxIrrepDegree n ≤ Nat.sqrt n := by
    refine Finset.sup_le fun G _ => ?_
    have h : maxDegreeOn G ^ 2 ≤ n := by
      have hc := @maxCharDegree_sq_le_card (Fin n) G (Fin.fintype n)
      rwa [Fintype.card_fin] at hc
    rw [Nat.le_sqrt, ← pow_two]
    exact h
  calc maxIrrepDegree n ^ 2 ≤ Nat.sqrt n ^ 2 := Nat.pow_le_pow_left hb 2
    _ ≤ n := Nat.sqrt_le' n

/-- **`a(p) = 1` for every prime `p`.** Every group of prime order is cyclic
(`isCyclic_of_prime_card`), hence abelian, hence has all character degrees `1`
(`maxCharDegree_of_commGroup`).  This is the prime case of the OEIS comment
"`a(n) = 1` iff every group of order `n` is Abelian (A051532)", and it pins
`a(2) = a(3) = a(5) = a(7) = a(11) = ⋯ = 1` in one theorem. -/
theorem maxIrrepDegree_prime (p : ℕ) (hp : p.Prime) : maxIrrepDegree p = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_antisymm (Finset.sup_le fun G _ => ?_) (one_le_maxIrrepDegree p hp.pos)
  letI := G
  haveI : IsCyclic (Fin p) := isCyclic_of_prime_card (p := p) (by simp)
  letI cg : CommGroup (Fin p) := IsCyclic.commGroup
  exact le_of_eq (maxCharDegree_of_commGroup (Fin p))

/-- **`a(p²) = 1` for every prime `p`.** Every group of order `p²` is abelian
(`IsPGroup.commGroupOfCardEqPrimeSq`), hence has all character degrees `1`.
This pins `a(4) = a(9) = a(25) = a(49) = ⋯ = 1`. -/
theorem maxIrrepDegree_prime_sq (p : ℕ) (hp : p.Prime) : maxIrrepDegree (p ^ 2) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine le_antisymm (Finset.sup_le fun G _ => ?_)
    (one_le_maxIrrepDegree (p ^ 2) (pow_pos hp.pos 2))
  letI := G
  letI cg : CommGroup (Fin (p ^ 2)) := IsPGroup.commGroupOfCardEqPrimeSq (p := p) (by simp)
  exact le_of_eq (maxCharDegree_of_commGroup (Fin (p ^ 2)))

/-- **A nonabelian finite group has an irreducible representation of degree at
least `2`** — the converse direction of the A060938 comment "`a(n) = 1` iff every
group of order `n` is Abelian".

Proof.  Suppose every degree were `1`.  Then `Σᵢ dᵢ² = |G|`
(`GroupTPP.CharDegrees.charDegreeSum_two`) degenerates to `#irreps = |G|`, and
`#irreps = #ConjClasses G` (`GroupTPP.CharDegrees.card_charDegrees`), so the
surjection `ConjClasses.mk : G → ConjClasses G` is a surjection between finite
types of equal cardinality, hence injective.  Since `a * b` and `b * a` are
always conjugate (`b * (a * b) * b⁻¹ = b * a`), injectivity forces
`a * b = b * a`. -/
theorem two_le_maxCharDegree_of_mul_ne (G : Type*) [Group G] [Fintype G] {a b : G}
    (hab : a * b ≠ b * a) : 2 ≤ maxCharDegree G := by
  by_contra hlt
  -- Step 1: every character degree is `1`.
  have hall : ∀ d ∈ charDegrees G, d = 1 := by
    intro d hd
    have hd1 : 1 ≤ d := one_le_of_mem_charDegrees hd
    have hd2 : d ≤ maxCharDegree G := Multiset.le_sup hd
    omega
  -- Step 2: hence the squared-degree multiset is a multiset of ones …
  have hmap : (charDegrees G).map (fun d => d ^ 2)
      = Multiset.replicate (Multiset.card (charDegrees G)) 1 := by
    rw [← Multiset.card_map (fun d => d ^ 2) (charDegrees G), Multiset.eq_replicate_card]
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hc
    rw [hall d hd, one_pow]
  -- … and `Σᵢ dᵢ² = |G|` degenerates to `#irreps = |G|`.
  have hcount : Multiset.card (charDegrees G) = Fintype.card G := by
    have h2 := charDegreeSum_two G
    unfold charDegreeSum at h2
    rwa [hmap, Multiset.sum_replicate, smul_eq_mul, mul_one] at h2
  -- Step 3: `#irreps = #conjugacy classes`, so there are `|G|` conjugacy classes.
  have hcls : Nat.card (ConjClasses G) = Fintype.card G := by
    rw [← card_charDegrees, hcount]
  -- Step 4: a surjection between finite types of equal cardinality is injective.
  haveI : Finite (ConjClasses G) :=
    Finite.of_surjective (ConjClasses.mk : G → ConjClasses G) ConjClasses.mk_surjective
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  have hcard : Fintype.card G = Fintype.card (ConjClasses G) := by
    have hfin : Fintype.card (ConjClasses G) = Fintype.card G := by
      rw [← Nat.card_eq_fintype_card]; exact hcls
    exact hfin.symm
  have hbij : Function.Bijective (ConjClasses.mk : G → ConjClasses G) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr ⟨ConjClasses.mk_surjective, hcard⟩
  -- Step 5: `a * b` and `b * a` are conjugate, hence equal — contradiction.
  refine hab (hbij.injective ?_)
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_iff.mpr ⟨b, by group⟩

/-! ### Schmidt's comment -/

/-- **Schmidt's A060938 comment (2012-10-17):** `a(m) * a(n) ≤ a(m * n)`.

Proof.  Pick group structures `G` on `Fin m` and `H` on `Fin n` attaining `a(m)`
and `a(n)` (`exists_maxDegreeOn_eq`; the index types are nonempty finite).  Then
`G × H` is a group of order `m * n`, and its top character degree is exactly
`a(m) * a(n)` (`maxCharDegree_prod`, from
`GroupTPP.CharDegreesMul.charDegrees_prod`).  Transporting `G × H` to the carrier
`Fin (m * n)` (`maxCharDegree_le_maxIrrepDegree`) exhibits it as one of the
structures `a(m * n)` is a supremum over, so `a(m * n)` dominates it.

The hypotheses `0 < m`, `0 < n` are those of the OEIS entry (offset `1`); they
are used to make the two suprema attained. -/
theorem maxIrrepDegree_mul_le (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    maxIrrepDegree m * maxIrrepDegree n ≤ maxIrrepDegree (m * n) := by
  obtain ⟨G, hG⟩ := exists_maxDegreeOn_eq m hm
  obtain ⟨H, hH⟩ := exists_maxDegreeOn_eq n hn
  letI := G
  letI := H
  have hcard : Fintype.card (Fin m × Fin n) = m * n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  calc maxIrrepDegree m * maxIrrepDegree n
      = maxCharDegree (Fin m) * maxCharDegree (Fin n) := by rw [hG, hH]; rfl
    _ = maxCharDegree (Fin m × Fin n) := (maxCharDegree_prod (Fin m) (Fin n)).symm
    _ ≤ maxIrrepDegree (m * n) := maxCharDegree_le_maxIrrepDegree _ _ hcard

/-! ### Ground truth against the OEIS terms

A060938 begins (offset 1)

  `1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, …`

and `a(36) = 4`.  The values checked below are `a(0) = 0` (the pinned
convention), `a(1) = a(2) = a(3) = a(4) = a(5) = 1`, `a(6) = 2` — the entire
initial segment through `n = 6` — and the lower bound `4 ≤ a(36)` produced by the
main theorem.  Note that `a(6) = 2` is the first value that distinguishes
`maxIrrepDegree` from the constant `1`, so it is the check that actually
discriminates the definition. -/

section GroundTruth

/-- Auxiliary arithmetic: over `ℕ`, `a² ≤ k < (b+1)²` forces `a ≤ b`. -/
private theorem le_of_sq_le {a b k : ℕ} (h : a ^ 2 ≤ k) (hk : k < (b + 1) ^ 2) : a ≤ b := by
  by_contra hc
  have hb : b + 1 ≤ a := by omega
  have hsq : (b + 1) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hb 2
  omega

/-- `a(1) = 1` (OEIS A060938): the trivial group is the only group of order `1`. -/
theorem maxIrrepDegree_one : maxIrrepDegree 1 = 1 :=
  le_antisymm (le_of_sq_le (b := 1) (maxIrrepDegree_sq_le 1) (by norm_num))
    (one_le_maxIrrepDegree 1 (by norm_num))

/-- `a(2) = 1` (OEIS A060938). -/
theorem maxIrrepDegree_two : maxIrrepDegree 2 = 1 :=
  maxIrrepDegree_prime 2 Nat.prime_two

/-- `a(3) = 1` (OEIS A060938). -/
theorem maxIrrepDegree_three : maxIrrepDegree 3 = 1 :=
  maxIrrepDegree_prime 3 Nat.prime_three

/-- `a(4) = 1` (OEIS A060938): every group of order `4 = 2²` is abelian. -/
theorem maxIrrepDegree_four : maxIrrepDegree 4 = 1 := by
  have h := maxIrrepDegree_prime_sq 2 Nat.prime_two
  norm_num at h
  exact h

/-- `a(5) = 1` (OEIS A060938). -/
theorem maxIrrepDegree_five : maxIrrepDegree 5 = 1 :=
  maxIrrepDegree_prime 5 (by norm_num)

/-- `a(6) = 2` (OEIS A060938): the upper bound is `a(6)² ≤ 6 < 3²`, and the lower
bound is witnessed by the symmetric group `S₃ = Equiv.Perm (Fin 3)`, a nonabelian
group of order `6` (the transpositions `(0 1)` and `(0 2)` do not commute). -/
theorem maxIrrepDegree_six : maxIrrepDegree 6 = 2 := by
  refine le_antisymm (le_of_sq_le (b := 2) (maxIrrepDegree_sq_le 6) (by norm_num)) ?_
  have hcard : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    rfl
  have hpt : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) 0
      ≠ (Equiv.swap (0 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) 0 := by decide
  have hne : Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2
      ≠ Equiv.swap (0 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := fun h => hpt (by rw [h])
  calc (2 : ℕ) ≤ maxCharDegree (Equiv.Perm (Fin 3)) :=
        two_le_maxCharDegree_of_mul_ne (Equiv.Perm (Fin 3)) hne
    _ ≤ maxIrrepDegree 6 := maxCharDegree_le_maxIrrepDegree _ _ hcard

/-- Satisfiability of `maxIrrepDegree_mul_le`: both hypotheses instantiated
jointly at `m = 2`, `n = 3`, giving `a(2) * a(3) = 1 ≤ 2 = a(6)`. -/
example : maxIrrepDegree 2 * maxIrrepDegree 3 ≤ maxIrrepDegree 6 :=
  maxIrrepDegree_mul_le 2 3 (by norm_num) (by norm_num)

/-- The main theorem at `m = n = 6` reproduces the OEIS value `a(36) = 4` as a
lower bound — the content of the theorem, not a degenerate instance. -/
theorem four_le_maxIrrepDegree_36 : 4 ≤ maxIrrepDegree 36 := by
  have h := maxIrrepDegree_mul_le 6 6 (by norm_num) (by norm_num)
  rw [maxIrrepDegree_six] at h
  norm_num at h
  exact h

end GroundTruth

end GroupTPP.MaxIrrepDegree
