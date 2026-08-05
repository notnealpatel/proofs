/-
  Erdős Problem #20 (Sunflower Conjecture) — the classical Erdős–Rado
  sunflower lemma, on the `IsSunflowerWith`/`HasSunflower` definitions of
  `Erdos/Erdos20/Sunflower.lean`.

  ══════════════════════════════════════════════════════════════════════
  PRIMARY SOURCES (verbatim)
  ══════════════════════════════════════════════════════════════════════

  [1] erdosproblems.com problem #20, statement (via `goof erdos fetch 20`),
      quoted verbatim:

        "Let $f(n,k)$ be minimal such that every family  $\mathcal{F}$  of
        $n$-uniform sets with $\lvert  \mathcal{F}\rvert \geq f(n,k)$
        contains a $k$-sunflower. Is it true that\[f(n,k) < c_k^n\]for some
        constant $c_k>0$?"

      CONVENTION WARNING: erdosproblems.com writes $n$ for the uniformity
      and $k$ for the number of petals.  Wikipedia, the AFP entry, and this
      file all use the OPPOSITE convention: `k` is the common set size and
      `r` is the number of petals.  Erdős #20 asks for $f < c_r^k$; the
      lemma proved here is the classical $f \le (r-1)^k \cdot k!$, which is
      the *known* upper bound, not the conjecture.

  [2] Archive of Formal Proofs, entry "The Sunflower Lemma of Erdős and
      Rado", René Thiemann, February 25, 2021,
      https://www.isa-afp.org/entries/Sunflowers.html — abstract, verbatim:

        "We formally define sunflowers and provide a formalization of the
        sunflower lemma of Erdős and Rado: whenever a set of size-k-sets has
        a larger cardinality than (r - 1)^k · k!, then it contains a
        sunflower of cardinality r."

  [3] Same entry, theory `Erdos_Rado_Sunflower.thy`, the headline lemma
      (https://www.isa-afp.org/browser_info/current/AFP/Sunflowers/Erdos_Rado_Sunflower.html),
      verbatim:

        lemma Erdos_Rado_sunflower_same_card:
          assumes "∀ A ∈ F. finite A ∧ card A = k"
            and "card F > (r - 1)^k * fact k"
          shows "∃ S. S ⊆ F ∧ sunflower S ∧ card S = r ∧ {} ∉ S"

      and its theory `Sunflower.thy` definition, verbatim:

        definition sunflower :: "'a set set ⇒ bool" where
          "sunflower S = (∀ x. (∃ A B. A ∈ S ∧ B ∈ S ∧ A ≠ B ∧
             x ∈ A ∧ x ∈ B)
            ⟶ (∀ A. A ∈ S ⟶ x ∈ A))"

      and, immediately after the "at most k" variant `Erdos_Rado_sunflower`,
      verbatim:

        text ‹Using @{thm [source] sunflower_card_subset_lift} we can easily
          replace the condition that the cardinality is exactly @{term k}
          by the requirement that the cardinality is at most @{term k}.
          However, then @{term "{} ∉ S"} cannot be ensured.
          Consider @{term "(r :: nat) = 1 ∧ (k :: nat) > 0 ∧ F = {{}}"}.›

  [4] Wikipedia, "Sunflower (mathematics)" (via `goof wiki article`), the
      induction that this file formalizes, verbatim (the article blanks the
      theorem environment holding the bound itself, so the bound is pinned
      from [2]/[3] above):

        "Specifically, researchers analyze the function $f(k,r)$ for
        nonnegative integers $k, r$, which is defined to be the smallest
        nonnegative integer $n$ such that, for any set system $W$ such that
        every set $S \in W$ has cardinality at most $k$, if $W$ has more
        than $n$ sets, then $W$ contains a sunflower of $r$ sets."

        "In the general case, suppose $W$ has no sunflower with $r$ sets.
        Then consider $A_1,A_2,\ldots,A_t \in W$ to be a maximal collection
        of pairwise disjoint sets (that is, $A_i \cap A_j$ is the empty set
        unless $i = j$, and every set in $W$ intersects with some $A_i$).
        Because we assumed that $W$ had no sunflower of size $r$, and a
        collection of pairwise disjoint sets is a sunflower, $t < r$."

        "Hence, if $|W| \ge k(r-1)f(k-1,r)$, then $W$ contains an $r$ set
        sunflower of size $k$ sets. Hence, $f(k,r) \le k(r-1)f(k-1,r)$ and
        the theorem follows."

  [5] OEIS A332077 (via `goof oeis show A332077`), name and the relevant
      comment/formula lines, verbatim:

        name: "Square array of sunflower numbers Sun(m,n) = minimal number
        of distinct sets of cardinality <= m such that there is a sunflower
        with at least n sets among them, read by falling antidiagonals;
        m, n >= 1."

        comment: "Some authors (e.g., Wikipedia) use \"more than\" instead
        of \"at least\" in the definition, which corresponds to an index n
        decreased by 1. We use the same conventions Tao (but following OEIS
        standards we use m,n instead of k,r). Also, some authors (e.g.,
        Abbott et al. and the Polymath wiki page) use f(k,r) = Sun(k,r) - 1
        which is not the minimal number of required sets, but such that any
        collection of *more than* f(k,r) sets has the given property."

        formula: "(n-1)^m <= Sun(m,n) <= (n-1)^m*m! + 1. (Erdös & Rado)"

        terms: "1,2,1,3,2,1,4,7,2,1,5,11,21,2,1,6,21"

      This is a third independent pin of the same bound (`m` = set size,
      `n` = petals): "at least (n-1)^m·m! + 1 sets" is "more than
      (n-1)^m·m! sets", which is the hypothesis of
      `erdos_rado_sunflower_same_card` below.  Numeric consistency check
      against the tabulated antidiagonals (Sun(m,n) ≤ (n-1)^m·m! + 1):
        Sun(1,n) = n           vs bound (n-1)·1! + 1 = n    (tight)
        Sun(2,3) = 7           vs bound 2^2·2! + 1 = 9
        Sun(2,4) = 11          vs bound 3^2·2! + 1 = 19
        Sun(2,5) = 21          vs bound 4^2·2! + 1 = 33
        Sun(3,3) = 21          vs bound 2^3·3! + 1 = 49
      all satisfied.  (A332077 uses the "cardinality ≤ m" convention, i.e.
      the AFP `Erdos_Rado_sunflower` variant of [3]; only the numeric bound
      formula is used here, not that convention — see below.)

  ══════════════════════════════════════════════════════════════════════
  CONVENTION CHECK: nonempty petals
  ══════════════════════════════════════════════════════════════════════

  `IsSunflowerWith sub K` in `Sunflower.lean` demands a *named* kernel and,
  unlike the AFP `sunflower` predicate of [3], demands nonempty petals:

      (∀ S ∈ sub, K ⊆ S) ∧ (∀ S ∈ sub, S \ K ≠ ∅) ∧
      (∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → S ∩ T = K)

  This is strictly stronger than AFP's `sunflower`.  It costs nothing here,
  and produces NO off-by-one against the textbook bound:

  • r ≥ 2, k-uniform.  If S ∈ sub had S \ K = ∅ then S ⊆ K, and clause 1
    gives K ⊆ T for every other T ∈ sub, so S ⊆ T; |S| = |T| = k then
    forces S = T, contradicting |sub| ≥ 2.  So the petals are automatically
    nonempty and the argument delivers the clause for free.
  • r = 1, k ≥ 1.  Take K = ∅; the single member has card k ≥ 1.
  • k = 0.  Vacuous: the bound reads (r-1)^0 · 0! = 1 < |F|, but the only
    0-set is ∅, so |F| ≤ 1.

  Note our clause is strictly stronger than AFP's `{} ∉ S` here, not a
  restatement of it: `{} ∉ S` carries no content in the *same_card* lemma
  (every member has card k, and k = 0 is vacuous), whereas `S \ K ≠ ∅` says
  the kernel is a *proper* subset of each petal-bearing member.  AFP states
  `{} ∉ S` only so that the "≤ k" lift can be attempted.

  Hence `erdos_rado_sunflower_same_card` below is the bound of [2]/[3]
  at the same threshold, with a strictly stronger sunflower notion
  (nonempty petals vs `{} ∉ S`) and on `Fin n` rather than an arbitrary
  type — see DEVIATION below.

  What the convention DOES cost is the "cardinality at most k" variant
  `Erdos_Rado_sunflower` of [3].  AFP flags that its `{} ∉ S` conclusion
  fails there and offers r = 1, k > 0, F = {{}} as the reason; under the
  nonempty-petal convention that same instance refutes the "≤ k" statement
  outright, which is machine-checked here as
  `not_hasSunflower_of_mem_empty` / `erdosRado_le_variant_fails`.
  Only the uniform statement is claimed.

  ══════════════════════════════════════════════════════════════════════
  GROUND TYPE
  ══════════════════════════════════════════════════════════════════════

  `Fin n` (as in the rest of `Erdos/Erdos20/`).  The Erdős–Rado induction
  descends on the uniformity k while the ambient ground set is untouched,
  so a fixed `Fin n` suffices and the existing `IsSunflowerWith`,
  `HasSunflower` definitions are reused verbatim — no polymorphic
  `DecidableEq α` restatement is needed.

  DEVIATION from [3]: the AFP lemma quantifies over an arbitrary HOL type
  with `finite A` per member; this file fixes a finite ground set `Fin n`
  and a `Finset` family.  Substantively this is not a loss (the AFP
  hypothesis `card F > …` already forces `F` finite, and a finite family of
  finite sets embeds into some `Fin n`), but that reduction is NOT
  formalized here, so the Lean statement is formally the `Fin n` instance
  of the AFP statement rather than its full generality.

  ══════════════════════════════════════════════════════════════════════
  NOVELTY
  ══════════════════════════════════════════════════════════════════════

  NOT a first formalization: [2]/[3] is exactly this theorem in
  Isabelle/HOL (AFP, 2021).  Mathlib as vendored here contains zero
  occurrences of the string "sunflower" (checked 2026-08-05 over
  `.lake/packages/mathlib/Mathlib/`), and the bound is not stated anywhere
  else in this repository, so this is a first-in-Lean candidate only.
  It is unrelated to Naslund–Sawin (Erdős #857), which bounds
  3-sunflower-free subfamilies of a power set.
-/

import Erdos.Erdos20.Sunflower
import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false

open Finset
open scoped Nat

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════
-- SUNFLOWER CONSTRUCTORS
-- ════════════════════════════════════════════════════════════════════

/-- A pairwise disjoint family of nonempty sets is a sunflower with empty
kernel. This is the AFP `pairwise_disjnt_imp_sunflower`, plus the
nonempty-petal side condition our `IsSunflowerWith` carries. -/
theorem isSunflowerWith_empty_of_pairwise_disjoint {sub : Finset (Finset (Fin n))}
    (hne : ∀ S ∈ sub, S ≠ ∅)
    (hdisj : ∀ S ∈ sub, ∀ T ∈ sub, S ≠ T → S ∩ T = ∅) :
    IsSunflowerWith sub ∅ :=
  ⟨fun S _ => Finset.empty_subset S,
   fun S hS => by simpa only [Finset.sdiff_empty] using hne S hS,
   hdisj⟩

/-- Adding a fresh element `y` to every member of a sunflower, and to its
kernel, again yields a sunflower. This is the AFP
`sunflower_remove_element_lift` read in the forward direction. -/
theorem IsSunflowerWith.image_insert {sub : Finset (Finset (Fin n))}
    {K : Finset (Fin n)} {y : Fin n} (hsf : IsSunflowerWith sub K)
    (hy : ∀ T ∈ sub, y ∉ T) :
    IsSunflowerWith (sub.image (insert y)) (insert y K) := by
  obtain ⟨hker, hpetal, hpair⟩ := hsf
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.insert_subset_insert y (hker T hT)
  · intro S hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    have hTy : y ∉ T := hy T hT
    have hEq : insert y T \ insert y K = T \ K := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨hx1 | hx1, hx2, hx3⟩
        · exact absurd hx1 hx2
        · exact ⟨hx1, hx3⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨Or.inr hx1, fun hxy => hTy (hxy ▸ hx1), hx2⟩
    rw [hEq]
    exact hpetal T hT
  · intro S hS T hT hne
    obtain ⟨S', hS', rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hT
    have hne' : S' ≠ T' := fun h => hne (by rw [h])
    have hdistrib : insert y S' ∩ insert y T' = insert y (S' ∩ T') := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      tauto
    rw [hdistrib, hpair S' hS' T' hT' hne']

/-- `insert y ·` is injective on a family none of whose members contain `y`,
so it preserves cardinality. -/
theorem card_image_insert_of_forall_notMem {sub : Finset (Finset (Fin n))}
    {y : Fin n} (hy : ∀ T ∈ sub, y ∉ T) :
    (sub.image (insert y)).card = sub.card := by
  refine Finset.card_image_of_injOn ?_
  intro A hA B hB hAB
  simp only [Finset.mem_coe] at hA hB
  calc A = (insert y A).erase y := (Finset.erase_insert (hy A hA)).symm
    _ = (insert y B).erase y := by rw [hAB]
    _ = B := Finset.erase_insert (hy B hB)

-- ════════════════════════════════════════════════════════════════════
-- THE ERDŐS–RADO SUNFLOWER LEMMA
-- ════════════════════════════════════════════════════════════════════

/-- **Erdős–Rado sunflower lemma** (successor form, free of `ℕ`-subtraction).

If every member of `family` has exactly `k` elements and
`k ! * q ^ k < family.card`, then `family` contains a sunflower with `q + 1`
petals.

Proof: induction on `k`. For `k = 0` the hypothesis reads `1 < family.card`
while the only `0`-set is `∅`. For `k + 1`, pick a pairwise disjoint
subfamily `M ⊆ family` of maximum cardinality. If `q + 1 ≤ M.card` then any
`q + 1` of its members form a sunflower with kernel `∅`. Otherwise
`M.card ≤ q`, so `Y := ⋃ M` has at most `q * (k + 1)` elements and — by
maximality — meets every member of `family`; pigeonhole supplies `y ∈ Y`
lying in more than `k ! * q ^ k` members, and the induction hypothesis
applied to `{S \ {y} : y ∈ S ∈ family}` yields a sunflower which lifts back
by re-inserting `y`. -/
theorem hasSunflower_succ_of_factorial_mul_pow_lt {q k : ℕ}
    (family : Finset (Finset (Fin n)))
    (huniform : ∀ S ∈ family, S.card = k)
    (hcard : k ! * q ^ k < family.card) :
    HasSunflower family (q + 1) := by
  classical
  induction k generalizing family with
  | zero =>
      exfalso
      have hsub : family ⊆ {∅} := by
        intro S hS
        rw [Finset.mem_singleton]
        exact Finset.card_eq_zero.mp (huniform S hS)
      have hle : family.card ≤ 1 := by
        simpa only [Finset.card_singleton] using Finset.card_le_card hsub
      rw [Nat.factorial_zero, pow_zero, Nat.mul_one] at hcard
      omega
  | succ k ih =>
      -- `P` collects the pairwise disjoint subfamilies of `family`.
      set P : Finset (Finset (Finset (Fin n))) :=
        family.powerset.filter (fun M => ∀ S ∈ M, ∀ T ∈ M, S ≠ T → S ∩ T = ∅) with hPdef
      have hPne : P.Nonempty := by
        refine ⟨∅, ?_⟩
        rw [hPdef, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.empty_subset _, by tauto⟩
      obtain ⟨M, hMP, hMmax⟩ := P.exists_max_image Finset.card hPne
      have hMmem := Finset.mem_filter.mp (hPdef ▸ hMP)
      have hMfam : M ⊆ family := Finset.mem_powerset.mp hMmem.1
      have hMdisj : ∀ S ∈ M, ∀ T ∈ M, S ≠ T → S ∩ T = ∅ := hMmem.2
      by_cases hbig : q + 1 ≤ M.card
      · -- Branch 1: a large pairwise disjoint subfamily is itself a sunflower.
        obtain ⟨sub, hsubM, hsubcard⟩ := Finset.exists_subset_card_eq hbig
        refine ⟨sub, hsubM.trans hMfam, hsubcard, ∅, ?_⟩
        refine isSunflowerWith_empty_of_pairwise_disjoint ?_ ?_
        · intro S hS
          have hScard : S.card = k + 1 := huniform S (hMfam (hsubM hS))
          intro hSempty
          rw [hSempty, Finset.card_empty] at hScard
          exact Nat.succ_ne_zero k hScard.symm
        · exact fun S hS T hT hne => hMdisj S (hsubM hS) T (hsubM hT) hne
      · -- Branch 2: `M` is small, so its union is a small transversal.
        rw [not_le] at hbig
        set Y : Finset (Fin n) := M.biUnion id with hYdef
        have hYcard : Y.card ≤ q * (k + 1) := by
          calc Y.card ≤ ∑ S ∈ M, (id S).card := Finset.card_biUnion_le
            _ = ∑ _S ∈ M, (k + 1) :=
                Finset.sum_congr rfl fun S hS => huniform S (hMfam hS)
            _ = M.card * (k + 1) := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ q * (k + 1) := Nat.mul_le_mul_right _ (by omega)
        have hmeet : ∀ S ∈ family, (S ∩ Y).Nonempty := by
          intro S hS
          rw [Finset.nonempty_iff_ne_empty]
          intro hSY
          have hSnotM : S ∉ M := by
            intro hSM
            have hSsub : S ⊆ Y := fun x hx => Finset.mem_biUnion.mpr ⟨S, hSM, hx⟩
            have hSempty : S = ∅ := by
              rw [← Finset.inter_eq_left.mpr hSsub]
              exact hSY
            have hScard : S.card = k + 1 := huniform S hS
            rw [hSempty, Finset.card_empty] at hScard
            exact Nat.succ_ne_zero k hScard.symm
          have hins : insert S M ∈ P := by
            rw [hPdef, Finset.mem_filter, Finset.mem_powerset]
            refine ⟨Finset.insert_subset hS hMfam, ?_⟩
            have hSdisj : ∀ B ∈ M, S ∩ B = ∅ := by
              intro B hB
              refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
              rw [Finset.mem_inter] at hx
              have hxSY : x ∈ S ∩ Y :=
                Finset.mem_inter.mpr ⟨hx.1, Finset.mem_biUnion.mpr ⟨B, hB, hx.2⟩⟩
              rw [hSY] at hxSY
              exact Finset.notMem_empty x hxSY
            intro A hA B hB hAB
            rcases Finset.mem_insert.mp hA with rfl | hA'
            · rcases Finset.mem_insert.mp hB with rfl | hB'
              · exact absurd rfl hAB
              · exact hSdisj B hB'
            · rcases Finset.mem_insert.mp hB with rfl | hB'
              · rw [Finset.inter_comm]
                exact hSdisj A hA'
              · exact hMdisj A hA' B hB' hAB
          have hcontra := hMmax _ hins
          rw [Finset.card_insert_of_notMem hSnotM] at hcontra
          omega
        -- Pigeonhole on `Y`.
        have hpigeon : ∃ y ∈ Y, k ! * q ^ k < (family.filter (fun S => y ∈ S)).card := by
          by_contra hcon
          simp only [not_exists, not_and, not_lt] at hcon
          have hcover : family ⊆ Y.biUnion (fun y => family.filter (fun S => y ∈ S)) := by
            intro S hS
            obtain ⟨x, hx⟩ := hmeet S hS
            rw [Finset.mem_inter] at hx
            exact Finset.mem_biUnion.mpr ⟨x, hx.2, Finset.mem_filter.mpr ⟨hS, hx.1⟩⟩
          have hbound : family.card ≤ (k + 1)! * q ^ (k + 1) := by
            calc family.card
                ≤ (Y.biUnion (fun y => family.filter (fun S => y ∈ S))).card :=
                  Finset.card_le_card hcover
              _ ≤ ∑ y ∈ Y, (family.filter (fun S => y ∈ S)).card := Finset.card_biUnion_le
              _ ≤ ∑ _y ∈ Y, k ! * q ^ k := Finset.sum_le_sum hcon
              _ = Y.card * (k ! * q ^ k) := by rw [Finset.sum_const, smul_eq_mul]
              _ ≤ (q * (k + 1)) * (k ! * q ^ k) := Nat.mul_le_mul_right _ hYcard
              _ = (k + 1)! * q ^ (k + 1) := by rw [Nat.factorial_succ]; ring
          exact absurd hcard (not_lt.mpr hbound)
        obtain ⟨y, _, hylarge⟩ := hpigeon
        -- Delete `y` and apply the induction hypothesis.
        set Fy : Finset (Finset (Fin n)) := family.filter (fun S => y ∈ S) with hFydef
        set F' : Finset (Finset (Fin n)) := Fy.image (fun S => S.erase y) with hF'def
        have hFymem : ∀ S : Finset (Fin n), S ∈ Fy ↔ S ∈ family ∧ y ∈ S := by
          intro S
          rw [hFydef, Finset.mem_filter]
        have hF'mem : ∀ T : Finset (Fin n), T ∈ F' ↔ ∃ S ∈ Fy, S.erase y = T := by
          intro T
          rw [hF'def, Finset.mem_image]
        have hyF : ∀ S ∈ Fy, y ∈ S := fun S hS => ((hFymem S).mp hS).2
        have hFyfam : ∀ S ∈ Fy, S ∈ family := fun S hS => ((hFymem S).mp hS).1
        have hF'card : F'.card = Fy.card := by
          rw [hF'def]
          refine Finset.card_image_of_injOn ?_
          intro A hA B hB hAB
          simp only [Finset.mem_coe] at hA hB
          have hAB' : A.erase y = B.erase y := hAB
          calc A = insert y (A.erase y) := (Finset.insert_erase (hyF A hA)).symm
            _ = insert y (B.erase y) := by rw [hAB']
            _ = B := Finset.insert_erase (hyF B hB)
        have hF'uniform : ∀ T ∈ F', T.card = k := by
          intro T hT
          obtain ⟨S, hS, rfl⟩ := (hF'mem T).mp hT
          rw [Finset.card_erase_of_mem (hyF S hS), huniform S (hFyfam S hS)]
          omega
        obtain ⟨sub', hsub'F', hsub'card, K, hsf'⟩ :=
          ih F' hF'uniform (by rw [hF'card]; exact hylarge)
        -- Lift the sunflower back by re-inserting `y`.
        have hynot : ∀ T ∈ sub', y ∉ T := by
          intro T hT
          obtain ⟨S, _, rfl⟩ := (hF'mem T).mp (hsub'F' hT)
          exact Finset.notMem_erase y S
        refine ⟨sub'.image (insert y), ?_, ?_, insert y K, hsf'.image_insert hynot⟩
        · intro T hT
          obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hT
          obtain ⟨S, hS, hSe⟩ := (hF'mem T').mp (hsub'F' hT')
          rw [← hSe, Finset.insert_erase (hyF S hS)]
          exact hFyfam S hS
        · rw [card_image_insert_of_forall_notMem hynot, hsub'card]

/-- **Erdős–Rado sunflower lemma**, in the shape of the AFP entry
`Erdos_Rado_sunflower_same_card`: a family of `k`-element sets with more
than `(r - 1) ^ k * k !` members contains a sunflower with `r` petals.

The `1 ≤ r` hypothesis keeps `r - 1` off the `ℕ`-subtraction junk value. -/
theorem erdos_rado_sunflower_same_card {k r : ℕ}
    (family : Finset (Finset (Fin n))) (hr : 1 ≤ r)
    (huniform : ∀ S ∈ family, S.card = k)
    (hcard : (r - 1) ^ k * k ! < family.card) :
    HasSunflower family r := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  refine hasSunflower_succ_of_factorial_mul_pow_lt family huniform ?_
  have hswap : (q + 1 - 1) ^ k * k ! = k ! * q ^ k := by
    rw [Nat.add_sub_cancel, Nat.mul_comm]
  rw [← hswap]
  exact hcard

-- ════════════════════════════════════════════════════════════════════
-- SATISFIABILITY AND SHARPNESS OF THE UNIFORMITY HYPOTHESIS
-- ════════════════════════════════════════════════════════════════════

/-- Satisfiability witness: every hypothesis of `erdos_rado_sunflower_same_card`
holds jointly at `n = 2`, `k = 1`, `r = 2`, `family = {{0}, {1}}`, where
`(2 - 1) ^ 1 * 1 ! = 1 < 2 = family.card`. -/
example : HasSunflower ({{0}, {1}} : Finset (Finset (Fin 2))) 2 :=
  erdos_rado_sunflower_same_card (k := 1) _ (by norm_num) (by decide) (by decide)

/-- Satisfiability witness at a larger uniformity: `n = 4`, `k = 2`, `r = 2`,
`family = {{0,1}, {0,2}, {1,2}}`, where `(2 - 1) ^ 2 * 2 ! = 2 < 3`. -/
example :
    HasSunflower ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 4))) 2 :=
  erdos_rado_sunflower_same_card (k := 2) _ (by norm_num) (by decide) (by decide)

/-- Satisfiability witness with more than two petals: `n = 3`, `k = 1`,
`r = 3`, `family = {{0}, {1}, {2}}`, where `(3 - 1) ^ 1 * 1 ! = 2 < 3`. -/
example : HasSunflower ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) 3 :=
  erdos_rado_sunflower_same_card (k := 1) _ (by norm_num) (by decide) (by decide)

/-- Non-vacuity of the conclusion: `HasSunflower · 3` genuinely fails on a
nondegenerate uniform family.  The triangle `{{0,1}, {1,2}, {0,2}}` is
`2`-uniform with three members, but its three pairwise intersections are
`{1}`, `{2}`, `{0}` — no common kernel — so it carries no `3`-petal
sunflower.  (Consistently, it is far below the Erdős–Rado threshold
`(3 - 1) ^ 2 * 2 ! = 8` for `k = 2`, `r = 3`.) -/
theorem not_hasSunflower_triangle :
    ¬ HasSunflower ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 3))) 3 := by
  rintro ⟨sub, hsub, hcard, K, -, -, hpair⟩
  have hsubeq : sub = ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset (Fin 3))) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
  subst hsubeq
  have h1 : ({0, 1} : Finset (Fin 3)) ∩ ({1, 2} : Finset (Fin 3)) = K :=
    hpair _ (by decide) _ (by decide) (by decide)
  have h2 : ({0, 1} : Finset (Fin 3)) ∩ ({0, 2} : Finset (Fin 3)) = K :=
    hpair _ (by decide) _ (by decide) (by decide)
  rw [← h1] at h2
  exact absurd h2 (by decide)

/-- Under the nonempty-petal convention of `IsSunflowerWith`, a family whose
only member is `∅` has no `1`-petal sunflower: the kernel is forced to be `∅`
and the petal `∅ \ ∅` is then empty. -/
theorem not_hasSunflower_of_mem_empty :
    ¬ HasSunflower ({∅} : Finset (Finset (Fin 1))) 1 := by
  rintro ⟨sub, hsub, hcard, K, _, hpetal, -⟩
  obtain ⟨S, rfl⟩ := Finset.card_eq_one.mp hcard
  have hS0 : S = ∅ := Finset.mem_singleton.mp (hsub (Finset.mem_singleton_self S))
  have hSK : S \ K ≠ ∅ := hpetal S (Finset.mem_singleton_self S)
  rw [hS0] at hSK
  exact hSK (Finset.empty_sdiff K)

/-- The AFP "cardinality at most `k`" variant `Erdos_Rado_sunflower` is a true
theorem in Isabelle/HOL, but only because it drops the `{} ∉ S` conclusion.
Transcribed onto `IsSunflowerWith`, whose nonempty-petal clause cannot be
dropped, it becomes FALSE — refuted at exactly the instance the AFP text
flags as the reason for dropping `{} ∉ S` there: `r = 1`, `k = 1`, `F = {∅}`.
Every hypothesis of the "≤ k" statement holds — `∅` has card `≤ 1`, and
`(1 - 1) ^ 1 * 1 ! = 0 < 1 = F.card` — yet the conclusion fails.  This is why
only the uniform statement is claimed in this file. -/
theorem erdosRado_le_variant_fails :
    ¬ ∀ (m k r : ℕ) (family : Finset (Finset (Fin m))), 1 ≤ r →
        (∀ S ∈ family, S.card ≤ k) → (r - 1) ^ k * k ! < family.card →
        HasSunflower family r := by
  intro h
  refine not_hasSunflower_of_mem_empty (h 1 1 1 {∅} le_rfl ?_ ?_)
  · intro S hS
    rw [Finset.mem_singleton.mp hS, Finset.card_empty]
    exact Nat.zero_le 1
  · decide

-- ════════════════════════════════════════════════════════════════════
-- SIGNATURE AUDIT (the file declares `variable {n : ℕ}`)
-- ════════════════════════════════════════════════════════════════════

#check @isSunflowerWith_empty_of_pairwise_disjoint
#check @IsSunflowerWith.image_insert
#check @card_image_insert_of_forall_notMem
#check @hasSunflower_succ_of_factorial_mul_pow_lt
#check @erdos_rado_sunflower_same_card
#check @not_hasSunflower_triangle
#check @not_hasSunflower_of_mem_empty
#check @erdosRado_le_variant_fails

-- ════════════════════════════════════════════════════════════════════
-- AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════════

#print axioms isSunflowerWith_empty_of_pairwise_disjoint
#print axioms IsSunflowerWith.image_insert
#print axioms card_image_insert_of_forall_notMem
#print axioms hasSunflower_succ_of_factorial_mul_pow_lt
#print axioms erdos_rado_sunflower_same_card
#print axioms not_hasSunflower_triangle
#print axioms not_hasSunflower_of_mem_empty
#print axioms erdosRado_le_variant_fails
