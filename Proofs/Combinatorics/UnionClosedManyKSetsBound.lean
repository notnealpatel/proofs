/-
# Union-closed families with more than `C(n,k)` `k`-sets (sharp Petrov bound)

Amir Jafari, *On union-closed families with prescribed number of k-sets*,
arXiv:2609.11358 (2026), Theorem 1.2 (`thm:first-threshold`, Section 1.1),
proves that for `n ≥ k ≥ 1`, a finite union-closed family with more than
`binom(n,k)` distinct `k`-sets has at least `n-k+3` members of size at
least `n`, and that the bound is attained with `binom(n,k)+1` `k`-sets.
The proof is in Section 2. The weaker bound 3 is Fedor Petrov's
IMC 2016 problem. Both the bound and sharpness are formalized below.

## Formalization

* `F : Finset (Finset α)` is a finite family of finite sets; union-closedness is
  `IsUnionClosed`.  The `k`-sets of `F` are `F.filter (·.card = k)` and the large
  members are `F.filter (n ≤ ·.card)`.
* The proof follows the paper: induction on `k` through the generator form
  `exists_large_isGenUnion`.  If some `V_x` (union of generators avoiding `x`)
  has fewer than `n` points, delete `x` from the generators through `x` and
  induct; otherwise `supp 𝒜` and the distinct `V_x` give the large unions, and
  the class-label multiset injection gives `|𝒜| ≤ C(q + k - 1, k)`.
* The sharpness family `sharpFamily n k` is not the paper's union-closure of
  `binom([n],k) ∪ {[k-1] ∪ {n+1}}` but a union-closed superfamily on `{0,…,n}`
  with the same `k`-sets and the same large members.
-/
import Mathlib

set_option autoImplicit false

namespace UnionClosedManyKSetsBound

open Finset

variable {α : Type*} [DecidableEq α]

/-- A family `F` of finite sets is *union-closed* if `A ∪ B ∈ F` whenever `A, B ∈ F`. -/
def IsUnionClosed (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- `S` is the union of a nonempty subfamily of `𝒜`, in covering form: some member of `𝒜`
lies inside `S`, and every point of `S` lies in a member of `𝒜` contained in `S`. -/
def IsGenUnion (𝒜 : Finset (Finset α)) (S : Finset α) : Prop :=
  (∃ A ∈ 𝒜, A ⊆ S) ∧ ∀ y ∈ S, ∃ A ∈ 𝒜, A ⊆ S ∧ y ∈ A

/-- The union `V_x` of the members of `𝒜` avoiding the point `x`. -/
def unionAvoiding (𝒜 : Finset (Finset α)) (x : α) : Finset α :=
  (𝒜.filter (fun A => x ∉ A)).sup id

/-- The union of a nonempty subfamily `ℬ ⊆ 𝒜` is a generated union of `𝒜`. -/
theorem isGenUnion_sup {𝒜 ℬ : Finset (Finset α)} (hsub : ℬ ⊆ 𝒜) (hne : ℬ.Nonempty) :
    IsGenUnion 𝒜 (ℬ.sup id) := by
  obtain ⟨B, hB⟩ := hne
  refine ⟨⟨B, hsub hB, le_sup (f := id) hB⟩, fun y hy => ?_⟩
  obtain ⟨C, hC, hyC⟩ := mem_sup.1 hy
  exact ⟨C, hsub hC, le_sup (f := id) hC, hyC⟩

/-- It holds exactly when `S` is the union of a nonempty
subfamily of `𝒜`. -/
theorem isGenUnion_iff (𝒜 : Finset (Finset α)) (S : Finset α) :
    IsGenUnion 𝒜 S ↔ ∃ 𝒢 ⊆ 𝒜, 𝒢.Nonempty ∧ 𝒢.sup id = S := by
  constructor
  · rintro ⟨⟨A, hA, hAS⟩, hcov⟩
    refine ⟨𝒜.filter (· ⊆ S), filter_subset _ _, ⟨A, mem_filter.2 ⟨hA, hAS⟩⟩, ?_⟩
    apply le_antisymm
    · exact Finset.sup_le fun B hB => (mem_filter.1 hB).2
    · intro y hy
      obtain ⟨B, hB, hBS, hyB⟩ := hcov y hy
      exact mem_sup.2 ⟨B, mem_filter.2 ⟨hB, hBS⟩, hyB⟩
  · rintro ⟨𝒢, h𝒢, hne, rfl⟩
    exact isGenUnion_sup h𝒢 hne

/-- A generated union of `𝒜 ⊆ F` lies in `F` when `F` is union-closed. -/
theorem mem_of_isGenUnion {F 𝒜 : Finset (Finset α)} (hF : IsUnionClosed F) (h𝒜 : 𝒜 ⊆ F)
    {S : Finset α} (hS : IsGenUnion 𝒜 S) : S ∈ F := by
  obtain ⟨𝒢, h𝒢, hne, rfl⟩ := (isGenUnion_iff 𝒜 S).1 hS
  rw [← sup'_eq_sup hne]
  exact sup'_mem (F : Set (Finset α)) (fun A hA B hB => hF A hA B hB) 𝒢 hne id
    fun A hA => h𝒜 (h𝒢 hA)

/-- The point `x` does not lie in `V_x`. -/
theorem not_mem_unionAvoiding (𝒜 : Finset (Finset α)) (x : α) : x ∉ unionAvoiding 𝒜 x := by
  intro hx
  obtain ⟨A, hA, hxA⟩ := mem_sup.1 hx
  exact (mem_filter.1 hA).2 hxA

/-- Points with the same `V_·` lie in the same members of `𝒜`. -/
theorem mem_of_unionAvoiding_eq {𝒜 : Finset (Finset α)} {y z : α}
    (h : unionAvoiding 𝒜 z = unionAvoiding 𝒜 y) {C : Finset α} (hC : C ∈ 𝒜) (hz : z ∈ C) :
    y ∈ C := by
  by_contra hy
  have hCsub : C ⊆ unionAvoiding 𝒜 y := le_sup (f := id) (mem_filter.2 ⟨hC, hy⟩)
  exact not_mem_unionAvoiding 𝒜 z (h ▸ hCsub hz)

/-- Class-counting bound: if all members of `𝒜` are `k`-sets, then `|𝒜|` is at most the number
`C(q + k - 1, k)` of size-`k` multisets on the `q` distinct sets `V_x`, `x ∈ supp 𝒜`. -/
theorem card_le_choose_card_unionAvoiding {𝒜 : Finset (Finset α)} {k : ℕ}
    (hcard : ∀ A ∈ 𝒜, A.card = k) :
    𝒜.card ≤ (((𝒜.sup id).image (unionAvoiding 𝒜)).card + k - 1).choose k := by
  set V := 𝒜.sup id with hV
  set Q := V.image (unionAvoiding 𝒜) with hQ
  let cls : ∀ A ∈ 𝒜, A → Q := fun A hA y =>
    ⟨unionAvoiding 𝒜 y.1, mem_image_of_mem _ (le_sup (f := id) hA y.2)⟩
  let f : 𝒜 → Sym Q k := fun A =>
    ⟨(Finset.attach A.1).val.map (cls A.1 A.2), by
      rw [Multiset.card_map, Finset.card_val, Finset.card_attach, hcard A.1 A.2]⟩
  have hinj : Function.Injective f := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩ hAB
    have hval : (Finset.attach A).val.map (cls A hA) = (Finset.attach B).val.map (cls B hB) :=
      congrArg Subtype.val hAB
    have key : ∀ (A B : Finset α) (hA : A ∈ 𝒜) (hB : B ∈ 𝒜),
        (Finset.attach A).val.map (cls A hA) = (Finset.attach B).val.map (cls B hB) → A ⊆ B := by
      intro A B hA hB h y hy
      have hmem : cls A hA ⟨y, hy⟩ ∈ (Finset.attach B).val.map (cls B hB) :=
        h ▸ Multiset.mem_map_of_mem _ (mem_attach A ⟨y, hy⟩)
      obtain ⟨⟨z, hz⟩, -, hzy⟩ := Multiset.mem_map.1 hmem
      exact mem_of_unionAvoiding_eq (congrArg Subtype.val hzy) hB hz
    have hsub : A ⊆ B := key A B hA hB hval
    have hcardAB : B.card ≤ A.card := by rw [hcard A hA, hcard B hB]
    exact Subtype.ext (eq_of_subset_of_card_le hsub hcardAB)
  have hle := Fintype.card_le_of_injective f hinj
  rw [Sym.card_sym_eq_choose, Fintype.card_coe, Fintype.card_coe] at hle
  exact hle

/-- Second case of the proof: if every `V_x` with `x ∈ supp 𝒜` has at least `n` points, then the
support `V` together with the distinct sets `V_x` gives `n - k + 3` large generated unions. -/
theorem exists_of_forall_le_card_unionAvoiding {𝒜 : Finset (Finset α)} {k n : ℕ}
    (hn : 1 ≤ n) (hkn : k ≤ n) (hcard : ∀ A ∈ 𝒜, A.card = k) (hlt : n.choose k < 𝒜.card)
    (hlarge : ∀ x ∈ 𝒜.sup id, n ≤ (unionAvoiding 𝒜 x).card) :
    ∃ 𝒮 : Finset (Finset α), n - k + 3 ≤ 𝒮.card ∧ ∀ S ∈ 𝒮, n ≤ S.card ∧ IsGenUnion 𝒜 S := by
  set V := 𝒜.sup id with hV
  set Q := V.image (unionAvoiding 𝒜) with hQ
  have hQbound : n < Q.card + k - 1 := by
    by_contra hcon
    have h1 : (Q.card + k - 1).choose k ≤ n.choose k := Nat.choose_le_choose k (by omega)
    have h2 : 𝒜.card ≤ (Q.card + k - 1).choose k := card_le_choose_card_unionAvoiding hcard
    omega
  have hVQ : V ∉ Q := by
    intro hVQ
    obtain ⟨x, hx, hxV⟩ := mem_image.1 hVQ
    exact not_mem_unionAvoiding 𝒜 x (hxV ▸ hx)
  have hQne : Q.Nonempty := by
    rw [← card_pos]
    omega
  obtain ⟨W, hW⟩ := hQne
  obtain ⟨x0, hx0, -⟩ := mem_image.1 hW
  have hVlarge : n ≤ V.card :=
    (hlarge x0 hx0).trans (card_le_card (sup_mono (filter_subset _ _)))
  refine ⟨insert V Q, ?_, ?_⟩
  · rw [card_insert_of_notMem hVQ]
    omega
  · intro S hS
    rcases mem_insert.1 hS with rfl | hSQ
    · refine ⟨hVlarge, isGenUnion_sup (subset_refl _) ?_⟩
      rw [← card_pos]
      exact lt_of_le_of_lt (Nat.zero_le _) hlt
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hSQ
      refine ⟨hlarge x hx, isGenUnion_sup (filter_subset _ _) ?_⟩
      by_contra hempty
      rw [not_nonempty_iff_eq_empty] at hempty
      have h0 := hlarge x hx
      rw [unionAvoiding, hempty, sup_empty] at h0
      rw [bot_eq_empty, card_empty] at h0
      omega

/-- If every point of `S` avoids `x` in the sense of the erased family, then reinserting `x`
turns a generated union of `{A \ {x} : x ∈ A ∈ 𝒜}` into a generated union of `𝒜`. -/
theorem isGenUnion_insert {𝒜 : Finset (Finset α)} {x : α} {S : Finset α}
    (hS : IsGenUnion ((𝒜.filter (fun A => x ∈ A)).image (fun A => A.erase x)) S) :
    x ∉ S ∧ IsGenUnion 𝒜 (insert x S) := by
  obtain ⟨⟨B, hB, hBS⟩, hcov⟩ := hS
  have hlift : ∀ B ∈ (𝒜.filter (fun A => x ∈ A)).image (fun A => A.erase x), B ⊆ S →
      ∃ A ∈ 𝒜, A ⊆ insert x S ∧ B ⊆ A := by
    intro B hB hBS
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    obtain ⟨hA𝒜, hxA⟩ := mem_filter.1 hA
    refine ⟨A, hA𝒜, ?_, erase_subset _ _⟩
    intro y hy
    by_cases hyx : y = x
    · exact hyx ▸ mem_insert_self _ _
    · exact mem_insert_of_mem (hBS (mem_erase.2 ⟨hyx, hy⟩))
  refine ⟨?_, ?_, ?_⟩
  · intro hxS
    obtain ⟨C, hC, -, hxC⟩ := hcov x hxS
    obtain ⟨A, -, rfl⟩ := mem_image.1 hC
    exact (notMem_erase x A) hxC
  · obtain ⟨A, hA, hAS, -⟩ := hlift B hB hBS
    exact ⟨A, hA, hAS⟩
  · intro y hy
    rcases mem_insert.1 hy with rfl | hyS
    · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      obtain ⟨hA𝒜, hxA⟩ := mem_filter.1 hA
      refine ⟨A, hA𝒜, ?_, hxA⟩
      intro z hz
      by_cases hzx : z = y
      · exact hzx ▸ mem_insert_self _ _
      · exact mem_insert_of_mem (hBS (mem_erase.2 ⟨hzx, hz⟩))
    · obtain ⟨C, hC, hCS, hyC⟩ := hcov y hyS
      obtain ⟨A, hA, hAS, hCA⟩ := hlift C hC hCS
      exact ⟨A, hA, hAS, hCA hyC⟩

/-- Generator form of Theorem 1.2: if `𝒜` consists of more than `C(n, k)` distinct `k`-sets with
`k ≤ n`, then at least `n - k + 3` distinct unions of nonempty subfamilies of `𝒜` have at least
`n` points.  (For `k = 0` the hypothesis is never satisfied.) -/
theorem exists_large_isGenUnion :
    ∀ (k n : ℕ) (𝒜 : Finset (Finset α)), k ≤ n → (∀ A ∈ 𝒜, A.card = k) →
      n.choose k < 𝒜.card →
      ∃ 𝒮 : Finset (Finset α), n - k + 3 ≤ 𝒮.card ∧ ∀ S ∈ 𝒮, n ≤ S.card ∧ IsGenUnion 𝒜 S
  | 0, n, 𝒜, _, hcard, hlt => by
    exfalso
    have hsub : 𝒜 ⊆ {∅} := fun A hA => mem_singleton.2 (card_eq_zero.1 (hcard A hA))
    have h1 := card_le_card hsub
    rw [card_singleton, Nat.choose_zero_right] at *
    omega
  | k + 1, n, 𝒜, hkn, hcard, hlt => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    by_cases hsmall : ∃ x, (unionAvoiding 𝒜 x).card < m + 1
    · -- First case: many generators pass through `x`; delete `x` and induct.
      obtain ⟨x, hx⟩ := hsmall
      set 𝒜x := 𝒜.filter (fun A => x ∈ A) with h𝒜x
      set ℬ := 𝒜x.image (fun A => A.erase x) with hℬ
      have hsplit : 𝒜x.card + (𝒜.filter (fun A => x ∉ A)).card = 𝒜.card :=
        card_filter_add_card_filter_not _
      have havoid : (𝒜.filter (fun A => x ∉ A)).card ≤ m.choose (k + 1) := by
        have hsub : 𝒜.filter (fun A => x ∉ A) ⊆ (unionAvoiding 𝒜 x).powersetCard (k + 1) := by
          intro A hA
          exact mem_powersetCard.2 ⟨le_sup (f := id) hA, hcard A (mem_filter.1 hA).1⟩
        calc (𝒜.filter (fun A => x ∉ A)).card
            ≤ ((unionAvoiding 𝒜 x).powersetCard (k + 1)).card := card_le_card hsub
          _ = (unionAvoiding 𝒜 x).card.choose (k + 1) := card_powersetCard _ _
          _ ≤ m.choose (k + 1) := Nat.choose_le_choose _ (by omega)
      have hinj : Set.InjOn (fun A : Finset α => A.erase x) (𝒜x : Set (Finset α)) := by
        intro A hA B hB hAB
        rw [← insert_erase (mem_filter.1 hA).2, ← insert_erase (mem_filter.1 hB).2]
        exact congrArg (insert x) hAB
      have hℬcard : ℬ.card = 𝒜x.card := card_image_of_injOn hinj
      have hpascal : (m + 1).choose (k + 1) = m.choose k + m.choose (k + 1) :=
        Nat.choose_succ_succ m k
      have hℬlt : m.choose k < ℬ.card := by omega
      have hℬk : ∀ B ∈ ℬ, B.card = k := by
        intro B hB
        obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
        rw [card_erase_of_mem (mem_filter.1 hA).2, hcard A (mem_filter.1 hA).1]
        rfl
      obtain ⟨𝒮, h𝒮card, h𝒮⟩ := exists_large_isGenUnion k m ℬ (by omega) hℬk hℬlt
      have hins : Set.InjOn (insert x) (𝒮 : Set (Finset α)) := by
        intro S hS T hT hST
        have hxS := (isGenUnion_insert (h𝒮 S hS).2).1
        have hxT := (isGenUnion_insert (h𝒮 T hT).2).1
        rw [← erase_insert hxS, ← erase_insert hxT]
        exact congrArg (fun U => U.erase x) hST
      refine ⟨𝒮.image (insert x), ?_, ?_⟩
      · rw [card_image_of_injOn hins]
        omega
      · intro U hU
        obtain ⟨S, hS, rfl⟩ := mem_image.1 hU
        obtain ⟨hxS, hgen⟩ := isGenUnion_insert (h𝒮 S hS).2
        refine ⟨?_, hgen⟩
        rw [card_insert_of_notMem hxS]
        exact Nat.succ_le_succ (h𝒮 S hS).1
    · -- Second case: every `V_x` is large; count the classes.
      push Not at hsmall
      exact exists_of_forall_le_card_unionAvoiding (by omega) hkn hcard hlt
        fun x _ => hsmall x

/-- **Theorem 1.2 (first threshold), bound, without the hypothesis `1 ≤ k`.** If a union-closed
family `F` of finite sets contains more than `C(n, k)` distinct `k`-sets, where `k ≤ n`, then `F`
has at least `n - k + 3` members of cardinality at least `n`. -/
theorem le_card_filter_le_of_choose_lt (F : Finset (Finset α)) (hF : IsUnionClosed F)
    {n k : ℕ} (hkn : k ≤ n) (hN : n.choose k < (F.filter (fun A => A.card = k)).card) :
    n - k + 3 ≤ (F.filter (fun A => n ≤ A.card)).card := by
  set 𝒜 := F.filter (fun A => A.card = k) with h𝒜
  obtain ⟨𝒮, h𝒮card, h𝒮⟩ :=
    exists_large_isGenUnion k n 𝒜 hkn (fun A hA => (mem_filter.1 hA).2) hN
  have hsub : 𝒮 ⊆ F.filter (fun A => n ≤ A.card) := by
    intro S hS
    exact mem_filter.2 ⟨mem_of_isGenUnion hF (filter_subset _ _) (h𝒮 S hS).2, (h𝒮 S hS).1⟩
  exact h𝒮card.trans (card_le_card hsub)

/-- **Theorem 1.2 of Jafari (arXiv:2609.11358), bound.** Let `n ≥ k ≥ 1`. If a union-closed family `F`
of finite sets contains more than `C(n, k)` distinct `k`-sets, then `|F_{≥ n}| ≥ n - k + 3`,
i.e. `F` has at least `n - k + 3` members of cardinality at least `n`. -/
theorem thm_1_2 (F : Finset (Finset α)) (hF : IsUnionClosed F) {n k : ℕ} (_hk : 1 ≤ k)
    (hkn : k ≤ n) (hN : n.choose k < (F.filter (fun A => A.card = k)).card) :
    n - k + 3 ≤ (F.filter (fun A => n ≤ A.card)).card :=
  le_card_filter_le_of_choose_lt F hF hkn hN

/-- The extremal family for Theorem 1.2 (on the ground set `{0, …, n}`): the subsets `S` of
`{0, …, n}` that either avoid `n` and have at least `k` points, or contain `n` together with
`{0, …, k - 2}`.  Its `k`-sets are the `k`-subsets of `{0, …, n - 1}` and `{0, …, k - 2, n}`. -/
def sharpFamily (n k : ℕ) : Finset (Finset ℕ) :=
  (range (n + 1)).powerset.filter
    (fun S => (n ∉ S ∧ k ≤ S.card) ∨ (n ∈ S ∧ range (k - 1) ⊆ S))

/-- The extremal family is union-closed. -/
theorem isUnionClosed_sharpFamily (n k : ℕ) : IsUnionClosed (sharpFamily n k) := by
  intro S hS T hT
  simp only [sharpFamily, mem_filter, mem_powerset] at hS hT ⊢
  refine ⟨union_subset hS.1 hT.1, ?_⟩
  rcases hS.2 with ⟨hnS, hkS⟩ | ⟨hnS, hrS⟩
  · rcases hT.2 with ⟨hnT, hkT⟩ | ⟨hnT, hrT⟩
    · exact Or.inl ⟨by simp [hnS, hnT], hkS.trans (card_le_card subset_union_left)⟩
    · exact Or.inr ⟨mem_union_right _ hnT, hrT.trans subset_union_right⟩
  · exact Or.inr ⟨mem_union_left _ hnS, hrS.trans subset_union_left⟩

/-- The `k`-sets of the extremal family are the `k`-subsets of `{0, …, n - 1}` together with
`{0, …, k - 2, n}`. -/
theorem filter_card_eq_sharpFamily {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (sharpFamily n k).filter (fun A => A.card = k) =
      insert (insert n (range (k - 1))) ((range n).powersetCard k) := by
  have hn : n ∉ range (k - 1) := by rw [mem_range]; omega
  have hcardI : (insert n (range (k - 1))).card = k := by
    rw [card_insert_of_notMem hn, card_range]; omega
  ext S
  simp only [sharpFamily, mem_filter, mem_powerset, mem_insert, mem_powersetCard]
  constructor
  · rintro ⟨⟨hSsub, hS⟩, hSk⟩
    rcases hS with ⟨hnS, -⟩ | ⟨hnS, hrS⟩
    · right
      refine ⟨fun y hy => ?_, hSk⟩
      have hy' := mem_range.1 (hSsub hy)
      have hyn : y ≠ n := fun h => hnS (h ▸ hy)
      exact mem_range.2 (by omega)
    · left
      symm
      exact eq_of_subset_of_card_le (insert_subset hnS hrS) (by rw [hSk, hcardI])
  · rintro (rfl | ⟨hSsub, hSk⟩)
    · refine ⟨⟨insert_subset (mem_range.2 (by omega)) ?_, Or.inr ⟨mem_insert_self _ _,
        subset_insert _ _⟩⟩, hcardI⟩
      exact range_subset_range.2 (by omega)
    · refine ⟨⟨hSsub.trans (range_subset_range.2 (by omega)), Or.inl ⟨?_, hSk.ge⟩⟩, hSk⟩
      intro hnS
      exact (mem_range.1 (hSsub hnS)).false

/-- The extremal family contains exactly `C(n, k) + 1` distinct `k`-sets. -/
theorem card_filter_card_eq_sharpFamily {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((sharpFamily n k).filter (fun A => A.card = k)).card = n.choose k + 1 := by
  rw [filter_card_eq_sharpFamily hk hkn, card_insert_of_notMem, card_powersetCard, card_range]
  intro hmem
  have hsub := (mem_powersetCard.1 hmem).1 (mem_insert_self n (range (k - 1)))
  exact (mem_range.1 hsub).false

/-- The large members of the extremal family are among `{0, …, n}` and the sets
`{0, …, n} \ {y}` with `k - 1 ≤ y ≤ n`. -/
theorem filter_le_card_sharpFamily_subset {n k : ℕ} (hkn : k ≤ n) :
    (sharpFamily n k).filter (fun A => n ≤ A.card) ⊆
      insert (range (n + 1)) ((Ico (k - 1) (n + 1)).image fun y => (range (n + 1)).erase y) := by
  intro S hS
  simp only [sharpFamily, mem_filter, mem_powerset] at hS
  obtain ⟨⟨hSsub, hS⟩, hSn⟩ := hS
  by_cases hfull : range (n + 1) ⊆ S
  · exact mem_insert.2 (Or.inl (subset_antisymm hSsub hfull))
  · obtain ⟨y, hy, hyS⟩ := not_subset.1 hfull
    have hSy : S ⊆ (range (n + 1)).erase y := fun z hz =>
      mem_erase.2 ⟨fun h => hyS (h ▸ hz), hSsub hz⟩
    have hSeq : S = (range (n + 1)).erase y := by
      refine eq_of_subset_of_card_le hSy ?_
      rw [card_erase_of_mem hy, card_range]
      omega
    refine mem_insert.2 (Or.inr (mem_image.2 ⟨y, mem_Ico.2 ⟨?_, mem_range.1 hy⟩, hSeq.symm⟩))
    by_contra hlt
    push Not at hlt
    have hyn : y ≠ n := by omega
    have hnS : n ∈ S := by
      rw [hSeq]
      exact mem_erase.2 ⟨hyn.symm, self_mem_range_succ n⟩
    rcases hS with ⟨hnS', -⟩ | ⟨-, hrS⟩
    · exact hnS' hnS
    · exact hyS (hrS (mem_range.2 hlt))

/-- **Theorem 1.2 of Jafari (arXiv:2609.11358), sharpness.** For `n ≥ k ≥ 1` there is a
union-closed family of finite sets containing exactly `C(n, k) + 1` distinct `k`-sets and exactly
`n - k + 3` members of cardinality at least `n`. -/
theorem thm_1_2_sharp {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ F : Finset (Finset ℕ), IsUnionClosed F ∧
      (F.filter (fun A => A.card = k)).card = n.choose k + 1 ∧
      (F.filter (fun A => n ≤ A.card)).card = n - k + 3 := by
  refine ⟨sharpFamily n k, isUnionClosed_sharpFamily n k,
    card_filter_card_eq_sharpFamily hk hkn, le_antisymm ?_ ?_⟩
  · calc ((sharpFamily n k).filter (fun A => n ≤ A.card)).card
        ≤ (insert (range (n + 1))
            ((Ico (k - 1) (n + 1)).image fun y => (range (n + 1)).erase y)).card :=
          card_le_card (filter_le_card_sharpFamily_subset hkn)
      _ ≤ ((Ico (k - 1) (n + 1)).image fun y => (range (n + 1)).erase y).card + 1 :=
          card_insert_le _ _
      _ ≤ (Ico (k - 1) (n + 1)).card + 1 := Nat.add_le_add_right card_image_le 1
      _ = n - k + 3 := by rw [Nat.card_Ico]; omega
  · apply thm_1_2 _ (isUnionClosed_sharpFamily n k) hk hkn
    rw [card_filter_card_eq_sharpFamily hk hkn]
    exact Nat.lt_succ_self _

/-! ### Examples on small instances -/

example : IsUnionClosed ({{0}, {1}, {0, 1}} : Finset (Finset ℕ)) := by
  unfold IsUnionClosed; decide

example : ¬ IsUnionClosed ({{0}, {1}} : Finset (Finset ℕ)) := by
  unfold IsUnionClosed; decide

example : IsGenUnion ({{0}, {1}, {2}} : Finset (Finset ℕ)) {0, 2} := by
  unfold IsGenUnion; decide

example : ¬ IsGenUnion ({{0, 1}, {1, 2}} : Finset (Finset ℕ)) {0, 2} := by
  unfold IsGenUnion; decide

example : unionAvoiding ({{0, 1}, {1, 2}, {0, 2}} : Finset (Finset ℕ)) 0 = {1, 2} := by
  decide

/-- At `n = 2`, `k = 1`: the extremal family has `C(2,1) + 1 = 3` singletons. -/
example : ((sharpFamily 2 1).filter (fun A => A.card = 1)).card = 3 := by decide

/-- At `n = 2`, `k = 1`: the extremal family has `2 - 1 + 3 = 4` members of size `≥ 2`. -/
example : ((sharpFamily 2 1).filter (fun A => 2 ≤ A.card)).card = 4 := by decide

/-- At `n = 3`, `k = 2` the hypotheses of Theorem 1.2 hold jointly (non-vacuity). -/
example : IsUnionClosed (sharpFamily 3 2) ∧
    (3 : ℕ).choose 2 < ((sharpFamily 3 2).filter (fun A => A.card = 2)).card :=
  ⟨isUnionClosed_sharpFamily 3 2, by decide⟩

/-- At `n = 3`, `k = 2` the bound `3 - 2 + 3 = 4` is attained. -/
example : ((sharpFamily 3 2).filter (fun A => 3 ≤ A.card)).card = 4 := by decide

end UnionClosedManyKSetsBound
