/-
Higher commuting probabilities of finite groups.

Formalization of elementary propositions from

  Vadim E. Levit, Robert Shwartz,
  "Higher Commutativity in Finite Groups: Exact Asymptotics and Finite Spectrum",
  arXiv:2605.02071 (2026).

The `r`-th higher commuting probability of a finite group `G` is

  `P_r(G) = |{ (g_1,…,g_r) ∈ G^r : g_i g_j = g_j g_i for all i,j }| / |G|^r`,

generalizing Mathlib's `commProb` (the case `r = 2`).  We formalize:

* `higherCommProb_prod` (Prop. 2.13, direct products): `P_r(G × H) = P_r(G) * P_r(H)`.
* `higherCommProb_succ_le` (Prop. 2.11, monotonicity in `r`): `P_{r+1}(G) ≤ P_r(G)`;
  `higherCommProb_succ_lt`: strict when `G` is non-abelian.
* `higherCommProb_add_le` (Prop. 2.14, submultiplicativity): `P_{n+m}(G) ≤ P_n(G) * P_m(G)`;
  `higherCommProb_add_lt`: strict when `G` is non-abelian.
* `higherCommProb_quotient_ge` (Prop. 2.9, monotonicity under quotients): `P_r(G ⧸ N) ≥ P_r(G)`.

"Non-abelian" is expressed as the hypothesis `∃ a b : G, ¬ Commute a b`, which is exactly the
witness the strictness arguments consume.

(The source numbers direct products as Prop. 2.13; Remark 2.12 consumes the prior counter.)
-/
import Mathlib

open scoped Classical

noncomputable section

/-- The set of pairwise-commuting `r`-tuples of a multiplicative type, as a subtype of `Fin r → G`.
This is `Comm_r(G)` in Levit–Shwartz. -/
def commTuples (G : Type*) [Mul G] (r : ℕ) : Type _ :=
  { f : Fin r → G // ∀ i j, Commute (f i) (f j) }

instance (G : Type*) [Mul G] [Finite G] (r : ℕ) : Finite (commTuples G r) := by
  unfold commTuples; infer_instance

/-- The tuple with a single non-trivial entry `a` at index `k` and `1` elsewhere.
Used as the witness for strictness of the monotonicity propositions. -/
def singleTuple {G : Type*} [One G] {r : ℕ} (k : Fin r) (a : G) : Fin r → G :=
  fun i => if i = k then a else 1

theorem singleTuple_apply_self {G : Type*} [One G] {r : ℕ} (k : Fin r) (a : G) :
    singleTuple k a k = a := by simp [singleTuple]

/-- A tuple with a single non-trivial entry is pairwise commuting. -/
theorem singleTuple_commute (G : Type*) [Group G] (r : ℕ) (k : Fin r) (a : G) :
    ∀ i j, Commute (singleTuple k a i) (singleTuple k a j) := by
  intro i j
  unfold singleTuple
  by_cases hi : i = k
  · by_cases hj : j = k
    · simp [hi, hj]
    · simp [hj, Commute.one_right]
  · simp [hi, Commute.one_left]

/-- The `r`-th higher commuting probability of `G`:
`P_r(G) = |Comm_r(G)| / |G|^r`. The case `r = 2` agrees with Mathlib's `commProb`. -/
def higherCommProb (G : Type*) [Mul G] (r : ℕ) : ℚ :=
  Nat.card (commTuples G r) / (Nat.card G : ℚ) ^ r

theorem higherCommProb_def (G : Type*) [Mul G] (r : ℕ) :
    higherCommProb G r = Nat.card (commTuples G r) / (Nat.card G : ℚ) ^ r :=
  rfl

/-- The denominator `|G|^r` equals `Nat.card (Fin r → G)`. -/
theorem card_funFin (G : Type*) (r : ℕ) :
    Nat.card (Fin r → G) = Nat.card G ^ r := by
  rw [Nat.card_fun, Nat.card_fin]

/-- An injection that misses an element of its (finite) codomain is strictly
cardinality-decreasing. -/
theorem nat_card_lt_of_injective_of_notMem {α β : Type*} [Finite β] (f : α → β)
    (hf : Function.Injective f) {b : β} (hb : b ∉ Set.range f) :
    Nat.card α < Nat.card β := by
  have h1 : Nat.card α = Nat.card (Set.range f) := (Nat.card_range_of_injective hf).symm
  have h2 : Set.range f ⊂ (Set.univ : Set β) :=
    ⟨Set.subset_univ _, fun hsub => hb (hsub (Set.mem_univ b))⟩
  have h3 : Nat.card (Set.range f) < Nat.card (Set.univ : Set β) :=
    Set.Finite.card_lt_card Set.finite_univ h2
  rw [Nat.card_univ] at h3
  rw [h1]; exact h3

/-! ### Proposition 2.13: direct products -/

/-- A tuple in `(G × H)^r` is pairwise commuting iff both its coordinate projections are. -/
def commTuples_prod_equiv (G H : Type*) [Mul G] [Mul H] (r : ℕ) :
    commTuples (G × H) r ≃ commTuples G r × commTuples H r where
  toFun f :=
    (⟨fun i => (f.1 i).1, fun i j => ((Prod.commute_iff).1 (f.2 i j)).1⟩,
     ⟨fun i => (f.1 i).2, fun i j => ((Prod.commute_iff).1 (f.2 i j)).2⟩)
  invFun gh :=
    ⟨fun i => (gh.1.1 i, gh.2.1 i), fun i j => Prod.commute_iff.2 ⟨gh.1.2 i j, gh.2.2 i j⟩⟩
  left_inv f := by
    apply Subtype.ext; funext i; rfl
  right_inv gh := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- **Proposition 2.13.** Higher commuting probability is multiplicative over direct products. -/
theorem higherCommProb_prod (G H : Type*) [Mul G] [Mul H] (r : ℕ) :
    higherCommProb (G × H) r = higherCommProb G r * higherCommProb H r := by
  rw [higherCommProb_def, higherCommProb_def, higherCommProb_def,
    Nat.card_congr (commTuples_prod_equiv G H r), Nat.card_prod, Nat.card_prod]
  push_cast
  rw [mul_pow, div_mul_div_comm]

/-! ### Proposition 2.11: monotonicity in `r` -/

/-- Dropping the last coordinate injects pairwise-commuting `(r+1)`-tuples into
`Comm_r(G) × G`. -/
theorem commTuples_succ_inj (G : Type*) [Mul G] (r : ℕ) :
    ∃ φ : commTuples G (r + 1) → commTuples G r × G, Function.Injective φ := by
  refine ⟨fun f => (⟨Fin.init f.1, fun i j => f.2 i.castSucc j.castSucc⟩, f.1 (Fin.last r)), ?_⟩
  intro f g hfg
  apply Subtype.ext
  have h1 : Fin.init f.1 = Fin.init g.1 := congrArg (Subtype.val ∘ Prod.fst) hfg
  have h2 : f.1 (Fin.last r) = g.1 (Fin.last r) := congrArg Prod.snd hfg
  rw [← Fin.snoc_init_self f.1, ← Fin.snoc_init_self g.1, h1, h2]

theorem card_commTuples_succ_le (G : Type*) [Mul G] [Finite G] (r : ℕ) :
    Nat.card (commTuples G (r + 1)) ≤ Nat.card (commTuples G r) * Nat.card G := by
  obtain ⟨φ, hφ⟩ := commTuples_succ_inj G r
  calc Nat.card (commTuples G (r + 1)) ≤ Nat.card (commTuples G r × G) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (commTuples G r) * Nat.card G := Nat.card_prod _ _

/-- **Proposition 2.11.** The sequence `P_r(G)` is non-increasing in `r`. -/
theorem higherCommProb_succ_le (G : Type*) [Group G] [Finite G] (r : ℕ) :
    higherCommProb G (r + 1) ≤ higherCommProb G r := by
  have hpos : 0 < (Nat.card G : ℚ) := by exact_mod_cast Finite.card_pos
  rw [higherCommProb_def, higherCommProb_def, div_le_div_iff₀ (by positivity) (by positivity)]
  have h := card_commTuples_succ_le G r
  have hcast : (Nat.card (commTuples G (r + 1)) : ℚ) ≤ Nat.card (commTuples G r) * Nat.card G := by
    exact_mod_cast h
  calc (Nat.card (commTuples G (r + 1)) : ℚ) * (Nat.card G : ℚ) ^ r
      ≤ ((Nat.card (commTuples G r) : ℚ) * Nat.card G) * (Nat.card G) ^ r := by
        apply mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = (Nat.card (commTuples G r) : ℚ) * (Nat.card G) ^ (r + 1) := by ring

/-- The strict version of the cardinality bound: for non-abelian `G`, the tuple
`(a, 1, …, 1, b)` (with `[a, b] ≠ 1`) lies in the codomain but not the range of the
restriction injection. -/
theorem card_commTuples_succ_lt (G : Type*) [Group G] [Finite G] (r : ℕ)
    (h : ∃ a b : G, ¬ Commute a b) :
    Nat.card (commTuples G (r + 1 + 1)) < Nat.card (commTuples G (r + 1)) * Nat.card G := by
  obtain ⟨a, b, hab⟩ := h
  rw [← Nat.card_prod]
  set φ : commTuples G (r + 1 + 1) → commTuples G (r + 1) × G :=
    fun f => (⟨Fin.init f.1, fun i j => f.2 i.castSucc j.castSucc⟩, f.1 (Fin.last (r + 1)))
  have hinj : Function.Injective φ := by
    intro f g hfg
    apply Subtype.ext
    have h1 : Fin.init f.1 = Fin.init g.1 := congrArg (Subtype.val ∘ Prod.fst) hfg
    have h2 : f.1 (Fin.last (r + 1)) = g.1 (Fin.last (r + 1)) := congrArg Prod.snd hfg
    rw [← Fin.snoc_init_self f.1, ← Fin.snoc_init_self g.1, h1, h2]
  set w : commTuples G (r + 1) × G :=
    (⟨singleTuple (0 : Fin (r + 1)) a, singleTuple_commute G (r + 1) 0 a⟩, b)
  have hwnotin : w ∉ Set.range φ := by
    rintro ⟨f, hf⟩
    have hinit : Fin.init f.1 = singleTuple (0 : Fin (r + 1)) a :=
      congrArg (Subtype.val ∘ Prod.fst) hf
    have hlast : f.1 (Fin.last (r + 1)) = b := congrArg Prod.snd hf
    have hf0 : f.1 (Fin.castSucc 0) = a := by
      have := congrFun hinit 0
      rw [Fin.init] at this
      rw [this, singleTuple_apply_self]
    have := f.2 (Fin.castSucc 0) (Fin.last (r + 1))
    rw [hf0, hlast] at this
    exact hab this
  exact nat_card_lt_of_injective_of_notMem φ hinj hwnotin

/-- **Proposition 2.11 (strict part).** If `G` is non-abelian then `P_r(G)` is strictly
decreasing in `r` (for `r ≥ 1`). -/
theorem higherCommProb_succ_lt (G : Type*) [Group G] [Finite G] (r : ℕ)
    (h : ∃ a b : G, ¬ Commute a b) :
    higherCommProb G (r + 1 + 1) < higherCommProb G (r + 1) := by
  have hGpos : 0 < (Nat.card G : ℚ) := by exact_mod_cast Finite.card_pos
  rw [higherCommProb_def, higherCommProb_def, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hlt := card_commTuples_succ_lt G r h
  have hcast : (Nat.card (commTuples G (r + 1 + 1)) : ℚ)
      < Nat.card (commTuples G (r + 1)) * Nat.card G := by exact_mod_cast hlt
  calc (Nat.card (commTuples G (r + 1 + 1)) : ℚ) * (Nat.card G : ℚ) ^ (r + 1)
      < ((Nat.card (commTuples G (r + 1)) : ℚ) * Nat.card G) * (Nat.card G) ^ (r + 1) := by
        apply mul_lt_mul_of_pos_right hcast (by positivity)
    _ = (Nat.card (commTuples G (r + 1)) : ℚ) * (Nat.card G) ^ (r + 1 + 1) := by ring

/-! ### Proposition 2.14: submultiplicativity -/

/-- Splitting an `(n+m)`-tuple into its first `n` and last `m` coordinates injects
pairwise-commuting `(n+m)`-tuples into `Comm_n(G) × Comm_m(G)`. -/
theorem commTuples_add_inj (G : Type*) [Mul G] (n m : ℕ) :
    ∃ φ : commTuples G (n + m) → commTuples G n × commTuples G m, Function.Injective φ := by
  refine ⟨fun f =>
    (⟨fun i => f.1 (Fin.castAdd m i), fun i j => f.2 (Fin.castAdd m i) (Fin.castAdd m j)⟩,
     ⟨fun i => f.1 (Fin.natAdd n i), fun i j => f.2 (Fin.natAdd n i) (Fin.natAdd n j)⟩), ?_⟩
  intro f g hfg
  apply Subtype.ext
  have h1 : (fun i => f.1 (Fin.castAdd m i)) = (fun i => g.1 (Fin.castAdd m i)) :=
    congrArg (Subtype.val ∘ Prod.fst) hfg
  have h2 : (fun i => f.1 (Fin.natAdd n i)) = (fun i => g.1 (Fin.natAdd n i)) :=
    congrArg (Subtype.val ∘ Prod.snd) hfg
  have key : (Fin.appendEquiv n m).symm f.1 = (Fin.appendEquiv n m).symm g.1 := by
    simp only [Fin.appendEquiv, Equiv.coe_fn_symm_mk, Prod.mk.injEq]
    exact ⟨h1, h2⟩
  exact (Fin.appendEquiv n m).symm.injective key

theorem card_commTuples_add_le (G : Type*) [Mul G] [Finite G] (n m : ℕ) :
    Nat.card (commTuples G (n + m)) ≤ Nat.card (commTuples G n) * Nat.card (commTuples G m) := by
  obtain ⟨φ, hφ⟩ := commTuples_add_inj G n m
  calc Nat.card (commTuples G (n + m)) ≤ Nat.card (commTuples G n × commTuples G m) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (commTuples G n) * Nat.card (commTuples G m) := Nat.card_prod _ _

/-- **Proposition 2.14.** Higher commuting probability is submultiplicative in the index. -/
theorem higherCommProb_add_le (G : Type*) [Group G] [Finite G] (n m : ℕ) :
    higherCommProb G (n + m) ≤ higherCommProb G n * higherCommProb G m := by
  have hpos : 0 < (Nat.card G : ℚ) := by exact_mod_cast Finite.card_pos
  rw [higherCommProb_def, higherCommProb_def, higherCommProb_def, div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h := card_commTuples_add_le G n m
  have hcast : (Nat.card (commTuples G (n + m)) : ℚ)
      ≤ Nat.card (commTuples G n) * Nat.card (commTuples G m) := by exact_mod_cast h
  calc (Nat.card (commTuples G (n + m)) : ℚ) * ((Nat.card G : ℚ) ^ n * (Nat.card G) ^ m)
      ≤ ((Nat.card (commTuples G n) : ℚ) * Nat.card (commTuples G m))
          * ((Nat.card G : ℚ) ^ n * (Nat.card G) ^ m) := by
        apply mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = (Nat.card (commTuples G n) : ℚ) * Nat.card (commTuples G m) * (Nat.card G) ^ (n + m) := by
        ring

/-- The strict version of the submultiplicative cardinality bound: for non-abelian `G`,
the tuple with `a` in the first block and `b` in the second block (where `[a, b] ≠ 1`)
lies in the codomain but not the range of the block-splitting injection. -/
theorem card_commTuples_add_lt (G : Type*) [Group G] [Finite G] (n m : ℕ)
    (h : ∃ a b : G, ¬ Commute a b) :
    Nat.card (commTuples G (n + 1 + (m + 1)))
      < Nat.card (commTuples G (n + 1)) * Nat.card (commTuples G (m + 1)) := by
  obtain ⟨a, b, hab⟩ := h
  rw [← Nat.card_prod]
  set φ : commTuples G (n + 1 + (m + 1)) → commTuples G (n + 1) × commTuples G (m + 1) :=
    fun f =>
      (⟨fun i => f.1 (Fin.castAdd (m + 1) i),
          fun i j => f.2 (Fin.castAdd (m + 1) i) (Fin.castAdd (m + 1) j)⟩,
       ⟨fun i => f.1 (Fin.natAdd (n + 1) i),
          fun i j => f.2 (Fin.natAdd (n + 1) i) (Fin.natAdd (n + 1) j)⟩)
  have hinj : Function.Injective φ := by
    intro f g hfg
    apply Subtype.ext
    have h1 : (fun i => f.1 (Fin.castAdd (m + 1) i)) = (fun i => g.1 (Fin.castAdd (m + 1) i)) :=
      congrArg (Subtype.val ∘ Prod.fst) hfg
    have h2 : (fun i => f.1 (Fin.natAdd (n + 1) i)) = (fun i => g.1 (Fin.natAdd (n + 1) i)) :=
      congrArg (Subtype.val ∘ Prod.snd) hfg
    have key :
        (Fin.appendEquiv (n + 1) (m + 1)).symm f.1
          = (Fin.appendEquiv (n + 1) (m + 1)).symm g.1 := by
      simp only [Fin.appendEquiv, Equiv.coe_fn_symm_mk, Prod.mk.injEq]
      exact ⟨h1, h2⟩
    exact (Fin.appendEquiv (n + 1) (m + 1)).symm.injective key
  set w : commTuples G (n + 1) × commTuples G (m + 1) :=
    (⟨singleTuple (0 : Fin (n + 1)) a, singleTuple_commute G (n + 1) 0 a⟩,
     ⟨singleTuple (0 : Fin (m + 1)) b, singleTuple_commute G (m + 1) 0 b⟩)
  have hwnotin : w ∉ Set.range φ := by
    rintro ⟨f, hf⟩
    have hA : (fun i => f.1 (Fin.castAdd (m + 1) i)) = singleTuple (0 : Fin (n + 1)) a :=
      congrArg (Subtype.val ∘ Prod.fst) hf
    have hB : (fun i => f.1 (Fin.natAdd (n + 1) i)) = singleTuple (0 : Fin (m + 1)) b :=
      congrArg (Subtype.val ∘ Prod.snd) hf
    have hfa : f.1 (Fin.castAdd (m + 1) 0) = a := by
      have := congrFun hA 0; rw [this, singleTuple_apply_self]
    have hfb : f.1 (Fin.natAdd (n + 1) 0) = b := by
      have := congrFun hB 0; rw [this, singleTuple_apply_self]
    have := f.2 (Fin.castAdd (m + 1) 0) (Fin.natAdd (n + 1) 0)
    rw [hfa, hfb] at this
    exact hab this
  exact nat_card_lt_of_injective_of_notMem φ hinj hwnotin

/-- **Proposition 2.14 (strict part).** If `G` is non-abelian then the submultiplicative
inequality is strict (for `n, m ≥ 1`). -/
theorem higherCommProb_add_lt (G : Type*) [Group G] [Finite G] (n m : ℕ)
    (h : ∃ a b : G, ¬ Commute a b) :
    higherCommProb G (n + 1 + (m + 1)) < higherCommProb G (n + 1) * higherCommProb G (m + 1) := by
  have hGpos : 0 < (Nat.card G : ℚ) := by exact_mod_cast Finite.card_pos
  rw [higherCommProb_def, higherCommProb_def, higherCommProb_def, div_mul_div_comm,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have hlt := card_commTuples_add_lt G n m h
  have hcast : (Nat.card (commTuples G (n + 1 + (m + 1))) : ℚ)
      < Nat.card (commTuples G (n + 1)) * Nat.card (commTuples G (m + 1)) := by exact_mod_cast hlt
  calc (Nat.card (commTuples G (n + 1 + (m + 1))) : ℚ)
        * ((Nat.card G : ℚ) ^ (n + 1) * (Nat.card G) ^ (m + 1))
      < ((Nat.card (commTuples G (n + 1)) : ℚ) * Nat.card (commTuples G (m + 1)))
          * ((Nat.card G : ℚ) ^ (n + 1) * (Nat.card G) ^ (m + 1)) := by
        apply mul_lt_mul_of_pos_right hcast (by positivity)
    _ = (Nat.card (commTuples G (n + 1)) : ℚ) * Nat.card (commTuples G (m + 1))
          * (Nat.card G) ^ (n + 1 + (m + 1)) := by ring

/-! ### Proposition 2.9: monotonicity under quotients -/

/-- Choosing a section of the quotient map injects `Comm_r(G)` into
`Comm_r(G ⧸ N) × (Fin r → N)`: a commuting tuple `g` maps to its image tuple `π ∘ g`
together with the "remainders" `(σ (π gᵢ))⁻¹ * gᵢ ∈ N`, from which `g` is recovered. -/
theorem commTuples_quotient_inj (G : Type*) [Group G] (N : Subgroup G) [N.Normal] (r : ℕ) :
    ∃ φ : commTuples G r → commTuples (G ⧸ N) r × (Fin r → N), Function.Injective φ := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  set σ : (G ⧸ N) → G := Function.surjInv hsurj with hσ
  have hσπ : ∀ y, π (σ y) = y := fun y => Function.surjInv_eq hsurj y
  have hmem : ∀ (g : Fin r → G) (i : Fin r), (σ (π (g i)))⁻¹ * g i ∈ N := by
    intro g i
    have hk : (σ (π (g i)))⁻¹ * g i ∈ MonoidHom.ker π := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσπ, inv_mul_cancel]
    rwa [QuotientGroup.ker_mk' N] at hk
  refine ⟨fun g =>
    (⟨fun i => π (g.1 i), fun i j => (g.2 i j).map π⟩,
     fun i => ⟨(σ (π (g.1 i)))⁻¹ * g.1 i, hmem g.1 i⟩), ?_⟩
  intro g₁ g₂ h
  apply Subtype.ext
  funext i
  have hy : π (g₁.1 i) = π (g₂.1 i) := by
    have := congrArg (fun p => (p.1.1 i)) h; simpa using this
  have hn : (σ (π (g₁.1 i)))⁻¹ * g₁.1 i = (σ (π (g₂.1 i)))⁻¹ * g₂.1 i := by
    have := congrArg (fun p => (p.2 i : G)) h; simpa using this
  rw [hy] at hn
  exact mul_left_cancel hn

/-- **Proposition 2.9.** Passing to a quotient can only increase the higher commuting
probability. -/
theorem higherCommProb_quotient_ge (G : Type*) [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (r : ℕ) :
    higherCommProb G r ≤ higherCommProb (G ⧸ N) r := by
  obtain ⟨φ, hφ⟩ := commTuples_quotient_inj G N r
  have hcard : Nat.card (commTuples G r) ≤ Nat.card (commTuples (G ⧸ N) r) * Nat.card N ^ r := by
    calc Nat.card (commTuples G r)
        ≤ Nat.card (commTuples (G ⧸ N) r × (Fin r → N)) := Nat.card_le_card_of_injective φ hφ
      _ = Nat.card (commTuples (G ⧸ N) r) * Nat.card (Fin r → N) := Nat.card_prod _ _
      _ = Nat.card (commTuples (G ⧸ N) r) * Nat.card N ^ r := by rw [card_funFin]
  have hG : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hNpos : 0 < (Nat.card N : ℚ) := by exact_mod_cast Finite.card_pos
  have hQpos : 0 < (Nat.card (G ⧸ N) : ℚ) := by exact_mod_cast Finite.card_pos
  have hGpos : 0 < (Nat.card G : ℚ) := by exact_mod_cast Finite.card_pos
  rw [higherCommProb_def, higherCommProb_def, div_le_div_iff₀ (by positivity) (by positivity)]
  have hcastG : (Nat.card G : ℚ) = Nat.card (G ⧸ N) * Nat.card N := by exact_mod_cast hG
  have hcastcard : (Nat.card (commTuples G r) : ℚ)
      ≤ Nat.card (commTuples (G ⧸ N) r) * Nat.card N ^ r := by exact_mod_cast hcard
  rw [hcastG]
  calc (Nat.card (commTuples G r) : ℚ) * (Nat.card (G ⧸ N) : ℚ) ^ r
      ≤ ((Nat.card (commTuples (G ⧸ N) r) : ℚ) * Nat.card N ^ r) * (Nat.card (G ⧸ N)) ^ r := by
        apply mul_le_mul_of_nonneg_right hcastcard (by positivity)
    _ = (Nat.card (commTuples (G ⧸ N) r) : ℚ) * ((Nat.card (G ⧸ N) : ℚ) * Nat.card N) ^ r := by
        rw [mul_pow]; ring

/-! ### Link to Mathlib's `commProb` at `r = 2` -/

/-- Bijection between `commTuples G 2` and the subtype of commuting pairs `{p : G × G // …}`
used in Mathlib's `commProb`. -/
def commTuples_two_equiv (G : Type*) [Mul G] :
    commTuples G 2 ≃ { p : G × G // Commute p.1 p.2 } where
  toFun f := ⟨(f.1 0, f.1 1), f.2 0 1⟩
  invFun p := ⟨![p.1.1, p.1.2], by
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
      Commute.refl, p.2, p.2.symm]⟩
  left_inv f := by
    apply Subtype.ext; funext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  right_inv p := by
    apply Subtype.ext; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `higherCommProb G 2` agrees with Mathlib's `commProb G`. -/
@[simp]
theorem higherCommProb_two (G : Type*) [Mul G] :
    higherCommProb G 2 = commProb G := by
  simp only [higherCommProb_def, commProb, Nat.card_congr (commTuples_two_equiv G)]

end
