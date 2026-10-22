/-
# (a,b)-town (mod k) families: the off-diagonal bound `m_{k,n}(a,b) ≤ n`

Hanlin Zou, *On the maximum size of (a,b)-town (mod k) families*,
arXiv:2606.03613, Theorem 1.4 (`thm_main_ab`, Section 4.1), resolves
Conjecture 1.2 of Veselinov and Marinov: for `n ≥ k ≥ 2` and
`a,b < k`, `a ≠ b`, an `(a,b)`-town family on `[n]` has at most `n`
members. Such a family has set sizes congruent to `a` and intersections
of distinct members congruent to `b` modulo `k`.

## Formal reading

The ground set `[n]` is `Fin n`, a family is a `Finset (Finset (Fin n))`,
and congruences mod `k` are equalities in `ZMod k`.  The main theorem
`card_le_of_isTownFamily` needs only `0 < n` and `(a : ZMod k) ≠ b`; the
paper's hypotheses `n ≥ k ≥ 2`, `a, b < k` are not used.  The hypothesis
`0 < n` cannot be dropped: `{∅}` is a `(0,1)`-town (mod 2) family on
`Fin 0` of size `1` (`not_card_le_zero_without_pos`).  The paper-shaped
statement is `thm_1_4`.  Sharpness for `k = 2`: the singletons
(`isTownFamily_singletons`).

## Proof (a streamlined form of the paper's §4.1 argument)

Suppose `#𝒜 > n`.  Pick `B ∈ 𝒜` and `n` further members `A_1, …, A_n`.
The `n` integer linear equations `μ₀ = ∑_{j : x ∈ A_j} μ_j` (`x ∈ [n]`) in
the `n + 1` unknowns `μ₀, …, μ_n` have a nonzero integer solution
(Siegel's lemma in Mathlib).  Pairing with `A_i` and with `B` gives, in
`ZMod k`, `μ_i (a - b) = 0`, so `d ∣ μ_i` with
`d = addOrderOf ((a : ZMod k) - b) ≠ 1`; reading one coordinate gives
`d ∣ μ₀`.  The solution set is closed under division by `d`, so infinite
descent forces `μ = 0`, a contradiction.  Unlike the paper, this does not
need the `n + 1` bound nor the rank of the incidence matrix.
-/
import Mathlib

set_option autoImplicit false

namespace Combinatorics.TownFamiliesCompositeModulus

open Finset

/-- An `(a,b)`-town (mod `k`) family on `[n] = Fin n` (Zou, Definition in
§1, after Veselinov–Marinov): for all `A, B ∈ 𝒜`, `|A ∩ B| ≡ a (mod k)`
if `A = B` and `|A ∩ B| ≡ b (mod k)` if `A ≠ B`. -/
def IsTownFamily (k a b : ℕ) {n : ℕ} (𝒜 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ((#(A ∩ B) : ℕ) : ZMod k) = if A = B then (a : ZMod k) else b

instance (k a b n : ℕ) (𝒜 : Finset (Finset (Fin n))) :
    Decidable (IsTownFamily k a b 𝒜) := by
  unfold IsTownFamily; infer_instance

/-- The Fano plane lines on `Fin 7`: a `(3,1)`-town family modulo `3`
(Zou, Corollary 4.2 with `q = 2`). -/
example : IsTownFamily 3 3 1 ({{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6},
    {2, 3, 6}, {2, 4, 5}} : Finset (Finset (Fin 7))) := by decide +kernel

/-- Oddtown is the `(1,0)`-town (mod `2`) case. -/
example : IsTownFamily 2 1 0 ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) := by decide

/-- A non-example: two sets meeting in one point are not a `(1,0)`-town
(mod `2`). -/
example : ¬ IsTownFamily 2 1 0 ({{0}, {0, 1, 2}} : Finset (Finset (Fin 3))) := by decide

/-- The defining congruences, unfolded to the two-hypothesis form. -/
theorem isTownFamily_iff {k a b n : ℕ} (𝒜 : Finset (Finset (Fin n))) :
    IsTownFamily k a b 𝒜 ↔
      (∀ A ∈ 𝒜, ((#A : ℕ) : ZMod k) = a) ∧
        ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ((#(A ∩ B) : ℕ) : ZMod k) = b := by
  constructor
  · intro h
    refine ⟨fun A hA => ?_, fun A hA B hB hAB => ?_⟩
    · simpa using h A hA A hA
    · simpa [hAB] using h A hA B hB
  · rintro ⟨hs, hi⟩ A hA B hB
    by_cases hAB : A = B
    · subst hAB; simpa using hs A hA
    · simpa [hAB] using hi A hA B hB hAB

/-- Infinite descent: if every vector satisfying `P` has all entries divisible
by `d ≠ 0, 1`, and `P` is closed under division by `d`, then only the zero
vector satisfies `P`. -/
theorem eq_zero_of_dvd_descent {β : Type*} (P : (β → ℤ) → Prop) (d : ℕ) (hd : 1 < d)
    (hdvd : ∀ μ, P μ → ∀ j, (d : ℤ) ∣ μ j)
    (hdiv : ∀ ν : β → ℤ, P ((d : ℤ) • ν) → P ν) :
    ∀ μ, P μ → μ = 0 := by
  have hpow : ∀ t : ℕ, ∀ μ, P μ → ∀ j, (d : ℤ) ^ t ∣ μ j := by
    intro t
    induction t with
    | zero => intro μ _ j; simp
    | succ t ih =>
      intro μ hμ j
      have hdecomp : μ = (d : ℤ) • fun i => μ i / d := by
        funext i
        simp [Int.mul_ediv_cancel' (hdvd μ hμ i)]
      have hν := hdiv _ (hdecomp ▸ hμ)
      obtain ⟨c, hc⟩ := ih _ hν j
      refine ⟨c, ?_⟩
      rw [congrFun hdecomp j, Pi.smul_apply, smul_eq_mul, hc, pow_succ]
      ring
  intro μ hμ
  funext j
  by_contra hne
  have hdv : d ^ (μ j).natAbs ∣ (μ j).natAbs := by
    have h := hpow (μ j).natAbs μ hμ j
    rw [← Int.natCast_pow, Int.natCast_dvd] at h
    exact h
  have hpos : 0 < (μ j).natAbs := Int.natAbs_pos.mpr hne
  have hle := Nat.le_of_dvd hpos hdv
  have hlt : (μ j).natAbs < d ^ (μ j).natAbs := Nat.lt_pow_self hd
  omega

section Core

variable {α ι : Type*}

/-- The integer matrix of the linear system `μ₀ - ∑_{i : x ∈ F (some i)} μ_i = 0`,
one row per point `x`; the column `none` carries `μ₀`. -/
def relMatrix [DecidableEq α] (F : Option ι → Finset α) : Matrix α (Option ι) ℤ :=
  fun x c => Option.elim c 1 fun i => if x ∈ F (some i) then -1 else 0

/-- Row `x` of the system: `μ₀ = ∑_{i : x ∈ F (some i)} μ_i`. -/
theorem relMatrix_mulVec_eq_zero_iff [DecidableEq α] [Fintype ι] (F : Option ι → Finset α) (μ : Option ι → ℤ) :
    (relMatrix F).mulVec μ = 0 ↔
      ∀ x, μ none = ∑ i, if x ∈ F (some i) then μ (some i) else 0 := by
  rw [funext_iff]
  refine forall_congr' fun x => ?_
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, relMatrix, Option.elim,
    Pi.zero_apply, ite_mul, neg_mul, one_mul, zero_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib,
    ← Finset.sum_filter]
  constructor <;> intro h <;> linarith

/-- Pairing the relation with the set `F c`:
`μ₀ |F c| = ∑ᵢ μᵢ |F c ∩ F (some i)|`. -/
theorem pairing [DecidableEq α] [Fintype ι] (F : Option ι → Finset α) (μ : Option ι → ℤ)
    (hμ : ∀ x, μ none = ∑ i, if x ∈ F (some i) then μ (some i) else 0) (c : Option ι) :
    μ none * (#(F c) : ℤ) = ∑ i, μ (some i) * (#(F c ∩ F (some i)) : ℤ) := by
  calc μ none * (#(F c) : ℤ) = ∑ x ∈ F c, μ none := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ∑ x ∈ F c, ∑ i, if x ∈ F (some i) then μ (some i) else 0 :=
        Finset.sum_congr rfl fun x _ => hμ x
    _ = ∑ i, ∑ x ∈ F c, if x ∈ F (some i) then μ (some i) else 0 := Finset.sum_comm
    _ = ∑ i, μ (some i) * (#(F c ∩ F (some i)) : ℤ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Key divisibility.** In an `(a,b)`-town configuration indexed by
`Option ι`, every integer solution of the relation system has all entries
divisible by `addOrderOf ((a : ZMod k) - b)`. -/
theorem addOrderOf_dvd_of_rel [DecidableEq α] [Nonempty α] [Fintype ι] [DecidableEq ι] (k a b : ℕ) (F : Option ι → Finset α)
    (hsize : ∀ c, ((#(F c) : ℕ) : ZMod k) = a)
    (hinter : ∀ c c', c ≠ c' → ((#(F c ∩ F c') : ℕ) : ZMod k) = b)
    (μ : Option ι → ℤ) (hμ : ∀ x, μ none = ∑ i, if x ∈ F (some i) then μ (some i) else 0) :
    ∀ c, ((addOrderOf ((a : ZMod k) - b) : ℕ) : ℤ) ∣ μ c := by
  -- the pairings, cast to `ZMod k`
  have hpair : ∀ c, (μ none : ZMod k) * a =
      ∑ i, (μ (some i) : ZMod k) * ((#(F c ∩ F (some i)) : ℕ) : ZMod k) := by
    intro c
    have h := congrArg (Int.cast : ℤ → ZMod k) (pairing F μ hμ c)
    push_cast at h
    rw [← hsize c]
    exact_mod_cast h
  have hsome : ∀ i0 : ι, ((addOrderOf ((a : ZMod k) - b) : ℕ) : ℤ) ∣ μ (some i0) := by
    intro i0
    rw [addOrderOf_dvd_iff_zsmul_eq_zero, zsmul_eq_mul]
    have hB : (μ none : ZMod k) * a = ∑ i, (μ (some i) : ZMod k) * b := by
      rw [hpair none]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hinter none (some i) (Option.some_ne_none i).symm]
    have hA : (μ none : ZMod k) * a =
        ∑ i, (μ (some i) : ZMod k) * b + (μ (some i0) : ZMod k) * (a - b) := by
      rw [hpair (some i0)]
      have hterm : ∀ i, (μ (some i) : ZMod k) * ((#(F (some i0) ∩ F (some i)) : ℕ) : ZMod k) =
          (μ (some i) : ZMod k) * b +
            if i = i0 then (μ (some i) : ZMod k) * (a - b) else 0 := by
        intro i
        by_cases hi : i = i0
        · subst hi
          rw [Finset.inter_self, hsize, if_pos rfl]
          ring
        · rw [hinter (some i0) (some i) (fun h => hi (Option.some_injective _ h).symm),
            if_neg hi, add_zero]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i0, if_pos (Finset.mem_univ _)]
    rw [hA] at hB
    simpa using hB
  intro c
  cases c with
  | some i => exact hsome i
  | none =>
    obtain ⟨x⟩ := ‹Nonempty α›
    rw [hμ x]
    exact Finset.dvd_sum fun i _ => by
      split_ifs
      · exact hsome i
      · exact dvd_zero _

/-- **Core contradiction.** There is no configuration of sets `F c ⊆ α`,
indexed by `Option ι` with `#α ≤ #ι` and `α` nonempty, whose sizes are
`≡ a` and whose pairwise intersections (distinct indices) are `≡ b (mod k)`,
when `a ≢ b (mod k)`. -/
theorem false_of_townConfig [DecidableEq α] [Fintype α] [Nonempty α] [Fintype ι]
    [DecidableEq ι] (k a b : ℕ) (hab : (a : ZMod k) ≠ b) (F : Option ι → Finset α)
    (hsize : ∀ c, ((#(F c) : ℕ) : ZMod k) = a)
    (hinter : ∀ c c', c ≠ c' → ((#(F c ∩ F c') : ℕ) : ZMod k) = b)
    (hcard : Fintype.card α ≤ Fintype.card ι) : False := by
  obtain ⟨t, ht0, htM, -⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le (relMatrix F)
    (by rw [Fintype.card_option]; omega) Fintype.card_pos
  set d := addOrderOf ((a : ZMod k) - b) with hd_def
  have hd1 : d ≠ 1 := fun h => hab (sub_eq_zero.mp (AddMonoid.addOrderOf_eq_one_iff.mp h))
  have hdvd : ∀ μ : Option ι → ℤ, (relMatrix F).mulVec μ = 0 → ∀ c, (d : ℤ) ∣ μ c :=
    fun μ hμ => addOrderOf_dvd_of_rel k a b F hsize hinter μ
      ((relMatrix_mulVec_eq_zero_iff F μ).mp hμ)
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · apply ht0
    funext c
    have h := hdvd t htM c
    rw [hd0, Nat.cast_zero, zero_dvd_iff] at h
    exact h
  · have hd : 1 < d := by omega
    have hdiv : ∀ ν : Option ι → ℤ, (relMatrix F).mulVec ((d : ℤ) • ν) = 0 →
        (relMatrix F).mulVec ν = 0 := by
      intro ν hν
      rw [Matrix.mulVec_smul, smul_eq_zero] at hν
      rcases hν with h | h
      · exact absurd h (by exact_mod_cast hdpos.ne')
      · exact h
    exact ht0 (eq_zero_of_dvd_descent (fun μ => (relMatrix F).mulVec μ = 0) d hd hdvd hdiv t htM)

end Core

/-- **Off-diagonal bound** (Zou, arXiv:2606.03613, Theorem 1.4, resolving the
Veselinov–Marinov conjecture), in the generality the proof supports: if
`a ≢ b (mod k)` and `𝒜` is an `(a,b)`-town (mod `k`) family on `[n]` with
`0 < n`, then `#𝒜 ≤ n`.  No assumption `n ≥ k ≥ 2` is needed; `0 < n` is
necessary (`not_card_le_zero_without_pos`). -/
theorem card_le_of_isTownFamily {k a b n : ℕ} (hn : 0 < n) (hab : (a : ZMod k) ≠ b)
    {𝒜 : Finset (Finset (Fin n))} (h𝒜 : IsTownFamily k a b 𝒜) : #𝒜 ≤ n := by
  obtain ⟨hsize, hinter⟩ := (isTownFamily_iff 𝒜).mp h𝒜
  by_contra hle
  have hlt : n < #𝒜 := not_le.mp hle
  obtain ⟨B, hB⟩ : 𝒜.Nonempty := Finset.card_pos.mp (by omega)
  have hrest : n ≤ #(𝒜.erase B) := by
    rw [Finset.card_erase_of_mem hB]; omega
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hrest
  let F : Option S → Finset (Fin n) := fun c => Option.elim c B Subtype.val
  have hmem : ∀ c, F c ∈ 𝒜 := by
    intro c
    cases c with
    | none => exact hB
    | some A => exact Finset.mem_of_mem_erase (hS A.2)
  have hBS : B ∉ S := fun h => Finset.notMem_erase B 𝒜 (hS h)
  have hinj : ∀ c c', c ≠ c' → F c ≠ F c' := by
    intro c c' hcc'
    cases c with
    | none =>
      cases c' with
      | none => exact absurd rfl hcc'
      | some A' =>
        intro h
        have hBA : B = (A' : Finset (Fin n)) := h
        exact hBS (hBA ▸ A'.2)
    | some A =>
      cases c' with
      | none =>
        intro h
        have hAB : (A : Finset (Fin n)) = B := h
        exact hBS (hAB ▸ A.2)
      | some A' => exact fun h => hcc' (congrArg some (Subtype.ext h))
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact false_of_townConfig k a b hab F (fun c => hsize _ (hmem c))
    (fun c c' hcc' => hinter _ (hmem c) _ (hmem c') (hinj c c' hcc'))
    (by rw [Fintype.card_fin, Fintype.card_coe, hScard])

/-- **Theorem 1.4** (Zou, arXiv:2606.03613), in the paper's own hypotheses:
for `n ≥ k ≥ 2`, `0 ≤ a, b ≤ k - 1`, `a ≠ b`, every `(a,b)`-town (mod `k`)
family on `[n]` has at most `n` members, i.e. `m_{k,n}(a,b) ≤ n`. -/
theorem thm_1_4 {k a b n : ℕ} (_hk : 2 ≤ k) (hkn : k ≤ n) (ha : a < k) (hb : b < k)
    (hab : a ≠ b) {𝒜 : Finset (Finset (Fin n))} (h𝒜 : IsTownFamily k a b 𝒜) : #𝒜 ≤ n := by
  refine card_le_of_isTownFamily (by omega) ?_ h𝒜
  intro h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact hab h

/-- **Theorem 4.1** (Zou, arXiv:2606.03613): if `a ≢ b (mod k)`, every
`(a,b)`-town (mod `k`) family on `[n]` has at most `n + 1` members.  This
holds for every `n`, including `n = 0`. -/
theorem thm_4_1 {k a b n : ℕ} (hab : (a : ZMod k) ≠ b) {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : IsTownFamily k a b 𝒜) : #𝒜 ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    calc #𝒜 ≤ Fintype.card (Finset (Fin 0)) := Finset.card_le_univ 𝒜
      _ = 0 + 1 := by simp
  · exact (card_le_of_isTownFamily hn hab h𝒜).trans (Nat.le_succ n)

/-- The hypothesis `0 < n` in `card_le_of_isTownFamily` cannot be dropped:
on the empty ground set `{∅}` is a `(0,1)`-town (mod `2`) family of size
`1 > 0`, although `0 ≢ 1 (mod 2)`. -/
theorem not_card_le_zero_without_pos :
    ((0 : ℕ) : ZMod 2) ≠ ((1 : ℕ) : ZMod 2) ∧
      IsTownFamily 2 0 1 ({∅} : Finset (Finset (Fin 0))) ∧
      ¬ #({∅} : Finset (Finset (Fin 0))) ≤ 0 := by
  decide

/-- Sharpness for Oddtown: the `n` singletons of `[n]` form a `(1,0)`-town
(mod `k`) family for every `k`, so the bound `#𝒜 ≤ n` is attained. -/
theorem isTownFamily_singletons (k n : ℕ) :
    IsTownFamily k 1 0 ((Finset.univ : Finset (Fin n)).map ⟨fun i => ({i} : Finset (Fin n)),
      Finset.singleton_injective⟩) ∧
      #((Finset.univ : Finset (Fin n)).map ⟨fun i => ({i} : Finset (Fin n)), Finset.singleton_injective⟩) = n := by
  refine ⟨?_, by simp⟩
  intro A hA B hB
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hA hB
  obtain ⟨i, rfl⟩ := hA
  obtain ⟨j, rfl⟩ := hB
  by_cases hij : i = j
  · subst hij; simp
  · have hne : ({i} : Finset (Fin n)) ≠ {j} := by simpa using hij
    rw [if_neg hne, Finset.singleton_inter_of_notMem (by simpa using hij)]
    simp

/-- The Oddtown singletons on `[3]` satisfy the hypotheses of `thm_1_4`
with `k = 2`, `a = 1`, `b = 0`. -/
example : #({{0}, {1}, {2}} : Finset (Finset (Fin 3))) ≤ 3 :=
  thm_1_4 (k := 2) (a := 1) (b := 0) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide)

/-- At a composite modulus, with equality: the Fano lines form a
`(3,1)`-town (mod `4`) family on `[7]` of size `7`. -/
example : #({{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}} :
    Finset (Finset (Fin 7))) ≤ 7 :=
  card_le_of_isTownFamily (k := 4) (a := 3) (b := 1) (by norm_num) (by decide)
    (by decide +kernel)

end Combinatorics.TownFamiliesCompositeModulus
