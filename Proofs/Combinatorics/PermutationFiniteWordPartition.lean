import Combinatorics.PermutationBoundaryStandardization

set_option autoImplicit false

namespace PermutationFiniteWordPartition

open PermutationBoundaryStandardization PermutationOverlapBound

/-- The first `k` physical positions, in increasing order. -/
def prefixEmbedding {m k : ℕ} (h : k ≤ m) : Fin k ↪ Fin m :=
  ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin m => x.val) hij⟩

/-- The last `k` physical positions, in increasing order. -/
def suffix {m k : ℕ} (h : k ≤ m) : Fin k ↪ Fin m :=
  ⟨fun i => ⟨i.val + (m - k), by omega⟩, by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change i.val + (m - k) = j.val + (m - k) at hv
    omega⟩

example : prefixEmbedding (by decide : 2 ≤ 4) (1 : Fin 2) = (1 : Fin 4) := rfl
example : suffix (by decide : 2 ≤ 4) (0 : Fin 2) = (2 : Fin 4) := rfl

/-- The concrete prefixEmbedding restriction of a word. -/
def leftWord {m n k : ℕ} (L : Fin m → Fin n) (h : k ≤ m) : Fin k → Fin n :=
  fun i => L (prefixEmbedding h i)

/-- The concrete suffix restriction of a word. -/
def rightWord {m n k : ℕ} (R : Fin m → Fin n) (h : k ≤ m) : Fin k → Fin n :=
  fun i => R (suffix h i)

example (L : Fin 4 → Fin 5) : leftWord L (by decide : 2 ≤ 4) 1 = L 1 := rfl
example (R : Fin 4 → Fin 5) : rightWord R (by decide : 2 ≤ 4) 0 = R 2 := rfl

/-- A specified common pattern means injectivity within each restriction and the
comparisons of that pattern on both restrictions; cross-block ties are allowed. -/
def Common {m n k : ℕ} (L R : Fin m → Fin n) (h : k ≤ m)
    (σ : Equiv.Perm (Fin k)) : Prop :=
  Function.Injective (leftWord L h) ∧ Function.Injective (rightWord R h) ∧
  (∀ i j, σ i < σ j ↔ leftWord L h i < leftWord L h j) ∧
  (∀ i j, σ i < σ j ↔ rightWord R h i < rightWord R h j)

/-- `B_k` is injective agreement of the two restricted words. -/
def B {m n k : ℕ} (L R : Fin m → Fin n) (h : k ≤ m) : Prop :=
  ∃ σ, Common L R h σ

/-- `A_k` is agreement with a common pattern avoiding every overlap of length
at least two and strictly less than `k`. -/
def A {m n k : ℕ} (L R : Fin m → Fin n) (h : k ≤ m) : Prop :=
  ∃ σ, Common L R h σ ∧ ShortAvoid k σ

/-- The comparison formulation is exactly the production rank formulation. -/
theorem common_iff_rank {m n k : ℕ} (L R : Fin m → Fin n) (h : k ≤ m)
    (σ : Equiv.Perm (Fin k)) :
    Common L R h σ ↔ ∃ (hl : Function.Injective (leftWord L h))
      (hr : Function.Injective (rightWord R h)),
      rank ⟨leftWord L h, hl⟩ = σ ∧ rank ⟨rightWord R h, hr⟩ = σ := by
  constructor
  · rintro ⟨hl, hr, hpl, hpr⟩
    exact ⟨hl, hr, rank_unique _ σ hpl, rank_unique _ σ hpr⟩
  · rintro ⟨hl, hr, hpl, hpr⟩
    refine ⟨hl, hr, ?_, ?_⟩
    · intro i j
      rw [← hpl]
      exact rank_lt_iff _ i j
    · intro i j
      rw [← hpr]
      exact rank_lt_iff _ i j

/-- Agreement is precisely equality of the ranks of two injective restrictions. -/
theorem B_iff_rank {m n k : ℕ} (L R : Fin m → Fin n) (h : k ≤ m) :
    B L R h ↔ ∃ (hl : Function.Injective (leftWord L h))
      (hr : Function.Injective (rightWord R h)),
      rank ⟨leftWord L h, hl⟩ = rank ⟨rightWord R h, hr⟩ := by
  constructor
  · rintro ⟨σ, hc⟩
    obtain ⟨hl, hr, hsl, hsr⟩ := (common_iff_rank L R h σ).mp hc
    exact ⟨hl, hr, hsl.trans hsr.symm⟩
  · rintro ⟨hl, hr, he⟩
    exact ⟨_, (common_iff_rank L R h _).mpr ⟨hl, hr, rfl, he.symm⟩⟩

/-- Under a common length-`k` pattern, smaller agreement is equivalent to actual
self-overlap of that pattern, not an automatic consequence of agreement. -/
theorem B_iff_overlap {m n j k : ℕ} (L R : Fin m → Fin n)
    (hk : k ≤ m) (hjk : j < k) (σ : Equiv.Perm (Fin k))
    (hc : Common L R hk σ) :
    B L R (show j ≤ m by omega) ↔ Overlap hjk σ := by
  let hj : j ≤ m := by omega
  have hp (i t : Fin j) :
      σ (prefixEmbedding (Nat.le_of_lt hjk) i) < σ (prefixEmbedding (Nat.le_of_lt hjk) t) ↔
      leftWord L hj i < leftWord L hj t := by
    exact hc.2.2.1 _ _
  have hs (i t : Fin j) :
      σ (suffix (Nat.le_of_lt hjk) i) < σ (suffix (Nat.le_of_lt hjk) t) ↔
      rightWord R hj i < rightWord R hj t := by
    have hi : suffix hk (suffix (Nat.le_of_lt hjk) i) = suffix hj i := by
      apply Fin.ext
      change i.val + (k - j) + (m - k) = i.val + (m - j)
      omega
    have ht : suffix hk (suffix (Nat.le_of_lt hjk) t) = suffix hj t := by
      apply Fin.ext
      change t.val + (k - j) + (m - k) = t.val + (m - j)
      omega
    simpa only [rightWord, hi, ht] using
      hc.2.2.2 (suffix (Nat.le_of_lt hjk) i) (suffix (Nat.le_of_lt hjk) t)
  have hli : Function.Injective (leftWord L hj) := by
    intro i t he
    apply (prefixEmbedding (Nat.le_of_lt hjk)).injective
    apply hc.1
    exact he
  have hri : Function.Injective (rightWord R hj) := by
    intro i t he
    apply (suffix (Nat.le_of_lt hjk)).injective
    apply hc.2.1
    change R ⟨i.val + (k - j) + (m - k), _⟩ =
      R ⟨t.val + (k - j) + (m - k), _⟩
    change R ⟨i.val + (m - j), _⟩ = R ⟨t.val + (m - j), _⟩ at he
    simpa only [Nat.add_assoc, show k - j + (m - k) = m - j by omega] using he
  constructor
  · rintro ⟨τ, ht⟩ i t
    exact (hp i t).trans ((ht.2.2.1 i t).symm.trans
      ((ht.2.2.2 i t).trans (hs i t).symm))
  · intro ho
    let τ := rank (⟨leftWord L hj, hli⟩ : Fin j ↪ Fin n)
    refine ⟨τ, hli, hri, ?_, ?_⟩
    · exact rank_lt_iff _
    · intro i t
      exact (rank_lt_iff _ i t).trans ((hp i t).symm.trans
        ((ho i t).trans (hs i t)))

/-- Avoiding-pattern agreement is exactly agreement with no smaller nontrivial
agreement. This characterization holds off any global injectivity event. -/
theorem A_iff_least {m n k : ℕ} (L R : Fin m → Fin n) (hk : k ≤ m) :
    A L R hk ↔ B L R hk ∧
      ∀ j, 2 ≤ j → (hjk : j < k) → ¬ B L R (show j ≤ m by omega) := by
  constructor
  · rintro ⟨σ, hc, ha⟩
    refine ⟨⟨σ, hc⟩, ?_⟩
    intro j hj hjk hb
    exact ha j hj hjk hjk ((B_iff_overlap L R hk hjk σ hc).mp hb)
  · rintro ⟨⟨σ, hc⟩, hm⟩
    refine ⟨σ, hc, ?_⟩
    intro j hj hjk _ ho
    exact hm j hj hjk ((B_iff_overlap L R hk hjk σ hc).mpr ho)

/-- Distinct increasing nontrivial lengths cannot both be earliest agreement. -/
theorem A_disjoint {m n j k : ℕ} (L R : Fin m → Fin n)
    (hj : 2 ≤ j) (hjk : j < k) (hk : k ≤ m) :
    ¬ (A L R (show j ≤ m by omega) ∧ A L R hk) := by
  rintro ⟨ha, hb⟩
  exact ((A_iff_least L R hk).mp hb).2 j hj hjk
    ((A_iff_least L R _).mp ha).1

/-- The union of nontrivial agreement events is partitioned by their least
length; no good event or cross-block distinctness is assumed. -/
theorem exists_B_iff_exists_A {m n : ℕ} (L R : Fin m → Fin n) :
    (∃ k, ∃ hk : k ≤ m, 2 ≤ k ∧ B L R hk) ↔
      ∃ k, ∃ hk : k ≤ m, 2 ≤ k ∧ A L R hk := by
  classical
  constructor
  · intro hex
    let P : ℕ → Prop := fun k => ∃ hk : k ≤ m, 2 ≤ k ∧ B L R hk
    have he : ∃ k, P k := hex
    obtain ⟨hk, htwo, hb⟩ := Nat.find_spec he
    refine ⟨Nat.find he, hk, htwo, (A_iff_least L R hk).mpr ⟨hb, ?_⟩⟩
    intro j hj hjk hbj
    exact (Nat.find_min he hjk) ⟨by omega, hj, hbj⟩
  · rintro ⟨k, hk, htwo, ha⟩
    exact ⟨k, hk, htwo, ((A_iff_least L R hk).mp ha).1⟩

/-- For actual permutation words, agreement is precisely actual boundary
self-overlap, whenever that overlap is a proper length. -/
theorem B_permutation_iff {m k : ℕ} (π : Equiv.Perm (Fin m)) (hk : k < m) :
    B π π (Nat.le_of_lt hk) ↔ Overlap hk π := by
  constructor
  · rintro ⟨σ, hc⟩ i j
    exact (hc.2.2.1 i j).symm.trans (hc.2.2.2 i j)
  · intro ho
    let f : Fin k ↪ Fin m := (prefixEmbedding (Nat.le_of_lt hk)).trans π.toEmbedding
    refine ⟨rank f, (π.injective.comp (prefixEmbedding _).injective),
      (π.injective.comp (suffix _).injective), ?_, ?_⟩
    · exact rank_lt_iff f
    · intro i j
      exact (rank_lt_iff f i j).trans (ho i j)

/-- Actual permutation earliest overlap is exactly the finite-word partition
cell, with all smaller actual overlaps excluded. -/
theorem A_permutation_iff {m k : ℕ} (π : Equiv.Perm (Fin m)) (hk : k < m) :
    A π π (Nat.le_of_lt hk) ↔ Overlap hk π ∧
      ∀ j, 2 ≤ j → (hjk : j < k) → ¬ Overlap (show j < m by omega) π := by
  rw [A_iff_least, B_permutation_iff π hk]
  constructor
  · rintro ⟨ho, hm⟩
    refine ⟨ho, ?_⟩
    intro j hj hjk ho'
    exact hm j hj hjk ((B_permutation_iff π (by omega)).mpr ho')
  · rintro ⟨ho, hm⟩
    refine ⟨ho, ?_⟩
    intro j hj hjk hb
    exact hm j hj hjk ((B_permutation_iff π (by omega)).mp hb)

/-- Restricting an actual permutation to its two boundary words agrees with
its actual overlap event, with suffix positions in increasing physical order. -/
theorem B_boundary_permutation_iff {N m k : ℕ} (π : Equiv.Perm (Fin N))
    (hm : m ≤ N) (hk : k ≤ m) (hkn : k < N) :
    B (fun i => π (prefixEmbedding hm i)) (fun i => π (suffix hm i)) hk ↔
      Overlap hkn π := by
  have hadd : m - k + (N - m) = N - k := by omega
  constructor
  · rintro ⟨σ, hc⟩ i j
    have he := (hc.2.2.1 i j).symm.trans (hc.2.2.2 i j)
    change π ⟨i.val, _⟩ < π ⟨j.val, _⟩ ↔
      π ⟨i.val + (m - k) + (N - m), _⟩ <
        π ⟨j.val + (m - k) + (N - m), _⟩ at he
    simpa only [Nat.add_assoc, hadd] using he
  · intro ho
    let f := (prefixEmbedding (Nat.le_of_lt hkn)).trans π.toEmbedding
    refine ⟨rank f, ?_, ?_, ?_, ?_⟩
    · exact π.injective.comp ((prefixEmbedding hm).injective.comp
        (prefixEmbedding hk).injective)
    · exact π.injective.comp ((suffix hm).injective.comp (suffix hk).injective)
    · exact rank_lt_iff f
    · intro i j
      change rank f i < rank f j ↔
        π ⟨i.val + (m - k) + (N - m), _⟩ <
          π ⟨j.val + (m - k) + (N - m), _⟩
      simpa only [Nat.add_assoc, hadd] using (rank_lt_iff f i j).trans (ho i j)

/-- Two independently sampled internal blocks, anchored at the left first and
right last positions. The shared sample is not required to be injective. -/
def sampledLeft {m n : ℕ} (hm : 0 < m) (a : Fin n)
    (z : Fin (2 * (m - 1)) → Fin n) : Fin m → Fin n :=
  fun i => if hi : i.val = 0 then a else z ⟨i.val - 1, by omega⟩

/-- The right sampled block reads its internal coordinates in physical order. -/
def sampledRight {m n : ℕ} (hm : 0 < m) (b : Fin n)
    (z : Fin (2 * (m - 1)) → Fin n) : Fin m → Fin n :=
  fun i => if hi : i.val = m - 1 then b else z ⟨m - 1 + i.val, by omega⟩

example (a b : Fin 3) (z : Fin 2 → Fin 3) :
    sampledLeft (by decide : 0 < 2) a z 0 = a ∧
    sampledLeft (by decide : 0 < 2) a z 1 = z 0 ∧
    sampledRight (by decide : 0 < 2) b z 0 = z 1 ∧
    sampledRight (by decide : 0 < 2) b z 1 = b := by
  simp [sampledLeft, sampledRight]

/-- The partition applies to the concrete anchored iid words without conditioning. -/
theorem sampled_partition {m n : ℕ} (hm : 0 < m) (a b : Fin n)
    (z : Fin (2 * (m - 1)) → Fin n) :
    (∃ k, ∃ hk : k ≤ m, 2 ≤ k ∧
      B (sampledLeft hm a z) (sampledRight hm b z) hk) ↔
    ∃ k, ∃ hk : k ≤ m, 2 ≤ k ∧
      A (sampledLeft hm a z) (sampledRight hm b z) hk :=
  exists_B_iff_exists_A _ _

/-- Repeated values across the two blocks do not prevent earliest agreement. -/
theorem cross_block_ties : A (id : Fin 2 → Fin 2) id (by decide : 2 ≤ 2) := by
  refine ⟨Equiv.refl _, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j h
      exact h
    · intro i j h
      simpa [rightWord, suffix] using h
    · intro i j
      rfl
    · intro i j
      simp [rightWord, suffix]
  · intro j hj hjk
    omega

example : ∃ σ, Common (id : Fin 2 → Fin 2) id (by decide : 2 ≤ 2) σ :=
  ⟨_, cross_block_ties.choose_spec.1⟩
example : B (id : Fin 2 → Fin 2) id (by decide : 2 ≤ 2) :=
  ((A_iff_least _ _ _).mp cross_block_ties).1
example : ¬ Function.Injective (Sum.elim (id : Fin 2 → Fin 2) id) := by
  intro hi
  have he := hi (show Sum.elim (id : Fin 2 → Fin 2) id (Sum.inl 0) =
    Sum.elim (id : Fin 2 → Fin 2) id (Sum.inr 0) from rfl)
  cases he

example : ¬ B (id : Fin 2 → Fin 2) (Equiv.swap 0 1) (by decide : 2 ≤ 2) := by
  rintro ⟨σ, hc⟩
  have hl : leftWord (id : Fin 2 → Fin 2) (by decide : 2 ≤ 2) 0 <
      leftWord id (by decide : 2 ≤ 2) 1 := by decide
  have hr := (hc.2.2.2 0 1).mp ((hc.2.2.1 0 1).mpr hl)
  change (Equiv.swap (0 : Fin 2) 1) 0 < (Equiv.swap (0 : Fin 2) 1) 1 at hr
  exact (by decide : ¬ (Equiv.swap (0 : Fin 2) 1) 0 <
    (Equiv.swap (0 : Fin 2) 1) 1) hr

example : A
    (sampledLeft (by decide : 0 < 2) (0 : Fin 2)
      (fun i : Fin 2 => if i = 0 then 1 else 0))
    (sampledRight (by decide : 0 < 2) (1 : Fin 2)
      (fun i : Fin 2 => if i = 0 then 1 else 0)) (by decide : 2 ≤ 2) := by
  have hl : sampledLeft (by decide : 0 < 2) (0 : Fin 2)
      (fun i : Fin 2 => if i = 0 then 1 else 0) = id := by
    funext i
    fin_cases i <;> decide
  have hr : sampledRight (by decide : 0 < 2) (1 : Fin 2)
      (fun i : Fin 2 => if i = 0 then 1 else 0) = id := by
    funext i
    fin_cases i <;> decide
  rw [hl, hr]
  exact cross_block_ties

end PermutationFiniteWordPartition
