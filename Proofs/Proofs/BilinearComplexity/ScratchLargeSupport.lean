import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Scratch module: prove the "large support" lemma in isolation, then its proof
will be inlined into `SliceRank.lean`.
-/

open Finset in
/-- **Large-support lemma.** A subspace `V ⊆ (ι → K)` over a field contains a
vector whose number of nonzero coordinates is at least `finrank K V`. -/
theorem exists_mem_support_card_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] [DecidableEq K] (V : Submodule K (ι → K)) :
    ∃ v ∈ V, Module.finrank K V ≤ (Finset.univ.filter fun i => v i ≠ 0).card := by
  -- Define the support-size function
  set g : ↥V → ℕ := fun y => (Finset.univ.filter fun i => (y : ι → K) i ≠ 0).card with hg_def
  -- The range of g is nonempty and bounded above
  have hne : (Set.range g).Nonempty := Set.range_nonempty g
  have hbdd : BddAbove (Set.range g) := by
    use Fintype.card ι
    rintro _ ⟨y, rfl⟩
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans Finset.card_univ.le
  -- Let M be the supremum, realized by some ymax
  set M := sSup (Set.range g) with hM_def
  have hM_mem : M ∈ Set.range g := Nat.sSup_mem hne hbdd
  obtain ⟨ymax, hymax⟩ := hM_mem
  -- Every value of g is ≤ M
  have hle : ∀ y, g y ≤ M := fun y => le_csSup hbdd (Set.mem_range_self y)
  -- It suffices to show finrank K V ≤ M
  suffices hsuff : Module.finrank K V ≤ M by
    refine ⟨↑ymax, SetLike.coe_mem ymax, ?_⟩
    have : g ymax = (Finset.univ.filter fun i => (ymax : ι → K) i ≠ 0).card := rfl
    omega
  -- By contradiction
  by_contra hlt
  push Not at hlt
  -- So M < finrank K V
  -- Let T be the support of ymax
  set T : Finset ι := Finset.univ.filter fun i => (ymax : ι → K) i ≠ 0 with hT_def
  have hTcard : T.card = M := hymax
  -- Define the restriction map ρ : V →ₗ[K] (T → K)
  set ρ : ↥V →ₗ[K] (↥T → K) :=
    (LinearMap.funLeft K K (Subtype.val : ↥T → ι)).comp V.subtype with hρ_def
  -- finrank of range ρ ≤ T.card
  have hρ_range : Module.finrank K (LinearMap.range ρ) ≤ T.card := by
    calc Module.finrank K (LinearMap.range ρ)
        ≤ Module.finrank K (↥T → K) := Submodule.finrank_le _
      _ = Fintype.card ↥T := Module.finrank_pi _
      _ = T.card := Fintype.card_coe T
  -- rank-nullity
  have hrn := LinearMap.finrank_range_add_finrank_ker ρ
  -- So finrank of ker ρ ≥ 1
  have hker_pos : 0 < Module.finrank K (LinearMap.ker ρ) := by omega
  -- ker ρ ≠ ⊥
  have hker_ne : LinearMap.ker ρ ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hker_pos
    exact Nat.lt_irrefl 0 hker_pos
  -- Get a nonzero element in ker ρ
  obtain ⟨b, hb_mem, hb_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  -- b is in V (as a subtype element), and ρ b = 0
  have hρb : ρ b = 0 := LinearMap.mem_ker.mp hb_mem
  -- b's underlying function vanishes on T
  have hb_vanish : ∀ i : ι, i ∈ T → (b : ι → K) i = 0 := by
    intro i hi
    have := congr_fun hρb ⟨i, hi⟩
    simp [hρ_def, LinearMap.comp_apply, LinearMap.funLeft_apply, Submodule.subtype_apply] at this
    exact this
  -- b ≠ 0 as a function
  have hb_ne_fun : (b : ι → K) ≠ 0 := by
    rwa [ne_eq, Submodule.coe_eq_zero]
  -- Get a coordinate where b is nonzero
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hb_ne_fun
  simp only [Pi.zero_apply] at hi₀
  -- i₀ ∉ T
  have hi₀_not_mem : i₀ ∉ T := by
    intro hmem
    exact hi₀ (hb_vanish i₀ hmem)
  -- ymax vanishes at i₀
  have hymax_i₀ : (ymax : ι → K) i₀ = 0 := by
    by_contra h'
    exact hi₀_not_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
  -- The support of ymax + b contains insert i₀ T
  have hinsert_sub : insert i₀ T ⊆ Finset.univ.filter fun i => (↑(ymax + b) : ι → K) i ≠ 0 := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Submodule.coe_add, Pi.add_apply]
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · -- i = i₀
      rw [hymax_i₀, zero_add]
      exact hi₀
    · -- i ∈ T
      rw [hb_vanish i hi', add_zero]
      exact (Finset.mem_filter.mp hi').2
  -- g (ymax + b) ≥ M + 1
  have hg_big : M + 1 ≤ g (ymax + b) := by
    calc M + 1 = T.card + 1 := by omega
      _ = (insert i₀ T).card := (Finset.card_insert_of_notMem hi₀_not_mem).symm
      _ ≤ g (ymax + b) := Finset.card_le_card hinsert_sub
  -- But g (ymax + b) ≤ M
  have := hle (ymax + b)
  omega
