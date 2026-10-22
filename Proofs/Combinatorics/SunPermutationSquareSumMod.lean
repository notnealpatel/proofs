/-
# Sun's Conjecture 11.8 on permutation square sums

Yue-Feng She and Xin-Qi Luo, *Proof of a conjecture on permutations*,
arXiv:2606.18311, Theorem 1.1, Lemma 2.1 and Section 3. The conjecture is
Z.-W. Sun, *New conjectures in number theory and combinatorics* (Harbin
Institute of Technology Press, 2021), Conjecture 11.8.

For every `n > 4`, the values `F(τ) = ∑_{k=1}^n k²τ(k)²` cover every
residue modulo `2n+1`. Lemma 2.1 supplies subset sums of distinct squares
in `[129,Σ_n-129]` for `n ≥ 10`, with excluded values 128 and `Σ_n-128`.
These bounds and the full permutation theorem are established below.

## Conventions and proof

* `S_n` is `Equiv.Perm (Fin n)`, with `k : Fin n` standing for `k + 1 ∈ [1, n]`.
* The paper's Cases 1 and 2 are unified: with `m = ⌊(n-1)/2⌋`, swapping the
  values `m+1-d` and `m+1+d` for `d ∈ J ⊆ [1, m]` gives
  `F = ∑ k⁴ - ∑_{d ∈ J} (4d(m+1))²`, and `(4(m+1))² ≡ 1 (mod 2n+1)` because
  `2n+1 ∈ {4m+3, 4m+5}`.
* Case 3 is discharged by explicit witness tables (one permutation per residue),
  checked by `decide`.
-/
import Mathlib

set_option autoImplicit false

namespace SunPermutationSquareSumMod

/-! ## Definitions -/

/-- Sun's function `F(τ) = ∑_{k=1}^n k² τ(k)²` on `S_n`, with `S_n` realized as
`Equiv.Perm (Fin n)` and `k : Fin n` standing for the integer `k + 1`. -/
def sunF {n : ℕ} (τ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ k : Fin n, ((k : ℕ) + 1) ^ 2 * ((τ k : ℕ) + 1) ^ 2

/-- The identity of `S_3` has `F = 1·1 + 4·4 + 9·9 = 98`. -/
example : sunF (1 : Equiv.Perm (Fin 3)) = 98 := by decide

/-- The transposition `(1 3)` of `S_3` has `F = 1·9 + 4·4 + 9·1 = 34`. -/
example : sunF (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) = 34 := by decide

/-- The bound `n > 4` is sharp: for `n = 4` the residue `0 mod 9` is missed. -/
example : ∀ τ : Equiv.Perm (Fin 4), sunF τ % 9 ≠ 0 := by decide

/-- Subset-sum decision procedure: `rep m x = true` iff `x` is a sum of distinct
squares from `{1, …, m}` (soundness `exists_of_rep`, completeness
`rep_of_exists`). -/
def rep : ℕ → ℕ → Bool
  | 0, x => x == 0
  | m + 1, x => rep m x || (decide ((m + 1) ^ 2 ≤ x) && rep m (x - (m + 1) ^ 2))

/-- `5 = 1² + 2²` is a sum of distinct squares from `{1, 2}`. -/
example : rep 2 5 = true := by decide

/-- `2` is not a sum of distinct squares from `{1, 2}`. -/
example : rep 2 2 = false := by decide

/-! ## Subset sums of squares (Lemma 2.1) -/

/-- Soundness of `rep`: a positive answer yields `I ⊆ [1, m]` with
`∑_{i ∈ I} i² = x`. -/
theorem exists_of_rep (m x : ℕ) (h : rep m x = true) :
    ∃ I ⊆ Finset.Icc 1 m, ∑ i ∈ I, i ^ 2 = x := by
  induction m generalizing x with
  | zero =>
    have hx : x = 0 := by simpa [rep] using h
    exact ⟨∅, Finset.empty_subset _, by simp [hx]⟩
  | succ m ih =>
    simp only [rep, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hle, h⟩
    · obtain ⟨I, hI, hsum⟩ := ih x h
      exact ⟨I, hI.trans (Finset.Icc_subset_Icc_right (Nat.le_succ m)), hsum⟩
    · obtain ⟨I, hI, hsum⟩ := ih _ h
      have hnot : m + 1 ∉ I := fun hm => by
        have hmem := Finset.mem_Icc.mp (hI hm)
        omega
      refine ⟨insert (m + 1) I, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp
        · have hmem := Finset.mem_Icc.mp (hI hi)
          exact Finset.mem_Icc.mpr ⟨hmem.1, by omega⟩
      · rw [Finset.sum_insert hnot, hsum]
        omega

/-- Completeness of `rep`: every sum of distinct squares from `[1, m]` is
accepted. -/
theorem rep_of_exists (m x : ℕ) (h : ∃ I ⊆ Finset.Icc 1 m, ∑ i ∈ I, i ^ 2 = x) :
    rep m x = true := by
  induction m generalizing x with
  | zero =>
    obtain ⟨I, hI, hsum⟩ := h
    have hI0 : I = ∅ := Finset.subset_empty.mp (by simpa using hI)
    simp [rep, ← hsum, hI0]
  | succ m ih =>
    obtain ⟨I, hI, hsum⟩ := h
    simp only [rep, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hmI : m + 1 ∈ I
    · right
      have hsplit := Finset.add_sum_erase I (fun i => i ^ 2) hmI
      refine ⟨by omega, ih _ ⟨I.erase (m + 1), ?_, by omega⟩⟩
      intro i hi
      have hne := Finset.ne_of_mem_erase hi
      have hmem := Finset.mem_Icc.mp (hI (Finset.mem_of_mem_erase hi))
      exact Finset.mem_Icc.mpr ⟨hmem.1, by omega⟩
    · left
      refine ih x ⟨I, fun i hi => ?_, hsum⟩
      have hmem := Finset.mem_Icc.mp (hI hi)
      have hne : i ≠ m + 1 := fun h => hmI (h ▸ hi)
      exact Finset.mem_Icc.mpr ⟨hmem.1, by omega⟩

/-- `Σ_{m+1} = Σ_m + (m+1)²`. -/
theorem sumSq_succ (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 (m + 1), i ^ 2 = ∑ i ∈ Finset.Icc 1 m, i ^ 2 + (m + 1) ^ 2 :=
  Finset.sum_Icc_succ_top (by omega) _

/-- For `m ≥ 10`, `257 + (m+1)² ≤ Σ_m`; this is the paper's overlap estimate
`Σ_m - 129 - (129 + (m+1)²) ≥ 6` up to the off-by-one of closed intervals. -/
theorem sumSq_bound (m : ℕ) (hm : 10 ≤ m) :
    257 + (m + 1) ^ 2 ≤ ∑ i ∈ Finset.Icc 1 m, i ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [sumSq_succ]
    nlinarith

/-- Base case `m = 10` of Lemma 2.1, by kernel computation: every
`x ∈ [129, 256] = [129, Σ_10 - 129]` is a sum of distinct squares from `[1, 10]`. -/
theorem rep_base : ((List.range 128).all fun j => rep 10 (129 + j)) = true := by decide

/-- **Lemma 2.1 (She–Luo), interval part.** For every `m ≥ 10`, every integer in
`[129, Σ_m - 129]` is a sum of distinct squares from `[1, m]`. -/
theorem lemma_2_1 (m : ℕ) (hm : 10 ≤ m) (x : ℕ) (hx₁ : 129 ≤ x)
    (hx₂ : x + 129 ≤ ∑ i ∈ Finset.Icc 1 m, i ^ 2) :
    ∃ I ⊆ Finset.Icc 1 m, ∑ i ∈ I, i ^ 2 = x := by
  induction m, hm using Nat.le_induction generalizing x with
  | base =>
    have h385 : ∑ i ∈ Finset.Icc 1 10, i ^ 2 = 385 := by decide
    have hrep := List.all_eq_true.mp rep_base (x - 129) (List.mem_range.mpr (by omega))
    rw [show 129 + (x - 129) = x by omega] at hrep
    exact exists_of_rep 10 x hrep
  | succ m hm ih =>
    rw [sumSq_succ] at hx₂
    have hb := sumSq_bound m hm
    by_cases hsmall : x + 129 ≤ ∑ i ∈ Finset.Icc 1 m, i ^ 2
    · obtain ⟨I, hI, hsum⟩ := ih x hx₁ hsmall
      exact ⟨I, hI.trans (Finset.Icc_subset_Icc_right (Nat.le_succ m)), hsum⟩
    · obtain ⟨I, hI, hsum⟩ := ih (x - (m + 1) ^ 2) (by omega) (by omega)
      have hnot : m + 1 ∉ I := fun hm' => by
        have hmem := Finset.mem_Icc.mp (hI hm')
        omega
      refine ⟨insert (m + 1) I, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp
        · have hmem := Finset.mem_Icc.mp (hI hi)
          exact Finset.mem_Icc.mpr ⟨hmem.1, by omega⟩
      · rw [Finset.sum_insert hnot, hsum]
        omega

/-- `128` is not a sum of distinct squares from `[1, 11]` (kernel computation). -/
theorem rep_128 : rep 11 128 = false := by decide

/-- **Lemma 2.1 (She–Luo), sharpness part.** `128` is not a sum of distinct
squares from `[1, m]`; the paper states this for `m ≥ 10`, and it holds for every `m`. -/
theorem lemma_2_1_not_128 (m : ℕ) :
    ¬ ∃ I ⊆ Finset.Icc 1 m, ∑ i ∈ I, i ^ 2 = 128 := by
  rintro ⟨I, hI, hsum⟩
  have hI11 : I ⊆ Finset.Icc 1 11 := by
    intro i hi
    have hle : i ^ 2 ≤ 128 := hsum ▸ Finset.single_le_sum (f := fun i => i ^ 2)
      (fun _ _ => Nat.zero_le _) hi
    have hmem := Finset.mem_Icc.mp (hI hi)
    have hi11 : i ≤ 11 := by nlinarith
    exact Finset.mem_Icc.mpr ⟨hmem.1, hi11⟩
  have hrep := rep_of_exists 11 128 ⟨I, hI11, hsum⟩
  rw [rep_128] at hrep
  exact Bool.false_ne_true hrep

/-- **Lemma 2.1 (She–Luo), sharpness part, upper end.** For every `m ≥ 10`,
`Σ_m - 128` is not a sum of distinct squares from `[1, m]` (`128 ≤ Σ_m`, so the
subtraction is genuine). Together with `lemma_2_1` and `lemma_2_1_not_128` this
gives `L(m) = Σ_m - 257`. -/
theorem lemma_2_1_not_sub_128 (m : ℕ) (hm : 10 ≤ m) :
    128 ≤ ∑ i ∈ Finset.Icc 1 m, i ^ 2 ∧
      ¬ ∃ I ⊆ Finset.Icc 1 m, ∑ i ∈ I, i ^ 2 = ∑ i ∈ Finset.Icc 1 m, i ^ 2 - 128 := by
  have hb := sumSq_bound m hm
  refine ⟨by nlinarith, ?_⟩
  rintro ⟨I, hI, hsum⟩
  apply lemma_2_1_not_128 m
  refine ⟨Finset.Icc 1 m \ I, Finset.sdiff_subset, ?_⟩
  have hsplit := Finset.sum_sdiff hI (f := fun i => i ^ 2)
  omega

/-! ## The involution family (Cases 1 and 2) -/

/-- Composing with a transposition of two fixed points `a ≠ b` lowers `F` by
`((a+1)² - (b+1)²)²` (the paper's `2i²j² - i⁴ - j⁴ = -(i² - j²)²`). -/
theorem sunF_mul_swap {n : ℕ} (τ : Equiv.Perm (Fin n)) (a b : Fin n) (hab : a ≠ b)
    (ha : τ a = a) (hb : τ b = b) :
    (sunF (τ * Equiv.swap a b) : ℤ) =
      sunF τ - (((a : ℤ) + 1) ^ 2 - ((b : ℤ) + 1) ^ 2) ^ 2 := by
  have hdiff : (sunF (τ * Equiv.swap a b) : ℤ) - sunF τ =
      ∑ k : Fin n, ((((k : ℕ) : ℤ) + 1) ^ 2 * ((((τ * Equiv.swap a b) k : ℕ) : ℤ) + 1) ^ 2 -
        (((k : ℕ) : ℤ) + 1) ^ 2 * (((τ k : ℕ) : ℤ) + 1) ^ 2) := by
    simp only [sunF, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Finset.sum_sub_distrib]
  rw [Fintype.sum_eq_add a b hab] at hdiff
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, ha, hb]
      at hdiff
    linear_combination hdiff
  · intro k hk
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hk.1 hk.2]

/-- The involutions `τ_J` of Cases 1–2: for `2m+1 ≤ n` and `J ⊆ [1, m]`, swapping the
values `m+1-d` and `m+1+d` for every `d ∈ J` gives a permutation with
`F(τ_J) = ∑ k⁴ - ∑_{d ∈ J} (4d(m+1))²`; it fixes every point not swapped. -/
theorem exists_perm_family (n m : ℕ) (hm : 2 * m + 1 ≤ n) (J : Finset ℕ)
    (hJ : J ⊆ Finset.Icc 1 m) :
    ∃ τ : Equiv.Perm (Fin n),
      (∀ k : Fin n, (∀ d ∈ J, (k : ℕ) + d ≠ m ∧ (k : ℕ) ≠ m + d) → τ k = k) ∧
      (sunF τ : ℤ) = ∑ k : Fin n, (((k : ℕ) : ℤ) + 1) ^ 4 -
        ∑ d ∈ J, (4 * (d : ℤ) * ((m : ℤ) + 1)) ^ 2 := by
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ _ => rfl, ?_⟩
    simp only [sunF, Equiv.Perm.one_apply, Finset.sum_empty, sub_zero]
    push_cast
    exact Finset.sum_congr rfl fun k _ => by ring
  | insert d J hdJ ih =>
    have hd' := Finset.mem_Icc.mp (hJ (Finset.mem_insert_self d J))
    obtain ⟨τ, hfix, hval⟩ := ih ((Finset.subset_insert d J).trans hJ)
    let a : Fin n := ⟨m - d, by omega⟩
    let b : Fin n := ⟨m + d, by omega⟩
    have hab : a ≠ b := fun h => by
      have hv := congrArg Fin.val h
      simp only [a, b] at hv
      omega
    have hJm : ∀ d' ∈ J, 1 ≤ d' ∧ d' ≤ m ∧ d' ≠ d := fun d' hd'J =>
      have hmem := Finset.mem_Icc.mp (hJ (Finset.mem_insert_of_mem hd'J))
      ⟨hmem.1, hmem.2, fun h => hdJ (h ▸ hd'J)⟩
    have ha : τ a = a := hfix a fun d' hd'J => by
      have hd'' := hJm d' hd'J
      simp only [a]
      omega
    have hb : τ b = b := hfix b fun d' hd'J => by
      have hd'' := hJm d' hd'J
      simp only [b]
      omega
    refine ⟨τ * Equiv.swap a b, ?_, ?_⟩
    · intro k hk
      have hka : k ≠ a := fun h => by
        have hk1 := (hk d (Finset.mem_insert_self d J)).1
        rw [h] at hk1
        simp only [a] at hk1
        omega
      have hkb : k ≠ b := fun h => by
        have hk2 := (hk d (Finset.mem_insert_self d J)).2
        rw [h] at hk2
        simp only [b] at hk2
        omega
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hka hkb]
      exact hfix k fun d' hd'J => hk d' (Finset.mem_insert_of_mem hd'J)
    · rw [sunF_mul_swap τ a b hab ha hb, hval, Finset.sum_insert hdJ]
      have hacast : ((a : ℕ) : ℤ) = (m : ℤ) - d := by
        simp only [a]
        push_cast [Nat.cast_sub hd'.2]
        ring
      have hbcast : ((b : ℕ) : ℤ) = (m : ℤ) + d := by
        simp only [b]
        push_cast
        ring
      rw [hacast, hbcast]
      ring

/-- Cases 1–2 of the paper: for `n ≥ 21`, `F` hits every residue modulo `2n+1`. -/
theorem surj_of_large (n : ℕ) (hn : 21 ≤ n) :
    Function.Surjective fun τ : Equiv.Perm (Fin n) => (sunF τ : ZMod (2 * n + 1)) := by
  intro r
  set m := (n - 1) / 2 with hm_def
  have hm1 : 2 * m + 1 ≤ n := by omega
  have hm2 : n ≤ 2 * m + 2 := by omega
  have hm10 : 10 ≤ m := by omega
  -- `(4(m+1))² ≡ 1 (mod 2n+1)` since `2n+1 ∈ {4m+3, 4m+5}`.
  have hunit : (4 * ((m : ZMod (2 * n + 1)) + 1)) ^ 2 = 1 := by
    have h0 : ((2 * n + 1 : ℕ) : ZMod (2 * n + 1)) = 0 := ZMod.natCast_self _
    push_cast at h0
    rcases (show n = 2 * m + 1 ∨ n = 2 * m + 2 by omega) with hn' | hn'
    · have h4 : 4 * ((m : ZMod (2 * n + 1)) + 1) = 1 + (2 * (n : ZMod (2 * n + 1)) + 1) := by
        rw [hn']
        push_cast
        ring
      rw [h4, h0]
      ring
    · have h4 : 4 * ((m : ZMod (2 * n + 1)) + 1) = (2 * (n : ZMod (2 * n + 1)) + 1) - 1 := by
        rw [hn']
        push_cast
        ring
      rw [h4, h0]
      ring
  set C : ZMod (2 * n + 1) := ∑ k : Fin n, (((k : ℕ) : ZMod (2 * n + 1)) + 1) ^ 4 with hC
  set x : ℕ := 129 + (C - r - 129).val with hx
  have hxlt : (C - r - 129).val < 2 * n + 1 := ZMod.val_lt _
  have hb := sumSq_bound m hm10
  obtain ⟨I, hI, hsum⟩ := lemma_2_1 m hm10 x (by omega) (by nlinarith)
  obtain ⟨τ, -, hτ⟩ := exists_perm_family n m hm1 I hI
  refine ⟨τ, ?_⟩
  have hcast : (sunF τ : ZMod (2 * n + 1)) = ((sunF τ : ℤ) : ZMod (2 * n + 1)) := by
    push_cast
    rfl
  have hxcast : (x : ZMod (2 * n + 1)) = C - r := by
    rw [hx]
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  have hI' : ∑ d ∈ I, (4 * (d : ZMod (2 * n + 1)) * ((m : ZMod (2 * n + 1)) + 1)) ^ 2 =
      ((∑ d ∈ I, d ^ 2 : ℕ) : ZMod (2 * n + 1)) := by
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    linear_combination (d : ZMod (2 * n + 1)) ^ 2 * hunit
  simp only
  rw [hcast, hτ]
  push_cast
  rw [hI', hsum, hxcast, ← hC]
  ring

/-! ## Case 3: `5 ≤ n ≤ 20` by explicit witnesses -/

/-- Table checker: row `r < 2n+1` of `T` lists the images `τ 0, …, τ (n-1)` of a
permutation of `Fin n` whose `F`-value is `≡ r (mod 2n+1)`. -/
def checkTab (n : ℕ) (T : List (List ℕ)) : Bool :=
  (List.range (2 * n + 1)).all fun r =>
    let L := T.getD r []
    L.length == n && decide L.Nodup && L.all (· < n) &&
      (∑ k ∈ Finset.range n, (k + 1) ^ 2 * (L.getD k 0 + 1) ^ 2) % (2 * n + 1) == r

/-- `checkTab` rejects a table whose single row is not a permutation. -/
example : checkTab 1 [[0], [0], [1]] = false := by decide

/-- A duplicate-free list of length `n` with entries `< n` is a permutation of `Fin n`,
whose `F`-value is the list-indexed sum. -/
theorem exists_perm_of_list (n : ℕ) (L : List ℕ) (hlen : L.length = n) (hnd : L.Nodup)
    (hlt : ∀ x ∈ L, x < n) :
    ∃ τ : Equiv.Perm (Fin n),
      sunF τ = ∑ k ∈ Finset.range n, (k + 1) ^ 2 * (L.getD k 0 + 1) ^ 2 := by
  let f : Fin n → Fin n := fun k =>
    ⟨L[(k : ℕ)]'(by omega), hlt _ (List.getElem_mem _)⟩
  have hf : Function.Injective f := fun i j hij => by
    have h := congrArg Fin.val hij
    simp only [f] at h
    exact Fin.ext ((hnd.getElem_inj_iff).mp h)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.ofBijective_apply, f,
    List.getD_eq_getElem _ _ (show (k : ℕ) < L.length by omega)]

/-- Soundness of `checkTab`: a passing table proves surjectivity of `F mod (2n+1)`. -/
theorem surj_of_checkTab (n : ℕ) (T : List (List ℕ)) (h : checkTab n T = true) :
    Function.Surjective fun τ : Equiv.Perm (Fin n) => (sunF τ : ZMod (2 * n + 1)) := by
  intro r
  have hr := List.all_eq_true.mp h r.val (List.mem_range.mpr (ZMod.val_lt r))
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hr
  obtain ⟨⟨⟨hlen, hnd⟩, hlt⟩, hmod⟩ := hr
  obtain ⟨τ, hτ⟩ := exists_perm_of_list n _ hlen hnd hlt
  refine ⟨τ, ?_⟩
  simp only
  rw [← ZMod.natCast_mod, hτ, hmod, ZMod.natCast_zmod_val]

/-- Witness permutations for `n = 5`: row `r` lists `τ 0, …, τ 4` (0-indexed) with
`sunF τ ≡ r (mod 11)`. -/
def tab5 : List (List ℕ) :=
  [[0, 1, 2, 3, 4],
    [4, 3, 0, 2, 1],
    [1, 0, 2, 3, 4],
    [3, 1, 4, 0, 2],
    [1, 4, 2, 3, 0],
    [3, 0, 4, 2, 1],
    [2, 3, 1, 4, 0],
    [1, 0, 4, 2, 3],
    [1, 0, 3, 2, 4],
    [1, 0, 2, 4, 3],
    [1, 2, 4, 0, 3]]

/-- Witness permutations for `n = 6`: row `r` lists `τ 0, …, τ 5` (0-indexed) with
`sunF τ ≡ r (mod 13)`. -/
def tab6 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5],
    [2, 3, 1, 0, 5, 4],
    [3, 0, 2, 1, 5, 4],
    [1, 0, 3, 2, 5, 4],
    [5, 3, 1, 4, 2, 0],
    [3, 5, 4, 1, 0, 2],
    [2, 1, 5, 0, 4, 3],
    [4, 2, 3, 5, 1, 0],
    [4, 0, 2, 5, 3, 1],
    [0, 3, 2, 5, 4, 1],
    [2, 3, 5, 4, 1, 0],
    [4, 1, 5, 3, 2, 0],
    [4, 0, 1, 5, 2, 3]]

/-- Witness permutations for `n = 7`: row `r` lists `τ 0, …, τ 6` (0-indexed) with
`sunF τ ≡ r (mod 15)`. -/
def tab7 : List (List ℕ) :=
  [[4, 6, 1, 5, 3, 0, 2],
    [5, 1, 3, 4, 0, 2, 6],
    [4, 3, 5, 6, 0, 2, 1],
    [2, 3, 1, 5, 4, 6, 0],
    [1, 0, 5, 3, 6, 4, 2],
    [3, 6, 2, 0, 1, 5, 4],
    [5, 2, 0, 4, 3, 6, 1],
    [0, 1, 6, 2, 4, 5, 3],
    [6, 0, 5, 3, 4, 2, 1],
    [3, 2, 4, 6, 5, 1, 0],
    [4, 1, 2, 3, 5, 0, 6],
    [0, 1, 2, 3, 4, 5, 6],
    [0, 5, 4, 2, 6, 1, 3],
    [1, 0, 6, 3, 4, 2, 5],
    [4, 3, 2, 6, 1, 5, 0]]

/-- Witness permutations for `n = 8`: row `r` lists `τ 0, …, τ 7` (0-indexed) with
`sunF τ ≡ r (mod 17)`. -/
def tab8 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
    [5, 2, 7, 3, 0, 6, 1, 4],
    [5, 1, 7, 4, 6, 3, 2, 0],
    [1, 4, 6, 5, 0, 3, 2, 7],
    [6, 5, 3, 7, 0, 2, 1, 4],
    [1, 6, 3, 2, 7, 4, 5, 0],
    [7, 4, 2, 0, 1, 3, 5, 6],
    [3, 0, 1, 4, 5, 6, 2, 7],
    [2, 0, 1, 7, 5, 4, 6, 3],
    [1, 3, 6, 7, 4, 0, 2, 5],
    [4, 6, 3, 1, 2, 0, 7, 5],
    [4, 3, 5, 1, 7, 6, 2, 0],
    [0, 4, 1, 3, 5, 7, 6, 2],
    [2, 4, 1, 5, 7, 3, 0, 6],
    [2, 7, 1, 6, 3, 4, 5, 0],
    [5, 3, 1, 0, 7, 6, 2, 4],
    [0, 2, 3, 1, 4, 6, 7, 5]]

/-- Witness permutations for `n = 9`: row `r` lists `τ 0, …, τ 8` (0-indexed) with
`sunF τ ≡ r (mod 19)`. -/
def tab9 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8],
    [2, 7, 3, 1, 5, 0, 6, 4, 8],
    [1, 2, 6, 3, 5, 0, 8, 7, 4],
    [4, 3, 1, 7, 5, 6, 8, 2, 0],
    [3, 2, 4, 6, 5, 8, 1, 0, 7],
    [0, 7, 6, 1, 5, 4, 2, 3, 8],
    [6, 0, 2, 5, 1, 8, 4, 3, 7],
    [6, 4, 0, 2, 7, 8, 5, 3, 1],
    [5, 6, 1, 8, 3, 2, 7, 0, 4],
    [1, 0, 6, 7, 2, 3, 4, 8, 5],
    [2, 6, 8, 4, 1, 7, 3, 5, 0],
    [6, 2, 3, 7, 8, 0, 1, 5, 4],
    [3, 7, 5, 2, 1, 6, 4, 8, 0],
    [1, 0, 5, 8, 2, 7, 3, 6, 4],
    [4, 2, 6, 0, 3, 5, 8, 1, 7],
    [3, 2, 6, 5, 1, 0, 4, 7, 8],
    [8, 3, 6, 4, 1, 7, 5, 2, 0],
    [8, 4, 0, 7, 5, 2, 1, 6, 3],
    [3, 8, 4, 0, 6, 1, 2, 5, 7]]

/-- Witness permutations for `n = 10`: row `r` lists `τ 0, …, τ 9` (0-indexed) with
`sunF τ ≡ r (mod 21)`. -/
def tab10 : List (List ℕ) :=
  [[0, 6, 5, 1, 7, 8, 2, 4, 9, 3],
    [4, 2, 7, 5, 3, 6, 8, 1, 0, 9],
    [7, 8, 5, 2, 3, 4, 9, 0, 6, 1],
    [7, 1, 5, 6, 9, 2, 3, 4, 0, 8],
    [4, 1, 0, 5, 2, 6, 3, 9, 7, 8],
    [6, 5, 9, 4, 0, 1, 7, 8, 2, 3],
    [9, 5, 0, 3, 4, 2, 6, 7, 8, 1],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    [7, 2, 9, 3, 6, 1, 0, 4, 8, 5],
    [7, 0, 4, 5, 6, 8, 3, 9, 2, 1],
    [2, 6, 0, 7, 1, 4, 8, 3, 9, 5],
    [1, 2, 8, 0, 5, 4, 3, 7, 9, 6],
    [0, 3, 1, 4, 2, 5, 7, 6, 8, 9],
    [5, 2, 1, 0, 3, 4, 6, 7, 9, 8],
    [5, 2, 4, 0, 7, 8, 9, 1, 6, 3],
    [3, 9, 8, 1, 7, 0, 5, 4, 2, 6],
    [6, 5, 9, 4, 3, 1, 8, 7, 0, 2],
    [8, 0, 7, 1, 9, 3, 4, 6, 2, 5],
    [1, 9, 8, 5, 0, 6, 4, 7, 2, 3],
    [0, 5, 9, 8, 7, 3, 2, 6, 4, 1],
    [9, 4, 7, 3, 5, 6, 0, 8, 2, 1]]

/-- Witness permutations for `n = 11`: row `r` lists `τ 0, …, τ 10` (0-indexed) with
`sunF τ ≡ r (mod 23)`. -/
def tab11 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    [2, 10, 5, 4, 1, 3, 7, 8, 6, 0, 9],
    [6, 2, 4, 9, 1, 10, 5, 8, 7, 3, 0],
    [7, 4, 8, 5, 10, 0, 3, 2, 6, 1, 9],
    [4, 8, 1, 7, 9, 6, 5, 0, 10, 3, 2],
    [8, 6, 1, 9, 4, 10, 3, 5, 2, 7, 0],
    [3, 6, 1, 5, 7, 9, 0, 4, 10, 8, 2],
    [5, 7, 8, 1, 10, 2, 3, 9, 4, 0, 6],
    [2, 0, 1, 4, 8, 5, 10, 9, 3, 7, 6],
    [9, 4, 2, 3, 10, 0, 6, 8, 7, 1, 5],
    [5, 4, 0, 2, 6, 7, 8, 10, 3, 9, 1],
    [2, 7, 9, 1, 4, 0, 6, 10, 8, 3, 5],
    [1, 6, 8, 9, 5, 2, 7, 10, 3, 4, 0],
    [9, 6, 4, 0, 7, 1, 2, 8, 3, 10, 5],
    [6, 1, 4, 3, 8, 10, 5, 7, 0, 9, 2],
    [3, 0, 10, 4, 5, 6, 1, 2, 7, 8, 9],
    [4, 9, 10, 8, 5, 0, 1, 6, 2, 3, 7],
    [1, 0, 4, 7, 2, 6, 5, 3, 9, 10, 8],
    [10, 1, 4, 7, 9, 6, 2, 5, 8, 0, 3],
    [4, 3, 9, 8, 5, 10, 0, 7, 6, 2, 1],
    [3, 6, 1, 4, 0, 8, 5, 7, 2, 9, 10],
    [8, 0, 9, 7, 5, 4, 1, 6, 10, 2, 3],
    [4, 5, 10, 0, 2, 8, 3, 6, 1, 9, 7]]

/-- Witness permutations for `n = 12`: row `r` lists `τ 0, …, τ 11` (0-indexed) with
`sunF τ ≡ r (mod 25)`. -/
def tab12 : List (List ℕ) :=
  [[5, 11, 10, 7, 6, 1, 2, 9, 8, 0, 4, 3],
    [10, 5, 11, 1, 0, 4, 3, 8, 2, 7, 6, 9],
    [5, 11, 7, 1, 2, 4, 0, 3, 8, 6, 10, 9],
    [9, 2, 10, 1, 3, 4, 0, 7, 8, 6, 11, 5],
    [0, 1, 10, 4, 8, 3, 9, 7, 11, 2, 5, 6],
    [11, 9, 3, 10, 2, 5, 4, 8, 0, 1, 6, 7],
    [1, 0, 4, 7, 11, 6, 9, 10, 3, 2, 5, 8],
    [5, 9, 6, 0, 8, 3, 4, 1, 7, 2, 11, 10],
    [5, 11, 9, 7, 3, 10, 6, 1, 0, 4, 2, 8],
    [9, 7, 10, 5, 4, 0, 2, 8, 11, 6, 1, 3],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
    [1, 10, 5, 0, 3, 7, 9, 2, 11, 6, 4, 8],
    [5, 11, 1, 8, 9, 4, 2, 7, 3, 6, 10, 0],
    [5, 0, 10, 9, 1, 11, 2, 6, 4, 8, 7, 3],
    [1, 10, 9, 0, 8, 6, 3, 5, 7, 2, 11, 4],
    [4, 0, 3, 5, 10, 11, 9, 7, 2, 1, 8, 6],
    [6, 5, 1, 9, 0, 4, 7, 10, 2, 8, 11, 3],
    [9, 3, 2, 8, 5, 0, 6, 10, 4, 7, 1, 11],
    [0, 6, 1, 3, 9, 2, 10, 11, 5, 8, 7, 4],
    [6, 11, 8, 10, 4, 3, 9, 7, 2, 5, 1, 0],
    [2, 11, 4, 0, 5, 8, 3, 6, 9, 7, 1, 10],
    [7, 9, 10, 6, 11, 4, 5, 2, 1, 3, 8, 0],
    [5, 10, 6, 3, 11, 9, 8, 4, 1, 2, 0, 7],
    [6, 2, 9, 4, 3, 7, 10, 1, 11, 5, 0, 8],
    [11, 9, 10, 2, 6, 7, 8, 0, 1, 5, 3, 4]]

/-- Witness permutations for `n = 13`: row `r` lists `τ 0, …, τ 12` (0-indexed) with
`sunF τ ≡ r (mod 27)`. -/
def tab13 : List (List ℕ) :=
  [[8, 11, 12, 5, 3, 9, 1, 6, 0, 4, 10, 2, 7],
    [10, 12, 2, 7, 4, 6, 9, 0, 8, 3, 11, 1, 5],
    [1, 11, 9, 8, 12, 3, 0, 2, 4, 7, 6, 10, 5],
    [11, 9, 1, 0, 6, 4, 5, 7, 8, 3, 12, 10, 2],
    [2, 7, 12, 3, 4, 8, 11, 9, 10, 6, 0, 5, 1],
    [12, 0, 7, 6, 11, 9, 4, 2, 3, 8, 5, 1, 10],
    [2, 9, 12, 1, 6, 10, 11, 0, 8, 4, 3, 7, 5],
    [1, 6, 8, 3, 0, 9, 5, 7, 11, 2, 4, 12, 10],
    [5, 8, 3, 11, 10, 12, 2, 9, 1, 7, 0, 4, 6],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    [8, 1, 9, 10, 12, 2, 4, 6, 5, 3, 7, 0, 11],
    [2, 6, 4, 0, 11, 3, 12, 5, 10, 8, 7, 9, 1],
    [12, 11, 2, 0, 7, 1, 8, 5, 9, 3, 4, 10, 6],
    [7, 12, 3, 4, 10, 2, 5, 8, 6, 0, 1, 11, 9],
    [2, 0, 3, 7, 8, 1, 9, 5, 6, 4, 11, 12, 10],
    [1, 12, 11, 10, 6, 4, 8, 5, 0, 9, 2, 3, 7],
    [1, 7, 5, 9, 10, 8, 3, 2, 0, 12, 11, 4, 6],
    [10, 5, 3, 4, 8, 0, 12, 9, 1, 11, 6, 7, 2],
    [1, 3, 5, 4, 2, 10, 7, 6, 12, 0, 11, 9, 8],
    [4, 10, 8, 9, 5, 7, 11, 0, 12, 1, 3, 2, 6],
    [12, 5, 2, 3, 7, 10, 6, 0, 8, 1, 4, 11, 9],
    [11, 4, 12, 5, 6, 7, 9, 0, 2, 10, 8, 3, 1],
    [1, 5, 0, 3, 10, 8, 11, 9, 12, 4, 7, 2, 6],
    [0, 11, 6, 9, 12, 4, 10, 1, 7, 8, 2, 3, 5],
    [3, 5, 6, 10, 8, 0, 9, 1, 11, 12, 4, 7, 2],
    [2, 11, 10, 12, 9, 6, 7, 0, 5, 3, 4, 8, 1],
    [10, 2, 4, 12, 5, 9, 0, 11, 3, 8, 7, 1, 6]]

/-- Witness permutations for `n = 14`: row `r` lists `τ 0, …, τ 13` (0-indexed) with
`sunF τ ≡ r (mod 29)`. -/
def tab14 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    [11, 9, 6, 8, 3, 5, 10, 2, 0, 13, 7, 12, 4, 1],
    [6, 13, 5, 10, 7, 9, 3, 11, 1, 0, 8, 12, 4, 2],
    [1, 11, 6, 9, 3, 2, 7, 0, 8, 4, 12, 13, 5, 10],
    [6, 13, 9, 7, 3, 5, 10, 4, 2, 1, 8, 0, 12, 11],
    [7, 11, 4, 12, 10, 1, 5, 9, 8, 3, 6, 13, 2, 0],
    [4, 8, 7, 11, 3, 10, 1, 12, 5, 9, 2, 0, 6, 13],
    [13, 7, 9, 11, 6, 8, 5, 10, 4, 2, 12, 3, 1, 0],
    [6, 2, 7, 0, 12, 3, 10, 13, 8, 9, 11, 5, 4, 1],
    [0, 3, 13, 7, 5, 12, 8, 11, 2, 9, 4, 1, 10, 6],
    [4, 11, 2, 8, 13, 5, 10, 1, 7, 3, 0, 12, 9, 6],
    [2, 7, 5, 13, 8, 3, 12, 4, 0, 6, 10, 1, 11, 9],
    [6, 1, 0, 7, 3, 5, 8, 9, 11, 2, 12, 4, 13, 10],
    [8, 0, 4, 12, 13, 10, 7, 9, 2, 6, 3, 11, 1, 5],
    [0, 13, 4, 9, 11, 12, 7, 10, 3, 2, 6, 1, 8, 5],
    [12, 6, 10, 2, 11, 9, 8, 5, 0, 3, 1, 13, 7, 4],
    [10, 13, 12, 5, 4, 2, 9, 6, 8, 1, 3, 11, 0, 7],
    [10, 11, 0, 9, 5, 8, 13, 7, 2, 3, 12, 4, 1, 6],
    [1, 2, 11, 10, 4, 3, 9, 12, 5, 13, 6, 8, 0, 7],
    [2, 3, 1, 0, 8, 12, 6, 11, 9, 5, 13, 7, 10, 4],
    [1, 5, 8, 9, 11, 6, 4, 12, 10, 7, 13, 3, 2, 0],
    [5, 12, 2, 4, 0, 6, 10, 1, 8, 9, 3, 11, 13, 7],
    [12, 1, 8, 10, 2, 11, 9, 5, 7, 0, 13, 4, 3, 6],
    [4, 0, 12, 5, 1, 10, 3, 8, 6, 11, 7, 9, 13, 2],
    [1, 7, 3, 11, 5, 9, 0, 13, 10, 8, 4, 2, 6, 12],
    [1, 0, 4, 12, 6, 7, 2, 11, 13, 8, 9, 3, 10, 5],
    [6, 12, 0, 8, 7, 11, 1, 5, 9, 4, 3, 13, 2, 10],
    [11, 6, 0, 4, 12, 5, 3, 13, 9, 8, 1, 10, 2, 7],
    [4, 6, 11, 1, 12, 0, 7, 10, 13, 3, 8, 2, 9, 5]]

/-- Witness permutations for `n = 15`: row `r` lists `τ 0, …, τ 14` (0-indexed) with
`sunF τ ≡ r (mod 31)`. -/
def tab15 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    [4, 10, 8, 2, 12, 11, 6, 9, 3, 7, 14, 13, 0, 5, 1],
    [8, 7, 4, 9, 11, 12, 10, 14, 6, 13, 2, 3, 1, 0, 5],
    [7, 9, 1, 13, 11, 8, 4, 6, 14, 2, 0, 10, 5, 3, 12],
    [11, 1, 14, 7, 0, 10, 9, 13, 4, 8, 5, 6, 2, 3, 12],
    [7, 3, 4, 13, 2, 14, 10, 8, 11, 6, 12, 1, 9, 5, 0],
    [6, 0, 8, 7, 5, 13, 3, 9, 4, 1, 2, 12, 10, 11, 14],
    [8, 11, 13, 7, 0, 14, 5, 9, 10, 1, 6, 2, 12, 4, 3],
    [4, 2, 1, 6, 5, 10, 14, 8, 7, 13, 12, 0, 3, 9, 11],
    [12, 5, 10, 14, 2, 1, 6, 3, 8, 11, 13, 4, 0, 9, 7],
    [7, 10, 8, 4, 12, 2, 1, 6, 3, 14, 9, 5, 0, 13, 11],
    [0, 11, 14, 4, 8, 6, 1, 10, 13, 3, 7, 9, 5, 12, 2],
    [7, 5, 10, 12, 9, 14, 1, 13, 0, 4, 11, 3, 2, 6, 8],
    [11, 1, 7, 10, 9, 3, 2, 4, 0, 14, 13, 12, 8, 6, 5],
    [9, 5, 1, 10, 3, 12, 14, 8, 4, 6, 11, 2, 0, 7, 13],
    [8, 0, 14, 1, 13, 11, 10, 4, 2, 7, 12, 9, 5, 3, 6],
    [8, 2, 13, 10, 14, 9, 12, 7, 1, 6, 0, 4, 3, 5, 11],
    [12, 7, 3, 4, 9, 11, 0, 5, 2, 10, 1, 13, 6, 14, 8],
    [8, 4, 13, 1, 0, 9, 12, 11, 3, 10, 2, 14, 7, 6, 5],
    [12, 9, 14, 1, 11, 10, 5, 8, 13, 2, 4, 0, 7, 3, 6],
    [6, 0, 5, 7, 10, 3, 4, 1, 12, 11, 8, 14, 13, 9, 2],
    [0, 13, 12, 1, 9, 3, 14, 2, 7, 8, 6, 4, 11, 5, 10],
    [1, 9, 6, 11, 0, 5, 7, 4, 10, 14, 13, 3, 8, 12, 2],
    [0, 10, 11, 5, 9, 1, 6, 4, 12, 13, 3, 2, 14, 8, 7],
    [9, 13, 7, 10, 14, 11, 2, 12, 0, 6, 5, 8, 3, 1, 4],
    [11, 1, 8, 10, 0, 14, 3, 4, 7, 5, 2, 9, 13, 12, 6],
    [7, 2, 13, 12, 1, 4, 10, 3, 14, 6, 9, 5, 11, 8, 0],
    [10, 13, 6, 0, 2, 5, 9, 12, 1, 8, 11, 7, 14, 4, 3],
    [2, 1, 9, 11, 13, 14, 6, 12, 4, 3, 5, 8, 0, 7, 10],
    [2, 14, 10, 5, 12, 1, 3, 7, 6, 4, 0, 13, 9, 11, 8],
    [2, 10, 12, 13, 5, 3, 14, 11, 7, 0, 1, 9, 6, 8, 4]]

/-- Witness permutations for `n = 16`: row `r` lists `τ 0, …, τ 15` (0-indexed) with
`sunF τ ≡ r (mod 33)`. -/
def tab16 : List (List ℕ) :=
  [[2, 12, 8, 14, 13, 10, 3, 1, 6, 15, 4, 5, 7, 9, 11, 0],
    [15, 3, 2, 13, 10, 4, 11, 8, 0, 14, 1, 7, 6, 5, 12, 9],
    [1, 7, 8, 3, 6, 4, 0, 14, 11, 12, 5, 10, 9, 13, 15, 2],
    [8, 11, 7, 10, 14, 9, 0, 2, 1, 15, 5, 13, 3, 12, 6, 4],
    [10, 0, 5, 1, 12, 2, 15, 6, 8, 14, 7, 13, 3, 4, 11, 9],
    [4, 9, 8, 7, 3, 0, 11, 6, 13, 1, 10, 12, 15, 5, 14, 2],
    [2, 4, 12, 8, 7, 10, 15, 13, 0, 14, 5, 1, 3, 11, 6, 9],
    [8, 14, 2, 11, 3, 15, 7, 0, 6, 10, 5, 1, 9, 13, 12, 4],
    [10, 1, 12, 9, 15, 4, 13, 11, 14, 3, 6, 8, 5, 7, 0, 2],
    [8, 10, 1, 2, 13, 9, 0, 7, 12, 14, 3, 6, 5, 15, 4, 11],
    [15, 10, 13, 4, 14, 12, 8, 1, 9, 5, 0, 7, 11, 3, 2, 6],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [1, 8, 7, 3, 13, 4, 6, 15, 12, 2, 11, 0, 5, 9, 10, 14],
    [4, 15, 14, 7, 13, 1, 5, 11, 9, 2, 12, 6, 8, 10, 0, 3],
    [6, 4, 9, 8, 15, 5, 0, 10, 2, 14, 12, 7, 13, 3, 1, 11],
    [6, 13, 11, 7, 0, 5, 2, 12, 1, 15, 9, 10, 8, 4, 14, 3],
    [4, 10, 6, 13, 2, 7, 12, 1, 5, 14, 9, 0, 8, 11, 3, 15],
    [5, 8, 11, 1, 6, 7, 15, 12, 10, 0, 9, 14, 4, 13, 3, 2],
    [10, 13, 14, 7, 1, 5, 12, 2, 4, 15, 8, 0, 3, 6, 11, 9],
    [5, 2, 12, 13, 15, 1, 9, 4, 0, 6, 14, 7, 3, 10, 11, 8],
    [11, 15, 1, 7, 12, 6, 14, 13, 10, 8, 0, 5, 4, 3, 2, 9],
    [5, 7, 9, 14, 0, 4, 2, 3, 15, 12, 6, 13, 11, 1, 10, 8],
    [5, 13, 11, 3, 8, 9, 2, 4, 1, 14, 10, 7, 0, 12, 6, 15],
    [13, 12, 4, 8, 0, 14, 3, 2, 5, 15, 1, 10, 7, 11, 9, 6],
    [2, 8, 13, 15, 10, 7, 11, 0, 4, 5, 1, 3, 14, 12, 6, 9],
    [4, 14, 6, 13, 11, 5, 1, 0, 9, 8, 2, 7, 15, 12, 10, 3],
    [14, 1, 12, 4, 7, 15, 0, 3, 6, 13, 8, 11, 9, 10, 2, 5],
    [15, 7, 14, 9, 5, 8, 10, 4, 0, 11, 6, 2, 13, 1, 12, 3],
    [11, 14, 3, 8, 9, 1, 10, 4, 7, 15, 2, 5, 13, 12, 6, 0],
    [6, 4, 2, 13, 1, 10, 11, 14, 5, 15, 7, 9, 12, 8, 0, 3],
    [4, 0, 1, 10, 3, 9, 2, 8, 15, 14, 5, 13, 7, 11, 6, 12],
    [7, 12, 1, 5, 14, 2, 4, 10, 3, 0, 13, 15, 9, 11, 6, 8],
    [5, 15, 2, 1, 6, 0, 14, 8, 4, 13, 7, 10, 12, 3, 11, 9]]

/-- Witness permutations for `n = 17`: row `r` lists `τ 0, …, τ 16` (0-indexed) with
`sunF τ ≡ r (mod 35)`. -/
def tab17 : List (List ℕ) :=
  [[13, 7, 5, 0, 10, 3, 12, 14, 2, 1, 6, 11, 4, 15, 16, 8, 9],
    [6, 3, 11, 12, 5, 16, 10, 0, 2, 15, 1, 4, 13, 9, 7, 14, 8],
    [10, 4, 1, 16, 14, 11, 5, 9, 15, 6, 2, 12, 13, 8, 3, 0, 7],
    [11, 4, 5, 14, 6, 7, 3, 0, 8, 16, 2, 13, 1, 15, 9, 10, 12],
    [3, 0, 13, 8, 11, 9, 12, 15, 16, 2, 4, 14, 6, 7, 1, 10, 5],
    [2, 16, 7, 6, 4, 11, 9, 0, 1, 8, 15, 13, 5, 10, 14, 12, 3],
    [11, 4, 9, 8, 15, 7, 1, 2, 5, 16, 12, 6, 13, 10, 3, 14, 0],
    [2, 5, 1, 12, 7, 0, 16, 14, 6, 8, 9, 10, 15, 3, 13, 11, 4],
    [6, 0, 1, 9, 3, 14, 13, 12, 15, 16, 2, 8, 10, 11, 4, 5, 7],
    [4, 10, 11, 14, 9, 12, 1, 16, 3, 7, 0, 2, 15, 5, 6, 13, 8],
    [5, 11, 0, 2, 6, 12, 14, 9, 16, 8, 4, 13, 3, 1, 7, 15, 10],
    [11, 15, 8, 0, 5, 1, 2, 7, 16, 14, 4, 12, 10, 9, 13, 6, 3],
    [9, 2, 5, 8, 13, 16, 15, 12, 10, 4, 11, 0, 6, 14, 7, 3, 1],
    [5, 2, 8, 4, 16, 13, 7, 3, 0, 14, 1, 9, 15, 11, 6, 12, 10],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
    [8, 12, 14, 1, 5, 7, 13, 6, 4, 3, 0, 9, 16, 15, 11, 10, 2],
    [5, 14, 0, 2, 15, 12, 8, 13, 1, 7, 9, 6, 10, 16, 4, 3, 11],
    [13, 8, 4, 0, 1, 14, 7, 12, 2, 16, 15, 6, 9, 10, 3, 5, 11],
    [13, 12, 8, 14, 4, 16, 5, 9, 2, 6, 11, 15, 10, 3, 7, 0, 1],
    [15, 16, 5, 6, 7, 1, 11, 9, 14, 2, 13, 0, 10, 3, 8, 12, 4],
    [5, 14, 6, 1, 16, 4, 2, 3, 0, 8, 15, 13, 11, 10, 7, 9, 12],
    [10, 12, 1, 6, 9, 0, 16, 7, 15, 8, 11, 2, 14, 4, 5, 13, 3],
    [6, 2, 7, 1, 13, 8, 15, 3, 10, 14, 9, 0, 12, 4, 16, 5, 11],
    [12, 8, 4, 0, 2, 14, 11, 3, 16, 7, 5, 10, 15, 13, 9, 6, 1],
    [9, 10, 16, 6, 14, 11, 4, 15, 7, 1, 5, 8, 13, 0, 2, 12, 3],
    [9, 2, 16, 4, 12, 11, 8, 10, 14, 7, 1, 0, 3, 5, 13, 6, 15],
    [4, 10, 8, 12, 13, 2, 11, 16, 1, 14, 15, 3, 9, 7, 6, 0, 5],
    [12, 6, 7, 10, 1, 11, 0, 15, 9, 8, 16, 3, 4, 2, 13, 5, 14],
    [16, 8, 13, 7, 6, 12, 9, 14, 4, 0, 3, 11, 10, 2, 15, 1, 5],
    [0, 3, 4, 5, 6, 8, 9, 13, 2, 10, 16, 1, 7, 12, 15, 11, 14],
    [9, 0, 5, 11, 15, 16, 2, 6, 13, 3, 4, 1, 12, 8, 14, 7, 10],
    [11, 3, 7, 9, 1, 5, 16, 2, 13, 12, 4, 14, 8, 15, 10, 6, 0],
    [11, 4, 10, 6, 1, 2, 13, 9, 14, 16, 3, 5, 12, 8, 7, 0, 15],
    [2, 7, 4, 15, 0, 5, 16, 1, 12, 3, 9, 14, 8, 6, 10, 13, 11],
    [6, 13, 10, 15, 14, 2, 9, 11, 5, 3, 8, 0, 7, 1, 4, 12, 16]]

/-- Witness permutations for `n = 18`: row `r` lists `τ 0, …, τ 17` (0-indexed) with
`sunF τ ≡ r (mod 37)`. -/
def tab18 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
    [7, 4, 13, 9, 2, 0, 17, 5, 12, 10, 8, 15, 16, 1, 6, 11, 14, 3],
    [10, 9, 14, 17, 1, 4, 3, 0, 7, 16, 11, 6, 8, 5, 15, 13, 12, 2],
    [7, 3, 5, 0, 11, 15, 2, 12, 16, 17, 4, 9, 13, 10, 1, 6, 8, 14],
    [8, 3, 16, 5, 14, 10, 0, 17, 2, 13, 9, 12, 15, 7, 1, 11, 6, 4],
    [14, 8, 15, 2, 6, 0, 5, 12, 17, 13, 4, 9, 3, 10, 16, 7, 11, 1],
    [11, 3, 5, 12, 6, 1, 16, 4, 15, 13, 17, 14, 8, 2, 0, 7, 10, 9],
    [12, 8, 13, 11, 6, 16, 10, 3, 9, 15, 2, 0, 7, 5, 1, 14, 4, 17],
    [16, 2, 5, 1, 13, 8, 3, 4, 10, 7, 6, 15, 11, 17, 12, 9, 14, 0],
    [15, 2, 0, 7, 8, 4, 1, 12, 11, 14, 17, 5, 13, 6, 16, 3, 10, 9],
    [2, 15, 4, 6, 8, 3, 12, 11, 10, 0, 7, 17, 13, 14, 9, 16, 5, 1],
    [1, 15, 7, 13, 17, 5, 8, 11, 9, 6, 4, 10, 12, 14, 0, 16, 2, 3],
    [12, 11, 3, 5, 14, 0, 8, 15, 17, 1, 9, 2, 4, 13, 7, 6, 10, 16],
    [10, 3, 2, 11, 17, 12, 9, 16, 0, 8, 15, 1, 6, 4, 7, 14, 13, 5],
    [10, 4, 9, 16, 7, 14, 5, 1, 6, 11, 13, 8, 0, 12, 2, 3, 17, 15],
    [2, 9, 0, 7, 17, 8, 4, 1, 12, 14, 3, 10, 11, 5, 13, 16, 6, 15],
    [2, 4, 3, 0, 17, 11, 6, 12, 5, 14, 10, 1, 9, 8, 16, 7, 13, 15],
    [13, 17, 9, 12, 2, 4, 7, 14, 1, 16, 5, 10, 8, 3, 0, 15, 11, 6],
    [13, 10, 16, 9, 6, 14, 4, 8, 15, 12, 5, 0, 3, 11, 1, 7, 2, 17],
    [3, 15, 14, 2, 9, 11, 1, 17, 12, 0, 4, 13, 16, 5, 10, 8, 6, 7],
    [7, 0, 5, 8, 9, 2, 3, 16, 10, 13, 17, 15, 11, 12, 6, 14, 4, 1],
    [13, 8, 10, 17, 6, 16, 9, 5, 12, 15, 2, 3, 14, 1, 11, 7, 4, 0],
    [4, 16, 9, 17, 0, 3, 15, 1, 5, 8, 2, 7, 13, 11, 12, 14, 6, 10],
    [14, 16, 3, 13, 7, 0, 10, 15, 2, 6, 9, 17, 4, 5, 12, 8, 1, 11],
    [15, 7, 14, 11, 6, 1, 16, 5, 3, 9, 12, 0, 13, 8, 4, 17, 2, 10],
    [11, 8, 10, 4, 0, 1, 9, 5, 13, 14, 7, 6, 16, 15, 2, 12, 3, 17],
    [15, 8, 12, 7, 3, 2, 1, 0, 14, 9, 11, 16, 5, 6, 13, 4, 17, 10],
    [2, 15, 9, 6, 4, 11, 17, 0, 14, 16, 3, 13, 8, 12, 1, 7, 10, 5],
    [2, 15, 8, 9, 11, 0, 3, 1, 7, 10, 13, 12, 4, 14, 6, 17, 5, 16],
    [5, 6, 7, 4, 16, 1, 2, 17, 11, 13, 9, 15, 14, 3, 0, 10, 8, 12],
    [12, 3, 10, 9, 7, 14, 8, 6, 1, 5, 0, 11, 13, 4, 17, 16, 15, 2],
    [6, 4, 15, 10, 11, 13, 8, 0, 9, 17, 2, 16, 3, 1, 14, 12, 5, 7],
    [11, 0, 16, 8, 10, 17, 13, 7, 2, 5, 15, 9, 6, 14, 1, 3, 4, 12],
    [3, 16, 2, 10, 9, 14, 15, 4, 17, 7, 1, 12, 8, 5, 0, 6, 11, 13],
    [10, 13, 17, 15, 11, 7, 0, 14, 5, 12, 4, 16, 8, 2, 9, 3, 1, 6],
    [15, 10, 3, 5, 14, 11, 7, 0, 17, 13, 12, 8, 6, 16, 1, 4, 9, 2],
    [16, 17, 11, 13, 2, 9, 7, 12, 6, 0, 15, 14, 4, 10, 3, 1, 8, 5]]

/-- Witness permutations for `n = 19`: row `r` lists `τ 0, …, τ 18` (0-indexed) with
`sunF τ ≡ r (mod 39)`. -/
def tab19 : List (List ℕ) :=
  [[11, 16, 0, 3, 2, 1, 4, 13, 5, 7, 8, 17, 14, 12, 9, 15, 6, 18, 10],
    [3, 4, 15, 10, 7, 11, 18, 6, 5, 16, 9, 13, 8, 1, 0, 2, 12, 17, 14],
    [0, 2, 11, 18, 1, 15, 4, 10, 17, 3, 12, 8, 13, 6, 14, 9, 16, 7, 5],
    [8, 4, 6, 2, 3, 14, 11, 7, 5, 12, 17, 9, 18, 10, 13, 0, 1, 16, 15],
    [17, 15, 9, 1, 14, 4, 2, 8, 3, 11, 5, 6, 10, 13, 18, 0, 16, 7, 12],
    [7, 11, 17, 8, 16, 4, 6, 2, 15, 5, 18, 1, 3, 0, 13, 14, 12, 10, 9],
    [6, 13, 3, 14, 0, 12, 1, 18, 8, 2, 11, 7, 10, 4, 5, 17, 9, 15, 16],
    [7, 5, 12, 18, 13, 3, 17, 4, 11, 16, 10, 14, 9, 1, 15, 6, 0, 2, 8],
    [9, 17, 16, 11, 1, 2, 14, 8, 0, 3, 18, 13, 7, 12, 10, 5, 15, 4, 6],
    [9, 12, 18, 6, 11, 5, 7, 14, 1, 3, 4, 16, 17, 2, 13, 0, 10, 8, 15],
    [16, 17, 11, 8, 7, 9, 13, 0, 1, 5, 10, 2, 3, 18, 12, 4, 6, 14, 15],
    [14, 13, 18, 0, 9, 12, 5, 11, 15, 4, 17, 10, 8, 1, 2, 7, 6, 3, 16],
    [15, 3, 11, 14, 5, 9, 17, 2, 1, 6, 13, 18, 4, 7, 0, 10, 12, 8, 16],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18],
    [7, 8, 2, 3, 16, 12, 10, 0, 11, 15, 18, 14, 9, 1, 6, 4, 13, 17, 5],
    [14, 1, 4, 17, 18, 8, 7, 12, 13, 10, 2, 15, 3, 5, 11, 16, 6, 0, 9],
    [11, 7, 18, 12, 10, 17, 16, 15, 3, 1, 6, 2, 5, 14, 8, 13, 4, 9, 0],
    [15, 0, 2, 16, 4, 12, 18, 9, 17, 3, 7, 5, 1, 6, 13, 10, 8, 14, 11],
    [1, 7, 6, 9, 11, 10, 2, 16, 17, 0, 15, 8, 4, 5, 12, 14, 3, 18, 13],
    [10, 3, 14, 9, 4, 5, 15, 13, 16, 1, 2, 11, 8, 0, 6, 17, 7, 18, 12],
    [12, 10, 11, 14, 1, 17, 8, 6, 5, 0, 7, 2, 9, 18, 4, 3, 15, 13, 16],
    [2, 3, 1, 13, 10, 18, 8, 5, 17, 14, 6, 9, 15, 0, 11, 16, 12, 7, 4],
    [12, 5, 15, 16, 7, 17, 10, 9, 6, 18, 0, 4, 1, 2, 11, 3, 14, 8, 13],
    [5, 3, 0, 16, 7, 15, 17, 11, 4, 12, 6, 2, 8, 18, 13, 9, 14, 10, 1],
    [0, 9, 12, 6, 17, 13, 10, 15, 3, 18, 2, 4, 11, 7, 14, 1, 8, 5, 16],
    [18, 8, 7, 14, 5, 9, 2, 11, 3, 16, 6, 0, 13, 1, 12, 4, 10, 15, 17],
    [15, 17, 18, 1, 14, 12, 11, 2, 4, 3, 5, 7, 9, 13, 6, 10, 16, 8, 0],
    [11, 6, 5, 0, 16, 3, 7, 2, 13, 9, 18, 10, 17, 12, 15, 1, 4, 14, 8],
    [17, 18, 1, 8, 4, 6, 15, 10, 14, 0, 2, 11, 16, 7, 3, 13, 9, 5, 12],
    [5, 9, 16, 3, 17, 6, 10, 7, 18, 8, 15, 11, 2, 14, 1, 0, 4, 12, 13],
    [0, 17, 4, 6, 9, 2, 3, 15, 11, 14, 7, 18, 13, 16, 12, 5, 8, 10, 1],
    [9, 5, 10, 0, 13, 16, 2, 11, 12, 8, 3, 6, 17, 4, 7, 14, 15, 18, 1],
    [4, 13, 17, 16, 1, 9, 11, 0, 7, 15, 3, 5, 18, 12, 14, 8, 10, 2, 6],
    [13, 15, 8, 6, 2, 18, 10, 3, 9, 0, 16, 7, 1, 5, 11, 14, 17, 12, 4],
    [0, 9, 14, 8, 18, 2, 6, 11, 17, 13, 3, 12, 10, 7, 16, 5, 4, 1, 15],
    [13, 3, 12, 14, 16, 9, 5, 0, 11, 17, 6, 7, 8, 18, 4, 1, 2, 10, 15],
    [18, 13, 3, 10, 7, 16, 1, 17, 14, 9, 0, 12, 15, 6, 4, 5, 2, 11, 8],
    [13, 17, 3, 6, 16, 8, 18, 9, 12, 1, 15, 0, 4, 11, 2, 14, 10, 5, 7],
    [15, 2, 18, 1, 10, 11, 17, 6, 4, 0, 14, 7, 8, 9, 3, 5, 13, 12, 16]]

/-- Witness permutations for `n = 20`: row `r` lists `τ 0, …, τ 19` (0-indexed) with
`sunF τ ≡ r (mod 41)`. -/
def tab20 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19],
    [10, 6, 8, 15, 0, 18, 13, 2, 12, 9, 3, 7, 1, 5, 17, 19, 4, 14, 16, 11],
    [9, 5, 7, 4, 18, 1, 8, 6, 17, 14, 0, 15, 3, 19, 12, 13, 11, 16, 10, 2],
    [16, 3, 14, 7, 6, 4, 2, 13, 10, 1, 17, 9, 12, 18, 15, 8, 11, 0, 5, 19],
    [18, 15, 1, 19, 12, 10, 2, 17, 3, 16, 6, 7, 11, 5, 8, 0, 9, 14, 4, 13],
    [4, 2, 6, 17, 9, 8, 10, 7, 12, 1, 14, 16, 3, 5, 13, 15, 11, 18, 0, 19],
    [17, 14, 11, 6, 2, 13, 5, 8, 12, 18, 15, 3, 0, 16, 7, 10, 4, 19, 1, 9],
    [7, 18, 13, 5, 2, 6, 8, 19, 14, 4, 10, 12, 16, 15, 17, 0, 11, 1, 3, 9],
    [0, 4, 9, 3, 19, 2, 6, 16, 13, 7, 8, 17, 12, 15, 5, 10, 11, 14, 1, 18],
    [1, 2, 0, 10, 16, 5, 6, 11, 4, 19, 17, 12, 3, 13, 8, 14, 7, 18, 15, 9],
    [8, 18, 15, 5, 0, 11, 12, 14, 6, 16, 13, 17, 9, 1, 7, 10, 2, 3, 4, 19],
    [1, 0, 16, 17, 6, 2, 11, 4, 14, 18, 8, 10, 3, 19, 9, 12, 15, 5, 13, 7],
    [14, 13, 10, 3, 2, 8, 5, 4, 18, 16, 7, 9, 0, 11, 12, 6, 19, 1, 15, 17],
    [9, 7, 2, 4, 0, 15, 12, 5, 11, 6, 10, 13, 18, 19, 17, 1, 3, 8, 16, 14],
    [6, 1, 14, 12, 10, 4, 8, 11, 17, 13, 5, 3, 0, 16, 9, 7, 18, 19, 15, 2],
    [10, 8, 15, 16, 13, 19, 12, 11, 17, 2, 14, 5, 7, 6, 1, 0, 3, 18, 4, 9],
    [8, 17, 3, 4, 0, 1, 9, 7, 19, 16, 15, 2, 12, 13, 10, 11, 5, 6, 14, 18],
    [14, 6, 10, 3, 9, 18, 7, 1, 15, 16, 13, 11, 5, 19, 4, 0, 17, 12, 2, 8],
    [18, 13, 2, 17, 19, 15, 14, 12, 11, 0, 3, 4, 16, 10, 1, 7, 9, 6, 8, 5],
    [16, 12, 17, 11, 13, 10, 5, 18, 15, 4, 3, 2, 9, 1, 19, 6, 7, 0, 14, 8],
    [18, 8, 3, 16, 13, 19, 12, 14, 4, 2, 10, 5, 6, 17, 7, 15, 0, 1, 11, 9],
    [5, 9, 1, 15, 10, 7, 3, 2, 6, 12, 18, 13, 4, 0, 11, 14, 8, 19, 17, 16],
    [5, 9, 16, 4, 7, 15, 6, 17, 11, 8, 13, 19, 18, 2, 10, 3, 1, 0, 12, 14],
    [11, 17, 8, 5, 0, 1, 12, 19, 7, 3, 18, 13, 9, 14, 6, 2, 16, 10, 4, 15],
    [12, 1, 4, 5, 2, 16, 0, 14, 19, 3, 9, 18, 10, 13, 11, 15, 6, 7, 17, 8],
    [14, 3, 0, 5, 2, 9, 8, 18, 10, 15, 19, 4, 11, 1, 12, 17, 16, 13, 6, 7],
    [4, 18, 11, 16, 9, 5, 10, 17, 3, 13, 7, 15, 1, 19, 2, 6, 8, 14, 12, 0],
    [2, 6, 17, 5, 12, 9, 19, 10, 4, 16, 3, 8, 11, 15, 1, 14, 13, 18, 0, 7],
    [9, 2, 12, 11, 6, 1, 5, 19, 18, 3, 7, 13, 4, 14, 17, 10, 16, 8, 0, 15],
    [4, 1, 7, 10, 14, 11, 17, 19, 5, 0, 3, 2, 8, 9, 6, 16, 15, 18, 12, 13],
    [8, 9, 16, 7, 1, 18, 11, 6, 3, 15, 13, 0, 5, 2, 4, 14, 17, 12, 10, 19],
    [12, 4, 1, 14, 3, 6, 18, 5, 0, 15, 13, 8, 19, 7, 17, 9, 2, 16, 11, 10],
    [15, 12, 0, 11, 18, 19, 8, 14, 1, 2, 3, 4, 9, 7, 13, 6, 10, 5, 17, 16],
    [0, 3, 11, 6, 5, 13, 4, 8, 9, 15, 19, 10, 12, 17, 2, 16, 7, 14, 1, 18],
    [9, 10, 12, 15, 13, 7, 2, 6, 11, 3, 0, 19, 8, 18, 1, 16, 5, 4, 17, 14],
    [8, 10, 2, 17, 19, 5, 1, 18, 7, 15, 9, 12, 13, 14, 3, 11, 6, 16, 0, 4],
    [11, 8, 15, 19, 0, 9, 14, 12, 13, 16, 7, 5, 10, 18, 1, 3, 17, 2, 6, 4],
    [9, 2, 10, 15, 19, 13, 16, 12, 14, 18, 11, 8, 0, 7, 4, 1, 17, 5, 3, 6],
    [18, 3, 11, 15, 14, 16, 0, 9, 19, 10, 1, 8, 5, 7, 4, 12, 2, 6, 13, 17],
    [1, 17, 2, 8, 5, 16, 18, 13, 11, 0, 3, 19, 4, 9, 14, 15, 12, 6, 10, 7],
    [3, 2, 14, 5, 18, 15, 11, 13, 8, 9, 16, 4, 12, 7, 0, 6, 10, 19, 17, 1]]

/-- Case 3, `n = 5`: the witness table `tab5` passes the checker. -/
theorem checkTab_5 : checkTab 5 tab5 = true := by decide

/-- Case 3, `n = 6`: the witness table `tab6` passes the checker. -/
theorem checkTab_6 : checkTab 6 tab6 = true := by decide

/-- Case 3, `n = 7`: the witness table `tab7` passes the checker. -/
theorem checkTab_7 : checkTab 7 tab7 = true := by decide

/-- Case 3, `n = 8`: the witness table `tab8` passes the checker. -/
theorem checkTab_8 : checkTab 8 tab8 = true := by decide

/-- Case 3, `n = 9`: the witness table `tab9` passes the checker. -/
theorem checkTab_9 : checkTab 9 tab9 = true := by decide

/-- Case 3, `n = 10`: the witness table `tab10` passes the checker. -/
theorem checkTab_10 : checkTab 10 tab10 = true := by decide

/-- Case 3, `n = 11`: the witness table `tab11` passes the checker. -/
theorem checkTab_11 : checkTab 11 tab11 = true := by decide

/-- Case 3, `n = 12`: the witness table `tab12` passes the checker. -/
theorem checkTab_12 : checkTab 12 tab12 = true := by decide

/-- Case 3, `n = 13`: the witness table `tab13` passes the checker. -/
theorem checkTab_13 : checkTab 13 tab13 = true := by decide

/-- Case 3, `n = 14`: the witness table `tab14` passes the checker. -/
theorem checkTab_14 : checkTab 14 tab14 = true := by decide

/-- Case 3, `n = 15`: the witness table `tab15` passes the checker. -/
theorem checkTab_15 : checkTab 15 tab15 = true := by decide

/-- Case 3, `n = 16`: the witness table `tab16` passes the checker. -/
theorem checkTab_16 : checkTab 16 tab16 = true := by decide

/-- Case 3, `n = 17`: the witness table `tab17` passes the checker. -/
theorem checkTab_17 : checkTab 17 tab17 = true := by decide

/-- Case 3, `n = 18`: the witness table `tab18` passes the checker. -/
theorem checkTab_18 : checkTab 18 tab18 = true := by decide

/-- Case 3, `n = 19`: the witness table `tab19` passes the checker. -/
theorem checkTab_19 : checkTab 19 tab19 = true := by decide

/-- Case 3, `n = 20`: the witness table `tab20` passes the checker. -/
theorem checkTab_20 : checkTab 20 tab20 = true := by decide

/-- Case 3 of the paper: for `5 ≤ n ≤ 20`, `F` hits every residue modulo `2n+1`. -/
theorem surj_of_small (n : ℕ) (hn₁ : 5 ≤ n) (hn₂ : n ≤ 20) :
    Function.Surjective fun τ : Equiv.Perm (Fin n) => (sunF τ : ZMod (2 * n + 1)) := by
  interval_cases n
  · exact surj_of_checkTab 5 tab5 checkTab_5
  · exact surj_of_checkTab 6 tab6 checkTab_6
  · exact surj_of_checkTab 7 tab7 checkTab_7
  · exact surj_of_checkTab 8 tab8 checkTab_8
  · exact surj_of_checkTab 9 tab9 checkTab_9
  · exact surj_of_checkTab 10 tab10 checkTab_10
  · exact surj_of_checkTab 11 tab11 checkTab_11
  · exact surj_of_checkTab 12 tab12 checkTab_12
  · exact surj_of_checkTab 13 tab13 checkTab_13
  · exact surj_of_checkTab 14 tab14 checkTab_14
  · exact surj_of_checkTab 15 tab15 checkTab_15
  · exact surj_of_checkTab 16 tab16 checkTab_16
  · exact surj_of_checkTab 17 tab17 checkTab_17
  · exact surj_of_checkTab 18 tab18 checkTab_18
  · exact surj_of_checkTab 19 tab19 checkTab_19
  · exact surj_of_checkTab 20 tab20 checkTab_20

/-! ## Main theorem -/

/-- **Theorem 1.1 (She–Luo, arXiv:2606.18311; Sun's Conjecture 11.8).** For every
integer `n > 4`, the values `F(τ) = ∑_{k=1}^n k² τ(k)²`, `τ ∈ S_n`, contain a complete
residue system modulo `2n+1`: the map `τ ↦ F(τ) mod (2n+1)` is surjective. -/
theorem sun_conjecture_11_8 (n : ℕ) (hn : 4 < n) :
    Function.Surjective fun τ : Equiv.Perm (Fin n) => (sunF τ : ZMod (2 * n + 1)) := by
  rcases Nat.lt_or_ge n 21 with hsmall | hlarge
  · exact surj_of_small n hn (by omega)
  · exact surj_of_large n hlarge

/-- Alias of `sun_conjecture_11_8` under the paper's numbering (Theorem 1.1). -/
theorem theorem_1_1 (n : ℕ) (hn : 4 < n) :
    Function.Surjective fun τ : Equiv.Perm (Fin n) => (sunF τ : ZMod (2 * n + 1)) :=
  sun_conjecture_11_8 n hn

end SunPermutationSquareSumMod
