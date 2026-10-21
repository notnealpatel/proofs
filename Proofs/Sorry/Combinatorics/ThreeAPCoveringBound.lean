/-
# Explicit counting bounds for 3-AP covering sets and Stanley sequences

## Source

arXiv:2609.02041, Pitchayut Saengrungkongka, *Sparse k-AP Covering Sets and the Arithmetic
Kakeya Conjecture*, Section 1 (Introduction): the Definition of `k`-AP covering sets, the
Proposition citing Kiss–Sándor–Yang [p. 2], and the following remark on `S_3(A_0)` with the
Gerver–Ramsey and Moy references.  Context: Erdős Problem #271 (growth of Stanley sequences).

Verbatim (Section 1):

> A subset `A ⊆ ℕ_0` is `k`-AP covering if there exists `n_0` such that for all `x > n_0`,
> there exists `d ∈ ℕ_0` such that `x-d, x-2d, …, x-(k-1)d` are all in `A`.

> **Proposition** ([Kiss–Sándor–Yang, p. 2]). For any 3-AP covering set `A ⊆ ℕ_0` and
> `ε > 0`, we have `|A ∩ {0,1,…,n}| > (√2 - ε)√n` for all sufficiently large integers `n`.
> In particular, this proposition implies that the `n`-th term of the sequence `S_3(A_0)` is
> at most `(1/2 + o(1)) n^2`. This counting argument, in the specific setting of `S_3(A_0)`,
> appears in papers of Gerver and Ramsey and Moy.

Formalized target (triage a2-18): the explicit Moy / Gerver–Ramsey bound for the Stanley
sequence `S(0, n)` (`a_0 = 0`, `a_1 = n`, `a_{k+1}` the least `m > a_k` with
`{a_0, …, a_k, m}` 3-AP-free): `a_k ≤ (k - 1)(k + 2)/2 + n` for every `k ≥ 1`;
together with the explicit 3-AP covering count `2(n - n_0) ≤ m(m + 1)`,
`m = |A ∩ [0, n]|`, and the Kiss–Sándor–Yang Proposition derived from it.

Date: 2026-10-21.  Status: known; proved in the literature (Gerver–Ramsey, Moy,
Kiss–Sándor–Yang) and quoted, not proved, in arXiv:2609.02041.
-/
import Mathlib

set_option autoImplicit false

namespace ThreeAPCoveringBound

/-! ### Definitions -/

/-- `AvoidsAP L m` says that adjoining `m` to the finite list of naturals `L` creates no
relation `c + m = 2 * b` with `b, c ∈ L`; when `m` exceeds every element of `L` this is
exactly the statement that `m` is not the top of a nonconstant 3-AP `c < b < m` of `L ∪ {m}`. -/
def AvoidsAP (L : List ℕ) (m : ℕ) : Prop := ∀ b ∈ L, ∀ c ∈ L, c + m ≠ 2 * b

instance (L : List ℕ) : DecidablePred (AvoidsAP L) := fun m => by
  unfold AvoidsAP; infer_instance

/-- There is always some `m > M` avoiding all relations with `L`. -/
theorem exists_avoidsAP (L : List ℕ) (M : ℕ) : ∃ m, M < m ∧ AvoidsAP L m := by
  refine ⟨M + 2 * L.sum + 1, by omega, fun b hb c _ => ?_⟩
  have hbsum := List.le_sum_of_mem hb
  omega

/-- The greedy step: the least `m > M` with `AvoidsAP L m`. -/
def stanleyStep (L : List ℕ) (M : ℕ) : ℕ := Nat.find (exists_avoidsAP L M)

/-- `stanleyList n k` is the list `[a_k, …, a_1, a_0]` of the first `k + 1` terms of the
Stanley sequence `S(0, n)`: `a_0 = 0`, `a_1 = n`, and `a_{k+1}` is the least `m > a_k` such
that `{a_0, …, a_k, m}` contains no nonconstant 3-term arithmetic progression. -/
def stanleyList (n : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | 1 => [n, 0]
  | k + 2 =>
    stanleyStep (stanleyList n (k + 1)) ((stanleyList n (k + 1)).headD 0) :: stanleyList n (k + 1)

/-- The `k`-th term `a_k` of the Stanley sequence `S(0, n)` (indexed from `a_0 = 0`). -/
def stanley (n k : ℕ) : ℕ := (stanleyList n k).headD 0

/-- The paper's Definition for `k = 3`: `A ⊆ ℕ_0` is 3-AP covering if there is `n_0` such
that every `x > n_0` has some `d ∈ ℕ_0` with `x - d, x - 2d ∈ A` (the guard `2d ≤ x` records
that `x - 2d` is a nonnegative integer, so the truncated subtraction is exact). -/
def IsThreeAPCovering (A : Set ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ x, n₀ < x → ∃ d : ℕ, 2 * d ≤ x ∧ x - d ∈ A ∧ x - 2 * d ∈ A

/-! ### Ground truth (OEIS A005836 for `n = 1`; direct greedy computation otherwise) -/

example : (List.range 12).map (stanley 1) = [0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31] := by
  decide +kernel
example : (List.range 12).map (stanley 2) = [0, 2, 3, 5, 9, 11, 12, 14, 27, 29, 30, 32] := by
  decide +kernel
example : (List.range 12).map (stanley 4) = [0, 4, 5, 7, 11, 12, 16, 23, 26, 31, 33, 37] := by
  decide +kernel

/-- Ground truth for `IsThreeAPCovering`: `ℕ_0` itself is 3-AP covering (take `d = 0`). -/
example : IsThreeAPCovering Set.univ := ⟨0, fun _ _ => ⟨0, by simp⟩⟩

/-- Ground truth for `IsThreeAPCovering`: `∅` is not 3-AP covering. -/
example : ¬ IsThreeAPCovering ∅ := by
  rintro ⟨n₀, h⟩
  obtain ⟨d, -, hd, -⟩ := h (n₀ + 1) (by omega)
  exact hd

/-! ### Basic API -/

theorem stanley_zero (n : ℕ) : stanley n 0 = 0 := rfl

theorem stanley_one (n : ℕ) : stanley n 1 = n := rfl

theorem stanleyList_succ (n k : ℕ) :
    stanleyList n (k + 1) = stanley n (k + 1) :: stanleyList n k := by
  cases k with
  | zero => rfl
  | succ k => rfl

theorem stanley_add_two (n k : ℕ) :
    stanley n (k + 2) = stanleyStep (stanleyList n (k + 1)) (stanley n (k + 1)) := rfl

theorem mem_stanleyList {n k x : ℕ} : x ∈ stanleyList n k ↔ ∃ i ≤ k, stanley n i = x := by
  induction k with
  | zero =>
    simp only [stanleyList, List.mem_singleton, Nat.le_zero, exists_eq_left, stanley_zero]
    exact eq_comm
  | succ k ih =>
    rw [stanleyList_succ, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact ⟨k + 1, le_rfl, h.symm⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact Or.inr ⟨i, by omega, rfl⟩
      · left; rw [show i = k + 1 by omega]

/-- Consecutive terms increase: `a_k < a_{k+1}` (for `k = 0` this is `0 < n`). -/
theorem stanley_lt_succ {n : ℕ} (hn : 0 < n) (k : ℕ) : stanley n k < stanley n (k + 1) := by
  cases k with
  | zero => exact hn
  | succ k =>
    rw [stanley_add_two]
    exact (Nat.find_spec (exists_avoidsAP _ _)).1

/-- The Stanley sequence `S(0, n)` is strictly increasing. -/
theorem stanley_strictMono {n : ℕ} (hn : 0 < n) : StrictMono (stanley n) :=
  strictMono_nat_of_lt_succ (stanley_lt_succ hn)

/-- The new term `a_{k+2}` creates no relation `c + a_{k+2} = 2 b` with earlier terms. -/
theorem avoidsAP_stanley (n k : ℕ) : AvoidsAP (stanleyList n (k + 1)) (stanley n (k + 2)) := by
  rw [stanley_add_two]
  exact (Nat.find_spec (exists_avoidsAP _ _)).2

/-- Greedy minimality: every `y` strictly between `a_t` and `a_{t+1}` (with `1 ≤ t`) is
blocked, i.e. `y = 2 a_j - a_i` for some `i < j ≤ t`. -/
theorem stanley_blocked {n : ℕ} (hn : 0 < n) (t : ℕ) (ht : 1 ≤ t) (y : ℕ)
    (h1 : stanley n t < y) (h2 : y < stanley n (t + 1)) :
    ∃ j ≤ t, ∃ i < j, y + stanley n i = 2 * stanley n j := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hnot : ¬ AvoidsAP (stanleyList n (k + 1)) y := by
    intro hav
    rw [stanley_add_two] at h2
    exact Nat.find_min (exists_avoidsAP _ _) h2 ⟨h1, hav⟩
  simp only [AvoidsAP, not_forall, not_not, exists_prop] at hnot
  obtain ⟨b, hb, c, hc, hcb⟩ := hnot
  obtain ⟨j, hj, rfl⟩ := mem_stanleyList.1 hb
  obtain ⟨i, hi, rfl⟩ := mem_stanleyList.1 hc
  have hmono := stanley_strictMono hn
  have hjy : stanley n j < y := lt_of_le_of_lt (hmono.monotone hj) h1
  have hij : stanley n i < stanley n j := by omega
  exact ⟨j, hj, i, hmono.lt_iff_lt.1 hij, by omega⟩

/-! ### The counting argument for greedy sequences -/

/-- Every `y` with `a_1 < y < a_k` is either a term `a_t` with `1 < t < k`, or is blocked:
`y + a_i = 2 a_j` with `i < j < k`. -/
theorem term_or_blocked (a : ℕ → ℕ) (ha : StrictMono a)
    (hblock : ∀ t, 1 ≤ t → ∀ y, a t < y → y < a (t + 1) → ∃ j ≤ t, ∃ i < j, y + a i = 2 * a j)
    (k y : ℕ) (hy1 : a 1 < y) (hyk : y < a k) :
    (∃ t, 1 < t ∧ t < k ∧ a t = y) ∨ ∃ j < k, ∃ i < j, y + a i = 2 * a j := by
  have hk1 : 1 ≤ k := by
    by_contra h0
    obtain rfl : k = 0 := by omega
    have h01 : a 0 < a 1 := ha Nat.zero_lt_one
    omega
  have hex : ∃ t, y < a (t + 1) := ⟨k - 1, by rw [Nat.sub_add_cancel hk1]; exact hyk⟩
  have hyt : y < a (Nat.find hex + 1) := Nat.find_spec hex
  have ht1 : 1 ≤ Nat.find hex := by
    by_contra h0
    have h00 : Nat.find hex = 0 := by omega
    rw [h00, zero_add] at hyt
    omega
  have hat : a (Nat.find hex) ≤ y := by
    have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel ht1] at hmin
    omega
  have htk : Nat.find hex + 1 ≤ k := by
    by_contra h
    have hmin := Nat.find_min hex (show k - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel hk1] at hmin
    exact hmin hyk
  rcases hat.lt_or_eq with hlt | heq
  · obtain ⟨j, hj, i, hi, hyij⟩ := hblock _ ht1 y hlt hyt
    exact Or.inr ⟨j, by omega, i, hi, hyij⟩
  · refine Or.inl ⟨Nat.find hex, ?_, by omega, heq⟩
    by_contra h1
    have hf1 : Nat.find hex = 1 := by omega
    rw [hf1] at heq
    omega

/-- Abstract Gerver–Ramsey / Moy counting: if `a` is strictly increasing and every integer
strictly between consecutive terms `a_t < y < a_{t+1}` (`t ≥ 1`) has the form `2 a_j - a_i`
with `i < j ≤ t`, then `a_k ≤ a_1 + (k - 1)(k + 2)/2` for `k ≥ 1`. -/
theorem two_mul_le_of_blocked (a : ℕ → ℕ) (ha : StrictMono a)
    (hblock : ∀ t, 1 ≤ t → ∀ y, a t < y → y < a (t + 1) → ∃ j ≤ t, ∃ i < j, y + a i = 2 * a j)
    (k : ℕ) (hk : 1 ≤ k) : 2 * a k ≤ (k - 1) * (k + 2) + 2 * a 1 := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    simp
  have hsub : Finset.Ioo (a 1) (a k) ⊆ (Finset.Ioo 1 k).image a ∪
      ((Finset.range k).sigma Finset.range).image (fun p => 2 * a p.1 - a p.2) := by
    intro y hy
    rw [Finset.mem_Ioo] at hy
    rcases term_or_blocked a ha hblock k y hy.1 hy.2 with ⟨t, ht1, htk, hty⟩ | ⟨j, hj, i, hi, hyij⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨t, Finset.mem_Ioo.2 ⟨ht1, htk⟩, hty⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨j, i⟩, ?_, ?_⟩)
      · simp only [Finset.mem_sigma, Finset.mem_range]
        omega
      · show 2 * a j - a i = y
        omega
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le ((Finset.Ioo 1 k).image a)
    (((Finset.range k).sigma Finset.range).image (fun p => 2 * a p.1 - a p.2))
  have himg1 := Finset.card_image_le (s := Finset.Ioo 1 k) (f := a)
  have himg2 := Finset.card_image_le (s := (Finset.range k).sigma Finset.range)
    (f := fun p => 2 * a p.1 - a p.2)
  have hsig : ((Finset.range k).sigma Finset.range).card * 2 = k * (k - 1) := by
    rw [Finset.card_sigma]
    simp only [Finset.card_range]
    exact Finset.sum_range_id_mul_two k
  have hprod : (k - 1) * (k + 2) = k * (k - 1) + 2 * (k - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have h1k : a 1 < a k := ha (by omega)
  rw [Nat.card_Ioo] at hcard
  rw [Nat.card_Ioo] at himg1
  rw [hprod]
  generalize k * (k - 1) = P at *
  omega

/-- **Moy / Gerver–Ramsey bound** for the Stanley sequence `S(0, n)`: for `n ≥ 1` and `k ≥ 1`,
`a_k ≤ (k - 1)(k + 2)/2 + n`, stated without division as `2 a_k ≤ (k - 1)(k + 2) + 2 n`. -/
theorem two_mul_stanley_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : 1 ≤ k) :
    2 * stanley n k ≤ (k - 1) * (k + 2) + 2 * n := by
  have h := two_mul_le_of_blocked (stanley n) (stanley_strictMono hn)
    (fun t ht y h1 h2 => stanley_blocked hn t ht y h1 h2) k hk
  rwa [stanley_one] at h

/-- Sharpness at the boundary `n = 1`, `k = 2`: `a_2 = 3` and `2 · 3 = 1 · 4 + 2 · 1`. -/
example : 2 * stanley 1 2 = (2 - 1) * (2 + 2) + 2 * 1 := by decide +kernel

/-! ### Faithfulness: the greedy rule in terms of Mathlib's `ThreeAPFree` -/

/-- The set `{a_0, …, a_k}` of the first `k + 1` terms is the underlying set of `stanleyList`. -/
theorem mem_image_Iic_iff {n k x : ℕ} :
    x ∈ stanley n '' Set.Iic k ↔ x ∈ stanleyList n k := by
  rw [mem_stanleyList]
  simp only [Set.mem_image, Set.mem_Iic]

/-- Adding the next term inserts it into the prefix set. -/
theorem image_Iic_succ (n k : ℕ) :
    stanley n '' Set.Iic (k + 1) = insert (stanley n (k + 1)) (stanley n '' Set.Iic k) := by
  ext x
  rw [Set.mem_insert_iff, mem_image_Iic_iff, mem_image_Iic_iff, stanleyList_succ, List.mem_cons]

/-- Every prefix `{a_0, …, a_k}` of the Stanley sequence `S(0, n)` is 3-AP-free. -/
theorem threeAPFree_stanley {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ThreeAPFree (stanley n '' Set.Iic k) := by
  have hmono := stanley_strictMono hn
  induction k with
  | zero =>
    rw [show Set.Iic (0 : ℕ) = {0} by ext; simp, Set.image_singleton]
    exact threeAPFree_singleton _
  | succ k ih =>
    rw [image_Iic_succ]
    have hlt : ∀ i ∈ stanley n '' Set.Iic k, i < stanley n (k + 1) := by
      rintro _ ⟨i, hi, rfl⟩
      exact hmono (Nat.lt_succ_of_le hi)
    refine (threeAPFree_insert_of_lt hlt).2 ⟨ih, fun b hb c hc hbc => ?_⟩
    exfalso
    cases k with
    | zero =>
      obtain ⟨i, hi, rfl⟩ := hb
      obtain ⟨j, hj, rfl⟩ := hc
      rw [Set.mem_Iic, Nat.le_zero] at hi hj
      subst hi hj
      rw [stanley_one, stanley_zero] at hbc
      omega
    | succ k =>
      rw [mem_image_Iic_iff] at hb hc
      have hk2 : stanley n (k + 1 + 1) = stanley n (k + 2) := rfl
      exact avoidsAP_stanley n k b hb c hc (by omega)

/-- The greedy rule, verbatim: for `k ≥ 1`, `a_{k+1}` is the least `m > a_k` such that
`{a_0, …, a_k, m}` contains no nonconstant 3-term arithmetic progression (Mathlib's
`ThreeAPFree`). Stated with `k + 1` in place of `k`. -/
theorem stanley_isLeast {n : ℕ} (hn : 0 < n) (k : ℕ) :
    IsLeast {m | stanley n (k + 1) < m ∧ ThreeAPFree (insert m (stanley n '' Set.Iic (k + 1)))}
      (stanley n (k + 2)) := by
  have hmono := stanley_strictMono hn
  refine ⟨⟨hmono (by omega), ?_⟩, ?_⟩
  · rw [← image_Iic_succ]
    exact threeAPFree_stanley hn (k + 2)
  · rintro m ⟨hm, hfree⟩
    by_contra hle
    have hlt := not_le.1 hle
    rw [stanley_add_two] at hlt
    refine Nat.find_min (exists_avoidsAP _ _) hlt ⟨hm, fun b hb c hc hbc => ?_⟩
    have hlt' : ∀ i ∈ stanley n '' Set.Iic (k + 1), i < m := by
      rintro _ ⟨i, hi, rfl⟩
      exact lt_of_le_of_lt (hmono.monotone hi) hm
    rw [← mem_image_Iic_iff] at hb hc
    have hmb := (threeAPFree_insert_of_lt hlt').1 hfree |>.2 hb hc (by omega)
    have hblt := hlt' b hb
    omega

/-! ### 3-AP covering sets -/

/-- The paper's remark that a Stanley sequence is 3-AP covering, for `S(0, n)`: every
`x > a_1 = n` is a term (`d = 0`) or equals `2 a_j - a_i` (`d = a_j - a_i`). -/
theorem isThreeAPCovering_range_stanley {n : ℕ} (hn : 0 < n) :
    IsThreeAPCovering (Set.range (stanley n)) := by
  have hmono := stanley_strictMono hn
  refine ⟨stanley n 1, fun x hx => ?_⟩
  have hxk : x < stanley n (x + 1) := lt_of_lt_of_le (Nat.lt_succ_self x) (hmono.id_le (x + 1))
  rcases term_or_blocked (stanley n) hmono (fun t ht y h1 h2 => stanley_blocked hn t ht y h1 h2)
      (x + 1) x hx hxk with ⟨t, -, -, hxt⟩ | ⟨j, -, i, hij, hx2⟩
  · exact ⟨0, by omega, by simpa using ⟨t, hxt⟩, by simpa using ⟨t, hxt⟩⟩
  · have hlt : stanley n i < stanley n j := hmono hij
    refine ⟨stanley n j - stanley n i, by omega, ⟨j, by omega⟩, ⟨i, by omega⟩⟩

/-- **Explicit Kiss–Sándor–Yang count.** If every `x > n₀` has `d` with `2d ≤ x` and
`x - d, x - 2d ∈ A`, then for every `n`, with `m = |A ∩ [0, n]|`,
`2 n ≤ 2 n₀ + m (m + 1)`, i.e. `n - n₀ ≤ m(m + 1)/2`. -/
theorem two_mul_le_ncard_mul (A : Set ℕ) (n₀ : ℕ)
    (hA : ∀ x, n₀ < x → ∃ d : ℕ, 2 * d ≤ x ∧ x - d ∈ A ∧ x - 2 * d ∈ A) (n : ℕ) :
    2 * n ≤ 2 * n₀ + (A ∩ Set.Iic n).ncard * ((A ∩ Set.Iic n).ncard + 1) := by
  classical
  set B : Finset ℕ := (Finset.range (n + 1)).filter (· ∈ A) with hBdef
  have hBset : (B : Set ℕ) = A ∩ Set.Iic n := by
    ext x
    simp only [hBdef, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_Iic]
    rw [Nat.lt_add_one_iff, and_comm]
  have hm : (A ∩ Set.Iic n).ncard = B.card := by rw [← hBset, Set.ncard_coe_finset]
  set P := (B ×ˢ B).filter (fun p => p.2 ≤ p.1) with hPdef
  set Q := (B ×ˢ B).filter (fun p => p.1 ≤ p.2) with hQdef
  have hsub : Finset.Ioc n₀ n ⊆ P.image (fun p => 2 * p.1 - p.2) := by
    intro x hx
    rw [Finset.mem_Ioc] at hx
    obtain ⟨d, hd, hxd, hx2d⟩ := hA x hx.1
    refine Finset.mem_image.2 ⟨(x - d, x - 2 * d), ?_, ?_⟩
    · simp only [hPdef, hBdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨⟨by omega, hxd⟩, ⟨by omega, hx2d⟩⟩, by omega⟩
    · show 2 * (x - d) - (x - 2 * d) = x
      omega
  have hPQ : P.card = Q.card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    · intro p hp
      simp only [hPdef, hQdef, Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p hp
      simp only [hPdef, hQdef, Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  have hunion : P ∪ Q = B ×ˢ B := by
    ext p
    simp only [hPdef, hQdef, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total p.2 p.1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hinter : P ∩ Q = B.diag := by
    ext p
    simp only [hPdef, hQdef, Finset.mem_inter, Finset.mem_filter, Finset.mem_diag,
      Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, -⟩, h2⟩, -, h3⟩
      exact ⟨h1, le_antisymm h3 h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨⟨h1, h2 ▸ h1⟩, h2.ge⟩, ⟨h1, h2 ▸ h1⟩, h2.le⟩
  have hcount := Finset.card_union_add_card_inter P Q
  rw [hunion, hinter, Finset.card_product, Finset.diag_card] at hcount
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Nat.card_Ioc] at hcard
  rw [hm, Nat.mul_add, Nat.mul_one]
  generalize B.card * B.card = S at *
  omega

/-- **Proposition** ([Kiss–Sándor–Yang, p. 2], as quoted in arXiv:2609.02041, Section 1).
For any 3-AP covering set `A ⊆ ℕ_0` and `ε > 0`, `|A ∩ {0, 1, …, n}| > (√2 - ε)√n` for all
sufficiently large integers `n`. -/
theorem ksy_proposition (A : Set ℕ) (hA : IsThreeAPCovering A) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (√2 - ε) * √(n : ℝ) < ((A ∩ Set.Iic n).ncard : ℝ) := by
  obtain ⟨n₀, h⟩ := hA
  rcases le_or_gt (√2 - ε) 0 with hc | hc
  · filter_upwards [Filter.eventually_gt_atTop n₀] with n hn
    have key := two_mul_le_ncard_mul A n₀ h n
    have hm : 0 < (A ∩ Set.Iic n).ncard := by
      rcases Nat.eq_zero_or_pos (A ∩ Set.Iic n).ncard with h0 | h0
      · rw [h0] at key
        omega
      · exact h0
    calc (√2 - ε) * √(n : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg _)
      _ < ((A ∩ Set.Iic n).ncard : ℝ) := by exact_mod_cast hm
  · set c := √2 - ε with hcdef
    have hc2 : c ^ 2 < 2 := by
      have hlt : c < √2 := by rw [hcdef]; linarith
      calc c ^ 2 < √2 ^ 2 := pow_lt_pow_left₀ hlt hc.le two_ne_zero
        _ = 2 := Real.sq_sqrt (by norm_num)
    have hgap : 0 < 2 - c ^ 2 := by linarith
    set S0 : ℝ := (2 * n₀ + c) / (2 - c ^ 2) + 1 with hS0def
    have hS0 : 1 ≤ S0 := by
      have : 0 ≤ (2 * (n₀ : ℝ) + c) / (2 - c ^ 2) := by positivity
      linarith
    have hS0mul : (2 - c ^ 2) * S0 = 2 * n₀ + c + (2 - c ^ 2) := by
      rw [hS0def, mul_add, mul_div_cancel₀ _ hgap.ne', mul_one]
    filter_upwards [Filter.eventually_ge_atTop ⌈S0 ^ 2⌉₊] with n hn
    by_contra hcon
    have hmle := not_lt.1 hcon
    set m := (A ∩ Set.Iic n).ncard with hmdef
    have key : (2 * n : ℝ) ≤ 2 * n₀ + m * (m + 1) := by
      exact_mod_cast two_mul_le_ncard_mul A n₀ h n
    set s := √(n : ℝ) with hsdef
    have hs2 : s ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hS0s : S0 ≤ s := by
      rw [hsdef, Real.le_sqrt' (by linarith)]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hs1 : 1 ≤ s := hS0.trans hS0s
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hmm : (m : ℝ) * (m + 1) ≤ (c * s) * (c * s + 1) := by
      have hcs : 0 ≤ c * s := by positivity
      exact mul_le_mul hmle (by linarith) (by linarith) hcs
    have hupper : (2 - c ^ 2) * s ^ 2 ≤ 2 * n₀ + c * s := by nlinarith
    have hlower : (2 * n₀ + c + (2 - c ^ 2)) * s ≤ (2 - c ^ 2) * s ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hS0s (mul_nonneg hgap.le (by linarith : (0 : ℝ) ≤ s))
      rw [← hS0mul]
      calc (2 - c ^ 2) * S0 * s = (2 - c ^ 2) * s * S0 := by ring
        _ ≤ (2 - c ^ 2) * s * s := h1
        _ = (2 - c ^ 2) * s ^ 2 := by ring
    have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
    nlinarith

/-- Non-vacuity: the hypotheses of `ksy_proposition` hold jointly for the Stanley sequence
`S(0, 1)` (OEIS A005836) and `ε = 1`. -/
example : ∀ᶠ n : ℕ in Filter.atTop,
    (√2 - 1) * √(n : ℝ) < ((Set.range (stanley 1) ∩ Set.Iic n).ncard : ℝ) :=
  ksy_proposition _ (isThreeAPCovering_range_stanley Nat.one_pos) 1 one_pos

/-- Non-vacuity: the hypothesis of `two_mul_le_ncard_mul` holds for `A = ℕ_0`, `n₀ = 0`. -/
example (n : ℕ) : 2 * n ≤ 2 * 0 +
    ((Set.univ : Set ℕ) ∩ Set.Iic n).ncard * (((Set.univ : Set ℕ) ∩ Set.Iic n).ncard + 1) :=
  two_mul_le_ncard_mul Set.univ 0 (fun _ _ => ⟨0, by simp⟩) n

end ThreeAPCoveringBound
