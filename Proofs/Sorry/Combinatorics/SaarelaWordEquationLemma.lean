/-
# Saarela's Lemma 8: the counting lemma behind the Holub prize problem

## Source

* MathOverflow answer https://mathoverflow.net/a/119225 (question on open problems
  with prizes; answer id 119225) records Štěpán Holub's EUR 200 prize problem:
  if `x₀^k = x₁^k ⋯ xₙ^k` holds for three distinct positive `k` (Hakala–Kortelainen
  1997 for `k ∈ {1,2,3}`, Plandowski), must the `xᵢ` pairwise commute?
* Solved by Aleksi Saarela, "Word equations where a power equals a product of
  powers", STACS 2017, LIPIcs 66:55,
  https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2017.55
  (no arXiv id is involved for this target).
* Stated by: A. Saarela (Lemmas 7 and 8 of the paper above).
* Date of this card: 2026-10-21.
* Status: proved in the literature (Saarela 2017, peer reviewed). This module
  proves the integer-letter specializations of Lemmas 7 and 8 in Lean.

## Verbatim informal claims (Saarela 2017, Section 5)

> Lemma 7. Let x ∈ Γ*, s ∈ R, and Σ(x) ≠ 0 or s ≠ 0. Let k1, k2, k3 ∈ Z+ and
> k1 < k2 < k3. Let w_k = psw_{ks}(x^k). Let a ≥ max(w_{k1} w_{k2} w_{k3}).
> Then |w_{k1}|_a ≥ |w_{k2}|_a.

> Lemma 8. Let x0 be a zero-sum word, and let x1, ..., xn be words not all of
> which have zero sum. There are at most two positive integers k such that
> psw(x0^k) and psw(x1^k ⋯ xn^k) are abelian equivalent.

Here `psw_r(a₁ ⋯ aₘ) = b₁ ⋯ bₘ` with `bᵢ = r + a₁ + ⋯ + aᵢ`, `psw = psw_0`, and two
words are abelian equivalent iff every letter occurs equally often in both, i.e.
iff they are permutations of each other (`List.Perm`).

## Formalization notes

* The paper takes `Γ ⊆ ℝ`; the results below are the integer-letter
  specializations (`List ℤ`) needed downstream. Saarela's Lemma 3 only produces
  an alphabet isomorphism making a chosen word zero-sum; it does not rename
  real letters to integers. This module does not formalize a reduction of the
  full real-letter setting to the integer-letter setting.
* `x₁, …, xₙ` is a `List (List ℤ)`; `n = 0` is excluded by the hypothesis that
  some `xᵢ` has nonzero sum.
* `lemma8` is the three-exponent form; `lemma8_encard_le_two` is the paper's
  "at most two" form via `Set.encard` (which is `⊤` on infinite sets, so it
  also rules out infinitely many `k`). `abelK_example` shows the bound is sharp.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.SaarelaWordEquationLemma

/-- Prefix-sum word with offset: `psw r (a₁ ⋯ aₘ) = (r + a₁) (r + a₁ + a₂) ⋯`. -/
def psw : ℤ → List ℤ → List ℤ
  | _, [] => []
  | r, a :: w => (r + a) :: psw (r + a) w

/-- The `k`-th power of a word `x`, i.e. `x` concatenated with itself `k` times. -/
def pw (k : ℕ) (x : List ℤ) : List ℤ := (List.replicate k x).flatten

example : psw 0 [2, 2, -3, 1, 1, -3] = [2, 4, 1, 2, 3, 0] := by decide
example : pw 2 [1, -1] = [1, -1, 1, -1] := by decide

/-- `psw` of a concatenation. -/
theorem psw_append (r : ℤ) (u v : List ℤ) :
    psw r (u ++ v) = psw r u ++ psw (r + u.sum) v := by
  induction u generalizing r with
  | nil => simp [psw]
  | cons a u ih => simp [psw, ih, add_assoc]

/-- Shifting the offset translates every letter. -/
theorem psw_add (r t : ℤ) (w : List ℤ) : psw (r + t) w = (psw r w).map (· + t) := by
  induction w generalizing r with
  | nil => simp [psw]
  | cons a w ih =>
    simp only [psw, List.map_cons]
    rw [show r + t + a = r + a + t by ring, ih]

/-- `x^(k+1) = x · x^k`. -/
theorem pw_succ (k : ℕ) (x : List ℤ) : pw (k + 1) x = x ++ pw k x := by
  simp [pw, List.replicate_succ]

/-- `x^0` is the empty word. -/
theorem pw_zero (x : List ℤ) : pw 0 x = [] := by simp [pw]

/-- `Σ(x^k) = k Σ(x)`. -/
theorem sum_pw (k : ℕ) (x : List ℤ) : (pw k x).sum = k * x.sum := by
  induction k with
  | zero => simp [pw_zero]
  | succ k ih => rw [pw_succ, List.sum_append, ih]; push_cast; ring

/-- Count of a letter in a shifted prefix-sum word. -/
theorem count_psw (a r : ℤ) (w : List ℤ) :
    (psw r w).count a = (psw 0 w).count (a - r) := by
  have h := psw_add 0 r w
  rw [zero_add] at h
  rw [h, show a = (a - r) + r by ring, List.count_map_of_injective _ _ (add_left_injective r)]
  simp

/-- Count formula for prefix sums of a power. -/
theorem count_psw_pw (a r : ℤ) (k : ℕ) (x : List ℤ) :
    (psw r (pw k x)).count a =
      ∑ j ∈ Finset.range k, (psw 0 x).count (a - (r + j * x.sum)) := by
  induction k generalizing r with
  | zero => simp [pw_zero, psw]
  | succ k ih =>
    rw [pw_succ, psw_append, List.count_append, ih, Finset.sum_range_succ', count_psw]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2; ring

/-- Membership in prefix sums of a power. -/
theorem mem_psw_pw {p r : ℤ} {k j : ℕ} {x : List ℤ} (hp : p ∈ psw 0 x) (hj : j < k) :
    p + (r + j * x.sum) ∈ psw r (pw k x) := by
  induction k generalizing r j with
  | zero => omega
  | succ k ih =>
    rw [pw_succ, psw_append, List.mem_append]
    rcases j with _ | j
    · left
      have h := psw_add 0 r x
      rw [zero_add] at h
      rw [h]; simpa using List.mem_map_of_mem (f := (· + r)) hp
    · right
      have := ih (r := r + x.sum) (j := j) (by omega)
      convert this using 2; push_cast; ring


/-- Arithmetic core of Lemma 7, case `Σ(x) < 0`: the maximal shift in the middle
power is already attained by the first block of the first power. -/
theorem shift_eq_of_neg {K1 K2 K3 J s S : ℤ} (h12 : K1 < K2) (h23 : K2 < K3)
    (hJ0 : 0 ≤ J) (hS : S < 0)
    (b1 : K1 * s ≤ K2 * s + J * S) (b3 : K3 * s ≤ K2 * s + J * S) :
    K1 * s + 0 * S = K2 * s + J * S := by
  have hJS : J * S ≤ 0 := by nlinarith
  have hs1 : 0 ≤ s := by nlinarith
  have hs2 : s ≤ 0 := by nlinarith
  have hs : s = 0 := le_antisymm hs2 hs1
  subst hs
  nlinarith

/-- Arithmetic core of Lemma 7, case `Σ(x) > 0`: the maximal shift in the middle
power is already attained by the last block of the first power. -/
theorem shift_eq_of_pos {K1 K2 K3 J s S : ℤ} (h12 : K1 < K2) (h23 : K2 < K3)
    (hJ : J < K2) (hS : 0 < S)
    (b2 : K1 * s + (K1 - 1) * S ≤ K2 * s + J * S)
    (b4 : K3 * s + (K3 - 1) * S ≤ K2 * s + J * S) :
    K1 * s + (K1 - 1) * S = K2 * s + J * S := by
  have hJS : J * S ≤ (K2 - 1) * S := by nlinarith
  have hs1 : 0 ≤ s + S := by nlinarith
  have hs2 : s + S ≤ 0 := by nlinarith
  have hs : s = -S := by linarith
  subst hs
  nlinarith

/-- **Saarela, Lemma 7.** Let `x` be a word over `ℤ`, `s ∈ ℤ`, with `Σ(x) ≠ 0` or `s ≠ 0`,
and let `0 < k₁ < k₂ < k₃`. Put `w_k = psw_{ks}(x^k)`. If `a` is at least every letter of
`w_{k₁} w_{k₂} w_{k₃}`, then `|w_{k₁}|_a ≥ |w_{k₂}|_a`. -/
theorem lemma7 (x : List ℤ) (s : ℤ) (hns : x.sum ≠ 0 ∨ s ≠ 0) {k1 k2 k3 : ℕ}
    (h0 : 0 < k1) (h12 : k1 < k2) (h23 : k2 < k3) (a : ℤ)
    (ha : ∀ k ∈ [k1, k2, k3], ∀ b ∈ psw (k * s) (pw k x), b ≤ a) :
    (psw (k2 * s) (pw k2 x)).count a ≤ (psw (k1 * s) (pw k1 x)).count a := by
  set S := x.sum with hSdef
  set P := psw 0 x with hPdef
  rw [count_psw_pw, count_psw_pw]
  -- every block whose shift `t` carries an occurrence of `a` has maximal shift
  have hF1 : ∀ k ∈ [k1, k2, k3], ∀ j < k, ∀ t : ℤ, 0 < P.count (a - t) →
      (k : ℤ) * s + j * S ≤ t := by
    intro k hk j hj t ht
    have hmem : a - t ∈ P := List.count_pos_iff.mp ht
    have hin := mem_psw_pw (r := (k : ℤ) * s) hmem hj
    have hle := ha k hk _ hin
    linarith
  by_cases hall : ∀ j ∈ Finset.range k2, P.count (a - (k2 * s + j * S)) = 0
  · rw [Finset.sum_eq_zero hall]; exact Nat.zero_le _
  push Not at hall
  obtain ⟨j, hj, hpos⟩ := hall
  rw [Finset.mem_range] at hj
  have hpos' : 0 < P.count (a - (k2 * s + j * S)) := Nat.pos_of_ne_zero hpos
  have hk1 : k1 ∈ [k1, k2, k3] := by simp
  have hk2 : k2 ∈ [k1, k2, k3] := by simp
  have hk3 : k3 ∈ [k1, k2, k3] := by simp
  have hK12 : (k1 : ℤ) < k2 := by exact_mod_cast h12
  have hK23 : (k2 : ℤ) < k3 := by exact_mod_cast h23
  have hS : S ≠ 0 := by
    intro hS0
    have b1 := hF1 k1 hk1 0 h0 _ hpos'
    have b3 := hF1 k3 hk3 0 (by omega) _ hpos'
    rw [hS0] at b1 b3
    have hs : s = 0 := by nlinarith
    rcases hns with h | h
    · exact h hS0
    · exact h hs
  -- only the block `j` contributes in the middle power
  have hsingle : ∀ j0 ∈ Finset.range k2, j0 ≠ j → P.count (a - (k2 * s + j0 * S)) = 0 := by
    intro j0 hj0 hne
    rw [Finset.mem_range] at hj0
    by_contra hc
    have hc' := Nat.pos_of_ne_zero hc
    have e1 := hF1 k2 hk2 j0 hj0 _ hpos'
    have e2 := hF1 k2 hk2 j hj _ hc'
    have hjS : (j0 : ℤ) * S = j * S := by linarith
    have : (j0 : ℤ) = j := mul_right_cancel₀ hS hjS
    exact hne (by exact_mod_cast this)
  -- the same shift occurs in the first power
  obtain ⟨j', hj', hshift⟩ : ∃ j' < k1, (k1 : ℤ) * s + j' * S = k2 * s + j * S := by
    rcases lt_or_gt_of_ne hS with hneg | hposS
    · refine ⟨0, h0, ?_⟩
      have b1 := hF1 k1 hk1 0 h0 _ hpos'
      have b3 := hF1 k3 hk3 0 (by omega) _ hpos'
      push_cast at b1 b3 ⊢
      exact shift_eq_of_neg hK12 hK23 (by positivity) hneg (by linarith) (by linarith)
    · refine ⟨k1 - 1, by omega, ?_⟩
      have b2 := hF1 k1 hk1 (k1 - 1) (by omega) _ hpos'
      have b4 := hF1 k3 hk3 (k3 - 1) (by omega) _ hpos'
      have hc1 : ((k1 - 1 : ℕ) : ℤ) = k1 - 1 := by omega
      have hc3 : ((k3 - 1 : ℕ) : ℤ) = k3 - 1 := by omega
      rw [hc1] at b2 ⊢
      rw [hc3] at b4
      exact shift_eq_of_pos hK12 hK23 (by exact_mod_cast hj) hposS b2 b4
  calc ∑ j ∈ Finset.range k2, P.count (a - (k2 * s + j * S))
      = P.count (a - (k2 * s + j * S)) :=
        Finset.sum_eq_single j hsingle (fun h => absurd (Finset.mem_range.mpr hj) h)
    _ = P.count (a - (k1 * s + j' * S)) := by rw [hshift]
    _ ≤ ∑ j ∈ Finset.range k1, P.count (a - (k1 * s + j * S)) :=
        Finset.single_le_sum (f := fun j : ℕ => P.count (a - (k1 * s + j * S)))
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj')


/-- Concatenation of the blocks `psw_{k sᵢ}(xᵢ^k)` with `i ∈ I₁`, i.e. those with
`sᵢ ≠ 0` or `Σ(xᵢ) ≠ 0`; the second argument is the running offset `sᵢ`. -/
def blk1 (k : ℕ) : ℤ → List (List ℤ) → List ℤ
  | _, [] => []
  | r, x :: xs => (if r = 0 ∧ x.sum = 0 then [] else psw (k * r) (pw k x)) ++
      blk1 k (r + x.sum) xs

/-- Concatenation of the blocks `psw_{k sᵢ}(xᵢ^k)` with `i ∈ I₀`, i.e. those with
`sᵢ = 0` and `Σ(xᵢ) = 0`; the second argument is the running offset `sᵢ`. -/
def blk0 (k : ℕ) : ℤ → List (List ℤ) → List ℤ
  | _, [] => []
  | r, x :: xs => (if r = 0 ∧ x.sum = 0 then psw (k * r) (pw k x) else []) ++
      blk0 k (r + x.sum) xs

example : blk1 2 0 [[1, -1], [1], [-1]] = [1, 2, 1, 0] := by decide
example : blk0 2 0 [[1, -1], [1], [-1]] = [1, 0, 1, 0] := by decide

/-- Equation (6) of Saarela, at the level of letter counts: the count of `a` in
`psw_{kr}(x₁^k ⋯ xₙ^k)` splits into the `I₁`-blocks and the `I₀`-blocks. -/
theorem count_psw_flatten (a r : ℤ) (k : ℕ) (xs : List (List ℤ)) :
    (psw (k * r) (xs.map (pw k)).flatten).count a =
      (blk1 k r xs).count a + (blk0 k r xs).count a := by
  induction xs generalizing r with
  | nil => simp [psw, blk1, blk0]
  | cons x xs ih =>
    rw [List.map_cons, List.flatten_cons, psw_append, sum_pw,
      show (k : ℤ) * r + k * x.sum = k * (r + x.sum) by ring, List.count_append, ih]
    simp only [blk1, blk0, List.count_append]
    split_ifs <;> simp only [List.count_nil, zero_add] <;> ring

/-- Equation (7) of Saarela at the level of counts: for a zero-sum word,
`|psw(x^k)|_a = k |psw(x)|_a`. -/
theorem count_psw_pw_of_sum_eq_zero (a : ℤ) (k : ℕ) {x : List ℤ} (hx : x.sum = 0) :
    (psw 0 (pw k x)).count a = k * (psw 0 x).count a := by
  rw [count_psw_pw]
  simp [hx]

/-- The `I₀`-blocks scale linearly in `k`. -/
theorem count_blk0 (a r : ℤ) (k : ℕ) (xs : List (List ℤ)) :
    (blk0 k r xs).count a = k * (blk0 1 r xs).count a := by
  induction xs generalizing r with
  | nil => simp [blk0]
  | cons x xs ih =>
    simp only [blk0, List.count_append, ih]
    split_ifs with h
    · rw [h.1, mul_zero, Nat.cast_one, mul_zero, count_psw_pw_of_sum_eq_zero a k h.2,
        count_psw_pw_of_sum_eq_zero a 1 h.2]
      ring
    · simp

/-- Lemma 7 summed over the `I₁`-blocks. -/
theorem count_blk1_le (xs : List (List ℤ)) (r : ℤ) {k1 k2 k3 : ℕ}
    (h0 : 0 < k1) (h12 : k1 < k2) (h23 : k2 < k3) (a : ℤ)
    (ha : ∀ k ∈ [k1, k2, k3], ∀ b ∈ blk1 k r xs, b ≤ a) :
    (blk1 k2 r xs).count a ≤ (blk1 k1 r xs).count a := by
  induction xs generalizing r with
  | nil => simp [blk1]
  | cons x xs ih =>
    simp only [blk1, List.count_append]
    have hrest : ∀ k ∈ [k1, k2, k3], ∀ b ∈ blk1 k (r + x.sum) xs, b ≤ a := by
      intro k hk b hb
      exact ha k hk b (by simp only [blk1]; exact List.mem_append_right _ hb)
    have ih' := ih (r + x.sum) hrest
    split_ifs with h
    · simpa using ih'
    · have hns : x.sum ≠ 0 ∨ r ≠ 0 := by tauto
      have hblock : ∀ k ∈ [k1, k2, k3], ∀ b ∈ psw (k * r) (pw k x), b ≤ a := by
        intro k hk b hb
        refine ha k hk b ?_
        simp only [blk1, if_neg h]
        exact List.mem_append_left _ hb
      have h7 := lemma7 x r hns h0 h12 h23 a hblock
      omega

/-- The prefix-sum word of a nonempty word is nonempty. -/
theorem psw_ne_nil {r : ℤ} {w : List ℤ} (hw : w ≠ []) : psw r w ≠ [] := by
  cases w with
  | nil => exact absurd rfl hw
  | cons b w => simp [psw]

/-- The `I₁`-part is nonempty when some `xᵢ` has nonzero sum and `0 < k`. -/
theorem blk1_ne_nil {k : ℕ} (hk : 0 < k) (r : ℤ) {xs : List (List ℤ)}
    (hxs : ∃ x ∈ xs, x.sum ≠ 0) : blk1 k r xs ≠ [] := by
  induction xs generalizing r with
  | nil => simp at hxs
  | cons x xs ih =>
    simp only [blk1]
    by_cases hx : x.sum = 0
    · have hxs' : ∃ y ∈ xs, y.sum ≠ 0 := by
        obtain ⟨y, hy, hy0⟩ := hxs
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd hx hy0
        · exact ⟨y, hy', hy0⟩
      intro hnil
      exact ih (r + x.sum) hxs' (List.append_eq_nil_iff.mp hnil).2
    · have hcond : ¬ (r = 0 ∧ x.sum = 0) := fun h => hx h.2
      rw [if_neg hcond]
      have hxne : x ≠ [] := by rintro rfl; simp at hx
      have hpw : pw k x ≠ [] := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [pw_succ]; simp [hxne]
      intro hnil
      exact psw_ne_nil hpw (List.append_eq_nil_iff.mp hnil).1

/-- **Saarela, Lemma 8** (three-exponent form). Let `x₀` be a zero-sum word over `ℤ` and
`x₁, …, xₙ` words not all of which are zero-sum. Then there are no three positive integers
`k₁ < k₂ < k₃` such that `psw(x₀^k)` and `psw(x₁^k ⋯ xₙ^k)` are abelian equivalent
(permutations of each other) for every `k ∈ {k₁, k₂, k₃}`. -/
theorem lemma8 (x0 : List ℤ) (xs : List (List ℤ)) (hx0 : x0.sum = 0)
    (hxs : ∃ x ∈ xs, x.sum ≠ 0) {k1 k2 k3 : ℕ} (h0 : 0 < k1) (h12 : k1 < k2)
    (h23 : k2 < k3)
    (hp : ∀ k ∈ [k1, k2, k3], (psw 0 (pw k x0)).Perm (psw 0 (xs.map (pw k)).flatten)) :
    False := by
  classical
  set L := blk1 k1 0 xs ++ blk1 k2 0 xs ++ blk1 k3 0 xs with hL
  have hLne : L.toFinset.Nonempty := by
    rw [List.toFinset_nonempty_iff]
    intro hnil
    exact blk1_ne_nil h0 0 hxs (by
      simp only [hL, List.append_assoc, List.append_eq_nil_iff] at hnil
      exact hnil.1)
  obtain ⟨a, haL, hmax⟩ := L.toFinset.exists_max_image id hLne
  simp only [List.mem_toFinset, id] at haL hmax
  -- the count identity `k c₀ = f k + k C` for each `k ∈ K`
  have hid : ∀ k ∈ [k1, k2, k3], k * (psw 0 x0).count a =
      (blk1 k 0 xs).count a + k * (blk0 1 0 xs).count a := by
    intro k hk
    have hc := (hp k hk).count_eq a
    rw [count_psw_pw_of_sum_eq_zero a k hx0,
      show (0 : ℤ) = (k : ℤ) * 0 by ring, count_psw_flatten, count_blk0] at hc
    exact hc
  have ha : ∀ k ∈ [k1, k2, k3], ∀ b ∈ blk1 k 0 xs, b ≤ a := by
    intro k hk b hb
    refine hmax b ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> simp [hL, hb]
  have hmono := count_blk1_le xs 0 h0 h12 h23 a ha
  have hpos : 0 < (blk1 k1 0 xs).count a + (blk1 k2 0 xs).count a +
      (blk1 k3 0 xs).count a := by
    simp only [hL, List.mem_append] at haL
    rcases haL with (h | h) | h
    · have := List.count_pos_iff.mpr h; omega
    · have := List.count_pos_iff.mpr h; omega
    · have := List.count_pos_iff.mpr h; omega
  have e1 := hid k1 (by simp)
  have e2 := hid k2 (by simp)
  have e3 := hid k3 (by simp)
  set c0 := (psw 0 x0).count a
  set C := (blk0 1 0 xs).count a
  set f1 := (blk1 k1 0 xs).count a
  set f2 := (blk1 k2 0 xs).count a
  set f3 := (blk1 k3 0 xs).count a
  have z1 : (f1 : ℤ) = k1 * ((c0 : ℤ) - C) := by push_cast [← Nat.cast_inj (R := ℤ)] at e1; linarith
  have z2 : (f2 : ℤ) = k2 * ((c0 : ℤ) - C) := by push_cast [← Nat.cast_inj (R := ℤ)] at e2; linarith
  have z3 : (f3 : ℤ) = k3 * ((c0 : ℤ) - C) := by push_cast [← Nat.cast_inj (R := ℤ)] at e3; linarith
  have hK12 : (k1 : ℤ) < k2 := by exact_mod_cast h12
  have hd : (c0 : ℤ) - C ≤ 0 := by
    have hm : (f2 : ℤ) ≤ f1 := by exact_mod_cast hmono
    nlinarith
  have hf1 : (f1 : ℤ) ≤ 0 := by rw [z1]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hd
  have hf2 : (f2 : ℤ) ≤ 0 := by rw [z2]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hd
  have hf3 : (f3 : ℤ) ≤ 0 := by rw [z3]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hd
  omega


/-- The set `K(x₀; x₁, …, xₙ)` of positive exponents `k` for which `psw(x₀^k)` and
`psw(x₁^k ⋯ xₙ^k)` are abelian equivalent. -/
def abelK (x0 : List ℤ) (xs : List (List ℤ)) : Set ℕ :=
  {k | 0 < k ∧ (psw 0 (pw k x0)).Perm (psw 0 (xs.map (pw k)).flatten)}

/-- **Saarela, Lemma 8** (as stated in the paper). Let `x₀` be a zero-sum word over `ℤ`
and `x₁, …, xₙ` words not all of which have zero sum. There are at most two positive
integers `k` such that `psw(x₀^k)` and `psw(x₁^k ⋯ xₙ^k)` are abelian equivalent. -/
theorem lemma8_encard_le_two (x0 : List ℤ) (xs : List (List ℤ)) (hx0 : x0.sum = 0)
    (hxs : ∃ x ∈ xs, x.sum ≠ 0) : (abelK x0 xs).encard ≤ 2 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨t, hts, ht3⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
  obtain ⟨p, q, u, hpq, hpu, hqu, rfl⟩ := Set.encard_eq_three.mp ht3
  have hp : p ∈ abelK x0 xs := hts (by simp)
  have hq : q ∈ abelK x0 xs := hts (by simp)
  have hu : u ∈ abelK x0 xs := hts (by simp)
  have key : ∀ a b c : ℕ, a ∈ abelK x0 xs → b ∈ abelK x0 xs → c ∈ abelK x0 xs →
      a < b → b < c → False := by
    intro a b c ha hb hc hab hbc
    refine lemma8 x0 xs hx0 hxs ha.1 hab hbc ?_
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact ha.2
    · exact hb.2
    · exact hc.2
  rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hpu with h2 | h2 <;>
    rcases lt_or_gt_of_ne hqu with h3 | h3
  all_goals first
    | exact key _ _ _ hp hq hu (by omega) (by omega)
    | exact key _ _ _ hp hu hq (by omega) (by omega)
    | exact key _ _ _ hq hp hu (by omega) (by omega)
    | exact key _ _ _ hq hu hp (by omega) (by omega)
    | exact key _ _ _ hu hp hq (by omega) (by omega)
    | exact key _ _ _ hu hq hp (by omega) (by omega)

/-! ## Non-vacuity and sharpness

With `a = 2`, `b = -3`, the word `x₀ = ababa` is zero-sum, `x₁ = ab` is not, and
`(ababa)^k = (ab)^k a^k (ba)^k` holds for `k ∈ {1, 2}` (the paper's example). Hence the
bound `2` in Lemma 8 is attained. -/

example : ([2, -3, 2, -3, 2] : List ℤ).sum = 0 := by decide
example : ([2, -3] : List ℤ).sum ≠ 0 := by decide

/-- Sharpness of Lemma 8: for `x₀ = ababa`, `x₁ = ab`, `x₂ = a`, `x₃ = ba` with `a = 2`,
`b = -3`, the set `K` is exactly `{1, 2}`. -/
theorem abelK_example : abelK [2, -3, 2, -3, 2] [[2, -3], [2], [-3, 2]] = {1, 2} := by
  have h1 : 1 ∈ abelK [2, -3, 2, -3, 2] [[2, -3], [2], [-3, 2]] :=
    ⟨by norm_num, by decide⟩
  have h2 : 2 ∈ abelK [2, -3, 2, -3, 2] [[2, -3], [2], [-3, 2]] :=
    ⟨by norm_num, by decide⟩
  have hle := lemma8_encard_le_two [2, -3, 2, -3, 2] [[2, -3], [2], [-3, 2]] (by decide)
    ⟨[2, -3], by simp, by decide⟩
  have hsub : ({1, 2} : Set ℕ) ⊆ abelK [2, -3, 2, -3, 2] [[2, -3], [2], [-3, 2]] := by
    intro k hk
    rcases hk with rfl | rfl
    · exact h1
    · exact h2
  have h12 : ({1, 2} : Set ℕ).encard = 2 := Set.encard_pair (by norm_num)
  exact (Set.Finite.eq_of_subset_of_encard_le (Set.toFinite _) hsub
    (by rw [h12]; exact hle)).symm

end Candidates.SaarelaWordEquationLemma
