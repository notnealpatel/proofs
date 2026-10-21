/-
# Reverse-mex for the additive subtraction sets `{a, ab, a(b+1)}`

## Source

U. Larsson, H. Manabe, R. Miyadera, *A Subtraction Nim with a Pass*,
arXiv:2605.14321.  Definition `inversemex` (Section `subtractionnim`) and
Section "Conjectures" (label `conject`), subsection "Prediction on the
Reverse-Mex Property", second conjecture.

Definition (verbatim, Definition `inversemex`): "A subtraction Nim is said to
satisfy *reverse-mex* property if
`𝒢(x) = mex({𝒢(x+s_1), 𝒢(x+s_2), 𝒢(x+s_3)})`."

Conjecture (verbatim): "If `s_3 = s_1 + s_2`, then the subtraction Nim
satisfies the condition (a) in Conjecture `conditiona`."  Combined with the
paper's Conjecture `conditiona` ("A subtraction Nim has the reverse-mex
property if and only if this Nim satisfies the following (a)") this predicts:
every subtraction Nim with `S = {s_1, s_2, s_1 + s_2}` has the reverse-mex
property.  The paper proves reverse-mex only for `{2, 4n, 4n+2}`, `n ≥ 3`.

Status in the paper: conjecture based on computer calculation (open).

## This module (2026-10-21)

Special case of the conjecture (target `a6-22`): for every `a ≥ 1` and
`b ≥ 2`, the subtraction game with `S = {a, ab, a(b+1)}` (so
`s_3 = s_1 + s_2`) satisfies reverse-mex at every `x ≥ 0`.  The proof
combines

* the scaling lemma `𝒢_{aS}(x) = 𝒢_S(⌊x/a⌋)` (`grundy_scale`), and
* the closed form for `S = {1, b, b+1}` (`grundy_one_b_closed`):
  for even `b`, `𝒢(x) = 2·[x mod 2b ≥ b] + (x mod 2)`; for odd `b`, with
  `r = x mod (2b+1)`, `𝒢(x) = r mod 2` if `r ≤ b`, else `2 + ((r-b-1) mod 2)`.

As a corollary this settles equation (conjecture1) of the paper's pass
conjecture, part (a), for every `{a, 2an, 2an+a}` (`reverseMex_setA`).
The general conjecture for arbitrary `{s_1, s_2, s_1+s_2}` remains open.
-/
import Mathlib

set_option autoImplicit false

namespace SubtractionNimReverseMexAdditive

/-- The minimum excluded value of a finite set of natural numbers: the least
`m : ℕ` with `m ∉ s`. -/
noncomputable def mex (s : Finset ℕ) : ℕ :=
  Nat.find (Infinite.exists_notMem_finset s)

/-- Characterisation of `mex`: `mex s = m` iff `m ∉ s` and every smaller
natural number lies in `s`. -/
theorem mex_eq_iff (s : Finset ℕ) (m : ℕ) : mex s = m ↔ m ∉ s ∧ ∀ n < m, n ∈ s := by
  unfold mex
  rw [Nat.find_eq_iff]
  simp

/-- The legal subtraction amounts at a pile of `x` stones: the `s ∈ S` with
`0 < s ≤ x`. -/
def legal (S : Finset ℕ) (x : ℕ) : Finset ℕ :=
  S.filter (fun s => 0 < s ∧ s ≤ x)

/-- Grundy number `𝒢(x)` of the subtraction game with subtraction set `S`:
`𝒢(x) = mex{𝒢(x-s) : s ∈ S, 0 < s ≤ x}`. -/
noncomputable def grundy (S : Finset ℕ) (x : ℕ) : ℕ :=
  mex ((legal S x).attach.image (fun s => grundy S (x - s.1)))
termination_by x
decreasing_by
  have h := (Finset.mem_filter.mp s.2).2
  omega

/-- Unfolding equation for `grundy` without the `attach`. -/
theorem grundy_eq (S : Finset ℕ) (x : ℕ) :
    grundy S x = mex ((legal S x).image (fun s => grundy S (x - s))) := by
  rw [grundy]
  congr 1
  ext v
  simp

/-- Uniqueness of the Grundy function: any `F` satisfying the Grundy recursion
for `S` at every position equals `grundy S`. -/
theorem grundy_eq_of_forall (S : Finset ℕ) (F : ℕ → ℕ)
    (hF : ∀ x, F x = mex ((legal S x).image (fun s => F (x - s)))) (x : ℕ) :
    grundy S x = F x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [grundy_eq, hF x]
    congr 1
    refine Finset.image_congr ?_
    intro s hs
    have hs' := (Finset.mem_filter.mp hs).2
    exact ih (x - s) (by omega)

/-- Scaling lemma: multiplying every move by `a > 0` stretches the Grundy
sequence, `𝒢_{aS}(x) = 𝒢_S(⌊x/a⌋)`. -/
theorem grundy_scale (a : ℕ) (ha : 0 < a) (S : Finset ℕ) (x : ℕ) :
    grundy (S.image (a * ·)) x = grundy S (x / a) := by
  refine grundy_eq_of_forall _ (fun x => grundy S (x / a)) ?_ x
  intro x
  rw [grundy_eq]
  congr 1
  ext v
  simp only [legal, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, htpos, htle⟩, rfl⟩
    refine ⟨a * t, ⟨⟨t, ht, rfl⟩, Nat.mul_pos ha htpos, ?_⟩, ?_⟩
    · have := (Nat.le_div_iff_mul_le ha).mp htle
      linarith [Nat.mul_comm a t]
    · rw [Nat.sub_mul_div]
  · rintro ⟨s, ⟨⟨t, ht, rfl⟩, hspos, hsle⟩, rfl⟩
    refine ⟨t, ⟨ht, Nat.pos_of_mul_pos_left hspos, ?_⟩, ?_⟩
    · rw [Nat.le_div_iff_mul_le ha]
      linarith [Nat.mul_comm a t]
    · rw [Nat.sub_mul_div]

/-- A Grundy value never repeats along a move: for `s ∈ S` with `0 < s`,
`𝒢(x + s) ≠ 𝒢(x)`, since `x` is an option of `x + s`. -/
theorem grundy_add_ne (S : Finset ℕ) (x s : ℕ) (hs : s ∈ S) (hpos : 0 < s) :
    grundy S (x + s) ≠ grundy S x := by
  intro heq
  have hmex := ((mex_eq_iff _ _).mp (grundy_eq S (x + s)).symm).1
  apply hmex
  refine Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hpos, Nat.le_add_left s x⟩, ?_⟩
  rw [Nat.add_sub_cancel, heq]

/-- The reverse-mex property (paper, Definition `inversemex`) of the
subtraction game with set `S`: `𝒢(x) = mex{𝒢(x+s) : s ∈ S}` for every `x`. -/
def ReverseMex (S : Finset ℕ) : Prop :=
  ∀ x, grundy S x = mex (S.image fun s => grundy S (x + s))

/-- Criterion for reverse-mex: if all moves are positive and every value below
`𝒢(x)` is attained by some `𝒢(x+s)`, `s ∈ S`, then reverse-mex holds at `x`. -/
theorem reverseMex_at_of (S : Finset ℕ) (x : ℕ) (hpos : ∀ s ∈ S, 0 < s)
    (h : ∀ n < grundy S x, ∃ s ∈ S, grundy S (x + s) = n) :
    grundy S x = mex (S.image fun s => grundy S (x + s)) := by
  symm
  rw [mex_eq_iff]
  constructor
  · simp only [Finset.mem_image, not_exists, not_and]
    intro s hs heq
    exact grundy_add_ne S x s hs (hpos s hs) heq
  · intro n hn
    obtain ⟨s, hs, hsn⟩ := h n hn
    exact Finset.mem_image.mpr ⟨s, hs, hsn⟩

/-- Reverse-mex is preserved by scaling the subtraction set by `a > 0`. -/
theorem reverseMex_scale (a : ℕ) (ha : 0 < a) (S : Finset ℕ) (h : ReverseMex S) :
    ReverseMex (S.image (a * ·)) := by
  intro x
  rw [grundy_scale a ha, h (x / a), Finset.image_image]
  congr 1
  refine Finset.image_congr ?_
  intro t _
  simp only [Function.comp_apply]
  rw [grundy_scale a ha, Nat.add_mul_div_left x t ha]

/-! ### Residue arithmetic -/

/-- Residue of `y - t` modulo `m` in terms of `r = y % m`, for `t ≤ m` and `t ≤ y`. -/
theorem mod_sub_facts (m y t : ℕ) (hm : 0 < m) (ht : t ≤ m) (hty : t ≤ y) :
    (t ≤ y % m → (y - t) % m = y % m - t) ∧ (y % m < t → (y - t) % m = y % m + m - t) := by
  have hdm := Nat.div_add_mod y m
  have hr := Nat.mod_lt y hm
  generalize y / m = q at hdm
  generalize y % m = r at hdm hr ⊢
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hy : y - t = (r - t) + m * q := by omega
    rw [hy, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := by
      rcases q with _ | q'
      · omega
      · exact ⟨q', rfl⟩
    have hy : y - t = (r + m - t) + m * q' := by rw [Nat.mul_add] at hdm; omega
    rw [hy, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Disjunctive form of `mod_sub_facts`: either the move `t` is illegal, or
`(y - t) % m + t` equals `y % m` or `y % m + m`. -/
theorem mod_sub_cases (m y t : ℕ) (hm : 0 < m) (ht : t ≤ m) :
    y < t ∨ (y - t) % m + t = y % m ∨ (y - t) % m + t = y % m + m := by
  rcases Nat.lt_or_ge y t with h | h
  · exact Or.inl h
  · have hf := mod_sub_facts m y t hm ht h
    rcases Nat.lt_or_ge (y % m) t with h' | h'
    · exact Or.inr (Or.inr (by rw [hf.2 h']; omega))
    · exact Or.inr (Or.inl (by rw [hf.1 h']; omega))

/-- Either `y < m` (so `y % m = y`) or `y` exceeds its residue by at least `m`. -/
theorem mod_le_cases (m y : ℕ) : y % m = y ∨ y % m + m ≤ y := by
  rcases Nat.lt_or_ge y m with h | h
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · right
    have := Nat.mod_le (y - m) m
    rw [← Nat.mod_eq_sub_mod h] at this
    omega

/-- Residue of `y + t` modulo `m` in terms of `r = y % m`, for `t ≤ m`. -/
theorem mod_add_facts (m y t : ℕ) (hm : 0 < m) (ht : t ≤ m) :
    (y % m + t < m → (y + t) % m = y % m + t) ∧
      (m ≤ y % m + t → (y + t) % m = y % m + t - m) := by
  have hdm := Nat.div_add_mod y m
  have hr := Nat.mod_lt y hm
  generalize y / m = q at hdm
  generalize y % m = r at hdm hr ⊢
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hy : y + t = (r + t) + m * q := by omega
    rw [hy, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · have hy : y + t = (r + t - m) + m * (q + 1) := by rw [Nat.mul_add]; omega
    rw [hy, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]


/-! ### The closed form for `S = {1, b, b+1}` -/

/-- The closed form of the Grundy sequence of `S = {1, b, b+1}` (target spec):
for even `b`, `2·[x mod 2b ≥ b] + (x mod 2)`; for odd `b`, with
`r = x mod (2b+1)`, `r mod 2` if `r ≤ b` and `2 + ((r-b-1) mod 2)` otherwise
(the subtraction `r - b - 1` is guarded by `b < r`). -/
def closedForm (b x : ℕ) : ℕ :=
  if Even b then 2 * (if b ≤ x % (2 * b) then 1 else 0) + x % 2
  else if x % (2 * b + 1) ≤ b then x % (2 * b + 1) % 2 else 2 + (x % (2 * b + 1) - b - 1) % 2

/-- Membership in the image of the legal moves of `{1, b, b+1}` at `y`,
as an explicit three-way disjunction. -/
theorem mem_image_legal (b y v : ℕ) (hb : 1 ≤ b) (h : ℕ → ℕ) :
    v ∈ (legal {1, b, b + 1} y).image h ↔
      (1 ≤ y ∧ h 1 = v) ∨ (b ≤ y ∧ h b = v) ∨ (b + 1 ≤ y ∧ h (b + 1) = v) := by
  simp only [legal, Finset.mem_image, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨s, ⟨hs | hs | hs, _, hsy⟩, rfl⟩ <;> subst hs <;> simp_all
  · rintro (⟨hy, rfl⟩ | ⟨hy, rfl⟩ | ⟨hy, rfl⟩)
    · exact ⟨1, ⟨Or.inl rfl, Nat.one_pos, hy⟩, rfl⟩
    · exact ⟨b, ⟨Or.inr (Or.inl rfl), by omega, hy⟩, rfl⟩
    · exact ⟨b + 1, ⟨Or.inr (Or.inr rfl), by omega, hy⟩, rfl⟩

/-- Disjunctive form of `mod_add_facts`. -/
theorem mod_add_cases (m y t : ℕ) (hm : 0 < m) (ht : t ≤ m) :
    (y + t) % m = y % m + t ∨ (y + t) % m + m = y % m + t := by
  have hf := mod_add_facts m y t hm ht
  rcases Nat.lt_or_ge (y % m + t) m with h | h
  · exact Or.inl (hf.1 h)
  · exact Or.inr (by rw [hf.2 h]; omega)

/-- The even-`b` closed form as a function of the residue `r = x mod 2b`. -/
def gEven (b r : ℕ) : ℕ := if b ≤ r then 2 + r % 2 else r % 2

/-- The odd-`b` closed form as a function of the residue `r = x mod (2b+1)`. -/
def gOdd (b r : ℕ) : ℕ := if b < r then 2 + r % 2 else r % 2

/-- For even `b`, the closed form factors through `x mod 2b`. -/
theorem closedForm_of_even (b y : ℕ) (he : Even b) :
    closedForm b y = gEven b (y % (2 * b)) := by
  have h5 : y % (2 * b) % 2 = y % 2 := Nat.mod_mod_of_dvd y (Dvd.intro b rfl)
  simp only [closedForm, if_pos he, gEven, h5]
  split_ifs <;> omega

/-- For odd `b`, the closed form factors through `x mod (2b+1)`; for `b < r`,
`(r - b - 1) mod 2 = r mod 2` because `b + 1` is even. -/
theorem closedForm_of_odd (b y : ℕ) (ho : ¬ Even b) :
    closedForm b y = gOdd b (y % (2 * b + 1)) := by
  have hb : b % 2 = 1 := Nat.not_even_iff.mp ho
  simp only [closedForm, if_neg ho, gOdd]
  split_ifs <;> omega

/-- For even `b ≥ 2`, the closed form satisfies the Grundy recursion of
`{1, b, b+1}`. -/
theorem closedForm_even_rec (b y : ℕ) (hb : 2 ≤ b) (he : Even b) :
    mex ((legal {1, b, b + 1} y).image fun s => closedForm b (y - s)) = closedForm b y := by
  rw [mex_eq_iff]
  simp only [mem_image_legal b y _ (by omega : 1 ≤ b), closedForm_of_even b _ he]
  have hb2 : b % 2 = 0 := Nat.even_iff.mp he
  have hm : 0 < 2 * b := by omega
  have h0 := Nat.mod_lt y hm
  have h1 := mod_sub_cases (2 * b) y 1 hm (by omega)
  have h2 := mod_sub_cases (2 * b) y b hm (by omega)
  have h3 := mod_sub_cases (2 * b) y (b + 1) hm (by omega)
  have h4 := mod_le_cases (2 * b) y
  have h1' := Nat.mod_lt (y - 1) hm
  have h2' := Nat.mod_lt (y - b) hm
  have h3' := Nat.mod_lt (y - (b + 1)) hm
  generalize y % (2 * b) = r at *
  generalize (y - 1) % (2 * b) = r1 at *
  generalize (y - b) % (2 * b) = r2 at *
  generalize (y - (b + 1)) % (2 * b) = r3 at *
  refine ⟨?_, fun n hn => ?_⟩
  · simp only [gEven]
    split_ifs <;> omega
  · have hp := Nat.mod_two_eq_zero_or_one r
    unfold gEven at hn ⊢
    by_cases hh : b ≤ r
    · rw [if_pos hh] at hn
      have hy : b ≤ y := by omega
      have hr2 : r2 = r - b := by omega
      rcases hp with hp | hp
      · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
        · exact Or.inr (Or.inl ⟨hy, by rw [if_neg (by omega)]; omega⟩)
        · by_cases hrb : r = b
          · exact Or.inl ⟨by omega, by rw [if_neg (by omega)]; omega⟩
          · exact Or.inr (Or.inr ⟨by omega, by rw [if_neg (by omega)]; omega⟩)
      · obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
        · exact Or.inr (Or.inr ⟨by omega, by rw [if_neg (by omega)]; omega⟩)
        · exact Or.inr (Or.inl ⟨hy, by rw [if_neg (by omega)]; omega⟩)
        · exact Or.inl ⟨by omega, by rw [if_pos (by omega)]; omega⟩
    · rw [if_neg hh] at hn
      obtain rfl : n = 0 := by omega
      exact Or.inl ⟨by omega, by rw [if_neg (by omega)]; omega⟩

/-- For odd `b ≥ 2`, the closed form satisfies the Grundy recursion of
`{1, b, b+1}`. -/
theorem closedForm_odd_rec (b y : ℕ) (hb : 2 ≤ b) (ho : ¬ Even b) :
    mex ((legal {1, b, b + 1} y).image fun s => closedForm b (y - s)) = closedForm b y := by
  rw [mex_eq_iff]
  simp only [mem_image_legal b y _ (by omega : 1 ≤ b), closedForm_of_odd b _ ho]
  have hb2 : b % 2 = 1 := Nat.not_even_iff.mp ho
  have hm : 0 < 2 * b + 1 := by omega
  have h0 := Nat.mod_lt y hm
  have h1 := mod_sub_cases (2 * b + 1) y 1 hm (by omega)
  have h2 := mod_sub_cases (2 * b + 1) y b hm (by omega)
  have h3 := mod_sub_cases (2 * b + 1) y (b + 1) hm (by omega)
  have h4 := mod_le_cases (2 * b + 1) y
  have h1' := Nat.mod_lt (y - 1) hm
  have h2' := Nat.mod_lt (y - b) hm
  have h3' := Nat.mod_lt (y - (b + 1)) hm
  generalize y % (2 * b + 1) = r at *
  generalize (y - 1) % (2 * b + 1) = r1 at *
  generalize (y - b) % (2 * b + 1) = r2 at *
  generalize (y - (b + 1)) % (2 * b + 1) = r3 at *
  refine ⟨?_, fun n hn => ?_⟩
  · simp only [gOdd]
    split_ifs <;> omega
  · have hp := Nat.mod_two_eq_zero_or_one r
    unfold gOdd at hn ⊢
    by_cases hh : b < r
    · rw [if_pos hh] at hn
      have hy : b + 1 ≤ y := by omega
      have hr2 : r2 = r - b := by omega
      have hr3 : r3 = r - (b + 1) := by omega
      rcases hp with hp | hp
      · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
        · exact Or.inr (Or.inr ⟨hy, by rw [if_neg (by omega)]; omega⟩)
        · exact Or.inr (Or.inl ⟨by omega, by rw [if_neg (by omega)]; omega⟩)
      · obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
        · exact Or.inr (Or.inl ⟨by omega, by rw [if_neg (by omega)]; omega⟩)
        · exact Or.inr (Or.inr ⟨hy, by rw [if_neg (by omega)]; omega⟩)
        · exact Or.inl ⟨by omega, by rw [if_pos (by omega)]; omega⟩
    · rw [if_neg hh] at hn
      obtain rfl : n = 0 := by omega
      exact Or.inl ⟨by omega, by rw [if_neg (by omega)]; omega⟩

/-- For even `b ≥ 2`, every value below the closed form at `y` is attained at
`y + 1`, `y + b` or `y + b + 1`. -/
theorem closedForm_even_fwd (b y n : ℕ) (hb : 2 ≤ b) (he : Even b) (hn : n < closedForm b y) :
    closedForm b (y + 1) = n ∨ closedForm b (y + b) = n ∨ closedForm b (y + (b + 1)) = n := by
  simp only [closedForm_of_even b _ he] at hn ⊢
  have hb2 : b % 2 = 0 := Nat.even_iff.mp he
  have hm : 0 < 2 * b := by omega
  have h0 := Nat.mod_lt y hm
  have h1 := mod_add_cases (2 * b) y 1 hm (by omega)
  have h2 := mod_add_cases (2 * b) y b hm (by omega)
  have h3 := mod_add_cases (2 * b) y (b + 1) hm (by omega)
  have h1' := Nat.mod_lt (y + 1) hm
  have h2' := Nat.mod_lt (y + b) hm
  have h3' := Nat.mod_lt (y + (b + 1)) hm
  generalize y % (2 * b) = r at *
  generalize (y + 1) % (2 * b) = r1 at *
  generalize (y + b) % (2 * b) = r2 at *
  generalize (y + (b + 1)) % (2 * b) = r3 at *
  have hp := Nat.mod_two_eq_zero_or_one r
  unfold gEven at hn ⊢
  by_cases hh : b ≤ r
  · rw [if_pos hh] at hn
    have hr2 : r2 = r - b := by omega
    rcases hp with hp | hp
    · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · exact Or.inr (Or.inl (by rw [if_neg (by omega)]; omega))
      · exact Or.inr (Or.inr (by rw [if_neg (by omega)]; omega))
    · obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      · by_cases hr : r + 1 = 2 * b
        · exact Or.inl (by rw [if_neg (by omega)]; omega)
        · exact Or.inr (Or.inr (by rw [if_neg (by omega)]; omega))
      · exact Or.inr (Or.inl (by rw [if_neg (by omega)]; omega))
      · by_cases hr : r + 1 = 2 * b
        · exact Or.inr (Or.inr (by rw [if_pos (by omega)]; omega))
        · exact Or.inl (by rw [if_pos (by omega)]; omega)
  · rw [if_neg hh] at hn
    obtain rfl : n = 0 := by omega
    by_cases hr : r + 1 = b
    · exact Or.inr (Or.inr (by rw [if_neg (by omega)]; omega))
    · exact Or.inl (by rw [if_neg (by omega)]; omega)

/-- For odd `b ≥ 2`, every value below the closed form at `y` is attained at
`y + 1`, `y + b` or `y + b + 1`. -/
theorem closedForm_odd_fwd (b y n : ℕ) (hb : 2 ≤ b) (ho : ¬ Even b) (hn : n < closedForm b y) :
    closedForm b (y + 1) = n ∨ closedForm b (y + b) = n ∨ closedForm b (y + (b + 1)) = n := by
  simp only [closedForm_of_odd b _ ho] at hn ⊢
  have hb2 : b % 2 = 1 := Nat.not_even_iff.mp ho
  have hm : 0 < 2 * b + 1 := by omega
  have h0 := Nat.mod_lt y hm
  have h1 := mod_add_cases (2 * b + 1) y 1 hm (by omega)
  have h2 := mod_add_cases (2 * b + 1) y b hm (by omega)
  have h3 := mod_add_cases (2 * b + 1) y (b + 1) hm (by omega)
  have h1' := Nat.mod_lt (y + 1) hm
  have h2' := Nat.mod_lt (y + b) hm
  have h3' := Nat.mod_lt (y + (b + 1)) hm
  generalize y % (2 * b + 1) = r at *
  generalize (y + 1) % (2 * b + 1) = r1 at *
  generalize (y + b) % (2 * b + 1) = r2 at *
  generalize (y + (b + 1)) % (2 * b + 1) = r3 at *
  have hp := Nat.mod_two_eq_zero_or_one r
  unfold gOdd at hn ⊢
  by_cases hh : b < r
  · rw [if_pos hh] at hn
    have hr2 : r2 = r - (b + 1) := by omega
    have hr3 : r3 = r - b := by omega
    rcases hp with hp | hp
    · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · exact Or.inr (Or.inl (by rw [if_neg (by omega)]; omega))
      · exact Or.inr (Or.inr (by rw [if_neg (by omega)]; omega))
    · obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      · exact Or.inr (Or.inr (by rw [if_neg (by omega)]; omega))
      · exact Or.inr (Or.inl (by rw [if_neg (by omega)]; omega))
      · exact Or.inl (by rw [if_pos (by omega)]; omega)
  · rw [if_neg hh] at hn
    obtain rfl : n = 0 := by omega
    by_cases hr : r = b
    · exact Or.inr (Or.inr (by rw [if_neg (by omega)]; omega))
    · exact Or.inl (by rw [if_neg (by omega)]; omega)

/-- **Closed form for `S = {1, b, b+1}`.**  For `b ≥ 2` the Grundy number of
the subtraction game with set `{1, b, b+1}` is: for even `b`,
`𝒢(x) = 2·[x mod 2b ≥ b] + (x mod 2)`; for odd `b`, with `r = x mod (2b+1)`,
`𝒢(x) = r mod 2` if `r ≤ b` and `2 + ((r-b-1) mod 2)` otherwise. -/
theorem grundy_one_b_closed (b : ℕ) (hb : 2 ≤ b) (x : ℕ) :
    grundy {1, b, b + 1} x =
      if Even b then 2 * (if b ≤ x % (2 * b) then 1 else 0) + x % 2
      else if x % (2 * b + 1) ≤ b then x % (2 * b + 1) % 2
      else 2 + (x % (2 * b + 1) - b - 1) % 2 := by
  refine grundy_eq_of_forall _ (closedForm b) (fun y => ?_) x
  by_cases he : Even b
  · exact (closedForm_even_rec b y hb he).symm
  · exact (closedForm_odd_rec b y hb he).symm

/-- Reverse-mex for `S = {1, b, b+1}`, `b ≥ 2`. -/
theorem reverseMex_one_b (b : ℕ) (hb : 2 ≤ b) : ReverseMex {1, b, b + 1} := by
  intro x
  refine reverseMex_at_of _ x ?_ ?_
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    omega
  · intro n hn
    have hG : ∀ y, grundy {1, b, b + 1} y = closedForm b y := grundy_one_b_closed b hb
    rw [hG] at hn
    have hfwd : closedForm b (x + 1) = n ∨ closedForm b (x + b) = n ∨
        closedForm b (x + (b + 1)) = n := by
      by_cases he : Even b
      · exact closedForm_even_fwd b x n hb he hn
      · exact closedForm_odd_fwd b x n hb he hn
    simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, hG]
    exact hfwd

/-- **Reverse-mex for `{a, ab, a(b+1)}`** (special case of the second
conjecture of Section "Conjectures" of arXiv:2605.14321, the case
`s_3 = s_1 + s_2` with `s_1 ∣ s_2`).  For every `a ≥ 1` and `b ≥ 2`, the
subtraction game with `S = {a, ab, a(b+1)}` satisfies
`𝒢(x) = mex{𝒢(x+a), 𝒢(x+ab), 𝒢(x+a(b+1))}` for every `x ≥ 0`. -/
theorem reverseMex_additive_multiple (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b) (x : ℕ) :
    grundy {a, a * b, a * (b + 1)} x =
      mex (({a, a * b, a * (b + 1)} : Finset ℕ).image fun s =>
        grundy {a, a * b, a * (b + 1)} (x + s)) := by
  have hS : ({a, a * b, a * (b + 1)} : Finset ℕ) = ({1, b, b + 1} : Finset ℕ).image (a * ·) := by
    simp [Finset.image_insert]
  rw [hS]
  exact reverseMex_scale a ha _ (reverseMex_one_b b hb) x

/-- Corollary: equation (conjecture1) of the paper's pass conjecture, part (a),
holds for every `{a, 2an, 2an+a}` with `a, n ≥ 1`: the plain subtraction game
(no pass) with this set satisfies reverse-mex at every `x`. -/
theorem reverseMex_setA (a n : ℕ) (ha : 0 < a) (hn : 0 < n) (x : ℕ) :
    grundy {a, 2 * a * n, 2 * a * n + a} x =
      mex (({a, 2 * a * n, 2 * a * n + a} : Finset ℕ).image fun s =>
        grundy {a, 2 * a * n, 2 * a * n + a} (x + s)) := by
  have hS : ({a, 2 * a * n, 2 * a * n + a} : Finset ℕ) = {a, a * (2 * n), a * (2 * n + 1)} := by
    rw [show 2 * a * n + a = a * (2 * n + 1) by ring, show 2 * a * n = a * (2 * n) by ring]
  rw [hS]
  exact reverseMex_additive_multiple a (2 * n) ha (by omega) x

/-! ### Ground-truth checks -/

example : mex {0, 1, 3} = 2 := (mex_eq_iff _ _).mpr (by decide)

example : mex ∅ = 0 := (mex_eq_iff _ _).mpr (by decide)

example : legal {1, 4, 5} 4 = {1, 4} := by decide

/-- `{1,4,5}`: the closed form gives `0,1,0,1,2,3,2,3,0,1` for `x = 0..9`
(matching the Grundy values `𝒢(x,0)` computed move by move in
`SubtractionNimPassRefutation`). -/
example : (List.range 10).map (closedForm 4) = [0, 1, 0, 1, 2, 3, 2, 3, 0, 1] := by decide

/-- `{1,3,4}` (odd `b = 3`): period `7`, values `0,1,0,1,2,3,2`. -/
example : (List.range 8).map (closedForm 3) = [0, 1, 0, 1, 2, 3, 2, 0] := by decide

/-- `{1,2,3}`: `𝒢(x) = x mod 4`. -/
example : (List.range 8).map (closedForm 2) = [0, 1, 2, 3, 0, 1, 2, 3] := by decide

/-- Direct unfolding of `grundy`: `𝒢_{1,2,3}(0) = 0`. -/
example : grundy {1, 2, 3} 0 = 0 := by
  rw [grundy_eq]
  have hl : legal {1, 2, 3} 0 = ∅ := by decide
  rw [hl, Finset.image_empty]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- Direct unfolding of `grundy`: `𝒢_{1,2,3}(1) = 1`. -/
example : grundy {1, 2, 3} 1 = 1 := by
  have h0 : grundy {1, 2, 3} 0 = 0 := by
    rw [grundy_eq]
    have hl : legal {1, 2, 3} 0 = ∅ := by decide
    rw [hl, Finset.image_empty]
    exact (mex_eq_iff _ _).mpr (by decide)
  rw [grundy_eq]
  have hl : legal {1, 2, 3} 1 = {1} := by decide
  rw [hl, Finset.image_singleton, Nat.sub_self, h0]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- Non-vacuity of the hypotheses of `reverseMex_additive_multiple`: at
`a = 3`, `b = 2`, i.e. `S = {3, 6, 9}`. -/
example (x : ℕ) :
    grundy {3, 3 * 2, 3 * (2 + 1)} x =
      mex (({3, 3 * 2, 3 * (2 + 1)} : Finset ℕ).image fun s =>
        grundy {3, 3 * 2, 3 * (2 + 1)} (x + s)) :=
  reverseMex_additive_multiple 3 2 (by norm_num) le_rfl x

end SubtractionNimReverseMexAdditive
