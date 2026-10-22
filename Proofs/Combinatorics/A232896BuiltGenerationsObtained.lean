/-
# A232896 — positions of odd numbers in A232895

Clark Kimberling (OEIS A232895 and A232896, Dec 2013) conjectured that
the position of `2n-1` in A232895 is A232896(n). A232895 starts with
`1, 2`; each generation scans the preceding one in order, emits `x+2`
then `2x`, and deletes duplicates as they occur, as in Peter J. C. Moses's
program (Dec 02 2013). Tom Edgar (Mar 09 2015) gave the closed form
`a(n) = n - 1 + F(n+1)` for A232896.

The generations satisfy `g(k+1) = {2k+1} ∪ {2y : y > 0,
bitlen y + popcount y = k+2}`, begin with `2k+1`, and have `F(k+1)+1` elements.

## Encoding

Generations are 0-based: `gen k` is the entry's `g(k+1)`.  `prefixS N` is the concatenation
`g(1) ++ ⋯ ++ g(N)`; these are nested prefixes of `S` (`prefixS_eq_append`), so "the 1-based
position of `2n-1` in `S` is `a(n)`" is stated as: for every `N ≥ n`, `2n-1` occurs in
`prefixS N` and its 0-based `List.idxOf` there is `a(n) - 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A232896BuiltGenerationsObtained

/-! ## Definitions mirroring the entries -/

/-- Scan the candidate list in order and keep each candidate that has not been
seen before (neither in `seen` nor earlier in the scan): "duplicates are deleted as they
occur". -/
def emitNew : List ℕ → List ℕ → List ℕ
  | _, [] => []
  | seen, c :: cs => if c ∈ seen then emitNew seen cs else c :: emitNew (c :: seen) cs

/-- The candidates produced from a generation: `x + 2` then `2 * x` for each `x`, in order. -/
def children (g : List ℕ) : List ℕ := g.flatMap fun x => [x + 2, 2 * x]

/-- `genPair k = (g(k+1), g(1) ++ ⋯ ++ g(k+1))`: the current generation together with
everything generated so far. `g(1) = (1, 2)`, and `g(k+2)` is the new part of the children
of `g(k+1)`. -/
def genPair : ℕ → List ℕ × List ℕ
  | 0 => ([1, 2], [1, 2])
  | k + 1 =>
    let g := emitNew (genPair k).2 (children (genPair k).1)
    (g, (genPair k).2 ++ g)

/-- Generation `g(k+1)` of A232895 (0-based index `k`). -/
def gen (k : ℕ) : List ℕ := (genPair k).1

/-- The concatenation `g(1) ++ ⋯ ++ g(N)` of the first `N` generations: a prefix of
`S = A232895`. -/
def prefixS (N : ℕ) : List ℕ := (List.range N).flatMap gen

/-- A232896 by its defining recurrence `a(n) = 3a(n-1) - 2a(n-2) - a(n-3) + a(n-4)`,
`a(1..4) = 1, 3, 5, 8`, over `ℤ`.  The value `a 0 = 0` is the one forced by the recurrence
(`a 4 = 3·5 - 2·3 - 1 + a 0 = 8`) and by the entry's g.f.; it is not used by the
conjecture, which concerns `n ≥ 1`. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 5
  | n + 4 => 3 * a (n + 3) - 2 * a (n + 2) - a (n + 1) + a n

/-! ## Examples from the entries -/

example : gen 0 = [1, 2] := by decide
example : gen 1 = [3, 4] := by decide
example : gen 2 = [5, 6, 8] := by decide
example : gen 3 = [7, 10, 12, 16] := by decide
/-- The first 64 listed terms of A232895. -/
example : (prefixS 9).take 64 = [1, 2, 3, 4, 5, 6, 8, 7, 10, 12, 16, 9, 14, 20, 24, 18, 32, 11, 28,
    22, 40, 26, 48, 36, 34, 64, 13, 30, 56, 44, 42, 80, 52, 50, 96, 38, 72, 68, 66, 128, 15, 60, 58,
    112, 46, 88, 84, 82, 160, 54, 104, 100, 98, 192, 76, 74, 144, 70, 136, 132, 130, 256, 17, 62] := by
  decide
/-- The first 12 listed terms of A232896. -/
example : (List.range 12).map (fun n => a (n + 1)) =
    [1, 3, 5, 8, 12, 18, 27, 41, 63, 98, 154, 244] := by decide
/-- Direct check of the conjecture for `n = 5`: `9` sits at 1-based position `a 5 = 12`. -/
example : (prefixS 5).idxOf 9 + 1 = 12 := by decide

/-! ## Proof -/

/-- Membership in `emitNew seen cs`: exactly the candidates not in `seen`. -/
theorem mem_emitNew (seen cs : List ℕ) (x : ℕ) :
    x ∈ emitNew seen cs ↔ x ∈ cs ∧ x ∉ seen := by
  induction cs generalizing seen with
  | nil => simp [emitNew]
  | cons c cs ih =>
    unfold emitNew
    split_ifs with hc
    · rw [ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.1 h1 with rfl | h1
        · exact absurd hc h2
        · exact ⟨h1, h2⟩
    · rw [List.mem_cons, ih]
      simp only [List.mem_cons, not_or]
      constructor
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨Or.inl rfl, hc⟩
        · exact ⟨Or.inr h1, h3⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · by_cases hxc : x = c
          · exact Or.inl hxc
          · exact Or.inr ⟨h1, hxc, h2⟩

/-- `emitNew` never emits a value twice. -/
theorem nodup_emitNew (seen cs : List ℕ) : (emitNew seen cs).Nodup := by
  induction cs generalizing seen with
  | nil => simp [emitNew]
  | cons c cs ih =>
    unfold emitNew
    split_ifs with hc
    · exact ih seen
    · refine List.nodup_cons.2 ⟨?_, ih _⟩
      rw [mem_emitNew]
      simp

/-- A first candidate that is new is emitted first. -/
theorem emitNew_cons_of_notMem (seen cs : List ℕ) (c : ℕ) (hc : c ∉ seen) :
    emitNew seen (c :: cs) = c :: emitNew (c :: seen) cs := by
  simp [emitNew, hc]

/-- The second component of `genPair k` is the concatenation of generations `0, …, k`. -/
theorem genPair_snd (k : ℕ) : (genPair k).2 = prefixS (k + 1) := by
  induction k with
  | zero => simp [genPair, prefixS, gen]
  | succ k ih =>
    rw [prefixS, List.range_succ, List.flatMap_append, ← prefixS, ← ih]
    simp [genPair, gen]

/-- Generation `k + 1` is the new part of the children of generation `k`, scanned in order. -/
theorem gen_succ (k : ℕ) : gen (k + 1) = emitNew (prefixS (k + 1)) (children (gen k)) := by
  rw [← genPair_snd]; rfl

/-- Adding one generation to the prefix. -/
theorem prefixS_succ (N : ℕ) : prefixS (N + 1) = prefixS N ++ gen N := by
  simp [prefixS, List.range_succ]

/-- Membership in the prefix of `N` generations. -/
theorem mem_prefixS (N x : ℕ) : x ∈ prefixS N ↔ ∃ j < N, x ∈ gen j := by
  simp [prefixS]

/-- Membership in the children of a generation. -/
theorem mem_children (g : List ℕ) (x : ℕ) :
    x ∈ children g ↔ ∃ z ∈ g, x = z + 2 ∨ x = 2 * z := by
  simp [children]

/-- Proof device: `w y = bitlen y + popcount y`, computed from the binary digits of `y`. -/
def w (y : ℕ) : ℕ := (Nat.digits 2 y).length + (Nat.digits 2 y).sum

/-- `w 0 = 0`. -/
theorem w_zero : w 0 = 0 := by simp [w]

/-- Doubling a positive number appends a `0` bit: `w (2y) = w y + 1`. -/
theorem w_two_mul {y : ℕ} (hy : 0 < y) : w (2 * y) = w y + 1 := by
  have h2 : 0 < 2 * y := by omega
  unfold w
  rw [Nat.digits_def' (by norm_num) h2]
  simp only [List.length_cons, List.sum_cons, Nat.mul_mod_right, Nat.mul_div_cancel_left _ two_pos]
  ring

/-- `w (2y + 1) = w y + 2`. -/
theorem w_two_mul_add_one (y : ℕ) : w (2 * y + 1) = w y + 2 := by
  unfold w
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * y + 1) % 2 = 1 := by omega
  have h2 : (2 * y + 1) / 2 = y := by omega
  simp only [List.length_cons, List.sum_cons, h1, h2]
  ring

/-- `w y ≤ y + 1`. -/
theorem w_le (y : ℕ) : w y ≤ y + 1 := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    obtain ⟨z, rfl | rfl⟩ := Nat.even_or_odd' y
    · rcases Nat.eq_zero_or_pos z with rfl | hz
      · simp [w_zero]
      · rw [w_two_mul hz]; have := ih z (by omega); omega
    · rw [w_two_mul_add_one]
      rcases Nat.eq_zero_or_pos z with rfl | hz
      · simp [w_zero]
      · have := ih z (by omega); omega

/-- Every positive `y` has `2 ≤ w y`. -/
theorem two_le_w {y : ℕ} (hy : 0 < y) : 2 ≤ w y := by
  obtain ⟨z, rfl | rfl⟩ := Nat.even_or_odd' y
  · rw [w_two_mul (by omega)]
    have : 1 ≤ w z := by
      obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' z
      · rw [w_two_mul (by omega)]; omega
      · rw [w_two_mul_add_one]; omega
    omega
  · rw [w_two_mul_add_one]; omega

/-- For positive `y`, `w (y + 1) ≤ w y + 1`. -/
theorem w_succ_le {y : ℕ} (hy : 0 < y) : w (y + 1) ≤ w y + 1 := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    obtain ⟨z, rfl | rfl⟩ := Nat.even_or_odd' y
    · rw [w_two_mul (by omega), w_two_mul_add_one]
    · have h : 2 * z + 1 + 1 = 2 * (z + 1) := by ring
      rw [h, w_two_mul (by omega), w_two_mul_add_one]
      rcases Nat.eq_zero_or_pos z with rfl | hz
      · norm_num [w]
      · have := ih z (by omega) hz; omega

/-- `y < 2 ^ w y`, so each level set of `w` is finite. -/
theorem lt_two_pow_w (y : ℕ) : y < 2 ^ w y := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    obtain ⟨z, rfl | rfl⟩ := Nat.even_or_odd' y
    · rcases Nat.eq_zero_or_pos z with rfl | hz
      · simp [w_zero]
      · rw [w_two_mul hz, pow_succ]; have := ih z (by omega); omega
    · rw [w_two_mul_add_one, pow_add]
      rcases Nat.eq_zero_or_pos z with rfl | hz
      · simp [w_zero]
      · have := ih z (by omega); omega


/-- Proof device: the predicted set of generation `k` (0-based), namely
`{2k+1} ∪ {2y : y > 0, w y = k + 2}`. -/
def T (k x : ℕ) : Prop := x = 2 * k + 1 ∨ ∃ y, 0 < y ∧ w y = k + 2 ∧ x = 2 * y

/-- The predicted generations are pairwise disjoint. -/
theorem T_unique {i j x : ℕ} (hi : T i x) (hj : T j x) : i = j := by
  rcases hi with rfl | ⟨y, hy, hwy, rfl⟩ <;> rcases hj with h | ⟨y', hy', hwy', h⟩
  · omega
  · omega
  · omega
  · have : y = y' := by omega
    subst this; omega

/-- A child of a predicted generation-`k` element lies in a predicted generation `≤ k + 1`. -/
theorem T_of_child {k z x : ℕ} (hz : T k z) (hx : x = z + 2 ∨ x = 2 * z) :
    ∃ j ≤ k + 1, T j x := by
  rcases hz with rfl | ⟨y, hy, hwy, rfl⟩
  · rcases hx with rfl | rfl
    · exact ⟨k + 1, le_rfl, Or.inl (by ring)⟩
    · have h1 := w_two_mul_add_one k
      have h2 := w_le k
      have h3 := two_le_w (y := 2 * k + 1) (by omega)
      exact ⟨w (2 * k + 1) - 2, by omega, Or.inr ⟨2 * k + 1, by omega, by omega, rfl⟩⟩
  · rcases hx with rfl | rfl
    · have h1 := w_succ_le hy
      have h3 := two_le_w (y := y + 1) (by omega)
      exact ⟨w (y + 1) - 2, by omega, Or.inr ⟨y + 1, by omega, by omega, by ring⟩⟩
    · exact ⟨k + 1, le_rfl, Or.inr ⟨2 * y, by omega, by rw [w_two_mul hy, hwy], rfl⟩⟩

/-- Every predicted generation-`(k+1)` element is a child of a predicted generation-`k` element. -/
theorem exists_parent {k x : ℕ} (hx : T (k + 1) x) : ∃ z, T k z ∧ (x = z + 2 ∨ x = 2 * z) := by
  rcases hx with rfl | ⟨y, hy, hwy, rfl⟩
  · exact ⟨2 * k + 1, Or.inl rfl, Or.inl (by ring)⟩
  · obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' y
    · have hu : 0 < u := by omega
      rw [w_two_mul hu] at hwy
      exact ⟨2 * u, Or.inr ⟨u, hu, by omega, rfl⟩, Or.inr rfl⟩
    · rw [w_two_mul_add_one] at hwy
      rcases Nat.eq_zero_or_pos u with rfl | hu
      · simp [w_zero] at hwy
      · have h := w_two_mul hu
        exact ⟨2 * (2 * u), Or.inr ⟨2 * u, by omega, by omega, rfl⟩, Or.inl (by ring)⟩

/-- The prediction holds for generation `0`. -/
theorem mem_gen_zero_iff (x : ℕ) : x ∈ gen 0 ↔ T 0 x := by
  simp only [gen, genPair, List.mem_cons, List.not_mem_nil, or_false, T]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨1, by norm_num, by norm_num [w], rfl⟩
  · rintro (rfl | ⟨y, hy, hwy, rfl⟩)
    · exact Or.inl rfl
    · right
      rcases Nat.lt_or_ge y 2 with h | h
      · omega
      · obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' y
        · have := two_le_w (y := u) (by omega); rw [w_two_mul (by omega)] at hwy; omega
        · have := two_le_w (y := u) (by omega); rw [w_two_mul_add_one] at hwy; omega

/-- **Set description of the generations.** `x ∈ g(k+1)` iff `x = 2k+1` or
`x = 2y` with `y > 0` and `bitlen y + popcount y = k + 2`. -/
theorem mem_gen_iff (k x : ℕ) : x ∈ gen k ↔ T k x := by
  induction k using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    rcases k with _ | k
    · exact mem_gen_zero_iff x
    have hpre : ∀ y, y ∈ prefixS (k + 1) ↔ ∃ j ≤ k, T j y := by
      intro y
      rw [mem_prefixS]
      constructor
      · rintro ⟨j, hj, hy⟩
        exact ⟨j, by omega, (ih j (by omega) y).1 hy⟩
      · rintro ⟨j, hj, hy⟩
        exact ⟨j, by omega, (ih j (by omega) y).2 hy⟩
    rw [gen_succ, mem_emitNew, mem_children, hpre]
    constructor
    · rintro ⟨⟨z, hz, hxz⟩, hnot⟩
      obtain ⟨j, hj, hTj⟩ := T_of_child ((ih k (by omega) z).1 hz) hxz
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact absurd ⟨j, by omega, hTj⟩ hnot
      · have : j = k + 1 := by omega
        subst this; exact hTj
    · intro hx
      obtain ⟨z, hz, hxz⟩ := exists_parent hx
      refine ⟨⟨z, (ih k (by omega) z).2 hz, hxz⟩, ?_⟩
      rintro ⟨j, hj, hTj⟩
      have := T_unique hx hTj
      omega


/-- A predicted generation-`j` element does not occur in the first `N ≤ j` generations. -/
theorem notMem_prefixS_of_T {N j x : ℕ} (hx : T j x) (hN : N ≤ j) : x ∉ prefixS N := by
  rw [mem_prefixS]
  rintro ⟨i, hi, hxi⟩
  have := T_unique ((mem_gen_iff i x).1 hxi) hx
  omega

/-- **First element.** Generation `g(k+1)` begins with the odd number `2k+1`. -/
theorem gen_eq_cons (k : ℕ) : ∃ rest, gen k = (2 * k + 1) :: rest := by
  induction k with
  | zero => exact ⟨[2], rfl⟩
  | succ k ih =>
    obtain ⟨rest, hrest⟩ := ih
    have hnot : 2 * (k + 1) + 1 ∉ prefixS (k + 1) :=
      notMem_prefixS_of_T (j := k + 1) (Or.inl rfl) le_rfl
    have hch : children (gen k) = (2 * (k + 1) + 1) :: (2 * (2 * k + 1) :: children rest) := by
      rw [hrest]; simp only [children, List.flatMap_cons, List.cons_append, List.nil_append]
      ring_nf
    rw [gen_succ, hch, emitNew_cons_of_notMem _ _ _ hnot]
    exact ⟨_, rfl⟩

/-- Proof device: the positive `y` with `w y = m`, as a `Finset`. -/
def B (m : ℕ) : Finset ℕ := (Finset.range (2 ^ m)).filter fun y => 0 < y ∧ w y = m

/-- Membership in `B m`. -/
theorem mem_B {m y : ℕ} : y ∈ B m ↔ 0 < y ∧ w y = m := by
  simp only [B, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨hy, rfl⟩; exact ⟨lt_two_pow_w y, hy, rfl⟩

/-- The underlying set of generation `k`. -/
theorem gen_toFinset (k : ℕ) :
    (gen k).toFinset = insert (2 * k + 1) ((B (k + 2)).image (2 * ·)) := by
  ext x
  rw [List.mem_toFinset, mem_gen_iff, Finset.mem_insert, Finset.mem_image]
  simp only [T, mem_B]
  constructor
  · rintro (h | ⟨y, hy, hw, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, ⟨hy, hw⟩, rfl⟩
  · rintro (h | ⟨y, ⟨hy, hw⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, hw, rfl⟩

/-- Each generation has no repeated values. -/
theorem nodup_gen (k : ℕ) : (gen k).Nodup := by
  rcases k with _ | k
  · decide
  · rw [gen_succ]; exact nodup_emitNew _ _

/-- The size of generation `k` is `|B (k + 2)| + 1`. -/
theorem length_gen_eq (k : ℕ) : (gen k).length = (B (k + 2)).card + 1 := by
  rw [← List.toFinset_card_of_nodup (nodup_gen k), gen_toFinset, Finset.card_insert_of_notMem,
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp only [Finset.mem_image, not_exists, not_and]
  intro y _ h; omega

/-- For `m > 0`, `B (m + 2)` splits by parity into `2·B (m + 1)` and `2·B m + 1`. -/
theorem B_add_two {m : ℕ} (hm : 0 < m) :
    B (m + 2) = (B (m + 1)).image (2 * ·) ∪ (B m).image (fun z => 2 * z + 1) := by
  ext y
  simp only [Finset.mem_union, Finset.mem_image, mem_B]
  constructor
  · rintro ⟨hy, hw⟩
    obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' y
    · rw [w_two_mul (by omega)] at hw
      exact Or.inl ⟨u, ⟨by omega, by omega⟩, rfl⟩
    · rw [w_two_mul_add_one] at hw
      rcases Nat.eq_zero_or_pos u with rfl | hu
      · simp only [w_zero] at hw; omega
      · exact Or.inr ⟨u, ⟨hu, by omega⟩, rfl⟩
  · rintro (⟨u, ⟨hu, hw⟩, rfl⟩ | ⟨u, ⟨hu, hw⟩, rfl⟩)
    · exact ⟨by omega, by rw [w_two_mul hu, hw]⟩
    · exact ⟨by omega, by rw [w_two_mul_add_one, hw]⟩

/-- `|B (m + 1)| = F(m)`. -/
theorem card_B_succ (m : ℕ) : (B (m + 1)).card = Nat.fib m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · show (B 1).card = 0
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [mem_B] at hy
      have := two_le_w hy.1; omega
    · show (B 2).card = 1
      rw [Finset.card_eq_one]
      refine ⟨1, ?_⟩
      ext y
      rw [mem_B, Finset.mem_singleton]
      constructor
      · rintro ⟨hy, hw⟩
        obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' y
        · have := two_le_w (y := u) (by omega); rw [w_two_mul (by omega)] at hw; omega
        · rcases Nat.eq_zero_or_pos u with rfl | hu
          · rfl
          · have := two_le_w hu; rw [w_two_mul_add_one] at hw; omega
      · rintro rfl; exact ⟨by norm_num, by norm_num [w]⟩
    · rw [show m + 2 + 1 = (m + 1) + 2 by ring, B_add_two (by omega), Finset.card_union_of_disjoint,
        Finset.card_image_of_injective _ (fun a b h => by simpa using h),
        Finset.card_image_of_injective _ (fun a b h => by simpa using h),
        ih (m + 1) (by omega), ih m (by omega), Nat.fib_add_two]
      · ring
      · rw [Finset.disjoint_left]
        simp only [Finset.mem_image, not_exists, not_and]
        rintro _ ⟨u, _, rfl⟩ v _ h; omega

/-- **Generation sizes.** `|g(k+1)| = F(k+1) + 1`. -/
theorem length_gen (k : ℕ) : (gen k).length = Nat.fib (k + 1) + 1 := by
  rw [length_gen_eq, card_B_succ]


/-- Closed form (Tom Edgar, 2015): `a(n) = n - 1 + F(n+1)`, valid for all `n` here. -/
theorem a_eq (n : ℕ) : a n = (n : ℤ) - 1 + Nat.fib (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [a]
    | 1 => simp [a]
    | 2 => norm_num [a, Nat.fib_add_two]
    | 3 => norm_num [a, Nat.fib_add_two]
    | n + 4 =>
      rw [a, ih (n + 3) (by omega), ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)]
      have h1 := Nat.fib_add_two (n := n + 3)
      have h2 := Nat.fib_add_two (n := n + 2)
      have h3 := Nat.fib_add_two (n := n + 1)
      have h4 := Nat.fib_add_two (n := n)
      push_cast [h1, h2, h3, h4]
      ring

/-- The first `k` generations have total length `k + F(k+2) - 1`. -/
theorem length_prefixS (k : ℕ) : (prefixS k).length + 1 = k + Nat.fib (k + 2) := by
  induction k with
  | zero => simp [prefixS]
  | succ k ih =>
    rw [prefixS_succ, List.length_append, length_gen]
    have hfib : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    omega

/-- Prefixes of the concatenation are nested: the first `k` generations are a prefix of
the first `N ≥ k` generations. -/
theorem prefixS_eq_append {k N : ℕ} (h : k ≤ N) : ∃ R, prefixS N = prefixS k ++ R := by
  induction N, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ N _ ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨R ++ gen N, by rw [prefixS_succ, hR, List.append_assoc]⟩

/-- Position of `2k+1` (Edgar form): in every prefix of `N > k` generations, `2k+1` occurs
and its 0-based index is `k + F(k+2) - 1`. -/
theorem idxOf_prefixS (k N : ℕ) (h : k < N) :
    2 * k + 1 ∈ prefixS N ∧ (prefixS N).idxOf (2 * k + 1) + 1 = k + Nat.fib (k + 2) := by
  obtain ⟨R, hR⟩ := prefixS_eq_append (Nat.succ_le_of_lt h)
  obtain ⟨rest, hrest⟩ := gen_eq_cons k
  have hnot : 2 * k + 1 ∉ prefixS k := notMem_prefixS_of_T (j := k) (Or.inl rfl) le_rfl
  have hN : prefixS N = prefixS k ++ ((2 * k + 1) :: (rest ++ R)) := by
    rw [hR, prefixS_succ, hrest]; simp
  rw [hN, List.idxOf_append_of_notMem hnot, List.idxOf_cons_self, ← length_prefixS]
  simp

/-- `w` agrees with binary length plus binary weight on small values. -/
example : w 5 = 5 ∧ w 12 = 6 := by norm_num [w]

/-! ## The conjecture -/

/-- **Kimberling's conjecture (A232896 and A232895, Clark Kimberling, Dec 2013).**

For `1 ≤ n ≤ N`, the odd number `2n - 1` occurs among the first `N` generations of `S`,
and its 1-based position there (hence in `S`) equals `a(n)`, the term of A232896 defined by
the recurrence.  The guard `1 ≤ n` keeps `2 * n - 1` off truncated subtraction. -/
theorem a232896_position (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    2 * n - 1 ∈ prefixS N ∧ (((prefixS N).idxOf (2 * n - 1) + 1 : ℕ) : ℤ) = a n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  obtain ⟨hmem, hidx⟩ := idxOf_prefixS k N (by omega)
  rw [h2, a_eq]
  refine ⟨hmem, ?_⟩
  rw [hidx]
  push_cast
  ring

/-- The conjecture in Tom Edgar's closed form: for `1 ≤ n ≤ N`, the 1-based position of
`2n - 1` in `S` is `n - 1 + F(n+1)`. -/
theorem a232896_position_fib (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    2 * n - 1 ∈ prefixS N ∧ (prefixS N).idxOf (2 * n - 1) + 1 = n - 1 + Nat.fib (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [h2, show k + 1 - 1 + Nat.fib (k + 1 + 1) = k + Nat.fib (k + 2) by simp]
  exact idxOf_prefixS k N (by omega)

/-- Non-vacuity: the hypotheses of `a232896_position` are jointly satisfiable. -/
example : 2 * 3 - 1 ∈ prefixS 4 ∧ (((prefixS 4).idxOf (2 * 3 - 1) + 1 : ℕ) : ℤ) = a 3 :=
  a232896_position 3 4 (by norm_num) (by norm_num)

end Candidates.A232896BuiltGenerationsObtained
