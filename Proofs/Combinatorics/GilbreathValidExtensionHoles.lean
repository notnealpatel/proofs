/-
# Holes in valid-extension sets of finite Gilbreath sequences: maximum width

## Source

Leila Muney, *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*,
arXiv:2606.23721 (v2), Section "The doubling sequence and the maximum-width
conjecture" (Theorem `thm:doubling`, Conjecture `conj:max`), restated as
Open Question (1); the extension criterion is Prop. `prop:criterion`.

Setup (verbatim, 1-indexed): the difference triangle is `s_a^0 := s_a`,
`s_a^b := |s_{a+1}^{b-1} - s_a^{b-1}|`; `S` is *Gilbreath* if `s_1^b = 1`
for every `1 ≤ b ≤ n - 1`; `K_S := {k ∈ ℤ : (s_1, …, s_n, k) is Gilbreath}`;
`𝒢_n` is the set of strictly increasing Gilbreath sequences of length `n`
with `(s_1, s_2) = (2, 3)`; `U_n = (2, 3, 5, 9, 17, …, 2^{n-1} + 1)`.

Conjecture (Maximum width, verbatim): "For every `n ≥ 2`,
`max_{S ∈ 𝒢_n} |K_S| = 2^{n-1} + 1`, uniquely achieved by `U_n`."

Status: open in the paper (verified there by exhaustive computation for
`n ≤ 10`); the attainment half `|K_{U_n}| = 2^{n-1} + 1` is the paper's
Theorem `thm:doubling`. Recorded 2026-10-21. This file proves the full
conjecture (`conj_max`) with no `sorry`.

## Formalization

Sequences are `s : ℕ → ℤ`, 0-indexed, of which only `s 0, …, s (n-1)` matter
for length `n`; appending `k` is `Function.update s n k`.

Proof outline (upper bound and uniqueness are new here): the right
anti-diagonal entries `tri s i a` with `i + a = n - 1`, `1 ≤ i`, satisfy
`tri s i a ≤ 2 ^ a` (`antidiag_le`, induction on the length, using that the
apex is `1`); applied to the extended sequence this gives `|k - s (n-1)| ≤
2^{n-1}`, and parity (`even_tri`) halves the candidates. Equality forces the
gap sequence to double (`gap_eq_of_tight`).
-/
import Mathlib

set_option autoImplicit false

namespace GilbreathValidExtensionHoles

/-- The difference triangle of `s` (0-indexed): `tri s 0 a = s a` and
`tri s (b+1) a = |tri s b (a+1) - tri s b a|`; `tri s b a` is the paper's
`s_{a+1}^b`. -/
def tri (s : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, a => s a
  | b + 1, a => |tri s b (a + 1) - tri s b a|

/-- `s 0, …, s (n-1)` is Gilbreath: the leftmost entry of every row
`1 ≤ b ≤ n - 1` of the difference triangle equals `1`. -/
def IsGilbreath (n : ℕ) (s : ℕ → ℤ) : Prop :=
  ∀ b, 1 ≤ b → b < n → tri s b 0 = 1

/-- The valid-extension set `K_S` of the length-`n` sequence
`s 0, …, s (n-1)`: integers `k` such that appending `k` keeps it Gilbreath. -/
def validExt (n : ℕ) (s : ℕ → ℤ) : Set ℤ :=
  {k | IsGilbreath (n + 1) (Function.update s n k)}

/-- The doubling sequence `U = (2, 3, 5, 9, 17, …)`, `U i = 2 ^ i + 1` for
`i ≥ 1`; its length-`n` prefix is the paper's `U_n`. -/
def U (i : ℕ) : ℤ := if i = 0 then 2 else 2 ^ i + 1

/-- Membership of the length-`n` prefix of `s` in the paper's family `𝒢_n`:
Gilbreath, starting `(2, 3)`, strictly increasing. -/
def InG (n : ℕ) (s : ℕ → ℤ) : Prop :=
  IsGilbreath n s ∧ s 0 = 2 ∧ s 1 = 3 ∧ ∀ i, i + 1 < n → s i < s (i + 1)

/-! ### Ground truth on the paper's example `(2, 3, 5, 9, 15)` -/

/-- The paper's Example `ex:notation` sequence `(2,3,5,9,15)`. -/
def exS : ℕ → ℤ := fun i => [2, 3, 5, 9, 15].getD i 0

/-- Right anti-diagonal of `(2,3,5,9,15)` is `(6,2,0,1)`. -/
example : (tri exS 1 3, tri exS 2 2, tri exS 3 1, tri exS 4 0) = (6, 2, 0, 1) := by
  decide

example : IsGilbreath 5 exS := by
  intro b h1 h2
  interval_cases b <;> decide

/-- `15` is a hole: `K_{(2,3,5,9,15)} = {5,7,9,11,13,17,19,21,23,25}`. -/
example : (15 : ℤ) ∉ validExt 5 exS ∧ (13 : ℤ) ∈ validExt 5 exS ∧
    (25 : ℤ) ∈ validExt 5 exS ∧ (27 : ℤ) ∉ validExt 5 exS := by
  refine ⟨fun h => ?_, ?_, ?_, fun h => ?_⟩
  · have h4 := h 5 (by norm_num) (by norm_num)
    revert h4; decide
  · intro b h1 h2; interval_cases b <;> decide
  · intro b h1 h2; interval_cases b <;> decide
  · have h4 := h 5 (by norm_num) (by norm_num)
    revert h4; decide

example : U 0 = 2 ∧ U 1 = 3 ∧ U 2 = 5 ∧ U 3 = 9 ∧ U 4 = 17 := by decide

/-! ### Basic lemmas -/

/-- Rows below the top are nonnegative. -/
theorem tri_succ_nonneg (s : ℕ → ℤ) (b a : ℕ) : 0 ≤ tri s (b + 1) a := abs_nonneg _

/-- Locality: appending at position `n` does not change entries with `a + b < n`. -/
theorem tri_update_of_lt (s : ℕ → ℤ) (n : ℕ) (k : ℤ) :
    ∀ b a, a + b < n → tri (Function.update s n k) b a = tri s b a := by
  intro b
  induction b with
  | zero =>
    intro a ha
    simp only [tri]
    exact Function.update_of_ne (show a ≠ n by omega) k s
  | succ b ih =>
    intro a ha
    simp only [tri]
    rw [ih (a + 1) (by omega), ih a (by omega)]

/-- Gilbreath is inherited by prefixes. -/
theorem IsGilbreath.mono {n m : ℕ} {s : ℕ → ℤ} (h : IsGilbreath m s) (hnm : n ≤ m) :
    IsGilbreath n s := fun b hb1 hb2 => h b hb1 (by omega)

/-- **Anti-diagonal bound.** For a Gilbreath sequence of length `m + 1`, the right
anti-diagonal entry in row `i ≥ 1` (column `a = m - i`) is at most `2 ^ a`. -/
theorem antidiag_le {s : ℕ → ℤ} :
    ∀ m, IsGilbreath (m + 1) s → ∀ i a, 1 ≤ i → i + a = m → tri s i a ≤ 2 ^ a := by
  intro m
  induction m with
  | zero => intro _ i a hi hia; omega
  | succ m ihm =>
    intro hG
    have hprev := ihm (hG.mono (by omega))
    intro i a
    induction a generalizing i with
    | zero =>
      intro hi hia
      rw [hG i hi (by omega)]
      norm_num
    | succ a iha =>
      intro hi hia
      have h1 : tri s (i + 1) a ≤ 2 ^ a := iha (i + 1) (by omega) (by omega)
      have h2 : tri s i a ≤ 2 ^ a := hprev i a hi (by omega)
      have h3 : tri s i (a + 1) - tri s i a ≤ tri s (i + 1) a := le_abs_self _
      rw [pow_succ]
      linarith

/-- **Parity.** In a Gilbreath sequence of length `m`, entries strictly inside the
triangle (row `b ≥ 1`, column `a + 1 ≥ 1`, `a + b + 2 ≤ m`) are even. -/
theorem even_tri {m : ℕ} {s : ℕ → ℤ} (hG : IsGilbreath m s) :
    ∀ a b, 1 ≤ b → a + b + 2 ≤ m → Even (tri s b (a + 1)) := by
  intro a
  induction a with
  | zero =>
    intro b hb hm
    have h1 : tri s (b + 1) 0 = 1 := hG (b + 1) (by omega) (by omega)
    have h0 : tri s b 0 = 1 := hG b hb (by omega)
    simp only [tri] at h1
    rw [h0] at h1
    rcases abs_eq (zero_le_one' ℤ) |>.mp h1 with h | h
    · exact ⟨1, by linarith⟩
    · exact ⟨0, by linarith⟩
  | succ a ih =>
    intro b hb hm
    have hA : Even (tri s (b + 1) (a + 1)) := ih (b + 1) (by omega) (by omega)
    have hB : Even (tri s b (a + 1)) := ih b hb (by omega)
    simp only [tri] at hA
    rw [even_abs] at hA
    have := hA.add hB
    simpa using this


/-- Entries of rows `b ≥ 1` are nonnegative. -/
theorem tri_nonneg (s : ℕ → ℤ) {b : ℕ} (hb : 1 ≤ b) (a : ℕ) : 0 ≤ tri s b a := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  exact tri_succ_nonneg s b' a

/-- The new row-1 entry created by appending `k` after `s m` is `|k - s m|`. -/
theorem tri_update_one (s : ℕ → ℤ) (m : ℕ) (k : ℤ) :
    tri (Function.update s (m + 1) k) 1 m = |k - s m| := by
  simp only [tri, Function.update_self]
  rw [Function.update_of_ne (show m ≠ m + 1 by omega)]

/-! ### Upper bound -/

/-- The parity-compatible candidate interval of radius `2 ^ (p+1)` around `c`. -/
noncomputable def cand (c : ℤ) (p : ℕ) : Finset ℤ :=
  (Finset.Icc (-(2 : ℤ) ^ p) (2 ^ p)).image (fun j => c + 2 * j)

/-- The candidate interval has `2 ^ (p+1) + 1` elements. -/
theorem card_cand (c : ℤ) (p : ℕ) : (cand c p).card = 2 ^ (p + 1) + 1 := by
  unfold cand
  rw [Finset.card_image_of_injective _ (fun x y hxy => by simpa using hxy), Int.card_Icc]
  have h : (2 : ℤ) ^ p + 1 - -2 ^ p = ((2 ^ (p + 1) + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [h, Int.toNat_natCast]

/-- A valid extension `k` of a length-`m+1` sequence satisfies `|k - s m| ≤ 2 ^ m`. -/
theorem abs_sub_le_of_mem {m : ℕ} {s : ℕ → ℤ} {k : ℤ} (hk : k ∈ validExt (m + 1) s) :
    |k - s m| ≤ 2 ^ m := by
  have h := antidiag_le (m + 1) hk 1 m le_rfl (by omega)
  rwa [tri_update_one] at h

/-- For length `p + 2 ≥ 2`, every valid extension lies in the candidate interval. -/
theorem mem_cand_of_mem {p : ℕ} {s : ℕ → ℤ} {k : ℤ} (hk : k ∈ validExt (p + 2) s) :
    k ∈ cand (s (p + 1)) p := by
  have hle := abs_sub_le_of_mem hk
  have hev : Even (tri (Function.update s (p + 2) k) 1 (p + 1)) :=
    even_tri (m := p + 3) hk p 1 le_rfl (by omega)
  rw [tri_update_one, even_abs] at hev
  obtain ⟨r, hr⟩ := hev
  rw [hr] at hle
  obtain ⟨hl, hu⟩ := abs_le.mp hle
  rw [pow_succ] at hl hu
  simp only [cand, Finset.mem_image, Finset.mem_Icc]
  exact ⟨r, ⟨by linarith, by linarith⟩, by linarith⟩

/-- **Upper bound (conjecture, part 1).** For every `n ≥ 1` and every sequence `S`
of length `n`, the valid-extension set `K_S` is finite and `|K_S| ≤ 2^{n-1} + 1`.
(No Gilbreath, monotonicity or `(2,3)` hypothesis is needed: if `S` is not
Gilbreath then `K_S = ∅`.) -/
theorem validExt_finite_and_ncard_le (n : ℕ) (hn : 1 ≤ n) (s : ℕ → ℤ) :
    (validExt n s).Finite ∧ (validExt n s).ncard ≤ 2 ^ (n - 1) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hsub : validExt (0 + 1) s ⊆ (({s 0 - 1, s 0 + 1} : Finset ℤ) : Set ℤ) := by
      intro k hk
      have h1 : tri (Function.update s (0 + 1) k) 1 0 = 1 := hk 1 le_rfl (by omega)
      rw [tri_update_one] at h1
      rcases abs_eq (zero_le_one' ℤ) |>.mp h1 with h | h
      · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        right; linarith
      · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        left; linarith
    refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
    calc (validExt (0 + 1) s).ncard
        ≤ (({s 0 - 1, s 0 + 1} : Finset ℤ) : Set ℤ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({s 0 - 1, s 0 + 1} : Finset ℤ).card := Set.ncard_coe_finset _
      _ ≤ 2 := Finset.card_le_two
      _ = 2 ^ (0 + 1 - 1) + 1 := by norm_num
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    have hsub : validExt (p + 1 + 1) s ⊆ ((cand (s (p + 1)) p : Finset ℤ) : Set ℤ) :=
      fun k hk => mem_cand_of_mem hk
    refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
    calc (validExt (p + 1 + 1) s).ncard
        ≤ ((cand (s (p + 1)) p : Finset ℤ) : Set ℤ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (cand (s (p + 1)) p).card := Set.ncard_coe_finset _
      _ = 2 ^ (p + 1 + 1 - 1) + 1 := by rw [card_cand]; rfl


/-! ### The doubling sequence -/

/-- Consecutive gaps of `U` double: `U (a+1) - U a = 2 ^ a`. -/
theorem U_succ_sub (a : ℕ) : U (a + 1) - U a = 2 ^ a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp [U]
  · simp only [U, Nat.add_one_ne_zero, if_false, (Nat.pos_iff_ne_zero.mp ha), pow_succ]
    ring

/-- Every row `b ≥ 1` of the triangle of `U` is `(1, 2, 4, 8, …)`. -/
theorem tri_U (b : ℕ) (hb : 1 ≤ b) (a : ℕ) : tri U b a = 2 ^ a := by
  induction b, hb using Nat.le_induction generalizing a with
  | base =>
    show |U (a + 1) - U a| = 2 ^ a
    rw [U_succ_sub, abs_of_pos (by positivity)]
  | succ b hb ih =>
    show |tri U b (a + 1) - tri U b a| = 2 ^ a
    have hpos : (0 : ℤ) < 2 ^ a := by positivity
    have hd : (2 : ℤ) ^ (a + 1) - 2 ^ a = 2 ^ a := by rw [pow_succ]; ring
    rw [ih, ih, hd, abs_of_pos hpos]

/-- The doubling sequence lies in `𝒢_n` for every `n`. -/
theorem InG_U (n : ℕ) : InG n U := by
  refine ⟨fun b hb _ => by rw [tri_U b hb]; norm_num, by decide, by decide, fun i _ => ?_⟩
  have h := U_succ_sub i
  have : (0 : ℤ) < 2 ^ i := by positivity
  linarith

/-- Every point `U (p+1) + 2 j` with `|j| ≤ 2 ^ p` is a valid extension of `U_{p+2}`. -/
theorem mem_validExt_U (p : ℕ) (j : ℤ) (hj : j ∈ Finset.Icc (-(2 : ℤ) ^ p) (2 ^ p)) :
    U (p + 1) + 2 * j ∈ validExt (p + 2) U := by
  rw [Finset.mem_Icc] at hj
  set k := U (p + 1) + 2 * j with hk
  set t := Function.update U (p + 2) k with ht
  -- the new right edge stays even and below the doubling bound
  have hedge : ∀ i, 1 ≤ i → ∀ a, 1 ≤ a → i + a = p + 2 →
      Even (tri t i a) ∧ tri t i a ≤ 2 ^ a := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base =>
      intro a _ ha
      obtain rfl : a = p + 1 := by omega
      rw [ht, tri_update_one, hk, add_sub_cancel_left, even_abs, abs_mul, pow_succ]
      refine ⟨⟨j, two_mul j⟩, ?_⟩
      have : |j| ≤ 2 ^ p := abs_le.mpr ⟨by linarith, hj.2⟩
      rw [abs_two]; linarith
    | succ i hi ih =>
      intro a ha hia
      obtain ⟨hev, hle⟩ := ih (a + 1) (by omega) (by omega)
      have hloc : tri t i a = 2 ^ a := by
        rw [ht, tri_update_of_lt U (p + 2) k i a (by omega), tri_U i hi]
      have hnn : 0 ≤ tri t i (a + 1) := tri_nonneg t hi (a + 1)
      have hstep : tri t (i + 1) a = |tri t i (a + 1) - tri t i a| := rfl
      rw [hstep, hloc, even_abs]
      have h2a : Even ((2 : ℤ) ^ a) := (Int.even_pow).mpr ⟨even_two, by omega⟩
      refine ⟨hev.sub h2a, abs_le.mpr ⟨?_, ?_⟩⟩
      · linarith
      · rw [pow_succ] at hle; linarith
  intro b hb1 hb2
  rcases Nat.lt_or_ge b (p + 2) with hb | hb
  · rw [tri_update_of_lt U (p + 2) k b 0 (by omega), tri_U b hb1]
    norm_num
  · obtain rfl : b = p + 2 := by omega
    obtain ⟨⟨r, hr⟩, hle⟩ := hedge (p + 1) (by omega) 1 le_rfl (by omega)
    have hnn : 0 ≤ tri t (p + 1) 1 := tri_nonneg t (by omega) 1
    have hloc : tri t (p + 1) 0 = 1 := by
      rw [ht, tri_update_of_lt U (p + 2) k (p + 1) 0 (by omega), tri_U (p + 1) (by omega)]
      norm_num
    have hstep : tri t (p + 2) 0 = |tri t (p + 1) 1 - tri t (p + 1) 0| := rfl
    rw [hstep, hloc]
    have hcases : tri t (p + 1) 1 = 0 ∨ tri t (p + 1) 1 = 2 := by
      rw [pow_one] at hle; omega
    rcases hcases with h | h <;> rw [h] <;> norm_num

/-- **Attainment (paper's Theorem `thm:doubling`).** For every `n ≥ 2`,
`|K_{U_n}| = 2^{n-1} + 1`. -/
theorem ncard_validExt_U (n : ℕ) (hn : 2 ≤ n) : (validExt n U).ncard = 2 ^ (n - 1) + 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
  obtain ⟨hfin, hle⟩ := validExt_finite_and_ncard_le (p + 2) (by omega) U
  have hsub : ((cand (U (p + 1)) p : Finset ℤ) : Set ℤ) ⊆ validExt (p + 2) U := by
    intro k hk
    simp only [cand, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    exact mem_validExt_U p j hj
  have hge := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, card_cand] at hge
  exact le_antisymm hle (by simpa using hge)

/-! ### Uniqueness -/

/-- **Tightness propagates.** If a Gilbreath sequence of length `m + 2` has last gap
`|s (m+1) - s m| = 2 ^ m`, then every gap is extremal: `|s (a+1) - s a| = 2 ^ a`
for `a ≤ m`. -/
theorem gap_eq_of_tight {t : ℕ → ℤ} :
    ∀ m, IsGilbreath (m + 2) t → tri t 1 m = 2 ^ m → ∀ a ≤ m, tri t 1 a = 2 ^ a := by
  intro m
  induction m with
  | zero => intro _ h a ha; obtain rfl : a = 0 := by omega
            exact h
  | succ m ih =>
    intro hG h
    have h2 : tri t 2 m ≤ 2 ^ m := antidiag_le (m + 2) hG 2 m (by omega) (by omega)
    have h1 : tri t 1 m ≤ 2 ^ m :=
      antidiag_le (m + 1) (hG.mono (by omega)) 1 m le_rfl (by omega)
    have h3 : tri t 2 m = |tri t 1 (m + 1) - tri t 1 m| := rfl
    have h4 : tri t 1 (m + 1) - tri t 1 m ≤ tri t 2 m := h3 ▸ le_abs_self _
    have hm : tri t 1 m = 2 ^ m := by
      rw [h, pow_succ] at h4
      linarith
    intro a ha
    rcases Nat.lt_or_ge a (m + 1) with ha' | ha'
    · exact ih (hG.mono (by omega)) hm a (by omega)
    · obtain rfl : a = m + 1 := by omega
      exact h

/-- **Uniqueness (conjecture, part 3).** If `S ∈ 𝒢_n` (`n ≥ 2`) has
`|K_S| = 2^{n-1} + 1`, then `S = U_n`. -/
theorem eq_U_of_ncard_eq (n : ℕ) (hn : 2 ≤ n) (s : ℕ → ℤ) (hs : InG n s)
    (heq : (validExt n s).ncard = 2 ^ (n - 1) + 1) : ∀ i < n, s i = U i := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
  obtain ⟨_, hs0, _, hmono⟩ := hs
  rw [show p + 2 - 1 = p + 1 by omega] at heq
  have hsub : validExt (p + 2) s ⊆ ((cand (s (p + 1)) p : Finset ℤ) : Set ℤ) :=
    fun k hk => mem_cand_of_mem hk
  have hK : validExt (p + 2) s = ((cand (s (p + 1)) p : Finset ℤ) : Set ℤ) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, card_cand, heq]
  -- the far endpoint `s (p+1) + 2 ^ (p+1)` is a valid extension
  have hmem : s (p + 1) + 2 * 2 ^ p ∈ validExt (p + 2) s := by
    rw [hK]
    simp only [cand, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Icc]
    refine ⟨2 ^ p, ⟨?_, le_rfl⟩, rfl⟩
    have : (0 : ℤ) < 2 ^ p := by positivity
    linarith
  have htop : tri (Function.update s (p + 2) (s (p + 1) + 2 * 2 ^ p)) 1 (p + 1) =
      2 ^ (p + 1) := by
    rw [tri_update_one, add_sub_cancel_left, pow_succ, abs_of_pos (by positivity)]
    ring
  have hgaps := gap_eq_of_tight (p + 1) hmem htop
  have hgap : ∀ a, a + 1 < p + 2 → s (a + 1) = s a + 2 ^ a := by
    intro a ha
    have h := hgaps a (by omega)
    rw [tri_update_of_lt s (p + 2) _ 1 a (by omega)] at h
    have h' : |s (a + 1) - s a| = 2 ^ a := h
    rw [abs_of_pos (by linarith [hmono a ha])] at h'
    linarith
  intro i
  induction i with
  | zero => intro _; rw [hs0]; rfl
  | succ i ih =>
    intro hi
    rw [hgap i hi, ih (by omega)]
    linarith [U_succ_sub i]

/-- **Maximum-width conjecture (arXiv:2606.23721, Conjecture `conj:max`).** For every
`n ≥ 2`: every valid-extension set of a length-`n` sequence is finite; the maximum of
`|K_S|` over `S ∈ 𝒢_n` is `2^{n-1} + 1`; and it is uniquely achieved by the doubling
sequence `U_n` (as a length-`n` prefix). -/
theorem conj_max (n : ℕ) (hn : 2 ≤ n) :
    (∀ s, (validExt n s).Finite) ∧
    IsGreatest {w : ℕ | ∃ s, InG n s ∧ (validExt n s).ncard = w} (2 ^ (n - 1) + 1) ∧
    ∀ s, InG n s → (validExt n s).ncard = 2 ^ (n - 1) + 1 → ∀ i < n, s i = U i :=
  ⟨fun s => (validExt_finite_and_ncard_le n (by omega) s).1,
   ⟨⟨U, InG_U n, ncard_validExt_U n hn⟩,
    fun _ ⟨s, _, hw⟩ => hw ▸ (validExt_finite_and_ncard_le n (by omega) s).2⟩,
   eq_U_of_ncard_eq n hn⟩

end GilbreathValidExtensionHoles
