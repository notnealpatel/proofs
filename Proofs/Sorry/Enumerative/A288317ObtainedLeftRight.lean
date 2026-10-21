/-
# A288317 — length of the iterates of the rewrite 00 -> 0001, 1 -> 00

## OEIS source (retrieved with `oeis show A288317` / `oeis show A288314`, 2026-10-21)

```
A288317
NAME:     a(n) = a(n-1) + 3*a(n-2) - 2*a(n-3) - a(n-4) for n >= 4, where a(0) = 2,
          a(1) = 4, a(2) = 7, a(3) = 12.
TERMS:    2,4,7,12,22,40,75,139,262,489,922,1726,3252,6097,11479,21540,40531,...
FORMULA:  G.f.: (2 + 2*x - 3*x^2 - 3*x^3 - x^4)/(1 - x - 3*x^2 + 2*x^3 + x^4).
COMMENT:  Conjecture:  a(n) is the number of letters (0's and 1's) in the n-th
          iteration of the mapping 00->0001, 1->00, starting with 00; see A288314.
          (the comment is unsigned; the entry AUTHOR line is
          "Clark Kimberling, Jun 09 2017")
A288314 PROGRAM (Mathematica, defines the iteration):
          s = {0, 0}; w[0] = StringJoin[Map[ToString, s]];
          w[n_] := StringReplace[w[n - 1], {"00" -> "0001", "1" -> "00"}]
```

## Status

Triage: open (no proof in the entry or in the literature found by the triage).
This module proves the conjecture in full, in the generating-function form
(theorem `length_w_gf`).

Indexing: the data start `a(0) = 2 = |w_0|` with `w_0 = 00`, so the claim is
`|w_n| = a(n)` for all `n ≥ 0` (the A288314 program's `Table[..., {n, 1, 35}]`
is offset by one against the data; the data are what is formalized).

The NAME recurrence "for n >= 4" is wrong at `n = 4` (it gives 23, not 22); the
g.f. numerator has degree 4, so the order-4 recurrence holds only for `n ≥ 5`.
Both facts are recorded below (`length_w_rec`, `name_recurrence_fails_at_four`).

## Proof outline

Write `tok a = 1 0^a`.  For `n ≥ 1`, `w_n = 000 · tok x_1 ⋯ tok x_k · tok t`.
Mathematica's left-to-right rewrite restarts zero-pairing after every `1`, so
`step` acts token by token, and a pending trailing-zero count carries from one
token into the next (`S`, `P`).  Along the orbit the letters `x_i` lie in
`{3, 5, 6}`, `t` alternates between `3` and `1`, and the letter counts evolve by
the substitution `3 ↦ 6, 5 ↦ 3 6, 6 ↦ 3 3 5` (matrix with characteristic
polynomial `x^3 - 3x - 1`) plus boundary terms; the length recurrence with
characteristic polynomial `(x - 1)(x^3 - 3x - 1)` follows by linear arithmetic.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A288317ObtainedLeftRight

/-- One left-to-right non-overlapping pass of Mathematica's
`StringReplace[_, {"00" -> "0001", "1" -> "00"}]` on a binary word, with `false = 0`
and `true = 1`: at each position the rule `00 -> 0001` is tried first, then
`1 -> 00`; a `0` not followed by `0` is copied unchanged. -/
def step : List Bool → List Bool
  | false :: false :: rest => [false, false, false, true] ++ step rest
  | true :: rest => [false, false] ++ step rest
  | false :: rest => false :: step rest
  | [] => []

/-- The word `w_n`: `n` iterations of `step` starting from `w_0 = 00`. -/
def w (n : ℕ) : List Bool := step^[n] [false, false]

/- Ground truth against the A288314 Mathematica table: `w_1 = 0001`, `w_2 = 0001000`,
`w_3 = 000100000010`. -/
example : w 1 = [false, false, false, true] := by decide
example : w 2 = [false, false, false, true, false, false, false] := by decide
example : w 3 = [false, false, false, true, false, false, false, false, false, false, true,
    false] := by decide

/- Ground truth against the first twelve A288317 terms. -/
example : (List.range 12).map (fun n => (w n).length) =
    [2, 4, 7, 12, 22, 40, 75, 139, 262, 489, 922, 1726] := by decide +kernel

/-- The image `(0001)^(a/2) 0^(a % 2)` of a maximal run of `a` zeros. -/
def F (a : ℕ) : List Bool :=
  (List.replicate (a / 2) [false, false, false, true]).flatten ++ List.replicate (a % 2) false

/-- A run of `a` zeros followed by a `1` or by the end of the word rewrites to `F a`. -/
theorem step_zeros : ∀ (a : ℕ) (v : List Bool), v.head? ≠ some false →
    step (List.replicate a false ++ v) = F a ++ step v
  | 0, v, _ => by simp [F]
  | 1, v, hv => by
    match v, hv with
    | [], _ => rfl
    | true :: u, _ => rfl
    | false :: u, hv => exact absurd rfl hv
  | a + 2, v, hv => by
    have ih := step_zeros a v hv
    have h1 : (a + 2) / 2 = a / 2 + 1 := by omega
    have h2 : (a + 2) % 2 = a % 2 := by omega
    simp only [List.replicate_succ, List.cons_append, step, ih, F, h1, h2,
      List.flatten_cons, List.append_assoc]


/-- The token `1 0^a`. -/
def tok (a : ℕ) : List Bool := true :: List.replicate a false

/-- Concatenation of the tokens `tok x` for `x ∈ X`. -/
def T (X : List ℕ) : List Bool := (X.map tok).flatten

/-- The shape `000 · tok x_1 ⋯ tok x_k · tok t` of the words `w_n`, `n ≥ 1`. -/
def W (X : List ℕ) (t : ℕ) : List Bool := List.replicate 3 false ++ T X ++ tok t

/-- The image `00 · F a` of the token `tok a`. -/
def g (a : ℕ) : List Bool := [false, false] ++ F a

/-- `step` rewrites a token followed by a `1` or the end of the word as `g a`. -/
theorem step_tok (a : ℕ) (v : List Bool) (hv : v.head? ≠ some false) :
    step (tok a ++ v) = g a ++ step v := by
  simp only [tok, List.cons_append, step, step_zeros a v hv, g, List.append_assoc]

/-- Prefixing tokens keeps the head of a word different from `0`. -/
theorem head_T_append (X : List ℕ) (v : List Bool) (hv : v.head? ≠ some false) :
    (T X ++ v).head? ≠ some false := by
  cases X with
  | nil => simpa [T] using hv
  | cons x X => simp [T, tok]

/-- `step` acts token by token on a concatenation of tokens. -/
theorem step_T (X : List ℕ) (v : List Bool) (hv : v.head? ≠ some false) :
    step (T X ++ v) = (X.map g).flatten ++ step v := by
  induction X with
  | nil => simp [T]
  | cons x X ih =>
    have hT : T (x :: X) = tok x ++ T X := by simp [T]
    rw [hT, List.append_assoc, step_tok x _ (head_T_append X v hv), ih]
    simp

/-- `step` on a word of shape `W X t`. -/
theorem step_W (X : List ℕ) (t : ℕ) :
    step (W X t) = List.replicate 3 false ++ tok 1 ++ (X.map g).flatten ++ g t := by
  have hhead : (T X ++ tok t).head? ≠ some false := head_T_append X _ (by simp [tok])
  have hrest : step (T X ++ tok t) = (X.map g).flatten ++ g t := by
    rw [step_T X _ (by simp [tok])]
    have := step_tok t [] (by simp)
    simp only [List.append_nil] at this
    rw [this]
    simp [step]
  rw [W, List.append_assoc, step_zeros 3 _ hhead, hrest]
  simp [F, tok]

/-- `1 · F y` re-tokenizes as `(tok 3)^(y/2) · tok (y % 2)`. -/
theorem cons_F : ∀ y : ℕ, true :: F y = T (List.replicate (y / 2) 3) ++ tok (y % 2)
  | 0 => by simp [F, T, tok]
  | 1 => by simp [F, T, tok]
  | y + 2 => by
    have ih := cons_F y
    have h1 : (y + 2) / 2 = y / 2 + 1 := by omega
    have h2 : (y + 2) % 2 = y % 2 := by omega
    rw [h1, h2, List.replicate_succ]
    simp only [F, h1, h2, List.replicate_succ, List.flatten_cons] at ih ⊢
    simp only [T, List.map_cons, List.flatten_cons, tok] at ih ⊢
    simp [ih]


/-- For `2 ≤ x`, the image of `tok x` is `0^5 · (tok 3)^(x/2-1) · tok (x % 2)`. -/
theorem g_of_two_le (x : ℕ) (hx : 2 ≤ x) :
    g x = List.replicate 5 false ++ T (List.replicate (x / 2 - 1) 3) ++ tok (x % 2) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 := ⟨x - 2, by omega⟩
  have h1 : (y + 2) / 2 = y / 2 + 1 := by omega
  have h2 : (y + 2) % 2 = y % 2 := by omega
  have hF : F (y + 2) = [false, false, false, true] ++ F y := by
    simp [F, h1, h2, List.replicate_succ]
  rw [h1, h2, Nat.add_sub_cancel, List.append_assoc, ← cons_F y, g, hF]
  simp [List.replicate_succ]

/-- For `x < 2`, the image of `tok x` is `0^(x+2)`. -/
theorem g_of_lt_two (x : ℕ) (hx : x < 2) : g x = List.replicate (x + 2) false := by
  interval_cases x <;> rfl

/-- Appending zeros to a token lengthens it. -/
theorem tok_append_replicate (p k : ℕ) :
    tok p ++ List.replicate k false = tok (p + k) := by
  rw [tok, tok, List.cons_append, List.replicate_add]

/-- `T` turns list concatenation into word concatenation. -/
theorem T_append (X Y : List ℕ) : T (X ++ Y) = T X ++ T Y := by
  simp [T]

/-- `T` of a cons. -/
theorem T_cons (x : ℕ) (X : List ℕ) : T (x :: X) = tok x ++ T X := by
  simp [T]

/-- Tokens produced by re-tokenizing `tok p · g x_1 ⋯ g x_k` (all `x_i ≥ 2`):
the pending token `tok p` is completed by five zeros. -/
def S : ℕ → List ℕ → List ℕ
  | _, [] => []
  | p, x :: X => (p + 5) :: (List.replicate (x / 2 - 1) 3 ++ S (x % 2) X)

/-- Length of the pending trailing token after re-tokenizing `tok p · g x_1 ⋯ g x_k`. -/
def P : ℕ → List ℕ → ℕ
  | p, [] => p
  | _, x :: X => P (x % 2) X

/-- Re-tokenization: `tok p · g x_1 ⋯ g x_k = T (S p X) · tok (P p X)` when all `x_i ≥ 2`. -/
theorem tok_append_flatten_g (X : List ℕ) (hX : ∀ x ∈ X, 2 ≤ x) (p : ℕ) :
    tok p ++ (X.map g).flatten = T (S p X) ++ tok (P p X) := by
  induction X generalizing p with
  | nil => simp [S, P, T]
  | cons x X ih =>
    have hx : 2 ≤ x := hX x (by simp)
    have ih' := ih (fun y hy => hX y (by simp [hy])) (x % 2)
    simp only [List.map_cons, List.flatten_cons, S, P, T_cons, T_append]
    rw [g_of_two_le x hx, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
      tok_append_replicate, List.append_assoc, List.append_assoc, ih']
    simp only [List.append_assoc]

/-- The state map `(X, t) ↦ (X', t')` with `step (W X t) = W X' t'`. -/
def next (s : List ℕ × ℕ) : List ℕ × ℕ :=
  if 2 ≤ s.2 then (S 1 (s.1 ++ [s.2]), P 1 (s.1 ++ [s.2])) else (S 1 s.1, P 1 s.1 + (s.2 + 2))

/-- `step` on a word of shape `W X t`. -/
theorem step_W_eq (X : List ℕ) (t : ℕ) (hX : ∀ x ∈ X, 2 ≤ x) :
    step (W X t) = W (next (X, t)).1 (next (X, t)).2 := by
  rw [step_W]
  by_cases ht : 2 ≤ t
  · have hXt : ∀ x ∈ X ++ [t], 2 ≤ x := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hX x h
      · rw [List.mem_singleton] at h; omega
    have key := tok_append_flatten_g (X ++ [t]) hXt 1
    simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil] at key
    simp only [next, ht, if_true, W, List.append_assoc]
    rw [key]
  · have key := tok_append_flatten_g X hX 1
    simp only [next, ht, if_false, W, List.append_assoc]
    rw [g_of_lt_two t (by omega), ← List.append_assoc (tok 1), key, List.append_assoc,
      tok_append_replicate]

/-- Every token length produced by `S` is at least `2`. -/
theorem mem_S_two_le (p : ℕ) (X : List ℕ) : ∀ x ∈ S p X, 2 ≤ x := by
  induction X generalizing p with
  | nil => simp [S]
  | cons y X ih =>
    intro x hx
    simp only [S, List.mem_cons, List.mem_append, List.mem_replicate] at hx
    rcases hx with h | ⟨_, h⟩ | h
    · omega
    · omega
    · exact ih _ x h

/-- The state of `w_(n+1)`: iterate `next` from `([], 0)` (that is, from `w_1 = 0001`). -/
def st : ℕ → List ℕ × ℕ
  | 0 => ([], 0)
  | n + 1 => next (st n)

/-- All token lengths in the orbit states are at least `2`. -/
theorem st_two_le (n : ℕ) : ∀ x ∈ (st n).1, 2 ≤ x := by
  cases n with
  | zero => simp [st]
  | succ n =>
    simp only [st, next]
    split_ifs
    · exact mem_S_two_le _ _
    · exact mem_S_two_le _ _

/-- `w_(n+1) = W (st n).1 (st n).2`. -/
theorem w_succ_eq (n : ℕ) : w (n + 1) = W (st n).1 (st n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : w (n + 2) = step (w (n + 1)) := by
      simp only [w]; rw [Function.iterate_succ_apply']
    rw [h, ih, step_W_eq _ _ (st_two_le n)]
    rfl


/-- `P` of a concatenation. -/
theorem P_append (p : ℕ) (X Y : List ℕ) : P p (X ++ Y) = P (P p X) Y := by
  induction X generalizing p with
  | nil => rfl
  | cons x X ih => exact ih (x % 2)

/-- `S` of a concatenation. -/
theorem S_append (p : ℕ) (X Y : List ℕ) : S p (X ++ Y) = S p X ++ S (P p X) Y := by
  induction X generalizing p with
  | nil => rfl
  | cons x X ih => simp [S, P, ih]

/-- `P` of a list ending in `x` is `x % 2`. -/
theorem P_concat (p x : ℕ) (X : List ℕ) : P p (X ++ [x]) = x % 2 := by
  rw [P_append]; rfl

/-- The run substitution `x ↦ 3^(x/2-1) (x % 2 + 5)`; on `{3,5,6}`:
`3 ↦ 6`, `5 ↦ 3 6`, `6 ↦ 3 3 5`. -/
def sig (x : ℕ) : List ℕ := List.replicate (x / 2 - 1) 3 ++ [x % 2 + 5]

/-- `S` of a concatenation. -/
theorem S_append_P (p : ℕ) (X : List ℕ) :
    S p X ++ [P p X + 5] = (p + 5) :: (X.map sig).flatten := by
  induction X generalizing p with
  | nil => rfl
  | cons x X ih => simp [S, P, sig, ih]

/-- The run alphabet `{3, 5, 6}`. -/
def Good (x : ℕ) : Prop := x = 3 ∨ x = 5 ∨ x = 6

/-- `σ` maps words over `{3,5,6}` to words over `{3,5,6}`. -/
theorem good_sig (X : List ℕ) (hX : ∀ x ∈ X, Good x) : ∀ y ∈ (X.map sig).flatten, Good y := by
  intro y hy
  simp only [List.mem_flatten, List.mem_map] at hy
  obtain ⟨l, ⟨x, hx, rfl⟩, hyl⟩ := hy
  rcases hX x hx with rfl | rfl | rfl <;>
    simp only [sig, Nat.reduceDiv, tsub_self, Nat.add_one_sub_one, List.replicate_zero,
      List.replicate_one, List.reduceReplicate, Nat.reduceMod, Nat.reduceAdd, zero_add,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, or_self_left,
      Good] at hyl ⊢ <;> omega

/-- Letter counts of `σ(X)` for `X` over `{3,5,6}`. -/
theorem count_sig (X : List ℕ) (hX : ∀ x ∈ X, Good x) :
    (X.map sig).flatten.count 3 = X.count 5 + 2 * X.count 6 ∧
    (X.map sig).flatten.count 5 = X.count 6 ∧
    (X.map sig).flatten.count 6 = X.count 3 + X.count 5 := by
  induction X with
  | nil => simp
  | cons x X ih =>
    obtain ⟨h3, h5, h6⟩ := ih (fun y hy => hX y (by simp [hy]))
    simp only [List.map_cons, List.flatten_cons, List.count_append, List.count_cons, h3, h5, h6]
    rcases hX x (by simp) with rfl | rfl | rfl <;>
    simp only [sig, Nat.reduceDiv, tsub_self, Nat.add_one_sub_one, List.replicate_zero,
      List.replicate_one, List.reduceReplicate, Nat.reduceMod, Nat.reduceAdd, List.cons_append,
      List.nil_append, List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, ne_eq, Nat.reduceEqDiff, List.count_cons_of_ne, List.count_nil,
      List.count_cons_self, zero_add, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, add_zero,
      Nat.succ_ne_self, or_false, or_true, or_self,
      List.count_eq_one_of_mem, BEq.rfl, true_and, and_true] <;> omega

/-- Length of `T X` for `X` over `{3,5,6}`. -/
theorem length_T (X : List ℕ) (hX : ∀ x ∈ X, Good x) :
    (T X).length = 4 * X.count 3 + 6 * X.count 5 + 7 * X.count 6 := by
  induction X with
  | nil => simp [T]
  | cons x X ih =>
    have ih' := ih (fun y hy => hX y (by simp [hy]))
    rw [T_cons, List.length_append, ih']
    simp only [List.count_cons]
    rcases hX x (by simp) with rfl | rfl | rfl <;>
    simp only [tok, List.reduceReplicate, List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd, BEq.rfl, ↓reduceIte, Nat.reduceBEq, Bool.false_eq_true, add_zero] <;> omega

/-- Orbit invariant of `st m` for `1 ≤ m`: letters in `{3,5,6}`; for odd `m` the
trailing token is `tok 3` and the pending parity is `1`; for even `m` it is `tok 1`
and the pending parity is `0`. -/
def Inv (m : ℕ) : Prop :=
  (∀ x ∈ (st m).1, Good x) ∧
  (Odd m → (st m).2 = 3 ∧ P 1 (st m).1 = 1) ∧
  (Even m → (st m).2 = 1 ∧ P 1 (st m).1 = 0)

/-- Transition from an odd state. -/
theorem st_succ_odd (m : ℕ) (hm : Odd m) (h : Inv m) :
    (st (m + 1)).1 = 6 :: ((st m).1.map sig).flatten ∧ (st (m + 1)).2 = 1 ∧
    P 1 (st (m + 1)).1 = 0 := by
  obtain ⟨ht, hP⟩ := h.2.1 hm
  have hst : st (m + 1) = next (st m) := rfl
  have hX : (st (m + 1)).1 = S 1 (st m).1 ++ [6] := by
    rw [hst, next, ht, if_pos (by norm_num)]
    rw [S_append, hP]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have := S_append_P 1 (st m).1
    rw [hP] at this
    rw [hX, this]
  · rw [hst, next, ht, if_pos (by norm_num)]
    exact P_concat _ _ _
  · rw [hX, P_concat]

/-- Transition from an even state. -/
theorem st_succ_even (m : ℕ) (hm : Even m) (h : Inv m) :
    (st (m + 1)).1 ++ [5] = 6 :: ((st m).1.map sig).flatten ∧ (st (m + 1)).2 = 3 ∧
    P 1 (st (m + 1)).1 = 1 := by
  obtain ⟨ht, hP⟩ := h.2.2 hm
  have hst : st (m + 1) = next (st m) := rfl
  rw [hst, next, ht, if_neg (by norm_num)]
  refine ⟨?_, ?_, ?_⟩
  · have := S_append_P 1 (st m).1
    rw [hP] at this
    simpa using this
  · simp [hP]
  · rcases List.eq_nil_or_concat (st m).1 with hnil | ⟨Y, x, hYx⟩
    · rw [hnil] at hP; simp [P] at hP
    · rw [List.concat_eq_append] at hYx
      have hx : Good x := h.1 x (by rw [hYx]; simp)
      rw [hYx, P_concat] at hP
      have hx6 : x = 6 := by rcases hx with rfl | rfl | rfl <;> simp_all
      simp only [hYx, hx6, S_append]
      rw [P_append]
      simp [S, P]

/-- The orbit invariant holds for every `1 ≤ m`. -/
theorem inv_st : ∀ m, 1 ≤ m → Inv m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact ⟨by simp [st, next, S], fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by decide)⟩
  | succ m hm ih =>
    rcases Nat.even_or_odd m with he | ho
    · obtain ⟨hX, ht, hP⟩ := st_succ_even m he ih
      refine ⟨?_, fun _ => ⟨ht, hP⟩, fun h' => absurd h' (by simpa [Nat.even_add_one] using he)⟩
      intro x hx
      have hx' : x ∈ 6 :: ((st m).1.map sig).flatten := by
        rw [← hX]; exact List.mem_append_left _ hx
      rcases List.mem_cons.1 hx' with h | h
      · right; right; exact h
      · exact good_sig _ ih.1 x h
    · obtain ⟨hX, ht, hP⟩ := st_succ_odd m ho ih
      refine ⟨?_, fun h' => absurd h' (by simpa [Nat.odd_add_one] using ho), fun _ => ⟨ht, hP⟩⟩
      intro x hx
      rw [hX] at hx
      rcases List.mem_cons.1 hx with h | h
      · right; right; exact h
      · exact good_sig _ ih.1 x h

/-- Counts of `6 :: X`. -/
theorem count_cons_six (X : List ℕ) :
    (6 :: X).count 3 = X.count 3 ∧ (6 :: X).count 5 = X.count 5 ∧
    (6 :: X).count 6 = X.count 6 + 1 := by
  simp

/-- Linear evolution of the letter counts along the orbit. -/
theorem counts_succ (m : ℕ) (hm : 1 ≤ m) :
    (st (m + 1)).1.count 3 = (st m).1.count 5 + 2 * (st m).1.count 6 ∧
    (st (m + 1)).1.count 5 + (if Even m then 1 else 0) = (st m).1.count 6 ∧
    (st (m + 1)).1.count 6 = (st m).1.count 3 + (st m).1.count 5 + 1 := by
  have ih := inv_st m hm
  obtain ⟨h3, h5, h6⟩ := count_sig _ ih.1
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨hX, -, -⟩ := st_succ_even m he ih
    have e3 := congrArg (List.count 3) hX
    have e5 := congrArg (List.count 5) hX
    have e6 := congrArg (List.count 6) hX
    simp only [List.count_append, List.count_cons, List.count_nil] at e3 e5 e6
    simp only [if_pos he]
    simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, add_zero, BEq.rfl, zero_add]
      at e3 e5 e6
    omega
  · obtain ⟨hX, -, -⟩ := st_succ_odd m ho ih
    have hne : ¬ Even m := Nat.not_even_iff_odd.2 ho
    rw [hX]
    obtain ⟨c3, c5, c6⟩ := count_cons_six ((st m).1.map sig).flatten
    simp only [if_neg hne, c3, c5, c6]
    omega

/-- The trailing token length alternates: `1` at even, `3` at odd `m ≥ 1`. -/
theorem t_val (m : ℕ) (hm : 1 ≤ m) : (st m).2 = if Even m then 1 else 3 := by
  have ih := inv_st m hm
  rcases Nat.even_or_odd m with he | ho
  · rw [if_pos he]; exact (ih.2.2 he).1
  · rw [if_neg (Nat.not_even_iff_odd.2 ho)]; exact (ih.2.1 ho).1

/-- `|w_(m+1)|` in terms of the letter counts of `st m`. -/
theorem length_w_succ (m : ℕ) (hm : 1 ≤ m) :
    (w (m + 1)).length = 4 + 4 * (st m).1.count 3 + 6 * (st m).1.count 5 +
      7 * (st m).1.count 6 + (st m).2 := by
  rw [w_succ_eq, W, List.length_append, List.length_append, length_T _ (inv_st m hm).1]
  simp only [List.length_replicate, tok, List.length_cons]
  omega

/-- The order-4 recurrence for `|w_n|`, from `n = 6` on. -/
theorem length_rec (n : ℕ) (hn : 2 ≤ n) :
    ((w (n + 4)).length : ℤ) = (w (n + 3)).length + 3 * (w (n + 2)).length -
      2 * (w (n + 1)).length - (w n).length := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  rw [show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega,
    show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 1 = (m + 1) + 1 by omega]
  have L0 := length_w_succ m hm
  have L1 := length_w_succ (m + 1) (by omega)
  have L2 := length_w_succ (m + 2) (by omega)
  have L3 := length_w_succ (m + 3) (by omega)
  have L4 := length_w_succ (m + 4) (by omega)
  have T0 := counts_succ m hm
  have T1 := counts_succ (m + 1) (by omega)
  have T2 := counts_succ (m + 2) (by omega)
  have T3 := counts_succ (m + 3) (by omega)
  have V0 := t_val m hm
  have V1 := t_val (m + 1) (by omega)
  have V2 := t_val (m + 2) (by omega)
  have V3 := t_val (m + 3) (by omega)
  have V4 := t_val (m + 4) (by omega)
  rcases Nat.even_or_odd m with he | ho
  · have hm2 : m % 2 = 0 := Nat.even_iff.1 he
    have e1 : ¬ Even (m + 1) := by rw [Nat.even_iff]; omega
    have e2 : Even (m + 2) := by rw [Nat.even_iff]; omega
    have e3 : ¬ Even (m + 3) := by rw [Nat.even_iff]; omega
    have e4 : Even (m + 4) := by rw [Nat.even_iff]; omega
    simp only [if_pos he, if_neg e1, if_pos e2, if_neg e3, if_pos e4] at T0 T1 T2 T3 V0 V1 V2 V3 V4
    simp only [show m + 1 + 1 = m + 2 from rfl, show m + 2 + 1 = m + 3 from rfl,
      show m + 3 + 1 = m + 4 from rfl] at *
    omega
  · have hm2 : m % 2 = 1 := Nat.odd_iff.1 ho
    have he : ¬ Even m := by rw [Nat.even_iff]; omega
    have e1 : Even (m + 1) := by rw [Nat.even_iff]; omega
    have e2 : ¬ Even (m + 2) := by rw [Nat.even_iff]; omega
    have e3 : Even (m + 3) := by rw [Nat.even_iff]; omega
    have e4 : ¬ Even (m + 4) := by rw [Nat.even_iff]; omega
    simp only [if_neg he, if_pos e1, if_neg e2, if_pos e3, if_neg e4] at T0 T1 T2 T3 V0 V1 V2 V3 V4
    simp only [show m + 1 + 1 = m + 2 from rfl, show m + 2 + 1 = m + 3 from rfl,
      show m + 3 + 1 = m + 4 from rfl] at *
    omega

/-- The first six lengths `|w_0|, …, |w_5| = 2, 4, 7, 12, 22, 40`. -/
theorem length_w_init :
    (w 0).length = 2 ∧ (w 1).length = 4 ∧ (w 2).length = 7 ∧ (w 3).length = 12 ∧
      (w 4).length = 22 ∧ (w 5).length = 40 := by
  have v : (List.range 6).map (fun k => (w k).length) = [2, 4, 7, 12, 22, 40] := by
    decide +kernel
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at v
  exact v

open PowerSeries in
/-- **A288317 conjecture (unsigned comment; entry by Clark Kimberling, Jun 09 2017), proved.**

Verbatim: "Conjecture: a(n) is the number of letters (0's and 1's) in the n-th
iteration of the mapping 00->0001, 1->00, starting with 00; see A288314."

Here `a(n)` is the sequence with g.f.
`(2 + 2x - 3x^2 - 3x^3 - x^4)/(1 - x - 3x^2 + 2x^3 + x^4)`.  The denominator
has constant term `1`, so it is a unit in `ℤ⟦X⟧` and the identity below is
equivalent to `Σ |w_n| x^n` being that g.f. -/
theorem length_w_gf :
    PowerSeries.mk (fun n => ((w n).length : ℤ)) * (1 - X - 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4) =
      2 + 2 * X - 3 * X ^ 2 - 3 * X ^ 3 - X ^ 4 := by
  set f := PowerSeries.mk (fun n => ((w n).length : ℤ)) with hf
  have hl : f * (1 - X - 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4) =
      f - f * X ^ 1 - C (3 : ℤ) * (f * X ^ 2) + C (2 : ℤ) * (f * X ^ 3) + f * X ^ 4 := by
    rw [map_ofNat, map_ofNat]; ring
  have hr : (2 + 2 * X - 3 * X ^ 2 - 3 * X ^ 3 - X ^ 4 : ℤ⟦X⟧) =
      C (2 : ℤ) + C (2 : ℤ) * X ^ 1 - C (3 : ℤ) * X ^ 2 - C (3 : ℤ) * X ^ 3 -
        C (1 : ℤ) * X ^ 4 := by
    rw [map_ofNat, map_ofNat, map_one]; ring
  rw [hl, hr]
  ext n
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := length_w_init
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_C, hf,
    coeff_mk]
  match n with
  | 0 => simp [v0]
  | 1 => simp [v0, v1]
  | 2 => simp [v0, v1, v2]
  | 3 => simp [v0, v1, v2, v3]
  | 4 => simp [v0, v1, v2, v3, v4]
  | 5 => simp [v1, v2, v3, v4, v5]
  | k + 6 =>
    have hrec := length_rec (k + 2) (by omega)
    simp only [show k + 2 + 4 = k + 6 by omega, show k + 2 + 3 = k + 5 by omega,
      show k + 2 + 2 = k + 4 by omega, show k + 2 + 1 = k + 3 by omega] at hrec
    simp only [show ¬ (k + 6 = 0) by omega, if_false, show 1 ≤ k + 6 by omega,
      show 2 ≤ k + 6 by omega, show 3 ≤ k + 6 by omega, show 4 ≤ k + 6 by omega, if_true,
      show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
      Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, sub_zero, zero_add]
    linarith

/-- The order-4 recurrence `|w_(n+4)| = |w_(n+3)| + 3|w_(n+2)| - 2|w_(n+1)| - |w_n|`
holds for every `1 ≤ n`, i.e. for `a(m)` with `m ≥ 5` (the range forced by the
degree-4 numerator of the g.f.). -/
theorem length_w_rec (n : ℕ) (hn : 1 ≤ n) :
    ((w (n + 4)).length : ℤ) = (w (n + 3)).length + 3 * (w (n + 2)).length -
      2 * (w (n + 1)).length - (w n).length := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    obtain ⟨-, v1, v2, v3, v4, v5⟩ := length_w_init
    rw [v1, v2, v3, v4, v5]
    norm_num
  · exact length_rec n h

/-- The NAME of A288317 asserts the recurrence "for n >= 4"; it fails at `n = 4`:
`a(3) + 3a(2) - 2a(1) - a(0) = 23 ≠ 22 = |w_4|`. -/
theorem name_recurrence_fails_at_four :
    ((w 4).length : ℤ) ≠ (w 3).length + 3 * (w 2).length - 2 * (w 1).length - (w 0).length := by
  obtain ⟨v0, v1, v2, v3, v4, -⟩ := length_w_init
  rw [v0, v1, v2, v3, v4]
  norm_num

end Candidates.A288317ObtainedLeftRight
