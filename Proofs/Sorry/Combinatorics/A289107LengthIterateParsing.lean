/-
# A289107 — Kimberling: iterate lengths of `00->0010, 01->011, 10->000` (proved)

## OEIS source (retrieved 2026-10-21 with `oeis show A289107`, `oeis show
## A289104`, and the live entry https://oeis.org/A289107)

```
NAME:     a(n) = 2*a(n-1) - a(n-3) for n >= 5, a(0) = 2, a(1) = 4, a(2) = 7,
          a(3) = 12, a(4) = 22.
OFFSET:   0
TERMS:    2,4,7,12,22,37,62,102,167,272,442,717,1162,1882,3047,4932,7982,...
COMMENT:  Conjecture:  a(n) is the number of letters (0's and 1's) in the
          n-th iterate of the mapping 00->0010, 01->011, 10->000, starting
          with 00; see A289104.
FORMULA:  G.f.: (2 - x^2 + 2*x^4)/(1 - 2*x + x^3).
FORMULA:  a(n) = -3 + 2^(-1-n)*sqrt(5)*(-(1-sqrt(5))^(1 + n)
          + (1+sqrt(5))^(1+n)) for n>1. - _Colin Barker_, Jun 28 2017
AUTHOR:   _Clark Kimberling_, Jun 28 2017
```

The conjecture comment carries no separate signature; it belongs to the
entry's author, Clark Kimberling (Jun 28 2017).  The companion entry A289104
repeats it ("Conjecture: the number of letters (0's and 1's) in the n-th
iterate of the mapping is given by A289107.") and fixes the meaning of
"iterate" through its Mathematica program:

```
w[n_] := StringReplace[w[n - 1], {"00" -> "0010", "01" -> "011", "10" -> "000"}]
Table[StringLength[w[n]], {n, 0, 20}] (* A289107 *)
```

`StringReplace` scans left to right, replaces non-overlapping matches, tries
the rules in order at each position, and keeps unmatched characters.

## Status

Triage status: open (no proof in the entry or in the literature found by the
triage; Python agreement for `n < 30`, extended here to `n < 36`).  This
module **proves** the conjecture (`length_eq_a`) and the closed form
`|w n| + 3 = 5 F(n+1)` for `n ≠ 1` (`length_add_three_eq_five_mul_fib`), which
is Colin Barker's Binet formula with `F` the Fibonacci numbers.

## Proof outline

Each iterate is the bit coding of a word over a 16-letter alphabet obtained by
iterating a substitution `sub`.  Eleven letters are tokens of the parse of the
iterate (`00`, `01`, `10`, or a lone `1` before another `1`), decorated with
the letter left pending when the next iterate is parsed; five sentinel
letters track the end of the word, where the iterates alternately carry a
lone trailing `0`.  The admissible adjacent pairs (`adj`) form a set closed
under `sub`.  For an admissible word, `step` acts token by token
(`step_flatMap`), and the images retokenize as the coding of the substituted
word (`tele`).  The bit length then satisfies
`|w (n+7)| + |w (n+4)| = 2 |w (n+6)|` because the same identity holds on every
letter (`len_rec_letter`, a finite check), and the first seven lengths are
computed directly.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A289107LengthIterateParsing

/-! ## Definition layer

Letters are `Bool`, with `false` for `0` and `true` for `1`. -/

/-- One application of Mathematica's
`StringReplace[s, {"00" -> "0010", "01" -> "011", "10" -> "000"}]`:
scan left to right; at each position replace the first matching two-letter
pattern and skip past it; otherwise (pattern `11`, or a final single letter)
keep the letter and advance by one. -/
def step : List Bool → List Bool
  | false :: false :: t => false :: false :: true :: false :: step t
  | false :: true :: t => false :: true :: true :: step t
  | true :: false :: t => false :: false :: false :: step t
  | b :: t => b :: step t
  | [] => []

/-- The `n`-th iterate of `step`, starting from the word `00`. -/
def w (n : ℕ) : List Bool := step^[n] [false, false]

/-- A289107 as defined by its NAME line:
`a(n) = 2a(n-1) - a(n-3)` for `n ≥ 5`, with `a(0..4) = 2, 4, 7, 12, 22`. -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | 4 => 22
  | n + 5 => 2 * a (n + 4) - a (n + 2)

/-! ## Ground truth -/

-- The first iterates, as printed by the A289104 program
-- (`00`, `0010`, `0010000`, `001000000100`).
example : w 0 = [false, false] := rfl
example : w 1 = [false, false, true, false] := rfl
example : w 2 = [false, false, true, false, false, false, false] := rfl
example : w 3 =
    [false, false, true, false, false, false, false, false, false, true, false, false] := rfl

-- `step` keeps an unmatched `1` of a pattern `11` and a final single letter.
example : step [true, true, false] = [true, false, false, false] := rfl
example : step [false, true, false] = [false, true, true, false] := rfl

-- The recurrence reproduces the DATA line `2, 4, 7, ..., 3047, 4932`.
example : (List.range 16).map a =
    [2, 4, 7, 12, 22, 37, 62, 102, 167, 272, 442, 717, 1162, 1882, 3047, 4932] := by
  decide +kernel

-- The iterate lengths reproduce the first ten listed terms.
example : (List.range 10).map (fun n => (w n).length) =
    [2, 4, 7, 12, 22, 37, 62, 102, 167, 272] := by
  decide +kernel

/-! ## The coding alphabet -/

/-- Letters of the auxiliary substitution: eleven decorated parse tokens
`a, …, l` and five end-of-word sentinels `z0, …, z4`. -/
inductive Letter
  | a | b | c | d | e | g | h | i | j | k | l | z0 | z1 | z2 | z3 | z4
  deriving DecidableEq, Repr

namespace Letter

/-- The substitution on letters: the letters coding the next iterate produced
by one letter of the current iterate. -/
def sub : Letter → List Letter
  | a => [a, b] | b => [c] | c => [d, e] | d => [g, e] | e => [g, h]
  | g => [i, j] | h => [k] | i => [g] | j => [d, h] | k => [i, l] | l => [e]
  | z0 => [z1] | z1 => [z2] | z2 => [g, z3] | z3 => [z4] | z4 => [i, z1]

/-- The bits a letter codes: its parse token (`00`, `01`, `10`, or a lone `1`),
or for a sentinel the empty word or a lone trailing `0`. -/
def bits : Letter → List Bool
  | a | c | d | g => [false, false]
  | e | j | k => [false, true]
  | b | i => [true, false]
  | h | l => [true]
  | z0 | z1 | z3 => []
  | z2 | z4 => [false]

/-- What `step` writes for the bits of a letter: `00 ↦ 0010`, `01 ↦ 011`,
`10 ↦ 000`, and a lone letter is copied. -/
def img : Letter → List Bool
  | a | c | d | g => [false, false, true, false]
  | e | j | k => [false, true, true]
  | b | i => [false, false, false]
  | h | l => [true]
  | z0 | z1 | z3 => []
  | z2 | z4 => [false]

/-- The bit left pending, when the next iterate is parsed, just before the
image of this letter. -/
def pre : Letter → List Bool
  | a | b | i | z0 => []
  | c | d | e | h | j | l | z1 | z2 | z3 => [false]
  | g | k | z4 => [true]

/-- The bit left pending, when the next iterate is parsed, just after the
image of this letter. -/
def post : Letter → List Bool
  | a | h | l | z0 | z1 | z2 | z3 | z4 => []
  | b | c | d | g | i => [false]
  | e | j | k => [true]

/-- The admissible adjacent pairs of letters. -/
def adj : Letter → Letter → Bool
  | a, z0 | a, b | b, z1 | b, c | c, z2 | c, d | d, e | d, h | e, g | e, k
  | g, z2 | g, z3 | g, d | g, e | g, h | h, i | i, z1 | i, j | i, l | j, z4
  | j, g | j, k | k, g | l, i => true
  | _, _ => false

/-- The sentinel letters. -/
def isEnd : Letter → Bool
  | z0 | z1 | z2 | z3 | z4 => true
  | _ => false

end Letter

open Letter (sub bits img pre post adj isEnd)

/-- The substitution extended to words. -/
def S (V : List Letter) : List Letter := V.flatMap sub

/-- Bit length of a word over `Letter`. -/
def len (V : List Letter) : ℕ := (V.flatMap bits).length

/-- The coding word of the `n`-th iterate. -/
def W (n : ℕ) : List Letter := S^[n] [Letter.a, Letter.z0]

/-! ## Finite checks on letters -/

/-- Retokenization of one image: the pending bit followed by the image of a
letter is the coding of its substituted letters followed by the new pending
bit. -/
theorem tele_letter : ∀ x : Letter, pre x ++ img x = (sub x).flatMap bits ++ post x := by
  intro x; cases x <;> decide

/-- Along an admissible pair the pending bits agree. -/
theorem adj_post : ∀ x y : Letter, adj x y = true → post x = pre y := by
  intro x y; cases x <;> cases y <;> decide

/-- Admissible pairs are closed under the substitution. -/
theorem adj_closed : ∀ x y : Letter, adj x y = true →
    List.IsChain (fun u v => adj u v = true) (sub x ++ sub y) := by
  intro x y; cases x <;> cases y <;> decide

/-- The image of a single letter is admissible. -/
theorem sub_chain : ∀ x : Letter, List.IsChain (fun u v => adj u v = true) (sub x) := by
  intro x; cases x <;> decide

/-- The length identity `ℓ(σ⁷x) + ℓ(σ⁴x) = 2ℓ(σ⁶x)` on every letter. -/
theorem len_rec_letter : ∀ x : Letter,
    len (S^[7] [x]) + len (S^[4] [x]) = 2 * len (S^[6] [x]) := by
  intro x; cases x <;> decide

/-- The substitution of a sentinel ends with a sentinel. -/
theorem end_sub : ∀ z : Letter, isEnd z = true →
    ∃ (c : List Letter) (z' : Letter), sub z = c ++ [z'] ∧ isEnd z' = true := by
  intro z hz
  cases z <;> simp only [Letter.isEnd, Bool.false_eq_true] at hz
  · exact ⟨[], .z1, rfl, rfl⟩
  · exact ⟨[], .z2, rfl, rfl⟩
  · exact ⟨[.g], .z3, rfl, rfl⟩
  · exact ⟨[], .z4, rfl, rfl⟩
  · exact ⟨[.i], .z1, rfl, rfl⟩

/-- Nothing is pending after a sentinel. -/
theorem post_end : ∀ z : Letter, isEnd z = true → post z = [] := by
  intro z; cases z <;> decide

/-! ## `step` on admissible words -/

/-- `step` on the bits of a single letter. -/
theorem step_bits : ∀ x : Letter, step (bits x) = img x := by
  intro x; cases x <;> rfl

/-- `step` consumes the bits of the first letter of an admissible pair as one
token. -/
theorem step_bits_pair : ∀ (x y : Letter) (t : List Bool), adj x y = true →
    step (bits x ++ (bits y ++ t)) = img x ++ step (bits y ++ t) := by
  intro x y t hxy
  cases x <;> cases y <;> simp only [Letter.adj, Bool.false_eq_true] at hxy <;> rfl

/-- On an admissible word, `step` acts letter by letter. -/
theorem step_flatMap : ∀ V : List Letter, V.IsChain (fun u v => adj u v = true) →
    step (V.flatMap bits) = V.flatMap img
  | [], _ => rfl
  | [x], _ => by simpa using step_bits x
  | x :: y :: V, hc => by
      rw [List.isChain_cons_cons] at hc
      have ih := step_flatMap (y :: V) hc.2
      simp only [List.flatMap_cons] at ih ⊢
      rw [step_bits_pair x y _ hc.1, ih]

/-- On an admissible word, the images retokenize as the coding of the
substituted word, up to the pending bits at both ends. -/
theorem tele : ∀ (x : Letter) (V : List Letter),
    (x :: V).IsChain (fun u v => adj u v = true) →
    pre x ++ (x :: V).flatMap img =
      (S (x :: V)).flatMap bits ++ post ((x :: V).getLast (List.cons_ne_nil x V))
  | x, [], _ => by simpa [S] using tele_letter x
  | x, y :: V, hc => by
      rw [List.isChain_cons_cons] at hc
      have ih := tele y V hc.2
      rw [List.getLast_cons (List.cons_ne_nil y V)]
      simp only [S, List.flatMap_cons, List.flatMap_append] at ih ⊢
      rw [← List.append_assoc, tele_letter x, adj_post x y hc.1, List.append_assoc, ih]
      simp only [List.append_assoc]

/-- The substitution preserves admissibility. -/
theorem chain_S : ∀ V : List Letter, V.IsChain (fun u v => adj u v = true) →
    (S V).IsChain (fun u v => adj u v = true)
  | [], _ => by simp [S]
  | [x], _ => by simpa [S] using sub_chain x
  | x :: y :: V, hc => by
      rw [List.isChain_cons_cons] at hc
      have ih := chain_S (y :: V) hc.2
      have hne : sub y ≠ [] := by cases y <;> simp [Letter.sub]
      have hih : (sub y ++ S V).IsChain (fun u v => adj u v = true) := by
        simpa [S] using ih
      have key := List.IsChain.append_overlap (adj_closed x y hc.1) hih hne
      simpa [S, List.append_assoc] using key

/-! ## The coding words -/

/-- One more substitution gives the next coding word. -/
theorem W_succ (n : ℕ) : W (n + 1) = S (W n) := Function.iterate_succ_apply' _ _ _

/-- Every coding word is admissible. -/
theorem W_chain : ∀ n, (W n).IsChain (fun u v => adj u v = true)
  | 0 => by decide
  | n + 1 => by rw [W_succ]; exact chain_S _ (W_chain n)

/-- Every coding word starts with `a` and ends with a sentinel. -/
theorem W_shape : ∀ n, ∃ (U : List Letter) (z : Letter),
    W n = Letter.a :: (U ++ [z]) ∧ isEnd z = true
  | 0 => ⟨[], .z0, rfl, rfl⟩
  | n + 1 => by
      obtain ⟨U, z, hW, hz⟩ := W_shape n
      obtain ⟨c, z', hsub, hz'⟩ := end_sub z hz
      refine ⟨Letter.b :: (S U ++ c), z', ?_, hz'⟩
      rw [W_succ, hW]
      simp only [S, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil,
        hsub]
      simp [Letter.sub]

/-- The `n`-th iterate is the bit coding of the `n`-th coding word. -/
theorem w_eq : ∀ n, w n = (W n).flatMap bits
  | 0 => rfl
  | n + 1 => by
      have hstep : w (n + 1) = step (w n) := Function.iterate_succ_apply' _ _ _
      obtain ⟨U, z, hW, hz⟩ := W_shape n
      have hch := W_chain n
      rw [hstep, w_eq n, step_flatMap _ hch, W_succ, hW]
      rw [hW] at hch
      have ht := tele Letter.a (U ++ [z]) hch
      have hl : (Letter.a :: (U ++ [z])).getLast (List.cons_ne_nil _ _) = z := by
        simp
      rw [hl, post_end z hz] at ht
      simpa [Letter.pre] using ht

/-! ## Lengths -/

/-- Iterated substitution distributes over concatenation. -/
theorem iterate_S_append : ∀ (j : ℕ) (U V : List Letter),
    S^[j] (U ++ V) = S^[j] U ++ S^[j] V
  | 0, _, _ => rfl
  | j + 1, U, V => by
      simp only [Function.iterate_succ_apply']
      rw [iterate_S_append j U V]
      simp [S, List.flatMap_append]

/-- Iterated substitution fixes the empty word. -/
theorem iterate_S_nil (j : ℕ) : S^[j] [] = [] :=
  Function.iterate_fixed (f := S) rfl j

/-- Bit length is additive. -/
theorem len_append (U V : List Letter) : len (U ++ V) = len U + len V := by
  simp [len, List.flatMap_append]

/-- The length identity `ℓ(σ⁷V) + ℓ(σ⁴V) = 2ℓ(σ⁶V)` on every word. -/
theorem len_rec_word : ∀ V : List Letter,
    len (S^[7] V) + len (S^[4] V) = 2 * len (S^[6] V)
  | [] => by simp only [iterate_S_nil]; rfl
  | x :: V => by
      rw [← List.singleton_append, iterate_S_append, iterate_S_append, iterate_S_append,
        len_append, len_append, len_append]
      have hx := len_rec_letter x
      have hV := len_rec_word V
      omega

/-- The length of the `n`-th iterate is the bit length of its coding word. -/
theorem length_w (n : ℕ) : (w n).length = len (W n) := by
  rw [w_eq]; rfl

/-- `W (n + j)` is `W n` substituted `j` more times. -/
theorem W_add (n j : ℕ) : W (n + j) = S^[j] (W n) := by
  rw [W, W, add_comm, Function.iterate_add_apply]

/-- The iterate lengths satisfy `|w (n+7)| + |w (n+4)| = 2 |w (n+6)|`, i.e.
`a(m) = 2a(m-1) - a(m-3)` for `m ≥ 7`. -/
theorem length_rec (n : ℕ) :
    (w (n + 7)).length + (w (n + 4)).length = 2 * (w (n + 6)).length := by
  rw [length_w, length_w, length_w, W_add n 7, W_add n 4, W_add n 6]
  exact len_rec_word (W n)

/-! ## The conjecture -/

/-- **Kimberling's conjecture (A289107, Jun 28 2017), proved.**
Verbatim: "Conjecture:  a(n) is the number of letters (0's and 1's) in the
n-th iterate of the mapping 00->0010, 01->011, 10->000, starting with 00; see
A289104."  Here `w n` is the `n`-th iterate of Mathematica's `StringReplace`
with those rules, starting from `00`, and `a` is A289107 as defined by its
NAME line; the length is cast to `ℤ`, where `a` takes its values. -/
theorem length_eq_a : ∀ n : ℕ, ((w n).length : ℤ) = a n
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | 4 => by decide
  | 5 => by decide
  | 6 => by decide
  | m + 7 => by
      have h7 := length_rec m
      have h6 := length_eq_a (m + 6)
      have h4 := length_eq_a (m + 4)
      have ha : a (m + 7) = 2 * a (m + 6) - a (m + 4) := rfl
      rw [ha, ← h6, ← h4]
      omega

/-- The Fibonacci form of A289107: `a(n) + 3 = 5 F(n+1)` for `n ≠ 1`
(Colin Barker's Binet formula, stated in the entry for `n > 1`; it also holds
at `n = 0`).  The value `n = 1` is a genuine exception: `a(1) + 3 = 7`. -/
theorem a_add_three : ∀ n : ℕ, n ≠ 1 → a n + 3 = 5 * (Nat.fib (n + 1) : ℤ)
  | 0, _ => by decide
  | 1, h1 => absurd rfl h1
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | n + 5, _ => by
      have h4 := a_add_three (n + 4) (by omega)
      have h2 := a_add_three (n + 2) (by omega)
      have ha : a (n + 5) = 2 * a (n + 4) - a (n + 2) := rfl
      have f6 : Nat.fib (n + 6) = Nat.fib (n + 4) + Nat.fib (n + 5) := Nat.fib_add_two
      have f5 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := Nat.fib_add_two
      rw [ha]
      push_cast [f6, f5] at h4 h2 ⊢
      linarith

/-- **The "equivalently" form of the conjecture, proved.**  The `n`-th iterate
of `00->0010, 01->011, 10->000` from `00` has `5 F(n+1) - 3` letters for every
`n ≠ 1` (stated without subtraction), where `F` is the Fibonacci sequence. -/
theorem length_add_three_eq_five_mul_fib (n : ℕ) (hn : n ≠ 1) :
    (w n).length + 3 = 5 * Nat.fib (n + 1) := by
  have h := a_add_three n hn
  rw [← length_eq_a n] at h
  exact_mod_cast h

-- The exception at `n = 1` is real: `w 1 = 0010` has 4 letters, `5 F(2) - 3 = 2`.
example : (w 1).length + 3 ≠ 5 * Nat.fib 2 := by decide

end Candidates.A289107LengthIterateParsing
