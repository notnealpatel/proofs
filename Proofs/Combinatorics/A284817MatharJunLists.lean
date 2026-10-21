/-
# A284817 — Mathar: `2n - 1 - A284776(n) = A189664(n-1)`

## OEIS source (retrieved with `oeis show A284817` and the live `/internal`
## page, 2026-10-21)

```
%N A284817  a(n) = 2n - 1 - A284776(n).
%O A284817  1
%S A284817  0,0,1,0,0,0,1,0,1,0,0,1,0,0,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,1,...
%F A284817  a(n) = 2n - 1 - A284776.
%F A284817  Conjecture: a(n) = A189664(n-1). - _R. J. Mathar_, Jun 21 2025
%t A284817  s = Nest[Flatten[# /. {0 -> {0, 1}, 1 -> {0, 0, 1, 1}}] &, {0}, 7]; (* A284775 *)
%t A284817  u = Flatten[Position[s, 0]] ; (* A284776 *)
%A A284817  Clark Kimberling, Apr 14 2017

%N A284775  Fixed point of the morphism 0 -> 01, 1 -> 0011.
%N A284776  Positions of 0 in A284775; complement of A284777.
%S A284776  1,3,4,7,9,11,12,15,16,19,21,22,25,27,28,31,33,35,36,39,...
%N A189664  Fixed point of the morphism 0->010, 1->001.
%O A189664  1
%S A189664  0,1,0,0,0,1,0,1,0,0,1,0,0,1,0,0,0,1,0,1,...
%F A189664  a(3*k-2) = 0, a(3*k-1) = 1 - a(k), a(3*k) = a(k) for k >= 1, a(0) = 0.
```

The conjecture as stated by the triage: for all `n ≥ 1`,
`2n - 1 - A284776(n) = A189664(n-1)`, with `A189664(0) = 0` (the value the
A189664 entry itself fixes in its formula line).

## Literature status (triage)

Open: no proof in the entry or the literature as far as the triage could tell.
Triage evidence: verified for `1 ≤ n < 60000`. Re-validated here (Python,
2026-10-21): verified for `1 ≤ n < 200000`, together with the structural
identity used below.

## Result of this module

The conjecture is proved for every `n ≥ 1`, with no remaining `sorry`.

**Proof idea.** Write `w` for A284775 and `b` for A189664 (offset 1), and let
`ψ(0) = 10`, `ψ(1) = 01`. Then `w = 0 · ψ(b)`, i.e. `w(1) = 0` and
`(w(2j), w(2j+1)) = ψ(b(j))`. This follows from the letter identity
`ψ(μ(x)) · 1 = 1 · σ(ψ(x))` (`σ` the A284775 morphism, `μ` the A189664
morphism), which gives the finite-level identity
`0 · ψ(μ^k(0)) = σ^(k+1)(0) · 0` by induction on `k`. Hence every pair
`(2j, 2j+1)` (1-indexed) contains exactly one zero of `w`, located at
`2j + 1 - b(j)`, so the `(j+1)`-st zero sits at `2(j+1) - 1 - b(j)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A284817MatharJunLists

/-! ## Definition layer

Fixed points of prolongable morphisms on the alphabet `{0, 1} ⊆ ℕ` are defined
through the finite iterates `f^k(0)`. Since `f(0)` begins with `0`, each iterate
is a prefix of the next (`morphIter_succ_eq_append`), so letter `i` (0-indexed)
of the fixed point is letter `i` of any iterate long enough to contain it;
`fixedLetter` reads it off `f^(i+1)(0)`, which is long enough for both
morphisms used here (`lt_length_morphIter_sigma`, `lt_length_morphIter_mu`). -/

/-- The A284775 morphism `0 ↦ 01`, `1 ↦ 0011` (letters other than `0` are
treated as `1`; only `0` and `1` occur). -/
def sigma (a : ℕ) : List ℕ := if a = 0 then [0, 1] else [0, 0, 1, 1]

/-- The A189664 morphism `0 ↦ 010`, `1 ↦ 001` (letters other than `0` are
treated as `1`; only `0` and `1` occur). -/
def mu (a : ℕ) : List ℕ := if a = 0 then [0, 1, 0] else [0, 0, 1]

/-- Auxiliary morphism `0 ↦ 10`, `1 ↦ 01` used in the proof only:
A284775 is `0` followed by the `psi`-image of A189664. -/
def psi (a : ℕ) : List ℕ := if a = 0 then [1, 0] else [0, 1]

/-- The finite iterate `f^k(0)` of a morphism `f` applied to the word `0`. -/
def morphIter (f : ℕ → List ℕ) : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (morphIter f k).flatMap f

/-- Letter `i` (0-indexed) of the fixed point of `f` starting with `0`, read off
the iterate `f^(i+1)(0)`. -/
def fixedLetter (f : ℕ → List ℕ) (i : ℕ) : ℕ := (morphIter f (i + 1)).getD i 0

/-- A284775 (offset 1): the fixed point of `0 ↦ 01`, `1 ↦ 0011`.
`A284775 0` is a junk value (equal to `A284775 1`) and is never used. -/
def A284775 (n : ℕ) : ℕ := fixedLetter sigma (n - 1)

/-- A284776 (offset 1): the `n`-th position (1-indexed, increasing) of a `0`
in A284775. `Nat.nth` is 0-indexed, so the `n`-th position is the `(n-1)`-st
element of `{i | A284775 (i + 1) = 0}`, shifted by one. `A284776 0` is a junk
value (equal to `A284776 1`); every statement below assumes `1 ≤ n`. -/
noncomputable def A284776 (n : ℕ) : ℕ := Nat.nth (fun i => A284775 (i + 1) = 0) (n - 1) + 1

/-- A189664 (offset 1): the fixed point of `0 ↦ 010`, `1 ↦ 001`, extended by
`A189664 0 = 0` as in the entry's formula line ("`a(0) = 0`"). -/
def A189664 : ℕ → ℕ
  | 0 => 0
  | n + 1 => fixedLetter mu n

/-- A284817 (offset 1): `a(n) = 2n - 1 - A284776(n)`, computed in `ℤ`. -/
noncomputable def A284817 (n : ℕ) : ℤ := 2 * (n : ℤ) - 1 - (A284776 n : ℤ)

/-! ## Ground truth against the listed terms -/

example : (List.range 30).map (fun n => A284775 (n + 1)) =
    [0,1,0,0,1,1,0,1,0,1,0,0,1,1,0,0,1,1,0,1,0,0,1,1,0,1,0,0,1,1] := by decide

example : (List.range 30).map (fun n => A189664 (n + 1)) =
    [0,1,0,0,0,1,0,1,0,0,1,0,0,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,1,0] := by decide

/-! ## Proof -/

/-- If `f 0` begins with `0`, each iterate `f^(k+1)(0)` extends `f^k(0)`. -/
theorem morphIter_succ_eq_append (f : ℕ → List ℕ) (r : List ℕ) (hf : f 0 = 0 :: r) (k : ℕ) :
    ∃ t, morphIter f (k + 1) = morphIter f k ++ t := by
  induction k with
  | zero => exact ⟨r, by simp [morphIter, hf]⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t.flatMap f, ?_⟩
    show (morphIter f (k + 1)).flatMap f = _
    conv_lhs => rw [ht, List.flatMap_append]
    rfl

/-- If `f 0` begins with `0`, letters of `f^m(0)` are stable under further iteration. -/
theorem getD_morphIter_mono (f : ℕ → List ℕ) (r : List ℕ) (hf : f 0 = 0 :: r) {m m' i : ℕ}
    (hmm : m ≤ m') (hi : i < (morphIter f m).length) :
    (morphIter f m').getD i 0 = (morphIter f m).getD i 0 := by
  induction m', hmm using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    obtain ⟨t, ht⟩ := morphIter_succ_eq_append f r hf k
    have hlen : (morphIter f m).length ≤ (morphIter f k).length := by
      clear ih ht t
      induction k, hk using Nat.le_induction with
      | base => exact le_rfl
      | succ k' _ ih' =>
        obtain ⟨t', ht'⟩ := morphIter_succ_eq_append f r hf k'
        rw [ht', List.length_append]; omega
    rw [ht, List.getD_append _ _ _ _ (by omega), ih]

/-- Letter identity lifted to words: `ψ(μ(u)) · 1 = 1 · σ(ψ(u))`. -/
theorem psi_mu_append_one (u : List ℕ) :
    (u.flatMap mu).flatMap psi ++ [1] = 1 :: (u.flatMap psi).flatMap sigma := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    simp only [List.flatMap_cons, List.flatMap_append, List.append_assoc]
    by_cases ha : a = 0
    · simp [ha, mu, psi, sigma, ih]
    · simp [ha, mu, psi, sigma, ih]

/-- Finite-level form of `A284775 = 0 · ψ(A189664)`: `0 · ψ(μ^k(0)) = σ^(k+1)(0) · 0`. -/
theorem zero_cons_psi_morphIter (k : ℕ) :
    0 :: (morphIter mu k).flatMap psi = morphIter sigma (k + 1) ++ [0] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 := psi_mu_append_one (morphIter mu k)
    have h2 : morphIter sigma (k + 2) ++ [0, 1] =
        [0, 1] ++ ((morphIter mu k).flatMap psi).flatMap sigma := by
      have := congrArg (fun l => l.flatMap sigma) ih
      simpa [morphIter, List.flatMap_append, sigma] using this.symm
    refine List.append_cancel_right (bs := [1]) ?_
    simp only [morphIter] at h1 h2 ⊢
    rw [List.cons_append, h1, List.append_assoc]
    simpa using h2.symm

/-- `ψ` doubles lengths. -/
theorem length_flatMap_psi (u : List ℕ) : (u.flatMap psi).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    by_cases ha : a = 0 <;>
      simp only [psi, ha, ↓reduceIte, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd] <;> ring

/-- `|μ^k(0)| = 3^k`. -/
theorem length_morphIter_mu (k : ℕ) : (morphIter mu k).length = 3 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have key : ∀ u : List ℕ, (u.flatMap mu).length = 3 * u.length := by
      intro u
      induction u with
      | nil => rfl
      | cons a u ihu =>
        rw [List.flatMap_cons, List.length_append, ihu, List.length_cons]
        by_cases ha : a = 0 <;>
          simp only [mu, ha, ↓reduceIte, List.length_cons, List.length_nil, zero_add,
            Nat.reduceAdd] <;> ring
    rw [morphIter, key, ih, pow_succ]; ring

/-- `|σ^(k+1)(0)| = 2 · 3^k`. -/
theorem length_morphIter_sigma_succ (k : ℕ) : (morphIter sigma (k + 1)).length = 2 * 3 ^ k := by
  have h := congrArg List.length (zero_cons_psi_morphIter k)
  rw [List.length_cons, length_flatMap_psi, length_morphIter_mu, List.length_append] at h
  simp only [List.length_singleton] at h
  omega

/-- `σ^(i+1)(0)` is long enough to contain letter `i`. -/
theorem lt_length_morphIter_sigma (i : ℕ) : i < (morphIter sigma (i + 1)).length := by
  rw [length_morphIter_sigma_succ]
  have := Nat.lt_pow_self (n := i) (show 1 < 3 by norm_num)
  omega

/-- `μ^(i+1)(0)` is long enough to contain letter `i`. -/
theorem lt_length_morphIter_mu (i : ℕ) : i < (morphIter mu (i + 1)).length := by
  rw [length_morphIter_mu]
  have := Nat.lt_pow_self (n := i + 1) (show 1 < 3 by norm_num)
  omega

/-- Letter `i` of the fixed point can be read off any iterate long enough to contain it. -/
theorem fixedLetter_eq_getD (f : ℕ → List ℕ) (r : List ℕ) (hf : f 0 = 0 :: r) {i m : ℕ}
    (hi1 : i < (morphIter f (i + 1)).length) (hi : i < (morphIter f m).length) :
    fixedLetter f i = (morphIter f m).getD i 0 := by
  unfold fixedLetter
  rw [← getD_morphIter_mono f r hf (le_max_left (i + 1) m) hi1,
    getD_morphIter_mono f r hf (le_max_right (i + 1) m) hi]

/-- Letters `2j` and `2j+1` of `ψ(u)` are the two letters of `ψ(u_j)`. -/
theorem getD_flatMap_psi (u : List ℕ) (j : ℕ) (hj : j < u.length) :
    (u.flatMap psi).getD (2 * j) 0 = (if u.getD j 0 = 0 then 1 else 0) ∧
    (u.flatMap psi).getD (2 * j + 1) 0 = (if u.getD j 0 = 0 then 0 else 1) := by
  induction u generalizing j with
  | nil => simp at hj
  | cons a u ih =>
    have hcons : (a :: u).flatMap psi =
        (if a = 0 then 1 else 0) :: (if a = 0 then 0 else 1) :: u.flatMap psi := by
      by_cases ha : a = 0 <;> simp [psi, ha]
    rw [hcons]
    cases j with
    | zero => simp
    | succ j =>
      have hj' : j < u.length := by simpa using hj
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
        List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
        List.getD_cons_succ]
      exact ih j hj'


/-- Structure of A284775 (0-indexed): letters `2j+1, 2j+2` are `ψ(b_j)`, where `b_j`
is letter `j` (0-indexed) of A189664. -/
theorem fixedLetter_sigma_odd_even (j : ℕ) :
    fixedLetter sigma (2 * j + 1) = (if fixedLetter mu j = 0 then 1 else 0) ∧
    fixedLetter sigma (2 * j + 2) = (if fixedLetter mu j = 0 then 0 else 1) := by
  have hlenS := length_morphIter_sigma_succ (j + 1)
  have hpow : j + 1 < 3 ^ (j + 1) := Nat.lt_pow_self (show 1 < 3 by norm_num)
  have hjM : j < (morphIter mu (j + 1)).length := lt_length_morphIter_mu j
  have hid := zero_cons_psi_morphIter (j + 1)
  have hgetS : ∀ i, i < (morphIter sigma (j + 1 + 1)).length →
      fixedLetter sigma i = (0 :: (morphIter mu (j + 1)).flatMap psi).getD i 0 := by
    intro i hi
    rw [fixedLetter_eq_getD sigma [1] rfl (lt_length_morphIter_sigma i) hi, hid,
      List.getD_append _ _ _ _ hi]
  obtain ⟨h0, h1⟩ := getD_flatMap_psi (morphIter mu (j + 1)) j hjM
  have hb : (morphIter mu (j + 1)).getD j 0 = fixedLetter mu j := rfl
  rw [hb] at h0 h1
  constructor
  · rw [hgetS (2 * j + 1) (by omega), List.getD_cons_succ, h0]
  · rw [hgetS (2 * j + 2) (by omega), show 2 * j + 2 = (2 * j + 1) + 1 by rfl,
      List.getD_cons_succ, h1]

/-- A284775 begins with `0`. -/
theorem fixedLetter_sigma_zero : fixedLetter sigma 0 = 0 := rfl

/-- Every letter of `μ^k(0)` is `0` or `1`. -/
theorem mem_morphIter_mu_le_one (k : ℕ) : ∀ x ∈ morphIter mu k, x ≤ 1 := by
  induction k with
  | zero => simp [morphIter]
  | succ k _ =>
    intro x hx
    rw [morphIter, List.mem_flatMap] at hx
    obtain ⟨a, _, hxa⟩ := hx
    by_cases ha : a = 0 <;>
      simp only [mu, ha, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false,
        or_self_left] at hxa <;> omega

/-- Every letter of A189664 is `0` or `1`. -/
theorem fixedLetter_mu_le_one (j : ℕ) : fixedLetter mu j ≤ 1 := by
  have hj := lt_length_morphIter_mu j
  simp only [fixedLetter, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact mem_morphIter_mu_le_one _ _ (List.getElem_mem _)

/-- Letter `i` (0-indexed) of A284775 is `0`. -/
def IsZeroPos (i : ℕ) : Prop := fixedLetter sigma i = 0

/-- Decidability of `IsZeroPos`, inherited from equality on `ℕ`. -/
instance : DecidablePred IsZeroPos := fun i => inferInstanceAs (Decidable (fixedLetter sigma i = 0))

/-- A284775 has exactly `j + 1` zeros among its first `2j + 1` letters. -/
theorem count_isZeroPos_odd (j : ℕ) : Nat.count IsZeroPos (2 * j + 1) = j + 1 := by
  induction j with
  | zero => rw [Nat.count_succ, Nat.count_zero]; simp [IsZeroPos, fixedLetter_sigma_zero]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := fixedLetter_sigma_odd_even j
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, Nat.count_succ, Nat.count_succ, ih]
    by_cases hb : fixedLetter mu j = 0
    · simp [IsZeroPos, h1, h2, hb]
    · simp [IsZeroPos, h1, h2, hb]

/-- The `(j+1)`-st zero of A284775 (0-indexed, 0-indexed position) is at `2j + 2 - b_j`. -/
theorem nth_isZeroPos_succ (j : ℕ) :
    Nat.nth IsZeroPos (j + 1) + fixedLetter mu j = 2 * j + 2 := by
  obtain ⟨h1, h2⟩ := fixedLetter_sigma_odd_even j
  have hc := count_isZeroPos_odd j
  by_cases hb : fixedLetter mu j = 0
  · have hp : IsZeroPos (2 * j + 2) := by simp [IsZeroPos, h2, hb]
    have hcount : Nat.count IsZeroPos (2 * j + 2) = j + 1 := by
      rw [show 2 * j + 2 = 2 * j + 1 + 1 by rfl, Nat.count_succ, hc]
      simp [IsZeroPos, h1, hb]
    rw [← hcount, Nat.nth_count hp, hb]
  · have hp : IsZeroPos (2 * j + 1) := by simp [IsZeroPos, h1, hb]
    have hb1 : fixedLetter mu j = 1 := by have := fixedLetter_mu_le_one j; omega
    rw [← hc, Nat.nth_count hp, hb1]

/-- The first zero of A284775 is at position `0` (0-indexed). -/
theorem nth_isZeroPos_zero : Nat.nth IsZeroPos 0 = 0 := by
  have hp : IsZeroPos 0 := fixedLetter_sigma_zero
  have hc : Nat.count IsZeroPos 0 = 0 := Nat.count_zero _
  have hn := Nat.nth_count hp
  rwa [hc] at hn


/-- The positions of zeros of A284775, 0-indexed: the predicate in the
definition of `A284776` is `IsZeroPos` (after the index shift). -/
theorem A284775_succ_eq_zero_iff (i : ℕ) : A284775 (i + 1) = 0 ↔ IsZeroPos i := by
  simp [A284775, IsZeroPos]

/-- Closed form of A284776: for `n ≥ 1`, `A284776 n + A189664 (n - 1) = 2n - 1`. -/
theorem A284776_add_A189664 (n : ℕ) (hn : 1 ≤ n) :
    A284776 n + A189664 (n - 1) = 2 * n - 1 := by
  have hpred : (fun i => A284775 (i + 1) = 0) = IsZeroPos :=
    funext fun i => propext (A284775_succ_eq_zero_iff i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold A284776
  rw [hpred]
  cases m with
  | zero => simp [nth_isZeroPos_zero, A189664]
  | succ j =>
    have h := nth_isZeroPos_succ j
    simp only [Nat.add_sub_cancel, A189664]
    omega

/-- **Mathar's conjecture (A284817, R. J. Mathar, Jun 21 2025), proved.**

For every `n ≥ 1`, `2n - 1 - A284776(n) = A189664(n-1)`, where A284776 lists the
positions of `0` in the fixed point A284775 of `0 ↦ 01`, `1 ↦ 0011`, A189664 is
the fixed point of `0 ↦ 010`, `1 ↦ 001` (offset 1), and `A189664(0) = 0`.
The difference is taken in `ℤ`. -/
theorem two_mul_sub_one_sub_A284776_eq_A189664 (n : ℕ) (hn : 1 ≤ n) :
    2 * (n : ℤ) - 1 - (A284776 n : ℤ) = (A189664 (n - 1) : ℤ) := by
  have h := A284776_add_A189664 n hn
  have h' : (A284776 n : ℤ) + (A189664 (n - 1) : ℤ) = 2 * (n : ℤ) - 1 := by
    have h2 : ((2 * n - 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := by omega
    rw [← h2, ← h]
    push_cast
    ring
  linarith

/-- **Mathar's conjecture in the entry's own wording**: `A284817(n) = A189664(n-1)`
for all `n ≥ 1`. -/
theorem A284817_eq_A189664 (n : ℕ) (hn : 1 ≤ n) : A284817 n = (A189664 (n - 1) : ℤ) :=
  two_mul_sub_one_sub_A284776_eq_A189664 n hn

/-! ## Ground truth for the position sequences (via the proved closed form) -/

example : (List.range 20).map (fun n => A284776 (n + 1)) =
    [1,3,4,7,9,11,12,15,16,19,21,22,25,27,28,31,33,35,36,39] := by
  have h : ∀ n, A284776 (n + 1) = 2 * (n + 1) - 1 - A189664 n := fun n => by
    have := A284776_add_A189664 (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    omega
  simp only [h]
  decide

/-- Non-vacuity: the hypothesis `1 ≤ n` is met, e.g. at `n = 3`, where both
sides equal `1`. -/
example : A284817 3 = 1 := by
  rw [A284817_eq_A189664 3 (by norm_num)]
  decide

end Candidates.A284817MatharJunLists
