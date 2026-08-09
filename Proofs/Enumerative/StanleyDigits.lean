import Mathlib

/-!
# The Stanley sequence A003278: greedy 3-AP-avoidance = base-3 digits in {0,1}

**OEIS A003278** (Szekeres's sequence, Stanley sequence S(1)): `1, 2, 4, 5, 10, 11, 13, 14,
28, …` — simultaneously described as

* the greedy increasing sequence starting `1, 2` that avoids every nontrivial 3-term
  arithmetic progression, and
* `a(n) − 1` written in ternary equals `n − 1` written in binary; equivalently the terms are
  exactly `m + 1` for those `m` whose base-3 digits all lie in `{0, 1}` (A005836).

This file formalizes the greedy definition (`stanleyGreedy`, via `Nat.find` over the
Mathlib predicate `ThreeAPFree`), the digit closed form (`stanleyDigits`, via
`Nat.ofDigits 3 (Nat.digits 2 n)`), and proves them equal
(`stanleyGreedy_eq_stanleyDigits`).  On top of the closed form it proves the
identities conjectured by L. Edson Jeffery (OEIS, Nov 2015) and Arie Bos (OEIS, Aug 2022),
stated multiplicatively (never with `Nat` division):

* `3 * stanleyGreedy n = a191107 n + 2` where `a191107` enumerates the increasing
  sequence generated from `1` by `x ↦ 3x − 2` and `x ↦ 3x + 1` (**A191107**);
* `6 * stanleyGreedy n = a055246 n + 5` where `a055246` enumerates the increasing
  sequence generated from `1` by `x ↦ 3x − 2` and `x ↦ 3x + 4` (**A055246**, whose OEIS
  definition is via the Cantor middle-third erased intervals; we formalize the
  rule-generated description conjectured for it by Jeffery, which is the form the
  identity chain uses);
* Bos: `a191107 n = stanleyGreedy (2 * n)` (1-indexed: `A191107(n) = A003278(2n − 1)`).

Indexing convention: everything is 0-indexed, so `stanleyGreedy n = A003278(n+1)`,
`a191107 n = A191107(n+1)`, `a055246 n = A055246(n+1)`.  The rule-generated sets are
inductive predicates (`MemA191107`, `MemA055246`) with the `3x − 2` rule encoded
subtraction-free as `z + 1 ∈ S → 3z + 1 ∈ S`.  Their enumerations are pinned by
strict monotonicity + range equality, by uniqueness of strictly monotone
enumerations, and by `Nat.nth`.

Ground-truth data for all checks below was pulled live from
`oeis show A003278`, `oeis show A191107`, `oeis show A055246` (2026-07-29).

Attribution note (literature sweep, 2026-07-29): the greedy = digits
characterization is classical — the standard citation is A. M. Odlyzko and
R. P. Stanley, *Some curious sequences constructed with the greedy
algorithm* (unpublished Bell Labs memorandum, 1978); the observation
traces to Szekeres.  The Jeffery (2015) and Bos (2022) identities are
labeled "Conjecture" in the OEIS entries with no published proof, but the
closed-form PARI programs in the same entries (Ryde 2021, van Tol 2026)
trivially imply them — the labels are stale.  The proofs here are the
first rigorous ones we know of, but are not claimed as novel results. -/

set_option autoImplicit false

/-! ## The binary-to-ternary reencoding and its arithmetic -/

/-- Reinterpret the binary digits of `n` as ternary digits: `binToTernary n` is the number
whose base-3 expansion equals the base-2 expansion of `n`.  Its range is exactly the set of
naturals with base-3 digits in `{0, 1}` (sums of distinct powers of 3, OEIS A005836), see
`mem_range_binToTernary`. -/
def binToTernary (n : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 n)

/-- `binToTernary 0 = 0`. -/
theorem binToTernary_zero : binToTernary 0 = 0 := by
  simp [binToTernary]

/-- Appending binary digit `0` triples the ternary value. -/
theorem binToTernary_two_mul (n : ℕ) : binToTernary (2 * n) = 3 * binToTernary n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [binToTernary]
  · unfold binToTernary
    rw [Nat.digits_def' (b := 2) one_lt_two (by omega)]
    have h1 : 2 * n % 2 = 0 := by omega
    have h2 : 2 * n / 2 = n := by omega
    rw [h1, h2, Nat.ofDigits_cons]
    omega

/-- Appending binary digit `1` triples the ternary value and adds one. -/
theorem binToTernary_two_mul_add_one (n : ℕ) :
    binToTernary (2 * n + 1) = 3 * binToTernary n + 1 := by
  unfold binToTernary
  rw [Nat.digits_def' (b := 2) one_lt_two (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2, Nat.ofDigits_cons]
  omega

/-- `binToTernary 1 = 1`. -/
theorem binToTernary_one : binToTernary 1 = 1 := by
  have h := binToTernary_two_mul_add_one 0
  simpa [binToTernary_zero] using h

/-- Every natural splits off a low binary digit compatibly with `binToTernary`. -/
theorem binToTernary_bit (p : ℕ) :
    ∃ p' b : ℕ, b ≤ 1 ∧ p = 2 * p' + b ∧ binToTernary p = 3 * binToTernary p' + b := by
  rcases Nat.even_or_odd' p with ⟨p', hp | hp⟩
  · refine ⟨p', 0, Nat.zero_le 1, by omega, ?_⟩
    rw [hp, binToTernary_two_mul]
    omega
  · refine ⟨p', 1, le_rfl, by omega, ?_⟩
    rw [hp, binToTernary_two_mul_add_one]

/-- Bounded-induction workhorse for strict monotonicity of `binToTernary`. -/
theorem binToTernary_lt_binToTernary :
    ∀ N m n : ℕ, n ≤ N → m < n → binToTernary m < binToTernary n := by
  intro N
  induction N with
  | zero => intro m n hn hmn; omega
  | succ N ih =>
    intro m n hn hmn
    obtain ⟨m', bm, hbm, hmeq, hTm⟩ := binToTernary_bit m
    obtain ⟨n', bn, hbn, hneq, hTn⟩ := binToTernary_bit n
    rcases (show m' < n' ∨ (m' = n' ∧ bm < bn) by omega) with h | ⟨heq, hb⟩
    · have h1 : n' ≤ N := by omega
      have h2 := ih m' n' h1 h
      omega
    · subst heq
      omega

/-- `binToTernary` is strictly monotone; it therefore enumerates its range in
increasing order. -/
theorem binToTernary_strictMono : StrictMono binToTernary :=
  fun m n h => binToTernary_lt_binToTernary n m n le_rfl h

/-- Bounded-induction workhorse: the range of `binToTernary` contains no nontrivial
3-term arithmetic progression, in the strong digitwise form.  The proof is induction on
the binary bit decomposition; `omega` performs the mod-3 digit comparison. -/
theorem binToTernary_ap_aux :
    ∀ N p q r : ℕ, p + q + r ≤ N →
      binToTernary p + binToTernary r = 2 * binToTernary q → p = q ∧ r = q := by
  intro N
  induction N with
  | zero =>
    intro p q r hle h
    omega
  | succ N ih =>
    intro p q r hle h
    obtain ⟨p', bp, hbp, hpeq, hTp⟩ := binToTernary_bit p
    obtain ⟨q', bq, hbq, hqeq, hTq⟩ := binToTernary_bit q
    obtain ⟨r', br, hbr, hreq, hTr⟩ := binToTernary_bit r
    rw [hTp, hTr, hTq] at h
    have key : binToTernary p' + binToTernary r' = 2 * binToTernary q' ∧
        bp = bq ∧ br = bq := by
      interval_cases bp <;> interval_cases bq <;> interval_cases br <;> omega
    have hsum : p' + q' + r' ≤ N := by omega
    obtain ⟨hk1, hk2, hk3⟩ := key
    obtain ⟨h1, h2⟩ := ih p' q' r' hsum hk1
    omega

/-- If `binToTernary p`, `binToTernary q`, `binToTernary r` form a (possibly trivial)
arithmetic progression then `p = q = r`: images of distinct points never average. -/
theorem binToTernary_add_eq_two_mul {p q r : ℕ}
    (h : binToTernary p + binToTernary r = 2 * binToTernary q) : p = q ∧ r = q :=
  binToTernary_ap_aux (p + q + r) p q r le_rfl h

/-! ## The range of `binToTernary`: base-3 digits in `{0, 1}` -/

/-- Any ternary digit list with entries `≤ 1` evaluates into the range of
`binToTernary` (no trailing-zero canonicity needed). -/
theorem exists_binToTernary_eq_ofDigits :
    ∀ L : List ℕ, (∀ d ∈ L, d ≤ 1) → ∃ b, binToTernary b = Nat.ofDigits 3 L := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simp [binToTernary_zero]⟩
  | cons d L ihL =>
    intro hL
    obtain ⟨b, hb⟩ := ihL fun x hx => hL x (List.mem_cons_of_mem d hx)
    have hd : d ≤ 1 := hL d List.mem_cons_self
    interval_cases d
    · refine ⟨2 * b, ?_⟩
      rw [binToTernary_two_mul, hb, Nat.ofDigits_cons]
      omega
    · refine ⟨2 * b + 1, ?_⟩
      rw [binToTernary_two_mul_add_one, hb, Nat.ofDigits_cons]
      omega

/-- **Digit characterization of the range**: `m` is a value of `binToTernary` iff every
base-3 digit of `m` is `0` or `1` (OEIS A005836). -/
theorem mem_range_binToTernary {m : ℕ} :
    m ∈ Set.range binToTernary ↔ ∀ d ∈ Nat.digits 3 m, d ≤ 1 := by
  constructor
  · rintro ⟨n, rfl⟩ d hd
    have hdig : Nat.digits 3 (Nat.ofDigits 3 (Nat.digits 2 n)) = Nat.digits 2 n :=
      Nat.digits_ofDigits 3 (by norm_num) _
        (fun l hl => by have := Nat.digits_lt_base one_lt_two hl; omega)
        (fun hne => Nat.getLast_digit_ne_zero 2 (Nat.digits_ne_nil_iff_ne_zero.mp hne))
    simp only [binToTernary] at hd
    rw [hdig] at hd
    have := Nat.digits_lt_base one_lt_two hd
    omega
  · intro h
    obtain ⟨b, hb⟩ := exists_binToTernary_eq_ofDigits _ h
    exact ⟨b, by rw [hb, Nat.ofDigits_digits]⟩

/-! ## The averaging witnesses `keepOnes` and `capDigits`

For `m` outside the range of `binToTernary` (some base-3 digit equals 2) the numbers
`keepOnes m` (digits: `0↦0, 1↦1, 2↦0`) and `capDigits m` (digits: `0↦0, 1↦1, 2↦1`) satisfy
`keepOnes m + m = 2 * capDigits m` with both witnesses in the range and `capDigits m < m`.
This is the classical reason the greedy sequence can never take a value `m + 1` with a
`2`-digit in `m`. -/

/-- Replace every base-3 digit `2` of `m` by `0` (keep the `1`s). -/
def keepOnes (m : ℕ) : ℕ :=
  Nat.ofDigits 3 ((Nat.digits 3 m).map fun d => if d = 1 then 1 else 0)

/-- Cap every base-3 digit of `m` at `1` (replace `2`s by `1`s). -/
def capDigits (m : ℕ) : ℕ :=
  Nat.ofDigits 3 ((Nat.digits 3 m).map fun d => min d 1)

/-- The digitwise averaging identity: `keepOnes m + m = 2 * capDigits m`.
Digitwise: `0 + 0 = 2·0`, `1 + 1 = 2·1`, `0 + 2 = 2·1`, with no carries. -/
theorem keepOnes_add_self (m : ℕ) : keepOnes m + m = 2 * capDigits m := by
  have key : ∀ L : List ℕ, (∀ d ∈ L, d < 3) →
      Nat.ofDigits 3 (L.map fun d => if d = 1 then 1 else 0) + Nat.ofDigits 3 L =
        2 * Nat.ofDigits 3 (L.map fun d => min d 1) := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons d L ihL =>
      intro hL
      have hd : d < 3 := hL d List.mem_cons_self
      have ih := ihL fun x hx => hL x (List.mem_cons_of_mem d hx)
      simp only [List.map_cons, Nat.ofDigits_cons]
      have hstep : (if d = 1 then 1 else 0) + d = 2 * min d 1 := by
        interval_cases d <;> norm_num
      omega
  have h := key (Nat.digits 3 m) fun d hd => Nat.digits_lt_base (by norm_num) hd
  rw [Nat.ofDigits_digits 3 m] at h
  simpa only [keepOnes, capDigits] using h

/-- Mapping a digitwise-dominated function over a digit list can only shrink the value. -/
theorem ofDigits_map_le (f : ℕ → ℕ) (hf : ∀ d, f d ≤ d) :
    ∀ L : List ℕ, Nat.ofDigits 3 (L.map f) ≤ Nat.ofDigits 3 L := by
  intro L
  induction L with
  | nil => simp
  | cons d L ih =>
    simp only [List.map_cons, Nat.ofDigits_cons]
    have := hf d
    omega

/-- `capDigits m ≤ m`. -/
theorem capDigits_le (m : ℕ) : capDigits m ≤ m := by
  have h := ofDigits_map_le (fun d => min d 1) (fun d => min_le_left d 1) (Nat.digits 3 m)
  rw [Nat.ofDigits_digits 3 m] at h
  simpa only [capDigits] using h

/-- `keepOnes m ≤ m`. -/
theorem keepOnes_le (m : ℕ) : keepOnes m ≤ m := by
  have h := ofDigits_map_le (fun d => if d = 1 then 1 else 0)
    (fun d => by split <;> omega) (Nat.digits 3 m)
  rw [Nat.ofDigits_digits 3 m] at h
  simpa only [keepOnes] using h

/-- `keepOnes m` lies in the range of `binToTernary`: its digits are all `0` or `1`. -/
theorem keepOnes_mem_range (m : ℕ) : keepOnes m ∈ Set.range binToTernary := by
  obtain ⟨b, hb⟩ := exists_binToTernary_eq_ofDigits
    ((Nat.digits 3 m).map fun d => if d = 1 then 1 else 0)
    (fun d hd => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hd
      split <;> omega)
  exact ⟨b, by rw [hb]; rfl⟩

/-- `capDigits m` lies in the range of `binToTernary`: its digits are all `0` or `1`. -/
theorem capDigits_mem_range (m : ℕ) : capDigits m ∈ Set.range binToTernary := by
  obtain ⟨b, hb⟩ := exists_binToTernary_eq_ofDigits
    ((Nat.digits 3 m).map fun d => min d 1)
    (fun d hd => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hd
      exact min_le_right x 1)
  exact ⟨b, by rw [hb]; rfl⟩

/-- Base-3 unfolding of `capDigits`. -/
theorem capDigits_recurrence (k d : ℕ) (hd : d < 3) (h0 : 0 < 3 * k + d) :
    capDigits (3 * k + d) = 3 * capDigits k + min d 1 := by
  simp only [capDigits]
  rw [Nat.digits_def' (b := 3) (by norm_num) h0]
  have h1 : (3 * k + d) % 3 = d := by omega
  have h2 : (3 * k + d) / 3 = k := by omega
  rw [h1, h2]
  simp only [List.map_cons, Nat.ofDigits_cons]
  omega

/-- If capping the digits of `m` at `1` does not change `m`, then `m` was already a
value of `binToTernary`. -/
theorem mem_range_of_capDigits_eq :
    ∀ m : ℕ, capDigits m = m → m ∈ Set.range binToTernary := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact ⟨0, binToTernary_zero⟩
    · obtain ⟨k, d, hd, hkd⟩ : ∃ k d, d < 3 ∧ m = 3 * k + d :=
        ⟨m / 3, m % 3, by omega, by omega⟩
      subst hkd
      rw [capDigits_recurrence k d hd hpos] at hm
      have hck : capDigits k ≤ k := capDigits_le k
      have hdle : d ≤ 1 ∧ capDigits k = k := by omega
      obtain ⟨b, hb⟩ := ih k (by omega) hdle.2
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
      · exact ⟨2 * b, by rw [binToTernary_two_mul, hb]; omega⟩
      · exact ⟨2 * b + 1, by rw [binToTernary_two_mul_add_one, hb]⟩

/-- Outside the range of `binToTernary`, capping digits strictly shrinks: the middle
averaging witness sits strictly below `m`. -/
theorem capDigits_lt_of_not_mem_range {m : ℕ} (h : m ∉ Set.range binToTernary) :
    capDigits m < m := by
  rcases Nat.lt_or_ge (capDigits m) m with hlt | hge
  · exact hlt
  · exact absurd (mem_range_of_capDigits_eq m (le_antisymm (capDigits_le m) hge)) h

/-! ## The digit closed form of the Stanley sequence -/

/-- Digit closed form of the Stanley sequence A003278 (0-indexed:
`stanleyDigits n = A003278(n+1)`): the base-3 digits of `stanleyDigits n − 1` are the
base-2 digits of `n`. -/
def stanleyDigits (n : ℕ) : ℕ := binToTernary n + 1

/-- `stanleyDigits 0 = 1`. -/
theorem stanleyDigits_zero : stanleyDigits 0 = 1 := by
  simp [stanleyDigits, binToTernary_zero]

/-- `stanleyDigits` is strictly monotone. -/
theorem stanleyDigits_strictMono : StrictMono stanleyDigits := fun m n h => by
  simp only [stanleyDigits]
  have := binToTernary_strictMono h
  omega

/-- The values of the digit closed form form a 3-AP-free set (Mathlib's
`ThreeAPFree`): three values that average must come from a single index. -/
theorem threeAPFree_range_stanleyDigits : ThreeAPFree (Set.range stanleyDigits) := by
  rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ c ⟨k, rfl⟩ h
  simp only [stanleyDigits] at h
  have h' : binToTernary i + binToTernary k = 2 * binToTernary j := by omega
  obtain ⟨h1, -⟩ := binToTernary_add_eq_two_mul h'
  rw [h1]

/-! ## The greedy definition -/

/-- `k` is a good greedy extension of the finite set `s`: it exceeds every element of `s`
and inserting it keeps the set 3-AP-free (Mathlib's `ThreeAPFree`). -/
def IsGoodExt (s : Finset ℕ) (k : ℕ) : Prop :=
  (∀ a ∈ s, a < k) ∧ ThreeAPFree (↑(insert k s) : Set ℕ)

/-- `IsGoodExt s` is decidable, so the greedy step can be computed with `Nat.find`. -/
instance (s : Finset ℕ) : DecidablePred (IsGoodExt s) := fun k =>
  inferInstanceAs (Decidable ((∀ a ∈ s, a < k) ∧ ThreeAPFree (↑(insert k s) : Set ℕ)))

/-- Every 3-AP-free finite set admits a good greedy extension (e.g. `2 * max + 1`):
a fresh element above twice the maximum can never complete a progression. -/
theorem exists_isGoodExt {s : Finset ℕ} (hs : ThreeAPFree (↑s : Set ℕ)) :
    ∃ k, IsGoodExt s k := by
  have hM : ∀ x ∈ s, x ≤ s.sup id := fun x hx => Finset.le_sup (f := id) hx
  refine ⟨2 * s.sup id + 1, fun a ha => ?_, ?_⟩
  · have := hM a ha
    omega
  · intro a ha b hb c hc habc
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb hc
    rcases ha with rfl | ha <;> rcases hb with rfl | hb <;> rcases hc with rfl | hc
    · rfl
    · rfl
    · have := hM b hb; omega
    · have := hM b hb; have := hM c hc; omega
    · have := hM a ha; omega
    · have := hM a ha; have := hM c hc; omega
    · have := hM a ha; have := hM b hb; omega
    · exact hs (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr hc) habc

/-- The greedy step: the least good extension of a 3-AP-free finite set. -/
def nextTerm (s : Finset ℕ) (hs : ThreeAPFree (↑s : Set ℕ)) : ℕ :=
  Nat.find (exists_isGoodExt hs)

/-- The base of the greedy recursion: `{1}` is 3-AP-free. -/
theorem threeAPFree_greedyBase : ThreeAPFree (↑({1} : Finset ℕ) : Set ℕ) := by
  simp

/-- The greedy prefix sets bundled with the invariant that each is 3-AP-free; the
step inserts the least good extension, whose defining property restores the invariant. -/
def greedyAux : ℕ → {s : Finset ℕ // ThreeAPFree (↑s : Set ℕ)}
  | 0 => ⟨{1}, threeAPFree_greedyBase⟩
  | n + 1 =>
    ⟨insert (nextTerm (greedyAux n).1 (greedyAux n).2) (greedyAux n).1,
      (Nat.find_spec (exists_isGoodExt (greedyAux n).2)).2⟩

/-- The greedy prefix set `{a 0, …, a n}` of the Stanley sequence. -/
def greedySet (n : ℕ) : Finset ℕ := (greedyAux n).1

/-- Invariant: every greedy prefix set is 3-AP-free. -/
theorem greedySet_threeAPFree (n : ℕ) : ThreeAPFree (↑(greedySet n) : Set ℕ) :=
  (greedyAux n).2

/-- **The greedy Stanley sequence** (OEIS A003278, 0-indexed:
`stanleyGreedy n = A003278(n+1)`): starts at `1`, and each next term is the least
number exceeding all previous terms whose insertion keeps the prefix 3-AP-free. -/
def stanleyGreedy : ℕ → ℕ
  | 0 => 1
  | n + 1 => nextTerm (greedySet n) (greedySet_threeAPFree n)

/-- `stanleyGreedy 0 = 1`. -/
theorem stanleyGreedy_zero : stanleyGreedy 0 = 1 := rfl

/-- The greedy prefix set at `0`. -/
theorem greedySet_zero : greedySet 0 = {1} := rfl

/-- The greedy prefix set grows by exactly the next greedy term. -/
theorem greedySet_succ (n : ℕ) :
    greedySet (n + 1) = insert (stanleyGreedy (n + 1)) (greedySet n) := rfl

/-- Greediness, packaged: `stanleyGreedy (n+1)` is the least `k` that exceeds every
element of the prefix and keeps it 3-AP-free. -/
theorem isLeast_stanleyGreedy_succ (n : ℕ) :
    IsLeast {k | (∀ a ∈ greedySet n, a < k) ∧
      ThreeAPFree (↑(insert k (greedySet n)) : Set ℕ)} (stanleyGreedy (n + 1)) :=
  ⟨Nat.find_spec (exists_isGoodExt (greedySet_threeAPFree n)),
    fun _ hk => Nat.find_min' _ hk⟩

/-! ## The main theorem: greedy = digits -/

/-- **Key step**: on the prefix `{stanleyDigits 0, …, stanleyDigits n}` the greedy
choice is exactly `stanleyDigits (n+1)`.  Admissibility is 3-AP-freeness of the digit
form's range; minimality uses the averaging witnesses `keepOnes`/`capDigits` to shoot
down every smaller candidate. -/
theorem nextTerm_key {n : ℕ} {s : Finset ℕ} (hs : ThreeAPFree (↑s : Set ℕ))
    (hset : s = (Finset.range (n + 1)).image stanleyDigits) :
    nextTerm s hs = stanleyDigits (n + 1) := by
  subst hset
  simp only [nextTerm]
  rw [Nat.find_eq_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- every prefix element is smaller
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact stanleyDigits_strictMono (Finset.mem_range.mp hi)
  · -- inserting stanleyDigits (n+1) stays 3-AP-free: everything is in the range
    refine ThreeAPFree.mono ?_ threeAPFree_range_stanleyDigits
    intro z hz
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      Finset.mem_image] at hz
    rcases hz with rfl | ⟨i, -, rfl⟩
    · exact ⟨n + 1, rfl⟩
    · exact ⟨i, rfl⟩
  · -- minimality: no smaller k is a good extension
    intro k hk hgood
    obtain ⟨hlt, hfree⟩ := hgood
    have hn_mem : stanleyDigits n ∈ (Finset.range (n + 1)).image stanleyDigits :=
      Finset.mem_image_of_mem _ (Finset.self_mem_range_succ n)
    have h1 : stanleyDigits n < k := hlt _ hn_mem
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [stanleyDigits] at h1 hk
    have hm1 : binToTernary n < m := by omega
    have hm2 : m < binToTernary (n + 1) := by omega
    have hnr : m ∉ Set.range binToTernary := by
      rintro ⟨b, rfl⟩
      have hb1 : n < b := binToTernary_strictMono.lt_iff_lt.mp hm1
      have hb2 : b < n + 1 := binToTernary_strictMono.lt_iff_lt.mp hm2
      omega
    obtain ⟨i, hi⟩ := keepOnes_mem_range m
    obtain ⟨j, hj⟩ := capDigits_mem_range m
    have hxm : keepOnes m ≤ m := keepOnes_le m
    have hym : capDigits m < m := capDigits_lt_of_not_mem_range hnr
    have havg : keepOnes m + m = 2 * capDigits m := keepOnes_add_self m
    have hiN : i < n + 1 :=
      binToTernary_strictMono.lt_iff_lt.mp
        (show binToTernary i < binToTernary (n + 1) by omega)
    have hjN : j < n + 1 :=
      binToTernary_strictMono.lt_iff_lt.mp
        (show binToTernary j < binToTernary (n + 1) by omega)
    have hmemi : stanleyDigits i ∈
        (↑(insert (m + 1) ((Finset.range (n + 1)).image stanleyDigits)) : Set ℕ) := by
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
      exact Or.inr (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hiN))
    have hmemj : stanleyDigits j ∈
        (↑(insert (m + 1) ((Finset.range (n + 1)).image stanleyDigits)) : Set ℕ) := by
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
      exact Or.inr (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hjN))
    have hmemk : m + 1 ∈
        (↑(insert (m + 1) ((Finset.range (n + 1)).image stanleyDigits)) : Set ℕ) := by
      rw [Finset.coe_insert]
      exact Set.mem_insert _ _
    have happ : stanleyDigits i + (m + 1) = stanleyDigits j + stanleyDigits j := by
      simp only [stanleyDigits]
      omega
    have heq := hfree hmemi hmemj hmemk happ
    simp only [stanleyDigits] at heq
    -- keepOnes m = capDigits m forces m = capDigits m < m
    omega

/-- The greedy prefix sets are exactly the images of initial segments under the digit
closed form. -/
theorem greedySet_eq_image : ∀ n : ℕ, greedySet n = (Finset.range (n + 1)).image stanleyDigits := by
  intro n
  induction n with
  | zero =>
    rw [Finset.range_one, Finset.image_singleton, stanleyDigits_zero]
    exact greedySet_zero
  | succ n ih =>
    rw [greedySet_succ, show stanleyGreedy (n + 1) =
        nextTerm (greedySet n) (greedySet_threeAPFree n) from rfl,
      nextTerm_key (greedySet_threeAPFree n) ih, ih]
    conv_rhs => rw [Finset.range_add_one, Finset.image_insert]

/-- Pointwise form of the main theorem. -/
theorem stanleyGreedy_apply (n : ℕ) : stanleyGreedy n = stanleyDigits n := by
  cases n with
  | zero => rw [stanleyGreedy_zero, stanleyDigits_zero]
  | succ n => exact nextTerm_key (greedySet_threeAPFree n) (greedySet_eq_image n)

/-- **Main theorem (OEIS A003278)**: the greedy increasing 3-AP-avoiding sequence
starting from `1` coincides with the base-3-digits-in-`{0,1}` closed form:
`stanleyGreedy n = binToTernary n + 1`, i.e. `a(n) − 1` in ternary is `n − 1` in binary. -/
theorem stanleyGreedy_eq_stanleyDigits : stanleyGreedy = stanleyDigits :=
  funext stanleyGreedy_apply

/-- The main theorem, fully unfolded: the `n`-th greedy term is the base-2 digit string
of `n` read in base 3, plus one. -/
theorem stanleyGreedy_eq (n : ℕ) :
    stanleyGreedy n = Nat.ofDigits 3 (Nat.digits 2 n) + 1 :=
  stanleyGreedy_apply n

/-- Set form of the digit characterization: `m + 1` is a greedy Stanley term iff every
base-3 digit of `m` is `0` or `1` (i.e. `m ∈ A005836`).  Stated on `m + 1` to avoid
`Nat` subtraction. -/
theorem stanleyGreedy_eq_add_one_iff {m : ℕ} :
    (∃ n, stanleyGreedy n = m + 1) ↔ ∀ d ∈ Nat.digits 3 m, d ≤ 1 := by
  constructor
  · rintro ⟨n, hn⟩
    rw [stanleyGreedy_apply] at hn
    simp only [stanleyDigits] at hn
    exact mem_range_binToTernary.mp ⟨n, by omega⟩
  · intro h
    obtain ⟨b, hb⟩ := mem_range_binToTernary.mpr h
    refine ⟨b, ?_⟩
    rw [stanleyGreedy_apply]
    simp only [stanleyDigits]
    omega

/-- The greedy Stanley sequence is strictly increasing. -/
theorem stanleyGreedy_strictMono : StrictMono stanleyGreedy := by
  rw [stanleyGreedy_eq_stanleyDigits]
  exact stanleyDigits_strictMono

/-- The set of greedy Stanley terms is 3-AP-free. -/
theorem threeAPFree_range_stanleyGreedy : ThreeAPFree (Set.range stanleyGreedy) := by
  rw [stanleyGreedy_eq_stanleyDigits]
  exact threeAPFree_range_stanleyDigits

/-- Ralf Stephan's even-index recurrence (multiplicative form):
`a(2n) + 2 = 3 · a(n)` for the 0-indexed greedy sequence. -/
theorem stanleyGreedy_two_mul (n : ℕ) :
    stanleyGreedy (2 * n) + 2 = 3 * stanleyGreedy n := by
  rw [stanleyGreedy_apply, stanleyGreedy_apply]
  simp only [stanleyDigits, binToTernary_two_mul]
  ring

/-- Ralf Stephan's odd-index recurrence (multiplicative form):
`a(2n+1) + 1 = 3 · a(n)` for the 0-indexed greedy sequence. -/
theorem stanleyGreedy_two_mul_add_one (n : ℕ) :
    stanleyGreedy (2 * n + 1) + 1 = 3 * stanleyGreedy n := by
  rw [stanleyGreedy_apply, stanleyGreedy_apply]
  simp only [stanleyDigits, binToTernary_two_mul_add_one]
  ring

/-! ## The rule-generated sequences A191107 and A055246 -/

/-- Membership in **A191107** as a rule-generated set: `1` is a member, and each member
`y` generates `3y − 2` and `3y + 1`.  The subtraction rule is encoded without `Nat`
subtraction: a member of the form `z + 1` generates `3z + 1 = 3(z+1) − 2`. -/
inductive MemA191107 : ℕ → Prop where
  /-- `1` is a member. -/
  | one : MemA191107 1
  /-- `3y − 2` rule: if `y = z + 1` is a member, so is `3z + 1 = 3y − 2`. -/
  | left {z : ℕ} : MemA191107 (z + 1) → MemA191107 (3 * z + 1)
  /-- `3y + 1` rule: if `x` is a member, so is `3x + 1`. -/
  | right {x : ℕ} : MemA191107 x → MemA191107 (3 * x + 1)

/-- Membership in **A055246** as a rule-generated set (L. Edson Jeffery's description of
the Cantor middle-third interval sequence): `1` is a member, and each member `y`
generates `3y − 2` and `3y + 4`, subtraction-free as for `MemA191107`. -/
inductive MemA055246 : ℕ → Prop where
  /-- `1` is a member. -/
  | one : MemA055246 1
  /-- `3y − 2` rule: if `y = z + 1` is a member, so is `3z + 1 = 3y − 2`. -/
  | left {z : ℕ} : MemA055246 (z + 1) → MemA055246 (3 * z + 1)
  /-- `3y + 4` rule: if `x` is a member, so is `3x + 4`. -/
  | right {x : ℕ} : MemA055246 x → MemA055246 (3 * x + 4)

/-- Closed-form enumeration of A191107 (0-indexed: `a191107 n = A191107(n+1)`). -/
def a191107 (n : ℕ) : ℕ := 3 * binToTernary n + 1

/-- Closed-form enumeration of A055246 (0-indexed: `a055246 n = A055246(n+1)`). -/
def a055246 (n : ℕ) : ℕ := 6 * binToTernary n + 1

/-- Every value of `a191107` is generated by the A191107 rules. -/
theorem memA191107_a191107 : ∀ n : ℕ, MemA191107 (a191107 n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨n', hn | hn⟩
    · subst hn
      rcases Nat.eq_zero_or_pos n' with rfl | hpos
      · simpa [a191107, binToTernary_zero] using MemA191107.one
      · have h := ih n' (by omega)
        simp only [a191107] at h ⊢
        rw [binToTernary_two_mul]
        exact MemA191107.left (z := 3 * binToTernary n') h
    · subst hn
      have h := ih n' (by omega)
      simp only [a191107] at h ⊢
      rw [binToTernary_two_mul_add_one]
      exact MemA191107.right (x := 3 * binToTernary n' + 1) h

/-- Every value of `a055246` is generated by the A055246 rules. -/
theorem memA055246_a055246 : ∀ n : ℕ, MemA055246 (a055246 n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨n', hn | hn⟩
    · subst hn
      rcases Nat.eq_zero_or_pos n' with rfl | hpos
      · simpa [a055246, binToTernary_zero] using MemA055246.one
      · have h := ih n' (by omega)
        simp only [a055246] at h ⊢
        rw [binToTernary_two_mul]
        have hr : 6 * (3 * binToTernary n') + 1 = 3 * (6 * binToTernary n') + 1 := by ring
        rw [hr]
        exact MemA055246.left (z := 6 * binToTernary n') h
    · subst hn
      have h := ih n' (by omega)
      simp only [a055246] at h ⊢
      rw [binToTernary_two_mul_add_one]
      have hr : 6 * (3 * binToTernary n' + 1) + 1 =
          3 * (6 * binToTernary n' + 1) + 4 := by ring
      rw [hr]
      exact MemA055246.right (x := 6 * binToTernary n' + 1) h

/-- `a191107` enumerates exactly the rule-generated set A191107. -/
theorem range_a191107 : Set.range a191107 = {m | MemA191107 m} := by
  ext m
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, rfl⟩
    exact memA191107_a191107 n
  · intro hm
    induction hm with
    | one => exact ⟨0, by simp [a191107, binToTernary_zero]⟩
    | @left z hz ihz =>
      obtain ⟨b, hb⟩ := ihz
      refine ⟨2 * b, ?_⟩
      simp only [a191107] at hb ⊢
      rw [binToTernary_two_mul]
      omega
    | @right x hx ihx =>
      obtain ⟨b, hb⟩ := ihx
      refine ⟨2 * b + 1, ?_⟩
      simp only [a191107] at hb ⊢
      rw [binToTernary_two_mul_add_one]
      omega

/-- `a055246` enumerates exactly the rule-generated set A055246. -/
theorem range_a055246 : Set.range a055246 = {m | MemA055246 m} := by
  ext m
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, rfl⟩
    exact memA055246_a055246 n
  · intro hm
    induction hm with
    | one => exact ⟨0, by simp [a055246, binToTernary_zero]⟩
    | @left z hz ihz =>
      obtain ⟨b, hb⟩ := ihz
      refine ⟨2 * b, ?_⟩
      simp only [a055246] at hb ⊢
      rw [binToTernary_two_mul]
      omega
    | @right x hx ihx =>
      obtain ⟨b, hb⟩ := ihx
      refine ⟨2 * b + 1, ?_⟩
      simp only [a055246] at hb ⊢
      rw [binToTernary_two_mul_add_one]
      omega

/-- `a191107` is strictly monotone. -/
theorem a191107_strictMono : StrictMono a191107 := fun m n h => by
  simp only [a191107]
  have := binToTernary_strictMono h
  omega

/-- `a055246` is strictly monotone. -/
theorem a055246_strictMono : StrictMono a055246 := fun m n h => by
  simp only [a055246]
  have := binToTernary_strictMono h
  omega

/-- Uniqueness: any strictly monotone enumeration of the rule-generated set A191107
equals `a191107`; so `a191107` *is* "the increasing sequence generated by the rules". -/
theorem eq_a191107_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f)
    (hr : Set.range f = {m | MemA191107 m}) : f = a191107 :=
  (hf.range_inj a191107_strictMono).mp (hr.trans range_a191107.symm)

/-- Uniqueness: any strictly monotone enumeration of the rule-generated set A055246
equals `a055246`. -/
theorem eq_a055246_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f)
    (hr : Set.range f = {m | MemA055246 m}) : f = a055246 :=
  (hf.range_inj a055246_strictMono).mp (hr.trans range_a055246.symm)

/-- The rule-generated set A191107 is infinite. -/
theorem infinite_setOf_memA191107 : {m | MemA191107 m}.Infinite := by
  rw [← range_a191107]
  exact Set.infinite_range_of_injective a191107_strictMono.injective

/-- The rule-generated set A055246 is infinite. -/
theorem infinite_setOf_memA055246 : {m | MemA055246 m}.Infinite := by
  rw [← range_a055246]
  exact Set.infinite_range_of_injective a055246_strictMono.injective

/-- `Nat.nth` form of the enumeration: the `n`-th smallest member of the A191107 rule
set is `a191107 n`. -/
theorem nth_memA191107 : Nat.nth MemA191107 = a191107 :=
  eq_a191107_of_strictMono (Nat.nth_strictMono infinite_setOf_memA191107)
    (Nat.range_nth_of_infinite infinite_setOf_memA191107)

/-- `Nat.nth` form of the enumeration: the `n`-th smallest member of the A055246 rule
set is `a055246 n`. -/
theorem nth_memA055246 : Nat.nth MemA055246 = a055246 :=
  eq_a055246_of_strictMono (Nat.nth_strictMono infinite_setOf_memA055246)
    (Nat.range_nth_of_infinite infinite_setOf_memA055246)

/-! ## The Jeffery and Bos identities -/

/-- **Jeffery's identity** (OEIS A003278, Nov 2015), multiplicative form:
`3 · A003278(n) = A191107(n) + 2` (0-indexed here). -/
theorem three_mul_stanleyGreedy (n : ℕ) : 3 * stanleyGreedy n = a191107 n + 2 := by
  rw [stanleyGreedy_apply]
  simp only [stanleyDigits, a191107]
  ring

/-- **Jeffery's identity** (OEIS A003278, Nov 2015), multiplicative form:
`6 · A003278(n) = A055246(n) + 5` (0-indexed here). -/
theorem six_mul_stanleyGreedy (n : ℕ) : 6 * stanleyGreedy n = a055246 n + 5 := by
  rw [stanleyGreedy_apply]
  simp only [stanleyDigits, a055246]
  ring

/-- Jeffery's A055246–A191107 link (OEIS A055246, Nov 2015), multiplicative form:
`A055246(n) + 1 = 2 · A191107(n)`. -/
theorem a055246_add_one (n : ℕ) : a055246 n + 1 = 2 * a191107 n := by
  simp only [a055246, a191107]
  ring

/-- **Bos's identity** (OEIS A191107, Aug 2022): `A191107(n) = A003278(2n − 1)`;
0-indexed and subtraction-free this reads `a191107 n = stanleyGreedy (2n)`. -/
theorem a191107_eq_stanleyGreedy_two_mul (n : ℕ) :
    a191107 n = stanleyGreedy (2 * n) := by
  rw [stanleyGreedy_apply]
  simp only [stanleyDigits, a191107, binToTernary_two_mul]

/-! ## Ground checks against the OEIS data

The sequence values below are transcribed verbatim from `oeis show A003278`,
`oeis show A191107` and `oeis show A055246` (fetched 2026-07-29).

**Trust note**: `stanleyGreedy` (via `Nat.find`), `Nat.digits` (via well-founded
recursion) and hence `binToTernary`, `keepOnes`, `capDigits` do not reduce in the
kernel, so these ground checks use `native_decide`, which enlarges the trusted base
to the compiler.  `native_decide` is used **only** in this `example` block — every
named theorem above depends solely on `propext`/`Classical.choice`/`Quot.sound`. -/

/-- Ground check: the first 32 greedy Stanley terms match OEIS A003278. -/
example : (List.range 32).map stanleyGreedy =
    [1, 2, 4, 5, 10, 11, 13, 14, 28, 29, 31, 32, 37, 38, 40, 41,
     82, 83, 85, 86, 91, 92, 94, 95, 109, 110, 112, 113, 118, 119, 121, 122] := by
  native_decide

/-- Ground check: the digit closed form matches A003278 − 1 = A005836. -/
example : (List.range 17).map binToTernary =
    [0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31, 36, 37, 39, 40, 81] := by
  native_decide

/-- Ground check: the first 16 terms of `a191107` match OEIS A191107. -/
example : (List.range 16).map a191107 =
    [1, 4, 10, 13, 28, 31, 37, 40, 82, 85, 91, 94, 109, 112, 118, 121] := by
  native_decide

/-- Ground check: the first 16 terms of `a055246` match OEIS A055246. -/
example : (List.range 16).map a055246 =
    [1, 7, 19, 25, 55, 61, 73, 79, 163, 169, 181, 187, 217, 223, 235, 241] := by
  native_decide

/-- Ground check: the averaging witnesses at `m = 5` (ternary `12`):
`keepOnes 5 = 3`, `capDigits 5 = 4`, and `3 + 5 = 2 · 4`. -/
example : keepOnes 5 = 3 ∧ capDigits 5 = 4 := by native_decide

/-- Ground check of Jeffery's identity at `n = 8`: `3 · 28 = 82 + 2`. -/
example : 3 * stanleyGreedy 8 = a191107 8 + 2 := by native_decide

/-- Ground check of Bos's identity at `n = 3`: `a191107 3 = 13 = stanleyGreedy 6`. -/
example : a191107 3 = 13 ∧ stanleyGreedy 6 = 13 := by native_decide

/-! ## Kernel-checked witnesses and satisfiability of hypotheses -/

/-- Kernel-checked rule derivations: `4 = 3·1 + 1`, `10 = 3·4 − 2`, `13 = 3·4 + 1`,
`28 = 3·10 − 2` are members of the A191107 rule set. -/
example : MemA191107 4 := MemA191107.right MemA191107.one

/-- `10 = 3·4 − 2` via the subtraction-free `left` rule with `z = 3`. -/
example : MemA191107 10 := MemA191107.left (z := 3) (MemA191107.right MemA191107.one)

/-- `13 = 3·4 + 1`. -/
example : MemA191107 13 := MemA191107.right (MemA191107.right MemA191107.one)

/-- `7 = 3·1 + 4` and `25 = 3·7 + 4` are members of the A055246 rule set. -/
example : MemA055246 25 := MemA055246.right (MemA055246.right MemA055246.one)

/-- Sanity: `2` is *not* an A191107 member (all members are `≡ 1 (mod 3)` or `1`). -/
example : ¬ MemA191107 2 := by
  have key : ∀ m, MemA191107 m → m ≠ 2 := by
    intro m hm
    induction hm with
    | one => omega
    | @left z hz ih => omega
    | @right x hx ih => omega
  exact fun h => key 2 h rfl

/-- Satisfiability of `mem_range_binToTernary` in the negative direction: `2` has the
single ternary digit `2`, so it is not a `binToTernary` value.  This also jointly
instantiates the hypothesis of `capDigits_lt_of_not_mem_range`. -/
theorem two_not_mem_range_binToTernary : (2 : ℕ) ∉ Set.range binToTernary := by
  rw [mem_range_binToTernary]
  intro h
  have h2 : Nat.digits 3 2 = [2] := by
    rw [Nat.digits_def' (b := 3) (by norm_num) (by norm_num)]
    norm_num
  have := h 2 (by rw [h2]; exact List.mem_cons_self)
  omega

/-- Joint instantiation of the hypotheses of `capDigits_lt_of_not_mem_range`. -/
example : capDigits 2 < 2 := capDigits_lt_of_not_mem_range two_not_mem_range_binToTernary

/-- Joint instantiation of the hypotheses of `exists_isGoodExt` (the greedy step is
never stuck), at the base prefix `{1}`. -/
example : ∃ k, IsGoodExt {1} k := exists_isGoodExt threeAPFree_greedyBase

/-- Joint instantiation of the hypotheses of `binToTernary_add_eq_two_mul`: the trivial
progression at `p = q = r = 1`. -/
example : (1 : ℕ) = 1 ∧ (1 : ℕ) = 1 :=
  binToTernary_add_eq_two_mul (p := 1) (q := 1) (r := 1) (by rw [binToTernary_one])

/-- Joint instantiation of the hypotheses of `eq_a191107_of_strictMono` (and via
`nth_memA191107` of the `Nat.nth` machinery): `a191107` itself satisfies them. -/
example : a191107 = a191107 := eq_a191107_of_strictMono a191107_strictMono range_a191107

/-- Joint instantiation of the hypotheses of `nextTerm_key` at `n = 0`: the singleton
prefix `{1}` is `(Finset.range 1).image stanleyDigits`, and the key step yields
`stanleyDigits 1 = 2`. -/
example : nextTerm (greedySet 0) (greedySet_threeAPFree 0) = stanleyDigits 1 :=
  nextTerm_key (greedySet_threeAPFree 0) (greedySet_eq_image 0)

