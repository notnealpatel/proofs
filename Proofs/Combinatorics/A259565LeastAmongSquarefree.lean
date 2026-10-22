/-
# A259565 — the squarefree-mean greedy sequence

Reinhard Zumkeller (OEIS A259565, Jun 30 2015) conjectured that this
sequence permutes the odd numbers. It starts with `a(1) = 1`; each next
term is the least unused positive integer whose arithmetic mean with the
preceding term is an integer and squarefree.

## Proof outline

Infinite descent.  If some odd `m` never occurs, take the least one, an index
`N` after which every smaller odd number has occurred, and `K` the largest of
the first `N + 1` terms.  (i) No term after `N` has `(a + m)/2` squarefree,
since then the greedy rule would pick `m` next.  (ii) For every threshold
`T` and all large `c` there is `T < t ≤ c` with `t` and `t + c` both
squarefree: a counting argument in a residue class mod 4, using
`∑_{odd d ≥ 3} 1/d² ≤ 1/4`.  (iii) For a large term `y` this yields an
unused admissible candidate `b = 2t - m < y` with `(y-m)/2 = c`; by (i) the
greedy choice is not `b`, so the next term is below `b < y`.  Injectivity
then forces an infinite strictly decreasing run, which is impossible.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A259565LeastAmongSquarefree

/-! ## Definitions -/

/-- `x` is an admissible successor of the term `prev` given the set `used` of
terms so far: `x` is a positive integer, not yet used, and the mean
`(prev + x)/2` is an integer (`prev + x` is even) and squarefree. -/
def IsCand (used : Finset ℕ) (prev x : ℕ) : Prop :=
  0 < x ∧ x ∉ used ∧ Even (prev + x) ∧ Squarefree ((prev + x) / 2)

instance (used : Finset ℕ) (prev : ℕ) : DecidablePred (IsCand used prev) := fun x => by
  unfold IsCand; infer_instance

/-- An admissible successor always exists: take `x = 2p - prev` for a prime `p`
larger than `prev` and every used number. -/
theorem exists_isCand (used : Finset ℕ) (prev : ℕ) : ∃ x, IsCand used prev x := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (prev + used.sup id + 1)
  refine ⟨2 * p - prev, by omega, ?_, ?_, ?_⟩
  · intro h
    have hle : id (2 * p - prev) ≤ used.sup id := Finset.le_sup (f := id) h
    simp only [id] at hle
    omega
  · have hsum : prev + (2 * p - prev) = 2 * p := by omega
    rw [hsum]
    exact even_two_mul p
  · have hmean : (prev + (2 * p - prev)) / 2 = p := by omega
    rw [hmean]
    exact hpp.prime.squarefree

/-- The greedy successor: the least admissible successor of `prev` given `used`. -/
def next (used : Finset ℕ) (prev : ℕ) : ℕ := Nat.find (exists_isCand used prev)

/-- One greedy step on the state (last term, set of terms so far). -/
def stepState (s : ℕ × Finset ℕ) : ℕ × Finset ℕ :=
  (next s.2 s.1, insert (next s.2 s.1) s.2)

/-- `state k = (a(k+1), {a(1), …, a(k+1)})`. -/
def state : ℕ → ℕ × Finset ℕ
  | 0 => (1, {1})
  | n + 1 => stepState (state n)

/-- The sequence A259565 with OEIS offset 1: `a 1 = 1`, and `a (n+1)` is the least
admissible successor of `a n` given `{a 1, …, a n}` (see `a_succ`).  The value
`a 0 = 0` is a junk value outside the offset. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (state n).1

/-! ### Examples: listed terms -/

example : (List.range 8).map (fun n => a (n + 1)) = [1, 3, 7, 5, 9, 11, 15, 13] := by
  decide +kernel

/-- The state after the first eight terms `1, 3, 7, 5, 9, 11, 15, 13`. -/
theorem state_seven : state 7 = (13, {1, 3, 7, 5, 9, 11, 15, 13}) := by
  decide +kernel

/-- The ninth term is `a 9 = 17`. -/
example : a 9 = 17 := by
  show (stepState (state 7)).1 = 17
  rw [state_seven]
  decide +kernel

/-! ## Basic sequence lemmas -/

/-- The used set is the set of terms so far. -/
theorem state_snd (k : ℕ) :
    (state k).2 = (Finset.range (k + 1)).image (fun i => (state i).1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Finset.range_add_one, Finset.image_insert]
    show insert (state (k + 1)).1 (state k).2 = _
    rw [ih]

/-- The next term is an admissible successor. -/
theorem isCand_succ (k : ℕ) : IsCand (state k).2 (state k).1 (state (k + 1)).1 :=
  Nat.find_spec (exists_isCand (state k).2 (state k).1)

/-- Minimality of the greedy choice. -/
theorem succ_le_of_isCand (k x : ℕ) (hx : IsCand (state k).2 (state k).1 x) :
    (state (k + 1)).1 ≤ x :=
  Nat.find_min' (exists_isCand (state k).2 (state k).1) hx

/-- Every term is odd. -/
theorem state_odd (k : ℕ) : (state k).1 % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hev := (isCand_succ k).2.2.1
    rw [Nat.even_iff] at hev
    omega

/-- A new term differs from all previous terms. -/
theorem state_succ_ne (k j : ℕ) (hj : j ≤ k) : (state (k + 1)).1 ≠ (state j).1 := by
  intro h
  apply (isCand_succ k).2.1
  rw [state_snd, h]
  exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))

/-- The terms are pairwise distinct. -/
theorem state_injective : Function.Injective (fun k => (state k).1) := by
  intro i j hij
  simp only at hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact state_succ_ne k i (by omega) hij.symm
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact state_succ_ne k j (by omega) hij

/-! ## The counting lemma -/

/-- In the progression `4 * j + e` (`j < L`), at most `L / M + 1` terms are
divisible by a modulus `M` coprime to `4`. -/
theorem card_filter_dvd_le (L M e : ℕ) (hM : Nat.gcd M 4 = 1) :
    ((Finset.range L).filter (fun j => M ∣ 4 * j + e)).card ≤ L / M + 1 := by
  calc ((Finset.range L).filter (fun j => M ∣ 4 * j + e)).card
      ≤ (Finset.range (L / M + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun j => j / M)
        · intro j hj
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj
          simp only [Finset.coe_range, Set.mem_Iio]
          have hle : j / M ≤ L / M := Nat.div_le_div_right hj.1.le
          omega
        · intro j hj j' hj' hjj
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj hj'
          have h1 : 4 * j + e ≡ 4 * j' + e [MOD M] := by
            exact (Nat.modEq_zero_iff_dvd.2 hj.2).trans (Nat.modEq_zero_iff_dvd.2 hj'.2).symm
          have h2 : j ≡ j' [MOD M] :=
            Nat.ModEq.cancel_left_of_coprime hM (Nat.ModEq.add_right_cancel' e h1)
          have hjj' : j / M = j' / M := hjj
          rw [← Nat.div_add_mod j M, ← Nat.div_add_mod j' M, hjj', h2]
    _ = L / M + 1 := Finset.card_range _

/-- Telescoping bound: `∑_{i < D} 1/(2i+3)² ≤ 1/4 - 1/(4D+4)`. -/
theorem sum_inv_sq_le (D : ℕ) :
    ∑ i ∈ Finset.range D, (1 : ℚ) / ((2 * i + 3) ^ 2) ≤ 1 / 4 - 1 / (4 * (D : ℚ) + 4) := by
  induction D with
  | zero => norm_num
  | succ D ih =>
    rw [Finset.sum_range_succ]
    have key : (1 : ℚ) / ((2 * D + 3) ^ 2) ≤ 1 / (4 * D + 4) - 1 / (4 * ((D + 1 : ℕ) : ℚ) + 4) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      ring_nf
      nlinarith
    linarith


/-- A nonzero `n` not divisible by `4` nor by any odd square `(2i+3)²` with
`i < √n` is squarefree. -/
theorem squarefree_of_forall_not_dvd (n : ℕ) (hn0 : n ≠ 0) (hn4 : ¬ 4 ∣ n)
    (hn : ∀ i < Nat.sqrt n, ¬ (2 * i + 3) ^ 2 ∣ n) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hp' : p.Prime := hp
  rcases hp'.eq_two_or_odd with h2 | hodd
  · subst h2
    exact hn4 hpp
  · have h2 : 2 ≤ p := hp'.two_le
    have hle : p * p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpp
    have hsq : p ≤ Nat.sqrt n := Nat.le_sqrt.2 hle
    have hp3 : 2 * ((p - 3) / 2) + 3 = p := by omega
    apply hn ((p - 3) / 2) (by omega)
    rw [hp3, sq]
    exact hpp

/-- Key counting lemma: for every threshold `T` and all sufficiently large `c` there is
`T < t ≤ c` with both `t` and `t + c` squarefree. -/
theorem exists_squarefree_pair (T : ℕ) :
    ∃ C, ∀ c, C ≤ c → ∃ t, T < t ∧ t ≤ c ∧ Squarefree t ∧ Squarefree (t + c) := by
  refine ⟨4 * T + 2100, fun c hc => ?_⟩
  set r : ℕ := if c % 4 = 3 then 2 else 1 with hr_def
  have hr : (r = 1 ∧ c % 4 ≠ 3) ∨ (r = 2 ∧ c % 4 = 3) := by
    by_cases h : c % 4 = 3
    · right; simp [hr_def, h]
    · left; simp [hr_def, h]
  set q : ℕ := T / 4 + 1 with hq
  set L : ℕ := c / 4 - q - 1 with hL
  set D : ℕ := Nat.sqrt (2 * c) with hD
  let A : ℕ → Finset ℕ := fun i =>
    (Finset.range L).filter (fun j => (2 * i + 3) ^ 2 ∣ 4 * j + (4 * q + r))
  let B : ℕ → Finset ℕ := fun i =>
    (Finset.range L).filter (fun j => (2 * i + 3) ^ 2 ∣ 4 * j + (4 * q + r + c))
  let bad : Finset ℕ := (Finset.range D).biUnion (fun i => A i ∪ B i)
  have hcop : ∀ i : ℕ, Nat.gcd ((2 * i + 3) ^ 2) 4 = 1 := by
    intro i
    have hodd : Nat.Coprime (2 * i + 3) 2 := by
      rw [Nat.coprime_two_right]
      exact ⟨i + 1, by ring⟩
    have h4 : Nat.Coprime ((2 * i + 3) ^ 2) (2 ^ 2) := Nat.Coprime.pow 2 2 hodd
    exact h4
  have hAB : ∀ i, (A i ∪ B i).card ≤ 2 * (L / (2 * i + 3) ^ 2) + 2 := by
    intro i
    have hA : (A i).card ≤ L / (2 * i + 3) ^ 2 + 1 :=
      card_filter_dvd_le L ((2 * i + 3) ^ 2) (4 * q + r) (hcop i)
    have hB : (B i).card ≤ L / (2 * i + 3) ^ 2 + 1 :=
      card_filter_dvd_le L ((2 * i + 3) ^ 2) (4 * q + r + c) (hcop i)
    have hU := Finset.card_union_le (A i) (B i)
    omega
  have hbad_nat : bad.card ≤ ∑ i ∈ Finset.range D, (2 * (L / (2 * i + 3) ^ 2) + 2) :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => hAB i)
  have hbad : (bad.card : ℚ) ≤ L / 2 + 2 * D := by
    have h1 : (bad.card : ℚ) ≤ ∑ i ∈ Finset.range D, (2 * ((L : ℚ) / (2 * i + 3) ^ 2) + 2) := by
      calc (bad.card : ℚ) ≤ ((∑ i ∈ Finset.range D, (2 * (L / (2 * i + 3) ^ 2) + 2) : ℕ) : ℚ) := by
            exact_mod_cast hbad_nat
        _ = ∑ i ∈ Finset.range D, (2 * (((L / (2 * i + 3) ^ 2 : ℕ)) : ℚ) + 2) := by
            push_cast; rfl
        _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i _
            have hdiv := Nat.cast_div_le (α := ℚ) (m := L) (n := (2 * i + 3) ^ 2)
            push_cast at hdiv
            linarith
    have h2 : ∑ i ∈ Finset.range D, (2 * ((L : ℚ) / (2 * i + 3) ^ 2) + 2)
        = 2 * (L : ℚ) * ∑ i ∈ Finset.range D, (1 : ℚ) / ((2 * i + 3) ^ 2) + 2 * (D : ℚ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · ring
    have h3 := sum_inv_sq_le D
    have h4 : (0 : ℚ) ≤ 1 / (4 * (D : ℚ) + 4) := by positivity
    have hL0 : (0 : ℚ) ≤ L := by positivity
    rw [h2] at h1
    nlinarith
  have hDD : D * D ≤ 2 * c := Nat.sqrt_le (2 * c)
  have h32 : 32 * D ≤ c := by nlinarith
  have hLD : 4 * D < L := by omega
  have hlt : bad.card < (Finset.range L).card := by
    rw [Finset.card_range]
    have hltQ : (bad.card : ℚ) < L := by
      have hLDQ : (4 * D : ℚ) < L := by exact_mod_cast hLD
      linarith
    exact_mod_cast hltQ
  obtain ⟨j, hjL, hjbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hjL' : j < L := Finset.mem_range.1 hjL
  set t : ℕ := 4 * j + (4 * q + r) with ht
  have ht_le : t ≤ c := by omega
  refine ⟨t, by omega, ht_le, ?_, ?_⟩
  · apply squarefree_of_forall_not_dvd t (by omega) (by omega)
    intro i hi hdvd
    apply hjbad
    have hiD : i < D := lt_of_lt_of_le hi (Nat.sqrt_le_sqrt (by omega))
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hiD,
      Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hjL, hdvd⟩)⟩
  · apply squarefree_of_forall_not_dvd (t + c) (by omega) (by omega)
    intro i hi hdvd
    apply hjbad
    have hiD : i < D := lt_of_lt_of_le hi (Nat.sqrt_le_sqrt (by omega))
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hiD,
      Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hjL, ?_⟩)⟩
    rw [ht] at hdvd
    simpa [add_assoc] using hdvd


/-! ## The descent -/

/-- Every odd number occurs among the terms `(state k).1`. -/
theorem exists_state_eq (m : ℕ) (hm : m % 2 = 1) : ∃ k, (state k).1 = m := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  by_contra hnot
  push Not at hnot
  -- `N`: every smaller odd number occurs at an index `≤ N`.
  classical
  let f : ℕ → ℕ := fun m' =>
    if h : m' < m ∧ m' % 2 = 1 then Classical.choose (IH m' h.1 h.2) else 0
  let N : ℕ := (Finset.range m).sup f
  have hN : ∀ m' < m, m' % 2 = 1 → ∃ k ≤ N, (state k).1 = m' := by
    intro m' hm' hodd
    have hfm : f m' = Classical.choose (IH m' hm' hodd) := dif_pos ⟨hm', hodd⟩
    refine ⟨f m', Finset.le_sup (f := f) (Finset.mem_range.2 hm'), ?_⟩
    rw [hfm]
    exact Classical.choose_spec (IH m' hm' hodd)
  -- `K`: the largest of the first `N + 1` terms.
  let K : ℕ := (Finset.range (N + 1)).sup (fun i => (state i).1)
  have hK : ∀ i ≤ N, (state i).1 ≤ K := fun i hi =>
    Finset.le_sup (f := fun i => (state i).1) (Finset.mem_range.2 (by omega))
  -- (i) after `N`, no term has a squarefree mean with `m`.
  have hfix : ∀ k, N ≤ k → ¬ Squarefree (((state k).1 + m) / 2) := by
    intro k hk hsq
    have hcand : IsCand (state k).2 (state k).1 m := by
      refine ⟨by omega, ?_, ?_, hsq⟩
      · rw [state_snd, Finset.mem_image]
        rintro ⟨i, _, hi⟩
        exact hnot i hi
      · rw [Nat.even_iff]
        have hko := state_odd k
        omega
    have hle := succ_le_of_isCand k m hcand
    have hne := hnot (k + 1)
    have hodd := state_odd (k + 1)
    obtain ⟨i, hi, heq⟩ := hN (state (k + 1)).1 (by omega) hodd
    exact state_succ_ne k i (by omega) heq.symm
  -- (iii) above a threshold, every term after `N` is followed by a smaller term.
  have hdesc : ∃ Y, ∀ k, N ≤ k → Y ≤ (state k).1 → (state (k + 1)).1 < (state k).1 := by
    obtain ⟨C, hC⟩ := exists_squarefree_pair ((K + m) / 2)
    refine ⟨2 * C + m + 1, fun k hk hY => ?_⟩
    set y := (state k).1 with hy
    have hyodd : y % 2 = 1 := state_odd k
    obtain ⟨t, hTt, htc, hsqt, hsqtc⟩ := hC ((y - m) / 2) (by omega)
    have hcand : IsCand (state k).2 y (2 * t - m) := by
      refine ⟨by omega, ?_, ?_, ?_⟩
      · rw [state_snd, Finset.mem_image]
        rintro ⟨i, _, hi⟩
        by_cases hiN : i ≤ N
        · have hiK := hK i hiN
          omega
        · apply hfix i (by omega)
          have hmean : ((state i).1 + m) / 2 = t := by omega
          rw [hmean]
          exact hsqt
      · rw [Nat.even_iff]
        omega
      · have hmean : (y + (2 * t - m)) / 2 = t + (y - m) / 2 := by omega
        rw [hmean]
        exact hsqtc
    have hle := succ_le_of_isCand k _ hcand
    have hne : (state (k + 1)).1 ≠ 2 * t - m := by
      intro heq
      apply hfix (k + 1) (by omega)
      have hmean : ((state (k + 1)).1 + m) / 2 = t := by omega
      rw [hmean]
      exact hsqt
    omega
  obtain ⟨Y, hY⟩ := hdesc
  -- Only finitely many indices carry a term below `Y`.
  have hfin : (((fun k => (state k).1) ⁻¹' Set.Iio Y)).Finite :=
    Set.Finite.preimage state_injective.injOn (Set.finite_Iio Y)
  obtain ⟨B, hB⟩ := hfin.bddAbove
  have hbig : ∀ k, N + B + 1 ≤ k → Y ≤ (state k).1 := by
    intro k hk
    by_contra hlt
    push Not at hlt
    have hkB := hB (show k ∈ (fun k => (state k).1) ⁻¹' Set.Iio Y from hlt)
    omega
  -- An infinite strictly decreasing run of natural numbers.
  have hrun : ∀ i, (state (N + B + 1 + i)).1 + i ≤ (state (N + B + 1)).1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep := hY (N + B + 1 + i) (by omega) (hbig _ (by omega))
      have hidx : N + B + 1 + (i + 1) = N + B + 1 + i + 1 := by omega
      rw [hidx]
      omega
  have hend := hrun ((state (N + B + 1)).1 + 1)
  omega

/-! ## The conjecture -/

/-- The recursion of A259565 in the entry's form: for `n ≥ 1`, `a (n+1)` is the
least positive integer not among `a 1, …, a n` such that `(a n + a (n+1))/2` is
an integer and squarefree. -/
theorem a_succ (n : ℕ) (hn : 1 ≤ n) :
    a (n + 1) = Nat.find (exists_isCand ((Finset.Icc 1 n).image a) (a n)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hused : (Finset.Icc 1 (k + 1)).image a = (state k).2 := by
    rw [state_snd]
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact ⟨j, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j + 1, by omega, rfl⟩
  rw [hused]
  rfl

/-- Every term `a n` (`n ≥ 1`) is odd. -/
theorem a_odd (n : ℕ) (hn : 1 ≤ n) : Odd (a n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.odd_iff]
  exact state_odd k

/-- The terms `a n` (`n ≥ 1`) are pairwise distinct. -/
theorem a_injOn : Set.InjOn a (Set.Ici 1) := by
  intro i hi j hj hij
  simp only [Set.mem_Ici] at hi hj
  obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hij' := state_injective hij
  omega

/-- Every positive odd integer occurs in A259565. -/
theorem exists_a_eq (m : ℕ) (hm : Odd m) : ∃ n, 1 ≤ n ∧ a n = m := by
  obtain ⟨k, hk⟩ := exists_state_eq m (Nat.odd_iff.1 hm)
  exact ⟨k + 1, by omega, hk⟩

/-- **Zumkeller's conjecture (A259565, Reinhard Zumkeller, Jun 30 2015).**

The set of values `{a n : n ≥ 1}` is exactly the set of (positive) odd
integers; together with `a_injOn` this says `a` is a bijection from the
indices `n ≥ 1` onto the odd numbers (`a_bijOn`). -/
theorem image_a_eq : a '' Set.Ici 1 = {m : ℕ | Odd m} := by
  ext m
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact a_odd n hn
  · intro hm
    obtain ⟨n, hn, hnm⟩ := exists_a_eq m hm
    exact ⟨n, hn, hnm⟩

/-- A259565 is a permutation of the odd numbers: `a` maps the indices `n ≥ 1`
bijectively onto the odd natural numbers. -/
theorem a_bijOn : Set.BijOn a (Set.Ici 1) {m : ℕ | Odd m} :=
  ⟨fun n hn => a_odd n hn, a_injOn, fun m hm => exists_a_eq m hm⟩

end Candidates.A259565LeastAmongSquarefree
