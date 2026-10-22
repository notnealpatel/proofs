/-
Rule 45 transform of the primes (OEIS A093511; Bill McEachen, Jun 12 2024).

The source's window (i-2,i-1,i) encodes the bit index
4*[i-2 prime]+2*[i-1 prime]+[i prime]; Rule 45 keeps indices 0,2,3,5.
The infinite sequence uses the stable limit of the finite-prefix program.
For i≥6 the support is McEachen's bookend construction: between consecutive
prime bookends p+1,q+1 (p≥5), keep the middle value when q=p+2;
otherwise omit p+2 and q and retain the interior values.
With one-based sequence indexing, a(n)=Nat.nth InConstruct (n-4) for n>3.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A093511MceachenRuleTransform

/-- The prime indicator as a bit: `primeBit k = 1` if `k` is prime and `0` otherwise. -/
def primeBit (k : ℕ) : ℕ := if k.Prime then 1 else 0

/-- `IsTerm i`: `i` is a term of A093511, the Rule 45 transform of the prime indicator.
For `1 ≤ i`, bit `4·[i-2 prime] + 2·[i-1 prime] + [i prime]` of `45` is set. When `i = 1`
the truncated `i - 2` and `i - 1` are both `0`, which is not prime. This matches the PARI
convention that positions before `1` read as `0`. -/
def IsTerm (i : ℕ) : Prop :=
  1 ≤ i ∧ Nat.testBit 45 (4 * primeBit (i - 2) + 2 * primeBit (i - 1) + primeBit i) = true

/-- Membership in A093511 is decidable (prime tests and a bit test). -/
instance : DecidablePred IsTerm := fun i => by unfold IsTerm; infer_instance

/-- `a n` is the `n`-th term of A093511 (1-indexed, as in the OEIS: `a 1 = 1`).
`a 0` is a junk value and is never used. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

example : (List.range 105).filter (fun i => decide (IsTerm i)) =
    [1,3,5,6,7,8,10,12,13,14,16,18,19,20,22,24,26,27,28,30,31,32,34,35,36,38,40,42,43,44,46,
     48,50,51,52,54,56,57,58,60,61,62,64,65,66,68,70,72,73,74,76,77,78,80,82,84,86,87,88,90,
     92,93,94,95,96,98,100,102,103,104] := by decide +kernel

example : a 4 = 6 := by
  have h6 : IsTerm 6 := by decide
  have hc : Nat.count IsTerm 6 = 3 := by decide
  rw [a, show 4 - 1 = Nat.count IsTerm 6 by rw [hc], Nat.nth_count h6]


/-- `p` and `q` are consecutive primes: both prime, `p < q`, and no prime lies strictly
between them. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r, p < r → r < q → ¬ r.Prime

/-- McEachen's bookend construction. `i` is a bookend `p + 1` for a prime `p ≥ 5`, or `i`
lies strictly between the bookends `p + 1` and `q + 1` of consecutive primes `5 ≤ p < q`
and either the bookends are "twin composites" (`q = p + 2`) or `i` is adjacent to neither
bookend (`i ≠ p + 2` and `i ≠ q`). -/
def InConstruct (i : ℕ) : Prop :=
  (∃ p, p.Prime ∧ 5 ≤ p ∧ i = p + 1) ∨
  (∃ p q, ConsecutivePrimes p q ∧ 5 ≤ p ∧ p + 1 < i ∧ i < q + 1 ∧
     (q = p + 2 ∨ (i ≠ p + 2 ∧ i ≠ q)))

example : InConstruct 7 :=
  Or.inr ⟨5, 7, ⟨by norm_num, by norm_num, by norm_num, fun r h1 h2 => by
    obtain rfl : r = 6 := by omega
    norm_num⟩, le_rfl, by norm_num, by norm_num, Or.inl rfl⟩

example : InConstruct 92 :=
  Or.inr ⟨89, 97, ⟨by norm_num, by norm_num, by norm_num, fun r h1 h2 => by
    interval_cases r <;> norm_num⟩, by norm_num, by norm_num, by norm_num,
    Or.inr ⟨by norm_num, by norm_num⟩⟩

example : ¬ InConstruct 91 := by
  rintro (⟨p, hp, -, hpi⟩ | ⟨p, q, ⟨hp, hq, hpq, hcons⟩, -, hpi, hiq, hor⟩)
  · obtain rfl : p = 90 := by omega
    norm_num at hp
  · have hp89 : p = 89 := by
      by_contra hne
      have hlt : p < 89 := by
        rcases Nat.lt_or_ge p 89 with h | h
        · exact h
        · omega
      exact hcons 89 hlt (by omega) (by norm_num)
    subst hp89
    have hq97 : q ≤ 97 := by
      by_contra hgt
      exact hcons 97 (by omega) (by omega) (by norm_num)
    have hq91 : 91 ≤ q := by omega
    interval_cases q <;> revert hq hor <;> norm_num

example : InConstruct 6 := Or.inl ⟨5, by norm_num, le_rfl, rfl⟩

example : InConstruct 98 := Or.inl ⟨97, by norm_num, by norm_num, rfl⟩

example : ¬ InConstruct 97 := by
  rintro (⟨p, hp, -, hpi⟩ | ⟨p, q, ⟨hp, hq, hpq, hcons⟩, -, hpi, hiq, hor⟩)
  · obtain rfl : p = 96 := by omega
    norm_num at hp
  · have hp89 : 89 ≤ p := by
      by_contra hlt
      exact hcons 89 (by omega) (by omega) (by norm_num)
    have hq97 : q = 97 := by
      by_contra hne
      exact hcons 97 (by omega) (by omega) (by norm_num)
    subst hq97
    have hp95 : p ≤ 95 := by omega
    interval_cases p <;> revert hp hor <;> norm_num

/-- Truth table of Rule 45 on the prime indicator. For `1 ≤ i`, `i` is a term iff the
window `([i-2 prime], [i-1 prime], [i prime])` is `000`, `010`, `011` or `101`. -/
theorem isTerm_iff (i : ℕ) (hi : 1 ≤ i) :
    IsTerm i ↔
      (¬ (i - 2).Prime ∧ ¬ (i - 1).Prime ∧ ¬ i.Prime) ∨
      (¬ (i - 2).Prime ∧ (i - 1).Prime ∧ ¬ i.Prime) ∨
      (¬ (i - 2).Prime ∧ (i - 1).Prime ∧ i.Prime) ∨
      ((i - 2).Prime ∧ ¬ (i - 1).Prime ∧ i.Prime) := by
  unfold IsTerm primeBit
  by_cases hA : (i - 2).Prime <;> by_cases hB : (i - 1).Prime <;> by_cases hC : i.Prime <;>
    simp [hA, hB, hC, hi] <;> decide

/-- Inside the gap of consecutive primes `p < q`, for `p + 1 < i ≤ q`: `i - 2` is prime
exactly when `i = p + 2`, and `i` is prime exactly when `i = q`. -/
theorem prime_iff_of_consecutive {p q i : ℕ} (hpq : ConsecutivePrimes p q)
    (h1 : p + 1 < i) (h2 : i < q + 1) :
    ((i - 2).Prime ↔ i = p + 2) ∧ (i.Prime ↔ i = q) := by
  obtain ⟨hp, hq, hlt, hcons⟩ := hpq
  constructor
  · constructor
    · intro hprime
      by_contra hne
      exact hcons (i - 2) (by omega) (by omega) hprime
    · intro heq
      rw [heq, Nat.add_sub_cancel]
      exact hp
  · constructor
    · intro hprime
      by_contra hne
      exact hcons i (by omega) (by omega) hprime
    · intro heq
      rw [heq]
      exact hq

/-- **Local form of McEachen's conjecture.** For `6 ≤ i`, `i` is a term of A093511 iff `i`
belongs to the bookend construction. -/
theorem isTerm_iff_inConstruct (i : ℕ) (hi : 6 ≤ i) : IsTerm i ↔ InConstruct i := by
  rw [isTerm_iff i (by omega)]
  by_cases hB : (i - 1).Prime
  · have hodd : Odd (i - 1) := hB.odd_of_ne_two (by omega)
    have hA : ¬ (i - 2).Prime := by
      intro hA
      have := hA.even_iff.mp (by
        rcases hodd with ⟨k, hk⟩
        exact ⟨k, by omega⟩)
      omega
    have hC : ¬ i.Prime := by
      intro hC
      have := hC.even_iff.mp (by
        rcases hodd with ⟨k, hk⟩
        exact ⟨k + 1, by omega⟩)
      omega
    simp only [hA, hB, hC, not_false_eq_true, and_self, true_and, and_true, true_or, or_true,
      true_iff]
    exact Or.inl ⟨i - 1, hB, by omega, by omega⟩
  · have hleft : ¬ ∃ p, p.Prime ∧ 5 ≤ p ∧ i = p + 1 := by
      rintro ⟨p, hp, -, rfl⟩
      exact hB (by simpa using hp)
    have hdisj : ∀ p q, ConsecutivePrimes p q → p + 1 < i → i < q + 1 →
        (((i - 2).Prime ↔ i.Prime) ↔ (q = p + 2 ∨ (i ≠ p + 2 ∧ i ≠ q))) := by
      intro p q hpq h1 h2
      obtain ⟨hA, hC⟩ := prime_iff_of_consecutive hpq h1 h2
      rw [hA, hC]
      omega
    have hi7 : 7 ≤ i := by
      by_contra hlt
      obtain rfl : i = 6 := by omega
      exact hB (by norm_num)
    have hrule : ((¬ (i - 2).Prime ∧ ¬ (i - 1).Prime ∧ ¬ i.Prime) ∨
        (¬ (i - 2).Prime ∧ (i - 1).Prime ∧ ¬ i.Prime) ∨
        (¬ (i - 2).Prime ∧ (i - 1).Prime ∧ i.Prime) ∨
        ((i - 2).Prime ∧ ¬ (i - 1).Prime ∧ i.Prime)) ↔ ((i - 2).Prime ↔ i.Prime) := by
      simp only [hB, not_false_eq_true, true_and]
      tauto
    rw [hrule]
    classical
    have hexq : ∃ q, i ≤ q ∧ q.Prime := Nat.exists_infinite_primes i
    set q := Nat.find hexq with hqdef
    set p := Nat.findGreatest Nat.Prime (i - 2) with hpdef
    have hqspec : i ≤ q ∧ q.Prime := Nat.find_spec hexq
    have hp : p.Prime := Nat.findGreatest_spec (m := 5) (by omega) (by norm_num)
    have hp5 : 5 ≤ p := Nat.le_findGreatest (by omega) (by norm_num)
    have hpi : p ≤ i - 2 := Nat.findGreatest_le _
    have hcons : ConsecutivePrimes p q := by
      refine ⟨hp, hqspec.2, by omega, fun r h1 h2 hr => ?_⟩
      rcases Nat.lt_or_ge r (i - 1) with hlt | hge
      · exact Nat.findGreatest_is_greatest h1 (by omega) hr
      · rcases Nat.eq_or_lt_of_le hge with heq | hgt
        · exact hB (heq ▸ hr)
        · exact Nat.find_min hexq h2 ⟨by omega, hr⟩
    constructor
    · intro hiff
      exact Or.inr ⟨p, q, hcons, hp5, by omega, by omega,
        (hdisj p q hcons (by omega) (by omega)).mp hiff⟩
    · rintro (hl | ⟨p', q', hc', -, h1, h2, hor⟩)
      · exact absurd hl hleft
      · exact (hdisj p' q' hc' h1 h2).mpr hor


/-- Every element of the construction is at least `6`. -/
theorem six_le_of_inConstruct {i : ℕ} (hi : InConstruct i) : 6 ≤ i := by
  rcases hi with ⟨p, -, hp5, rfl⟩ | ⟨p, q, -, hp5, hpi, -, -⟩ <;> omega

/-- The construction is infinite: it contains `p + 1` for every prime `p ≥ 5`. -/
theorem inConstruct_infinite : (Set.ofPred InConstruct).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun n => ?_
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (n + 5)
  exact ⟨p + 1, Or.inl ⟨p, hpp, by omega, rfl⟩, by omega⟩

/-- From one-based index `4`, A093511 enumerates the bookend construction
in increasing order (Bill McEachen, Jun 12 2024). The `n-4` index in `Nat.nth`
is zero-based and guarded by `3<n`. -/
theorem mceachen_a093511 (n : ℕ) (hn : 3 < n) : a n = Nat.nth InConstruct (n - 4) := by
  classical
  set m := n - 4 with hm
  set x := Nat.nth InConstruct m with hx
  have hxC : InConstruct x := Nat.nth_mem_of_infinite inConstruct_infinite m
  have hx6 : 6 ≤ x := six_le_of_inConstruct hxC
  have hxT : IsTerm x := (isTerm_iff_inConstruct x hx6).mpr hxC
  have hcountC : Nat.count InConstruct x = m := Nat.count_nth_of_infinite inConstruct_infinite m
  have hsplit : x = 6 + (x - 6) := by omega
  have hshift : Nat.count (fun k => IsTerm (6 + k)) (x - 6) =
      Nat.count (fun k => InConstruct (6 + k)) (x - 6) := by
    congr 1
    funext k
    exact propext (isTerm_iff_inConstruct (6 + k) (by omega))
  have hC6 : Nat.count InConstruct 6 = 0 :=
    Nat.count_iff_forall_not.mpr fun k hk hkC => by
      have h6 := six_le_of_inConstruct hkC
      omega
  have hT6 : Nat.count IsTerm 6 = 3 := by decide
  have hcountT : Nat.count IsTerm x = m + 3 := by
    have e1 := Nat.count_add (p := IsTerm) 6 (x - 6)
    have e2 := Nat.count_add (p := InConstruct) 6 (x - 6)
    rw [← hsplit] at e1 e2
    omega
  have hn' : n - 1 = Nat.count IsTerm x := by omega
  rw [a, hn', Nat.nth_count hxT]

end Candidates.A093511MceachenRuleTransform
