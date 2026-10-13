import Mathlib
import Enumerative.Practical

set_option autoImplicit false

namespace ErdosCandidates.E18

/-- `RepresentableWithin m B`: every `1 ≤ n < m` is a sum of at most
    `B` distinct divisors of `m`. -/
def RepresentableWithin (m B : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n < m →
    ∃ S : Finset ℕ, S ⊆ m.divisors ∧ S.card ≤ B ∧ n = ∑ d ∈ S, d

/-- The least uniform number of distinct divisors needed to represent every
positive integer below `m`; the empty defining set has infimum zero. -/
noncomputable def h (m : ℕ) : ℕ := sInf {B : ℕ | RepresentableWithin m B}

example : RepresentableWithin 2 1 := by
  intro t ht hlt
  have heq : t = 1 := by omega
  subst t
  exact ⟨{1}, by decide, by decide, by decide⟩

example : h 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le (show RepresentableWithin 1 0 from by intro t ht hlt; omega)

/-- A practical number has a uniform representation bound given by its number
of divisors. -/
theorem representable_of_practical (m : ℕ) (hm : m.Practical) :
    RepresentableWithin m m.divisors.card := by
  intro t _ ht
  obtain ⟨S, hS, hsum⟩ := hm.exists_sum_eq (Nat.le_of_lt ht)
  exact ⟨S, hS, Finset.card_le_card hS, hsum.symm⟩

/-- Every integer from zero through `n!` is a sum of at most `n-1` distinct
positive divisors of `n!`, for `n ≥ 2`. The induction scales a representation
of the quotient by `n` and inserts its nonzero remainder. -/
theorem factorial_divisor_representation (n : ℕ) (hn : 2 ≤ n)
    (t : ℕ) (ht : t ≤ n.factorial) :
    ∃ S : Finset ℕ, S ⊆ n.factorial.divisors ∧ S.card ≤ n - 1 ∧
      t = ∑ d ∈ S, d := by
  induction n, hn using Nat.le_induction generalizing t with
  | base =>
    have ht2 : t ≤ 2 := by simpa using ht
    interval_cases t
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    · exact ⟨{1}, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨{2}, by norm_num, by norm_num, by norm_num⟩
  | succ k hk ih =>
    have hkpos : 0 < k + 1 := by omega
    have hq : t / (k + 1) ≤ k.factorial :=
      Nat.div_le_of_le_mul (by simpa only [Nat.factorial_succ] using ht)
    obtain ⟨D, hD, hcard, hsum⟩ := ih (t / (k + 1)) hq
    let E := D.image (fun d => (k + 1) * d)
    have hinj : Function.Injective (fun d : ℕ => (k + 1) * d) :=
      fun a b hab => Nat.eq_of_mul_eq_mul_left hkpos hab
    have hE : E ⊆ (k + 1).factorial.divisors := by
      intro e he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      have hdvd : d ∣ k.factorial := (Nat.mem_divisors.mp (hD hd)).1
      apply Nat.mem_divisors.mpr
      constructor
      · rw [Nat.factorial_succ]
        exact Nat.mul_dvd_mul_left (k + 1) hdvd
      · exact (Nat.factorial_pos _).ne'
    have hEcard : E.card ≤ k - 1 := by
      rw [Finset.card_image_of_injective D hinj]
      exact hcard
    have hEsum : ∑ d ∈ E, d = (k + 1) * (t / (k + 1)) := by
      rw [Finset.sum_image]
      · rw [← Finset.mul_sum, ← hsum]
      · intro a _ b _ hab
        exact hinj hab
    have hrlt : t % (k + 1) < k + 1 := Nat.mod_lt t hkpos
    have hdiv := Nat.div_add_mod t (k + 1)
    by_cases hrzero : t % (k + 1) = 0
    · refine ⟨E, hE, ?_, ?_⟩
      · omega
      · omega
    · have hrpos : 0 < t % (k + 1) := Nat.pos_of_ne_zero hrzero
      have hrmem : t % (k + 1) ∈ (k + 1).factorial.divisors := by
        exact Nat.mem_divisors.mpr
          ⟨Nat.dvd_factorial hrpos (Nat.le_of_lt hrlt), (Nat.factorial_pos _).ne'⟩
      have hrnot : t % (k + 1) ∉ E := by
        intro hrin
        obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hrin
        have hdpos : 0 < d := Nat.pos_of_mem_divisors (hD hd)
        have hlarge : k + 1 ≤ (k + 1) * d := by
          simpa using Nat.mul_le_mul_left (k + 1) hdpos
        omega
      refine ⟨insert (t % (k + 1)) E, Finset.insert_subset hrmem hE, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hrnot]
        omega
      · rw [Finset.sum_insert hrnot, hEsum]
        omega

/-- For `n ≥ 2`, at most `n-1` distinct divisors suffice below `n!`. -/
theorem representableWithin_factorial (n : ℕ) (hn : 2 ≤ n) :
    RepresentableWithin n.factorial (n - 1) := by
  intro t _ ht
  exact factorial_divisor_representation n hn t (Nat.le_of_lt ht)

/-- Erdős's factorial bound: `h(n!) < n` for `n ≥ 3`, obtained from the
explicit uniform bound `n-1` and the defining natural-number infimum. -/
theorem h_factorial_lt (n : ℕ) (hn : 3 ≤ n) : h n.factorial < n := by
  have hbound : h n.factorial ≤ n - 1 :=
    Nat.sInf_le (representableWithin_factorial n (by omega))
  omega

/-- Factorials are practical for `n ≥ 3`: the inclusive representation theorem
also represents the endpoint `n!`, as required by `Nat.Practical`. -/
theorem practical_factorial (n : ℕ) (hn : 3 ≤ n) :
    (n.factorial).Practical := by
  apply (Nat.practical_iff_exists_subset _).mpr
  refine ⟨Nat.factorial_pos _, ?_⟩
  intro t ht
  obtain ⟨S, hS, _, hsum⟩ := factorial_divisor_representation n (by omega) t ht
  exact ⟨S, hS, hsum.symm⟩

/-- The archived representation predicate is equivalent to bounded search
through the powerset of the divisor set. -/
theorem representableWithin_iff (m B : ℕ) :
    RepresentableWithin m B ↔
      ∀ t < m, 1 ≤ t → ∃ S ∈ m.divisors.powerset,
        S.card ≤ B ∧ t = ∑ d ∈ S, d := by
  constructor
  · intro hrep t ht hpos
    obtain ⟨S, hS, hcard, hsum⟩ := hrep t hpos ht
    exact ⟨S, Finset.mem_powerset.mpr hS, hcard, hsum⟩
  · intro hrep t hpos ht
    obtain ⟨S, hS, hcard, hsum⟩ := hrep t ht hpos
    exact ⟨S, Finset.mem_powerset.mp hS, hcard, hsum⟩

/-- Increasing the allowed cardinality preserves representability. -/
theorem RepresentableWithin.mono {m B C : ℕ} (hrep : RepresentableWithin m B)
    (hBC : B ≤ C) : RepresentableWithin m C := by
  intro t hpos ht
  obtain ⟨S, hS, hcard, hsum⟩ := hrep t hpos ht
  exact ⟨S, hS, hcard.trans hBC, hsum⟩

/-- A positive bound is the exact infimum if it works and its predecessor does
not. Positivity guards the natural-number predecessor. -/
theorem h_eq_of_representable_of_not_predecessor (m B : ℕ) (hB : 0 < B)
    (hrep : RepresentableWithin m B) (hnot : ¬ RepresentableWithin m (B - 1)) :
    h m = B := by
  have hupper : h m ≤ B := Nat.sInf_le hrep
  have hinf : RepresentableWithin m (h m) :=
    Nat.sInf_mem (s := {b : ℕ | RepresentableWithin m b}) ⟨B, hrep⟩
  have hlower : B ≤ h m := by
    by_contra hlt
    have hpred : h m ≤ B - 1 := by omega
    exact hnot (hinf.mono hpred)
  exact Nat.le_antisymm hupper hlower

/-- Ground truth: six needs exactly two distinct divisors, certified by bounded
powerset search (five is not representable with one divisor). -/
theorem h_six : h 6 = 2 := by
  apply h_eq_of_representable_of_not_predecessor 6 2 (by decide)
  · exact (representableWithin_iff 6 2).mpr (by decide)
  · intro hrep
    exact (show ¬ (∀ t < 6, 1 ≤ t → ∃ S ∈ (6 : ℕ).divisors.powerset,
      S.card ≤ 1 ∧ t = ∑ d ∈ S, d) from by decide)
      ((representableWithin_iff 6 1).mp hrep)

set_option maxRecDepth 4000 in
/-- Ground truth: twenty-four needs exactly three distinct divisors, certified
by bounded powerset search. -/
theorem h_twenty_four : h 24 = 3 := by
  apply h_eq_of_representable_of_not_predecessor 24 3 (by decide)
  · exact (representableWithin_iff 24 3).mpr (by decide)
  · intro hrep
    exact (show ¬ (∀ t < 24, 1 ≤ t → ∃ S ∈ (24 : ℕ).divisors.powerset,
      S.card ≤ 2 ∧ t = ∑ d ∈ S, d) from by decide)
      ((representableWithin_iff 24 2).mp hrep)

example : 0 < (2 : ℕ) ∧ RepresentableWithin 6 2 ∧
    ¬ RepresentableWithin 6 1 := by
  refine ⟨by decide, (representableWithin_iff 6 2).mpr (by decide), ?_⟩
  intro hrep
  exact (show ¬ (∀ t < 6, 1 ≤ t → ∃ S ∈ (6 : ℕ).divisors.powerset,
    S.card ≤ 1 ∧ t = ∑ d ∈ S, d) from by decide)
    ((representableWithin_iff 6 1).mp hrep)

example : 2 ≤ 2 ∧ 0 ≤ (2 : ℕ).factorial := by decide
example : 2 ≤ 2 ∧ 2 ≤ (2 : ℕ).factorial := by decide
example : (6 : ℕ).Practical := by decide
example : 3 ≤ (3 : ℕ) := by decide

end ErdosCandidates.E18
