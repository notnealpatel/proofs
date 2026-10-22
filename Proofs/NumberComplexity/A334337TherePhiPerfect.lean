/-
# A334337 — Sun: for every `n ≥ 1` some `φ(m·n)` is a perfect cube

OEIS A334337, Zhi-Wei Sun: for every positive `n`, some positive `m`
makes `φ(mn)` a cube. More generally, for every `k ≥ 1`,
`φ(φ(n!)^(k-1)·n!) = φ(n!)^k`.
Every prime factor of `φ(n!)` is at most `n`, hence divides `n!`, and
`φ(ab) = aφ(b)` when every prime factor of `a` divides `b`.
The witness `m = φ(n!)^(k-1)·(n-1)!` need not be least. It also gives
a fourth-power value for `n = 107`; no bound on that witness is proved.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A334337TherePhiPerfect

/-! ## Definitions -/

/-- `m` witnesses the A334337 property for `n`: `m` is positive and `φ(m · n)`
is a perfect cube. -/
def CubeWitness (n m : ℕ) : Prop :=
  0 < m ∧ ∃ c : ℕ, Nat.totient (m * n) = c ^ 3

/-- A cube root of `x`, if any, is at most `x`, so cubehood is a bounded
search. -/
theorem exists_cube_iff_bounded (x : ℕ) :
    (∃ c : ℕ, x = c ^ 3) ↔ ∃ c ∈ Finset.range (x + 1), x = c ^ 3 := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, Finset.mem_range.mpr ?_, hc⟩
    have hle : c ≤ c ^ 3 := by
      rcases Nat.eq_zero_or_pos c with h0 | hpos
      · simp [h0]
      · calc c = c ^ 1 := (pow_one c).symm
          _ ≤ c ^ 3 := Nat.pow_le_pow_right hpos (by norm_num)
    omega
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

/-- Decidability of `CubeWitness n m`, through the bounded cube search. -/
instance (n m : ℕ) : Decidable (CubeWitness n m) :=
  decidable_of_iff
    (0 < m ∧ ∃ c ∈ Finset.range (Nat.totient (m * n) + 1), Nat.totient (m * n) = c ^ 3)
    (and_congr_right fun _ => (exists_cube_iff_bounded _).symm)

/-! ## Examples for the witness predicate -/

/-- `a(3) = 5`: `φ(15) = 8 = 2^3`. -/
example : CubeWitness 3 5 := ⟨by norm_num, 2, by decide⟩

/-- `a(3) = 5` minimality: `m = 1, …, 4` are not witnesses for `n = 3`. -/
example : ∀ m < 5, ¬ CubeWitness 3 m := by decide

/-- `a(4) = 4`, `a(5) = 3`, `a(6) = 4`, `a(8) = 2`: witness and minimality. -/
example : CubeWitness 4 4 ∧ (∀ m < 4, ¬ CubeWitness 4 m) ∧
    CubeWitness 5 3 ∧ (∀ m < 3, ¬ CubeWitness 5 m) ∧
    CubeWitness 6 4 ∧ (∀ m < 4, ¬ CubeWitness 6 m) ∧
    CubeWitness 8 2 ∧ (∀ m < 2, ¬ CubeWitness 8 m) := by decide

/-! ## Proof -/

/-- If every prime factor of `a` divides `b`, then `φ(a · b) = a · φ(b)`. -/
theorem totient_mul_of_primeFactors_subset {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsub : a.primeFactors ⊆ b.primeFactors) :
    Nat.totient (a * b) = a * Nat.totient b := by
  have hpf : (a * b).primeFactors = b.primeFactors := by
    rw [Nat.primeFactors_mul ha hb, Finset.union_eq_right.mpr hsub]
  have hab := Nat.totient_mul_prod_primeFactors (a * b)
  have hb' := Nat.totient_mul_prod_primeFactors b
  rw [hpf] at hab
  have hpos : 0 < ∏ p ∈ b.primeFactors, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hab, mul_assoc a (Nat.totient b), hb', mul_assoc]

/-- Every prime factor `q` of `φ(N)` divides `N` or lies below some prime
factor of `N`. -/
theorem prime_dvd_totient {N q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.totient N) :
    q ∣ N ∨ ∃ p ∈ N.primeFactors, q < p := by
  rw [Nat.totient_eq_div_primeFactors_mul] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h1 | h2
  · exact Or.inl (h1.trans (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_dvd N)))
  · right
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp h2
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hle := Nat.le_of_dvd (by omega) hqp
    exact ⟨p, hp, by omega⟩

/-- Every prime factor of `φ(n!)` divides `n!`. -/
theorem primeFactors_totient_factorial_subset (n : ℕ) :
    (Nat.totient n.factorial).primeFactors ⊆ n.factorial.primeFactors := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  refine Nat.mem_primeFactors.mpr ⟨hqp, ?_, Nat.factorial_ne_zero n⟩
  rcases prime_dvd_totient hqp hqd with h | ⟨p, hp, hlt⟩
  · exact h
  · have hpn : p ≤ n :=
      (Nat.Prime.dvd_factorial (Nat.prime_of_mem_primeFactors hp)).mp
        (Nat.dvd_of_mem_primeFactors hp)
    exact (Nat.Prime.dvd_factorial hqp).mpr (by omega)

/-- Core identity: `φ(φ(n!)^j · n!) = φ(n!)^(j+1)` for every `j`. -/
theorem totient_pow_mul_factorial (n j : ℕ) :
    Nat.totient (Nat.totient n.factorial ^ j * n.factorial) =
      Nat.totient n.factorial ^ (j + 1) := by
  have hF : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hT : Nat.totient n.factorial ≠ 0 := by
    rw [Ne, Nat.totient_eq_zero]; exact hF
  rcases Nat.eq_zero_or_pos j with hj | hj
  · simp [hj]
  · have hsub : (Nat.totient n.factorial ^ j).primeFactors ⊆ n.factorial.primeFactors := by
      rw [Nat.primeFactors_pow _ (by omega)]
      exact primeFactors_totient_factorial_subset n
    rw [totient_mul_of_primeFactors_subset (pow_ne_zero j hT) hF hsub, pow_succ]

/-- **Generalisation (all exponents).** For every `n ≥ 1` and every `k ≥ 1`
there is `m ≥ 1` such that `φ(m · n)` is a perfect `k`-th power; the witness is
`m = φ(n!)^(k-1) · (n-1)!`.  With `k = 4`, `n = 107` this shows a fourth-power
value `φ(107 · m)` exists (the entry reports none with `m ≤ 10^8`). -/
theorem exists_totient_mul_eq_pow {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : ℕ, Nat.totient (m * n) = c ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  refine ⟨Nat.totient (r + 1).factorial ^ j * r.factorial, ?_, Nat.totient (r + 1).factorial, ?_⟩
  · have hT : 0 < Nat.totient (r + 1).factorial :=
      Nat.totient_pos.mpr (Nat.factorial_pos _)
    exact Nat.mul_pos (pow_pos hT j) (Nat.factorial_pos r)
  · have hmn : Nat.totient (r + 1).factorial ^ j * r.factorial * (r + 1) =
        Nat.totient (r + 1).factorial ^ j * (r + 1).factorial := by
      rw [Nat.factorial_succ, mul_assoc, mul_comm r.factorial (r + 1)]
    rw [hmn, totient_pow_mul_factorial]

/-- Sun’s conjecture (A334337): for every positive `n` there is a
positive `m` with `φ(mn)` a cube, the `k = 3` case of
`exists_totient_mul_eq_pow`. -/
theorem conjecture (n : ℕ) (hn : 0 < n) : ∃ m : ℕ, CubeWitness n m :=
  exists_totient_mul_eq_pow hn (by norm_num : 0 < 3)

/-- A fourth-power value at `n = 107`: some positive `m` makes
`φ(107·m)` a fourth power. No lower bound on `m` is proved here. -/
theorem exists_totient_mul_107_fourth_power :
    ∃ m : ℕ, 0 < m ∧ ∃ c : ℕ, Nat.totient (m * 107) = c ^ 4 :=
  exists_totient_mul_eq_pow (by norm_num) (by norm_num)

/-- A334337 as a sequence: the least `m` with `0 < m` and `φ(m · n)` a cube,
well defined for `n ≥ 1` by `conjecture`. -/
noncomputable def a (n : ℕ) (hn : 0 < n) : ℕ :=
  Nat.find (conjecture n hn)

/-- Examples: `a(1) = 1`, `a(2) = 1`, `a(3) = 5`, matching the listed terms. -/
example : a 1 (by norm_num) = 1 ∧ a 2 (by norm_num) = 1 ∧ a 3 (by norm_num) = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [a, Nat.find_eq_iff]; decide)

set_option maxRecDepth 20000 in
/-- Examples: `a(7) = 37`, the first large listed term. -/
example : a 7 (by norm_num) = 37 := by
  rw [a, Nat.find_eq_iff]
  decide

end Candidates.A334337TherePhiPerfect
