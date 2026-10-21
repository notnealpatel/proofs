/-
  Erdős Problem #1140 — n − 2x² always prime.
  Status: disproved (Mollin–Williams 1989 + Epure–Gica 2010, via class
  number one computations).  Tier B archive target with certificates.

  Verbatim statement (`goof erdos fetch 1140`, pulled 2026-08-05):

    "Do there exist infinitely many $n$ such that $n-2x^2$ is prime for
    all $x$ with $2x^2<n$?"

  DB remarks: known such n: 2, 5, 7, 13, 31, 61, 181, 199; these are,
  with at most one exception, all such n.  Epure–Gica [EpGi10, Thm 4.1]:
  the only such n ≡ 1 (mod 4) are 5, 13, 61, 181; their method with
  Mollin–Williams [MoWi89] gives: the only n ≡ 3 (mod 4) are 7, 31, 199
  and at most one further exception.  (Comment thread: Woett/Chojecki
  note the problem is thus fully answered "no" modulo the one possible
  exception; a GRH-conditional route also closes finiteness.)

  Repo adjacency: exactly the `Proofs/Erdos/Covering/ErdosMinus2k.lean`
  shape (`IsAllPrimeMinusPow`): predicate, decide certificates, finite
  window, archived completeness.

  Mathlib inventory (leandoc 2026-08-05): `Nat.Prime`,
  `Nat.decidablePrime`; the bound `2x² < n` makes the predicate
  decidable per n.  Class-number machinery (the actual proof) is out of
  scope for Mathlib today — completeness stays sorry'd.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1140

/-- `AllPrimeMinusTwoSq n`: `n − 2x²` is prime for every `x` with
    `2x² < n`.  (ℕ-subtraction is exact under `2x² < n`.)  Note `x = 0`
    is included, so any positive such `n` is itself prime. At `n = 0`
    the raw predicate is vacuously true: no x satisfies 2*x^2 < 0.
    It therefore differs from a positive-domain production predicate. -/
def AllPrimeMinusTwoSq (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime

/-- The raw predicate is equivalent to checking only natural numbers below `n`. -/
theorem allPrimeMinusTwoSq_iff_bounded (n : ℕ) :
    AllPrimeMinusTwoSq n ↔
      ∀ x < n, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime := by
  constructor
  · intro h x _ hx
    exact h x hx
  · intro h x hx
    have hx_sq : x ≤ x ^ 2 := Nat.le_self_pow (by decide) x
    have hx_twice_sq : x ≤ 2 * x ^ 2 := by omega
    exact h x (lt_of_le_of_lt hx_twice_sq hx) hx

example : AllPrimeMinusTwoSq 0 := by
  intro x hx
  exact False.elim (Nat.not_lt_zero _ hx)

/-- Decidability: `2x² < n` forces `x < n`, so the quantifier is bounded. -/
instance (n : ℕ) : Decidable (AllPrimeMinusTwoSq n) :=
  decidable_of_iff (∀ x < n, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime)
    (allPrimeMinusTwoSq_iff_bounded n).symm

set_option maxRecDepth 4096 in
/-- The eight known members, as kernel decide certificates.
    Trace for 13: 13, 11, 5 (x = 0, 1, 2) all prime. -/
theorem cert_known_members :
    AllPrimeMinusTwoSq 2 ∧ AllPrimeMinusTwoSq 5 ∧ AllPrimeMinusTwoSq 7 ∧
    AllPrimeMinusTwoSq 13 ∧ AllPrimeMinusTwoSq 31 ∧ AllPrimeMinusTwoSq 61 ∧
    AllPrimeMinusTwoSq 181 ∧ AllPrimeMinusTwoSq 199 := by
  decide

/-- Negative controls: 3 and 11 fail at `x = 1`, producing 1 and 9. -/
theorem cert_negative_controls : ¬ AllPrimeMinusTwoSq 3 ∧ ¬ AllPrimeMinusTwoSq 11 := by
  constructor
  · intro h
    have hprime : Nat.Prime 1 := h 1 (by decide)
    exact (by decide : ¬ Nat.Prime 1) hprime
  · intro h
    have hprime : Nat.Prime 9 := h 1 (by decide)
    exact (by decide : ¬ Nat.Prime 9) hprime

example : ¬ AllPrimeMinusTwoSq 3 ∧ ¬ AllPrimeMinusTwoSq 11 :=
  cert_negative_controls

/-- A divisor witness `p ∣ n - 2x²` with `2 ≤ p < n - 2x²` refutes the predicate. -/
private theorem not_all_of_dvd {n : ℕ} (p x : ℕ) (hp : 2 ≤ p) (hx : 2 * (x * x) < n)
    (hd : p ∣ n - 2 * (x * x)) (hlt : p < n - 2 * (x * x)) : ¬ AllPrimeMinusTwoSq n := by
  intro h
  have hsq : x ^ 2 = x * x := sq x
  have hprime : (n - 2 * (x * x)).Prime := by
    have hx' := h x (by rw [hsq]; exact hx)
    rwa [hsq] at hx'
  rcases (Nat.dvd_prime hprime).mp hd with h1 | h2
  · omega
  · omega

/-- `n ≥ 200` outside the six residue classes `19, 31, 61, 139, 181, 199 (mod 210)` is
    refuted by a witness `x ≤ 3` whose `n - 2x²` is divisible by `2`, `3`, `5` or `7`. -/
private theorem not_all_of_not_survivor {n : ℕ} (h1 : 200 ≤ n)
    (hs : n % 210 ∉ ({19, 31, 61, 139, 181, 199} : Finset ℕ)) : ¬ AllPrimeMinusTwoSq n := by
  intro hall
  have w : ∀ p x : ℕ, 2 ≤ p → 2 * (x * x) < n → (n - 2 * (x * x)) % p = 0 →
      p < n - 2 * (x * x) → False := fun p x hp hx hm hlt =>
    not_all_of_dvd p x hp hx (Nat.dvd_of_mod_eq_zero hm) hlt hall
  have h2 : n % 2 = 1 := by
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h | h
    · exact (w 2 0 le_rfl (by omega) (by omega) (by omega)).elim
    · exact h
  have h3 : n % 3 = 1 := by
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · exact (w 3 0 (by norm_num) (by omega) (by omega) (by omega)).elim
    · exact h
    · exact (w 3 1 (by norm_num) (by omega) (by omega) (by omega)).elim
  have h5 : n % 5 = 1 ∨ n % 5 = 4 := by
    rcases (by omega : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4)
      with h | h | h | h | h
    · exact (w 5 0 (by norm_num) (by omega) (by omega) (by omega)).elim
    · exact Or.inl h
    · exact (w 5 1 (by norm_num) (by omega) (by omega) (by omega)).elim
    · exact (w 5 2 (by norm_num) (by omega) (by omega) (by omega)).elim
    · exact Or.inr h
  have h7 : n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
    rcases (by omega : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨
      n % 7 = 5 ∨ n % 7 = 6) with h | h | h | h | h | h | h
    · exact (w 7 0 (by norm_num) (by omega) (by omega) (by omega)).elim
    · exact (w 7 2 (by norm_num) (by omega) (by omega) (by omega)).elim
    · exact (w 7 1 (by norm_num) (by omega) (by omega) (by omega)).elim
    · exact Or.inl h
    · exact (w 7 3 (by norm_num) (by omega) (by omega) (by omega)).elim
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  apply hs
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Bool test: `x` and `p` witness `2 ≤ p`, `2x² < n`, `p ∣ n - 2x²`, `p < n - 2x²`. -/
private def divWitness (n p x : ℕ) : Bool :=
  decide (2 ≤ p) && (n - 2 * (x * x)) % p == 0 && decide (2 * (x * x) < n) &&
    decide (p < n - 2 * (x * x))

example : divWitness 229 13 4 = false := by decide
example : divWitness 233 11 1 = true := by decide

private theorem not_all_of_divWitness {n p x : ℕ} (h : divWitness n p x = true) :
    ¬ AllPrimeMinusTwoSq n := by
  simp only [divWitness, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hp, hmod⟩, hx⟩, hlt⟩ := h
  exact not_all_of_dvd p x hp hx (Nat.dvd_of_mod_eq_zero hmod) hlt

/-- Kernel-reducible search: some `x < c` gives `divWitness n p x`. -/
private noncomputable def anyX (n p c : ℕ) : Bool :=
  Nat.rec false (fun x acc => divWitness n p x || acc) c

private theorem not_all_of_anyX {n p c : ℕ} (h : anyX n p c = true) :
    ¬ AllPrimeMinusTwoSq n := by
  induction c with
  | zero => exact absurd h (by simp [anyX])
  | succ c ih =>
    have hunfold : anyX n p (c + 1) = (divWitness n p c || anyX n p c) := rfl
    rw [hunfold, Bool.or_eq_true] at h
    rcases h with hw | hrest
    · exact not_all_of_divWitness hw
    · exact ih hrest

/-- Kernel-reducible search over a list of moduli `p`, with `x ≤ p / 2`
    (enough to hit every residue `2x² mod p`). -/
private noncomputable def anyP (n : ℕ) (ps : List ℕ) : Bool :=
  List.rec false (fun p _ acc => anyX n p (p / 2 + 1) || acc) ps

private theorem not_all_of_anyP {n : ℕ} {ps : List ℕ} (h : anyP n ps = true) :
    ¬ AllPrimeMinusTwoSq n := by
  induction ps with
  | nil => exact absurd h (by simp [anyP])
  | cons p ps ih =>
    have hunfold : anyP n (p :: ps) = (anyX n p (p / 2 + 1) || anyP n ps) := rfl
    rw [hunfold, Bool.or_eq_true] at h
    rcases h with hw | hrest
    · exact not_all_of_anyX hw
    · exact ih hrest

/-- Per-`n` certificate test with the primes `11 … 67` (67 is the largest needed
    for `n ≤ 10⁶` once `2, 3, 5, 7` are handled by `not_all_of_not_survivor`). -/
private noncomputable def windowCheck (n : ℕ) : Bool :=
  anyP n [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]

example : windowCheck 199 = false := by decide +kernel
example : windowCheck 229 = true := by decide +kernel

/-- `windowCheck`, vacuously true outside `[200, 10⁶]`. -/
private noncomputable def inWin (n : ℕ) : Bool :=
  decide (n < 200) || decide (1000000 < n) || windowCheck n

private theorem not_all_of_inWin {n : ℕ} (h : inWin n = true) (h1 : 200 ≤ n)
    (h2 : n ≤ 1000000) : ¬ AllPrimeMinusTwoSq n := by
  simp only [inWin, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · omega
  · omega
  · exact not_all_of_anyP h

/-- `inWin` on the six surviving residue classes in the block `210 k + [0, 210)`. -/
private noncomputable def checkClass (k : ℕ) : Bool :=
  inWin (210 * k + 19) && inWin (210 * k + 31) && inWin (210 * k + 61) &&
    inWin (210 * k + 139) && inWin (210 * k + 181) && inWin (210 * k + 199)

private theorem inWin_of_checkClass {k : ℕ} (h : checkClass k = true) (n : ℕ)
    (hn : n % 210 ∈ ({19, 31, 61, 139, 181, 199} : Finset ℕ)) (hk : n / 210 = k) :
    inWin n = true := by
  simp only [checkClass, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h19, h31⟩, h61⟩, h139⟩, h181⟩, h199⟩ := h
  have hdiv : n = 210 * k + n % 210 := by rw [← hk]; exact (Nat.div_add_mod n 210).symm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with hr | hr | hr | hr | hr | hr <;> rw [hr] at hdiv <;> rw [hdiv]
  · exact h19
  · exact h31
  · exact h61
  · exact h139
  · exact h181
  · exact h199

/-- Linear sweep: `checkClass (lo + i)` for all `i < len`. -/
private noncomputable def linSweep (lo len : ℕ) : Bool :=
  Nat.rec true (fun i acc => checkClass (lo + i) && acc) len

private theorem checkClass_of_linSweep {lo len : ℕ} (h : linSweep lo len = true) :
    ∀ i < len, checkClass (lo + i) = true := by
  induction len with
  | zero => intro i hi; omega
  | succ len ih =>
    have hunfold : linSweep lo (len + 1) = (checkClass (lo + len) && linSweep lo len) := rfl
    rw [hunfold, Bool.and_eq_true] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact ih h.2 i hlt
    · rw [heq]; exact h.1

/-- Binary-split sweep of depth `d` (keeps kernel recursion depth small). -/
private noncomputable def treeSweep (d : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (fun lo len => linSweep lo len)
    (fun _ ih lo len => ih lo (len / 2) && ih (lo + len / 2) (len - len / 2)) d

private theorem checkClass_of_treeSweep {d : ℕ} : ∀ {lo len : ℕ}, treeSweep d lo len = true →
    ∀ i < len, checkClass (lo + i) = true := by
  induction d with
  | zero => intro lo len h; exact checkClass_of_linSweep h
  | succ d ih =>
    intro lo len h i hi
    have hunfold : treeSweep (d + 1) lo len =
        (treeSweep d lo (len / 2) && treeSweep d (lo + len / 2) (len - len / 2)) := rfl
    rw [hunfold, Bool.and_eq_true] at h
    by_cases hi2 : i < len / 2
    · exact ih h.1 i hi2
    · have hright := ih h.2 (i - len / 2) (by omega)
      rwa [show lo + len / 2 + (i - len / 2) = lo + i by omega] at hright

/-- The kernel computation: every block `k < 4762` (covering `n ≤ 10⁶`) passes.
    Ordinary kernel reduction (`decide +kernel`), no `native_decide`. -/
private theorem treeSweep_window : treeSweep 7 0 4762 = true := by decide +kernel

/-- Finite window: no further members up to 10⁶.
    -- PROVABLE (native_decide; the per-n check is O(√n) primality
    tests — same scaling as the ErdosMinus2k window sweeps.  Kernel
    `decide` will not reach 10⁶; stage at 10⁴ first). -/
theorem window_1e6 :
    ∀ n ∈ Finset.Icc 200 1000000, ¬ AllPrimeMinusTwoSq n := by
  intro n hn
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  by_cases hs : n % 210 ∈ ({19, 31, 61, 139, 181, 199} : Finset ℕ)
  · have hk : n / 210 < 4762 := by omega
    have hc : checkClass (0 + n / 210) = true := checkClass_of_treeSweep treeSweep_window _ hk
    rw [Nat.zero_add] at hc
    exact not_all_of_inWin (inWin_of_checkClass hc n hs rfl) h1 h2
  · exact not_all_of_not_survivor h1 hs

/-- **Erdős #1140, resolution (Mollin–Williams + Epure–Gica)**: the set
    of such `n` is finite — the answer to the problem is NO.

    Source: "Do there exist infinitely many $n$ such that $n-2x^2$ is
    prime for all $x$ with $2x^2<n$?"  Disproved: the known members are
    2, 5, 7, 13, 31, 61, 181, 199 with at most one further exception
    (real quadratic class-number-one methods).  The class-number input
    is far outside current Mathlib — this stays archived; the
    certificates and window above are also admitted targets, not a sorry-free layer. -/
theorem erdos_1140_finite : {n : ℕ | AllPrimeMinusTwoSq n}.Finite := by
  sorry

/-- **Epure–Gica exact form for n ≡ 1 (mod 4)** (Thm 4.1, archived):
    the only members ≡ 1 (mod 4) are 5, 13, 61, 181 — no exception in
    this class. -/
theorem epure_gica_one_mod_four :
    {n : ℕ | AllPrimeMinusTwoSq n ∧ n % 4 = 1} = {5, 13, 61, 181} := by
  sorry

end ErdosCandidates.E1140

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Disposition: retained admitted archive; raw zero case is vacuous
   - Statement matches source verbatim; known list {2,5,7,13,31,61,181,199} verified.
   - Non-membership of 3 (3-2=1 not prime) and 11 (11-2=9 not prime) verified.
   - Epure-Gica mod-4 split and Mollin-Williams attribution match source sections.
   - AllPrimeMinusTwoSq predicate correctly uses strict ineq 2*x^2 < n; NAT-subtraction
     is exact under that guard. For positive n, x=0 forces n prime; at n=0
     the predicate is vacuous, so the positive known list is not exhaustive for the raw predicate.
   - Comment-sourced claims (Woett, Chojecki, GRH route) flagged as such in header.
   - Mathlib inventory (Nat.Prime, Nat.decidablePrime) correct.
-/
