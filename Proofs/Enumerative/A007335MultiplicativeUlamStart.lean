/-
# A007335: multiplicative Ulam numbers

OEIS A007335: Rémy Sigrist's characterization (Feb 16 2023) and Amiram
Eldar's reciprocal-sum conjecture (Jul 31 2022).
Related reference: Kravitz-Steinerberger, "Ulam sequences and Ulam sets",
arXiv:1705.01883. The proof below is self-contained.
Starting from `2, 3`, append the least larger number that is a product of
two distinct earlier terms in exactly one way. The members are exactly
`2^v 3^w` with `v = 1`, `w = 1`, or both exponents odd.
The greedy-rule theorem identifies the nth enumeration, and its reciprocal
series has sum `181/144 = 1/4 + 9/16 + 4/9`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A007335MultiplicativeUlamStart

/-! ## Definitions -/

/-- `Admits S n`: given the finite set `S` of earlier terms, the number `n` is admitted to
the sequence, i.e. `n` is one of the seeds `2, 3`, or `n > 3` and `n` is the product `u * w`
of two distinct elements `u < w` of `S` in exactly one way. -/
def Admits (S : Finset ℕ) (n : ℕ) : Prop :=
  n = 2 ∨ n = 3 ∨ (3 < n ∧ ((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ p.1 * p.2 = n)).card = 1)

/-- Decidability of `Admits`, for finite checks. -/
instance (S : Finset ℕ) (n : ℕ) : Decidable (Admits S n) := by
  unfold Admits; infer_instance

/-- `muUpTo N` is the set of MU-numbers `≤ N`, built greedily: the candidate `N + 1` is
admitted iff it is admitted relative to the MU-numbers `≤ N`. -/
def muUpTo : ℕ → Finset ℕ
  | 0 => ∅
  | N + 1 => if Admits (muUpTo N) (N + 1) then insert (N + 1) (muUpTo N) else muUpTo N

/-- `IsMU n`: `n` is an MU-number (a term of A007335). By construction (see `isMU_iff`)
this is the strong recursion: `n` is `2` or `3`, or `3 < n` and `n` is a product `u * w`
of two MU-numbers `u < w` in exactly one way. -/
def IsMU (n : ℕ) : Prop := n ∈ muUpTo n

/-- Decidability of `IsMU`, for finite checks. -/
instance : DecidablePred IsMU := fun n => by unfold IsMU; infer_instance

/-- `mu k` is the MU-number of index `k`, counted from `0`: OEIS `a(k + 1) = mu k`
(the entry has offset 1, `a(1) = 2`). -/
noncomputable def mu (k : ℕ) : ℕ := Nat.nth IsMU k

/-- `mu 0 = 2`, i.e. OEIS `a(1) = 2`. -/
lemma mu_zero : mu 0 = 2 := by
  have h := Nat.nth_count (p := IsMU) (n := 2) (by decide)
  rwa [show Nat.count IsMU 2 = 0 by decide] at h

/-- `mu 1 = 3`, i.e. OEIS `a(2) = 3`. -/
lemma mu_one : mu 1 = 3 := by
  have h := Nat.nth_count (p := IsMU) (n := 3) (by decide)
  rwa [show Nat.count IsMU 3 = 1 by decide] at h

/-- The exponent condition `x = 1 ∨ y = 1 ∨ (x, y both odd)`, in `omega`-friendly form. -/
def Good (x y : ℕ) : Prop := x = 1 ∨ y = 1 ∨ (x % 2 = 1 ∧ y % 2 = 1)

/-- Sigrist's target set: numbers `2^a 3^b` with `a = 1`, or `b = 1`, or `a` and `b` both
odd. -/
def InT (n : ℕ) : Prop := ∃ a b, n = 2 ^ a * 3 ^ b ∧ (a = 1 ∨ b = 1 ∨ (Odd a ∧ Odd b))

/-! ## Examples against the OEIS DATA line -/

set_option maxRecDepth 20000 in
-- The MU-numbers below `217` are exactly the first twelve listed terms.
example : (List.range 217).filter (fun n => decide (IsMU n)) =
    [2, 3, 6, 12, 18, 24, 48, 54, 96, 162, 192, 216] := by decide

-- `9 = 3 * 3` (not distinct) and `36 = 2 * 18 = 3 * 12` (two ways) are excluded.
set_option maxRecDepth 20000 in
example : ¬IsMU 9 ∧ ¬IsMU 36 ∧ IsMU 6 ∧ IsMU 12 := by decide

-- The indexed sequence: `a(1), a(2), a(3), a(4) = 2, 3, 6, 12`.
example : mu 0 = 2 ∧ mu 1 = 3 ∧ mu 2 = 6 ∧ mu 3 = 12 := by
  refine ⟨mu_zero, mu_one, ?_, ?_⟩
  · have h := Nat.nth_count (p := IsMU) (n := 6) (by decide)
    rwa [show Nat.count IsMU 6 = 2 by decide] at h
  · have h := Nat.nth_count (p := IsMU) (n := 12) (by decide)
    rwa [show Nat.count IsMU 12 = 3 by decide] at h

-- Sigrist's set at the boundary: `2, 3, 6` are in it, `1, 4, 9, 36` are not witnessed by
-- the obvious exponents (`(0,0)`, `(2,0)`, `(0,2)`, `(2,2)` fail the parity condition).
example : InT 2 ∧ InT 3 ∧ InT 6 :=
  ⟨⟨1, 0, rfl, Or.inl rfl⟩, ⟨0, 1, rfl, Or.inr (Or.inl rfl)⟩, ⟨1, 1, rfl, Or.inl rfl⟩⟩

/-! ## Proofs -/


/-- `sm x y = 2 ^ x * 3 ^ y`. -/
def sm (x y : ℕ) : ℕ := 2 ^ x * 3 ^ y

/-- The exponent of `2` in `sm x y` is `x`. -/
lemma sm_factorization_two (x y : ℕ) : (sm x y).factorization 2 = x := by
  have h32 : (Nat.factorization 3) 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [sm, Nat.factorization_mul (by positivity) (by positivity)]
  simp [Nat.Prime.factorization_self Nat.prime_two, h32]

/-- The exponent of `3` in `sm x y` is `y`. -/
lemma sm_factorization_three (x y : ℕ) : (sm x y).factorization 3 = y := by
  have h23 : (Nat.factorization 2) 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [sm, Nat.factorization_mul (by positivity) (by positivity)]
  simp [Nat.Prime.factorization_self Nat.prime_three, h23]

/-- `2 ^ x * 3 ^ y` determines `(x, y)`. -/
lemma sm_inj {x y x' y' : ℕ} : sm x y = sm x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    exact ⟨by rw [← sm_factorization_two x y, h, sm_factorization_two],
      by rw [← sm_factorization_three x y, h, sm_factorization_three]⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Exponents add under multiplication. -/
lemma sm_mul (x y x' y' : ℕ) : sm x y * sm x' y' = sm (x + x') (y + y') := by
  simp only [sm, pow_add]
  ring


/-- Uniqueness of the ordered factorization from an unordered one. -/
lemma existsUnique_of_unordered (P : ℕ → Prop) (n X Y : ℕ) (hXY : X ≠ Y)
    (hprod : X * Y = n) (hX : P X) (hY : P Y)
    (hall : ∀ u w, u * w = n → P u → P w → (u = X ∧ w = Y) ∨ (u = Y ∧ w = X)) :
    ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.1 * p.2 = n ∧ P p.1 ∧ P p.2 := by
  rcases lt_or_gt_of_ne hXY with hlt | hlt
  · refine ⟨(X, Y), ⟨hlt, hprod, hX, hY⟩, ?_⟩
    rintro ⟨u, w⟩ ⟨huw, hn, hu, hw⟩
    rcases hall u w hn hu hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd (huw.trans hlt) (lt_irrefl _)
  · refine ⟨(Y, X), ⟨hlt, by rw [mul_comm, hprod], hY, hX⟩, ?_⟩
    rintro ⟨u, w⟩ ⟨huw, hn, hu, hw⟩
    rcases hall u w hn hu hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd (huw.trans hlt) (lt_irrefl _)
    · rfl

/-- Two genuinely different unordered factorizations rule out uniqueness. -/
lemma not_existsUnique_of_two (P : ℕ → Prop) (n u₁ w₁ u₂ w₂ : ℕ)
    (h₁ : u₁ ≠ w₁) (h₂ : u₂ ≠ w₂) (hp₁ : u₁ * w₁ = n) (hp₂ : u₂ * w₂ = n)
    (hu₁ : P u₁) (hw₁ : P w₁) (hu₂ : P u₂) (hw₂ : P w₂)
    (hd : ¬(u₁ = u₂ ∧ w₁ = w₂)) (hd' : ¬(u₁ = w₂ ∧ w₁ = u₂)) :
    ¬∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.1 * p.2 = n ∧ P p.1 ∧ P p.2 := by
  rintro ⟨p, hp, huniq⟩
  have key : ∀ u w, u ≠ w → u * w = n → P u → P w → (u = p.1 ∧ w = p.2) ∨ (u = p.2 ∧ w = p.1) := by
    intro u w hne hn hu hw
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · left
      have hpe := huniq (u, w) ⟨hlt, hn, hu, hw⟩
      rw [← hpe]
      exact ⟨rfl, rfl⟩
    · right
      have hpe := huniq (w, u) ⟨hlt, by rw [mul_comm, hn], hw, hu⟩
      rw [← hpe]
      exact ⟨rfl, rfl⟩
  rcases key u₁ w₁ h₁ hp₁ hu₁ hw₁ with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
    rcases key u₂ w₂ h₂ hp₂ hu₂ hw₂ with ⟨a2, b2⟩ | ⟨a2, b2⟩
  · exact hd ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · exact hd' ⟨a1.trans b2.symm, b1.trans a2.symm⟩
  · exact hd' ⟨a1.trans b2.symm, b1.trans a2.symm⟩
  · exact hd ⟨a1.trans a2.symm, b1.trans b2.symm⟩

/-- `InT` in exponent form. -/
lemma inT_iff (n : ℕ) : InT n ↔ ∃ x y, n = sm x y ∧ Good x y := by
  simp only [InT, sm, Good, Nat.odd_iff]

/-- Exponent-level uniqueness. -/
lemma existsUnique_sm (x₁ y₁ x₂ y₂ : ℕ) (h₁ : Good x₁ y₁) (h₂ : Good x₂ y₂)
    (hne : ¬(x₁ = x₂ ∧ y₁ = y₂))
    (hall : ∀ z₁ w₁ z₂ w₂, Good z₁ w₁ → Good z₂ w₂ → z₁ + z₂ = x₁ + x₂ →
      w₁ + w₂ = y₁ + y₂ → (z₁ = x₁ ∧ w₁ = y₁ ∧ z₂ = x₂ ∧ w₂ = y₂) ∨
        (z₁ = x₂ ∧ w₁ = y₂ ∧ z₂ = x₁ ∧ w₂ = y₁)) :
    ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.1 * p.2 = sm (x₁ + x₂) (y₁ + y₂) ∧ InT p.1 ∧ InT p.2 := by
  refine existsUnique_of_unordered InT _ (sm x₁ y₁) (sm x₂ y₂)
    (fun h => hne (sm_inj.mp h)) (sm_mul _ _ _ _)
    ((inT_iff _).mpr ⟨_, _, rfl, h₁⟩) ((inT_iff _).mpr ⟨_, _, rfl, h₂⟩) ?_
  intro u w huw hu hw
  obtain ⟨z₁, w₁, rfl, hg₁⟩ := (inT_iff u).mp hu
  obtain ⟨z₂, w₂, rfl, hg₂⟩ := (inT_iff w).mp hw
  rw [sm_mul, sm_inj] at huw
  rcases hall z₁ w₁ z₂ w₂ hg₁ hg₂ huw.1 huw.2 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- Exponent-level non-uniqueness. -/
lemma not_existsUnique_sm (a b x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℕ)
    (g₁ : Good x₁ y₁) (g₂ : Good x₂ y₂) (g₃ : Good x₃ y₃) (g₄ : Good x₄ y₄)
    (ha : x₁ + x₂ = a) (hb : y₁ + y₂ = b) (ha' : x₃ + x₄ = a) (hb' : y₃ + y₄ = b)
    (hne₁ : ¬(x₁ = x₂ ∧ y₁ = y₂)) (hne₂ : ¬(x₃ = x₄ ∧ y₃ = y₄))
    (hd : ¬(x₁ = x₃ ∧ y₁ = y₃)) (hd' : ¬(x₁ = x₄ ∧ y₁ = y₄)) :
    ¬∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.1 * p.2 = sm a b ∧ InT p.1 ∧ InT p.2 := by
  subst ha hb
  refine not_existsUnique_of_two InT _ (sm x₁ y₁) (sm x₂ y₂) (sm x₃ y₃) (sm x₄ y₄)
    (fun h => hne₁ (sm_inj.mp h)) (fun h => hne₂ (sm_inj.mp h)) (sm_mul _ _ _ _) ?_
    ((inT_iff _).mpr ⟨_, _, rfl, g₁⟩) ((inT_iff _).mpr ⟨_, _, rfl, g₂⟩)
    ((inT_iff _).mpr ⟨_, _, rfl, g₃⟩) ((inT_iff _).mpr ⟨_, _, rfl, g₄⟩)
    (fun h => hd (sm_inj.mp h.1)) (fun h => hd' (sm_inj.mp h.1))
  rw [sm_mul, ha', hb']


/-- The combinatorial heart: for `3 < n`, `n` lies in the target set iff it has exactly
one factorization `u * w` with `u < w` and both factors in the target set. -/
theorem inT_iff_existsUnique (n : ℕ) (hn : 3 < n) :
    InT n ↔ ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.1 * p.2 = n ∧ InT p.1 ∧ InT p.2 := by
  constructor
  · intro hT
    obtain ⟨a, b, rfl, hg⟩ := (inT_iff n).mp hT
    have hsmall : ¬((a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1)) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [sm] at hn
    unfold Good at hg
    by_cases hodd : a % 2 = 1 ∧ b % 2 = 1
    · have e : sm a b = sm (1 + (a - 1)) ((b - 1) + 1) := by
        rw [sm_inj]; omega
      rw [e]
      refine existsUnique_sm 1 (b - 1) (a - 1) 1 (by unfold Good; omega)
        (by unfold Good; omega) (by omega) ?_
      intro z₁ w₁ z₂ w₂ g₁ g₂ hz hw
      unfold Good at g₁ g₂
      omega
    · by_cases ha : a = 1
      · have e : sm a b = sm (0 + 1) (1 + (b - 1)) := by
          rw [sm_inj]; omega
        rw [e]
        refine existsUnique_sm 0 1 1 (b - 1) (by unfold Good; omega)
          (by unfold Good; omega) (by omega) ?_
        intro z₁ w₁ z₂ w₂ g₁ g₂ hz hw
        unfold Good at g₁ g₂
        omega
      · have e : sm a b = sm (1 + (a - 1)) (0 + 1) := by
          rw [sm_inj]; omega
        rw [e]
        refine existsUnique_sm 1 0 (a - 1) 1 (by unfold Good; omega)
          (by unfold Good; omega) (by omega) ?_
        intro z₁ w₁ z₂ w₂ g₁ g₂ hz hw
        unfold Good at g₁ g₂
        omega
  · intro hEU
    obtain ⟨p, ⟨hlt, hprod, hu, hw⟩, -⟩ := id hEU
    obtain ⟨a₁, b₁, hp₁, g₁⟩ := (inT_iff _).mp hu
    obtain ⟨a₂, b₂, hp₂, g₂⟩ := (inT_iff _).mp hw
    rw [hp₁, hp₂, sm_mul] at hprod
    rw [hp₁, hp₂] at hlt
    have hne : ¬(a₁ = a₂ ∧ b₁ = b₂) := by
      rintro ⟨rfl, rfl⟩
      exact lt_irrefl _ hlt
    by_contra hT
    have hG : ¬Good (a₁ + a₂) (b₁ + b₂) := fun g => hT ((inT_iff n).mpr ⟨_, _, hprod.symm, g⟩)
    obtain ⟨a, ha⟩ : ∃ a, a₁ + a₂ = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b₁ + b₂ = b := ⟨_, rfl⟩
    rw [ha, hb] at hprod
    rw [ha, hb] at hG
    subst hprod
    unfold Good at g₁ g₂ hG
    have ha0 : a ≠ 0 := by
      rintro rfl
      have h1 : a₁ = 0 := by omega
      have h2 : a₂ = 0 := by omega
      subst h1 h2
      omega
    have hb0 : b ≠ 0 := by
      rintro rfl
      have h1 : b₁ = 0 := by omega
      have h2 : b₂ = 0 := by omega
      subst h1 h2
      omega
    clear g₁ g₂ hne hlt hu hw hp₁ hp₂ ha hb hT
    push Not at hG
    rcases Nat.mod_two_eq_zero_or_one a with hpa | hpa <;>
      rcases Nat.mod_two_eq_zero_or_one b with hpb | hpb
    · by_cases ha2 : a = 2 <;> by_cases hb2 : b = 2
      · exact not_existsUnique_sm a b 0 1 2 1 1 0 1 2 (by unfold Good; omega)
          (by unfold Good; omega) (by unfold Good; omega) (by unfold Good; omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) hEU
      · exact not_existsUnique_sm a b 1 0 1 b 1 1 1 (b - 1) (by unfold Good; omega)
          (by unfold Good; omega) (by unfold Good; omega) (by unfold Good; omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) hEU
      · exact not_existsUnique_sm a b 0 1 a 1 1 1 (a - 1) 1 (by unfold Good; omega)
          (by unfold Good; omega) (by unfold Good; omega) (by unfold Good; omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) hEU
      · exact not_existsUnique_sm a b 1 1 (a - 1) (b - 1) 1 (b - 1) (a - 1) 1
          (by unfold Good; omega)
          (by unfold Good; omega) (by unfold Good; omega) (by unfold Good; omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) hEU
    · exact not_existsUnique_sm a b 1 0 (a - 1) b 1 2 (a - 1) (b - 2) (by unfold Good; omega)
        (by unfold Good; omega) (by unfold Good; omega) (by unfold Good; omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hEU
    · exact not_existsUnique_sm a b 0 1 a (b - 1) 2 1 (a - 2) (b - 1) (by unfold Good; omega)
        (by unfold Good; omega) (by unfold Good; omega) (by unfold Good; omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hEU
    · omega


/-- One greedy step of `muUpTo`. -/
lemma mem_muUpTo_succ {N m : ℕ} :
    m ∈ muUpTo (N + 1) ↔ m ∈ muUpTo N ∨ (m = N + 1 ∧ Admits (muUpTo N) (N + 1)) := by
  rw [muUpTo]
  split_ifs with h
  · simp [h, or_comm]
  · simp [h]

/-- Elements of `muUpTo N` are at most `N`. -/
lemma le_of_mem_muUpTo {N m : ℕ} (h : m ∈ muUpTo N) : m ≤ N := by
  induction N with
  | zero => simp [muUpTo] at h
  | succ N ih =>
    rcases mem_muUpTo_succ.mp h with h | ⟨rfl, -⟩
    · exact (ih h).trans (Nat.le_succ N)
    · exact le_rfl

/-- `N + 1` is an MU-number iff it is admitted relative to `muUpTo N`. -/
lemma isMU_succ_iff (N : ℕ) : IsMU (N + 1) ↔ Admits (muUpTo N) (N + 1) := by
  rw [IsMU, mem_muUpTo_succ]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact absurd (le_of_mem_muUpTo h) (by omega)
    · exact h
  · exact fun h => Or.inr ⟨rfl, h⟩

/-- `muUpTo N` is exactly the set of MU-numbers `≤ N`. -/
lemma mem_muUpTo_iff {N m : ℕ} : m ∈ muUpTo N ↔ m ≤ N ∧ IsMU m := by
  induction N with
  | zero =>
    constructor
    · intro h; simp [muUpTo] at h
    · rintro ⟨h, h2⟩
      obtain rfl : m = 0 := by omega
      exact h2
  | succ N ih =>
    rw [mem_muUpTo_succ, ih]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨rfl, h⟩)
      · exact ⟨h1.trans (Nat.le_succ N), h2⟩
      · exact ⟨le_rfl, (isMU_succ_iff N).mpr h⟩
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge m (N + 1) with hlt | hge
      · exact Or.inl ⟨by omega, h2⟩
      · obtain rfl : m = N + 1 := by omega
        exact Or.inr ⟨rfl, (isMU_succ_iff N).mp h2⟩

/-- Every MU-number is at least `2`. -/
lemma two_le_of_isMU {m : ℕ} (h : IsMU m) : 2 ≤ m := by
  rcases m with _ | _ | m
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · omega

/-- The defining recursion of the MU-numbers. -/
theorem isMU_iff (n : ℕ) : IsMU n ↔ n = 2 ∨ n = 3 ∨
    (3 < n ∧ ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.1 * p.2 = n ∧ IsMU p.1 ∧ IsMU p.2) := by
  rcases n with _ | N
  · simp only [IsMU, muUpTo]
    simp
  rw [isMU_succ_iff, Admits]
  refine or_congr_right (or_congr_right (and_congr_right fun hN => ?_))
  rw [Finset.card_eq_one]
  have hmem : ∀ p : ℕ × ℕ, p ∈ (muUpTo N ×ˢ muUpTo N).filter
      (fun p => p.1 < p.2 ∧ p.1 * p.2 = N + 1) ↔
        p.1 < p.2 ∧ p.1 * p.2 = N + 1 ∧ IsMU p.1 ∧ IsMU p.2 := by
    rintro ⟨u, w⟩
    simp only [Finset.mem_filter, Finset.mem_product, mem_muUpTo_iff]
    constructor
    · rintro ⟨⟨⟨-, hu⟩, -, hw⟩, hlt, hprod⟩
      exact ⟨hlt, hprod, hu, hw⟩
    · rintro ⟨hlt, hprod, hu, hw⟩
      have h2 := two_le_of_isMU hu
      have hw' : w < N + 1 := by nlinarith
      exact ⟨⟨⟨by omega, hu⟩, by omega, hw⟩, hlt, hprod⟩
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, (hmem p).mp (by rw [hp]; exact Finset.mem_singleton_self p), fun q hq => ?_⟩
    have hqs := (hmem q).mpr hq
    rw [hp] at hqs
    exact Finset.mem_singleton.mp hqs
  · rintro ⟨p, hp, huniq⟩
    refine ⟨p, Finset.eq_singleton_iff_unique_mem.mpr ⟨(hmem p).mpr hp, fun q hq => ?_⟩⟩
    exact huniq q ((hmem q).mp hq)

/-- Every element of the target set is at least `2`. -/
lemma two_le_of_inT {m : ℕ} (h : InT m) : 2 ≤ m := by
  obtain ⟨a, b, rfl, hg⟩ := (inT_iff m).mp h
  unfold Good at hg
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hb : 1 ≤ b := by omega
    have h3b : 3 ≤ 3 ^ b := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    simp only [sm, pow_zero, one_mul]
    omega
  · have h2a : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    simp only [sm]
    nlinarith

/-- Sigrist's characterization, internal form: `IsMU n ↔ InT n`. -/
theorem isMU_iff_inT (n : ℕ) : IsMU n ↔ InT n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge 3 n with hn | hn
  · rw [isMU_iff, inT_iff_existsUnique n hn]
    have hne2 : n ≠ 2 := by omega
    have hne3 : n ≠ 3 := by omega
    simp only [hne2, hne3, hn, true_and, false_or]
    have hcong : ∀ p : ℕ × ℕ, (p.1 < p.2 ∧ p.1 * p.2 = n ∧ IsMU p.1 ∧ IsMU p.2) ↔
        (p.1 < p.2 ∧ p.1 * p.2 = n ∧ InT p.1 ∧ InT p.2) := by
      rintro ⟨u, w⟩
      dsimp only
      constructor
      · rintro ⟨hlt, hprod, hu, hw⟩
        have h2 := two_le_of_isMU hu
        have hu' : u < n := by nlinarith
        have hw' : w < n := by nlinarith
        exact ⟨hlt, hprod, (ih u hu').mp hu, (ih w hw').mp hw⟩
      · rintro ⟨hlt, hprod, hu, hw⟩
        have h2 := two_le_of_inT hu
        have hu' : u < n := by nlinarith
        have hw' : w < n := by nlinarith
        exact ⟨hlt, hprod, (ih u hu').mpr hu, (ih w hw').mpr hw⟩
    exact existsUnique_congr hcong
  · have h0 : ¬InT 0 := fun h => by
      obtain ⟨a, b, hab, -⟩ := (inT_iff 0).mp h
      exact absurd hab.symm (by unfold sm; positivity)
    have h1 : ¬InT 1 := fun h => by
      obtain ⟨a, b, hab, hg⟩ := (inT_iff 1).mp h
      obtain ⟨rfl, rfl⟩ := sm_inj.mp (show sm 0 0 = sm a b from hab)
      unfold Good at hg
      omega
    have h2 : InT 2 := (inT_iff 2).mpr ⟨1, 0, rfl, Or.inl rfl⟩
    have h3 : InT 3 := (inT_iff 3).mpr ⟨0, 1, rfl, Or.inr (Or.inl rfl)⟩
    interval_cases n
    · exact iff_of_false (by decide) h0
    · exact iff_of_false (by decide) h1
    · exact iff_of_true (by decide) h2
    · exact iff_of_true (by decide) h3


/-- `2 ^ x * 3 ^ y` is an MU-number iff `Good x y`. -/
lemma isMU_sm_iff (x y : ℕ) : IsMU (sm x y) ↔ Good x y := by
  rw [isMU_iff_inT, inT_iff]
  constructor
  · rintro ⟨x', y', h, hg⟩
    obtain ⟨rfl, rfl⟩ := sm_inj.mp h
    exact hg
  · exact fun hg => ⟨x, y, rfl, hg⟩

/-- There are infinitely many MU-numbers (e.g. all `2 * 3 ^ b`). -/
lemma isMU_infinite : (Set.ofPred IsMU).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun b : ℕ => sm 1 b) ?_ ?_
  · intro b b' h
    exact (sm_inj.mp h).2
  · intro b
    exact (isMU_sm_iff 1 b).mpr (Or.inl rfl)

/-- Parametrization of the MU-numbers by the three exponent families: `inl (i, j)` gives
`2^(2i+1) 3^(2j+1)` (both exponents odd), `inr (inl j)` gives `2 * 3^(2j)`, and
`inr (inr i)` gives `2^(2i) * 3`. -/
def param : (ℕ × ℕ) ⊕ (ℕ ⊕ ℕ) → ℕ
  | Sum.inl (i, j) => sm (2 * i + 1) (2 * j + 1)
  | Sum.inr (Sum.inl j) => sm 1 (2 * j)
  | Sum.inr (Sum.inr i) => sm (2 * i) 1

/-- The parametrization is injective. -/
lemma param_injective : Function.Injective param := by
  rintro (⟨i, j⟩ | j | i) (⟨i', j'⟩ | j' | i') h <;> simp only [param, sm_inj] at h <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] <;> omega

/-- The parametrization lands in the MU-numbers. -/
lemma isMU_param (z : (ℕ × ℕ) ⊕ (ℕ ⊕ ℕ)) : IsMU (param z) := by
  rcases z with ⟨i, j⟩ | j | i <;> rw [param, isMU_sm_iff] <;> unfold Good <;> omega

/-- Every MU-number is in the range of the parametrization. -/
lemma mem_range_param {n : ℕ} (h : IsMU n) : n ∈ Set.range param := by
  obtain ⟨x, y, rfl, hg⟩ := (inT_iff n).mp ((isMU_iff_inT n).mp h)
  unfold Good at hg
  by_cases hodd : x % 2 = 1 ∧ y % 2 = 1
  · refine ⟨Sum.inl ((x - 1) / 2, (y - 1) / 2), ?_⟩
    rw [param, sm_inj]; omega
  · by_cases hx : x = 1
    · refine ⟨Sum.inr (Sum.inl (y / 2)), ?_⟩
      rw [param, sm_inj]; omega
    · refine ⟨Sum.inr (Sum.inr (x / 2)), ?_⟩
      rw [param, sm_inj]; omega


/-- The reciprocal `1 / n` on MU-numbers, extended by zero elsewhere. -/
noncomputable def recipMU (n : ℕ) : ℝ := if IsMU n then 1 / (n : ℝ) else 0

/-- The reciprocal sum over the three families: `1/4 + 9/16 + 4/9 = 181/144`. -/
lemma hasSum_param : HasSum (recipMU ∘ param) (181 / 144) := by
  have hval : ∀ z, (recipMU ∘ param) z = 1 / (param z : ℝ) := fun z => by
    simp only [Function.comp, recipMU, if_pos (isMU_param z)]
  have h4 := hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have h9 := hasSum_geometric_of_lt_one (r := (1 / 9 : ℝ)) (by norm_num) (by norm_num)
  have hO : HasSum ((recipMU ∘ param) ∘ Sum.inl) (1 / 4) := by
    have hprod := h4.mul h9 (Summable.mul_of_nonneg h4.summable h9.summable
      (fun _ => by positivity) (fun _ => by positivity))
    have hfun : (recipMU ∘ param) ∘ Sum.inl =
        fun z : ℕ × ℕ => 1 / 6 * ((1 / 4 : ℝ) ^ z.1 * (1 / 9 : ℝ) ^ z.2) := by
      funext ⟨i, j⟩
      rw [Function.comp_apply, hval, param, sm]
      push_cast
      rw [pow_succ, pow_succ, pow_mul, pow_mul, one_div_pow, one_div_pow]
      field_simp
      ring
    have hsum := hprod.mul_left (1 / 6)
    rw [show (1 / 6 : ℝ) * ((1 - 1 / 4)⁻¹ * (1 - 1 / 9)⁻¹) = 1 / 4 by norm_num] at hsum
    rw [hfun]
    exact hsum
  have hA : HasSum (((recipMU ∘ param) ∘ Sum.inr) ∘ Sum.inl) (9 / 16) := by
    have hfun : ((recipMU ∘ param) ∘ Sum.inr) ∘ Sum.inl =
        fun j : ℕ => 1 / 2 * (1 / 9 : ℝ) ^ j := by
      funext j
      rw [Function.comp_apply, Function.comp_apply, hval, param, sm]
      push_cast
      rw [pow_mul, one_div_pow]
      field_simp
      norm_num
    have hsum := h9.mul_left (1 / 2)
    rw [show (1 / 2 : ℝ) * (1 - 1 / 9)⁻¹ = 9 / 16 by norm_num] at hsum
    rw [hfun]
    exact hsum
  have hB : HasSum (((recipMU ∘ param) ∘ Sum.inr) ∘ Sum.inr) (4 / 9) := by
    have hfun : ((recipMU ∘ param) ∘ Sum.inr) ∘ Sum.inr =
        fun i : ℕ => 1 / 3 * (1 / 4 : ℝ) ^ i := by
      funext i
      rw [Function.comp_apply, Function.comp_apply, hval, param, sm]
      push_cast
      rw [pow_mul, one_div_pow]
      field_simp
      norm_num
    have hsum := h4.mul_left (1 / 3)
    rw [show (1 / 3 : ℝ) * (1 - 1 / 4)⁻¹ = 4 / 9 by norm_num] at hsum
    rw [hfun]
    exact hsum
  rw [show (181 / 144 : ℝ) = 1 / 4 + (9 / 16 + 4 / 9) by norm_num]
  exact hO.sum (hA.sum hB)


/-- The reciprocals of all MU-numbers sum to `181/144`. -/
lemma hasSum_recipMU : HasSum recipMU (181 / 144) := by
  refine (param_injective.hasSum_iff (fun x hx => ?_)).mp hasSum_param
  rw [recipMU, if_neg (fun h => hx (mem_range_param h))]

/-- `mu` is strictly increasing. -/
lemma mu_strictMono : StrictMono mu := Nat.nth_strictMono isMU_infinite

/-- Every `mu k` is an MU-number. -/
lemma isMU_mu (k : ℕ) : IsMU (mu k) := Nat.nth_mem_of_infinite isMU_infinite k

/-- Below the next term, "earlier term" and "MU-number" agree. -/
lemma earlier_iff {k m : ℕ} (hm : m < mu (k + 2)) :
    (∃ i ≤ k + 1, mu i = m) ↔ IsMU m := by
  constructor
  · rintro ⟨i, -, rfl⟩
    exact isMU_mu i
  · intro h
    have hle : m ≤ mu (k + 1) := Nat.le_nth_of_lt_nth_succ hm h
    have hr : m ∈ Set.range mu := by
      rw [show mu = Nat.nth IsMU from rfl, Nat.range_nth_of_infinite isMU_infinite]
      exact h
    obtain ⟨i, rfl⟩ := hr
    exact ⟨i, mu_strictMono.le_iff_le.mp hle, rfl⟩

/-- For `mu (k + 1) < n ≤ mu (k + 2)`, the greedy admission test against the earlier
terms `mu 0, …, mu (k + 1)` agrees with `IsMU n`. -/
lemma greedy_iff {k n : ℕ} (hlo : mu (k + 1) < n) (hhi : n ≤ mu (k + 2)) :
    (∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.1 * p.2 = n ∧ (∃ i ≤ k + 1, mu i = p.1) ∧
      (∃ j ≤ k + 1, mu j = p.2)) ↔ IsMU n := by
  have h3 : 3 < n := by
    have hmono := mu_strictMono.monotone (show 1 ≤ k + 1 by omega)
    rw [mu_one] at hmono
    omega
  rw [isMU_iff n]
  simp only [show n ≠ 2 by omega, show n ≠ 3 by omega, h3, true_and, false_or]
  refine existsUnique_congr fun p => ?_
  rcases p with ⟨u, w⟩
  dsimp only
  constructor
  · rintro ⟨hlt, hprod, hu, hw⟩
    have hu' : IsMU u := by obtain ⟨i, -, rfl⟩ := hu; exact isMU_mu i
    have h2 := two_le_of_isMU hu'
    have hwn : w < n := by nlinarith
    have hun : u < n := by omega
    exact ⟨hlt, hprod, (earlier_iff (by omega)).mp hu, (earlier_iff (by omega)).mp hw⟩
  · rintro ⟨hlt, hprod, hu, hw⟩
    have h2 := two_le_of_isMU hu
    have hwn : w < n := by nlinarith
    have hun : u < n := by omega
    exact ⟨hlt, hprod, (earlier_iff (by omega)).mpr hu, (earlier_iff (by omega)).mpr hw⟩

/-- The greedy rule: for every `k`, `mu (k + 2)` is the
least number exceeding the last term `mu (k + 1)` that is the product `u * w` of two distinct
earlier terms `u < w` (both among `mu 0, …, mu (k + 1)`) in exactly one way. Together with
`mu_zero`, `mu_one` this is exactly the entry's definition of A007335. -/
theorem mu_greedy (k : ℕ) :
    IsLeast {n : ℕ | mu (k + 1) < n ∧ ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.1 * p.2 = n ∧
      (∃ i ≤ k + 1, mu i = p.1) ∧ (∃ j ≤ k + 1, mu j = p.2)} (mu (k + 2)) := by
  have hlt : mu (k + 1) < mu (k + 2) := mu_strictMono (by omega)
  refine ⟨⟨hlt, (greedy_iff hlt le_rfl).mpr (isMU_mu _)⟩, ?_⟩
  rintro n ⟨hlo, hEU⟩
  by_contra hcon
  push Not at hcon
  have hn := (greedy_iff hlo hcon.le).mp hEU
  have hle : n ≤ mu (k + 1) := Nat.le_nth_of_lt_nth_succ hcon hn
  exact absurd hlo (not_lt.mpr hle)

/-- Internal form of Eldar's sum. -/
theorem hasSum_one_div_mu : HasSum (fun k => 1 / (mu k : ℝ)) (181 / 144) := by
  have hcomp : (fun k => 1 / (mu k : ℝ)) = recipMU ∘ Nat.nth IsMU := by
    funext k
    rw [Function.comp_apply, recipMU, if_pos (Nat.nth_mem_of_infinite isMU_infinite k), mu]
  rw [hcomp]
  refine ((Nat.nth_injective isMU_infinite).hasSum_iff (fun x hx => ?_)).mpr hasSum_recipMU
  rw [Nat.range_nth_of_infinite isMU_infinite] at hx
  exact if_neg hx



/-! ## The conjecture and the structure theorem -/

/-- **Sigrist's characterization (A007335, Rémy Sigrist, Feb 16 2023, stated there as
empirical).** A number `n` is an MU-number iff `n = 2^v * 3^w` with `v = 1`, or `w = 1`,
or `v` and `w` both odd. Proved here by strong induction on `n` and parity casework on
the exponent vectors of the factorizations. -/
theorem sigrist_characterization (n : ℕ) :
    IsMU n ↔ ∃ v w : ℕ, n = 2 ^ v * 3 ^ w ∧ (v = 1 ∨ w = 1 ∨ (Odd v ∧ Odd w)) :=
  isMU_iff_inT n

/-- Eldar's A007335 reciprocal sum, stated as `HasSum` over all `mu k`.
The OEIS offset-one term is `a(n) = mu(n-1)`. Splitting into the families
`2^odd 3^odd`, `2*9^j` and `4^i*3` gives `1/4 + 9/16 + 4/9 = 181/144`. -/
theorem eldar_reciprocal_sum : HasSum (fun k : ℕ => 1 / (mu k : ℝ)) (181 / 144) :=
  hasSum_one_div_mu

end Candidates.A007335MultiplicativeUlamStart
