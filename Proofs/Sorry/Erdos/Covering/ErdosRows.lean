/- Existing archived conjecture/dependent declarations, relocated unchanged.
Production definitions and finite certificates remain in `Erdos.Covering.ErdosRows`. -/
import Erdos.Covering.ErdosRows
import Sorry.Erdos.Covering.ErdosMinus2k

set_option autoImplicit false

namespace Erdos.Covering

/-- **The A089654 conjecture** (OEIS A089654 comment, pinned 2026-07-30:
"P. Erdos conjectures that T(n,k) are all primes for n = 3, 7, 10, 22,
37, 52 and these are the only values of n with property").

OPEN, but **not an independent `sorry`**: it is derived here from the
archived `Erdos.Covering.erdos_1142` through the §3 bridge and the §4
index bijection, so this file adds no `sorry` of its own. That
derivation is the content: A089654's conjecture is A039669's conjecture
restricted to odd `m`, and nothing more. -/
theorem erdos_a089654 {n : ℕ} (hn : 0 < n) (h : ∀ x ∈ erdosRowList n, Nat.Prime x) :
    n ∈ ({3, 7, 10, 22, 37, 52} : Finset ℕ) := by
  have hm : IsAllPrimeMinusPow (2 * n + 1) :=
    (forall_prime_erdosRowList_iff_isAllPrimeMinusPow hn).mp h
  have hmem := erdos_1142 (2 * n + 1) hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
  omega

/-- A089654's all-prime rows as a set, granting `erdos_1142`. No new
`sorry`; `sorryAx`-dependent through `erdos_1142` alone. -/
theorem setOf_forall_prime_erdosRowList_of_erdos_1142 :
    {n : ℕ | 0 < n ∧ ∀ x ∈ erdosRowList n, Nat.Prime x} =
      ({3, 7, 10, 22, 37, 52} : Set ℕ) := by
  ext n
  constructor
  · rintro ⟨hn, h⟩
    have hmem := erdos_a089654 hn h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨by norm_num, forall_prime_erdosRowList_3⟩,
      ⟨by norm_num, forall_prime_erdosRowList_7⟩,
      ⟨by norm_num, forall_prime_erdosRowList_10⟩,
      ⟨by norm_num, forall_prime_erdosRowList_22⟩,
      ⟨by norm_num, forall_prime_erdosRowList_37⟩,
      ⟨by norm_num, forall_prime_erdosRowList_52⟩]

end Erdos.Covering
