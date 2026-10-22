/-
# Pocklington's primality criterion, with Proth's theorem as a corollary

## Classical source (recorded 2026-10-21)

* H. C. Pocklington, "The determination of the prime or composite nature of
  large numbers by Fermat's theorem", Proc. Cambridge Philos. Soc. 18
  (1914–16), 29–30.
* F. Proth, Comptes Rendus Acad. Sci. Paris 87 (1878), 926.
* R. Crandall and C. Pomerance, *Prime Numbers: A Computational Perspective*,
  2nd ed., §4.1 (Theorem 4.1.3 Pocklington; Theorem 4.1.4 / Proth's test).

## Primary-text correspondence

Pocklington's original two-page paper (read 9 March 1914) gives the local
prime-power step used below: if `p ^ α` is the exact `p`-part of `N - 1`,
the Fermat and coprimality checks force every prime divisor `r` of `N` to
satisfy `p ^ α ∣ r - 1` (p. 29).  It then explicitly combines distinct
prime factors in the resulting congruence condition.  The theorem
`pocklington` is the standard modern packaging of those local conclusions
for a known factor `F` with `N < F ^ 2`; it is not presented as a verbatim
numbered theorem from the original note.

The digitized 1878 page requires qualification rather than verbatim citation.
Its uncorrected Wikisource transcription (quality level 1) renders the author
as “E. Proth” and Theorem III's displayed form as `N = m * 2 ^ k`, omitting
the `+ 1` required for a Proth number; the page scan has the same apparent
formula.  Theorem III also expressly says that `a` is a nonresidue of `N`.
Accordingly, that transcription is recorded only as historical attribution,
not as an exact statement of `proth`.  The theorem below is the standard
modern sufficient form: the assumed congruence to `-1` is itself the
certificate, so its proof needs no separately formalized nonresidue
condition.  It also allows an even coefficient, whose power of two can be
absorbed into the exponent.  Here the result is derived from the fully
stated `pocklington` theorem rather than from the anomalous transcription.

Digitized primary texts: Internet Archive item
`proceedingsofcam1718191316camb`, vol. 18, pp. 29–30; and *Comptes rendus
hebdomadaires des séances de l’Académie des sciences*, vol. 87 (1878),
p. 926, digitized as page 932 of the volume.

## Informal statement (verbatim from the target specification)

```
Let N >= 2 and N - 1 = F R with F^2 > N. Suppose that for each prime q | F
there is a with a^{N-1} ≡ 1 (mod N) and gcd(a^{(N-1)/q} - 1, N) = 1. Then N
is prime. Corollary (Proth): if N = k 2^m + 1 with k < 2^m and
a^{(N-1)/2} ≡ -1 (mod N) for some a, then N is prime.
```

## Encoding

* Residues mod `N` are elements of `ZMod N`; `a ^ (N - 1) ≡ 1 (mod N)` is
  `a ^ (N - 1) = 1` in `ZMod N`, and `gcd(x, N) = 1` for a residue `x` is
  `IsUnit x` in `ZMod N` (`ZMod.isUnit_iff_coprime`).
* "`N - 1 = F R` for some `R`" is `F ∣ N - 1`; the natural subtraction is
  guarded by `2 ≤ N`.  The exponent `(N - 1) / q` is an exact quotient because
  `q ∣ F ∣ N - 1`.
* "each prime `q ∣ F`" is `q ∈ F.primeFactors` (nonzero `F` is forced by
  `F ∣ N - 1`, `N - 1 ≠ 0`).
* Proth: the source's `k` is a positive integer; the hypothesis `0 < k` is
  stated explicitly (with `k = 0` one gets `N = 1`, where `ZMod 1` is trivial
  and the congruence `a^0 ≡ -1` holds vacuously, so the claim would be false).

## Mathlib absence

`leandoc` exact `Nat.pocklington`, `pocklington`, `proth_primality`: miss;
search "pocklington primality criterion partial factorization", "proth prime":
only `lucas_primality` (full factorization of `N - 1`) and `Nat.pepin_primality`
(Fermat numbers).  `grep -ri "pocklington\|proth"` over Mathlib: no files.

## Proof idea

If `N` is composite, its least prime factor `r` satisfies `r ^ 2 ≤ N < F ^ 2`.
For a prime `q ∣ F` with `q ^ e ∥ F`, write `N - 1 = q ^ e * m`; the image
`c = a ^ m` in `ZMod r` satisfies `c ^ (q ^ e) = 1` and
`c ^ (q ^ (e - 1)) = a ^ ((N - 1) / q) ≠ 1`, so `orderOf c = q ^ e` divides
`r - 1`.  Hence `F ∣ r - 1`, so `F < r`, contradicting `r < F`.
-/
import Mathlib

set_option autoImplicit false

namespace NumberComplexity.Pocklington

/-- Local step of Pocklington's argument.  Let `r` be a prime divisor of `n`,
and let `q ^ (k + 1)` divide `n - 1`.  If some residue `a` modulo `n` satisfies
`a ^ (n - 1) = 1` and `a ^ ((n - 1) / q) - 1` is a unit modulo `n`, then
`q ^ (k + 1) ∣ r - 1`. -/
theorem prime_pow_dvd_sub_one_of_unit {n r q k : ℕ} (hr : r.Prime) (hrn : r ∣ n)
    (hq : q.Prime) (hqn : q ^ (k + 1) ∣ n - 1) (a : ZMod n)
    (ha : a ^ (n - 1) = 1) (hu : IsUnit (a ^ ((n - 1) / q) - 1)) :
    q ^ (k + 1) ∣ r - 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨m, hm⟩ := hqn
  let φ : ZMod n →+* ZMod r := ZMod.castHom hrn (ZMod r)
  let c : ZMod r := φ a ^ m
  have hfin : c ^ q ^ (k + 1) = 1 := by
    have h1 : φ (a ^ (n - 1)) = 1 := by rw [ha, map_one]
    rw [map_pow, hm] at h1
    simpa only [c, ← pow_mul, mul_comm] using h1
  have hdiv : (n - 1) / q = m * q ^ k := by
    rw [hm, show q ^ (k + 1) * m = q * (m * q ^ k) by ring]
    exact Nat.mul_div_cancel_left _ hq.pos
  have hnot : ¬ c ^ q ^ k = 1 := by
    intro h1
    have hu' : IsUnit (φ (a ^ ((n - 1) / q) - 1)) := hu.map φ
    rw [map_sub, map_one, map_pow, hdiv, pow_mul, h1, sub_self] at hu'
    exact not_isUnit_zero hu'
  have hord : orderOf c = q ^ (k + 1) := orderOf_eq_prime_pow hnot hfin
  have hc0 : c ≠ 0 := by
    rintro hc
    rw [hc, zero_pow (pow_ne_zero _ hq.ne_zero)] at hfin
    exact zero_ne_one hfin
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hc0

/-- Every prime power exactly dividing `F` divides `r - 1`; hence, under the
Pocklington hypotheses, `F ∣ r - 1` for every prime divisor `r` of `N`. -/
theorem dvd_sub_one_of_prime_dvd {N F r : ℕ} (hF0 : F ≠ 0) (hF : F ∣ N - 1)
    (hr : r.Prime) (hrN : r ∣ N)
    (h : ∀ q ∈ F.primeFactors, ∃ a : ZMod N,
      a ^ (N - 1) = 1 ∧ IsUnit (a ^ ((N - 1) / q) - 1)) :
    F ∣ r - 1 := by
  have hr1 : r - 1 ≠ 0 := by
    have := hr.two_le
    omega
  rw [← Nat.factorization_le_iff_dvd hF0 hr1, Finsupp.le_def]
  intro p
  by_cases hp : p ∈ F.primeFactors
  · obtain ⟨a, ha, hu⟩ := h p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpos : 0 < F.factorization p :=
      hpp.factorization_pos_of_dvd hF0 (Nat.dvd_of_mem_primeFactors hp)
    obtain ⟨k, hk⟩ : ∃ k, F.factorization p = k + 1 :=
      ⟨F.factorization p - 1, by omega⟩
    have hpk : p ^ (k + 1) ∣ N - 1 := by
      rw [← hk]
      exact (Nat.ordProj_dvd F p).trans hF
    have hdvd : p ^ (k + 1) ∣ r - 1 :=
      prime_pow_dvd_sub_one_of_unit hr hrN hpp hpk a ha hu
    rw [hk]
    exact (hpp.pow_dvd_iff_le_factorization hr1).1 hdvd
  · have hzero : F.factorization p = 0 := by
      rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
    rw [hzero]
    exact Nat.zero_le _

/-- **Pocklington's criterion** (Pocklington 1914; Crandall–Pomerance §4.1).
Let `N ≥ 2` and let `F ∣ N - 1` with `N < F ^ 2`.  If for every prime `q ∣ F`
there is a residue `a` modulo `N` with `a ^ (N - 1) ≡ 1 (mod N)` and
`gcd(a ^ ((N - 1) / q) - 1, N) = 1`, then `N` is prime. -/
theorem pocklington {N F : ℕ} (hN : 2 ≤ N) (hF : F ∣ N - 1) (hFN : N < F ^ 2)
    (h : ∀ q ∈ F.primeFactors, ∃ a : ZMod N,
      a ^ (N - 1) = 1 ∧ IsUnit (a ^ ((N - 1) / q) - 1)) :
    N.Prime := by
  by_contra hNp
  have hr : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hsq : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hNp
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hF
    omega
  have hFr : F ∣ N.minFac - 1 :=
    dvd_sub_one_of_prime_dvd hF0 hF hr (Nat.minFac_dvd N) h
  have hlt : F < N.minFac := by
    have hle := Nat.le_of_dvd (by have := hr.two_le; omega) hFr
    omega
  have hsq' : F ^ 2 < N.minFac ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  omega

/-- **Proth's theorem** (Proth 1878), as a corollary of Pocklington's
criterion.  If `N = k * 2 ^ m + 1` with `0 < k < 2 ^ m` and some residue `a`
satisfies `a ^ ((N - 1) / 2) ≡ -1 (mod N)`, then `N` is prime. -/
theorem proth {N k m : ℕ} (hk : 0 < k) (hkm : k < 2 ^ m) (hN : N = k * 2 ^ m + 1)
    (a : ZMod N) (ha : a ^ ((N - 1) / 2) = -1) : N.Prime := by
  have hm : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hkm
    omega
  have hN1 : N - 1 = k * 2 ^ m := by omega
  have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 hm
  have heven : N - 1 = 2 * ((N - 1) / 2) := by
    rw [Nat.mul_div_cancel' (hN1 ▸ h2m.mul_left k)]
  have hodd : Nat.Coprime 2 N := by
    rw [Nat.coprime_two_left]
    rw [hN]
    exact ((h2m.mul_left k).even even_two).add_one
  have h1 : 1 < 2 ^ m := Nat.one_lt_two_pow hm
  have hN2 : 2 ≤ N := by
    rw [hN]
    nlinarith
  apply pocklington (F := 2 ^ m) hN2 (hN1 ▸ dvd_mul_left _ _)
  · have h2 : k * 2 ^ m + 2 ^ m ≤ 2 ^ m * 2 ^ m := by nlinarith
    rw [hN, sq]
    omega
  · intro q hq
    rw [Nat.primeFactors_prime_pow hm Nat.prime_two, Finset.mem_singleton] at hq
    subst hq
    refine ⟨a, ?_, ?_⟩
    · rw [heven, pow_mul', ha]
      norm_num
    · rw [ha, show (-1 : ZMod N) - 1 = -((2 : ℕ) : ZMod N) by push_cast; ring]
      exact ((ZMod.isUnit_iff_coprime 2 N).2 hodd).neg

/-- Satisfiability witness for `pocklington`: `N = 13`, `F = 4` (`4 ∣ 12`,
`13 < 16`), and the single prime `q = 2 ∣ 4` with witness `a = 2`. -/
example : (13 : ℕ).Prime := by
  refine pocklington (F := 4) (by norm_num) (by norm_num) (by norm_num) ?_
  intro q hq
  have hq2 : q = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num)
      Nat.prime_two, Finset.mem_singleton] at hq
    exact hq
  subst hq2
  refine ⟨2, by decide, ?_⟩
  rw [show ((2 : ZMod 13) ^ ((13 - 1) / 2) - 1) = ((11 : ℕ) : ZMod 13) by decide,
    ZMod.isUnit_iff_coprime]
  norm_num

/-- Satisfiability witness for `proth`: `13 = 3 * 2 ^ 2 + 1`, `3 < 4`, and
`2 ^ 6 ≡ -1 (mod 13)`. -/
example : (13 : ℕ).Prime :=
  proth (k := 3) (m := 2) (by norm_num) (by norm_num) (by norm_num) 2 (by decide)

end NumberComplexity.Pocklington
