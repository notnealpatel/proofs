seq:     A267632
claim:   palindrome-rows
status:  odd case PROVED; n = 2^j stated, intended sorry
         (2026-07-29; commit 5976abf)
stmt:    S
proof:   S (n odd) / unknown (n = 2^j)
module:  Proofs/Enumerative/PalindromeRows.lean (Enumerative.PalindromeRows)
source:  OEIS A267632 comment, unattributed
         ("observation-conjecture")

FORMALIZED (2026-07-29)
  T_symm_of_odd : Odd n → k ≤ n → T n k = T n (n - k) — proved via the
  card's complement route, at the STRONGER range k ≤ n (endpoints
  kernel-verified; the OEIS truncated-row claim is a restriction).
  T_symm_of_two_pow (1 ≤ k < 2^j) — stated, intended sorry (open).
  Rows 1–8 kernel-checked vs the live entry; sharpness controls at
  rows 6, 10, 12. Literature sweep 2026-07-29: LIKELY-KNOWN
  (one-line corollary of Ramanathan 1944 / Barnes 1959, never stated
  explicitly; OEIS label stale); see PLAN.md §6.

CLAIM
  T(n,k) = number of k-element subsets of {1,...,n}
  whose sum is divisible by n (k >= 1). Conjecture:
  the row (T(n,1),...,T(n,n-1)) — the row with its
  last element removed — is a palindrome whenever n is
  odd or n is a power of 2. Equivalently
  T(n,k) = T(n,n-k) for 1 <= k <= n-1 under those
  hypotheses.

LEAN
  Statement direct from Mathlib:
    (Finset.powersetCard k (range n)).filter
      (fun S => n ∣ S.sum id) |>.card
  and the symmetry equation. No new defs.

ROUTE (n odd — provable now, high confidence)
  Complementation S ↦ {1..n} \ S is a bijection
  powersetCard k → powersetCard (n-k), and
  sum(S^c) = n(n+1)/2 - sum(S). For n odd,
  n ∣ n(n+1)/2, so n ∣ sum(S) iff n ∣ sum(S^c).
  Finset.card_bij closes it.
ROUTE (n = 2^j — open)
  Complement argument fails (n ∤ n(n+1)/2 for n even).
  Hadjicostas/Barnes formula
    T(n,k) = (1/n) * sum over s ∣ gcd(n,k) of
      (-1)^(k - k/s) phi(s) C(n/s, k/s)
  restricts to odd s... for n = 2^j the divisors s are
  powers of 2; a sign/digit analysis is plausible but
  unworked. Gauss-sum vocabulary exists in Mathlib
  (gaussSum, IsPrimitiveRoot).

EVIDENCE
  Observation across computed rows in-entry.
