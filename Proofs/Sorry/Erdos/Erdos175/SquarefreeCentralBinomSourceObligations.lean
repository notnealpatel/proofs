/-!
# A046098: squarefree central-binomial residual

DOCUMENTATION ONLY: no imports, executable declarations or admissions.
The preserved passage below is the complete A046098 residual in Formalize/INDEX.
Source and current evidence were read from
Proofs/Erdos/Erdos175/SquarefreeCentralBinom.lean: OEIS A046098 concerns natural
indices n and Squarefree (Nat.choose n (n / 2)), including n = 0. Noe's comment
(2007-04-06) is the finite assertion "No other n < 10^8", not an unbounded
classification. The production theorem squarefree_choose_half_iff proves
exactly that bounded classification, including the thirteen listed positives
and all ten formerly missing small odd cases, with kernel-checked certificates.

The literature recorded there (Granville-Ramare / Velammal for the even half,
Sander for sufficiently large perturbed binomials) is not fully formalized by
the bounded certificate. Unbounded local closure still needs the odd tail
n >= 10^8 and the even power-of-two tail beyond k = 30, indexed by
n = 2^(k+1) in A046098. Halving a central binomial coefficient can destroy a
square factor, so the odd tail does not follow just by dividing an even-case
certificate by two. This document adds no tail theorem or admission and does
not reassign the completed finite checks.

## Formalize/INDEX — complete A046098 residual (verbatim)

```text
- **A046098:** `Proofs/Erdos/Erdos175/SquarefreeCentralBinom.lean` now proves the exact classification for every `n < 10^8` (`squarefree_choose_half_iff`), including all ten previously missing small odd cases. The current `NotSquarefree.lean:witness_cert` uses a kernel-checked certificate, not the old native computation. The unbounded classification still requires the remaining odd cases `n ≥ 10^8` and the even power-of-two tail: extend `Erdos175.not_squarefree_centralBinom_two_pow` beyond `k = 30` (A046098 index `n = 2^(k+1)`). Do not reassign the completed small certificates.
```
-/
