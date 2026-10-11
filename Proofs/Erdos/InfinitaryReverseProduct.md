# Infinitary reverse-product unit D

## Scope and translation

Implemented at accepted base `8aba7fd28e5d2d30ebb2ecb3492f6a92b1bd27af` in
`Proofs/Erdos/InfinitaryReverseProduct.lean`, namespace `InfinitarySuperperfect`.
The sole import is `Erdos.InfinitaryReverseBudget`. No definitions, axioms,
computational trust extensions, or additional public helper declarations were added.

The two public exports are:

- `InfinitarySuperperfect.reverseProduct_eq_mixed`
- `InfinitarySuperperfect.exists_reverseTag_mixed`

Both retain the packet's quantifiers `n m j k : ℕ` and the exact premises
`hn hm hm2 hreverse hmod hj hk hshape`. The first proof does not need `hj`
(named `_hj` in its binder), but preserves it in the public interface.
There is no evenness, square, forward equation, pairwise-coprimality, or
selected-slot primality assumption. The second conclusion selects an actual
sigma tag in `reverseTags m`; it does not select from a deduplicated set of
normalized values. Its ordinary three-valuation may be zero.

The accepted count and sigma identities first cancel the positive two-power,
then five. The `hk` guard gives `2 ≤ 2^k`, so natural subtraction is not truncated.
Valuation additivity over the positive actual tagged factors gives a sum equal
to `2^k-1`. Its oddness excludes an all-even sum. The selected factor divides
the product; its prime support is contained in `{3,5}`. The private
`reconstruct_mixed` helper uses ordinary prime factorization, including missing
primes with zero exponent. No coprimality of individual slots is used.

## Joint satisfiability and domain checks

Private supporting lemmas `witness_data`, `witness_tags`, and
`witness_premises` independently establish the joint model
`n=225`, `m=356`, `j=k=1` without using either new export:

- `356 = 2^2 * 89`, with prime support `{2,89}` and valuations two and one;
- `reverseTags 356 = {⟨89,0⟩}`, a nonempty actual tagged domain;
- `sigma 356 = 450 = 2*225`, and the odd support is one modulo four;
- `225.factorization 2 = 0` and the stipulated mixed shape holds;
- both exponent guards hold.

Examples independently check `reverseProduct 356 = 45` and that the actual
slot at base 89 and height zero has positive odd five-valuation and the ordinary
mixed factorization. Two further examples call **both** public exports with
these joint premises. An example proves `Odd 225`.

This is **not a whole-even-square/full-cycle witness**: `n` is odd, and no
forward equality `m = sigma n` is assumed or claimed. Positivity and the odd
valuation sum prevent the selected-tag conclusion from being vacuous. The
public `n,m` domains have this concrete joint model; the selected domain is
nonempty in that model and is proved to contain a tag under the general premises.

## Checks and evidence

Producer checks used the actual Lean compiler: four bounded production build
invocations, one bounded API-probe invocation, and one bounded imported audit.
The first build failed; the next three succeeded (the third included the
joint witness, and the fourth was the final cached check). Initial feedback caught a
rewrite that entered `n.factorization 2`, an incorrect guessed prime API,
and the explicit function argument required by `Finset.even_sum`. Local
repairs were compiled. Exact signatures were inspected with `leandoc` and
a disposable `#check` probe; no probe commands remain in production.

Successful bounded production check (including all witness examples):

```sh
timeout 60s lake -q build +Erdos.InfinitaryReverseProduct
```

The witness build exited zero with no warnings or errors. A final cached
build receipt and an imported signature/axiom audit are recorded below.
The imported audit was a disposable leaf at `Proofs/Scratch/DAudit.lean`:

```lean
import Erdos.InfinitaryReverseProduct
set_option autoImplicit false
#check @InfinitarySuperperfect.reverseProduct_eq_mixed
#check @InfinitarySuperperfect.exists_reverseTag_mixed
#print axioms InfinitarySuperperfect.reverseProduct_eq_mixed
#print axioms InfinitarySuperperfect.exists_reverseTag_mixed
```

Exact audit command (exit zero):

```sh
set -o pipefail; timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/DAudit.lean 2>&1 | tee /tmp/infinitary-D-audit.txt
```

The imported output covers **all public exports**; both depend only on
`propext`, `Classical.choice`, and `Quot.sound`. This is producer compilation,
non-vacuity evidence, and axiom inspection, not the parent's independent
final-artifact review. There are no `sorry`s, `native_decide`, new axioms,
`implemented_by`, `extern`, or `csimp` declarations.

## Consumer and remaining gates

The actual selected tag and its positive odd five-valuation are now available
to E under the packet premises. E's height and positive-three-valuation bridge,
C→D composition, a forward equality, the strict witness, and full f2 exclusion
remain unpaid and are outside this unit. No C import or dependency was added.
No integration, adoption, independent review dispatch, global ledger edit,
or `References` edit was performed.

The only finalized files are this companion and its Lean module. Scratch audit
and probe sources are removed before handoff. Evidence is embedded here so the
parent can copy it to
`/home/exedev/x/erdos/prize-portfolio/activation-01a1290e/infinitary-D/`;
that destination is outside this producer's permitted write target and was not
written. Build artifacts are the workspace-local
`.lake/build/lib/lean/Erdos/InfinitaryReverseProduct.olean` and `.ilean`.

### Actual imported audit output

```text
InfinitarySuperperfect.reverseProduct_eq_mixed : ∀ (n m j k : ℕ),
  0 < n →
    0 < m →
      m.factorization 2 = 2 →
        InfinitarySuperperfect.sigma m = 2 * n →
          (∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) →
            1 ≤ j →
              1 ≤ k →
                n = 2 ^ n.factorization 2 * 3 ^ 2 ^ j * 5 ^ 2 ^ k →
                  InfinitarySuperperfect.reverseProduct m = 3 ^ 2 ^ j * 5 ^ (2 ^ k - 1)
InfinitarySuperperfect.exists_reverseTag_mixed : ∀ (n m j k : ℕ),
  0 < n →
    0 < m →
      m.factorization 2 = 2 →
        InfinitarySuperperfect.sigma m = 2 * n →
          (∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) →
            1 ≤ j →
              1 ≤ k →
                n = 2 ^ n.factorization 2 * 3 ^ 2 ^ j * 5 ^ 2 ^ k →
                  ∃ i ∈ InfinitarySuperperfect.reverseTags m,
                    0 < (InfinitarySuperperfect.normalizedSlot i.fst i.snd).factorization 5 ∧
                      Odd ((InfinitarySuperperfect.normalizedSlot i.fst i.snd).factorization 5) ∧
                        InfinitarySuperperfect.normalizedSlot i.fst i.snd =
                          3 ^ (InfinitarySuperperfect.normalizedSlot i.fst i.snd).factorization 3 *
                            5 ^ (InfinitarySuperperfect.normalizedSlot i.fst i.snd).factorization 5
'InfinitarySuperperfect.reverseProduct_eq_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfinitarySuperperfect.exists_reverseTag_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Final build receipt

```sh
set -o pipefail; (timeout 60s lake -q build +Erdos.InfinitaryReverseProduct && printf 'build exit: 0\n') 2>&1 | tee /tmp/infinitary-D-build.txt
```

Actual output (exit zero):

```text
build exit: 0
```
