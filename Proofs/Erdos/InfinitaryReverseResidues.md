# Infinitary selected-tag residues (bounded unit E)

## Scope and contracts

Production consists only of `InfinitaryReverseResidues.lean` and this companion.
The sole import is `Erdos.InfinitaryReverseProduct`, at the assigned accepted
D baseline `bff14bbecebc708894ea6c8a0567c7500c7e86d8`. There are exactly two
public named declarations, both in `InfinitarySuperperfect`; all named helpers
and witness certificates are private. No new definitions are introduced.

* `reverseTag_residues`: for natural `m,q,h`, actual membership
  `⟨q,h⟩ ∈ reverseTags m`, `q % 4 = 1`, positive odd actual ordinary
  five-valuation of `normalizedSlot q h`, and its reconstruction as the product
  of three and five raised to its actual ordinary valuations imply
  `h = 0`, positive actual three-valuation, `q % 3 = 2`, `q % 5 = 4`, and
  `q % 16 = 9 ∨ q % 16 = 13`. There is **no** positivity premise on `m`,
  reverse equation, whole-square/even premise, positive-three premise, or
  normalized-slot primality premise. Exponents in the public contract are
  valuations of the actual slot, not independently supplied variables.
* `exists_reverse_prime_residues`: precisely D's `n,m,j,k` hypotheses
  (`0<n`, `0<m`, `v₂(m)=2`, `sigma m=2*n`, every actual odd prime factor
  of `m` one modulo four, `1≤j`, `1≤k`, and the prescribed mixed shape of
  `n`) imply an actual prime `q ≠ 2` dividing `m`, with residues one modulo
  four, two modulo three, four modulo five, and nine or thirteen modulo sixteen.
  The proof applies D's `exists_reverseTag_mixed`, keeps its selected tag,
  applies the local export, and transports prime/divisibility through membership.

The intended objects, quantifiers, premises, and conclusions survive unchanged.
No deduplication, pairwise-coprimality, or primality of normalized slots occurs.
There is no pending-C dependency, canonical-exclusion composition, forward
composition, or full-cycle theorem.

## Elementary proof checkpoints and boundary audit

`Nat.mem_primeFactors` supplies `q.Prime`, `q ∣ m`, and `m ≠ 0` from actual
membership; it does not require an external positivity premise. `q=3` is
excluded by its modulo-four residue. Primality then excludes zero residue
modulo three. The adopted `normalizedSlot_spec` supplies the exact successor
identity `1+q^(2^h)=2*3^v*5^u`, with actual valuations `u,v`.

Positive `u` makes the right-hand side zero modulo five. For heights at least
two, exhaustive residues modulo five give `q^4 % 5 = 0` or `1`; raising to
`2^t` preserves this dichotomy and contradicts the successor identity. This
proof includes the zero residue rather than assuming a nonzero residue, so
it also covers the `q=5` boundary without an additional hypothesis or a
Fermat theorem. At height one, the square is one modulo three. A positive
three-valuation is impossible, but zero three-valuation contradicts the odd
five-power residue two modulo three. Thus the height is zero. Zero
three-valuation at height zero would force `q % 3 = 0`, again impossible.
The identity now gives the residues modulo three and five (in particular,
`q=5` is excluded also by the resulting residue four modulo five).

Odd five-powers are five modulo eight; three-powers are one or three modulo
eight. Hence the slot is five or seven modulo eight. Doubling the slot in the
exact successor identity gives nine or thirteen modulo sixteen for `q`.
There is no natural subtraction in this new arithmetic proof and no new
unguarded division, bounded extremum, or totalized analytic operator.

## Joint nonvacuity and concrete tests

The production module independently reconstructs, rather than invoking D's
private witness lemmas:

* `n=225`, `m=356`, `j=k=1`, `m.primeFactors={2,89}`;
* actual valuations `v₂(356)=2`, `v₈₉(356)=1`, `v₂(225)=0`;
* `reverseTags 356={⟨89,0⟩}` and the reverse equation `sigma 356=450`;
* all D premises jointly, with nonempty actual support;
* `normalizedSlot 89 0=45`, actual `v₃=2`, actual `v₅=1`;
* both exports called on these jointly established premises;
* an independent concrete certificate that 89 is prime, not two, divides 356,
  and has residues `1,2,4,9` modulo `4,3,5,16` respectively.

`225` is odd and not even: this is not a whole-even-square example.
The independent forward computation proves `sigma 225=260 ≠ 356`, so this
is explicitly **not** a full cycle. No claim that the joint example satisfies
unpaid full-cycle premises is made. The optional 29/15 example was omitted.
All domains are natural numbers, nonempty; the actual tag-selection hypotheses
are simultaneously inhabited by this concrete example. No degenerate
instance assumptions are introduced.

## Producer checks and actual outputs

Every compiler/build invocation ran through `tool_task` with a 70-second task
bound and a 60-second command bound. No observed invocation timed out. Successful narrow
build command (task `build-e5`, exit 0, empty output):

```sh
timeout 60s lake -q build +Erdos.InfinitaryReverseResidues
```

This checked both exports and their concrete joint calls. The later final build
checked the additional independent forward-noncycle example using the same
command (task `final-build-e`): exit 0, empty output, as observed. The production
Lean bytes have not changed since that final successful build. The private forward
computation was first checked separately using:

```sh
timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/EProbe.lean
```

Task `forward-probe2`: exit 0, empty output.

Imported all-public signature and axiom audit command:

```sh
timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/EAudit.lean
```

The disposable leaf imports E and contains exactly `#check @` and `#print axioms`
for both public declarations. Task `audit-e` exited 0 and printed:

```text
InfinitarySuperperfect.reverseTag_residues : ∀ (m q h : ℕ),
  ⟨q, h⟩ ∈ InfinitarySuperperfect.reverseTags m →
    q % 4 = 1 →
      0 < (InfinitarySuperperfect.normalizedSlot q h).factorization 5 →
        Odd ((InfinitarySuperperfect.normalizedSlot q h).factorization 5) →
          InfinitarySuperperfect.normalizedSlot q h =
              3 ^ (InfinitarySuperperfect.normalizedSlot q h).factorization 3 *
                5 ^ (InfinitarySuperperfect.normalizedSlot q h).factorization 5 →
            h = 0 ∧
              0 < (InfinitarySuperperfect.normalizedSlot q h).factorization 3 ∧
                q % 3 = 2 ∧ q % 5 = 4 ∧ (q % 16 = 9 ∨ q % 16 = 13)
InfinitarySuperperfect.exists_reverse_prime_residues : ∀ (n m j k : ℕ),
  0 < n →
    0 < m →
      m.factorization 2 = 2 →
        InfinitarySuperperfect.sigma m = 2 * n →
          (∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) →
            1 ≤ j →
              1 ≤ k →
                n = 2 ^ n.factorization 2 * 3 ^ 2 ^ j * 5 ^ 2 ^ k →
                  ∃ q, Nat.Prime q ∧ q ≠ 2 ∧ q ∣ m ∧ q % 4 = 1 ∧ q % 3 = 2 ∧ q % 5 = 4 ∧ (q % 16 = 9 ∨ q % 16 = 13)
'InfinitarySuperperfect.reverseTag_residues' depends on axioms: [propext, Classical.choice, Quot.sound]
'InfinitarySuperperfect.exists_reverse_prime_residues' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first imported audit above is the counted producer PASS. A repeat using
the same command was launched as `final-audit-e`, but its completion receipt
is unavailable after resumption; it is **not counted as PASS**. No further
audit or build was run during final cleanup. The coordinator owns the fresh
imported final-artifact audit.

Actual producer effort comprised six narrow production build invocations
(four failed, two succeeded), two API-probe invocations (both failed, while
exposing useful exact signatures), two forward-probe invocations (one failed,
one succeeded), and two imported audit launches (one observed PASS, one
completion unavailable). Failures and repairs are recorded below; these are
invocation counts, not invented time estimates.

## Failures, repairs, and infrastructure observations

* Initial direct import probe failed with `unknown module prefix 'Erdos'`:
  the assigned workspace had no built Erdos dependency artifacts yet. The
  narrow E build populated its ordinary dependency cache. No cache layout,
  baseline, or dependency source was changed; D's review gates were not rerun.
* The API probe confirmed `Nat.mem_primeFactors` as
  `p ∈ n.primeFactors ↔ Nat.Prime p ∧ p ∣ n ∧ n ≠ 0` and
  `Nat.Prime.dvd_iff_eq` as `a ∣ p ↔ p = a` under `a ≠ 1`.
  It also failed on the guessed nonexistent `Nat.pow_mod_zero`; that name
  is not used. `leandoc` exact/generated queries and this compiler probe,
  rather than guesses, settled these APIs.
* `build-e` failed on equality orientation and recursive unrestricted modular
  simp. Local repairs corrected the orientation and made modular reductions
  explicit. `build-e2` exposed the direction of `pow_mul`, a branch-name
  mistake, and missing arithmetic normalization. `build-e3` then exposed the
  syntactic `2^2` versus `4` rewrite boundary; an explicit `change` repaired it.
* `build-e4` reached the joint local-export example but rewrote the slot value
  before its valuation identities, making those rewrites inapplicable. Reordering
  these rewrites fixed it. Unused simp arguments were removed. `build-e5`
  succeeded without warnings or output.
* The separate forward probe initially failed on an accidental trailing literal
  `EOF` token. Removing it yielded the successful `forward-probe2` above.
  One literal edit initially missed because the token lacked a final newline;
  the corrected exact edit removed it.
* An inspection command attempted a nonexistent dependency filename after
  successfully reading D; its exit was nonzero and did not affect proofs.
  `jj --ignore-working-copy status` reports the pre-snapshot working-copy
  state and did not yet list new files; filesystem inspection establishes
  the actual producer scope. No revision operation was performed.

This is compiler-checked conditional mathematics plus explicit nonvacuity,
not evidence for an actual whole cycle. No `sorry`, new axioms, `native_decide`,
trusted-code overrides, production audit commands, or new public helpers are
present. During final cleanup, `Proofs/Scratch/EProbe.lean` and
`Proofs/Scratch/EAudit.lean` were removed with `rm`; separate `test ! -e`
checks confirmed both absent. The command exited 0 and printed:

```text
Both scratch source files removed; absence confirmed.
```

The finalized write scope is only the production pair; the two temporary
scratch sources no longer exist. Dependency sources and unrelated tracked
files were not edited. The harness owns snapshotting and the parent owns
inspection of the resulting exact finalized diff.

## Remaining gates and consumers

Producer proof, nonvacuity and imported standard-three-axiom checks are paid.
Independent final whole-literal review of this exact pair and the coordinator's
fresh imported audit/adoption remain coordinator-owned. No integration,
adoption, rebase, References change, global ledger edit, or peer contact was
performed. E supplies the actual prime-residue input for a future consumer of
canonical exclusion; C/whole-square valuation transport and that composition
are deliberately not implemented here. No additional mathematical assumption
was introduced to make the E implication easier.
