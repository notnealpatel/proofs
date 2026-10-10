# Conditional a=12, five-square-slot exclusion

`a12_e3_false` excludes the exact full natural-number identity for positive odd
`e ≥ 3`. `a12_odd_exponent_eq_one` has the same hypotheses with `3 ≤ e` removed
and concludes `e = 1`. These are internal verified conditional progress, not a
solution of Erdős 1052; novelty and significance have not been established.

The base/exponent pairs are actual distinct prime components. The allowed odd
square bases exclude 3, 5, 7, and 13, without any additional residue restriction.
No bound on `p^e`, identity-existence hypothesis, or seed hypothesis is added.
The paid seed forces (11,1), and the paid Force61 consumer supplies an actual
positive 61 slot. Its additional nondivisibility-by-81 conclusion is unused.
All 20 placements of these two slots transport the full integer identity and
positive residual exponents; all three residual positions are then considered.

For absence of (17,1), the residual caps are 362/361, 530/529, 842/841;
for absence of (19,1), they are 290/289, 530/529, 842/841. Distinct bases
permit each exceptional cap at most once. Higher powers of the excluded square
base are still allowed. The exact multiplier is
`(4097/4096)*(1+1/73^3)*(122/121)*(3722/3721)`.
Each capped product is strictly below 65/64, as certified by Lean `norm_num`.
The universally quantified finite prime-gap check (q below 29) transfers through
monotonicity of positive powers and reciprocals to arbitrary positive exponents;
it is not an asymptotic or finite-search inference. No Sage computation is used.
After the two actual squares are forced, the full integer identity sends primes
29 (dividing 17²+1) and 181 (dividing 19²+1) to the single remaining slot. Neither
can be p because p mod 24 is 1. Their required equality gives the contradiction.

Structural premises are jointly inhabited, explicitly at p=73, e=3 and square
pairs (11,1),(61,1),(17,1),(19,1),(23,1). All quantified numeric domains are
nonempty and all denominator powers are positive. Satisfiability of the full
identity is deliberately **not** asserted: its inconsistency for e≥3 is the
proved content, rather than contradictory structural assumptions. The e=1
consumer makes no existence claim. No new definitions or assumed axioms occur.

Canonical `erdos fetch 1052` was run using the installed binary. Its problem
statement is context/metadata only, not proof evidence. No OEIS lookup was
consequential. The unpaid upstream bridges remain global fixed-core reduction,
a=12 branch selection, Wall/a>10, and any consequence for original problem 1052.
No successor work or literature comparison was undertaken.

## Final verification receipt

The final Lean bytes passed `timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052A12E3Exclusion` (exit 0; no diagnostics). Separate disposable leaf audits, each with a 10-second command bound, checked the four paid API signatures, both full main signatures, and all 13 new theorem axiom closures. Every closure was exactly `[propext, Classical.choice, Quot.sound]`. No production audit commands or temporary scaffolding remain. Both full main signatures retain all 13 universally quantified naturals and the requested identity; the only contract difference is removal of `3 ≤ e` for the e=1 consumer.

Source SHA-256: `d06a5c3edb0f592eccd01b94d08bd77091c8b4c77f95d122607da19af2299b58`.
