# A230528 — addition-chain doubling gap

- **Mathematical status:** open question of Alexey Slizkov (OEIS A230528).
- **Work status:** hard-blocked; counterexample-searchable but not currently dispatched.
- **Remaining target:** prove or refute `∀ k, NumberComplexity.l k - NumberComplexity.l (2*k) ≤ 1`.
- **Proved prerequisites:** `Proofs/NumberComplexity/TwoBitAdditionChain.lean` proves the exact shortest length for every positive number of binary weight at most two; `Proofs/NumberComplexity/SlizkovDoubling.lean` consequently proves `NumberComplexity.l (2*k) = NumberComplexity.l k + 1` on that infinite family (`l_two_mul_eq_add_one_of_binaryWeight_le_two`). The same file states the exact general question and proves the elementary append-a-doubling inequality. Its checked range through `k=50000` is evidence only.
- **Next obligation:** either give a structural bound on the possible saving or provide an explicit `k` together with certified optimal chain lengths witnessing a larger deficit.
