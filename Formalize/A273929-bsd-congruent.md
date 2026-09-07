# A273929 — congruent numbers in classes 5, 6, 7 mod 8

- **Mathematical status:** open unconditionally; known conditionally on BSD through the Tunnell/Monsky lineage.
- **Work status:** hard-blocked; the rank-free congruent-number/point bridge is formalized, while the unconditional inclusion remains open.
- **Remaining target:** prove unconditionally that every `n` with `MemA273929 n` gives `A273929.HasNontrivialPoint (n : ℚ)`, equivalently that every squarefree `n≡5,6,7 mod 8` is primitive congruent.
- **Available ground:** `Proofs/Enumerative/CongruentBSD.lean` proves `A273929.isCongruentArea_iff_hasNontrivialPoint` and the point-form equivalence `A273929.a273929_subset_iff_hasNontrivialPoint`, so no general bridge remains to define or prove. It also proves the concrete instance `A273929.isPrimitiveCongruent_twentyOne : IsPrimitiveCongruent 21` (and other small cases).
- **Next obligation:** supply unconditional nontrivial-point existence uniformly for all `MemA273929 n`. The archived inclusion `A273929.a273929_subset_a006991` still has intentional `sorry`; the bridge and the isolated proof at `21` do not discharge it.
