# A051293 verification

## Result

The recovered pair was repaired and freshly elaborated. `Challenge.lean` is an independent statement surface: it imports only Mathlib modules, gives the literal powerset count, and gives the recursive Fubini definition. Its three theorem bodies deliberately remain `sorry`. `Solution.lean` does not import `Challenge.lean`; it repeats the independent definitions and proves the selected declarations by bridging to `A051293.a_oeis`, `A051293.fubini`, `A051293.cloitre_conjecture`, and the general-theorem-derived fixed-order result in `Enumerative.A051293.Cloitre`.

The obsolete/nonexistent import `Mathlib.Analysis.Asymptotics.Asymptotics` was replaced by the current `Mathlib.Analysis.Asymptotics.Defs` module. The coefficient proof no longer asks `decide` to reduce the well-founded recursive definition (which cannot reduce that way). Instead it proves the recurrence bridge `fubiniCoefficient_eq_fubini` by strong induction and uses the existing kernel-proved ground coefficients.

The zero cases are totalized in the statement. Both asymptotic bridges use `Filter.eventually_gt_atTop 0`, so the `if 0 < n` branch agrees eventually with the existing theorem. The fixed-order source theorem `A051293.cloitre_explicit_tendsto` is itself obtained from `A051293.cloitre_conjecture 5`; no analytic proof is duplicated here.

## Compilation evidence

Immediately before elaboration, `tool_atop` reported 22.62 GiB available out of 23.46 GiB. Commands were single-Lean, explicitly memory-bounded, and externally time-bounded.

Challenge:

```text
timeout 180s lake env lean -M 5500 -j1 Palomar/A051293/Challenge.lean
exit 0
Palomar/A051293/Challenge.lean:48:8: warning: declaration uses `sorry`
Palomar/A051293/Challenge.lean:54:8: warning: declaration uses `sorry`
Palomar/A051293/Challenge.lean:69:8: warning: declaration uses `sorry`
```

Solution:

```text
timeout 240s lake env bash -c \
  'export LEAN_PATH=/home/exedev/p/proofs/.lake/build/lib/lean:$LEAN_PATH; \
   exec lean -M 7000 -j1 Palomar/A051293/Solution.lean'
exit 0
```

The workspace had no local `Enumerative.A051293.Cloitre.olean`. The second command therefore used the existing read-only project build directory. Before using it, byte comparisons established that this workspace and `/home/exedev/p/proofs` have identical `Counting.lean`, `Cloitre.lean`, `lake-manifest.json`, and `lean-toolchain` files. No cache was copied or reconstructed, no Lake build fan-out was started, and no project configuration was changed.

A 6 GiB process virtual-address `ulimit` was initially tried but made Lean report that it could not read an existing Mathlib `.olean`; using Lean's own `-M` allocation limit without that address-space restriction resolved the artifact. At `-M 5500`, Solution reached Lean's explicit allocation limit. Raising only the Solution command to `-M 7000` completed successfully while host headroom remained above 22 GiB.

## Declaration alignment

The count definitions in Challenge and Solution are byte-identical, as are the recursive coefficient definitions. Normalizing whitespace in each selected theorem statement (through `:= by`) produced identical Challenge/Solution signatures with these SHA-256 checksums:

```text
fubiniCoefficient_first_six  e81d1be76eee28c5a0a0de4e1303d77503058f041ed6ec661ad6b79863d5d9c0
arbitrary_order_asymptotic   09f3163d055cbaf9cb9d565b102bf58226786b1e19b07082bb16453a978e06b4
fixed_order_five             2a10423f69a7c45269e5b617ec9aef01b77aab3bcf7b9b2af5777844411b11ca
```

Both files elaborated those declarations under `set_option autoImplicit false`. The emitted `#check` output for the two asymptotic declarations agreed with their literal source signatures.

## Axiom and placeholder audit

`Solution.lean` contains no `sorry`, `native_decide`, or `Lean.ofReduceBool`. Lean emitted:

```text
'PalomarA051293.fubiniCoefficient_first_six' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'PalomarA051293.arbitrary_order_asymptotic' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'PalomarA051293.fixed_order_five' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Thus every selected Solution theorem stays within the permitted axiom set. The three `sorry` warnings belong only to the intentional Challenge holes.

No Comparator executable/configuration is present in this isolated workspace, and the edit scope prohibited adding comparator JSON or root Lake wiring. Separate elaboration, literal definition comparison, normalized selected-signature comparison, and transitive `#print axioms` output provide the verification recorded here.
