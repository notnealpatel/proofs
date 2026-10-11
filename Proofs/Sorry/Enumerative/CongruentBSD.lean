import Enumerative.CongruentBSD

/-!
# Archived open admission

The attributed declaration below is relocated verbatim from `Enumerative.CongruentBSD`.
Its intended `sorry` is not a proof; production retains the independent results,
concrete witnesses, and explicitly hypothesis-parameterized conditional statements.
References to results above or below in the original attribution refer to production.
-/

set_option autoImplicit false

namespace A273929

/-- **A273929 is a subset of the primitive congruent numbers A006991 (OEIS, conditional on
the Birch and Swinnerton-Dyer conjecture).**

Verbatim from the entry's `comments` field, pulled 2026-08-05:

> It has been shown, conditional on the Birch Swinnerton-Dyer conjecture, that this
> sequence is a subset of the primitive congruent numbers (A006991). The union of this
> sequence with A062695 gives A006991. Also this sequence is the intersection of A047574
> and A005117.

Only the first sentence is archived here; the second is
`isPrimitiveCongruent_iff_of_congruent` and the third is true by construction (see the
docstring of `MemA273929`).

**Status: open.**  This is the single intended `sorry` of the file.  The claim is a
theorem *conditional* on BSD for the curves `y² = x³ − n²x`, by Tunnell's criterion (whose
converse direction is exactly what BSD supplies — see the verbatim wiki quotation in the
module docstring) together with the observation that the Tunnell counting condition is
automatic in the residue classes `5, 6, 7 (mod 8)`; the entry's own Mathematica program,
pinned verbatim in the module docstring, encodes precisely that short circuit
(`MemberQ[{5, 6, 7}, Mod[n, 8]], ok = True`).

**Equivalent point form.**  By `a273929_subset_iff_hasNontrivialPoint`, this statement is
equivalent to: for every squarefree `n ≡ 5, 6, 7 (mod 8)` the curve `Eₙ` carries a
rational point with `y ≠ 0`.  That is the shape a proof would have to take, and it is why
this file needs no rank functional.

**Why it is hard.**  What has to be produced is an actual rational point, and the residue
condition on its own only supplies the *Tunnell counting condition* — the conditional half
of the pinned wiki sentence is exactly the step "these equalities are sufficient to
conclude that `n` is a congruent number", and that step is the one that needs BSD.  The
unconditional results are all partial.  The wiki records, verbatim:

> if $p ≡ 5 (mod 8)$, then $p$ is a congruent number.

> if $p ≡ 7 (mod 8)$, then $p$ and 2$p$ are congruent numbers.

> It is also known that in each of the congruence classes $5, 6, 7 (mod 8)$, for any given
> $k$ there are infinitely many square-free congruent numbers with $k$ prime factors.

Neither covers all squarefree `n ≡ 5, 6, 7 (mod 8)`, and Mathlib has neither Heegner
points, nor `L`-functions of elliptic curves over `ℚ` in a usable form, nor a Mordell–Weil
theorem.

**The residue classes are not interchangeable.**  The archived claim is specific to
`5, 6, 7 (mod 8)`; the wiki records the opposite behaviour in one of the complementary
classes, verbatim:

> if $p ≡ 3 ([[modular arithmetic|mod]] 8)$, then $p$ is not a congruent number, but 2$p$
> is a congruent number.

So the primitive congruent numbers `≡ 1, 2, 3 (mod 8)` are a *proper* subset of the
squarefree numbers in those classes — which is why `IsPrimitiveCongruentLow` carries
`IsPrimitiveCongruent` as a conjunct and not just the residue.  That negative statement is
not formalised here either (it is another descent; see "Mathlib gaps").

What *is* proved here about this statement: it holds at the first six terms
`5, 6, 7, 13, 14, 15` of the pinned `terms` field
(`isPrimitiveCongruent_of_mem_first_six`), by explicit triangles. -/
theorem a273929_subset_a006991 (n : ℕ) (hn : MemA273929 n) : IsPrimitiveCongruent n := by
  sorry

end A273929
