seq:     A060938
claim:   schmidt-max-irrep-degree-submult
status:  PROVED 2026-07-30 (GroupTPP/MaxIrrepDegree.lean,
         commit 3d513bd; first recorded proof, LIKELY-KNOWN
         tier — Serre/Isaacs corollary, see file header)
stmt:    M
proof:   S-M
module:  Proofs/GroupTPP/CharDegrees.lean,
         CharDegreesMul.lean (charDegrees_prod)
source:  OEIS A060938 comment, Eric M. Schmidt,
         2012-10-17

CLAIM
  a(n) = maximal degree of a complex irreducible
  representation over all groups of order n.
  Claim: a(m) * a(n) <= a(m*n).

LEAN
  Def: max over group structures on Fin n (Fintype;
  see gnu note in A000001-cdo-iteration.md) of max of
  charDegrees — project already has charDegrees and
  card/sum facts (CharDegrees.lean). Statement M.

ROUTE (provable now, high confidence)
  Take G of order m and H of order n realizing the
  maxima. G x H has order mn, and
  charDegrees (G x H) = pointwise products
  (project theorem charDegrees_prod,
  CharDegreesMul.lean — verify exact form). Max of
  products >= product of maxes for these witnesses;
  a(mn) is a sup over MORE groups, so
  a(mn) >= a(m)a(n). Two lemmas + sup plumbing.
  This proves an OEIS comment that appears unproved
  anywhere: novel formalization + novel proof.

EVIDENCE
  All GAP-computed terms consistent.
