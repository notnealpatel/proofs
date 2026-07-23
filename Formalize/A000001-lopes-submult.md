seq:     A000001
claim:   lopes-gnu-submultiplicativity
status:  open; COPRIME CASE PROVABLE NOW
stmt:    M
proof:   M (coprime case) / open (general)
module:  Xlib group layer; Proofs/Xlib/WreathNg.lean
         (direct-product lower-bound flavor)
source:  OEIS A000001 comment, Jorge R. F. F. Lopes,
         2024-04-21

CLAIM
  gnu(i) * gnu(j) <= gnu(i*j) for all i, j >= 1.

LEAN
  gnu def as in A000001-cdo-iteration.md (M, via
  decidable iso on Fin n group structures).

ROUTE (coprime case — provable now, high confidence)
  For gcd(i,j) = 1 the map (G,H) -> G x H is
  injective on iso-class pairs: inside G x H the
  elements of order dividing i are exactly G x 1
  (order of (g,h) = lcm of orders; |H| coprime to i
  forces h = 1), so G is recovered as a
  characteristic subset, and H symmetrically. Hence
  gnu(i)gnu(j) <= gnu(ij). Mathlib has order-of-
  element and product-group machinery; the argument
  is elementary and self-contained. Novel: this
  coprime case appears unproved anywhere in-entry.
ROUTE (general case)
  Open: G x H ≅ G' x H' with non-coprime orders does
  not force G ≅ G' (cancellation fails in general);
  a different injection is needed.

EVIDENCE
  Verified within GAP SmallGroups range per entry
  discussion.
