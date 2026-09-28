# Erdős 142 — the transverse-energy conjecture (TE): reduction, tensor no-go, and the missing lemma

Status: **TE is open. It is neither proved nor disproved here**, and nothing below
resolves Erdős 142. This note records (i) a complete rigorous reduction of the
Erdős-142 "square-gain" target to TE, (ii) a rigorous proof that the *first term
alone* is false, (iii) a rigorous **no-go theorem** showing that no carry-free
digit/tensor cap can refute TE (this corrects a proposed counterfamily), and (iv)
the exact missing lemma.

All sets are finite. Write `[N) = {0,1,…,N-1}` and view `S ⊆ [N)²` with points
`p = (p₁,p₂)`; `p₁` is the first coordinate (column index), `p₂` the second
(row index). Let `r = r₃(N)` be the largest size of a 3-AP-free subset of `[N)`,
and `α = r/N`.

## 0. Definitions

* A **vector cap** is `S ⊆ [N)²` with no *nonconstant* coordinatewise 3-term
  progression: there is no `p,q,r ∈ S` with `p + r = 2q` (coordinatewise) unless
  `p = q = r`.
* **Additive energy** `E(S) = #{(a,b,c,d) ∈ S⁴ : a+b = c+d}`.
* **Transverse additive energy**
  `E⊥(S) = #{(a,b,c,d) ∈ S⁴ : a+b = c+d, a₁ ≠ c₁, a₂ ≠ c₂}`.
* Difference representation `r_S(u) = #{(x,y) ∈ S² : x − y = u}`. Then
  `E(S) = Σ_u r_S(u)²` and **`E⊥(S) = Σ_{u₁≠0, u₂≠0} r_S(u)²`** (the map
  `(a,b,c,d) ↦ u = a−c = d−b` together with the two ordered pairs `(a,c),(d,b)`
  is a bijection). Hence `E(S) − E⊥(S) = Σ_{u₁=0 or u₂=0} r_S(u)²`.

**Candidate (TE).** There exist absolute `η > 0`, `C`, `N₀` such that every vector
cap `S ⊆ [N)²` with `N ≥ N₀` satisfies

> `E⊥(S) ≤ C α^{1+η} |S|³ + C r |S|²`.  (TE)

## 1. Rigorous reduction (TE ⇒ square gain)

**Lemma 1a (energy lower bound).** `E(S) ≥ |S|⁴ / (4N²)`.
*Proof.* Pair-sums `x+y` with `x,y ∈ S` lie in `[0,2N)²`, a set of `4N²` points. With
`ν(s) = #{(x,y)∈S² : x+y=s}`, Cauchy–Schwarz gives
`E(S) = Σ_s ν(s)² ≥ (Σ_s ν(s))²/(4N²) = |S|⁴/(4N²)`. ∎

**Lemma 1b (excluded quadruples).** `E(S) − E⊥(S) ≤ 2 r |S|²`.
*Proof.* Count quadruples with `a₁ = c₁`. From `a+b=c+d` and `a₁=c₁` we get `b₁=d₁`;
writing `a=(x,p), b=(x',q), c=(x,s), d=(x',t)` the remaining condition is `p+q = s+t`
with `(x,p),(x,s)` in column `x` and `(x',q),(x',t)` in column `x'`. Let
`R_x = {y : (x,y) ∈ S}`. Fixing `p,q,s` determines `t`, so the count for a column pair
`(x,x')` is `≤ |R_x|²|R_{x'}|`. Summing,
`Σ_{x,x'} |R_x|²|R_{x'}| = (Σ_x |R_x|²)(Σ_{x'} |R_{x'}|)`.
Each `R_x` is a 1-D 3-AP-free set (a coordinatewise progression constant in the first
coordinate is forbidden), so `|R_x| ≤ r`; and `Σ_x |R_x| = |S|`. Hence the count is
`≤ (r|S|)·|S| = r|S|²`. The same argument bounds the `a₂=c₂` quadruples by `r|S|²`, and a
union bound gives `E(S) − E⊥(S) ≤ 2 r |S|²`. ∎

**Lemma 1c (consequence of TE).** Assume TE. Let `A ⊆ [N²)` be 3-AP-free, `m=|A|`, and
let `S ⊆ [N)²` be its base-`N` digit set. Then `S` is a vector cap, `|S| = m`, and

> `m ≤ (4C + o(1)) · N² α^{1+η}`,  hence  `r₃(N²) ≤ (4C+o(1)) N² α^{1+η}`.

*Proof.* `S` is a vector cap: a nonconstant coordinatewise progression
`(a₁,a₂)+(c₁,c₂) = 2(b₁,b₂)` gives `a + c = 2b` in `A`, a nonconstant 3-AP. Also
`|S|=m`. By 1a, 1b and TE,
`m⁴/(4N²) = |S|⁴/(4N²) ≤ E(S) ≤ E⊥(S) + 2r|S|² ≤ C α^{1+η} m³ + (C+2) r m²`.
Dividing by `m²`, the positive root of `m²/(4N²) − Cα^{1+η}m − (C+2)r = 0` is
`m = 2CN²α^{1+η} + 2N √(C²α^{2+2η}N² + (C+2)r)`. Inside the root,
`C²α^{2+2η}N² / ((C+2)r) = (C²/(C+2)) · N α^{1+2η} → ∞` because `α = N^{−o(1)}`
(Roth's theorem) and `N α^{1+2η} = N^{1−o(1)}`; hence the root is
`Cα^{1+η}N(1+o(1))` and `m ≤ (4C+o(1))N²α^{1+η}`. ∎

**The gain, stated accurately.** The TE-derived upper bound is
`r₃(N²) ≤ (4C+o(1)) N² α^{1+η}` with `N²α^{1+η} = N²(r/N)^{1+η} = r^{1+η}N^{1−η}`.
Since `r = r₃(N) = N^{1−o(1)}` (Behrend's lower bound together with Roth's theorem),
`N = r^{1+o(1)}`, hence `N^{1−η} = r^{(1−η)(1+o(1))} = r^{1−η+o(1)}` and
`N²α^{1+η} = r^{1+η}N^{1−η} = r^{2+o(1)}`. Thus the upper bound may be **rewritten**
purely in terms of `r₃(N)`:

> `r₃(N²) ≤ (4C+o(1)) · r₃(N)^{2+o(1)}`.

This is an upper-bound reformulation only; **no matching lower bound is asserted or used**,
and in particular `r₃(N)²` is *not* in general a lower bound for `r₃(N²)` — the naive
base-`N` product carries, e.g. `r₃(4)=3` but `r₃(16)=8 < 9 = r₃(4)²`. Relative to the
trivial upper bound `r₃(N²) ≤ N²`, the saving is `α^{1+η} = N^{−o(1)}`, a subpolynomial
factor, **not** a fixed power of `N`; equivalently, in the Behrend regime
`α = exp(−c√(log N))` the saving is `exp(−c(1+η)√(log N))`. No claim is made here about
any specific published record for `r₃`, and the exponent `1+η` is not optimised.

**Remark 1c′ (what is really at stake).** The bound `r₃(N²) ≤ N r` is trivial: every
row `S_y = {x : (x,y) ∈ S}` of a vector cap is a 1-D 3-AP-free set, so `|S_y| ≤ r`, and
there are at most `N` nonempty rows, giving `|S| ≤ N r` (the same holds via columns).
But `N² α^{1+η}` at `η = 0` equals `N²·(r/N) = N r`. Hence the **scale of the
cardinality consequence of TE at `η = 0`** coincides with the trivial row bound
`r₃(N²) ≤ N r`; the entire content of TE is the subpolynomial factor `α^η = N^{−o(1)}` by
which it improves that scale. Since `α = N^{−o(1)}`, the improvement is `N^{−o(1)}`, not a
fixed power of `N`. This is why the second term `C r |S|²` cannot be dropped (Lemma 1d)
and why the conjecture is non-trivial only in the transverse (off-axis) energy.

**Lemma 1d (the second term is necessary).** The "stronger form" of TE with the second
term deleted is **false**. Let `A ⊆ [N)` be a 1-D cap of size `r`, and put
`S = A × {0,1} ⊆ [N)²`. Then `S` is a vector cap (second coordinates lie in `{0,1}`, so
`ε₁+ε₃ = 2ε₂` forces `ε₁=ε₂=ε₃`), `|S| = 2r`, and `E⊥(S) = 2 (E(A) − r²)` (indeed
`r_S(w,0)=2r_A(w)` and `r_S(w,±1)=r_A(w)`, so `E⊥(S)=Σ_{w≠0}2r_A(w)²=2(E(A)−r²)`, in
agreement with Prop. 4(a) at `T={0,1}`). Since `E(A) ≥ r⁴/(2N)`,
`E⊥(S) ≥ 2(r⁴/(2N) − r²) = r²(α r − 2) ≍ α r³`, and `|S|³ = 8r³`, so

> `E⊥(S)/(α^{1+η}|S|³) ≥ (α r − 2)/(8 α^{1+η} r) ≍ (1/8) α^{−η} → ∞`.

So the first term alone cannot hold; the second term is essential, exactly as stated in
the problem. (Note `E⊥(S) ≤ 2r³ = |S|³/4 ≤ r|S|²`, so TE itself holds here.)

## 2. Tensor / carry-free digit caps do **not** refute TE

This section corrects a proposed counterfamily. Fix an integer base `b ≥ 3` and a
**digit alphabet** `D ⊆ {0,…,b−1}`; assume the no-carry condition `b > 2 max D` and that
`D` is 1-D 3-AP-free. Let `D^d = { Σ_{i<d} εᵢ bⁱ : εᵢ ∈ D } ⊆ [b^d)`.

**Fact 2a.** If `D,E` are 1-D 3-AP-free and `b > 2 max(D∪E)`, then
`B=D^d`, `C=E^d` are 1-D 3-AP-free, `S = B×C ⊆ [N)²` with `N = b^d` is a vector cap,
`|S| = |D|^d |E|^d`, and

> `E(B) = E(D)^d`, `E(C) = E(E)^d`, and `E⊥(S) = (E(D)^d − |D|^{2d})(E(E)^d − |E|^{2d})`.

*Proof.* Write `x=Σ_i x_i b^i` and `y=Σ_i y_i b^i` with `x_i,y_i ∈ D`, and let
`M = max D`, so `2M < b`.

*(i) Signed digits and uniqueness.* For `x,y∈B` we have `x−y=Σ_i (x_i−y_i)b^i` with
coefficients `x_i−y_i ∈ D−D ⊆ [−M,M] ⊂ (−b/2,b/2)`. Suppose `Σ_i e_i b^i = Σ_i f_i b^i`
with `e_i,f_i ∈ D−D`; then `g_i := e_i−f_i` satisfies `|g_i| < b` and `Σ_i g_i b^i = 0`.
Reducing modulo `b` gives `g_0 ≡ 0 (mod b)`, and the only multiple of `b` with `|g_0|<b`
is `0`, so `g_0 = 0`; dividing by `b` and iterating gives `e_i = f_i` for all `i`.
(Reduction modulo `b` and divisibility are valid for negative integers, so this argument
covers negative differences too.) Hence signed-digit expansions with coefficients in
`D−D` are **unique**. Consequently, for `u = Σ_i u_i b^i` with `u_i ∈ D−D` the digit
pairs may be chosen independently, giving `r_B(u) = ∏_i r_D(u_i)`; if `u` admits no such
expansion then `r_B(u) = 0`. Therefore
`E(B) = Σ_u r_B(u)² = ∏_i (Σ_e r_D(e)²) = E(D)^d`.

*(ii) 3-AP-freeness.* If `x+z = 2y` with `x,y,z ∈ B`, then `x_i+z_i ≤ 2M < b` and
`2y_i ≤ 2M < b`, so `Σ_i (x_i+z_i)b^i = Σ_i (2y_i)b^i` is an equality of base-`b`
expansions with digits in `[0,b)`, and uniqueness of such expansions gives
`x_i+z_i = 2y_i` for all `i`. If `x ≠ y` then `x_i ≠ y_i` for some `i`, so
`(x_i,y_i,z_i)` is a nonconstant 3-AP in `D`, impossible; hence `x=y=z`.

The energy formula for `S=B×C` is the product identity
`E⊥(B×C) = (E(B)−|B|²)(E(C)−|C|²)` (from `r_S(u)=r_B(u₁)r_C(u₂)` and `r_B(0)=|B|`,
`r_C(0)=|C|`). ∎

**Fact 2b (energy deficit).** For any set `D` with `|D| = t ≥ 2`, `E(D) < t³`.
*Proof.* `E(D) = Σ_e r_D(e)² ≤ (max_e r_D(e))·Σ_e r_D(e) ≤ t·t² = t³`. Equality forces
`r_D(e) = t` for every `e` with `r_D(e) > 0`; `r_D(e)=t` means `x+e ∈ D` for all `x ∈ D`,
i.e. `D+e ⊆ D`, and finiteness gives `D+e = D`, so `e = 0`. But `Σ_{e≠0} r_D(e)² = t³ − t² > 0`
for `t ≥ 2`, contradicting equality. ∎

**Theorem 2c (no-go).** Fix `b, D, E` once and for all, with `t=|D| ≥ 2`, `u=|E| ≥ 2`, and
set `q := (E(D)/t³)(E(E)/u³)`. Then `q < 1` is a **fixed constant depending only on
`b,D,E`** (by Fact 2b), and as `d → ∞` (so `N = b^d → ∞`)

> `E⊥(S)/|S|³ = q^d (1 + o(1))`,  hence for every `η > 0`,  `E⊥(S)/|S|³ ≤ C_η ρ(N)^{1+η}`,

where `ρ(N) = r₃(N)/N`. In fact `E⊥(S) ≤ ρ(N)|S|³` for all large `d` (TE holds with
`η = 0`), so this family satisfies TE for **every** `η > 0` and never refutes it. (If
`t=1` or `u=1` then `B` or `C` is a singleton and `E⊥(S)=0`, so TE is trivial.)

*Proof.* `|S|³ = t^{6d}u^{6d}` and by Fact 2a
`E⊥/|S|³ = (E(D)/t³)^d(E(E)/u³)^d(1−o(1)) = q^d(1+o(1))`, with `q<1`.
Behrend's theorem gives `r₃(M) ≥ M exp(−C₀√(log M))`, so for `M=N=b^d`,
`ρ(N) ≥ exp(−C₀√(d log b))`. Hence
`q^d / ρ(N)^{1+η} ≤ q^d exp(C₀(1+η)√(d log b)) → 0`
because `q<1` kills the exponential while `√d` is subexponential. The second term of TE
is irrelevant (the first already dominates). ∎

**Corollary 2d (the proposed criterion is wrong).** The criterion "`2α(D) ≤ 1`", with
`α(D) = log(t³/E(D))/log(b/t)`, arises only from comparing `E⊥/|S|³` with the
**per-digit** density `(t/b)^d =: β^d`, not with the true density `ρ(b^d)`. It is
achievable by 3-AP-free alphabets — e.g. `D={0,1}`, `b=4` gives
`α(D) = log(4/3)/log 2 ≈ 0.415 < 1/2` — yet by Theorem 2c it does **not** refute TE.
Conversely, no lower bound `α(D) ≥ 1/2` follows from 3-AP-freeness: for fixed `D`,
`α(D) → 0` as `b → ∞`. The correct criterion for a digit-product family to threaten TE
would be `E(D)=t³` (so that `q` is not `<1`), which is impossible for `t ≥ 2` by Fact
2b. **Hence no carry-free digit/tensor cap refutes TE.**

### Numerical confirmation (true density `ρ(N)=r₃(N)/N`, `N=b^d`)

| base `b` | `d` | `N` | `\|S\|` | `E⊥` | `E⊥/\|S\|³` | `ρ(N)` | TE holds? |
|---|---|---|---|---|---|---|---|
| 3 | 2 | 9  | 16  | 400     | 0.0977 | 5/9=0.556  | yes |
| 3 | 3 | 27 | 64  | 23104   | 0.0881 | 11/27=0.407| yes |
| 3 | 4 | 81 | 256 | 1081600 | 0.0645 | 22/81=0.272| yes |
| 4 | 3 | 64 | 64  | 23104   | 0.0881 | 20/64=0.312| yes |

(`S = B×B`, `B={0,1}^d` in base `b`.) In every case `E⊥/|S|³ < ρ(N)`, i.e. TE holds
already with `η=0`; asymptotically this persists because `E⊥/|S|³ = q^d` is exponential
in `d` while `ρ(N) ≥ exp(−C₀√(d log b))` is only subexponential.

## 3. Proved special cases

**Proposition 3 (tensor caps).** With `B=D^d`, `C=E^d`, `S=B×C` as in §2, TE holds for
every `η > 0`, and indeed for `η = 0` for all sufficiently large `d`; moreover the
second term of TE is not needed. ∎ (Theorem 2c.)

**Proposition 4.** *(a) Exact products.* If `S = A × T` with `A,T ⊆ [N)` 1-D caps, then
`|S| = |A||T|` and

> `E⊥(S) = (E(A) − |A|²)(E(T) − |T|²)`.

For `|T| = 1` the right side is `0` and indeed `E⊥(S) = 0` (all differences have second
coordinate `0`). *Proof.* `r_S(u) = r_A(u₁) r_T(u₂)`, `r_A(0)=|A|`, `r_T(0)=|T|`, so
`E⊥(S) = Σ_{u₁,u₂≠0} r_A(u₁)² r_T(u₂)² = (E(A)−|A|²)(E(T)−|T|²)`. ∎

**Maximum-cap Cartesian-product stress test.** **Evidence: exact prose reduction independently audited, not Lean formalized.** Take a maximum scalar cap `A ⊂ [N)`, put `r = |A| = r₃(N)` and `α = r/N`, and define its ordered additive energy by

> `E(A) = #{(a,b,a',b') ∈ A⁴ : a+b = a'+b'}`.

For `S = A × A`, the product identity in Proposition 4(a), specialized to `T = A`, gives for the note's coordinatewise transverse functional (both coordinate pairings nonidentity)

> `E⊥(S) = (E(A) − r²)²`.

This is not the ordinary two-dimensional energy: the full product has `E(S) = E(A)²`. Nor is it the convention that excludes only the globally diagonal difference `u=(0,0)`, which would give `E(A)² − r⁴` and would retain the axis terms with `u₁=0` or `u₂=0`. The coordinatewise transverse functional excludes both axes, as required here.

With `m = |S| = r²`, TE therefore becomes exactly

> `(E(A) − r²)² ≤ C α^(1+η) r⁶ + C r⁵`.

Since `r = N^(1−o(1))`, while `α = r/N = N^(−o(1))`, the ratio of the first term on the right to the second is `α^(1+η)r = N^(1−o(1)) → ∞`. Thus, after an eventual threshold and with constants uniform over all maximum caps, TE restricted to this product subfamily is asymptotically equivalent to

> `E(A) − r² ≪ r³ α^((1+η)/2)`

for every maximum cap `A`. This necessary-and-sufficient reformulation is only for the product subfamily; it says nothing equivalent about arbitrary vector caps `S`.

As a heuristic, not a known exponent or a claim about the energy of maximum caps, write
`E(A) − r² ~ r³ α^σ`. Because `α → 0`, TE requires `σ ≥ (1+η)/2`; at `η = √2−1` the threshold is `σ = 1/√2`. Larger `σ` means smaller energy. The product stress test therefore reduces to an open one-dimensional upper bound for the energy of every maximal-size cap, and supplies neither a proof of TE nor a counterexample.

Two guardrails are essential. Cauchy–Schwarz gives only the lower bound
`E(A) ≥ r⁴/|A+A|`; it cannot prove the needed upper bound. Behrend gives a lower bound on `α`, but does not control the energy of every maximum cap.

**The formula is *not* valid for arbitrary subsets.** Take `A = T = {0,1}` and the
diagonal `S = {(0,0),(1,1)} ⊆ A×T`. Then `S` is a vector cap (a two-point set has no
nontrivial 3-AP), `E⊥(S) = 2` (only the two differences `±(1,1)` occur, once each),
whereas the right-hand side gives `(E(A)−|A|²)(E(T)−|T|²) = (6−4)² = 4`. So the product
formula requires `S` to be the *full* product.

*(b) Arbitrary sets on at most two rows (or columns).* Let `S ⊆ [N) × {τ₀,τ₁}` be
arbitrary (no cap hypothesis), with `X = {x : (x,τ₀) ∈ S}`, `Y = {x : (x,τ₁) ∈ S}` and
`n = |S| = |X|+|Y|`. Then

> `E⊥(S) ≤ |S|³/4`.

*Proof.* The second-coordinate equation `a₂+b₂ = c₂+d₂` together with `a₂ ≠ c₂` forces
`{a₂,c₂}={τ₀,τ₁}` and `{b₂,d₂}={τ₀,τ₁}`, in exactly two orientations, giving
`E⊥(S) = 2 Σ_{w≠0} t(w)²` with `t(w) = #{(x,y) ∈ X×Y : x−y = w}`. Now
`Σ_w t(w)² = #{(x,x')∈X², (y,y')∈Y² : x−x' = y−y'} = Σ_δ r_X(δ) r_Y(δ) ≤ √(E(X)) √(E(Y))`
by Cauchy–Schwarz, and `E(X) ≤ |X|³`, `E(Y) ≤ |Y|³`, so `E⊥(S) ≤ 2(|X||Y|)^{3/2} ≤ 2(n²/4)^{3/2} = n³/4`
(AM–GM). ∎

If in addition `S` is a vector cap, then each row `X, Y` is 1-D 3-AP-free, so
`|X|,|Y| ≤ r` and `n ≤ 2r`; hence

> `|S|³/4 ≤ (n/4) n² ≤ (r/2) n² ≤ r |S|²`,

so TE holds for such `S` via the second term alone. The same holds with rows and columns
interchanged.

*(c)* Any vector cap with `|S| ≤ r` satisfies TE trivially, since
`E⊥(S) ≤ E(S) ≤ |S|³ ≤ r|S|²`.

## 4. The exact missing lemma

**Missing lemma (transverse-energy inverse theorem).** There exist absolute `η>0,C` such
that every vector cap `S ⊆ [N)²` (`N` large) satisfies TE, equivalently
`E⊥(S) ≤ C α^{1+η}|S|³ + C r|S|²`.

**What the inverse-theorem route gives, and why it falls short.** The only route
considered here is the "energy ⇒ many 3-APs" inverse theorem. In one dimension the
relevant statement is Pohoata–Roche-Newton, arXiv:1905.08457, Theorem 6.1: *if `A ⊂ ℤ`
has `E(A) ≥ δ|A|³` additive quadruples, then `A` contains at least
`exp(−Cδ^{−c})|A|²` three-term arithmetic progressions* (attributed there to Sanders).
To use it for a finite `S ⊂ ℤ²` one first transports `S` to `ℤ`: for `M > 2N` the map
`φ(x,y) = x + My` is injective on `[N)²` and, because all coordinate sums are `< 2N < M`,
it satisfies `φ(p)+φ(r) = 2φ(q) ⟺ p+r = 2q`; thus `φ` is a **Freiman 2-isomorphism**
onto `φ(S) ⊂ ℤ`, preserving additive energy and the set of 3-APs. Applying Theorem 6.1 to
`A = φ(S)` and using that a vector cap has only the `|S|` trivial 3-APs
(`p=q=r`) gives

> `E⊥(S) ≤ E(S) ≤ |S|³ / (log|S|)^{1/c}`,

a **logarithmic** saving. But TE demands the saving `α^{1+η} = N^{−o(1)} = e^{−o(log N)}`,
which in the Behrend regime `α = e^{−c√(log N)}` equals `e^{−c(1+η)√(log N)}` — *smaller*
than any inverse power of `log N`. The polylog-versus-`√log` gap is exactly what is
missing. Note also that the excluded part satisfies `E(S) − E⊥(S) ≤ 2r|S|²` by Lemma 1b,
so the gap lies entirely in the transverse part.

**Conditional resolution (what a power saving would buy).** Suppose there were an
absolute `δ ∈ (0,1)` such that every vector cap `S ⊆ [N)²` satisfied the **power-saving
energy bound** `E(S) ≤ |S|^{3−δ}`. Then TE holds. Indeed `E⊥(S) ≤ E(S) ≤ |S|^{3−δ}`, and
dividing by `|S|³` it suffices that `|S|^{−δ} ≤ Cα^{1+η} + Cr/|S|` for all `|S| ≥ 1`. This
splits into two regimes:

* `|S| ≤ (Cr)^{1/(1−δ)}`: then `|S|^{1−δ} ≤ Cr`, i.e. `|S|^{−δ} ≤ Cr/|S|`;
* `|S| > (Cr)^{1/(1−δ)}`: then `|S| ≥ (Cr)^{1/(1−δ)} ≥ (Cα^{1+η})^{−1/δ}` for `N ≥ N₀`,
  i.e. `|S|^{−δ} ≤ Cα^{1+η}`,

because `(Cr)^{1/(1−δ)}(Cα^{1+η})^{1/δ} ≥ r^{1/(1−δ)}Cα^{(1+η)/δ} = N^{1/(1−δ)−o(1)} → ∞`
using `r = N^{1−o(1)}` and `α = N^{−o(1)}`. So a power-saving energy bound for 2-D
3-AP-free sets would **imply** TE. The available inverse theorem supplies only the
polylogarithmic saving `1/polylog`, which does **not** suffice. No such power saving is
proved or disproved here, and Erdős 142 remains open.

Concretely, universal bounds of this family stop far short of TE: Shao
(arXiv:1308.2247, Prop. 2.2) gives a bound of the form
`E(S) ≤ e₂|S|³ + O(N|S|²)` with `e₂ ≈ 0.4595`, i.e. `E(S)/|S|³ ≤ e₂ + O(N/|S|)`, a
constant — whereas TE needs a factor tending to `0`. (This is not a survey of the
literature; no exhaustiveness is claimed, and it is not asserted that no sharper
argument exists.)

## 5. Summary

* TE ⇒ `r₃(N²) ≤ (4C+o(1)) N² α^{1+η} = (4C+o(1)) r₃(N)^{2+o(1)}` (Lemma 1c): a
  saving of order `N^{−o(1)}` over the trivial `r₃(N²) ≤ N²`, i.e. a subpolynomial
  factor, not a fixed power of `N`.
* The first term of TE alone is false (Lemma 1d, constant `1/8`); the second term is
  essential.
* No carry-free digit/tensor cap refutes TE (Theorem 2c, Corollary 2d); the per-digit
  exponent `log(4/3)/log 2 ≈ 0.415` (for `D={0,1}`, `b=4`) is an artefact of substituting
  the per-digit density `(t/b)^d` for the true density `r₃(N)/N`.
* Proved special cases: tensor caps (§3); exact products `A×T` and arbitrary sets on
  ≤2 rows/columns (§3); caps with `|S| ≤ r` (§3).
* Missing lemma: the transverse-energy inverse theorem of §4.
* **TE and Erdős 142 remain open.**
