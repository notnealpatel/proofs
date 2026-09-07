# Boolean matrices have full Boolean row rank asymptotically

## Result

The development formalizes the exact-fullness statement suggested in OEIS A354741: for a uniformly chosen square $n\times n$ matrix over the Boolean semiring,
$$
\Pr(\text{Boolean row rank}=n)\longrightarrow 1
\quad(n\to\infty).
$$

Here the Boolean semiring is `{0,1}` with addition $=\lor$ and multiplication $=\land$, not arithmetic in $\mathbb F_2$. A matrix is `BoolMatrix m n := Fin m → Fin n → BoolSemiring`. For rows $u,v$, `RowLE u v` means that every coordinate where $u=1$ also has $v=1$.

For a set of row indices $S$, `rowSpan A S` is the finite set of coordinatewise-OR sums of subsets of the rows in $S$, including the empty sum. `BoolRowRankLE A r` asserts that some set of at most $r$ rows has the same span as all rows, and `boolRowRank A` is the least such cardinality. This is the row-rank statistic used for the A354741 counting problem.

The principal declarations are `boolRowRank_eq_of_antichain`, `card_filter_rowLE_le`, `card_dominatedRowLE_le`, `one_sub_le_fullRowRankFraction`, and `fullRowRankFraction_tendsto_one` in `Proofs/BilinearComplexity/BooleanRankGeneric.lean`.

## Counting mechanism

If all rows are nonzero and pairwise incomparable under `RowLE`, then every row is necessary: a row omitted from a spanning set would have to be the OR of remaining rows, forcing one of those rows to be dominated by it.

For fixed distinct ordered rows $i,j$, and $n\ge2$, the source proves
$$
\#\{A:\operatorname{RowLE}(A_i,A_j)\}
 \le 3^n\,2^{n(n-2)}.
$$
The factor $3^n$ comes from the three allowed ordered bit pairs in each column; the other $n-2$ rows are unrestricted. The union bound gives at most
$$
n^2\,3^n\,2^{n(n-2)}
$$
matrices with a dominated distinct row pair. Since there are $2^{n^2}$ total matrices, the defined fraction `fullRowRankFraction n` satisfies, for every $n\ge2$,
$$
1-n^2(3/4)^n
\le \texttt{fullRowRankFraction }n
\le1.
$$
The squeeze theorem yields the stated limit. No claim is made for a generic random-matrix model: the theorem concerns only uniformly counted $n\times n$ Boolean matrices with this row-rank definition.

## Rank distinction and contribution

`BooleanRank.lean` defines a different statistic, `boolRank`: the least factorization/rectangle-cover (Schein) rank. The source proves only the bridge `boolRank_le_boolRowRank`; these ranks are not interchangeable and diverge in general. The result here is not a theorem about rectangle-cover rank, real rank, or arbitrary field rank. The $\mathbb F_2$ contrast is also a different problem: its full-rank probability tends to $\prod_{i\ge1}(1-2^{-i})\approx0.2888$, not 1.

The contribution is a machine-formalized proof of the precise A354741 row-rank limit and its elementary antichain/union-bound mechanism. It should be described as formalization and proof development, not as an established global-priority claim.

## Recovered evidence and limitations

The supplied draft records an earlier cold check, kernel computations giving 156 full Boolean-row-rank matrices and 168 nonsingular $\mathbb F_2$ matrices at $n=3$, and a literature sweep that found no record of this exact statement or antichain proof as of 2026-08-02/03. The nearest recorded neighbor was Pourmoradnasseri–Theis (2017), concerning rectangle-cover rank and $(1-o(1))n$, not exact Boolean row-rank fullness. These are recovered reports, not fresh verification in this workspace; the literature gate remains incomplete.

## Remaining obligations

A prover/package pass must prepare the minimal Palomar Challenge and Solution bridge, an allowlisted Comparator configuration, `formalization.yaml`, licensing/package metadata, and a pinned reviewable commit. Those artifacts were intentionally not created here. Human review is pending; no agent review, Palomar acceptance, publication, or human approval is claimed. The development was AI-assisted.
