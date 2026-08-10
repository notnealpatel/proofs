---
name: sage
description: Invoke SageMath for computational algebra. Use when a task involves finite fields, polynomials, factoring, matrices over GF(p), number-theoretic computations, combinatorics, or computational verification of conjectures.
---

# `sage` — Computational Algebra via SageMath

Two modes. `print()` is mandatory — `sage -c` does not auto-echo.

```bash
sage -c "<expr>"        # evaluate a Sage expression
sage script.sage        # run a .sage file
```

Write `.sage` files with the `Write` tool for anything longer
than two lines; pass the path to `sage`. Do not heredoc.

## Sage syntax (not Python)

| Sage | Python | Note |
|------|--------|------|
| `a^b` | `a**b` | `^` is power, not xor |
| `a^^b` | `a^b` | `^^` is xor |
| `5` | `Integer(5)` | bare ints are Sage Integers |
| `1/3` | `Integer(1)/Integer(3)` | exact rational, not float |
| `5r` | `5` | raw Python int (suffix `r`) |
| `R.<x> = QQ[]` | `R = QQ['x']; (x,) = R._first_ngens(1)` | generator binding |
| `R.0` | `R.gen(0)` | generator access |

## Finite fields

```bash
sage -c "F=GF(7); print(F(3)*F(5))"                      # 1
sage -c "k.<a>=GF(11^3); print(a^2+a+1)"                 # a^2 + a + 1
sage -c "print(GF(997).multiplicative_generator())"       # primitive root
```

Bind generator names explicitly (`k.<a> = ...`) so repr is
deterministic.

## Polynomials

```bash
sage -c "R.<x>=GF(7)[]; print((x^2-1).factor())"         # (x + 1) * (x + 6)
sage -c "R.<x>=GF(7)[]; print((x^2+1).is_irreducible())" # True
sage -c "R.<x>=QQ[]; print((x^3-1).roots())"             # [(1, 1)]
sage -c "R.<x>=QQ[]; print((x^3-1).roots(ring=QQbar))"   # all roots in algebraic closure
```

## Matrices

```bash
sage -c "print(matrix(GF(7),[[1,2],[3,4]]).det())"        # 5
sage -c "print(matrix(QQ,[[1,2],[3,4]]).eigenvalues())"
sage -c "print(matrix(ZZ,[[1,2],[3,4]]).smith_form())"
```

Matrix repr is `[1 2]\n[3 4]` (no commas). For machine parsing,
use `M.list()` or `[list(r) for r in M.rows()]`.

## Number theory

```bash
sage -c "print(is_prime(97))"                             # True
sage -c "print(factor(100))"                              # 2^2 * 5^2
sage -c "print(list(factor(100)))"                        # [(2, 2), (5, 2)]
sage -c "print(euler_phi(100))"                           # 40
sage -c "print(next_prime(100))"                          # 101
sage -c "print(bernoulli(12))"                            # -691/2730
sage -c "print(number_of_partitions(100))"                # 190569292
```

## Combinatorics

```bash
sage -c "print(binomial(100,50))"
sage -c "print(Partitions(10).cardinality())"             # 42
sage -c "print(list(Permutations(3)))"
sage -c "print(graphs.PetersenGraph().chromatic_number())" # 3
sage -c "G=graphs.CycleGraph(5); print(G.automorphism_group().order())" # 10
```

## Sequences (OEIS)

```bash
sage -c "print(oeis([1,1,2,3,5,8,13]))"                  # search by terms
sage -c "s=oeis('A000045'); print(s.first_terms()[:10])"  # lookup by ID
```

## Groebner bases

```bash
sage -c "R.<x,y>=GF(7)[]; I=R.ideal(x^2+y,y^2+x); print(I.groebner_basis())"
sage -c "R.<x,y>=GF(7)[]; I=R.ideal(x^2+y,y^2+x); print(I.variety())"
```

## Elliptic curves

```bash
sage -c "E=EllipticCurve(QQ,[0,1]); print(E.rank())"
sage -c "E=EllipticCurve(GF(101),[0,1]); print(E.order())"
sage -c "E=EllipticCurve(GF(101),[0,1]); print(E.abelian_group())"
```

## Conjecture verification pattern

Write a `.sage` file when testing a conjecture over a range.
Always print structured output (one line per case, or JSON).

```python
# verify_conjecture.sage
import json
results = []
for n in range(2, 100):
    val = euler_phi(n)
    holds = (val >= sqrt(n))
    results.append({"n": int(n), "phi": int(val), "holds": bool(holds)})
    if not holds:
        print(f"COUNTEREXAMPLE: n={n}, phi(n)={val}")
if all(r["holds"] for r in results):
    print(f"VERIFIED for n in [2, 99]")
print(json.dumps({"tested": len(results), "all_hold": all(r["holds"] for r in results)}))
```

```bash
sage verify_conjecture.sage
```

## JSON output

Cast Sage types to `int`/`str`/`bool` before `json.dumps` —
Sage Integers are not directly JSON-serializable.

```bash
sage -c "
import json
F = GF(7)
print(json.dumps({'add': int(F(3)+F(5)), 'mul': int(F(3)*F(5))}))
"
```

## Structured output reference

| Need | Use |
|------|-----|
| Factor list | `list(f.factor())` → `[(factor, exp)]` |
| Flat root list | `.roots(multiplicities=False)` |
| Matrix as flat list | `M.list()` (row-major) |
| Matrix as nested list | `[list(r) for r in M.rows()]` |
| Scalar | `print()` directly |
| JSON-safe int | `int(sage_integer)` |
| JSON-safe list | `[int(x) for x in sage_list]` |
