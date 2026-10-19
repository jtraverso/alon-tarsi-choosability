# The Alon–Tarsi theorem and 3-choosability of planar bipartite graphs in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

An *orientation* of a simple graph `G` is a relation `D` such that every arc is an edge of `G`,
every edge is oriented, and no edge is oriented both ways (`AlonTarsi.IsOrientation`). An
*Eulerian subdigraph* of `D` is a set of arcs with, at every vertex, as many arcs leaving as
entering; `AlonTarsi.eulerianCount D 0` and `AlonTarsi.eulerianCount D 1` count the even and the
odd ones. All statements are in the namespace `OrientationColouring`:

1. `alon_tarsi`, **the Alon–Tarsi theorem (1992)**. If `G` has an orientation `D` whose numbers
   of even and odd Eulerian subdigraphs differ, then `G` can be properly coloured from any lists
   with `|L(v)| > outdeg_D(v)` for every vertex `v`.
2. `choosable_three_of_isPlanar_bipartite`, **Alon–Tarsi (1992)**. Every finite planar bipartite
   graph is 3-choosable.

Planarity is combinatorial: a graph is planar if it has a *plane map*, a rotation system of its
darts of genus zero (Euler defect `0`). This is the notion of the registered entry
[PALOMAR-2026-10-15-000005](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000005&version=1)
([jtraverso/planar-list-colouring](https://github.com/jtraverso/planar-list-colouring)), where it is
shown to be equivalent to excluding `K₅` and `K₃,₃` minors (Wagner's theorem). Its definitions, and
those of orientations and Eulerian counts, are reproduced in `Challenge.lean` verbatim, with the
same names as in the library. `comparator.json` selects only the theorems; the definitions are not
selected separately and enter the check only as part of the theorem statements that use them.
Mathlib has the Combinatorial Nullstellensatz but neither of these theorems.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the audited statements. It imports only
  Mathlib.
- [`Solution.lean`](Solution.lean) and [`AlonTarsiLib/`](AlonTarsiLib): the proofs.
- [`LeanPool/`](LeanPool): plane maps, Euler's formula, face-length bounds and minor-closure of
  planarity, reused unchanged from the registered entry PALOMAR-2026-10-15-000005.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Alon–Tarsi** (`GraphPolynomial.lean`). Take the graph polynomial `∏_{arcs (u,v)} (x_u − x_v)`
  over `ℤ`. Expanding the product, its coefficient at the monomial `∏ x_v^{outdeg(v)}` is the sum
  of `(−1)^{|F|}` over the Eulerian arc sets `F`, i.e. `EE(D) − EO(D) ≠ 0`. The total degree equals
  the degree of this monomial, so Mathlib's Combinatorial Nullstellensatz
  (`combinatorial_nullstellensatz_exists_eval_nonzero`) gives a point, with coordinates from the
  lists (colours injected into `ℤ`), where the polynomial does not vanish: a proper list colouring.
* **Planar bipartite graphs** (`PlanarSparse.lean`).
  - In a bipartite graph every Eulerian subdigraph has an even number of arcs (summing out- minus
    in-degrees over one side), so `EO = 0 < 1 ≤ EE`.
  - Every set `s` of edges of a planar bipartite graph satisfies `|s| ≤ 2 |V(s)|`: subgraphs of
    planar graphs are planar (minor closure), and by induction (deleting an edge at a vertex
    lying in one edge of `s`) one reduces to the case where faces have length at least 4, where
    Euler's formula gives the bound.
  - Hakimi's lemma via Hall's theorem: an injective choice, for each edge, of one of its endpoints
    and one of two copies gives an orientation with all out-degrees at most 2.
  - Apply the Alon–Tarsi theorem with lists of size `3 > 2`.

## Sources

* N. Alon, M. Tarsi, *Colorings and orientations of graphs*, Combinatorica 12 (1992) 125–134,
  doi:10.1007/BF01204715.
* N. Alon, *Combinatorial Nullstellensatz*, Combin. Probab. Comput. 8 (1999) 7–29,
  doi:10.1017/S0963548398003411.
* S. L. Hakimi, *On the degrees of the vertices of a directed graph*, J. Franklin Inst. 279
  (1965) 290–308, doi:10.1016/0016-0032(65)90340-6.

## Authorship and use of AI

The author chose the results. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
