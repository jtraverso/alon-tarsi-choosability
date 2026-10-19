/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import AlonTarsiLib.AlonTarsi

/-!
# Proofs of the statements in `Challenge.lean`

The definitions used by the statements (`AlonTarsi.IsOrientation`, `AlonTarsi.eulerianCount` and
the planarity notions `LeanPool.K5MinorFreeChoosability.IsPlanar`, `PlaneMap`, `eulerDefect`, ...)
are the library's own declarations, imported from `AlonTarsiLib/` and `LeanPool/`;
`Challenge.lean` reproduces them verbatim. The theorems are proved in `AlonTarsiLib/`: the graph
polynomial and its coefficient at the out-degree monomial (`GraphPolynomial.lean`) with Mathlib's
Combinatorial Nullstellensatz, and the sparsity of planar bipartite graphs from Euler's formula and
an out-degree-2 orientation by Hall's theorem (`PlanarSparse.lean`).
-/

@[expose] public section

open Finset SimpleGraph

/-! ## Statements -/

namespace OrientationColouring

open AlonTarsi

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- **The Alon–Tarsi theorem (1992).** If an orientation `D` of `G` has different numbers of even
and odd Eulerian subdigraphs, then `G` can be properly coloured from any lists `L` with
`|L v|` larger than the out-degree of `v` in `D`. -/
theorem alon_tarsi {Color : Type*} (G : SimpleGraph V) (D : V → V → Prop)
    (hD : IsOrientation G D) (hEO : eulerianCount D 0 ≠ eulerianCount D 1)
    (L : V → Finset Color) (hL : ∀ v, #{w | D v w} < (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v :=
  AlonTarsi.alon_tarsi G D hD hEO L hL

omit [Fintype V] [DecidableEq V] in
/-- **Alon–Tarsi (1992).** Every finite planar bipartite graph is 3-choosable. -/
theorem choosable_three_of_isPlanar_bipartite [Finite V] {Color : Type*} (G : SimpleGraph V)
    (hP : LeanPool.K5MinorFreeChoosability.IsPlanar G) (hB : G.Colorable 2)
    (L : V → Finset Color) (hL : ∀ v, 3 ≤ (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v :=
  AlonTarsi.choosable_three_of_isPlanar_bipartite G hP hB L hL

end OrientationColouring
