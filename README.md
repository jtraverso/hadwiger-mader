# Mader's theorem and Hadwiger's conjecture for t ≤ 4 in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

This repository formalizes, for finite simple graphs:

1. **Mader's theorem (1967).** A nonempty graph whose average degree is at least `2^{r−2}` has
   the complete graph `K_r` as a minor (`HadwigerMader.mader`). The hypothesis is stated as
   `2^r · |V| ≤ 8 · |E|`.
2. **Dirac (1952).**
   - A nonempty graph without a `K₄` minor has a vertex of degree at most two
     (`HadwigerMader.exists_degree_le_two`).
   - Such a graph on `n ≥ 2` vertices has at most `2n − 3` edges
     (`HadwigerMader.card_edgeFinset_le`).
3. **Hadwiger's conjecture for `t ≤ 4`** (Hadwiger 1943, Dirac 1952).
   - A graph without a `K₃` minor is 2-colourable (`HadwigerMader.colorable_two_of_not_isMinor_K3`).
   - A graph without a `K₄` minor is 3-colourable
     (`HadwigerMader.colorable_three_of_not_isMinor_K4`).

Minors are branch-set models. `H` is a minor of `G` when `G` has disjoint, nonempty, connected
branch sets, one for every vertex of `H`, with an edge of `G` between the branch sets of adjacent
vertices. This is the same definition as in the author's entries
[jtraverso/planar-list-colouring](https://github.com/jtraverso/planar-list-colouring) and
[jtraverso/kuratowski](https://github.com/jtraverso/kuratowski).

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and `CliqueMinorsLib/`: the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

The proofs never change the vertex type. A Finset of current vertices plays the role of the
graph, and edge contraction merges `y` into `x` by isolating `y`. Branch-set models in a
contracted graph or in a neighbourhood graph lift back to `G`.

* **Mader** (Diestel, *Graph Theory*, Prop. 7.2.1). The proof is by induction on `r` and then on
  the number of vertices.
  - If contracting an edge at `x` keeps the density bound, use induction and lift the model back
    to `G`.
  - Otherwise every neighbour of `x` has at least `2^{r−3}` common neighbours with `x`. Then the
    neighbourhood of `x` is dense enough to contain `K_{r−1}`, and adding `{x}` gives `K_r`.
* **Dirac's lemma.** Take a minimal counterexample with minimum degree at least 3.
  - Minimality forces a vertex `x` of degree 3 whose neighbours `a, b, c` induce a path
    `a–b–c`, with degree conditions on `a`, `b` and `c`.
  - Deleting `x` and `b` and adding the edge `ac` gives a smaller minor. It has minimum degree at
    least 3, which contradicts minimality.
* **Edge bound and Hadwiger for `t = 4`.** Remove a vertex of degree at most two and induct. For
  colouring, the removed vertex finds a colour that its at most two neighbours do not use.
* **Hadwiger for `t = 3`.** A cycle contracts to `K₃`, so the graph is a forest, and forests are
  2-colourable.

## Sources

* W. Mader, *Homomorphieeigenschaften und mittlere Kantendichte von Graphen*, Math. Ann. 174
  (1967) 265–268, doi:10.1007/BF01364272.
* G. A. Dirac, *A property of 4-chromatic graphs and some remarks on critical graphs*, J. London
  Math. Soc. 27 (1952) 85–92, doi:10.1112/jlms/s1-27.1.85.
* H. Hadwiger, *Über eine Klassifikation der Streckenkomplexe*, Vierteljahrsschr. Naturforsch.
  Ges. Zürich 88 (1943) 133–142.
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer (2017),
  doi:10.1007/978-3-662-53622-3.

## Authorship and use of AI

The author chose the results. The statements and proof plans were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs, which were audited and rebuilt locally. Lean
checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
