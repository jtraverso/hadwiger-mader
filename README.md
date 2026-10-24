# Mader's clique-minor bounds and Hadwiger for t ≤ 4

Lean 4 formalizations for finite simple graphs, using ordinary minors represented by
disjoint nonempty connected branch sets. This extension adds the K₅ density theorem:

**If n ≥ 3 and e(G) ≥ 3n − 5, then G has a K₅ minor.** Consequently, a K₅-minor-free
graph with n ≥ 3 has at most 3n − 6 edges.

The condition n ≥ 3 is essential: K₂ satisfies the density inequality but has no K₅ minor.
The Lean statements use `3 * n ≤ e + 5` and `e + 6 ≤ 3 * n`, avoiding truncated
natural-number subtraction. These are ordinary minor results; this package does not
establish a K₅ subdivision or Hadwiger's conjecture for t = 5.

## Results

All eight statements are in namespace `HadwigerMader` in the independently compiled
`Challenge.lean`; their proofs are in `Solution.lean`.

| Theorem | Scope |
| --- | --- |
| `mader` | Nonempty finite graph, `2^r * n ≤ 8 * e` implies a Kᵣ minor |
| `exists_degree_le_two` | A nonempty K₄-minor-free finite graph has a vertex of degree ≤ 2 |
| `card_edgeFinset_le` | K₄-minor-free graphs: `e + 3 ≤ 2 * n` for n ≥ 2 |
| `colorable_two_of_not_isMinor_K3` | K₃-minor-free graphs are 2-colorable |
| `colorable_three_of_not_isMinor_K4` | K₄-minor-free graphs are 3-colorable |
| `card_le_of_isMinor` | A finite minor has no more vertices than its host |
| `mader_K5` | `n ≥ 3` and `3 * n ≤ e + 5` imply a K₅ minor |
| `card_edgeFinset_le_K5` | K₅-minor-free graphs: `e + 6 ≤ 3 * n` for n ≥ 3 |

The first five statements and proof bodies are preserved from commit
`cb10154cd439a419d0bbf34052839dd27242b619`, registered as
`PALOMAR-2026-10-16-000001` version 1. This is a proposed extension; passing mechanical
preflight does not itself register a new Palomar version.

## Proof and reuse

`CliqueMinorsLib/K5Density.lean` reuses the existing edge-contraction count, lifting of
minor models through contractions, and Dirac's minimum-degree-three K₄-minor lemma.
Induct on the number of supported vertices. Contract an edge with at most two common
neighbors, losing at most three edges. Otherwise, the neighborhood of a chosen
nonisolated vertex has minimum degree at least three; its K₄ minor lifts to a K₅ minor
after adjoining the central vertex. The three-vertex base case has at most three edges.

The cardinality lemma chooses one vertex from each disjoint branch set. The new module
has no further project dependencies. Existing library proof bodies are preserved;
aggregate Mathlib imports are narrowed and classical scopes are localized so that the
strict build is warning-free.

## Verification

Pinned toolchain: Lean `v4.35.0-rc3`; Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e` (`v4.35.0-rc3`). Run:

```sh
./scripts/check.sh
```

This builds the solution with `--wfail`, compiles the independent Challenge, audits all
eight results and small complete-graph cases, and runs sandboxed Comparator with both
Lean and NanoDa. The Challenge has eight intentional theorem placeholders; no solution
or library proof contains `sorry` or a custom axiom. The only permitted axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

See [VERIFICATION.md](VERIFICATION.md), [formalization.yaml](formalization.yaml), and
[MATHLIB_DEFINITIONS.md](MATHLIB_DEFINITIONS.md). GitHub Actions runs the strict build and
the official full Palomar mechanical preflight on pull requests.

## Sources and attribution

- W. Mader, *Homomorphiesätze für Graphen*, Math. Ann. 178 (1968), 154–168,
  [doi:10.1007/BF01350657](https://doi.org/10.1007/BF01350657): selected K₅ ordinary-minor
  density case, rather than a formalization of the entire paper.
- W. Mader (1967), *Homomorphieeigenschaften und mittlere Kantendichte von Graphen*,
  [doi:10.1007/BF01364272](https://doi.org/10.1007/BF01364272).
- G. A. Dirac (1952), *A property of 4-chromatic graphs and some remarks on critical
  graphs*, [doi:10.1112/jlms/s1-27.1.85](https://doi.org/10.1112/jlms/s1-27.1.85).
- H. Hadwiger (1943), *Über eine Klassifikation der Streckenkomplexe*.
- R. Diestel, *Graph Theory*, fifth edition (2017), Proposition 7.2.1 for the inherited
  general Mader bound.

Author and responsible maintainer: Juan Pablo Traverso Gianini. The inherited proofs
were produced using Aristotle and Claude Code, as recorded in the original metadata.
The K₅ extension and packaging were produced with OpenAI Codex and mechanically checked.
No independent human mathematical review of the extension or mathematical novelty is
claimed. License: Apache-2.0.
