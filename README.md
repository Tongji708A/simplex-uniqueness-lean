# The Equality Cases of the Weak Simplex Conjecture in Lean

[![Lean CI](https://github.com/Tongji708A/simplex-uniqueness-lean/actions/workflows/lean_action_ci.yml/badge.svg?branch=main)](https://github.com/Tongji708A/simplex-uniqueness-lean/actions/workflows/lean_action_ci.yml)

This repository contains a Lean 4 companion formalization for *The Equality
Cases of the Weak Simplex Conjecture: A Response to Mulgund's Open Problem
8.1* by Kaiwen Yang, Hao Xu and Ge Xiong. It builds on
[mathlib](https://github.com/leanprover-community/mathlib4) and on the
formalization accompanying
[Mulgund's resolution of the Weak Simplex Conjecture](https://github.com/abhmul/weak-simplex-conjecture-lean),
pinned to Lean 4.31.0.

## What is formalized

The repository machine-checks the moment-generating half of Mulgund's Open
Problem 8.1 along a distributional route that is independent of the strict
product inequality used in the paper:

1. stochastic domination combined with equality of one strictly increasing
   moment forces equality of laws, and
2. a correlated Gaussian vector satisfying `R - J/(n+1) ⪰ 0` whose
   coordinate maximum carries the independent-maximum distribution at every
   threshold must have `R = I`.

Together these give, for any single moment-generating parameter, that
equality with the regular-simplex value forces the regular-simplex Gram
matrix. The Gram-rigidity step identifying the code geometrically is also
formalized.

| Paper result | Lean declaration | Source |
|---|---|---|
| Strict-monotone rigidity of stochastic domination | `measure_eq_of_iic_le_of_integral_eq`, `measure_eq_of_iic_le_of_mgf_eq` | [`StrictMonoDomination.lean`](SimplexUniquenessLean/StrictMonoDomination.lean) |
| All-threshold rigidity: independent maximum law forces `R = I` | `eq_one_of_lowerOrthant_eq_iid` | [`TailRigidity.lean`](SimplexUniquenessLean/TailRigidity.lean) |
| Normal upper-tail bound, bivariate pair-tail lower bound | `gaussianReal_tail_le_pdf_div`, `bivariate_pair_tail_lower_bound` | [`TailRigidity.lean`](SimplexUniquenessLean/TailRigidity.lean) |
| Gram rigidity: equal Gram matrices of spanning families are orthogonally equivalent | `exists_linearIsometryEquiv_of_gram_eq` | [`GramRigidity.lean`](SimplexUniquenessLean/GramRigidity.lean) |

## Scope

The paper's single-threshold theorem (strictness of the lower-orthant
comparison at every finite threshold) additionally rests on Royen's Gaussian
correlation theorem, which has no formalization to date, and is therefore
not formalized here. Its grouping step reduces to the slab-against-convex
Khatri–Šidák case, which we consider a plausible target for future
formalization. The coding and mean-width consequences in the paper are
likewise not formalized as standalone Lean theorems.

## Axiom audit

[`SimplexUniquenessLean/Audit/Axioms.lean`](SimplexUniquenessLean/Audit/Axioms.lean)
prints the transitive axioms of every public declaration. The accepted
output for each is exactly `[propext, Classical.choice, Quot.sound]`. The
same audit applied to the dependency reproduces the clean result reported
there.

## Building

Install Lean via [elan](https://lean-lang.org/install/), then

```bash
lake exe cache get
lake build
lake env lean SimplexUniquenessLean/Audit/Axioms.lean
```

The build pulls the dependency at the pinned revision recorded in
`lakefile.toml`.

## License

MIT. See [LICENSE](LICENSE).
