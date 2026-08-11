# Provenance

- The mathematical content follows the accompanying paper *The Equality
  Cases of the Weak Simplex Conjecture: A Response to Mulgund's Open Problem
  8.1*; theorem statements in this repository were authored to match the
  paper's statements.
- Proof scripts were developed with AI assistance (Anthropic Claude for
  statement design and verification harness; OpenAI models for proof
  search) under human direction, and are accepted solely on the basis of
  the Lean kernel check together with the axiom audit in
  `SimplexUniquenessLean/Audit/Axioms.lean`, whose accepted output for
  every public declaration is exactly `[propext, Classical.choice,
  Quot.sound]`.
- The dependency `weak-simplex-conjecture-lean` (Mulgund) is consumed at
  the pinned revision recorded in `lakefile.toml`; its own axiom audit was
  reproduced independently before this development began.
- No `sorry`, no `axiom` declarations and no `native_decide` are used
  anywhere in this repository.
