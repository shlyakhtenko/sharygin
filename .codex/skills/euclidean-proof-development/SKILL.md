---
name: euclidean-proof-development
description: Develop and refactor Lean proofs in this repository's standalone synthetic Euclidean geometry formalization. Use when proving, reviewing, comparing, or reorganizing geometry declarations in this repository.
---

# Euclidean Proof Development

Treat the repository as the complete source of geometric knowledge. Favor direct proofs, and
let abstractions emerge only from proof patterns already present here.

## Establish the available context

1. Read the target statement, its imports, and the primitive definitions and axioms it uses.
2. Search the repository for relevant declarations and prior proofs.
3. Inspect the full proof of any result considered for reuse; do not select a theorem from its
   name alone.
4. Use Lean's core logic and declarations imported from this repository. Do not use Mathlib,
   online geometry references, textbook results, or geometric theorems recalled from outside
   the repository.

## Construct a direct proof

- Start from the hypotheses, definitions, axioms, and small repository lemmas nearest to the
  goal.
- Prefer explicit proof steps such as `intro`, `apply`, `exact`, constructors, and short `calc`
  blocks when they expose the geometric argument.
- Do not first prove a substantially broader theorem merely to discharge one goal.
- Do not add or strengthen an axiom, or change a theorem statement, to make a proof succeed
  unless the user explicitly requests that foundational change.
- Keep every foundational axiom in `Euclid/Geometry.lean`. Do not declare axioms, theorem-shaped
  postulate classes, or local substitutes for missing geometry in construction or solution files.
- A completed problem solution must contain no `axiom`, `sorry`, or theorem hypothesis that
  merely restates a missing geometric result. Configuration assumptions intrinsic to the problem
  are permitted.
- Keep imports within this project and Lean's bundled core/standard library.
- Build the affected file and then run `lake build`; leave no `sorry` in completed work.

## Extract common lemmas organically

Treat a reusable lemma as justified only after existing repository proofs reveal it.

1. Compare the current proof with completed proofs in the repository.
2. Identify a repeated, nontrivial sequence of formal steps rather than a similarity suggested
   only by an informal geometric theorem.
3. State the narrowest intermediate lemma that captures exactly that repeated sequence.
4. Record the declarations that motivated the extraction in a short source comment or docstring.
5. Refactor the earlier proof or proofs and the current proof to use the common lemma.
6. Keep the lemma only if the refactoring makes the shared proof structure clearer or removes
   real duplication. Do not add speculative or unused generalizations.

When no concrete repeated proof pattern exists, keep the new proof direct and local.

## Preserve evidence for proof-similarity analysis

- Prefer stable, descriptive declaration names and small proof blocks.
- Avoid opaque automation when it would conceal which repository facts perform the argument.
- Keep refactors separate enough in the diff that the common structure is reviewable.
- Report which prior proofs were compared and whether a shared lemma was extracted.
