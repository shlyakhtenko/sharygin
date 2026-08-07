# Rules for Formalizing Problems

Consult this file before starting each new geometry problem in this repository.

## Keep each problem self-contained

- Give every problem its own solution file and its own supporting folder.
- Name them from the source, PDF page, and problem number. For example:
  - `soultions/sharygin-11-5.lean`
  - `soultions/Sharygin11Problem5/`
- Do not import another problem's solution or problem-local supporting modules.
- A solution may repeat definitions, lemmas, or proof steps used for an earlier problem.
- If part of an earlier proof is needed, write that part again in the new problem's folder and
  namespace.

## Do not generalize prematurely

- Prove the current problem directly.
- Choose the proof of the current problem without considering what may be useful for any later
  problem.
- Do not steer problem `N` toward a construction, lemma, or proof pattern because it might help
  with problems `N + 1`, `N + 2`, or any other future problem.
- Do not extract a shared theorem merely because the current proof resembles an earlier proof.
- Do not refactor earlier solutions while working on the new problem.
- Do not create common problem-independent files at this stage.
- Similarities should remain visible in the separate proofs so that useful abstractions can emerge
  later from the accumulated formalizations.

## Use only the repository's geometry

- Treat the repository as the complete source of geometric knowledge.
- Do not use Mathlib, online geometry references, textbook theorems, or remembered external
  theorems as proof inputs.
- Existing top-level definitions and approved foundational axioms may be reused.
- Existing problem solutions may be inspected for proof ideas, but any reused problem-local
  argument must be written independently for the new problem.

## Preserve the foundational boundary

- Keep foundational definitions and axioms in the top-level `Euclid` files.
- Keep problem-specific constructions and lemmas in that problem's folder.
- Do not add or strengthen an axiom without explicit approval.
- If a proof cannot continue without a missing foundational principle, identify the exact gap and
  ask for approval before changing the foundation.
- Intrinsic nondegeneracy and configuration data required to state the original problem correctly
  are permitted.

## Completion requirements

A completed problem must:

- state and prove a final theorem in its main solution file;
- contain no `sorry`;
- contain no solution-local `axiom` or theorem-shaped substitute for a missing result;
- have no hypothesis that merely assumes the desired geometric conclusion;
- compile directly with `lake env lean` on its main solution file;
- compile its problem-local Lake target, when one exists;
- leave the full project build passing; and
- pass a source audit for accidental imports of other problem-local modules.
