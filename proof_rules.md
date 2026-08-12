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
- define the geometric objects occurring in the source problem, rather than replacing them with
  unrelated scalar variables or a certificate that already contains the desired computation;
- be checked against the source statement for the correct hypotheses, conclusion, page, problem
  number, and interpretation of any diagram;
- contain no `sorry`;
- contain no solution-local `axiom` or theorem-shaped substitute for a missing result;
- have no hypothesis that merely assumes the desired geometric conclusion;
- have no configuration field that assumes a substantive intermediate theorem merely to make the
  final calculation go through; configuration fields may record the original givens, chosen
  auxiliary constructions, exact incidence or region decompositions, and explicit congruence or
  symmetry witnesses;
- include a `Solution.md` in the problem's supporting folder which:
  - restates the source problem in natural language;
  - gives the natural-language proof actually implemented by the Lean files;
  - identifies the geometric configuration data used by the final theorem;
  - explains how each nontrivial configuration field follows from the source givens or is an
    explicitly chosen auxiliary construction; and
  - records any remaining formalization caveat instead of presenting a partial certificate as a
    completed geometry proof;
- compile directly with `lake env lean` on its main solution file;
- compile its problem-local Lake target, when one exists;
- leave the full project build passing; and
- pass a source audit for accidental imports of other problem-local modules.

## Audit before declaring completion

For every new or revised problem, compare the PDF statement, `Configuration.lean`, and the final
theorem side by side.  In particular, check that:

- every hypothesis in Lean is either in the source problem or is justified construction data;
- the conclusion is the source conclusion, not only an algebraic consequence of an assumed
  geometric formula;
- named regions such as a polygon, sector, lens, covered part, or uncovered part are defined from
  points, segments, circles, and region operations;
- equal-area, proportionality, trigonometric, or metric formulas are proved unless they are among
  the approved top-level axioms;
- symmetry and finite-partition records contain actual regions and rigid motions, not precomputed
  scalar areas; and
- `Solution.md` matches the Lean proof after any refactor.
