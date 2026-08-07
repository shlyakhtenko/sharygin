# Euclid

A standalone Lean 4 project for synthetic elementary Euclidean geometry and the study of
similarities between formal proofs.

The project deliberately does not depend on Mathlib. Its primitive language and initial
axiomatic boundary are in `Euclid/Geometry.lean`.

`Euclid/Elementary.lean` adds globally shared textbook constructions such as midpoints, circles,
directed arcs, and tangents. It contains definitions only; geometric results about them must be
derived from the primitive foundation.

`Euclid/Geometry.lean` also provides an abstract directed-angle measurement with addition modulo
one full turn. Its foundational laws include same-ray invariance, invariance under SSS angle
congruence, and the fixed measure of a straight angle. It assumes no triangle or circle theorem.

For metric problems, `Euclid/Geometry.lean` provides an exact ordered scalar system and a segment
length measurement compatible with betweenness and segment congruence. Similarity, Pythagoras,
power of a point, and square roots are not axioms.

Build the library with:

```sh
lake build
```
