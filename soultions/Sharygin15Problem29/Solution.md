# Sharygin, PDF page 15, problem 29

## Problem

Find the area of the quadrilateral bounded by the angle bisectors of a
parallelogram whose adjacent side lengths are \(a,b\) and whose included
angle is \(\alpha\).

## Answer

The area is

\[
  \frac{(a-b)^2\sin\alpha}{2}.
\]

The square makes the formula independent of which adjacent side is called
\(a\) and which is called \(b\).

## Natural-language proof

Use oblique coordinates with origin at one vertex of the parallelogram and
unit basis vectors \(u,v\) directed along its adjacent sides. The vertices
then have coordinates

\[
  A=(0,0),\quad B=(a,0),\quad C=(a,b),\quad D=(0,b).
\]

Because \(u,v\) are unit vectors, an internal angle bisector consists of
points whose two oblique coordinates have the appropriate equal signed
distances from the adjacent side lines. Thus the four internal bisectors
have equations

\[
\begin{aligned}
 A &: x=y,\\
 B &: x+y=a,\\
 C &: x-y=a-b,\\
 D &: x+y=b.
\end{aligned}
\]

Let consecutive intersections of these four lines be \(P,Q,R,S\). Solving
the pairs of equations gives

\[
\begin{aligned}
P&=(a/2,a/2),\\
Q&=(a-b/2,b/2),\\
R&=(a/2,b-a/2),\\
S&=(b/2,b/2).
\end{aligned}
\]

Therefore the two diagonals of the bounded quadrilateral have vectors

\[
  Q-S=(a-b)u,
  \qquad
  P-R=(a-b)v.
\]

The diagonals consequently have equal length \(|a-b|\), and the angle
between them is \(\alpha\). The area of a quadrilateral whose diagonals
bisect one another is half the magnitude of their cross product. Hence

\[
  [PQRS]
    =\frac12 |a-b|^2\sin\alpha
    =\frac{(a-b)^2\sin\alpha}{2}.
\]

## Current formalization audit: incomplete

The existing `Coordinates.lean` and `Solution.lean` correctly verify the
scalar algebra after the four oblique-coordinate equations have been
written down. In particular, they calculate the four pairwise intersections,
the two diagonal coordinate differences, and the final determinant identity.

They do **not yet constitute a formalization of the geometry problem**:

- `Coordinates.Point` is merely a pair of ordered scalars, not a point of a
  repository `Plane`.
- `Data.sinAlpha` is an arbitrary scalar and is not connected to an actual
  angle of an actual parallelogram.
- `OnABisector`, `OnBBisector`, and the other incidence predicates are
  defined directly by the desired coordinate equations; the Lean
  development does not prove that geometric angle bisectors have those
  equations.
- `quadrilateralDoubleArea` is defined to be the determinant expression. It
  is not the value of an `AreaMeasurement` on the actual region bounded by
  the four bisectors.

Thus the present theorem proves only the algebraic coordinate calculation,
not the source statement. Completing the problem requires a problem-local
geometric layer that:

1. starts with an actual parallelogram in a `Plane` and four actual internal
   angle-bisector lines;
2. derives the locations and diagonal lengths of their four intersections;
3. defines the bounded quadrilateral as an actual planar region; and
4. derives its area, including the diagonal-area or equivalent dissection
   argument, from the approved finite-additive area axioms.

No new foundational axiom has yet been shown necessary; these are substantial
derived theorems that remain to be implemented locally. Until those bridges
are supplied, problem 29 must not be counted as a completed formalization.
