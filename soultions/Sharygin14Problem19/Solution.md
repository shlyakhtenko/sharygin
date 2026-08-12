# Sharygin, PDF page 14, problem 19

## Problem

Let `ABCD` be a convex quadrilateral satisfying

`AB + CD = AD + BC`.

Prove that one circle touches all four sides.

## Formalization audit

`ConvexQuadrilateral` contains exactly four vertices in strict cyclic order and the displayed
length equality.  The conclusion returns a circle and, for each closed side, a contact point
on that segment together with a tangent line equal to the side's supporting line.  No circle,
contact, angle bisector, perpendicular, or order condition occurs among the hypotheses.

The side-contact record names the tangent line by an arbitrary second point on the supporting
line.  This correctly permits a contact at either endpoint of a side; choosing one fixed
endpoint as the line's second point would accidentally exclude contact at that endpoint.

## Proof

Construct the internal angle bisectors at `A` and `B`.  Their supporting lines cannot be
parallel: the corresponding-angle laws, angle additivity, and the zero-angle ray-uniqueness
law would otherwise contradict the half-plane relations supplied by convexity.  Their
intersection `O` lies on the forward rays of both bisectors.

Drop the perpendicular from `O` to `AB` at `X`.  The local projection-order theorem proves
that `X` lies on the closed segment `AB`.  Let `omega` be the circle centered at `O` through
`X`.  Reflection symmetry in the two angle bisectors and the perpendicular-foot tangent
theorem construct contacts `Z` and `Y` on the forward rays `AD` and `BC`, respectively, and
prove that all three supporting lines are tangent to `omega`.

Now compare `CD` and `AD`.  Suppose first that `CD <= AD`.  Lay off `DE = DC` on `DA` and
`BF = BC` on `BA`.  Pitot's equality gives `AE = AF`.  Thus the three isosceles triangles at
`D`, `A`, and `B` show that `O` also lies on the internal angle bisector at `D`.  The
projection-order theorem then places `Z` on the finite side `AD`.

Reflecting the known tangent from `D` constructs the other tangent from `D`; the angle-bisector
and same-side uniqueness arguments put its contact `W` on the forward ray `DC`.  Equal tangent
lengths and Pitot's equality reduce to

`BY + CD = DW + BC`.

The ray orders show that `Y` and `W` are either both on their finite sides or both beyond
`C`; a mixed order would force both excess lengths to be zero and hence gives endpoint
contacts, which are already finite.  In the remaining beyond-beyond case, equal tangent
lengths give `CY = CW`.  The midpoint of `YW` shows that both the constructed internal
bisector point at `C` and `O` lie on the perpendicular bisector of `YW`.  Convexity selects
the forward internal bisector ray.  Applying the projection-order theorem at `C` contradicts
the assumption that `Y` lies beyond `C`.  Therefore both `Y` and `W` lie on `BC` and `CD`.

This supplies all four closed-side contacts.  If instead `AD <= CD`, read the same
quadrilateral in reverse cyclic order `C,B,A,D`.  It satisfies the first comparison, so the
proved branch applies; reordering its four side-contact witnesses gives the desired witnesses
for `A,B,C,D`.

## Formalization status

Complete.  The theorem `problem19` proves the exact `Statement` from the original source
hypotheses.  The solution contains no `sorry`, no added axiom, and no conditional auxiliary
configuration in its final theorem.
