# Sharygin, PDF page 12, problem 8

## Problem

Through a point `M` inside a circle of radius `R`, at distance `a` from its center, draw an
arbitrary chord `AB`.  Prove that `|MA| |MB|` is constant and equals `R^2 - a^2`.

## Proof represented in Lean

Construct the chord through `M` and the circle center.  Segment additivity on this radial chord,
followed by the difference-of-squares identity, gives the product of its two pieces as
`R^2 - OM^2`.

The intersecting-chords theorem, derived problem-locally from the angle and similarity machinery,
shows that the product of the two pieces of any other chord through `M` equals the radial product.
Therefore `MA * MB = R^2 - OM^2` for every chord.

## Formalization audit

The configuration records precisely an interior point and an ordered chord through it.  The
radial chord, its endpoints, and both product identities are derived.  The PDF extraction renders
the multiplication sign poorly, but the intended and formalized statement is the chord-product
identity, not a difference of lengths.  No desired metric equality occurs among the hypotheses.
