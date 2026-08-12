# Sharygin, PDF page 13, problem 15

## Problem

For a triangle with side `a` opposite angle `A` and circumradius `R`, prove

`S = a² sin B sin C / (2 sin A)`

and

`S = 2R² sin A sin B sin C`.

## Formalization audit

The triangle is nondegenerate and its three vertices lie on the stated circumcircle. Two altitude certificates are stored in the configuration, but their existence for every nondegenerate triangle is proved locally; they impose no special shape on the triangle.

Each sine is defined as opposite leg divided by hypotenuse in a right triangle cut out by an altitude. The problem-local `SineCompatibility` development proves that two right-triangle realizations of the same angle have the same value. Therefore, unlike the still-pending audit of problem 3, these formulas do not depend on an arbitrary choice of realization.

## Proof

The base-times-height formula yields

`2S = AB · h_c`.

Reading the three sines in the altitude triangles and cancelling nonzero side lengths gives the division-free first identity

`(2S) sin A = a² sin B sin C`.

For the second identity, the inscribed-angle development and sine-realization compatibility prove the extended sine law in the three needed forms:

`a = 2R sin A`, `b = 2R sin B`, and `c = 2R sin C`.

Substituting two of these identities into `2S = bc sin A` gives

`2S = (2R)² sin A sin B sin C`,

which is the division-free form of `S = 2R² sin A sin B sin C`.

