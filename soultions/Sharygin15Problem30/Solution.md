# Sharygin, PDF page 15, problem 30

## Statement

A circle is inscribed in a rhombus of altitude `h` and acute angle `α`. Of the two circles tangent to the incircle and to the two sides at an adjacent acute or obtuse vertex, the circle at the acute vertex is the larger one. Its radius `r` is

`r = h(1 - sin(α/2)) / (2(1 + sin(α/2)))`.

The Lean theorem states the formula without division:

`2(1 + sin(α/2))r = (1 - sin(α/2))h`.

This avoids adding division to the repository's ordered scalar interface.

## Proof

Let `I` be the center of the incircle and let its radius be `R`. Consider either one of the two corner circles. Write `V` for the relevant vertex, `J` for its center, `r` for its radius, and `s` for the sine of half the angle at `V`.

Both `I` and `J` lie on the angle bisector at `V`. Drop the perpendiculars from these centers to either side of the angle. The resulting right triangles give

`VI · s = R` and `VJ · s = r`.

The corner circle lies between `V` and the incircle. Since the two circles touch externally, their centers and contact point are collinear and

`VI = VJ + R + r`.

Multiply this equality by `s` and use the two right-triangle identities. This gives

`R = r + Rs + rs`,

hence

`(1 + s)r = (1 - s)R`.

The center `I` of the incircle is the center of the rhombus. This is proved from the four tangencies and the rhombus symmetries; it is not included as configuration data. Reflecting one contact point through the rhombus center then identifies it with the contact on the opposite side. Thus the altitude joining those opposite sides is a diameter of the incircle, so `h = 2R`. Substitution yields

`2(1 + s)r = (1 - s)h`.

It remains to determine which corner gives the larger radius. Let the consecutive vertices be `A, B, C, D`, with `∠DAB = α` acute, and let `O` be the intersection of the diagonals. The rhombus diagonals bisect the vertex angles and are perpendicular; these facts are derived locally from the rhombus congruences.

Choose a ray at `A` perpendicular to `AB` on the side containing `AD`. Since `AD` lies strictly between `AB` and that perpendicular ray and `AO` lies strictly between `AB` and `AD`, the angle `BAO` is smaller than the remaining angle between `AO` and the perpendicular ray. A directed-angle triangle-sum calculation in the right triangle `AOB` identifies that remaining angle with `ABO`. Therefore

`∠BAO < ∠ABO`.

The elementary side-angle comparison in triangle `AOB` now gives

`OB < OA`.

Because `I = O`, the obtuse vertex `B` is closer to the incircle center than the acute vertex `A`. From `VI · s = R`, the farther vertex has the smaller half-angle sine. Thus

`sin(α/2) ≤ sin((180° - α)/2)`.

Finally, the already-derived equation `(1+s)r = (1-s)R`, together with positivity, shows that a smaller value of `s` gives a larger value of `r`. Hence the acute-corner circle has radius at least that of the obtuse-corner circle, and its radius satisfies the displayed formula.

## Formalization boundary

The Lean configuration supplies the rhombus, its incircle with genuine side tangencies, and the two genuine corner circles with their side tangencies and external tangency to the incircle. It also records the oriented incidence expressing that `α` is acute. It does not assume the radius formula, any radius comparison, that the incircle center is the rhombus center, or that opposite contact points form a diameter; all of those conclusions used above are proved in this problem's folder.
