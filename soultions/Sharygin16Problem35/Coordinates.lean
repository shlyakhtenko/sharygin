import Sharygin16Problem35.Scalar

/-!
# Right-triangle coordinates for Sharygin, PDF page 16, problem 35

The right-angle vertex is the origin, and the two legs lie on perpendicular unit axes.
Reflection in the internal right-angle bisector is therefore coordinate interchange.
-/

namespace Soultions.Sharygin.Page16.Problem35.Coordinates

open Euclid
open Soultions.Sharygin.Page16.Problem35.Scalar

variable (S : OrderedScalar) [S.Axioms]

abbrev Point := S.Carrier × S.Carrier
abbrev Direction := S.Carrier × S.Carrier

def two : S.Carrier := S.add S.one S.one

def half (x : S.Carrier) : S.Carrier :=
  S.mul (S.inv (two S)) x

def addDirection (p q : Direction S) : Direction S :=
  (S.add p.1 q.1, S.add p.2 q.2)

def subPoint (p q : Point S) : Direction S :=
  (S.sub p.1 q.1, S.sub p.2 q.2)

def dot (p q : Direction S) : S.Carrier :=
  S.add (S.mul p.1 q.1) (S.mul p.2 q.2)

def Perpendicular (p q : Direction S) : Prop :=
  dot S p q = S.zero

/-- Reflection in the line whose unit-coordinate equation is `x = y`. -/
def reflectInRightBisector (p : Direction S) : Direction S :=
  (p.2, p.1)

/-- Two ray directions make equal angles with the internal right-angle bisector exactly when
reflection in that bisector exchanges their chosen positive representatives. -/
def RightBisectorBisects (p q : Direction S) : Prop :=
  reflectInRightBisector S p = q

/-- A nondegenerate right triangle with legs of lengths `b` and `c`. -/
structure Data where
  b : S.Carrier
  c : S.Carrier
  b_nonnegative : S.le S.zero b
  c_nonnegative : S.le S.zero c
  b_nonzero : b ≠ S.zero
  c_nonzero : c ≠ S.zero

def Data.a (_data : Data S) : Point S := (S.zero, S.zero)
def Data.bVertex (data : Data S) : Point S := (data.b, S.zero)
def Data.cVertex (data : Data S) : Point S := (S.zero, data.c)

/-- The proposed midpoint of the hypotenuse. -/
def Data.midpoint (data : Data S) : Point S :=
  (half S data.b, half S data.c)

/-- A representative of the median ray, obtained by doubling the midpoint vector. -/
def Data.medianDirection (data : Data S) : Direction S :=
  addDirection S data.midpoint data.midpoint

/-- The direction from `B` to `C`. -/
def Data.hypotenuseDirection (data : Data S) : Direction S :=
  subPoint S data.cVertex data.bVertex

/-- The altitude from `A` has this positive direction. -/
def Data.altitudeDirection (data : Data S) : Direction S :=
  (data.c, data.b)

def rightBisectorDirection : Direction S := (S.one, S.one)

end Soultions.Sharygin.Page16.Problem35.Coordinates
