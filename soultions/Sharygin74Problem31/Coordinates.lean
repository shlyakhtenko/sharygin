import Sharygin74Problem31.Scalar

/-!
# Barycentric coordinates for Sharygin, PDF page 74, problem 31

The reference triangle is represented by the affine coordinates
`A = (0,0)`, `B = (1,0)`, `C = (0,1)`.  A parameter and its complementary
parameter describe the two points symmetric about a side midpoint.
-/

namespace Soultions.Sharygin.Page74.Problem31.Coordinates

open Euclid
open Soultions.Sharygin.Page74.Problem31.Scalar

variable (S : OrderedScalar) [S.Axioms]

abbrev Point := S.Carrier × S.Carrier

def addPoint (p q : Point S) : Point S :=
  (S.add p.1 q.1, S.add p.2 q.2)

def scalePoint (x : S.Carrier) (p : Point S) : Point S :=
  (S.mul x p.1, S.mul x p.2)

def centroid (p q r : Point S) : Point S :=
  let three := S.add (S.add S.one S.one) S.one
  scalePoint S (S.inv three) (addPoint S (addPoint S p q) r)

def midpointEquation (p m q : Point S) : Prop :=
  addPoint S p q = addPoint S m m

def orientedDoubleArea (p q r : Point S) : S.Carrier :=
  S.sub
    (S.mul (S.sub q.1 p.1) (S.sub r.2 p.2))
    (S.mul (S.sub q.2 p.2) (S.sub r.1 p.1))

/-- The six points of the problem in barycentric coordinates. -/
structure Configuration where
  t : S.Carrier
  u : S.Carrier
  v : S.Carrier

def Configuration.a₁ (c : Configuration S) : Point S :=
  (S.sub S.one c.t, c.t)

def Configuration.a₂ (c : Configuration S) : Point S :=
  (c.t, S.sub S.one c.t)

def Configuration.b₁ (c : Configuration S) : Point S :=
  (S.zero, S.sub S.one c.u)

def Configuration.b₂ (c : Configuration S) : Point S :=
  (S.zero, c.u)

def Configuration.c₁ (c : Configuration S) : Point S :=
  (c.v, S.zero)

def Configuration.c₂ (c : Configuration S) : Point S :=
  (S.sub S.one c.v, S.zero)

def referenceA : Point S := (S.zero, S.zero)
def referenceB : Point S := (S.one, S.zero)
def referenceC : Point S := (S.zero, S.one)

end Soultions.Sharygin.Page74.Problem31.Coordinates
