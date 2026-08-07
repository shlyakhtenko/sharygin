import Sharygin16Problem32.Scalar

/-!
# Diagonal coordinates for Sharygin, PDF page 16, problem 32

If `u` and `v` are the two diagonal vectors, twice the two segments joining opposite-side
midpoints have vectors `u+v` and `v-u`.  The definitions below retain exactly those quantities.
-/

namespace Soultions.Sharygin.Page16.Problem32.Coordinates

open Euclid

variable (S : OrderedScalar) [S.Axioms]

abbrev Vector := S.Carrier × S.Carrier

def addVector (u v : Vector S) : Vector S :=
  (S.add u.1 v.1, S.add u.2 v.2)

def subVector (u v : Vector S) : Vector S :=
  (S.sub u.1 v.1, S.sub u.2 v.2)

def dot (u v : Vector S) : S.Carrier :=
  S.add (S.mul u.1 v.1) (S.mul u.2 v.2)

def normSquare (u : Vector S) : S.Carrier :=
  S.add (S.square u.1) (S.square u.2)

def cross (u v : Vector S) : S.Carrier :=
  S.sub (S.mul u.1 v.2) (S.mul u.2 v.1)

/-- Coordinate data for the two diagonals and their stated scalar lengths. -/
structure Data where
  firstDiagonal : Vector S
  secondDiagonal : Vector S
  a : S.Carrier
  b : S.Carrier
  a_nonnegative : S.le S.zero a
  b_nonnegative : S.le S.zero b
  first_length :
    normSquare S firstDiagonal = S.square a
  second_length :
    normSquare S secondDiagonal = S.square b
  /-- Congruence of the two opposite-side midpoint connectors, after doubling both vectors. -/
  midpoint_connectors_congruent :
    normSquare S (addVector S firstDiagonal secondDiagonal) =
      normSquare S (subVector S secondDiagonal firstDiagonal)
  /-- The convex cyclic orientation selects the nonnegative determinant. -/
  convex_orientation :
    S.le S.zero (cross S firstDiagonal secondDiagonal)

/-- Twice the quadrilateral area in diagonal coordinates. -/
def quadrilateralDoubleArea (data : Data S) : S.Carrier :=
  cross S data.firstDiagonal data.secondDiagonal

end Soultions.Sharygin.Page16.Problem32.Coordinates
