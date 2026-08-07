import Sharygin16Problem33.Scalar

/-!
# Right-triangle directions for Sharygin, PDF page 16, problem 33

A pair `(run,rise)` represents the acute angle of a right triangle.  Composition is complex
multiplication; its direction is therefore the sum of the represented angles.
-/

namespace Soultions.Sharygin.Page16.Problem33.Directions

open Euclid

variable (S : OrderedScalar) [S.Axioms]

abbrev Direction := S.Carrier × S.Carrier

def two : S.Carrier := S.add S.one S.one

def three : S.Carrier := S.add (two S) S.one

def compose (p q : Direction S) : Direction S :=
  (S.sub (S.mul p.1 q.1) (S.mul p.2 q.2),
    S.add (S.mul p.1 q.2) (S.mul p.2 q.1))

/-- The three angles have runs `AB`, `AN = 2 AB`, and `AD = 3 AB`, and common rise `AB`. -/
structure Data where
  side : S.Carrier
  side_nonzero : side ≠ S.zero

def Data.amb (data : Data S) : Direction S :=
  (data.side, data.side)

def Data.anb (data : Data S) : Direction S :=
  (S.mul (two S) data.side, data.side)

def Data.adb (data : Data S) : Direction S :=
  (S.mul (three S) data.side, data.side)

def Data.sumDirection (data : Data S) : Direction S :=
  compose S (compose S data.amb data.anb) data.adb

/-- A vertical direction represents a right angle; the problem data separately exclude the
degenerate zero scale. -/
def IsRightDirection (p : Direction S) : Prop := p.1 = S.zero

end Soultions.Sharygin.Page16.Problem33.Directions
