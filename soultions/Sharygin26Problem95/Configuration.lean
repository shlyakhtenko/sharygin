import Sharygin26Problem95.Scalar

/-!
# Altitude data for Sharygin, PDF page 26, problem 95

The foot `D` lies on `AB`, so `AB = AD + DB`.  The right triangles `BCD` and `ACD`
supply the two displayed Pythagorean identities.  The given equality is `AD = BC`.
-/

namespace Soultions.Sharygin.Page26.Problem95.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def sevenTimes (x : S.Carrier) := S.add (S.add (fourTimes S x) (twice S x)) x

structure Data where
  sideAB : S.Carrier
  sideAC : S.Carrier
  sideBC : S.Carrier
  ad : S.Carrier
  db : S.Carrier
  altitude : S.Carrier
  rootSeven : S.Carrier
  side_ab_value : sideAB = threeTimes S S.one
  altitude_square : S.square altitude = threeTimes S S.one
  foot_between : sideAB = S.add ad db
  ad_eq_bc : ad = sideBC
  bcd_pythagorean :
    S.square sideBC = S.add (S.square db) (S.square altitude)
  acd_pythagorean :
    S.square sideAC = S.add (S.square ad) (S.square altitude)
  side_ab_ne_zero : sideAB ≠ S.zero
  twice_one_ne_zero : twice S S.one ≠ S.zero
  root_seven_square : S.square rootSeven = sevenTimes S S.one
  positive_sum : S.add sideAC rootSeven ≠ S.zero

end Soultions.Sharygin.Page26.Problem95.Configuration
