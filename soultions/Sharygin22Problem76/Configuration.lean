import Sharygin22Problem76.Scalar

/-!
# Trisected-chord data for Sharygin, PDF page 22, problem 76

The three intersection segments are equal thirds of the chords, hence form an equilateral
triangle of side `a/3`.  Coordinates based at its center give `81R²=21a²`.
-/

namespace Soultions.Sharygin.Page22.Problem76.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def sevenTimes (x : S.Carrier) := S.add (S.add (threeTimes S x) (threeTimes S x)) x
def nineTimes (x : S.Carrier) := threeTimes S (threeTimes S x)
def twentyOneTimes (x : S.Carrier) := threeTimes S (sevenTimes S x)

structure Data where
  chord : S.Carrier
  radius : S.Carrier
  rootTwentyOne : S.Carrier
  root_square : S.square rootTwentyOne = twentyOneTimes S S.one
  radius_square :
    S.square (nineTimes S radius) = twentyOneTimes S (S.square chord)
  geometric_root :
    S.add (nineTimes S radius) (S.mul rootTwentyOne chord) ≠ S.zero

end Soultions.Sharygin.Page22.Problem76.Configuration
