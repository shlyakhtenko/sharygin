import Sharygin19Problem55.Scalar

/-!
# Area data for Sharygin, PDF page 19, problem 55

The two parallels cut off similar triangles at `B` with scale factors `5/6`
and `1/2`; their areas therefore have factors `25/36` and `1/4`.
-/

namespace Soultions.Sharygin.Page19.Problem55.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def nineTimes (x : S.Carrier) := threeTimes S (threeTimes S x)
def sixteenTimes (x : S.Carrier) := fourTimes S (fourTimes S x)
def twentyFiveTimes (x : S.Carrier) :=
  S.add (sixteenTimes S x) (nineTimes S x)
def thirtySixTimes (x : S.Carrier) := fourTimes S (nineTimes S x)

structure Data where
  totalArea : S.Carrier
  largeCutoffArea : S.Carrier
  smallCutoffArea : S.Carrier
  stripArea : S.Carrier
  large_similarity_area :
    thirtySixTimes S largeCutoffArea = twentyFiveTimes S totalArea
  small_similarity_area :
    fourTimes S smallCutoffArea = totalArea
  strip_partition :
    S.add stripArea smallCutoffArea = largeCutoffArea

end Soultions.Sharygin.Page19.Problem55.Configuration
