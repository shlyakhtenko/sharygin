import Sharygin17Problem45.Scalar

/-!
# Diagonal-area data for Sharygin, PDF page 17, problem 45

For bases `a,b`, all four small triangle areas share the same altitude/intersection scale `q`.
The base-adjacent triangles therefore have areas `a²q,b²q`, while either cross triangle has
area `abq`.
-/

namespace Soultions.Sharygin.Page17.Problem45.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) : S.Carrier := S.add x x
def fourTimes (x : S.Carrier) : S.Carrier := twice S (twice S x)

structure Data where
  firstBase : S.Carrier
  secondBase : S.Carrier
  commonAreaScale : S.Carrier

def Data.firstArea (data : Data S) : S.Carrier :=
  S.mul (S.square data.firstBase) data.commonAreaScale

def Data.secondArea (data : Data S) : S.Carrier :=
  S.mul (S.square data.secondBase) data.commonAreaScale

def Data.crossArea (data : Data S) : S.Carrier :=
  S.mul (S.mul data.firstBase data.secondBase) data.commonAreaScale

def Data.totalArea (data : Data S) : S.Carrier :=
  S.add (S.add data.firstArea data.secondArea) (twice S data.crossArea)

end Soultions.Sharygin.Page17.Problem45.Configuration
