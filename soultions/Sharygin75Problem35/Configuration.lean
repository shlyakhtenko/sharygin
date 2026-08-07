import Sharygin75Problem35.Scalar

/-!
# Coordinate configuration for Sharygin, PDF page 75, problem 35

Use `A=(0,0)`, `B=(1,0)`, and `C=(0,1)`.  The point `E=(0,e)` lies on
`AC`.  Writing `N=(-t,e+t)` puts `EN ∥ BC`, and writing `M=(m,e)` puts
`EM ∥ AB`.  The remaining field is precisely the assertion that the
arbitrary line through `B` contains both `N` and `M`.
-/

namespace Soultions.Sharygin.Page75.Problem35.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

abbrev Point := S.Carrier × S.Carrier

def subPoint (p q : Point S) : Point S :=
  (S.sub p.1 q.1, S.sub p.2 q.2)

def determinant (p q : Point S) : S.Carrier :=
  S.sub (S.mul p.1 q.2) (S.mul p.2 q.1)

def parallelVectors (p q : Point S) : Prop :=
  determinant S p q = S.zero

structure Data where
  e : S.Carrier
  t : S.Carrier
  mCoordinate : S.Carrier
  b_n_m_collinear :
    determinant S
        (subPoint S
          (S.neg t, S.add e t)
          (S.one, S.zero))
        (subPoint S
          (mCoordinate, e)
          (S.one, S.zero)) =
      S.zero

def Data.a (_data : Data S) : Point S :=
  (S.zero, S.zero)

def Data.c (_data : Data S) : Point S :=
  (S.zero, S.one)

def Data.n (data : Data S) : Point S :=
  (S.neg data.t, S.add data.e data.t)

def Data.m (data : Data S) : Point S :=
  (data.mCoordinate, data.e)

def Conclusion (data : Data S) : Prop :=
  parallelVectors S
    (subPoint S data.n data.a)
    (subPoint S data.m data.c)

end Soultions.Sharygin.Page75.Problem35.Configuration
