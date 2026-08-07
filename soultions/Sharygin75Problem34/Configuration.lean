import Sharygin75Problem34.Scalar

/-!
# Coordinate configuration for Sharygin, PDF page 75, problem 34
-/

namespace Soultions.Sharygin.Page75.Problem34.Configuration

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
  u : S.Carrier
  v : S.Carrier
  t : S.Carrier
  q : S.Carrier
  bk_parallel_ad :
    S.mul t u = S.one
  am_parallel_bc :
    S.mul q
        (S.add (S.sub u S.one) v) =
      S.one

def Data.c (data : Data S) : Point S :=
  (data.u, data.v)

def Data.d (_data : Data S) : Point S :=
  (S.zero, S.one)

def Data.k (data : Data S) : Point S :=
  (S.mul data.t data.u, S.mul data.t data.v)

def Data.m (data : Data S) : Point S :=
  (S.mul data.q (S.sub data.u S.one),
    S.mul data.q data.v)

def Conclusion (data : Data S) : Prop :=
  parallelVectors S
    (subPoint S data.k data.m)
    (subPoint S data.d data.c)

end Soultions.Sharygin.Page75.Problem34.Configuration
