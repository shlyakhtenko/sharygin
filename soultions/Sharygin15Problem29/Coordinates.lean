import Sharygin15Problem29.Scalar

/-!
# Oblique unit coordinates for Sharygin, page 15, problem 29

The coordinate axes point along the two adjacent sides of the parallelogram.  Because both
basis directions are unit vectors, the internal angle bisectors have the four equations used
below.  The Euclidean area scale of this oblique basis is `sinAlpha`.
-/

namespace Soultions.Sharygin.Page15.Problem29.Coordinates

open Euclid
open Soultions.Sharygin.Page15.Problem29.Scalar

variable (S : OrderedScalar) [S.Axioms]

abbrev Point := S.Carrier × S.Carrier

def two : S.Carrier := S.add S.one S.one

def half (x : S.Carrier) : S.Carrier :=
  S.mul (S.inv (two S)) x

theorem two_ne_zero : two S ≠ S.zero := by
  intro htwo
  change S.add S.one S.one = S.zero at htwo
  have hone_le_zero : S.le S.one S.zero := by
    have h := OrderedScalar.Axioms.add_le_add_right
      S.zero S.one S.one OrderedScalar.Axioms.zero_le_one
    rw [OrderedScalar.Axioms.zero_add, htwo] at h
    exact h
  have hzero_one := OrderedScalar.Axioms.le_antisymm
    S.zero S.one OrderedScalar.Axioms.zero_le_one hone_le_zero
  exact OrderedScalar.Axioms.zero_ne_one hzero_one

theorem half_add_half (x : S.Carrier) :
    S.add (half S x) (half S x) = x := by
  have htwo := two_ne_zero S
  calc
    S.add (half S x) (half S x) =
        S.mul (two S) (half S x) := by
      symm
      change
        S.mul (S.add S.one S.one) (half S x) =
          S.add (half S x) (half S x)
      rw [right_distrib S,
        OrderedScalar.Axioms.one_mul]
    _ = S.mul (two S) (S.mul (S.inv (two S)) x) := rfl
    _ = S.mul (S.mul (two S) (S.inv (two S))) x :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one x := by
      rw [OrderedScalar.Axioms.mul_inv (two S) htwo]
    _ = x := OrderedScalar.Axioms.one_mul x

def subPoint (p q : Point S) : Point S :=
  (S.sub p.1 q.1, S.sub p.2 q.2)

def determinant (p q : Point S) : S.Carrier :=
  S.sub (S.mul p.1 q.2) (S.mul p.2 q.1)

/-- Side lengths and the sine of their included angle. -/
structure Data where
  a : S.Carrier
  b : S.Carrier
  sinAlpha : S.Carrier

def Data.p (data : Data S) : Point S :=
  (half S data.a, half S data.a)

def Data.q (data : Data S) : Point S :=
  (S.sub data.a (half S data.b), half S data.b)

def Data.r (data : Data S) : Point S :=
  (half S data.a, S.sub data.b (half S data.a))

def Data.s (data : Data S) : Point S :=
  (half S data.b, half S data.b)

/-- The bisector at the origin `A`. -/
def OnABisector (p : Point S) : Prop := p.1 = p.2

/-- The bisector at `B = (a,0)`. -/
def OnBBisector (a : S.Carrier) (p : Point S) : Prop :=
  S.add p.1 p.2 = a

/-- The bisector at `C = (a,b)`. -/
def OnCBisector (a b : S.Carrier) (p : Point S) : Prop :=
  S.sub p.1 p.2 = S.sub a b

/-- The bisector at `D = (0,b)`. -/
def OnDBisector (b : S.Carrier) (p : Point S) : Prop :=
  S.add p.1 p.2 = b

/-- Twice the Euclidean area, computed from the two diagonals in the oblique basis. -/
def quadrilateralDoubleArea (data : Data S) : S.Carrier :=
  S.mul
    (determinant S
      (subPoint S data.q data.s)
      (subPoint S data.p data.r))
    data.sinAlpha

end Soultions.Sharygin.Page15.Problem29.Coordinates
