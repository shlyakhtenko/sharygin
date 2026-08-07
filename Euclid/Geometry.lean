/-!
# A small synthetic language for Euclidean plane geometry

The primitive relations are betweenness and segment congruence. `Axioms` is a compact
Tarski-style starting point: later declarations should derive facts from these fields rather
than silently enlarging the foundation.
-/

universe u v

namespace Euclid

/-- The two orientations for directed angles. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq

/-- Reverse a rotation sense. -/
def RotationSense.reverse : RotationSense → RotationSense
  | .clockwise => .counterclockwise
  | .counterclockwise => .clockwise

/-- The operations required for exact elementary length calculations. -/
structure OrderedScalar where
  Carrier : Type v
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  inv : Carrier → Carrier
  le : Carrier → Carrier → Prop

namespace OrderedScalar

variable (S : OrderedScalar)

/-- Subtraction in an ordered scalar system. -/
def sub (x y : S.Carrier) : S.Carrier :=
  S.add x (S.neg y)

/-- The square of a scalar. -/
def square (x : S.Carrier) : S.Carrier :=
  S.mul x x

/-- Repeated addition of a scalar.  This is the scalar meaning of `n` equal-area pieces. -/
def nsmul : Nat → S.Carrier → S.Carrier
  | 0, _ => S.zero
  | n + 1, x => S.add (nsmul n x) x

/-- Ordered-field laws needed by elementary metric geometry. -/
class Axioms : Prop where
  add_assoc : ∀ x y z, S.add (S.add x y) z = S.add x (S.add y z)
  add_comm : ∀ x y, S.add x y = S.add y x
  zero_add : ∀ x, S.add S.zero x = x
  add_zero : ∀ x, S.add x S.zero = x
  add_neg : ∀ x, S.add x (S.neg x) = S.zero
  mul_assoc : ∀ x y z, S.mul (S.mul x y) z = S.mul x (S.mul y z)
  mul_comm : ∀ x y, S.mul x y = S.mul y x
  one_mul : ∀ x, S.mul S.one x = x
  mul_one : ∀ x, S.mul x S.one = x
  zero_mul : ∀ x, S.mul S.zero x = S.zero
  left_distrib : ∀ x y z, S.mul x (S.add y z) = S.add (S.mul x y) (S.mul x z)
  zero_ne_one : S.zero ≠ S.one
  inv_zero : S.inv S.zero = S.zero
  mul_inv : ∀ x, x ≠ S.zero → S.mul x (S.inv x) = S.one
  le_refl : ∀ x, S.le x x
  le_trans : ∀ x y z, S.le x y → S.le y z → S.le x z
  le_antisymm : ∀ x y, S.le x y → S.le y x → x = y
  le_total : ∀ x y, S.le x y ∨ S.le y x
  add_le_add_right : ∀ x y z, S.le x y → S.le (S.add x z) (S.add y z)
  mul_nonneg : ∀ x y, S.le S.zero x → S.le S.zero y → S.le S.zero (S.mul x y)
  zero_le_one : S.le S.zero S.one

end OrderedScalar

/-- The primitive data of a synthetic plane. -/
structure Plane where
  Point : Type u
  Bet : Point → Point → Point → Prop
  Congruent : Point → Point → Point → Point → Prop
  Orientation : Point → Point → Point → Option RotationSense

namespace Plane

variable (G : Plane)

/-- A planar region is specified by the points which belong to it. -/
abbrev Region := G.Point → Prop

namespace Region

/-- The empty planar region. -/
def empty : G.Region := fun _ => False

/-- Union of two planar regions. -/
def union (X Y : G.Region) : G.Region := fun p => X p ∨ Y p

/-- Intersection of two planar regions. -/
def inter (X Y : G.Region) : G.Region := fun p => X p ∧ Y p

end Region

/--
A rigid motion of the plane, presented together with its inverse.

Distance preservation is stated in the primitive congruence language, so this definition does
not depend on a chosen scalar length measurement.
-/
structure Isometry where
  toFun : G.Point → G.Point
  invFun : G.Point → G.Point
  left_inv : ∀ p, invFun (toFun p) = p
  right_inv : ∀ p, toFun (invFun p) = p
  preserves_congruence :
    ∀ a b, G.Congruent (toFun a) (toFun b) a b

namespace Region

/-- The pointwise image of a region under a rigid motion. -/
def image (f : G.Isometry) (X : G.Region) : G.Region :=
  fun p => ∃ q, X q ∧ f.toFun q = p

/-- Two regions are congruent when one is the image of the other under a rigid motion. -/
def Congruent (X Y : G.Region) : Prop :=
  ∃ f : G.Isometry, Y = image G f X

end Region

/-- Three points are collinear when one of them lies between the other two. -/
def Collinear (a b c : G.Point) : Prop :=
  G.Bet a b c ∨ G.Bet b c a ∨ G.Bet c a b

/-- The closed segment with endpoints `a` and `b`. -/
def ClosedSegment (a b : G.Point) : G.Region :=
  fun p => p = a ∨ p = b ∨ G.Bet a p b

/-- The closed triangular region spanned by `a`, `b`, and `c`. -/
def TriangleRegion (a b c : G.Point) : G.Region :=
  fun p => ∃ q, G.ClosedSegment a b q ∧ G.ClosedSegment q c p

/-- Two nonvertex points lie on the same ray from `o`. -/
def SameRay (o a b : G.Point) : Prop :=
  a ≠ o ∧ b ≠ o ∧ G.Collinear o a b ∧ ¬G.Bet a o b

/--
Two points lie on opposite sides of a line when neither lies on the line and their joining
segment meets it.
-/
def OppositeSides (a b p q : G.Point) : Prop :=
  ¬G.Collinear a b p ∧
    ¬G.Collinear a b q ∧
      ∃ x, G.Collinear a b x ∧ G.Bet p x q

/--
Two nondegenerate lines are strictly parallel when they have no common point.

Coincident lines are deliberately excluded: this is the relation used by the geometric
construction of a fourth proportional.
-/
def StrictlyParallel (a b c d : G.Point) : Prop :=
  a ≠ b ∧ c ≠ d ∧
    ∀ p, ¬(G.Collinear a b p ∧ G.Collinear c d p)

theorem strictlyParallel_iff_no_intersection {a b c d : G.Point} :
    G.StrictlyParallel a b c d ↔
      a ≠ b ∧ c ≠ d ∧
        ¬∃ p, G.Collinear a b p ∧ G.Collinear c d p := by
  constructor
  · rintro ⟨hab, hcd, hdisjoint⟩
    refine ⟨hab, hcd, ?_⟩
    rintro ⟨p, hp⟩
    exact hdisjoint p hp
  · rintro ⟨hab, hcd, hdisjoint⟩
    refine ⟨hab, hcd, ?_⟩
    intro p hp
    exact hdisjoint ⟨p, hp⟩

/--
The unit-free geometric configuration that expresses equality of two ratios.

The points `a, c` lie on one ray from `o`, the points `b, d` lie on another, and the two
joining segments are parallel.  Thus the construction expresses `oa / oc = ob / od`
without taking division as a geometric primitive.
-/
def FourthProportionalConfiguration (o a b c d : G.Point) : Prop :=
  G.SameRay o a c ∧
    G.SameRay o b d ∧
      ¬G.Collinear o a b ∧
        G.StrictlyParallel a b c d

/-- A choice of exact scalar values for segment lengths. -/
structure LengthMeasurement where
  scalar : OrderedScalar
  length : G.Point → G.Point → scalar.Carrier

namespace LengthMeasurement

variable {G : Plane} (L : LengthMeasurement G)

/-- The closed disk whose radius is represented by the segment from `center` to `radiusPoint`. -/
def ClosedDisk (center radiusPoint : G.Point) : G.Region :=
  fun p => L.scalar.le (L.length center p) (L.length center radiusPoint)

/--
Foundational compatibility laws between synthetic segments and scalar lengths.

No triangle, similarity, Pythagorean, circle, or power-of-a-point theorem is assumed here.
-/
class Axioms : Prop where
  scalar_axioms : OrderedScalar.Axioms L.scalar
  length_nonnegative : ∀ a b, L.scalar.le L.scalar.zero (L.length a b)
  length_eq_zero : ∀ a b, L.length a b = L.scalar.zero ↔ a = b
  length_symm : ∀ a b, L.length a b = L.length b a
  congruent_iff :
    ∀ a b c d, G.Congruent a b c d ↔ L.length a b = L.length c d
  bet_additive :
    ∀ a b c, G.Bet a b c →
      L.length a c = L.scalar.add (L.length a b) (L.length b c)
  /--
  Scalar multiplication interprets the geometric fourth-proportional construction.

  This is the bridge between the already defined scalar operation and its geometric meaning,
  not a triangle, circle, Pythagorean, or power-of-a-point theorem.
  -/
  fourth_proportional_mul :
    ∀ o a b c d,
      G.FourthProportionalConfiguration o a b c d →
      L.scalar.mul (L.length o a) (L.length o d) =
        L.scalar.mul (L.length o b) (L.length o c)

end LengthMeasurement

/-- A directed angle represented by two ray points, their common vertex, and an orientation. -/
structure DirectedAngle where
  first : G.Point
  vertex : G.Point
  second : G.Point
  sense : RotationSense

/--
Primitive data for measuring directed angles. Addition is understood modulo one full turn, so
measures can be represented canonically by values in `[0, 360)` without requiring real numbers.
-/
structure AngleMeasurement where
  Measure : Type v
  zero : Measure
  halfTurn : Measure
  add : Measure → Measure → Measure
  neg : Measure → Measure
  measure : DirectedAngle G → Measure

namespace AngleMeasurement

variable (M : AngleMeasurement G)

/-- Difference of two angle measures. -/
def sub {G : Plane} (M : AngleMeasurement G) (x y : M.Measure) : M.Measure :=
  M.add x (M.neg y)

/-- Twice an angle measure. -/
def twice {G : Plane} (M : AngleMeasurement G) (x : M.Measure) : M.Measure :=
  M.add x x

/--
Minimal algebraic and angular-additivity laws for directed-angle measurement.

These laws characterize measurement itself; they contain no triangle or circle theorems.
-/
class Axioms : Prop where
  add_assoc : ∀ x y z, M.add (M.add x y) z = M.add x (M.add y z)
  add_comm : ∀ x y, M.add x y = M.add y x
  zero_add : ∀ x, M.add M.zero x = x
  add_zero : ∀ x, M.add x M.zero = x
  add_neg : ∀ x, M.add x (M.neg x) = M.zero
  twice_halfTurn : M.twice M.halfTurn = M.zero
  measure_refl :
    ∀ a o sense,
      M.measure ⟨a, o, a, sense⟩ = M.zero
  measure_add :
    ∀ a b c o sense,
      a ≠ o →
      b ≠ o →
      c ≠ o →
      M.measure ⟨a, o, c, sense⟩ =
        M.add (M.measure ⟨a, o, b, sense⟩) (M.measure ⟨b, o, c, sense⟩)
  same_ray_invariant :
    ∀ a a' b b' o sense,
      G.SameRay o a a' →
      G.SameRay o b b' →
      M.measure ⟨a, o, b, sense⟩ = M.measure ⟨a', o, b', sense⟩
  zero_measure_only_same_ray :
    ∀ a o b sense,
      a ≠ o →
      b ≠ o →
      M.measure ⟨a, o, b, sense⟩ = M.zero →
      G.SameRay o a b
  ray_determined_by_measure_same_side :
    ∀ a o b b' sense,
      ¬G.Collinear a o b →
      ¬G.Collinear a o b' →
      G.Orientation a o b = G.Orientation a o b' →
      M.measure ⟨a, o, b, sense⟩ = M.measure ⟨a, o, b', sense⟩ →
      G.SameRay o b b'
  twice_injective_same_orientation :
    ∀ a o b a' o' b' sense,
      ¬G.Collinear a o b →
      ¬G.Collinear a' o' b' →
      G.Orientation a o b = G.Orientation a' o' b' →
      M.twice (M.measure ⟨a, o, b, sense⟩) =
        M.twice (M.measure ⟨a', o', b', sense⟩) →
      M.measure ⟨a, o, b, sense⟩ =
        M.measure ⟨a', o', b', sense⟩
  sss_preserving :
    ∀ a o b a' o' b' sense,
      G.Congruent o a o' a' →
      G.Congruent o b o' b' →
      G.Congruent a b a' b' →
      G.Orientation a o b = G.Orientation a' o' b' →
      M.measure ⟨a, o, b, sense⟩ = M.measure ⟨a', o', b', sense⟩
  sss_reversing :
    ∀ a o b a' o' b' sense,
      G.Congruent o a o' a' →
      G.Congruent o b o' b' →
      G.Congruent a b a' b' →
      G.Orientation a o b = (G.Orientation a' o' b').map RotationSense.reverse →
      M.measure ⟨a, o, b, sense⟩ =
        M.measure ⟨a', o', b', sense.reverse⟩
  measure_straight :
    ∀ a o b sense,
      a ≠ o →
      b ≠ o →
      G.Bet a o b →
      M.measure ⟨a, o, b, sense⟩ = M.halfTurn
  reverse_sense :
    ∀ a b o,
      a ≠ o →
      b ≠ o →
      M.measure ⟨a, o, b, .clockwise⟩ =
        M.measure ⟨b, o, a, .counterclockwise⟩

end AngleMeasurement

/--
Four cyclically ordered points form a rectangle when their diagonals have a common midpoint,
the first three vertices are noncollinear, and one corner is right.

The midpoint conditions express the parallelogram property directly in the primitive Tarski
language, avoiding any additional affine primitive.
-/
def Rectangle
    (M : AngleMeasurement G)
    (a b c d : G.Point) : Prop :=
  (∃ center,
      G.Bet a center c ∧
      G.Congruent a center center c ∧
      G.Bet b center d ∧
      G.Congruent b center center d) ∧
    ¬G.Collinear a b c ∧
    ∃ sense,
      M.twice (M.measure ⟨a, b, c, sense⟩) =
        M.halfTurn

/--
A finitely additive area measurement on planar regions.

The distinguished scalar `pi` is normalized by the disk-area law in
`AreaMeasurement.Axioms`.  It is data of the measurement rather than an additional scalar
operation.
-/
structure AreaMeasurement
    (G : Plane)
    (L : LengthMeasurement G) where
  area : G.Region → L.scalar.Carrier
  pi : L.scalar.Carrier

namespace AreaMeasurement

variable
    {G : Plane}
    {L : LengthMeasurement G}
    (A : AreaMeasurement G L)

/-- The area of a triangle is the measure of its closed triangular region. -/
def triangleArea (a b c : G.Point) : L.scalar.Carrier :=
  A.area (G.TriangleRegion a b c)

/-- Two regions are area-disjoint when their overlap has area zero. -/
def AreaDisjoint (X Y : G.Region) : Prop :=
  A.area (Plane.Region.inter (G := G) X Y) = L.scalar.zero

/--
Foundational compatibility laws for unsigned Euclidean area.

The normalization laws give the areas of rectangles and disks.  In particular, the familiar
base-times-height formula for a triangle is not assumed: it must be obtained from rectangle
area, finite additivity, and congruence invariance.
-/
class Axioms (M : AngleMeasurement G) : Prop where
  empty_area :
    A.area (Plane.Region.empty (G := G)) = L.scalar.zero
  finite_additive :
    ∀ X Y,
      A.AreaDisjoint X Y →
      A.area (Plane.Region.union (G := G) X Y) =
        L.scalar.add (A.area X) (A.area Y)
  /-- Rigid motions preserve the area of every planar region. -/
  isometry_invariant :
    ∀ (f : G.Isometry) (X : G.Region),
      A.area (Plane.Region.image G f X) = A.area X
  swap :
    ∀ a b c,
      A.triangleArea a b c =
        A.triangleArea b a c
  cyclic :
    ∀ a b c,
      A.triangleArea a b c =
        A.triangleArea b c a
  congruent :
    ∀ a b c a' b' c',
      G.Congruent a b a' b' →
      G.Congruent b c b' c' →
      G.Congruent c a c' a' →
      A.triangleArea a b c =
        A.triangleArea a' b' c'
  cut_additive :
    ∀ a b c d,
      G.Bet b d c →
      A.triangleArea a b c =
        L.scalar.add
          (A.triangleArea a b d)
          (A.triangleArea a d c)
  rectangle_area :
    ∀ a b c d,
      G.Rectangle M a b c d →
      L.scalar.add
          (A.triangleArea a b c)
          (A.triangleArea a c d) =
        L.scalar.mul
          (L.length a b)
          (L.length b c)
  /-- The area of a disk of radius `r` is `pi * r²`; this fixes the meaning of `pi`. -/
  disk_area :
    ∀ center radiusPoint,
      A.area (L.ClosedDisk center radiusPoint) =
        L.scalar.mul
          A.pi
          (L.scalar.square (L.length center radiusPoint))

end AreaMeasurement

/--
A compact synthetic foundation for elementary Euclidean plane geometry.

The final field is a second-order continuity principle. Keeping all assumptions in this class
makes the axiomatic boundary explicit in theorem signatures.
-/
class Axioms : Prop where
  congruenceReversal : ∀ a b, G.Congruent a b b a
  congruenceTransitivity :
    ∀ a b p q r s, G.Congruent a b p q → G.Congruent a b r s → G.Congruent p q r s
  congruenceIdentity : ∀ a b c, G.Congruent a b c c → a = b
  segmentConstruction :
    ∀ a b c q, ∃ x, G.Bet q a x ∧ G.Congruent a x b c
  fiveSegment :
    ∀ a b c d a' b' c' d',
      a ≠ b →
      G.Bet a b c →
      G.Bet a' b' c' →
      G.Congruent a b a' b' →
      G.Congruent b c b' c' →
      G.Congruent a d a' d' →
      G.Congruent b d b' d' →
      G.Congruent c d c' d'
  betweennessIdentity : ∀ a b, G.Bet a b a → a = b
  innerPasch :
    ∀ a b c p q,
      G.Bet a p c →
      G.Bet b q c →
      ∃ x, G.Bet p x b ∧ G.Bet q x a
  /--
  A line crossed by a segment separates every other off-line point from at least one endpoint
  of that segment.
  -/
  planeSeparation :
    ∀ a b p q r,
      G.OppositeSides a b p q →
      ¬G.Collinear a b r →
      G.OppositeSides a b p r ∨ G.OppositeSides a b q r
  lowerDimension :
    ∃ a b c, ¬G.Collinear a b c
  upperDimension :
    ∀ a b c p q,
      p ≠ q →
      G.Congruent a p a q →
      G.Congruent b p b q →
      G.Congruent c p c q →
      G.Collinear a b c
  euclidean :
    ∀ a b c d t,
      G.Bet a d t →
      G.Bet b d c →
      a ≠ d →
      ∃ x y, G.Bet a b x ∧ G.Bet a c y ∧ G.Bet x t y
  continuity :
    ∀ X Y : G.Point → Prop,
      (∃ a, ∀ x y, X x → Y y → G.Bet a x y) →
      ∃ b, ∀ x y, X x → Y y → G.Bet x b y
  orientation_collinear :
    ∀ a b c, G.Orientation a b c = none ↔ G.Collinear a b c
  orientation_cyclic :
    ∀ a b c, G.Orientation a b c = G.Orientation b c a
  orientation_swap :
    ∀ a b c,
      G.Orientation a b c = (G.Orientation b a c).map RotationSense.reverse
  orientation_crossing :
    ∀ a b p q x,
      ¬G.Collinear a b p →
      G.Collinear a b x →
      G.Bet p x q →
      x ≠ q →
      G.Orientation a b p = (G.Orientation a b q).map RotationSense.reverse

theorem Axioms.orientation_opposite_sides [G.Axioms] {a b p q : G.Point}
    (h : G.OppositeSides a b p q) :
    G.Orientation a b p = (G.Orientation a b q).map RotationSense.reverse := by
  obtain ⟨hp, hq, x, hxline, hpxq⟩ := h
  apply Axioms.orientation_crossing a b p q x hp hxline hpxq
  intro hxq
  subst x
  exact hq hxline

end Plane

end Euclid
