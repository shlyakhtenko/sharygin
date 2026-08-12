import Sharygin19Problem51.Partitions
import Sharygin19Problem51.Pythagorean
import Sharygin19Problem51.TriangleAltitudeArea

/-!
# Geometric configuration for Sharygin, PDF page 19, problem 51

The fields below describe the regular hexagon, the relevant pieces of its two representative
vertex disks, and explicit rigid-motion partitions.  They contain no asserted area formula.
-/

namespace Soultions.Sharygin.Page19.Problem51.Configuration

open Euclid Plane
open Soultions.Sharygin.Page19.Problem51.Partitions
open Soultions.Sharygin.Page19.Problem51.TriangleAltitudeArea
open Soultions.Sharygin.Page19.Problem51.Similarity

variable {G : Plane} {L : LengthMeasurement G}

def difference (X Y : G.Region) : G.Region := fun p => X p ∧ ¬Y p

def cell (o a b : G.Point) : G.Region := G.TriangleRegion o a b
def leftSector (L : LengthMeasurement G) (o a b radiusPoint : G.Point) : G.Region :=
  Plane.Region.inter (G := G) (cell o a b) (L.ClosedDisk a radiusPoint)
def rightSector (L : LengthMeasurement G) (o a b radiusPoint : G.Point) : G.Region :=
  Plane.Region.inter (G := G) (cell o a b) (L.ClosedDisk b radiusPoint)
def overlap (L : LengthMeasurement G) (o a b ra rb : G.Point) : G.Region :=
  Plane.Region.inter (G := G) (leftSector L o a b ra) (L.ClosedDisk b rb)
def localUncovered (L : LengthMeasurement G) (o a b ra rb : G.Point) : G.Region :=
  difference (cell o a b)
    (Plane.Region.union (G := G) (L.ClosedDisk a ra) (L.ClosedDisk b rb))

def hexagonRegion (o v0 v1 v2 v3 v4 v5 : G.Point) : G.Region :=
  U6 (cell o v0 v1) (cell o v1 v2) (cell o v2 v3)
    (cell o v3 v4) (cell o v4 v5) (cell o v5 v0)

def sixDisks (L : LengthMeasurement G)
    (v0 v1 v2 v3 v4 v5 r0 r1 r2 r3 r4 r5 : G.Point) : G.Region :=
  U6 (L.ClosedDisk v0 r0) (L.ClosedDisk v1 r1) (L.ClosedDisk v2 r2)
    (L.ClosedDisk v3 r3) (L.ClosedDisk v4 r4) (L.ClosedDisk v5 r5)

def uncoveredRegion (L : LengthMeasurement G)
    (o v0 v1 v2 v3 v4 v5 r0 r1 r2 r3 r4 r5 : G.Point) : G.Region :=
  difference (hexagonRegion o v0 v1 v2 v3 v4 v5)
    (sixDisks L v0 v1 v2 v3 v4 v5 r0 r1 r2 r3 r4 r5)

/-- The exact data needed by the problem-local Pythagorean proof for a right triangle. -/
structure RightTriangleCertificate
    (M : AngleMeasurement G) (a b c : G.Point) where
  altitudeFoot : G.Point
  noncollinear : ¬G.Collinear a b c
  foot_between : G.Bet a altitudeFoot c
  a_ne_foot : a ≠ altitudeFoot
  foot_ne_c : altitudeFoot ≠ c
  rightA : SameAngle G a b c b altitudeFoot a
  rightA_orientation :
    G.Orientation a b c = G.Orientation b altitudeFoot a
  rightC : SameAngle G c b a b altitudeFoot c
  rightC_orientation :
    G.Orientation c b a = G.Orientation b altitudeFoot c

/-- Complete geometric data for one representative cell of the regular hexagon. -/
structure Data
    (M : AngleMeasurement G) (A : AreaMeasurement G L) where
  center : G.Point
  v0 : G.Point
  v1 : G.Point
  v2 : G.Point
  v3 : G.Point
  v4 : G.Point
  v5 : G.Point
  radiusPoint0 : G.Point
  radiusPoint1 : G.Point
  radiusPoint2 : G.Point
  radiusPoint3 : G.Point
  radiusPoint4 : G.Point
  radiusPoint5 : G.Point
  rootThree : L.scalar.Carrier
  rootThree_nonnegative : L.scalar.le L.scalar.zero rootThree
  root_three_square :
    L.scalar.square rootThree = L.scalar.nsmul 3 L.scalar.one

  /- The altitude of the representative equilateral center triangle. -/
  cellAltitude : InteriorAltitude G M v0 v1 center
  center_v0_is_side : G.Congruent center v0 v0 v1
  center_v1_is_side : G.Congruent center v1 v0 v1
  cell_foot_midpoint : G.Midpoint v0 cellAltitude.foot v1
  cellRightTriangle :
    RightTriangleCertificate M center cellAltitude.foot v0

  /- The prescribed radius is `side / sqrt 2`, in division-free form. -/
  radius0_square :
    L.scalar.nsmul 2 (L.scalar.square (L.length v0 radiusPoint0)) =
      L.scalar.square (L.length v0 v1)
  radius1_square :
    L.scalar.nsmul 2 (L.scalar.square (L.length v1 radiusPoint1)) =
      L.scalar.square (L.length v0 v1)
  radius2_square :
    L.scalar.nsmul 2 (L.scalar.square (L.length v2 radiusPoint2)) =
      L.scalar.square (L.length v0 v1)
  radius3_square :
    L.scalar.nsmul 2 (L.scalar.square (L.length v3 radiusPoint3)) =
      L.scalar.square (L.length v0 v1)
  radius4_square :
    L.scalar.nsmul 2 (L.scalar.square (L.length v4 radiusPoint4)) =
      L.scalar.square (L.length v0 v1)
  radius5_square :
    L.scalar.nsmul 2 (L.scalar.square (L.length v5 radiusPoint5)) =
      L.scalar.square (L.length v0 v1)

  /- Six congruent center triangles, and the corresponding uncovered pieces. -/
  hexagonCells : SixPartition A (hexagonRegion center v0 v1 v2 v3 v4 v5)
  representative_cell : hexagonCells.x0 = cell center v0 v1
  uncoveredCells : SixPartition A
    (uncoveredRegion L center v0 v1 v2 v3 v4 v5
      radiusPoint0 radiusPoint1 radiusPoint2 radiusPoint3 radiusPoint4 radiusPoint5)
  representative_uncovered :
    uncoveredCells.x0 =
      localUncovered L center v0 v1 radiusPoint0 radiusPoint1

  /- The 60-degree pieces at the two endpoints of the representative cell. -/
  disk0Six : SixPartition A (L.ClosedDisk v0 radiusPoint0)
  disk0_sector :
    disk0Six.x0 = leftSector L center v0 v1 radiusPoint0
  disk1Six : SixPartition A (L.ClosedDisk v1 radiusPoint1)
  disk1_sector :
    disk1Six.x0 = rightSector L center v0 v1 radiusPoint1

  /- A circle-intersection point and the two 45-degree sectors forming the half-lens. -/
  midpoint : G.Point
  intersectionPoint : G.Point
  midpoint_v0_v1 : G.Midpoint v0 midpoint v1
  intersection_on_circle0 :
    G.Congruent v0 intersectionPoint v0 radiusPoint0
  lensRightTriangle :
    RightTriangleCertificate M v0 midpoint intersectionPoint
  leftSense : RotationSense
  rightSense : RotationSense
  left_right_angle :
    M.twice (M.measure ⟨v0, midpoint, intersectionPoint, leftSense⟩) = M.halfTurn
  right_right_angle :
    M.twice (M.measure ⟨v1, midpoint, intersectionPoint, rightSense⟩) = M.halfTurn
  left_noncollinear : ¬G.Collinear v0 midpoint intersectionPoint
  right_noncollinear : ¬G.Collinear v1 midpoint intersectionPoint

  sector45Left : G.Region
  sector45Right : G.Region
  disk0Eight : EightPartition A (L.ClosedDisk v0 radiusPoint0)
  disk0_sector45 : disk0Eight.x0 = sector45Left
  disk1Eight : EightPartition A (L.ClosedDisk v1 radiusPoint1)
  disk1_sector45 : disk1Eight.x0 = sector45Right
  segmentLeft : G.Region
  segmentRight : G.Region
  sector45Left_cut :
    sector45Left = Plane.Region.union (G := G)
      (G.TriangleRegion v0 midpoint intersectionPoint) segmentLeft
  sector45Left_disjoint :
    A.AreaDisjoint (G.TriangleRegion v0 midpoint intersectionPoint) segmentLeft
  sector45Right_cut :
    sector45Right = Plane.Region.union (G := G)
      (G.TriangleRegion v1 midpoint intersectionPoint) segmentRight
  sector45Right_disjoint :
    A.AreaDisjoint (G.TriangleRegion v1 midpoint intersectionPoint) segmentRight
  overlap_cut :
    overlap L center v0 v1 radiusPoint0 radiusPoint1 =
      Plane.Region.union (G := G) segmentLeft segmentRight
  overlap_disjoint : A.AreaDisjoint segmentLeft segmentRight

end Soultions.Sharygin.Page19.Problem51.Configuration
