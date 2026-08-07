import Euclid

/-!
# Area calculation for Sharygin, PDF page 14, problem 22

This file performs only the problem's twelve-sector calculation.  The sectors and their rigid
motions are recorded explicitly so that no general finite-family abstraction is introduced in
advance of later proofs.
-/

namespace Soultions.Sharygin.Page14.Problem22.Area

open Euclid Plane

variable {G : Plane} {L : LengthMeasurement G}

private theorem add_left_comm
    (S : OrderedScalar) [S.Axioms]
    (x y z : S.Carrier) :
    S.add x (S.add y z) = S.add y (S.add x z) := by
  rw [← OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm x y,
    OrderedScalar.Axioms.add_assoc]

private theorem twelve_halves_are_six_wholes
    (S : OrderedScalar) [S.Axioms]
    (x : S.Carrier) :
    S.nsmul 12 x = S.nsmul 6 (S.add x x) := by
  simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.add_comm, add_left_comm S]

def U2 (s0 s1 : G.Region) : G.Region := Plane.Region.union (G := G) s0 s1
def U3 (s0 s1 s2 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U2 s0 s1) s2
def U4 (s0 s1 s2 s3 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U3 s0 s1 s2) s3
def U5 (s0 s1 s2 s3 s4 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U4 s0 s1 s2 s3) s4
def U6 (s0 s1 s2 s3 s4 s5 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U5 s0 s1 s2 s3 s4) s5
def U7 (s0 s1 s2 s3 s4 s5 s6 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U6 s0 s1 s2 s3 s4 s5) s6
def U8 (s0 s1 s2 s3 s4 s5 s6 s7 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U7 s0 s1 s2 s3 s4 s5 s6) s7
def U9 (s0 s1 s2 s3 s4 s5 s6 s7 s8 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U8 s0 s1 s2 s3 s4 s5 s6 s7) s8
def U10 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U9 s0 s1 s2 s3 s4 s5 s6 s7 s8) s9
def U11 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) s10
def U12 (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U11 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) s11

/-- The twelve sectors used in this problem, including their exact disk partition data. -/
structure TwelveSectorPartition
    (A : AreaMeasurement G L) (center radiusPoint : G.Point) where
  s0 : G.Region
  s1 : G.Region
  s2 : G.Region
  s3 : G.Region
  s4 : G.Region
  s5 : G.Region
  s6 : G.Region
  s7 : G.Region
  s8 : G.Region
  s9 : G.Region
  s10 : G.Region
  s11 : G.Region
  congruent01 : Plane.Region.Congruent (G := G) s0 s1
  congruent02 : Plane.Region.Congruent (G := G) s0 s2
  congruent03 : Plane.Region.Congruent (G := G) s0 s3
  congruent04 : Plane.Region.Congruent (G := G) s0 s4
  congruent05 : Plane.Region.Congruent (G := G) s0 s5
  congruent06 : Plane.Region.Congruent (G := G) s0 s6
  congruent07 : Plane.Region.Congruent (G := G) s0 s7
  congruent08 : Plane.Region.Congruent (G := G) s0 s8
  congruent09 : Plane.Region.Congruent (G := G) s0 s9
  congruent010 : Plane.Region.Congruent (G := G) s0 s10
  congruent011 : Plane.Region.Congruent (G := G) s0 s11
  disjoint01 : A.AreaDisjoint s0 s1
  disjoint012 : A.AreaDisjoint (U2 s0 s1) s2
  disjoint0123 : A.AreaDisjoint (U3 s0 s1 s2) s3
  disjoint01234 : A.AreaDisjoint (U4 s0 s1 s2 s3) s4
  disjoint012345 : A.AreaDisjoint (U5 s0 s1 s2 s3 s4) s5
  disjoint0123456 : A.AreaDisjoint (U6 s0 s1 s2 s3 s4 s5) s6
  disjoint01234567 : A.AreaDisjoint (U7 s0 s1 s2 s3 s4 s5 s6) s7
  disjoint012345678 : A.AreaDisjoint (U8 s0 s1 s2 s3 s4 s5 s6 s7) s8
  disjoint0123456789 : A.AreaDisjoint (U9 s0 s1 s2 s3 s4 s5 s6 s7 s8) s9
  disjoint012345678910 : A.AreaDisjoint (U10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) s10
  disjoint01234567891011 :
    A.AreaDisjoint (U11 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) s11
  disk_partition :
    U12 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 = L.ClosedDisk center radiusPoint

theorem area_eq_of_congruent
    (M : AngleMeasurement G)
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms A M]
    {X Y : G.Region}
    (h : Plane.Region.Congruent (G := G) X Y) :
    A.area X = A.area Y := by
  obtain ⟨f, rfl⟩ := h
  exact (AreaMeasurement.Axioms.isometry_invariant M f X).symm

/-- A disk partitioned into twelve congruent sectors has twelve times one sector's area. -/
theorem disk_area_eq_twelve_sector_areas
    (M : AngleMeasurement G)
    (A : AreaMeasurement G L)
    [L.Axioms]
    [AreaMeasurement.Axioms A M]
    {center radiusPoint : G.Point}
    (partition : TwelveSectorPartition A center radiusPoint) :
    A.area (L.ClosedDisk center radiusPoint) =
      L.scalar.nsmul 12 (A.area partition.s0) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  have h1 : A.area partition.s0 = A.area partition.s1 :=
    area_eq_of_congruent M A partition.congruent01
  have h2 : A.area partition.s0 = A.area partition.s2 :=
    area_eq_of_congruent M A partition.congruent02
  have h3 : A.area partition.s0 = A.area partition.s3 :=
    area_eq_of_congruent M A partition.congruent03
  have h4 : A.area partition.s0 = A.area partition.s4 :=
    area_eq_of_congruent M A partition.congruent04
  have h5 : A.area partition.s0 = A.area partition.s5 :=
    area_eq_of_congruent M A partition.congruent05
  have h6 : A.area partition.s0 = A.area partition.s6 :=
    area_eq_of_congruent M A partition.congruent06
  have h7 : A.area partition.s0 = A.area partition.s7 :=
    area_eq_of_congruent M A partition.congruent07
  have h8 : A.area partition.s0 = A.area partition.s8 :=
    area_eq_of_congruent M A partition.congruent08
  have h9 : A.area partition.s0 = A.area partition.s9 :=
    area_eq_of_congruent M A partition.congruent09
  have h10 : A.area partition.s0 = A.area partition.s10 :=
    area_eq_of_congruent M A partition.congruent010
  have h11 : A.area partition.s0 = A.area partition.s11 :=
    area_eq_of_congruent M A partition.congruent011
  have hu2 :
      A.area (U2 partition.s0 partition.s1) =
        L.scalar.nsmul 2 (A.area partition.s0) := by
    rw [U2, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint01, ← h1]
    change L.scalar.add (A.area partition.s0) (A.area partition.s0) =
      L.scalar.add (L.scalar.add L.scalar.zero (A.area partition.s0)) (A.area partition.s0)
    rw [OrderedScalar.Axioms.zero_add (S := L.scalar)]
  have hu3 :
      A.area (U3 partition.s0 partition.s1 partition.s2) =
        L.scalar.nsmul 3 (A.area partition.s0) := by
    rw [U3, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint012, hu2, ← h2]
    unfold OrderedScalar.nsmul
    rfl
  have hu4 :
      A.area (U4 partition.s0 partition.s1 partition.s2 partition.s3) =
        L.scalar.nsmul 4 (A.area partition.s0) := by
    rw [U4, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint0123, hu3, ← h3]
    unfold OrderedScalar.nsmul
    rfl
  have hu5 :
      A.area (U5 partition.s0 partition.s1 partition.s2 partition.s3 partition.s4) =
        L.scalar.nsmul 5 (A.area partition.s0) := by
    rw [U5, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint01234, hu4, ← h4]
    unfold OrderedScalar.nsmul
    rfl
  have hu6 :
      A.area (U6 partition.s0 partition.s1 partition.s2 partition.s3 partition.s4
        partition.s5) = L.scalar.nsmul 6 (A.area partition.s0) := by
    rw [U6, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint012345, hu5, ← h5]
    unfold OrderedScalar.nsmul
    rfl
  have hu7 :
      A.area (U7 partition.s0 partition.s1 partition.s2 partition.s3 partition.s4
        partition.s5 partition.s6) = L.scalar.nsmul 7 (A.area partition.s0) := by
    rw [U7, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint0123456, hu6, ← h6]
    unfold OrderedScalar.nsmul
    rfl
  have hu8 :
      A.area (U8 partition.s0 partition.s1 partition.s2 partition.s3 partition.s4
        partition.s5 partition.s6 partition.s7) =
        L.scalar.nsmul 8 (A.area partition.s0) := by
    rw [U8, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint01234567, hu7, ← h7]
    unfold OrderedScalar.nsmul
    rfl
  have hu9 :
      A.area (U9 partition.s0 partition.s1 partition.s2 partition.s3 partition.s4
        partition.s5 partition.s6 partition.s7 partition.s8) =
        L.scalar.nsmul 9 (A.area partition.s0) := by
    rw [U9, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint012345678, hu8, ← h8]
    unfold OrderedScalar.nsmul
    rfl
  have hu10 :
      A.area (U10 partition.s0 partition.s1 partition.s2 partition.s3 partition.s4
        partition.s5 partition.s6 partition.s7 partition.s8 partition.s9) =
        L.scalar.nsmul 10 (A.area partition.s0) := by
    rw [U10, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint0123456789,
      hu9, ← h9]
    unfold OrderedScalar.nsmul
    rfl
  have hu11 :
      A.area (U11 partition.s0 partition.s1 partition.s2 partition.s3 partition.s4
        partition.s5 partition.s6 partition.s7 partition.s8 partition.s9 partition.s10) =
        L.scalar.nsmul 11 (A.area partition.s0) := by
    rw [U11, AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint012345678910,
      hu10, ← h10]
    unfold OrderedScalar.nsmul
    rfl
  calc
    A.area (L.ClosedDisk center radiusPoint) =
        A.area (U12 partition.s0 partition.s1 partition.s2 partition.s3 partition.s4
          partition.s5 partition.s6 partition.s7 partition.s8 partition.s9 partition.s10
          partition.s11) := congrArg A.area partition.disk_partition.symm
    _ = L.scalar.add
          (A.area (U11 partition.s0 partition.s1 partition.s2 partition.s3 partition.s4
            partition.s5 partition.s6 partition.s7 partition.s8 partition.s9 partition.s10))
          (A.area partition.s11) :=
      AreaMeasurement.Axioms.finite_additive M _ _ partition.disjoint01234567891011
    _ = L.scalar.nsmul 12 (A.area partition.s0) := by
      rw [hu11, ← h11]
      unfold OrderedScalar.nsmul
      rfl

/-- If the selected sector is half of a triangle, the full disk has six triangle areas. -/
theorem disk_area_eq_six_triangle_areas
    (M : AngleMeasurement G)
    (A : AreaMeasurement G L)
    [L.Axioms]
    [AreaMeasurement.Axioms A M]
    {center radiusPoint a b c : G.Point}
    (partition : TwelveSectorPartition A center radiusPoint)
    (sector_is_half :
      L.scalar.add (A.area partition.s0) (A.area partition.s0) =
        A.triangleArea a b c) :
    A.area (L.ClosedDisk center radiusPoint) =
      L.scalar.nsmul 6 (A.triangleArea a b c) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  calc
    A.area (L.ClosedDisk center radiusPoint) =
        L.scalar.nsmul 12 (A.area partition.s0) :=
      disk_area_eq_twelve_sector_areas M A partition
    _ = L.scalar.nsmul 6
          (L.scalar.add (A.area partition.s0) (A.area partition.s0)) :=
      twelve_halves_are_six_wholes L.scalar _
    _ = L.scalar.nsmul 6 (A.triangleArea a b c) :=
      congrArg (L.scalar.nsmul 6) sector_is_half

end Soultions.Sharygin.Page14.Problem22.Area
