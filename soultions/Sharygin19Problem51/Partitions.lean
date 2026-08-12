import Euclid

/-!
# The two circle partitions used in Sharygin, PDF page 19, problem 51

Only the sixfold and eightfold partitions occurring in this problem are recorded.  Their
conclusions are derived from finite additivity and rigid-motion invariance.
-/

namespace Soultions.Sharygin.Page19.Problem51.Partitions

open Euclid Plane

variable {G : Plane} {L : LengthMeasurement G}

def U2 (x0 x1 : G.Region) : G.Region := Plane.Region.union (G := G) x0 x1
def U3 (x0 x1 x2 : G.Region) : G.Region := Plane.Region.union (G := G) (U2 x0 x1) x2
def U4 (x0 x1 x2 x3 : G.Region) : G.Region := Plane.Region.union (G := G) (U3 x0 x1 x2) x3
def U5 (x0 x1 x2 x3 x4 : G.Region) : G.Region := Plane.Region.union (G := G) (U4 x0 x1 x2 x3) x4
def U6 (x0 x1 x2 x3 x4 x5 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U5 x0 x1 x2 x3 x4) x5
def U7 (x0 x1 x2 x3 x4 x5 x6 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U6 x0 x1 x2 x3 x4 x5) x6
def U8 (x0 x1 x2 x3 x4 x5 x6 x7 : G.Region) : G.Region :=
  Plane.Region.union (G := G) (U7 x0 x1 x2 x3 x4 x5 x6) x7

structure SixPartition (A : AreaMeasurement G L) (whole : G.Region) where
  x0 : G.Region
  x1 : G.Region
  x2 : G.Region
  x3 : G.Region
  x4 : G.Region
  x5 : G.Region
  c01 : Plane.Region.Congruent (G := G) x0 x1
  c02 : Plane.Region.Congruent (G := G) x0 x2
  c03 : Plane.Region.Congruent (G := G) x0 x3
  c04 : Plane.Region.Congruent (G := G) x0 x4
  c05 : Plane.Region.Congruent (G := G) x0 x5
  d01 : A.AreaDisjoint x0 x1
  d012 : A.AreaDisjoint (U2 x0 x1) x2
  d0123 : A.AreaDisjoint (U3 x0 x1 x2) x3
  d01234 : A.AreaDisjoint (U4 x0 x1 x2 x3) x4
  d012345 : A.AreaDisjoint (U5 x0 x1 x2 x3 x4) x5
  cover : U6 x0 x1 x2 x3 x4 x5 = whole

structure EightPartition (A : AreaMeasurement G L) (whole : G.Region) where
  x0 : G.Region
  x1 : G.Region
  x2 : G.Region
  x3 : G.Region
  x4 : G.Region
  x5 : G.Region
  x6 : G.Region
  x7 : G.Region
  c01 : Plane.Region.Congruent (G := G) x0 x1
  c02 : Plane.Region.Congruent (G := G) x0 x2
  c03 : Plane.Region.Congruent (G := G) x0 x3
  c04 : Plane.Region.Congruent (G := G) x0 x4
  c05 : Plane.Region.Congruent (G := G) x0 x5
  c06 : Plane.Region.Congruent (G := G) x0 x6
  c07 : Plane.Region.Congruent (G := G) x0 x7
  d01 : A.AreaDisjoint x0 x1
  d012 : A.AreaDisjoint (U2 x0 x1) x2
  d0123 : A.AreaDisjoint (U3 x0 x1 x2) x3
  d01234 : A.AreaDisjoint (U4 x0 x1 x2 x3) x4
  d012345 : A.AreaDisjoint (U5 x0 x1 x2 x3 x4) x5
  d0123456 : A.AreaDisjoint (U6 x0 x1 x2 x3 x4 x5) x6
  d01234567 : A.AreaDisjoint (U7 x0 x1 x2 x3 x4 x5 x6) x7
  cover : U8 x0 x1 x2 x3 x4 x5 x6 x7 = whole

theorem area_eq_of_congruent
    (M : AngleMeasurement G) (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms A M] {X Y : G.Region}
    (h : Plane.Region.Congruent (G := G) X Y) : A.area X = A.area Y := by
  obtain ⟨f, rfl⟩ := h
  exact (AreaMeasurement.Axioms.isometry_invariant M f X).symm

theorem six_partition_area
    (M : AngleMeasurement G) (A : AreaMeasurement G L)
    [L.Axioms] [AreaMeasurement.Axioms A M]
    {whole : G.Region} (p : SixPartition A whole) :
    A.area whole = L.scalar.nsmul 6 (A.area p.x0) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  have h1 := area_eq_of_congruent M A p.c01
  have h2 := area_eq_of_congruent M A p.c02
  have h3 := area_eq_of_congruent M A p.c03
  have h4 := area_eq_of_congruent M A p.c04
  have h5 := area_eq_of_congruent M A p.c05
  have hu2 : A.area (U2 p.x0 p.x1) = L.scalar.nsmul 2 (A.area p.x0) := by
    rw [U2, AreaMeasurement.Axioms.finite_additive M _ _ p.d01, ← h1]
    simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
  have hu3 : A.area (U3 p.x0 p.x1 p.x2) = L.scalar.nsmul 3 (A.area p.x0) := by
    rw [U3, AreaMeasurement.Axioms.finite_additive M _ _ p.d012, hu2, ← h2]
    rfl
  have hu4 : A.area (U4 p.x0 p.x1 p.x2 p.x3) = L.scalar.nsmul 4 (A.area p.x0) := by
    rw [U4, AreaMeasurement.Axioms.finite_additive M _ _ p.d0123, hu3, ← h3]
    rfl
  have hu5 : A.area (U5 p.x0 p.x1 p.x2 p.x3 p.x4) = L.scalar.nsmul 5 (A.area p.x0) := by
    rw [U5, AreaMeasurement.Axioms.finite_additive M _ _ p.d01234, hu4, ← h4]
    rfl
  calc
    A.area whole = A.area (U6 p.x0 p.x1 p.x2 p.x3 p.x4 p.x5) := congrArg A.area p.cover.symm
    _ = L.scalar.add (A.area (U5 p.x0 p.x1 p.x2 p.x3 p.x4)) (A.area p.x5) :=
      AreaMeasurement.Axioms.finite_additive M _ _ p.d012345
    _ = L.scalar.nsmul 6 (A.area p.x0) := by rw [hu5, ← h5]; rfl

theorem eight_partition_area
    (M : AngleMeasurement G) (A : AreaMeasurement G L)
    [L.Axioms] [AreaMeasurement.Axioms A M]
    {whole : G.Region} (p : EightPartition A whole) :
    A.area whole = L.scalar.nsmul 8 (A.area p.x0) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  have h1 := area_eq_of_congruent M A p.c01
  have h2 := area_eq_of_congruent M A p.c02
  have h3 := area_eq_of_congruent M A p.c03
  have h4 := area_eq_of_congruent M A p.c04
  have h5 := area_eq_of_congruent M A p.c05
  have h6 := area_eq_of_congruent M A p.c06
  have h7 := area_eq_of_congruent M A p.c07
  have hu2 : A.area (U2 p.x0 p.x1) = L.scalar.nsmul 2 (A.area p.x0) := by
    rw [U2, AreaMeasurement.Axioms.finite_additive M _ _ p.d01, ← h1]
    simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
  have hu3 : A.area (U3 p.x0 p.x1 p.x2) = L.scalar.nsmul 3 (A.area p.x0) := by
    rw [U3, AreaMeasurement.Axioms.finite_additive M _ _ p.d012, hu2, ← h2]; rfl
  have hu4 : A.area (U4 p.x0 p.x1 p.x2 p.x3) = L.scalar.nsmul 4 (A.area p.x0) := by
    rw [U4, AreaMeasurement.Axioms.finite_additive M _ _ p.d0123, hu3, ← h3]; rfl
  have hu5 : A.area (U5 p.x0 p.x1 p.x2 p.x3 p.x4) = L.scalar.nsmul 5 (A.area p.x0) := by
    rw [U5, AreaMeasurement.Axioms.finite_additive M _ _ p.d01234, hu4, ← h4]; rfl
  have hu6 : A.area (U6 p.x0 p.x1 p.x2 p.x3 p.x4 p.x5) =
      L.scalar.nsmul 6 (A.area p.x0) := by
    rw [U6, AreaMeasurement.Axioms.finite_additive M _ _ p.d012345, hu5, ← h5]; rfl
  have hu7 : A.area (U7 p.x0 p.x1 p.x2 p.x3 p.x4 p.x5 p.x6) =
      L.scalar.nsmul 7 (A.area p.x0) := by
    rw [U7, AreaMeasurement.Axioms.finite_additive M _ _ p.d0123456, hu6, ← h6]; rfl
  calc
    A.area whole = A.area (U8 p.x0 p.x1 p.x2 p.x3 p.x4 p.x5 p.x6 p.x7) :=
      congrArg A.area p.cover.symm
    _ = L.scalar.add (A.area (U7 p.x0 p.x1 p.x2 p.x3 p.x4 p.x5 p.x6)) (A.area p.x7) :=
      AreaMeasurement.Axioms.finite_additive M _ _ p.d01234567
    _ = L.scalar.nsmul 8 (A.area p.x0) := by rw [hu7, ← h7]; rfl

end Soultions.Sharygin.Page19.Problem51.Partitions
