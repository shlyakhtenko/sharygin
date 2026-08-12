import Sharygin19Problem51.Configuration

/-!
# Direct area decompositions for Sharygin, PDF page 19, problem 51
-/

namespace Soultions.Sharygin.Page19.Problem51.Area

open Euclid Plane
open Soultions.Sharygin.Page19.Problem51.Partitions
open Soultions.Sharygin.Page19.Problem51.Configuration
open Soultions.Sharygin.Page19.Problem51.TriangleArea

variable {G : Plane} {L : LengthMeasurement G}

def leftOnly (L : LengthMeasurement G) (o a b ra rb : G.Point) : G.Region :=
  fun p => cell o a b p ∧ L.ClosedDisk a ra p ∧ ¬L.ClosedDisk b rb p

def rightOnly (L : LengthMeasurement G) (o a b ra rb : G.Point) : G.Region :=
  fun p => cell o a b p ∧ ¬L.ClosedDisk a ra p ∧ L.ClosedDisk b rb p

private theorem areaDisjoint_of_pointwise
    (M : AngleMeasurement G) (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms A M] {X Y : G.Region}
    (h : ∀ p, ¬(X p ∧ Y p)) : A.AreaDisjoint X Y := by
  unfold AreaMeasurement.AreaDisjoint
  have hempty : Plane.Region.inter (G := G) X Y = Plane.Region.empty (G := G) := by
    funext p
    apply propext
    constructor
    · intro hp
      exact (h p hp).elim
    · intro hp
      exact hp.elim
  rw [hempty, AreaMeasurement.Axioms.empty_area M]

/-- Inclusion-exclusion in the representative center triangle, proved from its four atoms. -/
theorem local_inclusion_exclusion
    (M : AngleMeasurement G) (A : AreaMeasurement G L)
    [L.Axioms] [AreaMeasurement.Axioms A M]
    (o a b ra rb : G.Point) :
    L.scalar.add
        (A.area (localUncovered L o a b ra rb))
        (L.scalar.add
          (A.area (leftSector L o a b ra))
          (A.area (rightSector L o a b rb))) =
      L.scalar.add
        (A.area (cell o a b))
        (A.area (overlap L o a b ra rb)) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  classical
  let U := localUncovered L o a b ra rb
  let X := leftOnly L o a b ra rb
  let Y := rightOnly L o a b ra rb
  let O := overlap L o a b ra rb
  have hUX : A.AreaDisjoint U X := areaDisjoint_of_pointwise M A (by
    intro p hp
    exact hp.1.2 (Or.inl hp.2.2.1))
  have hUXY : A.AreaDisjoint (Plane.Region.union (G := G) U X) Y :=
    areaDisjoint_of_pointwise M A (by
      intro p hp
      rcases hp.1 with hu | hx
      · exact hu.2 (Or.inr hp.2.2.2)
      · exact hp.2.2.1 hx.2.1)
  have hUXYO : A.AreaDisjoint
      (Plane.Region.union (G := G) (Plane.Region.union (G := G) U X) Y) O :=
    areaDisjoint_of_pointwise M A (by
      intro p hp
      rcases hp.1 with hux | hy
      · rcases hux with hu | hx
        · exact hu.2 (Or.inl hp.2.1.2)
        · exact hx.2.2 hp.2.2
      · exact hy.2.1 hp.2.1.2)
  have hcell :
      Plane.Region.union (G := G)
        (Plane.Region.union (G := G) (Plane.Region.union (G := G) U X) Y) O =
        cell o a b := by
    funext p
    apply propext
    simp only [Plane.Region.union, U, X, Y, O, localUncovered, difference,
      leftOnly, rightOnly, overlap, leftSector, cell, Plane.Region.inter]
    constructor
    · intro hp
      rcases hp with huxy | ho
      · rcases huxy with hux | hy
        · rcases hux with hu | hx
          · exact hu.1
          · exact hx.1
        · exact hy.1
      · exact ho.1.1
    · intro ht
      by_cases ha : L.ClosedDisk a ra p
      · by_cases hb : L.ClosedDisk b rb p
        · exact Or.inr ⟨⟨ht, ha⟩, hb⟩
        · exact Or.inl (Or.inl (Or.inr ⟨ht, ha, hb⟩))
      · by_cases hb : L.ClosedDisk b rb p
        · exact Or.inl (Or.inr ⟨ht, ha, hb⟩)
        · exact Or.inl (Or.inl (Or.inl ⟨ht, fun h => h.elim ha hb⟩))
  have hXO : A.AreaDisjoint X O := areaDisjoint_of_pointwise M A (by
    intro p hp
    exact hp.1.2.2 hp.2.2)
  have hYO : A.AreaDisjoint Y O := areaDisjoint_of_pointwise M A (by
    intro p hp
    exact hp.1.2.1 hp.2.1.2)
  have hleft : Plane.Region.union (G := G) X O = leftSector L o a b ra := by
    funext p
    apply propext
    simp only [Plane.Region.union, X, O, leftOnly, overlap, leftSector,
      cell, Plane.Region.inter]
    constructor
    · intro hp
      rcases hp with hx | ho
      · exact ⟨hx.1, hx.2.1⟩
      · exact ho.1
    · intro hp
      by_cases hb : L.ClosedDisk b rb p
      · exact Or.inr ⟨hp, hb⟩
      · exact Or.inl ⟨hp.1, hp.2, hb⟩
  have hright : Plane.Region.union (G := G) Y O = rightSector L o a b rb := by
    funext p
    apply propext
    simp only [Plane.Region.union, Y, O, rightOnly, overlap, leftSector,
      rightSector, cell, Plane.Region.inter]
    constructor
    · intro hp
      rcases hp with hy | ho
      · exact ⟨hy.1, hy.2.2⟩
      · exact ⟨ho.1.1, ho.2⟩
    · intro hp
      by_cases ha : L.ClosedDisk a ra p
      · exact Or.inr ⟨⟨hp.1, ha⟩, hp.2⟩
      · exact Or.inl ⟨hp.1, ha, hp.2⟩
  have hcellArea : A.area (cell o a b) =
      L.scalar.add
        (L.scalar.add (L.scalar.add (A.area U) (A.area X)) (A.area Y))
        (A.area O) := by
    rw [← hcell, AreaMeasurement.Axioms.finite_additive M _ _ hUXYO,
      AreaMeasurement.Axioms.finite_additive M _ _ hUXY,
      AreaMeasurement.Axioms.finite_additive M _ _ hUX]
  have hleftArea : A.area (leftSector L o a b ra) =
      L.scalar.add (A.area X) (A.area O) := by
    rw [← hleft, AreaMeasurement.Axioms.finite_additive M _ _ hXO]
  have hrightArea : A.area (rightSector L o a b rb) =
      L.scalar.add (A.area Y) (A.area O) := by
    rw [← hright, AreaMeasurement.Axioms.finite_additive M _ _ hYO]
  rw [hleftArea, hrightArea, hcellArea]
  dsimp [U, O]
  letI : Std.Associative L.scalar.add := ⟨OrderedScalar.Axioms.add_assoc⟩
  letI : Std.Commutative L.scalar.add := ⟨OrderedScalar.Axioms.add_comm⟩
  ac_rfl

theorem lens_decomposition
    (M : AngleMeasurement G) (A : AreaMeasurement G L)
    [L.Axioms] [AreaMeasurement.Axioms A M]
    (d : Data M A) :
    L.scalar.add
        (A.area (overlap L d.center d.v0 d.v1 d.radiusPoint0 d.radiusPoint1))
        (L.scalar.add
          (A.triangleArea d.v0 d.midpoint d.intersectionPoint)
          (A.triangleArea d.v1 d.midpoint d.intersectionPoint)) =
      L.scalar.add (A.area d.sector45Left) (A.area d.sector45Right) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  have hleft : A.area d.sector45Left =
      L.scalar.add (A.triangleArea d.v0 d.midpoint d.intersectionPoint)
        (A.area d.segmentLeft) := by
    rw [d.sector45Left_cut, AreaMeasurement.Axioms.finite_additive M _ _
      d.sector45Left_disjoint]
    rfl
  have hright : A.area d.sector45Right =
      L.scalar.add (A.triangleArea d.v1 d.midpoint d.intersectionPoint)
        (A.area d.segmentRight) := by
    rw [d.sector45Right_cut, AreaMeasurement.Axioms.finite_additive M _ _
      d.sector45Right_disjoint]
    rfl
  have hoverlap : A.area
      (overlap L d.center d.v0 d.v1 d.radiusPoint0 d.radiusPoint1) =
      L.scalar.add (A.area d.segmentLeft) (A.area d.segmentRight) := by
    rw [d.overlap_cut, AreaMeasurement.Axioms.finite_additive M _ _ d.overlap_disjoint]
  rw [hleft, hright, hoverlap]
  letI : Std.Associative L.scalar.add := ⟨OrderedScalar.Axioms.add_assoc⟩
  letI : Std.Commutative L.scalar.add := ⟨OrderedScalar.Axioms.add_comm⟩
  ac_rfl

theorem right_triangle_areas (M : AngleMeasurement G) (A : AreaMeasurement G L)
    [G.Axioms] [M.Axioms] [L.Axioms] [AreaMeasurement.Axioms A M] (d : Data M A) :
    L.scalar.add (A.triangleArea d.v0 d.midpoint d.intersectionPoint)
        (A.triangleArea d.v0 d.midpoint d.intersectionPoint) =
      L.scalar.mul (L.length d.v0 d.midpoint)
        (L.length d.midpoint d.intersectionPoint) ∧
    L.scalar.add (A.triangleArea d.v1 d.midpoint d.intersectionPoint)
        (A.triangleArea d.v1 d.midpoint d.intersectionPoint) =
      L.scalar.mul (L.length d.v1 d.midpoint)
        (L.length d.midpoint d.intersectionPoint) := by
  constructor
  · exact right_triangle_double_area G M L A d.left_noncollinear d.leftSense
      d.left_right_angle
  · exact right_triangle_double_area G M L A d.right_noncollinear d.rightSense
      d.right_right_angle

end Soultions.Sharygin.Page19.Problem51.Area
