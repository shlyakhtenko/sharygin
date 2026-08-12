import Sharygin14Problem19.Similarity

/-!
# Source configuration for Sharygin, page 14, problem 19

Convexity is recorded by a common strict orientation of the four consecutive triples.  The
conclusion uses the repository's incidence definition of tangency and requires each contact
point to lie on the corresponding closed side segment.
-/

namespace Soultions.Sharygin.Page14.Problem19.Configuration

open Euclid Plane
open Soultions.Sharygin.Page14.Problem19.Tarski
open Soultions.Sharygin.Page14.Problem19.Affine
open Soultions.Sharygin.Page14.Problem19.Similarity

variable (G : Plane)

/-- Four vertices in strict convex cyclic order, together with Pitot's length equality. -/
structure ConvexQuadrilateral (L : LengthMeasurement G) where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  sense : RotationSense
  turnABC : G.Orientation a b c = some sense
  turnBCD : G.Orientation b c d = some sense
  turnCDA : G.Orientation c d a = some sense
  turnDAB : G.Orientation d a b = some sense
  pitot :
    L.scalar.add (L.length a b) (L.length c d) =
      L.scalar.add (L.length a d) (L.length b c)

namespace ConvexQuadrilateral

variable {G : Plane} [G.Axioms] {L : LengthMeasurement G}

private theorem noncollinear_of_orientation_some
    {a b c : G.Point} {sense : RotationSense}
    (h : G.Orientation a b c = some sense) :
    ¬G.Collinear a b c := by
  intro hcollinear
  have hnone : G.Orientation a b c = none :=
    (Plane.Axioms.orientation_collinear a b c).2 hcollinear
  rw [h] at hnone
  contradiction

theorem abc_noncollinear (q : ConvexQuadrilateral G L) :
    ¬G.Collinear q.a q.b q.c :=
  noncollinear_of_orientation_some q.turnABC

theorem bcd_noncollinear (q : ConvexQuadrilateral G L) :
    ¬G.Collinear q.b q.c q.d :=
  noncollinear_of_orientation_some q.turnBCD

theorem cda_noncollinear (q : ConvexQuadrilateral G L) :
    ¬G.Collinear q.c q.d q.a :=
  noncollinear_of_orientation_some q.turnCDA

theorem dab_noncollinear (q : ConvexQuadrilateral G L) :
    ¬G.Collinear q.d q.a q.b :=
  noncollinear_of_orientation_some q.turnDAB

theorem a_ne_b (q : ConvexQuadrilateral G L) : q.a ≠ q.b := by
  intro h
  apply q.abc_noncollinear
  simpa [h] using collinear_refl_left G q.a q.c

theorem b_ne_c (q : ConvexQuadrilateral G L) : q.b ≠ q.c := by
  intro h
  apply q.abc_noncollinear
  simpa [h] using collinear_refl_right G q.a q.b

theorem c_ne_d (q : ConvexQuadrilateral G L) : q.c ≠ q.d := by
  intro h
  apply q.bcd_noncollinear
  simpa [h] using collinear_refl_right G q.b q.c

theorem d_ne_a (q : ConvexQuadrilateral G L) : q.d ≠ q.a := by
  intro h
  apply q.dab_noncollinear
  simpa [h] using collinear_refl_left G q.a q.b

private theorem oppositeSides_of_orientation_ne
    {a b p q : G.Point}
    (hp_off : ¬G.Collinear a b p)
    (hq_off : ¬G.Collinear a b q)
    (hne : G.Orientation a b p ≠ G.Orientation a b q) :
    G.OppositeSides a b p q := by
  apply Classical.byContradiction
  intro hnot
  exact hne (orientation_eq_of_not_oppositeSides G hp_off hq_off hnot)

/-- The two diagonals of a strict convex quadrilateral cross internally. -/
theorem opposite_ac (q : ConvexQuadrilateral G L) :
    G.OppositeSides q.a q.c q.b q.d := by
  have hb_off : ¬G.Collinear q.a q.c q.b := by
    intro h
    exact q.abc_noncollinear (collinear_swap_last G h)
  have hd_off : ¬G.Collinear q.a q.c q.d := by
    intro h
    exact q.cda_noncollinear (collinear_cyclic G h)
  apply oppositeSides_of_orientation_ne hb_off hd_off
  have hb_orientation :
      G.Orientation q.a q.c q.b = some q.sense.reverse := by
    calc
      G.Orientation q.a q.c q.b =
          (G.Orientation q.c q.a q.b).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap _ _ _
      _ = (G.Orientation q.a q.b q.c).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic q.c q.a q.b,
          Plane.Axioms.orientation_cyclic q.a q.b q.c]
      _ = some q.sense.reverse := by rw [q.turnABC]; rfl
  have hd_orientation :
      G.Orientation q.a q.c q.d = some q.sense := by
    calc
      _ = G.Orientation q.c q.d q.a := by
        rw [Plane.Axioms.orientation_cyclic q.a q.c q.d,
          Plane.Axioms.orientation_cyclic q.c q.d q.a]
      _ = some q.sense := q.turnCDA
  rw [hb_orientation, hd_orientation]
  cases q.sense <;> decide

theorem opposite_bd (q : ConvexQuadrilateral G L) :
    G.OppositeSides q.b q.d q.a q.c := by
  have ha_off : ¬G.Collinear q.b q.d q.a := by
    intro h
    exact q.dab_noncollinear (collinear_cyclic G h)
  have hc_off : ¬G.Collinear q.b q.d q.c := by
    intro h
    exact q.bcd_noncollinear (collinear_swap_last G h)
  apply oppositeSides_of_orientation_ne ha_off hc_off
  have ha_orientation :
      G.Orientation q.b q.d q.a = some q.sense := by
    calc
      _ = G.Orientation q.d q.a q.b := by
        rw [Plane.Axioms.orientation_cyclic q.b q.d q.a,
          Plane.Axioms.orientation_cyclic q.d q.a q.b]
      _ = some q.sense := q.turnDAB
  have hc_orientation :
      G.Orientation q.b q.d q.c = some q.sense.reverse := by
    calc
      G.Orientation q.b q.d q.c =
          (G.Orientation q.d q.b q.c).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap _ _ _
      _ = (G.Orientation q.b q.c q.d).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic q.d q.b q.c,
          Plane.Axioms.orientation_cyclic q.b q.c q.d]
      _ = some q.sense.reverse := by rw [q.turnBCD]; rfl
  rw [ha_orientation, hc_orientation]
  cases q.sense <;> decide

/-- The diagonals have a common point lying between both pairs of opposite vertices. -/
theorem diagonal_intersection (q : ConvexQuadrilateral G L) :
    ∃ x, G.Bet q.a x q.c ∧ G.Bet q.b x q.d := by
  obtain ⟨_, _, x, hacx, hbxd⟩ := q.opposite_ac
  obtain ⟨_, _, y, hbdy, hayc⟩ := q.opposite_bd
  have hbdx : G.Collinear q.b q.d x :=
    collinear_swap_last G (Or.inl hbxd)
  have hacy : G.Collinear q.a q.c y :=
    collinear_swap_last G (Or.inl hayc)
  have hac : q.a ≠ q.c := by
    intro h
    apply q.abc_noncollinear
    simpa [h] using
      (collinear_cyclic G (collinear_refl_left G q.a q.b))
  have hbd : q.b ≠ q.d := by
    intro h
    apply q.bcd_noncollinear
    simpa [h] using
      (collinear_cyclic G (collinear_refl_left G q.d q.c))
  have hxy : x = y := by
    apply Classical.byContradiction
    intro hne
    have hxya : G.Collinear x y q.a :=
      collinear_three_on_line G hac hacx hacy
        (collinear_cyclic G (collinear_refl_left G q.a q.c))
    have hxyc : G.Collinear x y q.c :=
      collinear_three_on_line G hac hacx hacy
        (collinear_refl_right G q.a q.c)
    have hxyb : G.Collinear x y q.b :=
      collinear_three_on_line G hbd hbdx hbdy
        (collinear_cyclic G (collinear_refl_left G q.b q.d))
    exact q.abc_noncollinear
      (collinear_three_on_line G hne hxya hxyb hxyc)
  subst y
  exact ⟨x, hayc, hbxd⟩

end ConvexQuadrilateral

/-- A circle touches the closed segment `pq` at `contact`. -/
structure SideContact (circle : Circle G) (p q : G.Point) where
  contact : G.Point
  on_segment : G.Bet p contact q
  through : G.Point
  through_on_line : G.Collinear p q through
  tangent : G.TangentAt circle contact through

/-- One circle touches all four sides of a quadrilateral. -/
structure FourSideTangency
    (circle : Circle G)
    (a b c d : G.Point) where
  sideAB : SideContact G circle a b
  sideBC : SideContact G circle b c
  sideCD : SideContact G circle c d
  sideAD : SideContact G circle a d

/-- The exact existential conclusion of problem 19. -/
def Statement (L : LengthMeasurement G) : Prop :=
  ∀ quadrilateral : ConvexQuadrilateral G L,
    ∃ circle : Circle G,
      Nonempty
        (FourSideTangency G circle
          quadrilateral.a quadrilateral.b quadrilateral.c quadrilateral.d)

end Soultions.Sharygin.Page14.Problem19.Configuration
