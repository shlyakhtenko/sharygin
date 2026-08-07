import Euclid
import Sharygin13Problem15.Tarski
import Sharygin13Problem15.Midpoint
import Sharygin13Problem15.Affine

/-!
# Problem-local directed-angle layer for Sharygin, page 13, problem 15

The triangle-turn and inscribed-angle calculations are duplicated here for the secant-product
argument, in accordance with `proof_rules.md`.
-/

namespace Soultions.Sharygin.Page13.Problem15

open Euclid Plane
open Soultions.Sharygin.Page13.Problem15.Tarski
open Soultions.Sharygin.Page13.Problem15.Midpoint

section LocalFacts

variable (G : Plane) [G.Axioms]

/-- Directed triangle sum, kept local until it has been derived from the plane axioms below. -/
private def TriangleTurn (M : AngleMeasurement G) (a b c : G.Point)
    (sense : RotationSense) : Prop :=
  M.add
      (M.add
        (M.measure ⟨a, b, c, sense⟩)
        (M.measure ⟨b, c, a, sense⟩))
      (M.measure ⟨c, a, b, sense⟩) =
    M.halfTurn

/--
The two congruent triangle copies used in the Euclidean parallel construction for a triangle.
The existence proof is the geometric core of the local triangle-sum derivation.
-/
private structure TriangleSumConstruction (a b c : G.Point) where
  x : G.Point
  y : G.Point
  y_a_x : G.Bet y a x
  ax_bc : G.Congruent a x b c
  bx_ac : G.Congruent b x a c
  ay_cb : G.Congruent a y c b
  cy_ab : G.Congruent c y a b
  x_opposite_c : G.OppositeSides a b x c
  y_opposite_b : G.OppositeSides a c y b

/-- Local to this solution so later solutions can reveal whether the proof pattern recurs. -/
private theorem congruent_refl (a b : G.Point) : G.Congruent a b a b := by
  exact Plane.Axioms.congruenceTransitivity b a a b a b
    (Plane.Axioms.congruenceReversal b a) (Plane.Axioms.congruenceReversal b a)

private theorem congruent_symm {a b c d : G.Point} (h : G.Congruent a b c d) :
    G.Congruent c d a b := by
  exact Plane.Axioms.congruenceTransitivity a b c d a b h (congruent_refl G a b)

private theorem congruent_trans {a b c d e f : G.Point} (h₁ : G.Congruent a b c d)
    (h₂ : G.Congruent c d e f) : G.Congruent a b e f := by
  exact Plane.Axioms.congruenceTransitivity c d a b e f (congruent_symm G h₁) h₂

private theorem congruent_zero (a b : G.Point) : G.Congruent a a b b := by
  obtain ⟨x, _, h⟩ :=
    Plane.Axioms.segmentConstruction a b b a
  have hax : a = x :=
    Plane.Axioms.congruenceIdentity a x b h
  exact hax ▸ h

private theorem bet_endpoint_refl (a b : G.Point) : G.Bet a b b := by
  obtain ⟨x, hbet, hzero⟩ :=
    Plane.Axioms.segmentConstruction b b b a
  have hbx : b = x :=
    Plane.Axioms.congruenceIdentity b x b hzero
  exact hbx ▸ hbet

private theorem bet_symm {a b c : G.Point} (h : G.Bet a b c) : G.Bet c b a := by
  obtain ⟨x, h_between_b, h_between_c⟩ :=
    Plane.Axioms.innerPasch a b c b c h (bet_endpoint_refl G b c)
  have hbx : b = x :=
    Plane.Axioms.betweennessIdentity b x h_between_b
  exact hbx ▸ h_between_c

private theorem bet_start_refl (a b : G.Point) : G.Bet a a b := by
  exact bet_symm G (bet_endpoint_refl G b a)

private theorem bet_inner_trans {a b c d : G.Point} (habd : G.Bet a b d)
    (hbcd : G.Bet b c d) : G.Bet a b c := by
  obtain ⟨x, h_between_b, h_between_c⟩ :=
    Plane.Axioms.innerPasch a b d b c habd hbcd
  have hbx : b = x :=
    Plane.Axioms.betweennessIdentity b x h_between_b
  exact bet_symm G (hbx ▸ h_between_c)

private theorem bet_antisymm {a b c : G.Point} (habc : G.Bet a b c)
    (hacb : G.Bet a c b) : b = c := by
  have h_cycle : G.Bet b c b :=
    bet_inner_trans G (bet_symm G hacb) (bet_symm G habc)
  exact Plane.Axioms.betweennessIdentity b c h_cycle

private theorem segment_add {a b c a' b' c' : G.Point} (hab : a ≠ b)
    (h_between : G.Bet a b c) (h_between' : G.Bet a' b' c')
    (h₁ : G.Congruent a b a' b') (h₂ : G.Congruent b c b' c') :
    G.Congruent a c a' c' := by
  have hca : G.Congruent c a c' a' :=
    Plane.Axioms.fiveSegment a b c a a' b' c' a' hab h_between h_between'
      h₁ h₂ (congruent_zero G a a')
      (congruent_trans G (Plane.Axioms.congruenceReversal b a)
        (congruent_trans G h₁ (Plane.Axioms.congruenceReversal a' b')))
  exact congruent_trans G
    (Plane.Axioms.congruenceReversal a c)
    (congruent_trans G hca (Plane.Axioms.congruenceReversal c' a'))

omit [G.Axioms] in
private theorem collinear_cyclic {a b c : G.Point} (h : G.Collinear a b c) :
    G.Collinear b c a := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

private theorem collinear_swap {a b c : G.Point} (h : G.Collinear a b c) :
    G.Collinear b a c := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (bet_symm G h))
  · exact Or.inr (Or.inl (bet_symm G h))
  · exact Or.inl (bet_symm G h)

private theorem orientation_same_side {a b p q r : G.Point}
    (hp : G.OppositeSides a b p r) (hq : G.OppositeSides a b q r) :
    G.Orientation a b p = G.Orientation a b q := by
  rw [Plane.Axioms.orientation_opposite_sides (G := G) hp,
    Plane.Axioms.orientation_opposite_sides (G := G) hq]

private theorem orientation_copy_across_line {a b p q : G.Point}
    (h : G.OppositeSides a b p q) :
    G.Orientation b a p = G.Orientation a b q := by
  have hopposite :
      G.Orientation a b p = (G.Orientation a b q).map RotationSense.reverse :=
    Plane.Axioms.orientation_opposite_sides (G := G) h
  rw [Plane.Axioms.orientation_swap a b p] at hopposite
  cases hp : G.Orientation b a p <;>
    cases hq : G.Orientation a b q <;>
    simp_all [RotationSense.reverse]
  case some.some left right =>
    cases left <;> cases right <;> simp_all

private theorem sameRay_refl {o a : G.Point} (h : a ≠ o) : G.SameRay o a a := by
  refine ⟨h, h, Or.inl (bet_endpoint_refl G o a), ?_⟩
  intro h_between
  exact h (Plane.Axioms.betweennessIdentity a o h_between)

private theorem sameRay_symm {o a b : G.Point} (h : G.SameRay o a b) :
    G.SameRay o b a := by
  refine
    ⟨h.2.1, h.1, collinear_cyclic G (collinear_swap G h.2.2.1), ?_⟩
  intro hboa
  exact h.2.2.2 (bet_symm G hboa)

private theorem sameRay_from_far_endpoint {a b c : G.Point} (h : G.Bet a b c)
    (hbc : b ≠ c) : G.SameRay c b a := by
  have hac : a ≠ c := by
    intro hac
    subst a
    exact hbc (Plane.Axioms.betweennessIdentity c b h).symm
  refine ⟨hbc, hac, Or.inl (bet_symm G h), ?_⟩
  intro h_between
  exact hbc (bet_antisymm G h (bet_symm G h_between))

private theorem sameRay_from_near_endpoint {a b c : G.Point} (h : G.Bet a b c)
    (hab : a ≠ b) (hbc : b ≠ c) : G.SameRay a b c := by
  have hac : a ≠ c := by
    intro hac
    subst c
    exact hab (Plane.Axioms.betweennessIdentity a b h)
  refine ⟨hab.symm, hac.symm, Or.inl h, ?_⟩
  intro hbac
  have hcycle : G.Bet c a c :=
    Tarski.bet_outer_trans G (bet_symm G hbac) h hab
  exact hac (Plane.Axioms.betweennessIdentity c a hcycle).symm

private theorem circle_radii_congruent {circle : Circle G} {p q : G.Point}
    (hp : G.OnCircle circle p) (hq : G.OnCircle circle q) :
    G.Congruent circle.center p circle.center q := by
  exact congruent_trans G hp (congruent_symm G hq)

private theorem center_ne_onCircle {circle : Circle G} {p : G.Point}
    (hp : G.OnCircle circle p) : circle.center ≠ p := by
  intro hop
  subst p
  have hradius_zero : G.Congruent circle.center circle.radiusPoint circle.center circle.center := by
    exact congruent_symm G hp
  exact circle.radius_ne
    (Plane.Axioms.congruenceIdentity circle.center circle.radiusPoint circle.center hradius_zero)

private theorem inside_point_ne_onCircle {circle : Circle G} {p q : G.Point}
    (hp : G.InsideCircle circle p) (hq : G.OnCircle circle q) :
    p ≠ q := by
  intro hpq
  subst q
  obtain ⟨r, hr, hp_between, hpr⟩ := hp
  have hop : circle.center ≠ p :=
    center_ne_onCircle G hq
  have hpr_eq : p = r :=
    bet_equal_initial_collapse G hop hp_between
      (congruent_symm G (circle_radii_congruent G hq hr))
  exact hpr hpr_eq

private theorem orientation_swap_last (a b c : G.Point) :
    G.Orientation a b c = (G.Orientation a c b).map RotationSense.reverse := by
  rw [Plane.Axioms.orientation_swap a c b, Plane.Axioms.orientation_cyclic c a b]
  cases G.Orientation a b c with
  | none => rfl
  | some sense => cases sense <;> rfl

private theorem measure_sameRay_zero (M : AngleMeasurement G) [M.Axioms]
    {o a b : G.Point} (sense : RotationSense) (h : G.SameRay o a b) :
    M.measure ⟨a, o, b, sense⟩ = M.zero := by
  calc
    M.measure ⟨a, o, b, sense⟩ =
        M.measure ⟨a, o, a, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant a a b a o sense
        (sameRay_refl G h.1)
        (sameRay_symm G h)
    _ = M.zero := AngleMeasurement.Axioms.measure_refl a o sense

private theorem isosceles_base_angles (M : AngleMeasurement G) [M.Axioms]
    {a b c : G.Point} (sense : RotationSense) (h : G.Congruent a b a c) :
    M.measure ⟨a, b, c, sense⟩ = M.measure ⟨a, c, b, sense.reverse⟩ := by
  exact AngleMeasurement.Axioms.sss_reversing a b c a c b sense
    (congruent_trans G
      (congruent_trans G (Plane.Axioms.congruenceReversal b a) h)
      (Plane.Axioms.congruenceReversal a c))
    (Plane.Axioms.congruenceReversal b c)
    (congruent_symm G h)
    (orientation_swap_last G a b c)

/--
The triangle-turn identity for a collinear triple is immediate: exactly one of its three
directed angles is straight and the other two have coincident rays.
-/
private theorem triangle_turn_of_collinear (M : AngleMeasurement G) [M.Axioms]
    {a b c : G.Point} (sense : RotationSense)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcol : G.Collinear a b c) :
    TriangleTurn G M a b c sense := by
  rcases hcol with habc | hbca | hcab
  · have h₁ :
        M.measure ⟨a, b, c, sense⟩ = M.halfTurn :=
      AngleMeasurement.Axioms.measure_straight a b c sense
        hab hbc.symm habc
    have h₂ :
        M.measure ⟨b, c, a, sense⟩ = M.zero :=
      measure_sameRay_zero G M sense
        (sameRay_from_far_endpoint G habc hbc)
    have h₃ :
        M.measure ⟨c, a, b, sense⟩ = M.zero :=
      measure_sameRay_zero G M sense
        (sameRay_symm G (sameRay_from_near_endpoint G habc hab hbc))
    unfold TriangleTurn
    rw [h₁, h₂, h₃, AngleMeasurement.Axioms.add_zero,
      AngleMeasurement.Axioms.add_zero]
  · have h₁ :
        M.measure ⟨a, b, c, sense⟩ = M.zero :=
      measure_sameRay_zero G M sense
        (sameRay_symm G (sameRay_from_near_endpoint G hbca hbc hac.symm))
    have h₂ :
        M.measure ⟨b, c, a, sense⟩ = M.halfTurn :=
      AngleMeasurement.Axioms.measure_straight b c a sense
        hbc hac hbca
    have h₃ :
        M.measure ⟨c, a, b, sense⟩ = M.zero :=
      measure_sameRay_zero G M sense
        (sameRay_from_far_endpoint G hbca hac.symm)
    unfold TriangleTurn
    rw [h₁, h₂, h₃, AngleMeasurement.Axioms.zero_add,
      AngleMeasurement.Axioms.add_zero]
  · have h₁ :
        M.measure ⟨a, b, c, sense⟩ = M.zero :=
      measure_sameRay_zero G M sense
        (sameRay_from_far_endpoint G hcab hab)
    have h₂ :
        M.measure ⟨b, c, a, sense⟩ = M.zero :=
      measure_sameRay_zero G M sense
        (sameRay_symm G (sameRay_from_near_endpoint G hcab hac.symm hab))
    have h₃ :
        M.measure ⟨c, a, b, sense⟩ = M.halfTurn :=
      AngleMeasurement.Axioms.measure_straight c a b sense
        hac.symm hab.symm hcab
    unfold TriangleTurn
    rw [h₁, h₂, h₃, AngleMeasurement.Axioms.zero_add,
      AngleMeasurement.Axioms.zero_add]

private theorem triangle_turn_of_construction (M : AngleMeasurement G) [M.Axioms]
    {a b c : G.Point} (sense : RotationSense)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (construction : TriangleSumConstruction G a b c) :
    TriangleTurn G M a b c sense := by
  have hxa : construction.x ≠ a := by
    intro hxa
    have hzero : G.Congruent a a b c := by
      simpa [hxa] using construction.ax_bc
    exact hbc
      (Plane.Axioms.congruenceIdentity b c a
        (congruent_symm G hzero))
  have hya : construction.y ≠ a := by
    intro hya
    have hzero : G.Congruent a a c b := by
      simpa [hya] using construction.ay_cb
    exact hbc.symm
      (Plane.Axioms.congruenceIdentity c b a
        (congruent_symm G hzero))
  have hcopy_x :
      M.measure ⟨b, a, construction.x, sense⟩ =
        M.measure ⟨a, b, c, sense⟩ := by
    exact AngleMeasurement.Axioms.sss_preserving
      b a construction.x a b c sense
      (Plane.Axioms.congruenceReversal a b)
      construction.ax_bc construction.bx_ac
      (orientation_copy_across_line G construction.x_opposite_c)
  have hyc_ba : G.Congruent construction.y c b a := by
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal construction.y c)
      (congruent_trans G construction.cy_ab
        (Plane.Axioms.congruenceReversal a b))
  have hcopy_y :
      M.measure ⟨construction.y, a, c, sense⟩ =
        M.measure ⟨b, c, a, sense⟩ := by
    exact AngleMeasurement.Axioms.sss_preserving
      construction.y a c b c a sense
      construction.ay_cb (Plane.Axioms.congruenceReversal a c)
      hyc_ba (by
        rw [Plane.Axioms.orientation_cyclic construction.y a c]
        calc
          G.Orientation a c construction.y =
              (G.Orientation a c b).map RotationSense.reverse :=
            Plane.Axioms.orientation_opposite_sides (G := G)
              construction.y_opposite_b
          _ = G.Orientation a b c := (orientation_swap_last G a b c).symm
          _ = G.Orientation b c a := Plane.Axioms.orientation_cyclic a b c)
  have hsplit :
      M.measure ⟨construction.y, a, construction.x, sense⟩ =
        M.add
          (M.measure ⟨construction.y, a, c, sense⟩)
          (M.add
            (M.measure ⟨c, a, b, sense⟩)
            (M.measure ⟨b, a, construction.x, sense⟩)) := by
    calc
      M.measure ⟨construction.y, a, construction.x, sense⟩ =
          M.add
            (M.measure ⟨construction.y, a, c, sense⟩)
            (M.measure ⟨c, a, construction.x, sense⟩) :=
        AngleMeasurement.Axioms.measure_add construction.y c construction.x
          a sense hya hac.symm hxa
      _ = M.add
            (M.measure ⟨construction.y, a, c, sense⟩)
            (M.add
              (M.measure ⟨c, a, b, sense⟩)
              (M.measure ⟨b, a, construction.x, sense⟩)) := by
        rw [AngleMeasurement.Axioms.measure_add c b construction.x
          a sense hac.symm hab.symm hxa]
  change
    M.add
        (M.add
          (M.measure ⟨a, b, c, sense⟩)
          (M.measure ⟨b, c, a, sense⟩))
        (M.measure ⟨c, a, b, sense⟩) =
      M.halfTurn
  calc
    M.add
        (M.add
          (M.measure ⟨a, b, c, sense⟩)
          (M.measure ⟨b, c, a, sense⟩))
        (M.measure ⟨c, a, b, sense⟩) =
        M.add
          (M.measure ⟨a, b, c, sense⟩)
          (M.add
            (M.measure ⟨b, c, a, sense⟩)
            (M.measure ⟨c, a, b, sense⟩)) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add
          (M.add
            (M.measure ⟨b, c, a, sense⟩)
            (M.measure ⟨c, a, b, sense⟩))
          (M.measure ⟨a, b, c, sense⟩) :=
      AngleMeasurement.Axioms.add_comm _ _
    _ = M.add
          (M.measure ⟨b, c, a, sense⟩)
          (M.add
            (M.measure ⟨c, a, b, sense⟩)
            (M.measure ⟨a, b, c, sense⟩)) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add
          (M.measure ⟨construction.y, a, c, sense⟩)
          (M.add
            (M.measure ⟨c, a, b, sense⟩)
            (M.measure ⟨b, a, construction.x, sense⟩)) := by
      rw [hcopy_x, hcopy_y]
    _ = M.measure ⟨construction.y, a, construction.x, sense⟩ := hsplit.symm
    _ = M.halfTurn :=
      AngleMeasurement.Axioms.measure_straight
        construction.y a construction.x sense hya hxa construction.y_a_x

/-- Triangle-angle sum, derived locally from the reflected-copy construction. -/
private theorem triangle_turn (M : AngleMeasurement G) [M.Axioms]
    {a b c : G.Point} (sense : RotationSense)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    TriangleTurn G M a b c sense := by
  by_cases hcol : G.Collinear a b c
  · exact triangle_turn_of_collinear G M sense hab hac hbc hcol
  obtain ⟨copies, hyax⟩ :=
    Soultions.Sharygin.Page13.Problem15.Affine.triangleCopies_aligned G hcol
  exact triangle_turn_of_construction G M sense hab hac hbc {
    x := copies.x
    y := copies.y
    y_a_x := hyax
    ax_bc := copies.ax_bc
    bx_ac := copies.bx_ac
    ay_cb := copies.ay_cb
    cy_ab := copies.cy_ab
    x_opposite_c := copies.x_opposite_c
    y_opposite_b := copies.y_opposite_b
  }

/-- Public problem-local form of the triangle-angle-sum identity. -/
theorem triangle_measure_sum (M : AngleMeasurement G) [M.Axioms]
    {a b c : G.Point} (sense : RotationSense)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    M.add
        (M.add
          (M.measure ⟨a, b, c, sense⟩)
          (M.measure ⟨b, c, a, sense⟩))
        (M.measure ⟨c, a, b, sense⟩) =
      M.halfTurn :=
  triangle_turn G M sense hab hac hbc

omit [G.Axioms] in
private theorem neg_add (M : AngleMeasurement G) [M.Axioms] (x : M.Measure) :
    M.add (M.neg x) x = M.zero := by
  calc
    M.add (M.neg x) x = M.add x (M.neg x) := AngleMeasurement.Axioms.add_comm _ _
    _ = M.zero := AngleMeasurement.Axioms.add_neg x

omit [G.Axioms] in
private theorem add_left_cancel (M : AngleMeasurement G) [M.Axioms] {a b c : M.Measure}
    (h : M.add a b = M.add a c) : b = c := by
  calc
    b = M.add M.zero b := (AngleMeasurement.Axioms.zero_add b).symm
    _ = M.add (M.add (M.neg a) a) b :=
      congrArg (fun x => M.add x b) (neg_add G M a).symm
    _ = M.add (M.neg a) (M.add a b) := AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add (M.neg a) (M.add a c) := congrArg (fun x => M.add (M.neg a) x) h
    _ = M.add (M.add (M.neg a) a) c := (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero c := congrArg (fun x => M.add x c) (neg_add G M a)
    _ = c := AngleMeasurement.Axioms.zero_add c

omit [G.Axioms] in
private theorem eq_sub_of_add_eq (M : AngleMeasurement G) [M.Axioms] {x y z : M.Measure}
    (h : M.add x z = y) : x = M.sub y z := by
  apply add_left_cancel G M (a := z)
  calc
    M.add z x = M.add x z := AngleMeasurement.Axioms.add_comm _ _
    _ = y := h
    _ = M.add y M.zero := (AngleMeasurement.Axioms.add_zero y).symm
    _ = M.add y (M.add z (M.neg z)) :=
      congrArg (fun t => M.add y t) (AngleMeasurement.Axioms.add_neg z).symm
    _ = M.add z (M.add y (M.neg z)) := by
      calc
        M.add y (M.add z (M.neg z)) =
            M.add (M.add y z) (M.neg z) :=
          (AngleMeasurement.Axioms.add_assoc _ _ _).symm
        _ = M.add (M.add z y) (M.neg z) :=
          congrArg (fun t => M.add t (M.neg z)) (AngleMeasurement.Axioms.add_comm y z)
        _ = M.add z (M.add y (M.neg z)) :=
          AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add z (M.sub y z) := rfl

omit [G.Axioms] in
private theorem eq_neg_of_add_eq_zero (M : AngleMeasurement G) [M.Axioms]
    {x y : M.Measure} (h : M.add x y = M.zero) : y = M.neg x := by
  exact add_left_cancel G M (h.trans (AngleMeasurement.Axioms.add_neg x).symm)

omit [G.Axioms] in
private theorem neg_neg (M : AngleMeasurement G) [M.Axioms] (x : M.Measure) :
    M.neg (M.neg x) = x := by
  apply add_left_cancel G M (a := M.neg x)
  calc
    M.add (M.neg x) (M.neg (M.neg x)) = M.zero :=
      AngleMeasurement.Axioms.add_neg (M.neg x)
    _ = M.add (M.neg x) x := (neg_add G M x).symm

omit [G.Axioms] in
private theorem twice_add (M : AngleMeasurement G) [M.Axioms] (x y : M.Measure) :
    M.twice (M.add x y) = M.add (M.twice x) (M.twice y) := by
  calc
    M.twice (M.add x y) = M.add (M.add x y) (M.add x y) := rfl
    _ = M.add x (M.add y (M.add x y)) := AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add x (M.add x (M.add y y)) := by
      rw [← AngleMeasurement.Axioms.add_assoc y x y,
        AngleMeasurement.Axioms.add_comm y x, AngleMeasurement.Axioms.add_assoc]
    _ = M.add (M.add x x) (M.add y y) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add (M.twice x) (M.twice y) := rfl

omit [G.Axioms] in
private theorem add_halfTurns_cancel (M : AngleMeasurement G) [M.Axioms]
    (x y : M.Measure) :
    M.add (M.add x M.halfTurn) (M.add y M.halfTurn) = M.add x y := by
  calc
    M.add (M.add x M.halfTurn) (M.add y M.halfTurn) =
        M.add x (M.add M.halfTurn (M.add y M.halfTurn)) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add x (M.add M.halfTurn (M.add M.halfTurn y)) := by
      rw [AngleMeasurement.Axioms.add_comm y M.halfTurn]
    _ = M.add x (M.add (M.add M.halfTurn M.halfTurn) y) := by
      rw [AngleMeasurement.Axioms.add_assoc M.halfTurn M.halfTurn y]
    _ = M.add x (M.add M.zero y) :=
      congrArg (fun t => M.add x (M.add t y))
        AngleMeasurement.Axioms.twice_halfTurn
    _ = M.add x y := by rw [AngleMeasurement.Axioms.zero_add]

omit [G.Axioms] in
private theorem triangle_turn_rearrange (M : AngleMeasurement G) [M.Axioms]
    {x n e : M.Measure}
    (h : M.add (M.add x (M.neg n)) (M.neg e) = M.halfTurn) :
    M.add x M.halfTurn = M.add e n := by
  have h₁ : M.add x (M.neg n) = M.add M.halfTurn e := by
    calc
      M.add x (M.neg n) = M.sub M.halfTurn (M.neg e) :=
        eq_sub_of_add_eq G M h
      _ = M.add M.halfTurn e := by
        change M.add M.halfTurn (M.neg (M.neg e)) = M.add M.halfTurn e
        rw [neg_neg]
  have h₂ : x = M.add (M.add M.halfTurn e) n := by
    calc
      x = M.add x M.zero := (AngleMeasurement.Axioms.add_zero x).symm
      _ = M.add x (M.add (M.neg n) n) :=
        congrArg (M.add x) (neg_add G M n).symm
      _ = M.add (M.add x (M.neg n)) n :=
        (AngleMeasurement.Axioms.add_assoc _ _ _).symm
      _ = M.add (M.add M.halfTurn e) n := congrArg (fun t => M.add t n) h₁
  calc
    M.add x M.halfTurn = M.add (M.add (M.add M.halfTurn e) n) M.halfTurn :=
      congrArg (fun t => M.add t M.halfTurn) h₂
    _ = M.add (M.add M.halfTurn (M.add e n)) M.halfTurn := by
      rw [AngleMeasurement.Axioms.add_assoc M.halfTurn e n]
    _ = M.add M.halfTurn (M.add (M.add e n) M.halfTurn) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add M.halfTurn (M.add M.halfTurn (M.add e n)) := by
      rw [AngleMeasurement.Axioms.add_comm (M.add e n) M.halfTurn]
    _ = M.add (M.add M.halfTurn M.halfTurn) (M.add e n) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero (M.add e n) :=
      congrArg (fun t => M.add t (M.add e n)) AngleMeasurement.Axioms.twice_halfTurn
    _ = M.add e n := AngleMeasurement.Axioms.zero_add _

omit [G.Axioms] in
private theorem exterior_rearrange (M : AngleMeasurement G) [M.Axioms]
    {x d : M.Measure} (h : M.add x d = M.halfTurn) :
    M.neg d = M.add x M.halfTurn := by
  have hx : x = M.add M.halfTurn (M.neg d) :=
    eq_sub_of_add_eq G M h
  symm
  calc
    M.add x M.halfTurn = M.add (M.add M.halfTurn (M.neg d)) M.halfTurn :=
      congrArg (fun t => M.add t M.halfTurn) hx
    _ = M.add M.halfTurn (M.add (M.neg d) M.halfTurn) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add M.halfTurn (M.add M.halfTurn (M.neg d)) := by
      rw [AngleMeasurement.Axioms.add_comm (M.neg d) M.halfTurn]
    _ = M.add (M.add M.halfTurn M.halfTurn) (M.neg d) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero (M.neg d) :=
      congrArg (fun t => M.add t (M.neg d)) AngleMeasurement.Axioms.twice_halfTurn
    _ = M.neg d := AngleMeasurement.Axioms.zero_add _

omit [G.Axioms] in
private theorem isosceles_turn_rearrange (M : AngleMeasurement G) [M.Axioms]
    {x c : M.Measure}
    (h : M.add (M.twice x) (M.neg c) = M.halfTurn) :
    c = M.add (M.twice x) M.halfTurn := by
  have hx : M.twice x = M.add M.halfTurn c := by
    calc
      M.twice x = M.sub M.halfTurn (M.neg c) := eq_sub_of_add_eq G M h
      _ = M.add M.halfTurn c := by
        change M.add M.halfTurn (M.neg (M.neg c)) = M.add M.halfTurn c
        rw [neg_neg]
  symm
  calc
    M.add (M.twice x) M.halfTurn =
        M.add (M.add M.halfTurn c) M.halfTurn :=
      congrArg (fun t => M.add t M.halfTurn) hx
    _ = M.add M.halfTurn (M.add c M.halfTurn) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add M.halfTurn (M.add M.halfTurn c) := by
      rw [AngleMeasurement.Axioms.add_comm c M.halfTurn]
    _ = M.add (M.add M.halfTurn M.halfTurn) c :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero c :=
      congrArg (fun t => M.add t c) AngleMeasurement.Axioms.twice_halfTurn
    _ = c := AngleMeasurement.Axioms.zero_add c

omit [G.Axioms] in
private theorem reverse_angle_is_neg (M : AngleMeasurement G) [M.Axioms]
    {a b o : G.Point} (sense : RotationSense) (ha : a ≠ o) (hb : b ≠ o) :
    M.measure ⟨b, o, a, sense⟩ = M.neg (M.measure ⟨a, o, b, sense⟩) := by
  apply eq_neg_of_add_eq_zero G M
  exact
    (AngleMeasurement.Axioms.measure_add a b a o sense ha hb ha).symm.trans
      (AngleMeasurement.Axioms.measure_refl a o sense)

omit [G.Axioms] in
private theorem straight_angle_split (M : AngleMeasurement G) [M.Axioms]
    {a b c d : G.Point} (sense : RotationSense) (ha : a ≠ b) (hc : c ≠ b)
    (hd : d ≠ b)
    (h_between : G.Bet a b c) :
    M.add (M.measure ⟨a, b, d, sense⟩) (M.measure ⟨d, b, c, sense⟩) =
      M.halfTurn := by
  rw [← AngleMeasurement.Axioms.measure_add a d c b sense ha hd hc]
  exact AngleMeasurement.Axioms.measure_straight a b c sense ha hc h_between

omit [G.Axioms] in
private theorem exterior_angle_from_triangle_turn (M : AngleMeasurement G) [M.Axioms]
    {v a b d : G.Point} (sense : RotationSense)
    (hva : v ≠ a) (hba : b ≠ a) (hda : d ≠ a)
    (hvd : v ≠ d) (had : a ≠ d) (hdv : d ≠ v) (hav : a ≠ v)
    (h_between : G.Bet v a b)
    (h_turn :
      M.add
          (M.add
            (M.measure ⟨v, a, d, sense⟩)
            (M.measure ⟨a, d, v, sense⟩))
          (M.measure ⟨d, v, a, sense⟩) =
        M.halfTurn) :
    M.measure ⟨b, a, d, sense⟩ =
      M.add (M.measure ⟨a, v, d, sense⟩) (M.measure ⟨v, d, a, sense⟩) := by
  have h_turn' :
      M.add
          (M.add
            (M.measure ⟨v, a, d, sense⟩)
            (M.neg (M.measure ⟨v, d, a, sense⟩)))
          (M.neg (M.measure ⟨a, v, d, sense⟩)) =
        M.halfTurn := by
    rw [reverse_angle_is_neg G M sense hvd had,
      reverse_angle_is_neg G M sense hav hdv] at h_turn
    exact h_turn
  have h_exterior :
      M.measure ⟨b, a, d, sense⟩ =
        M.add (M.measure ⟨v, a, d, sense⟩) M.halfTurn := by
    calc
      M.measure ⟨b, a, d, sense⟩ =
          M.neg (M.measure ⟨d, a, b, sense⟩) :=
        reverse_angle_is_neg G M sense hda hba
      _ = M.add (M.measure ⟨v, a, d, sense⟩) M.halfTurn :=
        exterior_rearrange G M
          (straight_angle_split G M sense hva hba hda h_between)
  calc
    M.measure ⟨b, a, d, sense⟩ =
        M.add (M.measure ⟨v, a, d, sense⟩) M.halfTurn := h_exterior
    _ = M.add (M.measure ⟨a, v, d, sense⟩) (M.measure ⟨v, d, a, sense⟩) :=
      triangle_turn_rearrange G M h_turn'

omit [G.Axioms] in
private theorem reverse_sense_measure (M : AngleMeasurement G) [M.Axioms]
    {a b o : G.Point} (sense : RotationSense) (ha : a ≠ o) (hb : b ≠ o) :
    M.measure ⟨a, o, b, sense.reverse⟩ = M.measure ⟨b, o, a, sense⟩ := by
  cases sense with
  | clockwise =>
      exact (AngleMeasurement.Axioms.reverse_sense b a o hb ha).symm
  | counterclockwise =>
      exact AngleMeasurement.Axioms.reverse_sense a b o ha hb

private theorem isosceles_base_angles_cyclic (M : AngleMeasurement G) [M.Axioms]
    {a b c : G.Point} (sense : RotationSense) (h : G.Congruent a b a c)
    (hac : a ≠ c) (hbc : b ≠ c) :
    M.measure ⟨a, b, c, sense⟩ = M.measure ⟨b, c, a, sense⟩ := by
  calc
    M.measure ⟨a, b, c, sense⟩ =
        M.measure ⟨a, c, b, sense.reverse⟩ :=
      isosceles_base_angles G M sense h
    _ = M.measure ⟨b, c, a, sense⟩ :=
      reverse_sense_measure G M sense hac hbc

private theorem inscribed_angle_from_triangle_turn (M : AngleMeasurement G) [M.Axioms]
    {circle : Circle G} {p q r : G.Point} (sense : RotationSense)
    (hp : G.OnCircle circle p) (hq : G.OnCircle circle q)
    (hr : G.OnCircle circle r) (hpr : p ≠ r) (hrq : r ≠ q)
    (h_turn_pr : TriangleTurn G M circle.center p r sense)
    (h_turn_rq : TriangleTurn G M circle.center r q sense) :
    M.twice (M.measure ⟨p, r, q, sense⟩) =
      M.measure ⟨p, circle.center, q, sense⟩ := by
  have hpo : p ≠ circle.center := (center_ne_onCircle G hp).symm
  have hqo : q ≠ circle.center := (center_ne_onCircle G hq).symm
  have hro : r ≠ circle.center := (center_ne_onCircle G hr).symm
  have hor : circle.center ≠ r := center_ne_onCircle G hr
  have hqr : q ≠ r := hrq.symm
  have hbase_pr :
      M.measure ⟨circle.center, p, r, sense⟩ =
        M.measure ⟨p, r, circle.center, sense⟩ :=
    isosceles_base_angles_cyclic G M sense
      (circle_radii_congruent G hp hr) (center_ne_onCircle G hr) hpr
  have hbase_rq :
      M.measure ⟨circle.center, r, q, sense⟩ =
        M.measure ⟨r, q, circle.center, sense⟩ :=
    isosceles_base_angles_cyclic G M sense
      (circle_radii_congruent G hr hq) (center_ne_onCircle G hq) hrq
  have hcentral_pr :
      M.measure ⟨p, circle.center, r, sense⟩ =
        M.add
          (M.twice (M.measure ⟨circle.center, p, r, sense⟩))
          M.halfTurn := by
    apply isosceles_turn_rearrange G M
    change
      M.add
          (M.add
            (M.measure ⟨circle.center, p, r, sense⟩)
            (M.measure ⟨p, r, circle.center, sense⟩))
          (M.measure ⟨r, circle.center, p, sense⟩) =
        M.halfTurn at h_turn_pr
    rw [← hbase_pr, reverse_angle_is_neg G M sense hpo hro] at h_turn_pr
    exact h_turn_pr
  have hcentral_rq :
      M.measure ⟨r, circle.center, q, sense⟩ =
        M.add
          (M.twice (M.measure ⟨circle.center, r, q, sense⟩))
          M.halfTurn := by
    apply isosceles_turn_rearrange G M
    change
      M.add
          (M.add
            (M.measure ⟨circle.center, r, q, sense⟩)
            (M.measure ⟨r, q, circle.center, sense⟩))
          (M.measure ⟨q, circle.center, r, sense⟩) =
        M.halfTurn at h_turn_rq
    rw [← hbase_rq, reverse_angle_is_neg G M sense hro hqo] at h_turn_rq
    exact h_turn_rq
  calc
    M.twice (M.measure ⟨p, r, q, sense⟩) =
        M.twice
          (M.add
            (M.measure ⟨p, r, circle.center, sense⟩)
            (M.measure ⟨circle.center, r, q, sense⟩)) := by
      exact congrArg M.twice
        (AngleMeasurement.Axioms.measure_add p circle.center q r sense
          hpr hor hqr)
    _ = M.add
          (M.twice (M.measure ⟨p, r, circle.center, sense⟩))
          (M.twice (M.measure ⟨circle.center, r, q, sense⟩)) :=
      twice_add G M _ _
    _ = M.add
          (M.twice (M.measure ⟨circle.center, p, r, sense⟩))
          (M.twice (M.measure ⟨circle.center, r, q, sense⟩)) := by
      rw [← hbase_pr]
    _ = M.add
          (M.add
            (M.twice (M.measure ⟨circle.center, p, r, sense⟩))
            M.halfTurn)
          (M.add
            (M.twice (M.measure ⟨circle.center, r, q, sense⟩))
            M.halfTurn) := by
      symm
      exact add_halfTurns_cancel G M _ _
    _ = M.add
          (M.measure ⟨p, circle.center, r, sense⟩)
          (M.measure ⟨r, circle.center, q, sense⟩) := by
      rw [← hcentral_pr, ← hcentral_rq]
    _ = M.measure ⟨p, circle.center, q, sense⟩ :=
      (AngleMeasurement.Axioms.measure_add p r q circle.center sense
        hpo hro hqo).symm

/-- The inscribed-angle identity in the exact form needed by the secant-product proof. -/
theorem inscribed_angle (M : AngleMeasurement G) [M.Axioms]
    {circle : Circle G} {p q r : G.Point} (sense : RotationSense)
    (hp : G.OnCircle circle p) (hq : G.OnCircle circle q)
    (hr : G.OnCircle circle r) (hpr : p ≠ r) (hrq : r ≠ q) :
    M.twice (M.measure ⟨p, r, q, sense⟩) =
      M.measure ⟨p, circle.center, q, sense⟩ := by
  apply inscribed_angle_from_triangle_turn G M sense
    hp hq hr hpr hrq
  · exact triangle_turn G M sense
      (center_ne_onCircle G hp)
      (center_ne_onCircle G hr)
      hpr
  · exact triangle_turn G M sense
      (center_ne_onCircle G hr)
      (center_ne_onCircle G hq)
      hrq

end LocalFacts

end Soultions.Sharygin.Page13.Problem15
