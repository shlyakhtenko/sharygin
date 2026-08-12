import Sharygin14Problem19.PitotComparison

/-!
# Direct incenter consequences for problem 19

The auxiliary points forced by Pitot's equality form three isosceles triangles.  This file
connects those equalities to the two already constructed adjacent angle bisectors.
-/

namespace Soultions.Sharygin.Page14.Problem19.DirectIncenter

open Euclid Plane
open Soultions.Sharygin.Page14.Problem19.Tarski
open Soultions.Sharygin.Page14.Problem19.Midpoint
open Soultions.Sharygin.Page14.Problem19.Affine
open Soultions.Sharygin.Page14.Problem19.Scalar
open Soultions.Sharygin.Page14.Problem19.Similarity
open Soultions.Sharygin.Page14.Problem19.Projection
open Soultions.Sharygin.Page14.Problem19.Tangent
open Soultions.Sharygin.Page14.Problem19.TangencyLengths
open Soultions.Sharygin.Page14.Problem19.Configuration
open Soultions.Sharygin.Page14.Problem19.Construction
open Soultions.Sharygin.Page14.Problem19.Construction.BisectorAxis
open Soultions.Sharygin.Page14.Problem19.InitialCircle
open Soultions.Sharygin.Page14.Problem19.ParallelAngles
open Soultions.Sharygin.Page14.Problem19.PitotComparison

variable (G : Plane) [G.Axioms]

/-- Equal segments laid off on the two boundary rays remain equidistant from every point on
the corresponding angle-bisector ray.  Endpoint coincidences are included explicitly. -/
theorem equidistant_boundary_pair
    {a b c o x y : G.Point}
    (axis : BisectorAxis G a b c)
    (ho : G.SameRay a axis.midpoint o)
    (hx : x = a ∨ G.SameRay a b x)
    (hy : y = a ∨ G.SameRay a c y)
    (hxy : G.Congruent a x a y) :
    G.Congruent o x o y := by
  rcases hx with hxa | hx
  · subst x
    have hay_zero : G.Congruent a a a y := hxy
    have hay : a = y :=
      Plane.Axioms.congruenceIdentity a y a (congruent_symm G hay_zero)
    subst y
    exact congruent_refl G o a
  rcases hy with hya | hy
  · subst y
    have hax_zero : G.Congruent a x a a := hxy
    have hax : x = a := Plane.Axioms.congruenceIdentity x a a
      (congruent_trans G (Plane.Axioms.congruenceReversal x a) hax_zero)
    subst x
    exact congruent_refl G o a
  have hangle : SameAngle G x a o o a y :=
    sameAngle_change_rays G
      hx
      ho
      ho
      hy
      axis.halves_angle
  have hthird : G.Congruent x o y o :=
    triangle_sas_third_side G
      (o := a) (a := x) (b := o)
      (p := a) (c := y) (d := o)
      hx.2.1 ho.2.1 hxy (congruent_refl G a o)
      (SameAngle.trans hangle (SameAngle.reverse (G := G)))
  exact congruent_trans G
    (Plane.Axioms.congruenceReversal o x)
    (congruent_trans G hthird
      (Plane.Axioms.congruenceReversal y o))

/-- Equal segments on the two rays opposite an angle's boundaries have the same symmetry
axis as equal segments on the boundary rays themselves. -/
theorem equidistant_opposite_boundary_pair
    {a b c o x y : G.Point}
    (axis : BisectorAxis G a b c)
    (ho : G.SameRay a axis.midpoint o)
    (hbx : G.Bet b a x)
    (hcy : G.Bet c a y)
    (hxy : G.Congruent a x a y) :
    G.Congruent o x o y := by
  have hba : b ≠ a := axis.left_on_ray.1
  have hca : c ≠ a := axis.right_on_ray.1
  by_cases hxa : x = a
  · subst x
    have hay : a = y := Plane.Axioms.congruenceIdentity a y a
      (congruent_symm G hxy)
    subst y
    exact congruent_refl G o a
  by_cases hya : y = a
  · subst y
    have hax : x = a := Plane.Axioms.congruenceIdentity x a a
      (congruent_trans G (Plane.Axioms.congruenceReversal x a) hxy)
    exact (hxa hax).elim
  have hbase : SameAngle G b a o o a c :=
    sameAngle_change_rays G
      (sameRay_refl G hba) ho ho (sameRay_refl G hca) axis.halves_angle
  have hfirst : SameAngle G b a o c a o :=
    SameAngle.trans hbase (SameAngle.reverse (G := G))
  have hsupplemented : SameAngle G x a o y a o :=
    sameAngle_supplements G
      ⟨hba, ho.2.1⟩ ⟨hca, ho.2.1⟩ hxa hya hbx hcy hfirst
  have hthird : G.Congruent x o y o :=
    triangle_sas_third_side G
      (o := a) (a := x) (b := o)
      (p := a) (c := y) (d := o)
      hxa ho.2.1 hxy (congruent_refl G a o) hsupplemented
  exact congruent_trans G
    (Plane.Axioms.congruenceReversal o x)
    (congruent_trans G hthird
      (Plane.Axioms.congruenceReversal y o))

/-- A point between `u` and `a` is either `a` or lies on the ray from `a` through `u`. -/
theorem endpoint_or_sameRay_of_between
    {u x a : G.Point}
    (hua : u ≠ a)
    (h : G.Bet u x a) :
    x = a ∨ G.SameRay a u x := by
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxu : x = u
  · subst x
    exact Or.inr (sameRay_refl G hua)
  · exact Or.inr
      (sameRay_symm G
        (sameRay_from_near_endpoint G (bet_symm G h)
          (fun h => hxa h.symm) hxu))

/-- In the `CD ≤ AD` branch the first two bisectors make `O` equidistant from `C` and the
point `E` laid off on `DA`. -/
theorem longAD_center_equidistant_CE
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (axes : BisectorIntersection G q)
    (hforward :
      G.SameRay q.a axes.axisA.midpoint axes.point ∧
      G.SameRay q.b axes.axisB.midpoint axes.point)
    (construction : LongADConstruction G q) :
    G.Congruent axes.point construction.e axes.point q.c := by
  have he_ray := endpoint_or_sameRay_of_between G q.d_ne_a construction.e_between_DA
  have hf_ray := endpoint_or_sameRay_of_between G q.a_ne_b.symm construction.f_between_BA
  have hoe_of : G.Congruent axes.point construction.e axes.point construction.f :=
    equidistant_boundary_pair G axes.axisA hforward.1
      he_ray hf_ray construction.ae_eq_af
  have hf_on_BA : construction.f = q.b ∨ G.SameRay q.b q.a construction.f := by
    by_cases hfb : construction.f = q.b
    · exact Or.inl hfb
    by_cases hfa : construction.f = q.a
    · exact Or.inr (by simpa [hfa] using sameRay_refl G q.a_ne_b)
    · exact Or.inr
        (sameRay_symm G
          (sameRay_from_near_endpoint G construction.f_between_BA
            (fun h => hfb h.symm) hfa))
  have hoc_of : G.Congruent axes.point construction.f axes.point q.c :=
    equidistant_boundary_pair G axes.axisB hforward.2
      hf_on_BA (Or.inr (sameRay_refl G q.b_ne_c.symm))
      construction.bf_eq_bc
  exact congruent_trans G hoe_of hoc_of

private theorem same_side_BC_of_AD
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L) :
    ¬G.OppositeSides q.a q.d q.b q.c := by
  intro hopposite
  have horientation := Plane.Axioms.orientation_opposite_sides (G := G) hopposite
  have hb : G.Orientation q.a q.d q.b = some q.sense.reverse := by
    calc
      _ = (G.Orientation q.d q.a q.b).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap _ _ _
      _ = some q.sense.reverse := by rw [q.turnDAB]; rfl
  have hc : G.Orientation q.a q.d q.c = some q.sense.reverse := by
    calc
      _ = (G.Orientation q.d q.a q.c).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap _ _ _
      _ = (G.Orientation q.c q.d q.a).map RotationSense.reverse := by
        exact congrArg (Option.map RotationSense.reverse)
          (Plane.Axioms.orientation_cyclic q.c q.d q.a).symm
      _ = some q.sense.reverse := by rw [q.turnCDA]; rfl
  rw [hb, hc] at horientation
  cases hs : q.sense <;> simp [hs, RotationSense.reverse] at horientation

private theorem same_side_AD_of_BC
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L) :
    ¬G.OppositeSides q.b q.c q.a q.d := by
  intro hopposite
  have horientation := Plane.Axioms.orientation_opposite_sides (G := G) hopposite
  have ha : G.Orientation q.b q.c q.a = some q.sense := by
    calc
      _ = G.Orientation q.a q.b q.c :=
        (Plane.Axioms.orientation_cyclic q.a q.b q.c).symm
      _ = some q.sense := q.turnABC
  rw [ha, q.turnBCD] at horientation
  cases hs : q.sense <;> simp [hs, RotationSense.reverse] at horientation

/-- In the `CD ≤ AD` branch the center lies on the forward internal bisector at `D`. -/
theorem longAD_center_on_D_bisector
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (axes : BisectorIntersection G q)
    (hforward :
      G.SameRay q.a axes.axisA.midpoint axes.point ∧
      G.SameRay q.b axes.axisB.midpoint axes.point)
    (construction : LongADConstruction G q)
    (axisD : BisectorAxis G q.d q.a q.c) :
    G.SameRay q.d axisD.midpoint axes.point := by
  have he_ne_d : construction.e ≠ q.d := by
    intro hed
    have hzero : G.Congruent q.d q.d q.d q.c := by
      simpa [hed] using construction.de_eq_dc
    exact q.c_ne_d
      (Plane.Axioms.congruenceIdentity q.d q.c q.d
        (congruent_symm G hzero)).symm
  have he_on_DA : G.SameRay q.d q.a construction.e := by
    by_cases hea : construction.e = q.a
    · simpa [hea] using sameRay_refl G q.d_ne_a.symm
    · exact sameRay_symm G
        (sameRay_from_near_endpoint G construction.e_between_DA
          (fun h => he_ne_d h.symm) hea)
  have ho_ne_d : axes.point ≠ q.d := by
    intro hod
    have hline : G.Collinear q.a q.d axes.axisA.midpoint := by
      simpa only [hod] using collinear_swap_last G hforward.1.2.2.1
    exact (axes.axisA.strictInterior
      (fun h => q.dab_noncollinear (collinear_swap G h))).off_first_boundary hline
  have hoe_oc : G.Congruent axes.point construction.e axes.point q.c :=
    longAD_center_equidistant_CE G L q axes hforward construction
  have hmid_equidistant :
      G.Congruent axisD.midpoint construction.e axisD.midpoint q.c :=
    equidistant_boundary_pair G axisD
      (sameRay_refl G axisD.midpoint_ne_vertex)
      (Or.inr he_on_DA)
      (Or.inr (sameRay_refl G q.c_ne_d))
      construction.de_eq_dc
  have he_ne_c : construction.e ≠ q.c := by
    intro hec
    have hdca : G.Collinear q.d q.c q.a := by
      simpa only [hec] using (Or.inl construction.e_between_DA :
        G.Collinear q.d construction.e q.a)
    exact q.cda_noncollinear (collinear_swap G hdca)
  obtain ⟨m, hm⟩ := midpoint_exists G construction.e q.c
  have hmDO : G.Collinear m q.d axes.point :=
    equidistant_points_collinear_with_midpoint G he_ne_c hm
      construction.de_eq_dc hoe_oc
  have hmDaxis : G.Collinear m q.d axisD.midpoint :=
    equidistant_points_collinear_with_midpoint G he_ne_c hm
      construction.de_eq_dc hmid_equidistant
  have hm_ne_d : m ≠ q.d := by
    intro hmd
    subst m
    have hdec : G.Collinear q.d construction.e q.c :=
      collinear_swap G (Or.inl hm.1)
    have hdea : G.Collinear q.d construction.e q.a :=
      Or.inl construction.e_between_DA
    exact q.cda_noncollinear
      (collinear_swap G (collinear_trans G he_ne_d.symm hdec hdea))
  have hDaxisO : G.Collinear q.d axisD.midpoint axes.point :=
    collinear_three_on_line G hm_ne_d
      (collinear_refl_right G m q.d) hmDaxis hmDO
  rcases sameRay_or_opposite_of_collinear G
      axisD.midpoint_ne_vertex ho_ne_d hDaxisO with hsame | hopposite
  · exact hsame
  · have haxisOffAD : ¬G.Collinear q.a q.d axisD.midpoint := by
      intro h
      exact (axisD.strictInterior
        (fun h => q.cda_noncollinear
          (collinear_cyclic G (collinear_cyclic G h)))).off_first_boundary
        (collinear_swap G h)
    have hoOffAD : ¬G.Collinear q.a q.d axes.point := by
      intro h
      have haxisLine : G.Collinear q.a q.d axes.axisA.midpoint :=
        collinear_three_on_line G hforward.1.2.1.symm
          (collinear_cyclic G (collinear_refl_left G q.a axes.point))
          (collinear_swap_last G h)
          (collinear_swap_last G axes.point_on_axisA)
      exact (axes.axisA.strictInterior
        (fun h' => q.dab_noncollinear (collinear_swap G h'))).off_first_boundary haxisLine
    have haxisSameC : ¬G.OppositeSides q.a q.d axisD.midpoint q.c := by
      intro h
      exact (axisD.strictInterior
        (fun h => q.cda_noncollinear
          (collinear_cyclic G (collinear_cyclic G h)))).with_second_boundary
        (oppositeSides_swap_line G h)
    have hOSameB : ¬G.OppositeSides q.a q.d axes.point q.b := by
      have haxisSameB :=
        (axes.axisA.strictInterior
          (fun h => q.dab_noncollinear (collinear_swap G h))).with_second_boundary
      have haxisSameO := not_oppositeSides_of_sameRay G hforward.1
        (axes.axisA.strictInterior
          (fun h => q.dab_noncollinear (collinear_swap G h))).off_first_boundary
      exact not_oppositeSides_trans G
        (axes.axisA.strictInterior
          (fun h => q.dab_noncollinear (collinear_swap G h))).off_first_boundary
        (fun h => haxisSameO (oppositeSides_symm G h))
        haxisSameB
    have hOSameC : ¬G.OppositeSides q.a q.d axes.point q.c :=
      not_oppositeSides_trans G
        (by
          intro h
          exact q.dab_noncollinear (collinear_swap G h))
        hOSameB (same_side_BC_of_AD G q)
    have haxisO_not : ¬G.OppositeSides q.a q.d axisD.midpoint axes.point :=
      not_oppositeSides_trans G
        (by
          intro h
          exact q.cda_noncollinear
            (collinear_cyclic G (collinear_swap_last G h)))
        haxisSameC
        (fun h => hOSameC (oppositeSides_symm G h))
    exact False.elim (haxisO_not
      ⟨haxisOffAD, hoOffAD, q.d,
        collinear_refl_right G q.a q.d, hopposite⟩)

/-- A tangent contact, together with its supporting side line, supplies the same symmetric
perpendicular-foot data used by the projection construction. -/
theorem projectionData_of_tangent
    {circle : Circle G}
    {contact through p q : G.Point}
    (htangent : G.TangentAt circle contact through)
    (hthrough : G.Collinear p q through)
    (hcontact : G.Collinear p q contact) :
    ∃ data : ProjectionData G circle.center p q, data.foot = contact := by
  obtain ⟨right, hreflected⟩ := pointReflection_exists G contact through
  have hequal : G.Congruent circle.center through circle.center right :=
    tangent_symmetric_equidistant G htangent hreflected
  have hoff : ¬G.Collinear through contact circle.center := by
    intro h
    exact tangent_center_off_line G htangent (collinear_cyclic G h)
  have hcenter_ne : circle.center ≠ contact :=
    center_ne_onCircle G htangent.2.1
  exact ⟨{
    foot := contact
    left := through
    right := right
    reflected := hreflected
    apex_equidistant := hequal
    apex_off_baseline := hoff
    center_ne_foot := hcenter_ne
    left_on_line := hthrough
    foot_on_line := hcontact
  }, rfl⟩

/-- In the `CD ≤ AD` branch the original contact on the ray `AD` lies on the finite side. -/
theorem longAD_contactAD_between
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (axes : BisectorIntersection G q)
    (hforward :
      G.SameRay q.a axes.axisA.midpoint axes.point ∧
      G.SameRay q.b axes.axisB.midpoint axes.point)
    (construction : LongADConstruction G q)
    (axisD : BisectorAxis G q.d q.a q.c)
    (data : ThreeRayTangency G q)
    (hcircle : data.circle.center = axes.point) :
    G.Bet q.a data.contactAD q.d := by
  have hcontactLine : G.Collinear q.a q.d data.contactAD :=
    data.contactAD_ray.2.2.1
  obtain ⟨projection, hfoot⟩ := projectionData_of_tangent G data.tangentAD
    (collinear_cyclic G (collinear_refl_left G q.a q.d)) hcontactLine
  have hDforward : G.SameRay q.d axisD.midpoint data.circle.center := by
    rw [hcircle]
    exact longAD_center_on_D_bisector G L q axes hforward construction axisD
  have hleftD : G.Collinear projection.left projection.foot q.d :=
    collinear_three_on_line G q.d_ne_a.symm
      projection.left_on_line projection.foot_on_line
      (collinear_refl_right G q.a q.d)
  have hleftA : G.Collinear projection.left projection.foot q.a :=
    collinear_three_on_line G q.d_ne_a.symm
      projection.left_on_line projection.foot_on_line
      (collinear_cyclic G (collinear_refl_left G q.a q.d))
  have hnotBeyondD' : ¬G.Bet projection.foot q.d q.a :=
    projection_not_behind_bisected_vertex G M L
      (bisectorAxis_swap G axisD)
      (fun h => q.cda_noncollinear
        (collinear_swap G h))
      hDforward projection hleftD hleftA
  have hnotBeyondD : ¬G.Bet data.contactAD q.d q.a := by
    simpa only [hfoot] using hnotBeyondD'
  rcases sameRay_order G data.contactAD_ray with hADcontact | hAcontactD
  · exact False.elim (hnotBeyondD (bet_symm G hADcontact))
  · exact hAcontactD

/-- The newly established bisector at `D` turns the known `AD` tangent into a tangent on the
forward ray `DC`. -/
theorem longAD_fourth_ray_tangent
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (axes : BisectorIntersection G q)
    (hforward :
      G.SameRay q.a axes.axisA.midpoint axes.point ∧
      G.SameRay q.b axes.axisB.midpoint axes.point)
    (construction : LongADConstruction G q)
    (axisD : BisectorAxis G q.d q.a q.c)
    (data : ThreeRayTangency G q)
    (hcircle : data.circle.center = axes.point) :
    ∃ contactCD,
      G.SameRay q.d q.c contactCD ∧
      G.TangentAt data.circle contactCD q.d := by
  have hADbetween := longAD_contactAD_between G M L q axes hforward
    construction axisD data hcircle
  have hcontact_ne_d : data.contactAD ≠ q.d := by
    obtain ⟨projection, hfoot⟩ := projectionData_of_tangent G data.tangentAD
      (collinear_cyclic G (collinear_refl_left G q.a q.d))
      data.contactAD_ray.2.2.1
    have hDforward : G.SameRay q.d axisD.midpoint data.circle.center := by
      rw [hcircle]
      exact longAD_center_on_D_bisector G L q axes hforward construction axisD
    have hleftD : G.Collinear projection.left projection.foot q.d :=
      collinear_three_on_line G q.d_ne_a.symm
        projection.left_on_line projection.foot_on_line
        (collinear_refl_right G q.a q.d)
    have hnotBeyond := projection_not_behind_bisected_vertex G M L
      (bisectorAxis_swap G axisD)
      (fun h => q.cda_noncollinear
        (collinear_swap G h))
      hDforward projection hleftD
      (collinear_three_on_line G q.d_ne_a.symm
        projection.left_on_line projection.foot_on_line
        (collinear_cyclic G (collinear_refl_left G q.a q.d)))
    intro hcontactD
    apply hnotBeyond
    rw [hfoot, hcontactD]
    exact bet_start_refl G q.d q.a
  have htangentD : G.TangentAt data.circle data.contactAD q.d :=
    tangent_rebase G data.tangentAD hcontact_ne_d
      (collinear_cyclic G
        (collinear_cyclic G data.contactAD_ray.2.2.1))
  have hcontactRayD : G.SameRay q.d q.a data.contactAD :=
    sameRay_symm G
      (sameRay_from_near_endpoint G (bet_symm G hADbetween)
        hcontact_ne_d.symm data.contactAD_ray.2.1)
  have hDforward : G.SameRay q.d axisD.midpoint data.circle.center := by
    rw [hcircle]
    exact longAD_center_on_D_bisector G L q axes hforward construction axisD
  exact other_tangent_on_other_bisector_side G M L
    (bisectorAxis_swap G axisD)
    (fun h => q.cda_noncollinear
      (collinear_swap G h))
    hDforward rfl hcontactRayD htangentD

/-- After the `AD` contact is known to be finite, Pitot's equality reduces to a balance of
the two remaining tangent lengths. -/
theorem outer_contact_balance
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (data : ThreeRayTangency G q)
    {contactCD : G.Point}
    (hcontactAD : G.Bet q.a data.contactAD q.d)
    (hcontactCDRay : G.SameRay q.d q.c contactCD)
    (htangentCD : G.TangentAt data.circle contactCD q.d) :
    L.scalar.add (L.length q.b data.contactBC) (L.length q.c q.d) =
      L.scalar.add (L.length q.d contactCD) (L.length q.b q.c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have ha : L.length q.a data.contactAB = L.length q.a data.contactAD :=
    equal_tangent_lengths G M L data.tangentAB_atA data.tangentAD
      (collinear_refl_right G data.contactAB q.a)
      (collinear_refl_right G data.contactAD q.a)
  have hb : L.length q.b data.contactAB = L.length q.b data.contactBC :=
    equal_tangent_lengths G M L data.tangentAB_atB data.tangentBC
      (collinear_refl_right G data.contactAB q.b)
      (collinear_refl_right G data.contactBC q.b)
  have hd : L.length q.d data.contactAD = L.length q.d contactCD :=
    equal_tangent_lengths G M L data.tangentAD htangentCD
      (collinear_swap G (Or.inl hcontactAD))
      (collinear_refl_right G contactCD q.d)
  have hab : L.length q.a q.b =
      L.scalar.add (L.length q.a data.contactAB)
        (L.length data.contactAB q.b) :=
    LengthMeasurement.Axioms.bet_additive
      q.a data.contactAB q.b data.contactAB_between
  have had : L.length q.a q.d =
      L.scalar.add (L.length q.a data.contactAD)
        (L.length data.contactAD q.d) :=
    LengthMeasurement.Axioms.bet_additive
      q.a data.contactAD q.d hcontactAD
  have hp := q.pitot
  rw [hab, had,
    LengthMeasurement.Axioms.length_symm data.contactAB q.b,
    LengthMeasurement.Axioms.length_symm data.contactAD q.d,
    ha, hb, hd] at hp
  apply add_left_cancel L.scalar
    (x := L.length q.a data.contactAD)
  calc
    L.scalar.add (L.length q.a data.contactAD)
        (L.scalar.add (L.length q.b data.contactBC) (L.length q.c q.d)) =
      L.scalar.add
        (L.scalar.add (L.length q.a data.contactAD)
          (L.length q.b data.contactBC))
        (L.length q.c q.d) :=
          (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = L.scalar.add
        (L.scalar.add (L.length q.a data.contactAD)
          (L.length q.d contactCD))
        (L.length q.b q.c) := hp
    _ = L.scalar.add (L.length q.a data.contactAD)
        (L.scalar.add (L.length q.d contactCD) (L.length q.b q.c)) :=
          OrderedScalar.Axioms.add_assoc _ _ _

private theorem nonnegative_pair_zero
    (S : OrderedScalar) [S.Axioms]
    {x y : S.Carrier}
    (hx : S.le S.zero x)
    (hy : S.le S.zero y)
    (hxy : S.add x y = S.zero) :
    x = S.zero ∧ y = S.zero := by
  have hy_le_zero : S.le y S.zero := by
    have h := OrderedScalar.Axioms.add_le_add_right S.zero x y hx
    rw [OrderedScalar.Axioms.zero_add, hxy] at h
    exact h
  have hy_zero := OrderedScalar.Axioms.le_antisymm y S.zero hy_le_zero hy
  have hx_zero : x = S.zero := by
    rw [hy_zero, OrderedScalar.Axioms.add_zero] at hxy
    exact hxy
  exact ⟨hx_zero, hy_zero⟩

/-- Pitot's equality rules out exactly one of the two outer contacts passing its far
endpoint.  Thus the contacts are either both finite or both beyond `C`; endpoint contacts
are included in the finite alternative. -/
theorem outer_contacts_finite_or_beyond
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (data : ThreeRayTangency G q)
    {contactCD : G.Point}
    (hcontactCDRay : G.SameRay q.d q.c contactCD)
    (hbalance :
      L.scalar.add (L.length q.b data.contactBC) (L.length q.c q.d) =
        L.scalar.add (L.length q.d contactCD) (L.length q.b q.c)) :
    (G.Bet q.b data.contactBC q.c ∧ G.Bet q.d contactCD q.c) ∨
      (G.Bet q.b q.c data.contactBC ∧ G.Bet q.d q.c contactCD) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  rcases sameRay_order G data.contactBC_ray with hyBeyond | hyFinite <;>
    rcases sameRay_order G hcontactCDRay with hwBeyond | hwFinite
  · exact Or.inr ⟨hyBeyond, hwBeyond⟩
  · have hby : L.length q.b data.contactBC =
        L.scalar.add (L.length q.b q.c) (L.length q.c data.contactBC) :=
      LengthMeasurement.Axioms.bet_additive _ _ _ hyBeyond
    have hdc : L.length q.c q.d =
        L.scalar.add (L.length q.d contactCD) (L.length contactCD q.c) := by
      rw [LengthMeasurement.Axioms.length_symm q.c q.d]
      exact LengthMeasurement.Axioms.bet_additive _ _ _ hwFinite
    have hzero : L.scalar.add (L.length q.c data.contactBC)
        (L.length contactCD q.c) = L.scalar.zero := by
      apply add_left_cancel L.scalar
        (x := L.scalar.add (L.length q.b q.c) (L.length q.d contactCD))
      calc
        L.scalar.add
            (L.scalar.add (L.length q.b q.c) (L.length q.d contactCD))
            (L.scalar.add (L.length q.c data.contactBC)
              (L.length contactCD q.c)) =
          L.scalar.add (L.length q.b data.contactBC) (L.length q.c q.d) := by
            rw [hby, hdc]
            simp only [OrderedScalar.Axioms.add_assoc,
              OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
        _ = L.scalar.add (L.length q.d contactCD) (L.length q.b q.c) :=
          hbalance
        _ = L.scalar.add
            (L.scalar.add (L.length q.b q.c) (L.length q.d contactCD))
            L.scalar.zero := by
              rw [OrderedScalar.Axioms.add_zero,
                OrderedScalar.Axioms.add_comm]
    obtain ⟨hyZero, hwZero⟩ := nonnegative_pair_zero L.scalar
      (LengthMeasurement.Axioms.length_nonnegative q.c data.contactBC)
      (LengthMeasurement.Axioms.length_nonnegative contactCD q.c) hzero
    have hyEq : q.c = data.contactBC :=
      (LengthMeasurement.Axioms.length_eq_zero q.c data.contactBC).mp hyZero
    have hwEq : contactCD = q.c :=
      (LengthMeasurement.Axioms.length_eq_zero contactCD q.c).mp hwZero
    exact Or.inl ⟨by
      rw [← hyEq]
      exact bet_endpoint_refl G q.b q.c, by
      rw [hwEq]
      exact bet_endpoint_refl G q.d q.c⟩
  · have hbc : L.length q.b q.c =
        L.scalar.add (L.length q.b data.contactBC)
          (L.length data.contactBC q.c) :=
      LengthMeasurement.Axioms.bet_additive _ _ _ hyFinite
    have hdw : L.length q.d contactCD =
        L.scalar.add (L.length q.d q.c) (L.length q.c contactCD) :=
      LengthMeasurement.Axioms.bet_additive _ _ _ hwBeyond
    have hzero : L.scalar.add (L.length q.c contactCD)
        (L.length data.contactBC q.c) = L.scalar.zero := by
      apply add_left_cancel L.scalar
        (x := L.scalar.add (L.length q.b data.contactBC) (L.length q.d q.c))
      calc
        L.scalar.add
            (L.scalar.add (L.length q.b data.contactBC) (L.length q.d q.c))
            (L.scalar.add (L.length q.c contactCD)
              (L.length data.contactBC q.c)) =
          L.scalar.add (L.length q.d contactCD) (L.length q.b q.c) := by
            rw [hdw, hbc]
            simp only [OrderedScalar.Axioms.add_assoc,
              OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
        _ = L.scalar.add (L.length q.b data.contactBC) (L.length q.c q.d) :=
          hbalance.symm
        _ = L.scalar.add
            (L.scalar.add (L.length q.b data.contactBC) (L.length q.d q.c))
            L.scalar.zero := by
              rw [LengthMeasurement.Axioms.length_symm q.c q.d,
                OrderedScalar.Axioms.add_zero]
    obtain ⟨hwZero, hyZero⟩ := nonnegative_pair_zero L.scalar
      (LengthMeasurement.Axioms.length_nonnegative q.c contactCD)
      (LengthMeasurement.Axioms.length_nonnegative data.contactBC q.c) hzero
    have hwEq : q.c = contactCD :=
      (LengthMeasurement.Axioms.length_eq_zero q.c contactCD).mp hwZero
    have hyEq : data.contactBC = q.c :=
      (LengthMeasurement.Axioms.length_eq_zero data.contactBC q.c).mp hyZero
    exact Or.inl ⟨by
      rw [hyEq]
      exact bet_endpoint_refl G q.b q.c, by
      rw [← hwEq]
      exact bet_endpoint_refl G q.d q.c⟩
  · exact Or.inl ⟨hyFinite, hwFinite⟩

/-- When both outer contacts lie beyond `C`, their equal tangent lengths put the center on
the internal bisector line at `C`; convexity selects its forward ray. -/
theorem outer_center_on_C_bisector
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (data : ThreeRayTangency G q)
    {contactCD : G.Point}
    (hcontactCDRay : G.SameRay q.d q.c contactCD)
    (htangentCD : G.TangentAt data.circle contactCD q.d)
    (hyBeyond : G.Bet q.b q.c data.contactBC)
    (hwBeyond : G.Bet q.d q.c contactCD)
    (hy_ne_c : data.contactBC ≠ q.c)
    (axisC : BisectorAxis G q.c q.b q.d) :
    G.SameRay q.c axisC.midpoint data.circle.center := by
  have hcy_cw_len : L.length q.c data.contactBC =
      L.length q.c contactCD :=
    equal_tangent_lengths G M L data.tangentBC htangentCD
      (collinear_cyclic G (collinear_cyclic G data.contactBC_ray.2.2.1))
      (collinear_cyclic G (collinear_cyclic G hcontactCDRay.2.2.1))
  have hcy_cw : G.Congruent q.c data.contactBC q.c contactCD :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mpr hcy_cw_len
  have hw_ne_c : contactCD ≠ q.c := by
    intro hwc
    subst contactCD
    have hzero : G.Congruent q.c data.contactBC q.c q.c := hcy_cw
    have hcy : data.contactBC = q.c :=
      Plane.Axioms.congruenceIdentity data.contactBC q.c q.c
        (congruent_trans G
          (Plane.Axioms.congruenceReversal data.contactBC q.c) hzero)
    exact hy_ne_c hcy
  have hy_ne_w : data.contactBC ≠ contactCD := by
    intro hyw
    have hbcY : G.Collinear q.b q.c data.contactBC := Or.inl hyBeyond
    have hdcY : G.Collinear q.d q.c data.contactBC := by simpa [hyw] using Or.inl hwBeyond
    have hbcd : G.Collinear q.b q.c q.d :=
      collinear_three_on_line G hy_ne_c
        (collinear_swap_last G (collinear_cyclic G (collinear_cyclic G hbcY)))
        (collinear_refl_right G data.contactBC q.c)
        (collinear_swap_last G (collinear_cyclic G (collinear_cyclic G hdcY)))
    exact q.bcd_noncollinear hbcd
  have hcenter_equal :
      G.Congruent data.circle.center data.contactBC
        data.circle.center contactCD :=
    congruent_trans G data.tangentBC.2.1
      (congruent_symm G htangentCD.2.1)
  have hmid_equal :
      G.Congruent axisC.midpoint data.contactBC axisC.midpoint contactCD :=
    equidistant_opposite_boundary_pair G axisC
      (sameRay_refl G axisC.midpoint_ne_vertex)
      hyBeyond hwBeyond hcy_cw
  obtain ⟨mid, hmid⟩ := midpoint_exists G data.contactBC contactCD
  have hmidCO : G.Collinear mid q.c data.circle.center :=
    equidistant_points_collinear_with_midpoint G hy_ne_w hmid
      hcy_cw hcenter_equal
  have hmidCaxis : G.Collinear mid q.c axisC.midpoint :=
    equidistant_points_collinear_with_midpoint G hy_ne_w hmid
      hcy_cw hmid_equal
  have hmid_ne_c : mid ≠ q.c := by
    intro hmc
    subst mid
    have hycw : G.Collinear data.contactBC q.c contactCD := Or.inl hmid.1
    have hbcY : G.Collinear q.b q.c data.contactBC := Or.inl hyBeyond
    have hdcW : G.Collinear q.d q.c contactCD := Or.inl hwBeyond
    have hbcW : G.Collinear q.b q.c contactCD :=
      collinear_three_on_line G hy_ne_c
        (collinear_swap_last G (collinear_cyclic G (collinear_cyclic G hbcY)))
        (collinear_refl_right G data.contactBC q.c) hycw
    exact q.bcd_noncollinear
      (collinear_three_on_line G hw_ne_c
        (collinear_swap_last G (collinear_cyclic G (collinear_cyclic G hbcW)))
        (collinear_refl_right G contactCD q.c)
        (collinear_swap_last G (collinear_cyclic G (collinear_cyclic G hdcW))))
  have hCaxisO : G.Collinear q.c axisC.midpoint data.circle.center :=
    collinear_three_on_line G hmid_ne_c
      (collinear_refl_right G mid q.c) hmidCaxis hmidCO
  have ho_ne_c : data.circle.center ≠ q.c := by
    intro hoc
    have hline : G.Collinear data.contactBC data.circle.center q.b := by
      rw [hoc]
      exact collinear_swap_last G
        (collinear_cyclic G (collinear_cyclic G data.contactBC_ray.2.2.1))
    exact tangent_center_off_line G data.tangentBC hline
  rcases sameRay_or_opposite_of_collinear G
      axisC.midpoint_ne_vertex ho_ne_c hCaxisO with hsame | hopposite
  · exact hsame
  · have haxisOffBC : ¬G.Collinear q.b q.c axisC.midpoint := by
      intro h
      exact (axisC.strictInterior
        (fun h' => q.bcd_noncollinear
          (collinear_swap_last G (collinear_cyclic G h')))).off_first_boundary
        (collinear_swap G h)
    have hoOffBC : ¬G.Collinear q.b q.c data.circle.center := by
      intro h
      have haxisLine : G.Collinear q.b q.c data.axes.axisB.midpoint := by
        have hcenterAxis : G.Collinear q.b data.circle.center data.axes.axisB.midpoint :=
          collinear_swap_last G data.forward.2.2.2.1
        exact collinear_three_on_line G data.forward.2.2.1.symm
          (collinear_cyclic G (collinear_refl_left G q.b data.circle.center))
          (collinear_swap_last G h) hcenterAxis
      exact (data.axes.axisB.strictInterior
        (fun h' => q.abc_noncollinear (collinear_swap G h'))).off_second_boundary
        haxisLine
    have haxisSameD : ¬G.OppositeSides q.b q.c axisC.midpoint q.d :=
      by
        intro h
        exact (axisC.strictInterior
          (fun h' => q.bcd_noncollinear
            (collinear_swap_last G (collinear_cyclic G h')))).with_second_boundary
          (oppositeSides_swap_line G h)
    have hOSameA : ¬G.OppositeSides q.b q.c data.circle.center q.a := by
      have haxisSameA :=
        (data.axes.axisB.strictInterior
          (fun h' => q.abc_noncollinear (collinear_swap G h'))).with_first_boundary
      have haxisSameO := not_oppositeSides_of_sameRay G data.forward.2
        (data.axes.axisB.strictInterior
          (fun h' => q.abc_noncollinear (collinear_swap G h'))).off_second_boundary
      exact not_oppositeSides_trans G
        (data.axes.axisB.strictInterior
          (fun h' => q.abc_noncollinear (collinear_swap G h'))).off_second_boundary
        (fun h => haxisSameO (oppositeSides_symm G h)) haxisSameA
    have hOSameD : ¬G.OppositeSides q.b q.c data.circle.center q.d :=
      not_oppositeSides_trans G
        (by
          intro h
          exact q.abc_noncollinear
            (collinear_cyclic G (collinear_cyclic G h)))
        hOSameA (same_side_AD_of_BC G q)
    have haxisO_not :
        ¬G.OppositeSides q.b q.c axisC.midpoint data.circle.center :=
      not_oppositeSides_trans G
        (by
          intro h
          exact q.bcd_noncollinear h)
        haxisSameD (fun h => hOSameD (oppositeSides_symm G h))
    exact False.elim (haxisO_not
      ⟨haxisOffBC, hoOffBC, q.c,
        collinear_refl_right G q.b q.c, hopposite⟩)

/-- In the long-`AD` branch, both remaining ray contacts are in fact contacts with the
closed sides `BC` and `CD`. -/
theorem longAD_outer_contacts_between
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (data : ThreeRayTangency G q)
    {contactCD : G.Point}
    (hcontactAD : G.Bet q.a data.contactAD q.d)
    (hcontactCDRay : G.SameRay q.d q.c contactCD)
    (htangentCD : G.TangentAt data.circle contactCD q.d) :
    G.Bet q.b data.contactBC q.c ∧ G.Bet q.d contactCD q.c := by
  have hbalance := outer_contact_balance G M L q data hcontactAD
    hcontactCDRay htangentCD
  rcases outer_contacts_finite_or_beyond G L q data hcontactCDRay hbalance with
      hfinite | hbeyond
  · exact hfinite
  · by_cases hyc : data.contactBC = q.c
    · have hcy_cw_len : L.length q.c data.contactBC =
          L.length q.c contactCD :=
        equal_tangent_lengths G M L data.tangentBC htangentCD
          (collinear_cyclic G
            (collinear_cyclic G data.contactBC_ray.2.2.1))
          (collinear_cyclic G (collinear_cyclic G hcontactCDRay.2.2.1))
      have hwZero : L.length q.c contactCD = L.scalar.zero := by
        rw [hyc, (LengthMeasurement.Axioms.length_eq_zero q.c q.c).2 rfl] at hcy_cw_len
        exact hcy_cw_len.symm
      have hwc : q.c = contactCD :=
        (LengthMeasurement.Axioms.length_eq_zero q.c contactCD).mp hwZero
      exact ⟨by
        rw [hyc]
        exact bet_endpoint_refl G q.b q.c, by
        rw [← hwc]
        exact bet_endpoint_refl G q.d q.c⟩
    · obtain ⟨axisC⟩ := bisectorAxis_exists G
        (fun h => q.bcd_noncollinear
          (collinear_swap_last G (collinear_cyclic G h)))
      have hCforward := outer_center_on_C_bisector G M L q data
        hcontactCDRay htangentCD hbeyond.1 hbeyond.2 hyc axisC
      obtain ⟨projection, hfoot⟩ := projectionData_of_tangent G data.tangentBC
        (collinear_cyclic G (collinear_refl_left G q.b q.c))
        data.contactBC_ray.2.2.1
      have hleftC : G.Collinear projection.left projection.foot q.c :=
        collinear_three_on_line G q.b_ne_c
          projection.left_on_line projection.foot_on_line
          (collinear_refl_right G q.b q.c)
      have hleftB : G.Collinear projection.left projection.foot q.b :=
        collinear_three_on_line G q.b_ne_c
          projection.left_on_line projection.foot_on_line
          (collinear_cyclic G (collinear_refl_left G q.b q.c))
      have hnotBeyond : ¬G.Bet projection.foot q.c q.b :=
        projection_not_behind_bisected_vertex G M L
          (bisectorAxis_swap G axisC)
          (fun h => q.bcd_noncollinear
            (collinear_cyclic G (collinear_cyclic G h)))
          hCforward projection hleftC hleftB
      exact False.elim (hnotBeyond (by
        rw [hfoot]
        exact bet_symm G hbeyond.1))

end Soultions.Sharygin.Page14.Problem19.DirectIncenter
