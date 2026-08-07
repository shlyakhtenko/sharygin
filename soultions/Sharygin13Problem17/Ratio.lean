import Sharygin13Problem17.Bisector

/-!
# Problem-local angle-bisector ratio for Sharygin, page 13, problem 17
-/

namespace Soultions.Sharygin.Page13.Problem17.Ratio

open Euclid Plane
open Soultions.Sharygin.Page13.Problem17.Tarski
open Soultions.Sharygin.Page13.Problem17.Midpoint
open Soultions.Sharygin.Page13.Problem17.Affine
open Soultions.Sharygin.Page13.Problem17.Midline
open Soultions.Sharygin.Page13.Problem17.Bisector

variable (G : Plane) [G.Axioms]

omit [G.Axioms] in
theorem strictlyParallel_of_parallel {a b c d : G.Point}
    (h : Parallel G a b c d) :
    G.StrictlyParallel a b c d := by
  exact (strictlyParallel_iff_no_intersection G).mpr h

theorem scalar_add_left_cancel
    (S : OrderedScalar) [S.Axioms]
    {x y z : S.Carrier}
    (h : S.add x y = S.add x z) :
    y = z := by
  have h' :=
    congrArg (fun w => S.add (S.neg x) w) h
  have hneg_add : S.add (S.neg x) x = S.zero := by
    rw [OrderedScalar.Axioms.add_comm]
    exact OrderedScalar.Axioms.add_neg x
  calc
    y = S.add S.zero y :=
      (OrderedScalar.Axioms.zero_add y).symm
    _ = S.add (S.add (S.neg x) x) y := by
      rw [hneg_add]
    _ = S.add (S.neg x) (S.add x y) :=
      OrderedScalar.Axioms.add_assoc _ _ _
    _ = S.add (S.neg x) (S.add x z) := h'
    _ = S.add (S.add (S.neg x) x) z :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by
      rw [hneg_add]
    _ = z := OrderedScalar.Axioms.zero_add z

theorem scalar_right_distrib
    (S : OrderedScalar) [S.Axioms]
    (x y z : S.Carrier) :
    S.mul (S.add x y) z =
      S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm
      (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

/--
Two lines meeting at `z` coincide when both are parallel to the same fixed line.
-/
theorem parallel_lines_coincide_at
    {a b c d e f z : G.Point}
    (hab_ef : Parallel G a b e f)
    (hcd_ef : Parallel G c d e f)
    (habz : G.Collinear a b z)
    (hcdz : G.Collinear c d z) :
    G.Collinear a b c ∧
      G.Collinear a b d := by
  obtain ⟨x, hzx, habx⟩ : ∃ x,
      z ≠ x ∧ G.Collinear a b x := by
    by_cases hza : z = a
    · exact ⟨b, by simpa [hza] using hab_ef.1,
        collinear_refl_right G a b⟩
    · exact ⟨a, hza,
        collinear_cyclic G
          (collinear_refl_left G a b)⟩
  obtain ⟨y, hzy, hcdy⟩ : ∃ y,
      z ≠ y ∧ G.Collinear c d y := by
    by_cases hzc : z = c
    · exact ⟨d, by simpa [hzc] using hcd_ef.1,
        collinear_refl_right G c d⟩
    · exact ⟨c, hzc,
        collinear_cyclic G
          (collinear_refl_left G c d)⟩
  have hzx_parallel_ef :
      Parallel G z x e f :=
    parallel_replace_left G hab_ef hzx
      habz habx
  have hzy_parallel_ef :
      Parallel G z y e f :=
    parallel_replace_left G hcd_ef hzy
      hcdz hcdy
  have hyzx : G.Collinear y z x :=
    parallel_through_collinear G
      hzx_parallel_ef hzy_parallel_ef
  have hzyx : G.Collinear z y x :=
    collinear_swap G hyzx
  have hzy_c :
      G.Collinear z y c :=
    collinear_three_on_line G hcd_ef.1
      hcdz hcdy
      (collinear_cyclic G
        (collinear_refl_left G c d))
  have hzy_d :
      G.Collinear z y d :=
    collinear_three_on_line G hcd_ef.1
      hcdz hcdy
      (collinear_refl_right G c d)
  have hzx_c :
      G.Collinear z x c :=
    collinear_three_on_line G hzy
      (collinear_cyclic G
        (collinear_refl_left G z y))
      hzyx hzy_c
  have hzx_d :
      G.Collinear z x d :=
    collinear_three_on_line G hzy
      (collinear_cyclic G
        (collinear_refl_left G z y))
      hzyx hzy_d
  have hzx_a :
      G.Collinear z x a :=
    collinear_three_on_line G hab_ef.1
      habz habx
      (collinear_cyclic G
        (collinear_refl_left G a b))
  have hzx_b :
      G.Collinear z x b :=
    collinear_three_on_line G hab_ef.1
      habz habx
      (collinear_refl_right G a b)
  exact
    ⟨collinear_three_on_line G hzx
        hzx_a hzx_b hzx_c,
      collinear_three_on_line G hzx
        hzx_a hzx_b hzx_d⟩

/--
The fourth-proportional product for two transversals whose corresponding endpoints lie on
opposite rays from their intersection.

Reflect the first parallel segment through the intersection.  Its image has the same-directed
rays required by `fourth_proportional_mul`.  If the image line coincides with the second
parallel, uniqueness of line intersections identifies the reflected endpoints directly.
-/
theorem crossed_fourth_proportional_mul
    (L : LengthMeasurement G) [L.Axioms]
    {o a b c d : G.Point}
    (hao : a ≠ o) (hbo : b ≠ o)
    (hco : c ≠ o) (hdo : d ≠ o)
    (haoc : G.Bet a o c)
    (hbod : G.Bet b o d)
    (hoff : ¬G.Collinear o a b)
    (hparallel : Parallel G a b c d) :
    L.scalar.mul (L.length o a) (L.length o d) =
      L.scalar.mul (L.length o b) (L.length o c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨a', haa'⟩ :=
    pointReflection_exists G o a
  obtain ⟨b', hbb'⟩ :=
    pointReflection_exists G o b
  have ha'o : a' ≠ o :=
    pointReflection_other_ne G haa' hao
  have hb'o : b' ≠ o :=
    pointReflection_other_ne G hbb' hbo
  have ha'_c : G.SameRay o a' c :=
    sameRay_of_common_predecessor G
      hao haa'.between haoc ha'o hco
  have hb'_d : G.SameRay o b' d :=
    sameRay_of_common_predecessor G
      hbo hbb'.between hbod hb'o hdo
  have hoo : PointReflection G o o o :=
    ⟨bet_endpoint_refl G o o,
      congruent_refl G o o⟩
  have hoff_image :
      ¬G.Collinear a' b' o := by
    intro hcol
    have habo : G.Collinear a b o :=
      pointReflection_preserves_collinear G
        (pointReflection_symm G haa')
        (pointReflection_symm G hbb')
        hoo hcol
    exact hoff
      (collinear_cyclic G
        (collinear_cyclic G habo))
  have hoff_ab : ¬G.Collinear a b o := by
    intro habo
    exact hoff
      (collinear_cyclic G
        (collinear_cyclic G habo))
  have hab_image :
      Parallel G a b a' b' :=
    pointReflection_image_parallel G
      hparallel.1 hoff_ab haa' hbb'
  by_cases hintersection :
      ∃ z,
        G.Collinear a' b' z ∧
          G.Collinear c d z
  · obtain ⟨z, habz, hcdz⟩ := hintersection
    have hcoincide :
        G.Collinear a' b' c ∧
          G.Collinear a' b' d :=
      parallel_lines_coincide_at G
        (parallel_symm G hab_image)
        (parallel_symm G hparallel)
        habz hcdz
    have ha'c : a' = c := by
      apply Classical.byContradiction
      intro ha'c_ne
      have ha'c_a' :
          G.Collinear a' c a' :=
        collinear_cyclic G
          (collinear_refl_left G a' c)
      have ha'c_b' :
          G.Collinear a' c b' :=
        collinear_swap_last G hcoincide.1
      have ha'c_o :
          G.Collinear a' c o :=
        collinear_cyclic G
          ha'_c.2.2.1
      exact hoff_image
        (collinear_three_on_line G ha'c_ne
          ha'c_a' ha'c_b' ha'c_o)
    have hb'd : b' = d := by
      apply Classical.byContradiction
      intro hb'd_ne
      have hb'd_a' :
          G.Collinear b' d a' := by
        have ha'b'_d :
            G.Collinear a' b' d :=
          hcoincide.2
        exact collinear_cyclic G ha'b'_d
      have hb'd_b' :
          G.Collinear b' d b' :=
        collinear_cyclic G
          (collinear_refl_left G b' d)
      have hb'd_o :
          G.Collinear b' d o :=
        collinear_cyclic G
          hb'_d.2.2.1
      have ha'b'_o :
          G.Collinear a' b' o :=
        collinear_three_on_line G hb'd_ne
          hb'd_a' hb'd_b' hb'd_o
      exact hoff_image ha'b'_o
    have ha'_length :
        L.length o a' = L.length o a :=
      (LengthMeasurement.Axioms.congruent_iff
        o a' o a).mp haa'.radius
    have hb'_length :
        L.length o b' = L.length o b :=
      (LengthMeasurement.Axioms.congruent_iff
        o b' o b).mp hbb'.radius
    rw [← ha'c, ← hb'd, ha'_length,
      hb'_length]
    exact OrderedScalar.Axioms.mul_comm _ _
  · have hab_cd :
        Parallel G a' b' c d :=
      ⟨hab_image.2.1, hparallel.2.1,
        hintersection⟩
    have hconfiguration :
        G.FourthProportionalConfiguration
          o a' b' c d :=
      ⟨ha'_c, hb'_d,
        (by
          intro h
          exact hoff_image
            (collinear_cyclic G h)),
        strictlyParallel_of_parallel G hab_cd⟩
    have hproduct :
        L.scalar.mul
            (L.length o a') (L.length o d) =
          L.scalar.mul
            (L.length o b') (L.length o c) :=
      LengthMeasurement.Axioms.fourth_proportional_mul
        o a' b' c d hconfiguration
    have ha'_length :
        L.length o a' = L.length o a :=
      (LengthMeasurement.Axioms.congruent_iff
        o a' o a).mp haa'.radius
    have hb'_length :
        L.length o b' = L.length o b :=
      (LengthMeasurement.Axioms.congruent_iff
        o b' o b).mp hbb'.radius
    rwa [ha'_length, hb'_length] at hproduct

/-- Cross-multiplied internal angle-bisector theorem. -/
theorem interior_ratio
    (L : LengthMeasurement G) [L.Axioms]
    (config : InteriorConfiguration G) :
    L.scalar.mul
        (L.length config.b config.m)
        (L.length config.a config.c) =
      L.scalar.mul
        (L.length config.m config.c)
        (L.length config.a config.b) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hab : config.a ≠ config.b := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_left G config.a config.c
  have hbc : config.b ≠ config.c := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_right G config.a config.b
  obtain ⟨d, hbad, had_ac, ham_parallel_cd⟩ :=
    config.exterior_parallel_point G
  have hbd : config.b ≠ d := by
    intro h
    subst d
    exact hab
      (Plane.Axioms.betweennessIdentity
        config.b config.a hbad).symm
  have hBA_D :
      G.SameRay config.b config.a d := by
    refine
      ⟨hab, hbd.symm, Or.inl hbad, ?_⟩
    intro habd
    have hb_ab :
        G.Bet config.b config.a config.b :=
      bet_inner_trans G hbad habd
    exact hab
      (Plane.Axioms.betweennessIdentity
        config.b config.a hb_ab).symm
  have hBM_C :
      G.SameRay config.b config.m config.c := by
    refine
      ⟨config.b_ne_m.symm,
        hbc.symm, Or.inl config.m_on_side, ?_⟩
    intro hmbc
    have hb_mb :
        G.Bet config.b config.m config.b :=
      bet_inner_trans G config.m_on_side hmbc
    exact config.b_ne_m
      (Plane.Axioms.betweennessIdentity
        config.b config.m hb_mb)
  have hm_off_ba :
      ¬G.Collinear config.b config.a config.m := by
    intro hbam
    have hbm_a :
        G.Collinear config.b config.m config.a :=
      collinear_swap_last G hbam
    have hbm_c :
        G.Collinear config.b config.m config.c :=
      Or.inl config.m_on_side
    have hbm_b :
        G.Collinear config.b config.m config.b :=
      collinear_cyclic G
        (collinear_refl_left G config.b config.m)
    have hba_c :
        G.Collinear config.b config.a config.c :=
      collinear_three_on_line G config.b_ne_m
        hbm_b hbm_a hbm_c
    exact config.triangle_nondegenerate
      (collinear_swap G hba_c)
  have hconfiguration :
      G.FourthProportionalConfiguration
        config.b config.a config.m d config.c :=
    ⟨hBA_D, hBM_C, hm_off_ba,
      strictlyParallel_of_parallel G
        (parallel_reverse_right G ham_parallel_cd)⟩
  have hproduct :
      L.scalar.mul
          (L.length config.b config.a)
          (L.length config.b config.c) =
        L.scalar.mul
          (L.length config.b config.m)
          (L.length config.b d) :=
    LengthMeasurement.Axioms.fourth_proportional_mul
      config.b config.a config.m d config.c
      hconfiguration
  have hba_ab :
      L.length config.b config.a =
        L.length config.a config.b :=
    LengthMeasurement.Axioms.length_symm
      config.b config.a
  have hbc_add :
      L.length config.b config.c =
        L.scalar.add
          (L.length config.b config.m)
          (L.length config.m config.c) :=
    LengthMeasurement.Axioms.bet_additive
      config.b config.m config.c config.m_on_side
  have hbd_add :
      L.length config.b d =
        L.scalar.add
          (L.length config.b config.a)
          (L.length config.a d) :=
    LengthMeasurement.Axioms.bet_additive
      config.b config.a d hbad
  have had_length :
      L.length config.a d =
        L.length config.a config.c :=
    (LengthMeasurement.Axioms.congruent_iff
      config.a d config.a config.c).mp had_ac
  rw [hba_ab, hbc_add, hbd_add, hba_ab, had_length] at hproduct
  rw [OrderedScalar.Axioms.left_distrib] at hproduct
  rw [OrderedScalar.Axioms.left_distrib] at hproduct
  rw [OrderedScalar.Axioms.mul_comm
    (L.length config.b config.m)
    (L.length config.a config.b)] at hproduct
  have hcross :
      L.scalar.mul
          (L.length config.a config.b)
          (L.length config.m config.c) =
        L.scalar.mul
          (L.length config.b config.m)
          (L.length config.a config.c) :=
    scalar_add_left_cancel L.scalar hproduct
  calc
    L.scalar.mul
        (L.length config.b config.m)
        (L.length config.a config.c) =
      L.scalar.mul
        (L.length config.a config.b)
        (L.length config.m config.c) :=
      hcross.symm
    _ = L.scalar.mul
        (L.length config.m config.c)
        (L.length config.a config.b) :=
      OrderedScalar.Axioms.mul_comm _ _

/--
The exterior angle-bisector ratio when the intersection lies beyond `c`.
-/
theorem exterior_ratio_beyond_c
    (L : LengthMeasurement G) [L.Axioms]
    (config : ExteriorConfiguration G)
    (hbcm : G.Bet config.b config.c config.m) :
    L.scalar.mul
        (L.length config.b config.m)
        (L.length config.a config.c) =
      L.scalar.mul
        (L.length config.c config.m)
        (L.length config.a config.b) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hab : config.a ≠ config.b := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_left G config.a config.c
  have hbc : config.b ≠ config.c := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_right G config.a config.b
  obtain
    ⟨d, hd_ray, had_ac, hparallel,
      _, horder_beyond_c⟩ :=
    config.left_parallel_point_ordered G
  have hadb : G.Bet config.a d config.b :=
    horder_beyond_c hbcm
  have hdb : d ≠ config.b := by
    intro h
    have hdm :
        G.Collinear d config.c config.m := by
      simpa [h] using (Or.inl hbcm :
        G.Collinear config.b config.c config.m)
    exact hparallel.2.2
      ⟨config.m,
        collinear_refl_right G config.a config.m,
        hdm⟩
  have hBA_D :
      G.SameRay config.b config.a d := by
    refine
      ⟨hab, hdb, ?_, ?_⟩
    · exact collinear_cyclic G
        (collinear_cyclic G (Or.inl hadb))
    · intro habd
      have hbd_eq : config.b = d :=
        bet_antisymm G habd hadb
      exact hdb hbd_eq.symm
  have hBM_C :
      G.SameRay config.b config.m config.c := by
    refine
      ⟨config.b_ne_m.symm,
        hbc.symm, ?_, ?_⟩
    · exact collinear_swap_last G (Or.inl hbcm)
    · intro hmbc
      have hcbm : G.Bet config.c config.b config.m :=
        bet_symm G hmbc
      have hbcb : G.Bet config.b config.c config.b :=
        bet_inner_trans G hbcm hcbm
      have hbc_eq : config.b = config.c :=
        Plane.Axioms.betweennessIdentity
          config.b config.c hbcb
      exact hbc hbc_eq
  have hm_off_ba :
      ¬G.Collinear config.b config.a config.m := by
    intro hbam
    have hbm_a :
        G.Collinear config.b config.m config.a :=
      collinear_swap_last G hbam
    have hbm_c :
        G.Collinear config.b config.m config.c :=
      collinear_swap_last G (Or.inl hbcm)
    have hbm_b :
        G.Collinear config.b config.m config.b :=
      collinear_cyclic G
        (collinear_refl_left G
          config.b config.m)
    have hba_c :
        G.Collinear config.b config.a config.c :=
      collinear_three_on_line G config.b_ne_m
        hbm_b hbm_a hbm_c
    exact config.triangle_nondegenerate
      (collinear_swap G hba_c)
  have hconfiguration :
      G.FourthProportionalConfiguration
        config.b config.a config.m d config.c :=
    ⟨hBA_D, hBM_C, hm_off_ba,
      strictlyParallel_of_parallel G hparallel⟩
  have hproduct :
      L.scalar.mul
          (L.length config.b config.a)
          (L.length config.b config.c) =
        L.scalar.mul
          (L.length config.b config.m)
          (L.length config.b d) :=
    LengthMeasurement.Axioms.fourth_proportional_mul
      config.b config.a config.m d config.c
      hconfiguration
  have hba_ab :
      L.length config.b config.a =
        L.length config.a config.b :=
    LengthMeasurement.Axioms.length_symm
      config.b config.a
  have hbd_db :
      L.length config.b d =
        L.length d config.b :=
    LengthMeasurement.Axioms.length_symm
      config.b d
  have hab_add :
      L.length config.a config.b =
        L.scalar.add
          (L.length config.a d)
          (L.length d config.b) :=
    LengthMeasurement.Axioms.bet_additive
      config.a d config.b hadb
  have hbm_add :
      L.length config.b config.m =
        L.scalar.add
          (L.length config.b config.c)
          (L.length config.c config.m) :=
    LengthMeasurement.Axioms.bet_additive
      config.b config.c config.m hbcm
  have had_length :
      L.length config.a d =
        L.length config.a config.c :=
    (LengthMeasurement.Axioms.congruent_iff
      config.a d config.a config.c).mp had_ac
  rw [hba_ab, hab_add, hbm_add,
    hbd_db, had_length] at hproduct
  rw [scalar_right_distrib,
    scalar_right_distrib] at hproduct
  rw [OrderedScalar.Axioms.mul_comm
    (L.length d config.b)
    (L.length config.b config.c)] at hproduct
  rw [OrderedScalar.Axioms.add_comm] at hproduct
  have h_ac_bc :
      L.scalar.mul
          (L.length config.a config.c)
          (L.length config.b config.c) =
        L.scalar.mul
          (L.length config.c config.m)
          (L.length d config.b) :=
    scalar_add_left_cancel L.scalar hproduct
  rw [hbm_add, hab_add, had_length]
  rw [scalar_right_distrib,
    OrderedScalar.Axioms.left_distrib]
  rw [OrderedScalar.Axioms.mul_comm
    (L.length config.b config.c)
    (L.length config.a config.c)]
  rw [h_ac_bc]
  rw [OrderedScalar.Axioms.mul_comm
    (L.length config.c config.m)
    (L.length config.a config.c)]
  exact OrderedScalar.Axioms.add_comm _ _

/--
The exterior angle-bisector ratio when the intersection lies beyond `b`.
-/
theorem exterior_ratio_beyond_b
    (L : LengthMeasurement G) [L.Axioms]
    (config : ExteriorConfiguration G)
    (hmbc : G.Bet config.m config.b config.c) :
    L.scalar.mul
        (L.length config.b config.m)
        (L.length config.a config.c) =
      L.scalar.mul
        (L.length config.c config.m)
        (L.length config.a config.b) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hab : config.a ≠ config.b := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_left G config.a config.c
  have hbc : config.b ≠ config.c := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_right G config.a config.b
  obtain
    ⟨d, _, had_ac, hparallel,
      horder_beyond_b, _⟩ :=
    config.left_parallel_point_ordered G
  have habd : G.Bet config.a config.b d :=
    horder_beyond_b hmbc
  have hdb : d ≠ config.b := by
    intro h
    have hdm :
        G.Collinear d config.c config.m := by
      simpa [h] using
        (collinear_swap_last G
          (collinear_swap G (Or.inl hmbc) :
            G.Collinear config.b config.m config.c))
    exact hparallel.2.2
      ⟨config.m,
        collinear_refl_right G config.a config.m,
        hdm⟩
  have hm_off_ba :
      ¬G.Collinear config.b config.a config.m := by
    intro hbam
    have hbm_a :
        G.Collinear config.b config.m config.a :=
      collinear_swap_last G hbam
    have hbm_c :
        G.Collinear config.b config.m config.c :=
      collinear_swap G (Or.inl hmbc)
    have hbm_b :
        G.Collinear config.b config.m config.b :=
      collinear_cyclic G
        (collinear_refl_left G
          config.b config.m)
    have hba_c :
        G.Collinear config.b config.a config.c :=
      collinear_three_on_line G config.b_ne_m
        hbm_b hbm_a hbm_c
    exact config.triangle_nondegenerate
      (collinear_swap G hba_c)
  have hproduct :
      L.scalar.mul
          (L.length config.b config.a)
          (L.length config.b config.c) =
        L.scalar.mul
          (L.length config.b config.m)
          (L.length config.b d) :=
    crossed_fourth_proportional_mul G L
      hab config.b_ne_m.symm
      hdb hbc.symm
      habd hmbc hm_off_ba hparallel
  have hba_ab :
      L.length config.b config.a =
        L.length config.a config.b :=
    LengthMeasurement.Axioms.length_symm
      config.b config.a
  have had_add :
      L.length config.a d =
        L.scalar.add
          (L.length config.a config.b)
          (L.length config.b d) :=
    LengthMeasurement.Axioms.bet_additive
      config.a config.b d habd
  have hac_add :
      L.length config.a config.c =
        L.scalar.add
          (L.length config.a config.b)
          (L.length config.b d) := by
    rw [← had_add]
    exact
      ((LengthMeasurement.Axioms.congruent_iff
        config.a d config.a config.c).mp
        had_ac).symm
  have hmc_add :
      L.length config.m config.c =
        L.scalar.add
          (L.length config.m config.b)
          (L.length config.b config.c) :=
    LengthMeasurement.Axioms.bet_additive
      config.m config.b config.c hmbc
  have hcm_mc :
      L.length config.c config.m =
        L.length config.m config.c :=
    LengthMeasurement.Axioms.length_symm
      config.c config.m
  have hmb_bm :
      L.length config.m config.b =
        L.length config.b config.m :=
    LengthMeasurement.Axioms.length_symm
      config.m config.b
  rw [hba_ab] at hproduct
  have hproduct' :
      L.scalar.mul
          (L.length config.b config.m)
          (L.length config.b d) =
        L.scalar.mul
          (L.length config.b config.c)
          (L.length config.a config.b) := by
    calc
      L.scalar.mul
          (L.length config.b config.m)
          (L.length config.b d) =
        L.scalar.mul
          (L.length config.a config.b)
          (L.length config.b config.c) :=
        hproduct.symm
      _ = L.scalar.mul
          (L.length config.b config.c)
          (L.length config.a config.b) :=
        OrderedScalar.Axioms.mul_comm _ _
  rw [hac_add, hcm_mc, hmc_add, hmb_bm]
  rw [OrderedScalar.Axioms.left_distrib,
    scalar_right_distrib]
  rw [hproduct']

/-- Cross-multiplied exterior angle-bisector theorem. -/
theorem exterior_ratio
    (L : LengthMeasurement G) [L.Axioms]
    (config : ExteriorConfiguration G) :
    L.scalar.mul
        (L.length config.b config.m)
        (L.length config.a config.c) =
      L.scalar.mul
        (L.length config.c config.m)
        (L.length config.a config.b) := by
  rcases config.m_on_extension with hmbc | hbcm
  · exact exterior_ratio_beyond_b G L config hmbc
  · exact exterior_ratio_beyond_c G L config hbcm

end Soultions.Sharygin.Page13.Problem17.Ratio
