import Sharygin74Problem28.Grid

/-!
# Problem-local transversal ratios for Sharygin, PDF page 74, problem 28
-/

namespace Soultions.Sharygin.Page74.Problem28.Ratio

open Euclid Plane
open Soultions.Sharygin.Page74.Problem28.Tarski
open Soultions.Sharygin.Page74.Problem28.Midpoint
open Soultions.Sharygin.Page74.Problem28.Affine
open Soultions.Sharygin.Page74.Problem28.Similarity
open Soultions.Sharygin.Page74.Problem28.Projection

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

theorem scalar_add_left_comm
    (S : OrderedScalar) [S.Axioms]
    (x y z : S.Carrier) :
    S.add x (S.add y z) =
      S.add y (S.add x z) := by
  rw [← OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm x y,
    OrderedScalar.Axioms.add_assoc]

theorem scalar_mul_left_comm
    (S : OrderedScalar) [S.Axioms]
    (x y z : S.Carrier) :
    S.mul x (S.mul y z) =
      S.mul y (S.mul x z) := by
  rw [← OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm x y,
    OrderedScalar.Axioms.mul_assoc]

theorem scalar_mul_left_cancel
    (S : OrderedScalar) [S.Axioms]
    {x y z : S.Carrier}
    (hx : x ≠ S.zero)
    (h : S.mul x y = S.mul x z) :
    y = z := by
  have hinv :=
    congrArg (fun w => S.mul (S.inv x) w) h
  calc
    y = S.mul S.one y :=
      (OrderedScalar.Axioms.one_mul y).symm
    _ = S.mul (S.mul (S.inv x) x) y := by
      rw [OrderedScalar.Axioms.mul_comm
          (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = S.mul (S.inv x) (S.mul x y) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv x) (S.mul x z) := hinv
    _ = S.mul (S.mul (S.inv x) x) z :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one z := by
      rw [OrderedScalar.Axioms.mul_comm
          (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = z := OrderedScalar.Axioms.one_mul z

theorem scalar_mul_eq_zero_of_left_nonzero
    (S : OrderedScalar) [S.Axioms]
    {x y : S.Carrier}
    (hx : x ≠ S.zero)
    (h : S.mul x y = S.zero) :
    y = S.zero := by
  apply scalar_mul_left_cancel S hx
  rw [h]
  rw [OrderedScalar.Axioms.mul_comm]
  exact (OrderedScalar.Axioms.zero_mul x).symm

theorem scalar_mul_nonzero
    (S : OrderedScalar) [S.Axioms]
    {x y : S.Carrier}
    (hx : x ≠ S.zero)
    (hy : y ≠ S.zero) :
    S.mul x y ≠ S.zero := by
  intro hxy
  exact hy
    (scalar_mul_eq_zero_of_left_nonzero S hx hxy)

theorem scalar_add_nonzero_of_nonnegative_left
    (S : OrderedScalar) [S.Axioms]
    {x y : S.Carrier}
    (hx : x ≠ S.zero)
    (hx_nonnegative : S.le S.zero x)
    (hy_nonnegative : S.le S.zero y) :
    S.add x y ≠ S.zero := by
  intro hsum
  have hx_le_zero :
      S.le x S.zero := by
    have h :=
      OrderedScalar.Axioms.add_le_add_right
        S.zero y x hy_nonnegative
    rw [OrderedScalar.Axioms.zero_add,
      OrderedScalar.Axioms.add_comm] at h
    rwa [hsum] at h
  exact hx
    (OrderedScalar.Axioms.le_antisymm
      S.zero x hx_nonnegative hx_le_zero).symm

/-- Renaming the first of two parallel lines by two of its points preserves parallelism. -/
theorem parallel_replace_left {a b x y c d : G.Point}
    (hparallel : Parallel G a b c d)
    (hxy : x ≠ y)
    (hx : G.Collinear a b x)
    (hy : G.Collinear a b y) :
    Parallel G x y c d :=
  parallel_rebase_left G hparallel hx hy hxy

/-- Endpoints beyond the same predecessor determine the same ray. -/
theorem sameRay_of_common_predecessor
    {q a x y : G.Point}
    (hqa : q ≠ a)
    (hqx : G.Bet q a x)
    (hqy : G.Bet q a y)
    (hxa : x ≠ a)
    (hya : y ≠ a) :
    G.SameRay a x y := by
  have hcol : G.Collinear a x y :=
    collinear_on_common_ray G hqa hqx hqy
  refine ⟨hxa, hya, hcol, ?_⟩
  intro hxay
  rcases ray_connectivity G q a x y hqa hqx hqy with
    hqxy | hqyx
  · have haxy : G.Bet a x y :=
      bet_drop_left G hqx hqxy
    have hcycle : G.Bet x a x :=
      bet_inner_trans G hxay haxy
    exact hxa
      (Plane.Axioms.betweennessIdentity x a hcycle)
  · have hayx : G.Bet a y x :=
      bet_drop_left G hqy hqyx
    have hyax : G.Bet y a x :=
      bet_symm G hxay
    have hcycle : G.Bet a y a :=
      bet_inner_trans G hayx hyax
    exact hya
      (Plane.Axioms.betweennessIdentity a y hcycle).symm

/-- If `x` lies on a line and `x-p-q`, then `p` and `q` are not on opposite sides. -/
theorem not_oppositeSides_of_outward_bet
    {a b x p q : G.Point}
    (hxline : G.Collinear a b x)
    (hxpq : G.Bet x p q) :
    ¬G.OppositeSides a b p q := by
  intro hopposite
  have hab : a ≠ b :=
    oppositeSides_line_ne G hopposite
  have hpq : p ≠ q :=
    oppositeSides_ne G hopposite
  obtain ⟨hp_off, _, z, hzline, hpzq⟩ := hopposite
  have hxz : x = z := by
    apply Classical.byContradiction
    intro hxz
    have hpqx : G.Collinear p q x :=
      collinear_cyclic G (Or.inl hxpq)
    have hpqz : G.Collinear p q z :=
      collinear_swap_last G (Or.inl hpzq)
    have hpqp : G.Collinear p q p :=
      collinear_cyclic G (collinear_refl_left G p q)
    have hxzp : G.Collinear x z p :=
      collinear_three_on_line G hpq hpqx hpqz hpqp
    have hxza : G.Collinear x z a :=
      collinear_three_on_line G hab hxline hzline
        (collinear_cyclic G
          (collinear_refl_left G a b))
    have hxzb : G.Collinear x z b :=
      collinear_three_on_line G hab hxline hzline
        (collinear_refl_right G a b)
    exact hp_off
      (collinear_three_on_line G hxz
        hxza hxzb hxzp)
  subst z
  have hpx : p = x :=
    bet_antisymm G
      (bet_symm G hxpq)
      (bet_symm G hpzq)
  subst p
  exact hp_off hxline

/-- Endpoints of a line parallel to another line cannot be on opposite sides of it. -/
theorem not_oppositeSides_of_parallel_endpoints
    {a b c d : G.Point}
    (hparallel : Parallel G a b c d) :
    ¬G.OppositeSides c d a b := by
  intro hopposite
  obtain ⟨_, _, z, hz_cd, hazb⟩ := hopposite
  have hz_ab : G.Collinear a b z :=
    collinear_swap_last G (Or.inl hazb)
  exact hparallel.2.2 ⟨z, hz_ab, hz_cd⟩

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

/-- A nondegenerate triangle with a point on an exterior part of its base line. -/
structure ExteriorLineConfiguration where
  a : G.Point
  b : G.Point
  c : G.Point
  m : G.Point
  triangle_nondegenerate : ¬G.Collinear a b c
  m_on_extension : G.Bet m b c ∨ G.Bet b c m
  b_ne_m : b ≠ m
  c_ne_m : c ≠ m

/--
The line through `c` parallel to `a-m` meets the line `a-b`.
-/
theorem ExteriorLineConfiguration.parallel_point_exists
    (config : ExteriorLineConfiguration G) :
    ∃ d,
      G.Collinear config.a config.b d ∧
      Parallel G config.a config.m d config.c := by
  have hm_on_bc : G.Collinear config.b config.c config.m := by
    rcases config.m_on_extension with hmbc | hbcm
    · exact collinear_cyclic G (Or.inl hmbc)
    · exact Or.inl hbcm
  have hm_off_ab : ¬G.Collinear config.a config.b config.m := by
    intro habm
    have hbc_m : G.Collinear config.b config.c config.m :=
      hm_on_bc
    have hbm_a : G.Collinear config.b config.m config.a :=
      collinear_cyclic G habm
    have hbm_c : G.Collinear config.b config.m config.c :=
      collinear_swap_last G hbc_m
    have hbm_b : G.Collinear config.b config.m config.b :=
      collinear_cyclic G
        (collinear_refl_left G config.b config.m)
    have hba_c : G.Collinear config.b config.a config.c :=
      collinear_three_on_line G config.b_ne_m
        hbm_b hbm_a hbm_c
    exact config.triangle_nondegenerate
      (collinear_swap G hba_c)
  have hc_off_am : ¬G.Collinear config.a config.m config.c := by
    intro hamc
    have hmc_a : G.Collinear config.m config.c config.a :=
      collinear_cyclic G hamc
    have hmc_b : G.Collinear config.m config.c config.b := by
      exact collinear_cyclic G
        (collinear_swap_last G hm_on_bc)
    have hmc_c : G.Collinear config.m config.c config.c :=
      collinear_refl_right G config.m config.c
    have habc : G.Collinear config.a config.b config.c :=
      collinear_three_on_line G config.c_ne_m.symm
        hmc_a hmc_b hmc_c
    exact config.triangle_nondegenerate habc
  obtain ⟨q, hcq_am⟩ :=
    parallel_through_offpoint_exists G hc_off_am
  obtain ⟨d, habd, hcqd⟩ :=
    parallel_transversal_meets G hcq_am
      (collinear_cyclic G
        (collinear_refl_left G config.a config.b))
      (collinear_cyclic G
        (collinear_refl_left G config.a config.m))
      (collinear_refl_right G config.a config.m)
      hm_off_ab
  have hcd : config.c ≠ d := by
    intro h
    subst d
    exact config.triangle_nondegenerate habd
  have hcd_am : Parallel G config.c d config.a config.m :=
    parallel_rebase_left G hcq_am
      (collinear_cyclic G
        (collinear_refl_left G config.c q))
      hcqd hcd
  exact ⟨d, habd,
    parallel_reverse_right G
      (parallel_symm G hcd_am)⟩

/--
The exterior position of `m` determines on which part of the ray `a-b` the
parallel intersection lies.
-/
theorem ExteriorLineConfiguration.parallel_point_ordered
    (config : ExteriorLineConfiguration G) :
    ∃ d,
      G.SameRay config.a config.b d ∧
      Parallel G config.a config.m d config.c ∧
      (G.Bet config.m config.b config.c →
        G.Bet config.a config.b d) ∧
      (G.Bet config.b config.c config.m →
        G.Bet config.a d config.b) := by
  obtain ⟨d, hd_on_ab, hparallel⟩ :=
    config.parallel_point_exists G
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
  have ham : config.a ≠ config.m :=
    hparallel.1
  have hdc : d ≠ config.c :=
    hparallel.2.1
  have hm_on_bc : G.Collinear config.b config.c config.m := by
    rcases config.m_on_extension with hmbc | hbcm
    · exact collinear_cyclic G (Or.inl hmbc)
    · exact Or.inl hbcm
  have ha_off_dc : ¬G.Collinear d config.c config.a := by
    intro h
    exact hparallel.2.2
      ⟨config.a,
        collinear_cyclic G
          (collinear_refl_left G config.a config.m),
        h⟩
  have hm_off_dc : ¬G.Collinear d config.c config.m := by
    intro h
    exact hparallel.2.2
      ⟨config.m,
        collinear_refl_right G config.a config.m,
        h⟩
  have hd_off_am : ¬G.Collinear config.a config.m d := by
    intro h
    exact hparallel.2.2
      ⟨d, h,
        collinear_cyclic G
          (collinear_refl_left G d config.c)⟩
  have hc_off_am : ¬G.Collinear config.a config.m config.c := by
    intro h
    exact hparallel.2.2
      ⟨config.c, h,
        collinear_refl_right G d config.c⟩
  have hb_off_am : ¬G.Collinear config.a config.m config.b := by
    intro h
    have hmb_a : G.Collinear config.m config.b config.a :=
      collinear_cyclic G h
    have hmb_c : G.Collinear config.m config.b config.c :=
      collinear_cyclic G
        (collinear_cyclic G hm_on_bc)
    have hmb_b : G.Collinear config.m config.b config.b :=
      collinear_refl_right G config.m config.b
    exact config.triangle_nondegenerate
      (collinear_three_on_line G
        config.b_ne_m.symm
        hmb_a hmb_b hmb_c)
  have hdb : d ≠ config.b := by
    intro h
    have hdc_m : G.Collinear d config.c config.m := by
      rw [h]
      exact hm_on_bc
    exact hm_off_dc hdc_m
  have hda : d ≠ config.a := by
    intro h
    subst d
    exact hparallel.2.2
      ⟨config.a,
        collinear_cyclic G
          (collinear_refl_left G
            config.a config.m),
        collinear_cyclic G
          (collinear_refl_left G
            config.a config.c)⟩
  have hb_off_dc : ¬G.Collinear d config.c config.b := by
    intro hdc_b
    have hdb_d : G.Collinear d config.b d :=
      collinear_cyclic G
        (collinear_refl_left G d config.b)
    have hdb_c : G.Collinear d config.b config.c :=
      collinear_swap_last G hdc_b
    have hdb_a : G.Collinear d config.b config.a := by
      have hab_a : G.Collinear config.a config.b config.a :=
        collinear_cyclic G
          (collinear_refl_left G config.a config.b)
      exact collinear_three_on_line G hab
        hd_on_ab
        (collinear_refl_right G config.a config.b)
        hab_a
    have hdc_a : G.Collinear d config.c config.a :=
      collinear_three_on_line G hdb
        hdb_d hdb_c hdb_a
    exact ha_off_dc hdc_a
  have hnot_am_opposite :
      ¬G.OppositeSides d config.c config.a config.m :=
    not_oppositeSides_of_parallel_endpoints G hparallel
  have hd_order :
      G.Bet config.a config.b d ∨
        G.Bet config.a d config.b := by
    rcases hd_on_ab with habd | hbda | hdab
    · exact Or.inl habd
    · exact Or.inr (bet_symm G hbda)
    · exfalso
      rcases config.m_on_extension with hmbc | hbcm
      · have hdb_opposite :
            G.OppositeSides config.a config.m d config.b :=
          ⟨hd_off_am, hb_off_am, config.a,
            collinear_cyclic G
              (collinear_refl_left G config.a config.m),
            hdab⟩
        have hnot_bc :
            ¬G.OppositeSides config.a config.m
              config.b config.c :=
          not_oppositeSides_of_outward_bet G
            (collinear_refl_right G config.a config.m)
            hmbc
        rcases Plane.Axioms.planeSeparation
            config.a config.m d config.b config.c
            hdb_opposite hc_off_am with
          hdc_opposite | hbc_opposite
        · exact
            (not_oppositeSides_of_parallel_endpoints G
              (parallel_symm G hparallel))
              hdc_opposite
        · exact hnot_bc hbc_opposite
      · have hbm_opposite :
            G.OppositeSides d config.c
              config.b config.m :=
          ⟨hb_off_dc, hm_off_dc, config.c,
            collinear_refl_right G d config.c,
            hbcm⟩
        have hnot_ab :
            ¬G.OppositeSides d config.c
              config.a config.b :=
          not_oppositeSides_of_outward_bet G
            (collinear_cyclic G
              (collinear_refl_left G d config.c))
            hdab
        rcases Plane.Axioms.planeSeparation
            d config.c config.b config.m config.a
            hbm_opposite ha_off_dc with
          hba_opposite | hma_opposite
        · exact hnot_ab
            (oppositeSides_symm G hba_opposite)
        · exact hnot_am_opposite
            (oppositeSides_symm G hma_opposite)
  have hd_ray : G.SameRay config.a config.b d := by
    refine ⟨hab.symm, hda, hd_on_ab, ?_⟩
    · intro hbad
      rcases hd_order with habd | hadb
      · have hcycle : G.Bet config.b config.a config.b :=
          bet_inner_trans G hbad habd
        exact hab
          (Plane.Axioms.betweennessIdentity
            config.b config.a hcycle).symm
      · have hcycle : G.Bet config.b config.a config.b :=
          bet_outer_trans G hbad hadb hda.symm
        exact hab
          (Plane.Axioms.betweennessIdentity
            config.b config.a hcycle).symm
  have first_order :
      G.Bet config.m config.b config.c →
        G.Bet config.a config.b d := by
    intro hmbc
    rcases hd_order with habd | hadb
    · exact habd
    · have hb_off_dc' :
          ¬G.Collinear d config.c config.b :=
        hb_off_dc
      have hab_opposite :
          G.OppositeSides d config.c
            config.a config.b :=
        ⟨ha_off_dc, hb_off_dc', d,
          collinear_cyclic G
            (collinear_refl_left G d config.c),
          hadb⟩
      have hbm_opposite :
          G.OppositeSides d config.c
            config.b config.m := by
        rcases Plane.Axioms.planeSeparation
            d config.c config.a config.b config.m
            hab_opposite hm_off_dc with
          ham_opposite | hbm_opposite
        · exact False.elim
            (hnot_am_opposite ham_opposite)
        · exact hbm_opposite
      obtain ⟨_, _, z, hz_dc, hbzm⟩ :=
        hbm_opposite
      have hz_bm : G.Collinear config.b config.m z :=
        collinear_swap_last G (Or.inl hbzm)
      have hc_bm : G.Collinear config.b config.m config.c :=
        collinear_swap G (Or.inl hmbc)
      have hzm_c : G.Collinear z config.c config.m :=
        collinear_three_on_line G config.b_ne_m
          hz_bm hc_bm
          (collinear_refl_right G config.b config.m)
      have hzc_d : G.Collinear z config.c d := by
        exact collinear_cyclic G
          (collinear_swap_last G hz_dc)
      have hzc_c : G.Collinear z config.c config.c :=
        collinear_refl_right G z config.c
      have hzc : z = config.c := by
        apply Classical.byContradiction
        intro hzc_ne
        exact hm_off_dc
          (collinear_three_on_line G hzc_ne
            hzc_d hzc_c hzm_c)
      subst z
      have hbc_eq : config.b = config.c :=
        bet_antisymm G hmbc
          (bet_symm G hbzm)
      exact False.elim (hbc hbc_eq)
  have second_order :
      G.Bet config.b config.c config.m →
        G.Bet config.a d config.b := by
    intro hbcm
    rcases hd_order with habd | hadb
    · have hbm_opposite :
          G.OppositeSides d config.c
            config.b config.m :=
        ⟨hb_off_dc, hm_off_dc, config.c,
          collinear_refl_right G d config.c,
          hbcm⟩
      have hba_opposite :
          G.OppositeSides d config.c
            config.b config.a := by
        rcases Plane.Axioms.planeSeparation
            d config.c config.b config.m config.a
            hbm_opposite ha_off_dc with
          hba_opposite | hma_opposite
        · exact hba_opposite
        · exact False.elim
            (hnot_am_opposite
              (oppositeSides_symm G hma_opposite))
      obtain ⟨_, _, z, hz_dc, hbza⟩ :=
        hba_opposite
      have hz_ba : G.Collinear config.b config.a z :=
        collinear_swap_last G (Or.inl hbza)
      have hd_ba : G.Collinear config.b config.a d :=
        collinear_swap G (Or.inl habd)
      have hza_d : G.Collinear z d config.a :=
        collinear_three_on_line G hab.symm
          hz_ba hd_ba
          (collinear_refl_right G
            config.b config.a)
      have hzd_c : G.Collinear z d config.c :=
        collinear_cyclic G
          (collinear_cyclic G hz_dc)
      have hzd_d : G.Collinear z d d :=
        collinear_refl_right G z d
      have hzd : z = d := by
        apply Classical.byContradiction
        intro hzd_ne
        exact ha_off_dc
          (collinear_three_on_line G
            (p := d) (q := config.c)
            (r := config.a) hzd_ne
            hzd_d hzd_c hza_d)
      subst z
      have hadb' : G.Bet config.a d config.b :=
        bet_symm G hbza
      have hbd_eq : config.b = d :=
        bet_antisymm G habd hadb'
      exact False.elim (hdb hbd_eq.symm)
    · exact hadb
  exact ⟨d, hd_ray, hparallel,
    first_order, second_order⟩

/-- Exterior parallel ratio when `m` lies beyond `c`. -/
theorem exterior_parallel_ratio_beyond_c
    (L : LengthMeasurement G) [L.Axioms]
    (config : ExteriorLineConfiguration G)
    (hbcm : G.Bet config.b config.c config.m) :
    ∃ d,
      G.Bet config.a d config.b ∧
      Parallel G config.a config.m d config.c ∧
      L.scalar.mul
          (L.length config.b config.m)
          (L.length config.a d) =
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
  obtain ⟨d, hd_ray, hparallel, _, horder⟩ :=
    config.parallel_point_ordered G
  have hadb : G.Bet config.a d config.b :=
    horder hbcm
  have hdb : d ≠ config.b := by
    intro h
    subst d
    have hdm : G.Collinear config.b config.c config.m :=
      Or.inl hbcm
    exact hparallel.2.2
      ⟨config.m,
        collinear_refl_right G config.a config.m,
        hdm⟩
  have hBA_D : G.SameRay config.b config.a d := by
    refine ⟨hab, hdb, ?_, ?_⟩
    · exact collinear_cyclic G
        (collinear_cyclic G (Or.inl hadb))
    · intro habd
      exact hdb
        (bet_antisymm G habd hadb).symm
  have hBM_C : G.SameRay config.b config.m config.c := by
    refine ⟨config.b_ne_m.symm, hbc.symm, ?_, ?_⟩
    · exact collinear_swap_last G (Or.inl hbcm)
    · intro hmbc
      have hcbm : G.Bet config.c config.b config.m :=
        bet_symm G hmbc
      have hbcb : G.Bet config.b config.c config.b :=
        bet_inner_trans G hbcm hcbm
      exact hbc
        (Plane.Axioms.betweennessIdentity
          config.b config.c hbcb)
  have hm_off_ba :
      ¬G.Collinear config.b config.a config.m := by
    intro hbam
    have hbm_a : G.Collinear config.b config.m config.a :=
      collinear_swap_last G hbam
    have hbm_c : G.Collinear config.b config.m config.c :=
      collinear_swap_last G (Or.inl hbcm)
    have hbm_b : G.Collinear config.b config.m config.b :=
      collinear_cyclic G
        (collinear_refl_left G config.b config.m)
    have hba_c : G.Collinear config.b config.a config.c :=
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
    LengthMeasurement.Axioms.length_symm _ _
  have hbd_db :
      L.length config.b d = L.length d config.b :=
    LengthMeasurement.Axioms.length_symm _ _
  have hab_add :
      L.length config.a config.b =
        L.scalar.add
          (L.length config.a d)
          (L.length d config.b) :=
    LengthMeasurement.Axioms.bet_additive _ _ _ hadb
  have hbm_add :
      L.length config.b config.m =
        L.scalar.add
          (L.length config.b config.c)
          (L.length config.c config.m) :=
    LengthMeasurement.Axioms.bet_additive _ _ _ hbcm
  rw [hba_ab, hab_add, hbm_add, hbd_db] at hproduct
  rw [scalar_right_distrib,
    scalar_right_distrib] at hproduct
  rw [OrderedScalar.Axioms.mul_comm
    (L.length d config.b)
    (L.length config.b config.c)] at hproduct
  rw [OrderedScalar.Axioms.add_comm] at hproduct
  have hcross :
      L.scalar.mul
          (L.length config.a d)
          (L.length config.b config.c) =
        L.scalar.mul
          (L.length config.c config.m)
          (L.length d config.b) :=
    scalar_add_left_cancel L.scalar hproduct
  refine ⟨d, hadb, hparallel, ?_⟩
  rw [hbm_add, hab_add]
  rw [scalar_right_distrib,
    OrderedScalar.Axioms.left_distrib]
  rw [OrderedScalar.Axioms.mul_comm
    (L.length config.b config.c)
    (L.length config.a d)]
  rw [hcross]
  rw [OrderedScalar.Axioms.mul_comm
    (L.length config.c config.m)
    (L.length config.a d)]
  exact OrderedScalar.Axioms.add_comm _ _

/-- Exterior parallel ratio when `m` lies beyond `b`. -/
theorem exterior_parallel_ratio_beyond_b
    (L : LengthMeasurement G) [L.Axioms]
    (config : ExteriorLineConfiguration G)
    (hmbc : G.Bet config.m config.b config.c) :
    ∃ d,
      G.Bet config.a config.b d ∧
      Parallel G config.a config.m d config.c ∧
      L.scalar.mul
          (L.length config.b config.m)
          (L.length config.a d) =
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
  obtain ⟨d, _, hparallel, horder, _⟩ :=
    config.parallel_point_ordered G
  have habd : G.Bet config.a config.b d :=
    horder hmbc
  have hdb : d ≠ config.b := by
    intro h
    subst d
    have hdm : G.Collinear config.b config.c config.m :=
      collinear_cyclic G (Or.inl hmbc)
    exact hparallel.2.2
      ⟨config.m,
        collinear_refl_right G config.a config.m,
        hdm⟩
  have hm_off_ba :
      ¬G.Collinear config.b config.a config.m := by
    intro hbam
    have hbm_a : G.Collinear config.b config.m config.a :=
      collinear_swap_last G hbam
    have hbm_c : G.Collinear config.b config.m config.c :=
      collinear_swap G (Or.inl hmbc)
    have hbm_b : G.Collinear config.b config.m config.b :=
      collinear_cyclic G
        (collinear_refl_left G config.b config.m)
    have hba_c : G.Collinear config.b config.a config.c :=
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
    LengthMeasurement.Axioms.length_symm _ _
  have had_add :
      L.length config.a d =
        L.scalar.add
          (L.length config.a config.b)
          (L.length config.b d) :=
    LengthMeasurement.Axioms.bet_additive _ _ _ habd
  have hmc_add :
      L.length config.m config.c =
        L.scalar.add
          (L.length config.m config.b)
          (L.length config.b config.c) :=
    LengthMeasurement.Axioms.bet_additive _ _ _ hmbc
  have hcm_mc :
      L.length config.c config.m =
        L.length config.m config.c :=
    LengthMeasurement.Axioms.length_symm _ _
  have hmb_bm :
      L.length config.m config.b =
        L.length config.b config.m :=
    LengthMeasurement.Axioms.length_symm _ _
  rw [hba_ab] at hproduct
  have hproduct' :
      L.scalar.mul
          (L.length config.b config.m)
          (L.length config.b d) =
        L.scalar.mul
          (L.length config.b config.c)
          (L.length config.a config.b) := by
    calc
      _ = L.scalar.mul
          (L.length config.a config.b)
          (L.length config.b config.c) :=
        hproduct.symm
      _ = _ := OrderedScalar.Axioms.mul_comm _ _
  refine ⟨d, habd, hparallel, ?_⟩
  rw [had_add, hcm_mc, hmc_add, hmb_bm]
  rw [OrderedScalar.Axioms.left_distrib,
    scalar_right_distrib]
  rw [hproduct']

/--
The product form of Menelaus needed for this problem.

The proof constructs through `c` a parallel to the transversal `e-p`, obtains the
two fourth-proportional identities directly, and eliminates the constructed length.
-/
theorem menelaus_product
    (L : LengthMeasurement G) [L.Axioms]
    {a b c e h p : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (haeb : G.Bet a e b)
    (hahc : G.Bet a h c)
    (hae : a ≠ e)
    (heb : e ≠ b)
    (hah : a ≠ h)
    (hhc : h ≠ c)
    (hehp : G.Collinear e h p)
    (heh : e ≠ h)
    (hpb : p ≠ b)
    (hpc : p ≠ c)
    (hp_exterior : G.Bet p b c ∨ G.Bet b c p) :
    L.scalar.mul
        (L.scalar.mul (L.length a e) (L.length b p))
        (L.length h c) =
      L.scalar.mul
        (L.scalar.mul (L.length e b) (L.length c p))
        (L.length a h) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hab : a ≠ b := by
    intro hab
    subst b
    apply hnondegenerate
    exact collinear_refl_left G a c
  have hac : a ≠ c := by
    intro hac
    subst c
    apply hnondegenerate
    exact collinear_cyclic G
      (collinear_refl_left G a b)
  have hbc : b ≠ c := by
    intro hbc
    apply hnondegenerate
    rw [hbc]
    exact collinear_refl_right G a c
  have hebc : ¬G.Collinear e b c := by
    intro hebc
    have heba : G.Collinear e b a :=
      collinear_cyclic G (Or.inl haeb)
    have hebe : G.Collinear e b e :=
      collinear_cyclic G
        (collinear_refl_left G e b)
    have hebb : G.Collinear e b b :=
      collinear_refl_right G e b
    have habc : G.Collinear a b c :=
      collinear_three_on_line G heb
        heba hebb hebc
    exact hnondegenerate habc
  have hep : e ≠ p := by
    intro hep
    subst p
    apply hebc
    rcases hp_exterior with hpbc | hbcp
    · exact Or.inl hpbc
    · exact collinear_cyclic G
        (collinear_cyclic G (Or.inl hbcp))
  let exterior : ExteriorLineConfiguration G :=
    { a := e
      b := b
      c := c
      m := p
      triangle_nondegenerate := hebc
      m_on_extension := hp_exterior
      b_ne_m := hpb.symm
      c_ne_m := hpc.symm }
  obtain ⟨q, heq_order, hep_qc, hratio⟩ :
      ∃ q,
        (G.Bet e b q ∨ G.Bet e q b) ∧
        Parallel G e p q c ∧
        L.scalar.mul (L.length b p) (L.length e q) =
          L.scalar.mul (L.length c p) (L.length e b) := by
    rcases hp_exterior with hpbc | hbcp
    · obtain ⟨q, hebq, hparallel, hproduct⟩ :=
        exterior_parallel_ratio_beyond_b G L exterior hpbc
      exact ⟨q, Or.inl hebq, hparallel, hproduct⟩
    · obtain ⟨q, heqb, hparallel, hproduct⟩ :=
        exterior_parallel_ratio_beyond_c G L exterior hbcp
      exact ⟨q, Or.inr heqb, hparallel, hproduct⟩
  have hae_q : G.Bet a e q := by
    rcases heq_order with hebq | heqb
    · exact bet_outer_trans G haeb hebq heb
    · exact bet_inner_trans G haeb heqb
  have haq : a ≠ q := by
    intro haq
    subst q
    exact hae
      (Plane.Axioms.betweennessIdentity a e hae_q)
  have heq : e ≠ q := by
    intro heq
    subst q
    exact hep_qc.2.2
      ⟨e,
        collinear_cyclic G
          (collinear_refl_left G e p),
        collinear_cyclic G
          (collinear_refl_left G e c)⟩
  have heh_qc : Parallel G e h q c := by
    apply parallel_replace_left G hep_qc heh
    · exact collinear_cyclic G
        (collinear_refl_left G e p)
    · exact collinear_swap_last G hehp
  have haeh : ¬G.Collinear a e h := by
    intro haeh
    have hae_b : G.Collinear a e b :=
      Or.inl haeb
    have hae_c : G.Collinear a e c := by
      have hah_c : G.Collinear a h c :=
        Or.inl hahc
      have hah_a : G.Collinear a h a :=
        collinear_cyclic G
          (collinear_refl_left G a h)
      have hah_e : G.Collinear a h e :=
        collinear_swap_last G haeh
      have hah_c' : G.Collinear a h c :=
        hah_c
      have hae_c' : G.Collinear a e c :=
        collinear_three_on_line G hah
          hah_a hah_e hah_c'
      exact hae_c'
    exact hnondegenerate
      (collinear_three_on_line G hae
        (collinear_cyclic G
          (collinear_refl_left G a e))
        hae_b hae_c)
  have hAE_Q : G.SameRay a e q :=
    sameRay_of_order G hae.symm haq.symm
      (Or.inl hae_q)
  have hAH_C : G.SameRay a h c :=
    sameRay_of_order G hah.symm hac.symm
      (Or.inl hahc)
  have hconfiguration :
      G.FourthProportionalConfiguration
        a e h q c :=
    ⟨hAE_Q, hAH_C, haeh,
      strictlyParallel_of_parallel G heh_qc⟩
  have hparallel_product :
      L.scalar.mul (L.length a e) (L.length a c) =
        L.scalar.mul (L.length a h) (L.length a q) :=
    LengthMeasurement.Axioms.fourth_proportional_mul
      a e h q c hconfiguration
  have hac_add :
      L.length a c =
        L.scalar.add (L.length a h) (L.length h c) :=
    LengthMeasurement.Axioms.bet_additive _ _ _ hahc
  have haq_add :
      L.length a q =
        L.scalar.add (L.length a e) (L.length e q) :=
    LengthMeasurement.Axioms.bet_additive _ _ _ hae_q
  rw [hac_add, haq_add,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib] at hparallel_product
  rw [OrderedScalar.Axioms.mul_comm
    (L.length a h) (L.length a e)] at hparallel_product
  have hsmall :
      L.scalar.mul (L.length a e) (L.length h c) =
        L.scalar.mul (L.length a h) (L.length e q) :=
    scalar_add_left_cancel L.scalar hparallel_product
  calc
    L.scalar.mul
        (L.scalar.mul (L.length a e) (L.length b p))
        (L.length h c) =
      L.scalar.mul
        (L.scalar.mul (L.length b p) (L.length a e))
        (L.length h c) := by
          rw [OrderedScalar.Axioms.mul_comm
            (L.length a e) (L.length b p)]
    _ = L.scalar.mul
        (L.length b p)
        (L.scalar.mul (L.length a e) (L.length h c)) :=
          OrderedScalar.Axioms.mul_assoc _ _ _
    _ = L.scalar.mul
        (L.length b p)
        (L.scalar.mul (L.length a h) (L.length e q)) := by
          rw [hsmall]
    _ = L.scalar.mul
        (L.scalar.mul (L.length b p) (L.length a h))
        (L.length e q) :=
          (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = L.scalar.mul
        (L.scalar.mul (L.length a h) (L.length b p))
        (L.length e q) := by
          rw [OrderedScalar.Axioms.mul_comm
            (L.length b p) (L.length a h)]
    _ = L.scalar.mul
        (L.length a h)
        (L.scalar.mul (L.length b p) (L.length e q)) :=
          OrderedScalar.Axioms.mul_assoc _ _ _
    _ = L.scalar.mul
        (L.length a h)
        (L.scalar.mul (L.length c p) (L.length e b)) := by
          rw [hratio]
    _ = L.scalar.mul
        (L.scalar.mul (L.length c p) (L.length e b))
        (L.length a h) := by
          rw [OrderedScalar.Axioms.mul_comm]
    _ = L.scalar.mul
        (L.scalar.mul (L.length e b) (L.length c p))
        (L.length a h) := by
          rw [OrderedScalar.Axioms.mul_comm
            (L.length c p) (L.length e b)]

/--
A line through strict interior points of two sides of a triangle can meet the
third side-line only on an exterior part of that line.
-/
theorem interior_transversal_exterior
    {a b c e h p : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (haeb : G.Bet a e b)
    (hahc : G.Bet a h c)
    (hae : a ≠ e)
    (heb : e ≠ b)
    (hah : a ≠ h)
    (hhc : h ≠ c)
    (hehp : G.Collinear e h p)
    (hpbc : G.Collinear b c p) :
    G.Bet p b c ∨ G.Bet b c p := by
  have heh : e ≠ h := by
    intro heh
    subst h
    have hae_c : G.Collinear a e c :=
      Or.inl hahc
    exact hnondegenerate
      (collinear_three_on_line G hae
        (collinear_cyclic G
          (collinear_refl_left G a e))
        (Or.inl haeb) hae_c)
  have ha_off_eh : ¬G.Collinear e h a := by
    intro heha
    have hae_h : G.Collinear a e h :=
      collinear_cyclic G
        (collinear_cyclic G heha)
    have hae_b : G.Collinear a e b :=
      Or.inl haeb
    have hae_c : G.Collinear a e c := by
      have hah_e : G.Collinear a h e :=
        collinear_swap_last G hae_h
      have hah_c : G.Collinear a h c :=
        Or.inl hahc
      exact collinear_three_on_line G hah
        (collinear_cyclic G
          (collinear_refl_left G a h))
        hah_e hah_c
    exact hnondegenerate
      (collinear_three_on_line G hae
        (collinear_cyclic G
          (collinear_refl_left G a e))
        hae_b hae_c)
  have hb_off_eh : ¬G.Collinear e h b := by
    intro hehb
    have heb_e : G.Collinear e b e :=
      collinear_cyclic G
        (collinear_refl_left G e b)
    have heb_h : G.Collinear e b h :=
      collinear_swap_last G hehb
    have heb_a : G.Collinear e b a :=
      collinear_cyclic G (Or.inl haeb)
    have heh_a : G.Collinear e h a :=
      collinear_three_on_line G heb
        heb_e heb_h heb_a
    exact ha_off_eh heh_a
  have hc_off_eh : ¬G.Collinear e h c := by
    intro hehc
    have hhc_e : G.Collinear h c e :=
      collinear_cyclic G hehc
    have hhc_h : G.Collinear h c h :=
      collinear_cyclic G
        (collinear_refl_left G h c)
    have hhc_a : G.Collinear h c a :=
      collinear_cyclic G (Or.inl hahc)
    have heh_a : G.Collinear e h a :=
      collinear_three_on_line G hhc
        hhc_e hhc_h hhc_a
    exact ha_off_eh heh_a
  have ha_opposite_b :
      G.OppositeSides e h a b :=
    ⟨ha_off_eh, hb_off_eh, e,
      collinear_cyclic G
        (collinear_refl_left G e h),
      haeb⟩
  have ha_opposite_c :
      G.OppositeSides e h a c :=
    ⟨ha_off_eh, hc_off_eh, h,
      collinear_refl_right G e h,
      hahc⟩
  have hnot_bc :
      ¬G.OppositeSides e h b c :=
    not_oppositeSides_of_common_opposite G
      (oppositeSides_symm G ha_opposite_b)
      (oppositeSides_symm G ha_opposite_c)
  rcases hpbc with hbcp | hcpb | hpbc
  · exact Or.inr hbcp
  · exfalso
    exact hnot_bc
      ⟨hb_off_eh, hc_off_eh, p, hehp,
        bet_symm G hcpb⟩
  · exact Or.inl hpbc

/-- The exterior ratio determines a point uniquely on the part beyond `c`. -/
theorem exterior_ratio_unique_beyond_c
    (L : LengthMeasurement G) [L.Axioms]
    {b c p q : G.Point}
    (hbc : b ≠ c)
    (hbcp : G.Bet b c p)
    (hbcq : G.Bet b c q)
    (hpc : p ≠ c)
    (hqc : q ≠ c)
    (hcross :
      L.scalar.mul (L.length b p) (L.length c q) =
        L.scalar.mul (L.length b q) (L.length c p)) :
    p = q := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hbp :
      L.length b p =
        L.scalar.add (L.length b c) (L.length c p) :=
    LengthMeasurement.Axioms.bet_additive _ _ _ hbcp
  have hbq :
      L.length b q =
        L.scalar.add (L.length b c) (L.length c q) :=
    LengthMeasurement.Axioms.bet_additive _ _ _ hbcq
  rw [hbp, hbq, scalar_right_distrib,
    scalar_right_distrib] at hcross
  rw [OrderedScalar.Axioms.mul_comm
    (L.length c q) (L.length c p)] at hcross
  rw [OrderedScalar.Axioms.add_comm,
    OrderedScalar.Axioms.add_comm
      (L.scalar.mul (L.length b c) (L.length c p))
      (L.scalar.mul (L.length c p) (L.length c q))] at hcross
  have hshort :
      L.scalar.mul (L.length b c) (L.length c q) =
        L.scalar.mul (L.length b c) (L.length c p) :=
    scalar_add_left_cancel L.scalar hcross
  have hbc_length :
      L.length b c ≠ L.scalar.zero := by
    intro hzero
    exact hbc
      ((LengthMeasurement.Axioms.length_eq_zero b c).mp
        hzero)
  have hlength :
      L.length c q = L.length c p :=
    scalar_mul_left_cancel L.scalar hbc_length hshort
  have hray : G.SameRay c p q :=
    sameRay_of_common_predecessor G
      hbc hbcp hbcq hpc hqc
  have hcongruent : G.Congruent c p c q := by
    exact
      (LengthMeasurement.Axioms.congruent_iff
        (L := L) c p c q).mpr hlength.symm
  exact sameRay_congruent_unique G hray hcongruent

/-- The exterior ratio determines a point uniquely on the part beyond `b`. -/
theorem exterior_ratio_unique_beyond_b
    (L : LengthMeasurement G) [L.Axioms]
    {b c p q : G.Point}
    (hbc : b ≠ c)
    (hpbc : G.Bet p b c)
    (hqbc : G.Bet q b c)
    (hpb : p ≠ b)
    (hqb : q ≠ b)
    (hcross :
      L.scalar.mul (L.length b p) (L.length c q) =
        L.scalar.mul (L.length b q) (L.length c p)) :
    p = q := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hcp :
      L.length c p =
        L.scalar.add (L.length c b) (L.length b p) := by
    have hcbp : G.Bet c b p :=
      bet_symm G hpbc
    exact LengthMeasurement.Axioms.bet_additive _ _ _ hcbp
  have hcq :
      L.length c q =
        L.scalar.add (L.length c b) (L.length b q) := by
    have hcbq : G.Bet c b q :=
      bet_symm G hqbc
    exact LengthMeasurement.Axioms.bet_additive _ _ _ hcbq
  rw [hcp, hcq,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib] at hcross
  rw [OrderedScalar.Axioms.mul_comm
    (L.length b q) (L.length b p)] at hcross
  rw [OrderedScalar.Axioms.add_comm,
    OrderedScalar.Axioms.add_comm
      (L.scalar.mul (L.length b q) (L.length c b))
      (L.scalar.mul (L.length b p) (L.length b q))] at hcross
  have hshort :
      L.scalar.mul (L.length b p) (L.length c b) =
        L.scalar.mul (L.length b q) (L.length c b) :=
    scalar_add_left_cancel L.scalar hcross
  rw [OrderedScalar.Axioms.mul_comm
      (L.length b p) (L.length c b),
    OrderedScalar.Axioms.mul_comm
      (L.length b q) (L.length c b)] at hshort
  have hcb_length :
      L.length c b ≠ L.scalar.zero := by
    intro hzero
    exact hbc
      ((LengthMeasurement.Axioms.length_eq_zero c b).mp
        hzero).symm
  have hlength :
      L.length b p = L.length b q :=
    scalar_mul_left_cancel L.scalar hcb_length hshort
  have hray : G.SameRay b p q :=
    sameRay_of_common_predecessor G
      hbc.symm (bet_symm G hpbc) (bet_symm G hqbc)
      hpb hqb
  have hcongruent : G.Congruent b p b q :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) b p b q).mpr hlength
  exact sameRay_congruent_unique G hray hcongruent

/--
Points on opposite exterior parts of a segment cannot have the same exterior
cross-ratio product.
-/
theorem exterior_ratio_not_opposite_branches
    (L : LengthMeasurement G) [L.Axioms]
    {b c p q : G.Point}
    (hbc : b ≠ c)
    (hpbc : G.Bet p b c)
    (hbcq : G.Bet b c q)
    (hcross :
      L.scalar.mul (L.length b p) (L.length c q) =
        L.scalar.mul (L.length b q) (L.length c p)) :
    False := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hcp :
      L.length c p =
        L.scalar.add (L.length b p) (L.length b c) := by
    have hpc :
        L.length p c =
          L.scalar.add (L.length p b) (L.length b c) :=
      LengthMeasurement.Axioms.bet_additive _ _ _ hpbc
    rw [LengthMeasurement.Axioms.length_symm c p,
      hpc,
      LengthMeasurement.Axioms.length_symm p b]
  have hbq :
      L.length b q =
        L.scalar.add (L.length b c) (L.length c q) :=
    LengthMeasurement.Axioms.bet_additive _ _ _ hbcq
  rw [hcp, hbq] at hcross
  have hexpand :
      L.scalar.mul
          (L.scalar.add (L.length b c) (L.length c q))
          (L.scalar.add (L.length b p) (L.length b c)) =
        L.scalar.add
          (L.scalar.mul (L.length b p) (L.length c q))
          (L.scalar.add
            (L.scalar.mul (L.length b c) (L.length b c))
            (L.scalar.add
              (L.scalar.mul (L.length b c) (L.length b p))
              (L.scalar.mul (L.length c q) (L.length b c)))) := by
    rw [scalar_right_distrib,
      OrderedScalar.Axioms.left_distrib,
      OrderedScalar.Axioms.left_distrib]
    simp only [OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm,
      OrderedScalar.Axioms.mul_comm]
  rw [hexpand] at hcross
  have hzero :
      L.scalar.zero =
        L.scalar.add
          (L.scalar.mul (L.length b c) (L.length b c))
          (L.scalar.add
            (L.scalar.mul (L.length b c) (L.length b p))
            (L.scalar.mul (L.length c q) (L.length b c))) := by
    apply scalar_add_left_cancel L.scalar
      (x := L.scalar.mul (L.length b p) (L.length c q))
    rw [OrderedScalar.Axioms.add_zero]
    exact hcross
  have hbc_length :
      L.length b c ≠ L.scalar.zero := by
    intro hzero
    exact hbc
      ((LengthMeasurement.Axioms.length_eq_zero b c).mp
        hzero)
  have hbc_square_nonzero :
      L.scalar.mul (L.length b c) (L.length b c) ≠
        L.scalar.zero := by
    intro hsquare
    exact hbc_length
      (scalar_mul_eq_zero_of_left_nonzero
        L.scalar hbc_length hsquare)
  have hbc_nonnegative :
      L.scalar.le L.scalar.zero (L.length b c) :=
    LengthMeasurement.Axioms.length_nonnegative _ _
  have hbp_nonnegative :
      L.scalar.le L.scalar.zero (L.length b p) :=
    LengthMeasurement.Axioms.length_nonnegative _ _
  have hcq_nonnegative :
      L.scalar.le L.scalar.zero (L.length c q) :=
    LengthMeasurement.Axioms.length_nonnegative _ _
  have htail_nonnegative :
      L.scalar.le L.scalar.zero
        (L.scalar.add
          (L.scalar.mul (L.length b c) (L.length b p))
          (L.scalar.mul (L.length c q) (L.length b c))) := by
    have h₁ :=
      OrderedScalar.Axioms.mul_nonneg
        (L.length b c) (L.length b p)
        hbc_nonnegative hbp_nonnegative
    have h₂ :=
      OrderedScalar.Axioms.mul_nonneg
        (L.length c q) (L.length b c)
        hcq_nonnegative hbc_nonnegative
    have h :=
      OrderedScalar.Axioms.add_le_add_right
        L.scalar.zero
        (L.scalar.mul (L.length c q) (L.length b c))
        (L.scalar.mul (L.length b c) (L.length b p))
        h₂
    rw [OrderedScalar.Axioms.zero_add,
      OrderedScalar.Axioms.add_comm] at h
    exact OrderedScalar.Axioms.le_trans
      L.scalar.zero
      (L.scalar.mul (L.length b c) (L.length b p))
      _ h₁ h
  have hsquare_nonnegative :=
    OrderedScalar.Axioms.mul_nonneg
      (L.length b c) (L.length b c)
      hbc_nonnegative hbc_nonnegative
  have hsum_nonzero :=
    scalar_add_nonzero_of_nonnegative_left
      L.scalar hbc_square_nonzero
      hsquare_nonnegative htail_nonnegative
  exact hsum_nonzero hzero.symm

/-- The exterior product determines its point on the whole exterior line. -/
theorem exterior_ratio_unique
    (L : LengthMeasurement G) [L.Axioms]
    {b c p q : G.Point}
    (hbc : b ≠ c)
    (hpb : p ≠ b)
    (hpc : p ≠ c)
    (hqb : q ≠ b)
    (hqc : q ≠ c)
    (hp : G.Bet p b c ∨ G.Bet b c p)
    (hq : G.Bet q b c ∨ G.Bet b c q)
    (hcross :
      L.scalar.mul (L.length b p) (L.length c q) =
        L.scalar.mul (L.length b q) (L.length c p)) :
    p = q := by
  rcases hp with hpbc | hbcp <;>
    rcases hq with hqbc | hbcq
  · exact exterior_ratio_unique_beyond_b G L
      hbc hpbc hqbc hpb hqb hcross
  · exact False.elim
      (exterior_ratio_not_opposite_branches G L
        hbc hpbc hbcq hcross)
  · exact False.elim
      (exterior_ratio_not_opposite_branches G L
        hbc hqbc hbcp hcross.symm)
  · exact exterior_ratio_unique_beyond_c G L
      hbc hbcp hbcq hpc hqc hcross

/-- Product relation cut out by an interior line parallel to the third side. -/
theorem interior_parallel_product
    (L : LengthMeasurement G) [L.Axioms]
    {a b c e h : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (haeb : G.Bet a e b)
    (hahc : G.Bet a h c)
    (hae : a ≠ e)
    (heb : e ≠ b)
    (hah : a ≠ h)
    (hhc : h ≠ c)
    (hparallel : Parallel G e h b c) :
    L.scalar.mul (L.length a e) (L.length h c) =
      L.scalar.mul (L.length a h) (L.length e b) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hab : a ≠ b := by
    intro hab
    subst b
    exact hnondegenerate
      (collinear_refl_left G a c)
  have hac : a ≠ c := by
    intro hac
    subst c
    exact hnondegenerate
      (collinear_cyclic G
        (collinear_refl_left G a b))
  have haeh : ¬G.Collinear a e h := by
    intro haeh
    have hae_b : G.Collinear a e b :=
      Or.inl haeb
    have hae_c : G.Collinear a e c := by
      have hah_e : G.Collinear a h e :=
        collinear_swap_last G haeh
      exact collinear_three_on_line G hah
        (collinear_cyclic G
          (collinear_refl_left G a h))
        hah_e (Or.inl hahc)
    exact hnondegenerate
      (collinear_three_on_line G hae
        (collinear_cyclic G
          (collinear_refl_left G a e))
        hae_b hae_c)
  have hAE_B : G.SameRay a e b :=
    sameRay_of_order G hae.symm hab.symm
      (Or.inl haeb)
  have hAH_C : G.SameRay a h c :=
    sameRay_of_order G hah.symm hac.symm
      (Or.inl hahc)
  have hconfiguration :
      G.FourthProportionalConfiguration
        a e h b c :=
    ⟨hAE_B, hAH_C, haeh,
      strictlyParallel_of_parallel G hparallel⟩
  have hproduct :
      L.scalar.mul (L.length a e) (L.length a c) =
        L.scalar.mul (L.length a h) (L.length a b) :=
    LengthMeasurement.Axioms.fourth_proportional_mul
      a e h b c hconfiguration
  have hac_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) a h c hahc
  have hab_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) a e b haeb
  rw [hac_add, hab_add,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib] at hproduct
  rw [OrderedScalar.Axioms.mul_comm
    (L.length a h) (L.length a e)] at hproduct
  exact scalar_add_left_cancel L.scalar hproduct

/-- No exterior point of a segment is equidistant from its endpoints. -/
theorem exterior_endpoint_lengths_ne
    (L : LengthMeasurement G) [L.Axioms]
    {b c p : G.Point}
    (hbc : b ≠ c)
    (hp : G.Bet p b c ∨ G.Bet b c p) :
    L.length b p ≠ L.length c p := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  intro hequal
  have hbc_length :
      L.length b c ≠ L.scalar.zero := by
    intro hzero
    exact hbc
      ((LengthMeasurement.Axioms.length_eq_zero b c).mp
        hzero)
  rcases hp with hpbc | hbcp
  · have hpc_add :
        L.length p c =
          L.scalar.add (L.length p b) (L.length b c) :=
      LengthMeasurement.Axioms.bet_additive _ _ _ hpbc
    rw [LengthMeasurement.Axioms.length_symm p c,
      LengthMeasurement.Axioms.length_symm p b,
      hequal] at hpc_add
    have hzero :
        L.length b c = L.scalar.zero := by
      have hcancel :
          L.scalar.add (L.length c p) L.scalar.zero =
            L.scalar.add (L.length c p) (L.length b c) := by
        rw [OrderedScalar.Axioms.add_zero]
        exact hpc_add
      exact (scalar_add_left_cancel L.scalar hcancel).symm
    exact hbc_length hzero
  · have hbp_add :
        L.length b p =
          L.scalar.add (L.length b c) (L.length c p) :=
      LengthMeasurement.Axioms.bet_additive _ _ _ hbcp
    rw [hequal] at hbp_add
    have hzero :
        L.length b c = L.scalar.zero := by
      have hcancel :
          L.scalar.add (L.length c p) L.scalar.zero =
            L.scalar.add (L.length c p) (L.length b c) := by
        rw [OrderedScalar.Axioms.add_zero,
          OrderedScalar.Axioms.add_comm]
        exact hbp_add
      exact (scalar_add_left_cancel L.scalar hcancel).symm
    exact hbc_length hzero

end Soultions.Sharygin.Page74.Problem28.Ratio
