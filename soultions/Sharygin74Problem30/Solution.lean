import Sharygin74Problem30.Configuration

/-!
# Proof of Sharygin, PDF page 74, problem 30
-/

namespace Soultions.Sharygin.Page74.Problem30.Solution

open Euclid Plane
open Soultions.Sharygin.Page74.Problem30.Tarski
open Soultions.Sharygin.Page74.Problem30.Midpoint
open Soultions.Sharygin.Page74.Problem30.Affine
open Soultions.Sharygin.Page74.Problem30.Similarity
open Soultions.Sharygin.Page74.Problem30.Projection
open Soultions.Sharygin.Page74.Problem30.Centroid
open Soultions.Sharygin.Page74.Problem30.Configuration
open Soultions.Sharygin.Page74.Problem30

variable (G : Plane) [G.Axioms]

/--
If `o` and `m` lie on `ac` with `AM = OC`, then the midpoint of `AC`
is also the midpoint of `OM`.
-/
private theorem complementary_points_midpoint
    {a c o m k : G.Point}
    (hac : a ≠ c)
    (haoc : G.Bet a o c)
    (hamc : G.Bet a m c)
    (ham_oc : G.Congruent a m o c)
    (hk : G.Midpoint a k c) :
    G.Midpoint o k m := by
  have hakc : PointReflection G k a c :=
    midpoint_as_pointReflection G hk
  obtain ⟨m', hom'⟩ :=
    pointReflection_exists G k o
  have hm'_inside : G.Bet a m' c := by
    have h :=
      pointReflection_preserves_bet G
        hakc hom' (pointReflection_symm G hakc)
        haoc
    exact bet_symm G h
  have ham'_co : G.Congruent a m' c o :=
    pointReflection_cross_congruent G
      hakc (pointReflection_symm G hom')
  have hcm'_ao : G.Congruent c m' a o :=
    pointReflection_cross_congruent G
      (pointReflection_symm G hakc)
      (pointReflection_symm G hom')
  have hm'm : m' = m := by
    by_cases ham : a = m
    · have hoc : o = c := by
        rw [← ham] at ham_oc
        exact Plane.Axioms.congruenceIdentity
          o c a (congruent_symm G ham_oc)
      have ham' : a = m' := by
        rw [hoc] at ham'_co
        exact Plane.Axioms.congruenceIdentity
          a m' c ham'_co
      exact ham'.symm.trans ham
    · have hmc_oa :
          G.Congruent m c o a :=
        segment_cancel_left G ham hamc
          (bet_symm G haoc)
          (congruent_trans G ham_oc
            (Plane.Axioms.congruenceReversal o c))
          (Plane.Axioms.congruenceReversal a c)
      have hcm_ao :
          G.Congruent c m a o := by
        exact congruent_trans G
          (Plane.Axioms.congruenceReversal c m)
          (congruent_trans G hmc_oa
            (Plane.Axioms.congruenceReversal o a))
      have ham'_am : G.Congruent a m' a m := by
        exact congruent_trans G ham'_co
          (congruent_trans G
            (Plane.Axioms.congruenceReversal c o)
            (congruent_symm G ham_oc))
      have hcm'_cm : G.Congruent c m' c m :=
        congruent_trans G hcm'_ao
          (congruent_symm G hcm_ao)
      exact tangent_circles_unique_of_between G
        hac hamc ham'_am hcm'_cm
  subst m'
  exact pointReflection_as_midpoint G hom'

private theorem scalar_add_left_cancel
    (S : OrderedScalar) [S.Axioms]
    {x y z : S.Carrier}
    (h : S.add x y = S.add x z) :
    y = z := by
  have h' := congrArg (fun w => S.add (S.neg x) w) h
  have hneg : S.add (S.neg x) x = S.zero := by
    rw [OrderedScalar.Axioms.add_comm]
    exact OrderedScalar.Axioms.add_neg x
  calc
    y = S.add S.zero y :=
      (OrderedScalar.Axioms.zero_add y).symm
    _ = S.add (S.add (S.neg x) x) y := by rw [hneg]
    _ = S.add (S.neg x) (S.add x y) :=
      OrderedScalar.Axioms.add_assoc _ _ _
    _ = S.add (S.neg x) (S.add x z) := h'
    _ = S.add (S.add (S.neg x) x) z :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by rw [hneg]
    _ = z := OrderedScalar.Axioms.zero_add z

private theorem scalar_mul_left_cancel
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

private theorem scalar_right_distrib
    (S : OrderedScalar) [S.Axioms]
    (x y z : S.Carrier) :
    S.mul (S.add x y) z =
      S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

private theorem scalar_add_nonzero_of_nonnegative_left
    (S : OrderedScalar) [S.Axioms]
    {x y : S.Carrier}
    (hx : x ≠ S.zero)
    (hx_nonnegative : S.le S.zero x)
    (hy_nonnegative : S.le S.zero y) :
    S.add x y ≠ S.zero := by
  intro hsum
  have hx_le_zero : S.le x S.zero := by
    have h :=
      OrderedScalar.Axioms.add_le_add_right
        S.zero y x hy_nonnegative
    rw [OrderedScalar.Axioms.zero_add,
      OrderedScalar.Axioms.add_comm] at h
    rwa [hsum] at h
  exact hx
    (OrderedScalar.Axioms.le_antisymm
      S.zero x hx_nonnegative hx_le_zero).symm

private theorem three_ne_zero
    (S : OrderedScalar) [S.Axioms] :
    S.add S.one (S.add S.one S.one) ≠ S.zero := by
  have hone : S.one ≠ S.zero :=
    OrderedScalar.Axioms.zero_ne_one.symm
  have hone_nonnegative :=
    OrderedScalar.Axioms.zero_le_one (S := S)
  have htwo_nonnegative : S.le S.zero (S.add S.one S.one) := by
    have h :=
      OrderedScalar.Axioms.add_le_add_right
        S.zero S.one S.one hone_nonnegative
    rw [OrderedScalar.Axioms.zero_add] at h
    exact OrderedScalar.Axioms.le_trans
      S.zero S.one _ hone_nonnegative h
  exact scalar_add_nonzero_of_nonnegative_left S
    hone hone_nonnegative htwo_nonnegative

private theorem not_oppositeSides_of_parallel_endpoints
    {a b c d : G.Point}
    (hparallel : Parallel G a b c d) :
    ¬G.OppositeSides c d a b := by
  intro hopposite
  obtain ⟨_, _, z, hz_cd, hazb⟩ := hopposite
  have hz_ab : G.Collinear a b z :=
    collinear_swap_last G (Or.inl hazb)
  exact hparallel.2.2 ⟨z, hz_ab, hz_cd⟩

private theorem twice_division_strict
    {b g k : G.Point}
    (hbk : b ≠ k)
    (hbgk : G.Bet b g k)
    (hratio : G.TwiceSegment g k b g) :
    b ≠ g ∧ g ≠ k := by
  obtain ⟨t, hbtg, hbt_gk, htg_gk⟩ := hratio
  have hbg : b ≠ g := by
    intro h
    subst g
    have hbt : b = t :=
      Plane.Axioms.betweennessIdentity b t hbtg
    subst t
    exact hbk
      (Plane.Axioms.congruenceIdentity
        b k b (congruent_symm G hbt_gk))
  have hgk : g ≠ k := by
    intro h
    subst k
    have htg : t = g :=
      Plane.Axioms.congruenceIdentity
        t g g htg_gk
    subst t
    have hbg' : b = g :=
      Plane.Axioms.congruenceIdentity
        b g g hbt_gk
    exact hbg hbg'
  exact ⟨hbg, hgk⟩

/--
Equal centroid divisions on two rays from `k` are joined by a line parallel
to the line through the two original vertices.
-/
private theorem two_thirds_connector_parallel
    (L : LengthMeasurement G) [L.Axioms]
    {k b d g h : G.Point}
    (hkbd : ¬G.Collinear k b d)
    (hbgk : G.Bet b g k)
    (hdhk : G.Bet d h k)
    (hbg_ratio : G.TwiceSegment g k b g)
    (hdh_ratio : G.TwiceSegment h k d h) :
    Parallel G g h b d := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hbk : b ≠ k := by
    intro h
    subst b
    exact hkbd (collinear_refl_left G k d)
  have hdk : d ≠ k := by
    intro h
    subst d
    exact hkbd
      (collinear_cyclic G
        (collinear_refl_left G k b))
  obtain ⟨hbg, hgk⟩ :=
    twice_division_strict G hbk hbgk hbg_ratio
  obtain ⟨hdh, hhk⟩ :=
    twice_division_strict G hdk hdhk hdh_ratio
  have hg_off_bd : ¬G.Collinear b d g := by
    intro hbdg
    have hbg_b : G.Collinear b g b :=
      collinear_cyclic G
        (collinear_refl_left G b g)
    have hbg_d : G.Collinear b g d :=
      collinear_swap_last G hbdg
    have hbg_k : G.Collinear b g k :=
      Or.inl hbgk
    exact hkbd
      (collinear_three_on_line G
        (p := k) (q := b) (r := d)
        hbg hbg_k hbg_b hbg_d)
  obtain ⟨q, hgq_parallel_bd⟩ :=
    parallel_through_offpoint_exists G hg_off_bd
  have hb_off_gq : ¬G.Collinear g q b := by
    intro h
    exact hgq_parallel_bd.2.2
      ⟨b, h, collinear_cyclic G
        (collinear_refl_left G b d)⟩
  have hd_off_gq : ¬G.Collinear g q d := by
    intro h
    exact hgq_parallel_bd.2.2
      ⟨d, h, collinear_refl_right G b d⟩
  have hk_off_gq : ¬G.Collinear g q k := by
    intro hgqk
    have hgk_b : G.Collinear g k b :=
      collinear_cyclic G (Or.inl hbgk)
    have hgk_g : G.Collinear g k g :=
      collinear_cyclic G
        (collinear_refl_left G g k)
    have hgq_b : G.Collinear g q b :=
      collinear_three_on_line G
        (p := g) (q := q) (r := b)
        hgk hgk_g
        (collinear_swap_last G hgqk) hgk_b
    exact hb_off_gq hgq_b
  have hk_opposite_b :
      G.OppositeSides g q k b :=
    ⟨hk_off_gq, hb_off_gq, g,
      collinear_cyclic G
        (collinear_refl_left G g q),
      bet_symm G hbgk⟩
  have hnot_bd :
      ¬G.OppositeSides g q b d :=
    not_oppositeSides_of_parallel_endpoints G
      (parallel_symm G hgq_parallel_bd)
  have hk_opposite_d :
      G.OppositeSides g q k d := by
    rcases Plane.Axioms.planeSeparation
        g q k b d hk_opposite_b hd_off_gq with
      hkd | hbd
    · exact hkd
    · exact False.elim (hnot_bd hbd)
  obtain ⟨_, _, z, hgqz, hkzd⟩ :=
    hk_opposite_d
  have hzk : z ≠ k := by
    intro h
    subst z
    exact hk_off_gq hgqz
  have hzg : z ≠ g := by
    intro hzg
    subst z
    have hgk_d : G.Collinear g k d :=
      collinear_swap G (Or.inl hkzd)
    have hgk_b : G.Collinear g k b :=
      collinear_cyclic G (Or.inl hbgk)
    exact hkbd
      (collinear_three_on_line G
        (p := k) (q := b) (r := d)
        hgk (collinear_refl_right G g k)
        hgk_b hgk_d)
  have hgz_parallel_bd :
      Parallel G g z b d :=
    parallel_rebase_left G hgq_parallel_bd
      (collinear_cyclic G
        (collinear_refl_left G g q))
      hgqz hzg.symm
  have hKG_B : G.SameRay k g b :=
    sameRay_of_order G hgk hbk
      (Or.inl (bet_symm G hbgk))
  have hKZ_D : G.SameRay k z d :=
    sameRay_of_order G hzk hdk
      (Or.inl hkzd)
  have hkgz : ¬G.Collinear k g z := by
    intro hcol
    have hkg_b : G.Collinear k g b :=
      hKG_B.2.2.1
    have hkg_d : G.Collinear k g d := by
      exact collinear_three_on_line G
        (a := k) (b := z)
        (p := k) (q := g) (r := d)
        hzk.symm
        (collinear_cyclic G
          (collinear_refl_left G k z))
        (collinear_swap_last G hcol)
        hKZ_D.2.2.1
    exact hkbd
      (collinear_three_on_line G
        (p := k) (q := b) (r := d)
        hgk
        (collinear_refl_right G g k)
        (collinear_swap G hkg_b)
        (collinear_swap G hkg_d))
  have hconfiguration :
      G.FourthProportionalConfiguration
        k g z b d :=
    ⟨hKG_B, hKZ_D, hkgz,
      (strictlyParallel_iff_no_intersection G).mpr
        hgz_parallel_bd⟩
  have hproduct :=
    LengthMeasurement.Axioms.fourth_proportional_mul
      (L := L) k g z b d hconfiguration
  obtain ⟨t, hbtg, hbt_gk, htg_gk⟩ :=
    hbg_ratio
  obtain ⟨u, hduh, hdu_hk, huh_hk⟩ :=
    hdh_ratio
  have hkb_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) k g b (bet_symm G hbgk)
  have hgb_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) g t b (bet_symm G hbtg)
  have hkd_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) k h d (bet_symm G hdhk)
  have hhd_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) h u d (bet_symm G hduh)
  have lbt_gk :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mp hbt_gk
  have ltg_gk :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mp htg_gk
  have ldu_hk :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mp hdu_hk
  have luh_hk :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mp huh_hk
  have hkb_three :
      L.length k b =
        L.scalar.add (L.length k g)
          (L.scalar.add (L.length k g)
            (L.length k g)) := by
    rw [hkb_add, hgb_add,
      LengthMeasurement.Axioms.length_symm g t,
      LengthMeasurement.Axioms.length_symm t b,
      lbt_gk, ltg_gk]
    rw [LengthMeasurement.Axioms.length_symm g k]
  have hkd_three :
      L.length k d =
        L.scalar.add (L.length k h)
          (L.scalar.add (L.length k h)
            (L.length k h)) := by
    rw [hkd_add, hhd_add,
      LengthMeasurement.Axioms.length_symm h u,
      LengthMeasurement.Axioms.length_symm u d,
      ldu_hk, luh_hk]
    rw [LengthMeasurement.Axioms.length_symm h k]
  rw [hkb_three, hkd_three] at hproduct
  rw [OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib] at hproduct
  have hthree :
      L.scalar.add L.scalar.one
        (L.scalar.add L.scalar.one L.scalar.one) ≠
        L.scalar.zero :=
    three_ne_zero L.scalar
  have hcompressed :
      L.scalar.mul
          (L.scalar.add L.scalar.one
            (L.scalar.add L.scalar.one L.scalar.one))
          (L.scalar.mul
            (L.length k g) (L.length k h)) =
        L.scalar.mul
          (L.scalar.add L.scalar.one
          (L.scalar.add L.scalar.one L.scalar.one))
          (L.scalar.mul
            (L.length k z) (L.length k g)) := by
    calc
      _ = L.scalar.add
          (L.scalar.mul (L.length k g) (L.length k h))
          (L.scalar.add
            (L.scalar.mul (L.length k g) (L.length k h))
            (L.scalar.mul (L.length k g) (L.length k h))) := by
            rw [scalar_right_distrib,
              scalar_right_distrib,
              OrderedScalar.Axioms.one_mul]
      _ = L.scalar.add
          (L.scalar.mul (L.length k z) (L.length k g))
          (L.scalar.add
            (L.scalar.mul (L.length k z) (L.length k g))
            (L.scalar.mul (L.length k z) (L.length k g))) :=
            hproduct
      _ = _ := by
            rw [scalar_right_distrib,
              scalar_right_distrib,
              OrderedScalar.Axioms.one_mul]
  have hsmall :=
    scalar_mul_left_cancel L.scalar hthree hcompressed
  rw [OrderedScalar.Axioms.mul_comm
    (L.length k z) (L.length k g)] at hsmall
  have lkg_ne :
      L.length k g ≠ L.scalar.zero := by
    intro hzero
    exact hgk
      ((LengthMeasurement.Axioms.length_eq_zero
        k g).mp hzero).symm
  have hl :
      L.length k h = L.length k z :=
    scalar_mul_left_cancel L.scalar lkg_ne hsmall
  have hKH_Z : G.SameRay k h z := by
    have hKH_D : G.SameRay k h d :=
      sameRay_of_order G hhk hdk
        (Or.inl (bet_symm G hdhk))
    exact sameRay_trans G hKH_D
      (sameRay_symm G hKZ_D)
  have hcongruent : G.Congruent k h k z :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mpr hl
  have hhz : h = z :=
    sameRay_congruent_unique G hKH_Z hcongruent
  subst z
  exact hgz_parallel_bd

/-- Sharygin, PDF page 74, problem 30. -/
theorem problem30
    (L : LengthMeasurement G) [L.Axioms]
    (config : Data G) :
    Conclusion G config := by
  have hac : config.a ≠ config.c := by
    intro h
    apply config.abc_nondegenerate
    rw [← h]
    exact collinear_cyclic G
      (collinear_refl_left G config.a config.b)
  have hbd : config.b ≠ config.d := by
    intro h
    apply config.kbd_nondegenerate
    rw [← h]
    exact collinear_refl_right G config.k config.b
  have hkom : G.Midpoint config.o config.k config.m :=
    complementary_points_midpoint G hac
      config.o_on_ac config.m_on_ac
      config.am_eq_oc config.k_midpoint_ac
  have hln : G.Midpoint config.o config.l config.n :=
    complementary_points_midpoint G hbd
      config.o_on_bd config.n_on_bd
      config.bn_eq_od config.l_midpoint_bd
  obtain ⟨pconfig⟩ :=
    centroid_exists G config.m config.n config.o
      config.mno_nondegenerate
  have hl_symm : G.Midpoint config.n config.l config.o :=
    pointReflection_as_midpoint G
      (pointReflection_symm G
        (midpoint_as_pointReflection G hln))
  have hl_eq :
      pconfig.midpointBC = config.l :=
    midpoint_unique G
      pconfig.midpointBC_isMidpoint hl_symm
  have hk_eq :
      pconfig.midpointCA = config.k :=
    midpoint_unique G
      pconfig.midpointCA_isMidpoint hkom
  have hmlp : G.Collinear config.m config.l pconfig.g := by
    rw [← hl_eq]
    exact collinear_swap_last G
      (Or.inl pconfig.a_g_midpointBC)
  have hnkp : G.Collinear config.n config.k pconfig.g := by
    rw [← hk_eq]
    exact collinear_swap_last G
      (Or.inl pconfig.b_g_midpointCA)
  have hk_symm : G.Midpoint config.c config.k config.a :=
    pointReflection_as_midpoint G
      (pointReflection_symm G
        (midpoint_as_pointReflection G
          config.k_midpoint_ac))
  have hkg_eq :
      config.centroid_abc.midpointCA = config.k :=
    midpoint_unique G
      config.centroid_abc.midpointCA_isMidpoint hk_symm
  have hkh_eq :
      config.centroid_adc.midpointCA = config.k :=
    midpoint_unique G
      config.centroid_adc.midpointCA_isMidpoint hk_symm
  have hbgk :
      G.Bet config.b config.centroid_abc.g config.k := by
    rw [← hkg_eq]
    exact config.centroid_abc.b_g_midpointCA
  have hdhk :
      G.Bet config.d config.centroid_adc.g config.k := by
    rw [← hkh_eq]
    exact config.centroid_adc.b_g_midpointCA
  have hn_pk :
      G.Bet config.n pconfig.g config.k := by
    rw [← hk_eq]
    exact pconfig.b_g_midpointCA
  have hratio_g :
      G.TwiceSegment
        config.centroid_abc.g config.k
        config.b config.centroid_abc.g := by
    rw [← hkg_eq]
    exact config.centroid_abc.ratioB
  have hratio_h :
      G.TwiceSegment
        config.centroid_adc.g config.k
        config.d config.centroid_adc.g := by
    rw [← hkh_eq]
    exact config.centroid_adc.ratioB
  have hratio_p :
      G.TwiceSegment
        pconfig.g config.k config.n pconfig.g := by
    rw [← hk_eq]
    exact pconfig.ratioB
  have hgh_parallel_bd :
      Parallel G
        config.centroid_abc.g
        config.centroid_adc.g
        config.b config.d :=
    two_thirds_connector_parallel G L
      config.kbd_nondegenerate hbgk hdhk
      hratio_g hratio_h
  have hgp_parallel_bn :
      Parallel G
        config.centroid_abc.g pconfig.g
        config.b config.n :=
    two_thirds_connector_parallel G L
      config.kbn_nondegenerate hbgk hn_pk
      hratio_g hratio_p
  have hgp_parallel_bd :
      Parallel G
        config.centroid_abc.g pconfig.g
        config.b config.d := by
    have hbd_parallel_gp :
        Parallel G config.b config.d
          config.centroid_abc.g pconfig.g :=
      parallel_rebase_left G
        (parallel_symm G hgp_parallel_bn)
        (collinear_cyclic G
          (collinear_refl_left G config.b config.n))
        (Or.inl config.n_on_bd) hbd
    exact parallel_symm G hbd_parallel_gp
  have hpgh :
      G.Collinear pconfig.g
        config.centroid_abc.g
        config.centroid_adc.g :=
    parallel_through_collinear G
      hgh_parallel_bd hgp_parallel_bd
  exact
    ⟨pconfig.g, hmlp, hnkp,
      collinear_cyclic G hpgh⟩

end Soultions.Sharygin.Page74.Problem30.Solution
