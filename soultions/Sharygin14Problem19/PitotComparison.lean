import Sharygin14Problem19.InitialCircle

/-!
# The side comparisons forced by Pitot's equality

This file stays local to problem 19.  It turns a comparison on one pair of opposite sides
into the corresponding comparison on the other pair, including the equality case.
-/

namespace Soultions.Sharygin.Page14.Problem19.PitotComparison

open Euclid Plane
open Soultions.Sharygin.Page14.Problem19.Tarski
open Soultions.Sharygin.Page14.Problem19.Midpoint
open Soultions.Sharygin.Page14.Problem19.Scalar
open Soultions.Sharygin.Page14.Problem19.Configuration

variable (G : Plane) [G.Axioms]

private theorem nonnegative_sum_eq_zero
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

/-- If `CD ≤ AD`, Pitot's equality forces `BC ≤ AB`. -/
theorem bc_le_ab_of_cd_le_ad
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (hcd_ad : SegmentLE G q.c q.d q.d q.a) :
    SegmentLE G q.b q.c q.b q.a := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  rcases segmentLE_total G q.b q.c q.b q.a with hbc_ab | hab_bc
  · exact hbc_ab
  · obtain ⟨e, hdea, hde_cd⟩ := hcd_ad
    obtain ⟨f, hbfc, hbf_ba⟩ := hab_bc
    have hde_len : L.length q.d e = L.length q.c q.d :=
      (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hde_cd
    have hbf_len : L.length q.b f = L.length q.a q.b := by
      calc
        L.length q.b f = L.length q.b q.a :=
          (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hbf_ba
        _ = L.length q.a q.b := LengthMeasurement.Axioms.length_symm _ _
    have had :
        L.length q.a q.d =
          L.scalar.add (L.length q.c q.d) (L.length e q.a) := by
      calc
        L.length q.a q.d = L.length q.d q.a :=
          LengthMeasurement.Axioms.length_symm _ _
        _ = L.scalar.add (L.length q.d e) (L.length e q.a) :=
          LengthMeasurement.Axioms.bet_additive _ _ _ hdea
        _ = _ := by rw [hde_len]
    have hbc :
        L.length q.b q.c =
          L.scalar.add (L.length q.a q.b) (L.length f q.c) := by
      calc
        L.length q.b q.c =
            L.scalar.add (L.length q.b f) (L.length f q.c) :=
          LengthMeasurement.Axioms.bet_additive _ _ _ hbfc
        _ = _ := by rw [hbf_len]
    have hremainders :
        L.scalar.add (L.length e q.a) (L.length f q.c) = L.scalar.zero := by
      have hp := q.pitot
      rw [had, hbc] at hp
      apply add_left_cancel L.scalar
        (x := L.scalar.add (L.length q.a q.b) (L.length q.c q.d))
      calc
        L.scalar.add
            (L.scalar.add (L.length q.a q.b) (L.length q.c q.d))
            (L.scalar.add (L.length e q.a) (L.length f q.c)) =
          L.scalar.add
            (L.scalar.add (L.length q.c q.d) (L.length e q.a))
            (L.scalar.add (L.length q.a q.b) (L.length f q.c)) := by
              simp only [OrderedScalar.Axioms.add_assoc,
                OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
        _ = L.scalar.add (L.length q.a q.b) (L.length q.c q.d) := hp.symm
        _ = L.scalar.add
            (L.scalar.add (L.length q.a q.b) (L.length q.c q.d))
            L.scalar.zero := (OrderedScalar.Axioms.add_zero _).symm
    obtain ⟨hea_zero, hfc_zero⟩ :=
      nonnegative_sum_eq_zero L.scalar
        (LengthMeasurement.Axioms.length_nonnegative e q.a)
        (LengthMeasurement.Axioms.length_nonnegative f q.c)
        hremainders
    have heq : e = q.a :=
      (LengthMeasurement.Axioms.length_eq_zero e q.a).mp hea_zero
    have hfeq : f = q.c :=
      (LengthMeasurement.Axioms.length_eq_zero f q.c).mp hfc_zero
    subst e
    subst f
    exact ⟨q.a, bet_endpoint_refl G q.b q.a,
      congruent_symm G hbf_ba⟩

/-- If `AD ≤ CD`, Pitot's equality forces `AB ≤ BC`. -/
theorem ab_le_bc_of_ad_le_cd
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (had_cd : SegmentLE G q.a q.d q.c q.d) :
    SegmentLE G q.a q.b q.b q.c := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  rcases segmentLE_total G q.a q.b q.b q.c with hab_bc | hbc_ab
  · exact hab_bc
  · obtain ⟨e, hced, hce_ad⟩ := had_cd
    obtain ⟨f, hafb, haf_bc⟩ := hbc_ab
    have hce_len : L.length q.c e = L.length q.a q.d :=
      (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hce_ad
    have haf_len : L.length q.a f = L.length q.b q.c :=
      (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp haf_bc
    have hcd :
        L.length q.c q.d =
          L.scalar.add (L.length q.a q.d) (L.length e q.d) := by
      calc
        L.length q.c q.d =
            L.scalar.add (L.length q.c e) (L.length e q.d) :=
          LengthMeasurement.Axioms.bet_additive _ _ _ hced
        _ = _ := by rw [hce_len]
    have hab :
        L.length q.a q.b =
          L.scalar.add (L.length q.b q.c) (L.length f q.b) := by
      calc
        L.length q.a q.b =
            L.scalar.add (L.length q.a f) (L.length f q.b) :=
          LengthMeasurement.Axioms.bet_additive _ _ _ hafb
        _ = _ := by rw [haf_len]
    have hremainders :
        L.scalar.add (L.length f q.b) (L.length e q.d) = L.scalar.zero := by
      have hp := q.pitot
      rw [hab, hcd] at hp
      apply add_left_cancel L.scalar
        (x := L.scalar.add (L.length q.a q.d) (L.length q.b q.c))
      calc
        L.scalar.add
            (L.scalar.add (L.length q.a q.d) (L.length q.b q.c))
            (L.scalar.add (L.length f q.b) (L.length e q.d)) =
          L.scalar.add
            (L.scalar.add (L.length q.b q.c) (L.length f q.b))
            (L.scalar.add (L.length q.a q.d) (L.length e q.d)) := by
              simp only [OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
        _ = L.scalar.add (L.length q.a q.d) (L.length q.b q.c) := hp
        _ = L.scalar.add
            (L.scalar.add (L.length q.a q.d) (L.length q.b q.c))
            L.scalar.zero := (OrderedScalar.Axioms.add_zero _).symm
    obtain ⟨hfb_zero, hed_zero⟩ :=
      nonnegative_sum_eq_zero L.scalar
        (LengthMeasurement.Axioms.length_nonnegative f q.b)
        (LengthMeasurement.Axioms.length_nonnegative e q.d)
        hremainders
    have heq : e = q.d :=
      (LengthMeasurement.Axioms.length_eq_zero e q.d).mp hed_zero
    have hfeq : f = q.b :=
      (LengthMeasurement.Axioms.length_eq_zero f q.b).mp hfb_zero
    subst e
    subst f
    exact ⟨q.c, bet_endpoint_refl G q.b q.c,
      congruent_symm G haf_bc⟩

/-- The three isosceles triangles used in the `CD ≤ AD` branch. -/
structure LongADConstruction
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L) where
  e : G.Point
  f : G.Point
  e_between_DA : G.Bet q.d e q.a
  f_between_BA : G.Bet q.b f q.a
  de_eq_dc : G.Congruent q.d e q.d q.c
  bf_eq_bc : G.Congruent q.b f q.b q.c
  ae_eq_af : G.Congruent q.a e q.a f

/-- Construct the three equal-side pairs when `CD ≤ AD`. -/
theorem longADConstruction_exists
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (hcd_ad : SegmentLE G q.c q.d q.d q.a) :
    Nonempty (LongADConstruction G q) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hbc_ab := bc_le_ab_of_cd_le_ad G L q hcd_ad
  obtain ⟨e, hdea, hde_cd⟩ := hcd_ad
  obtain ⟨f, hbfa, hbf_bc⟩ := hbc_ab
  have hde_len : L.length q.d e = L.length q.c q.d :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hde_cd
  have hbf_len : L.length q.b f = L.length q.b q.c :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hbf_bc
  have hab :
      L.length q.a q.b =
        L.scalar.add (L.length q.b q.c) (L.length f q.a) := by
    calc
      L.length q.a q.b = L.length q.b q.a :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.scalar.add (L.length q.b f) (L.length f q.a) :=
        LengthMeasurement.Axioms.bet_additive _ _ _ hbfa
      _ = _ := by rw [hbf_len]
  have had :
      L.length q.a q.d =
        L.scalar.add (L.length q.c q.d) (L.length e q.a) := by
    calc
      L.length q.a q.d = L.length q.d q.a :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.scalar.add (L.length q.d e) (L.length e q.a) :=
        LengthMeasurement.Axioms.bet_additive _ _ _ hdea
      _ = _ := by rw [hde_len]
  have hfa_ea : L.length f q.a = L.length e q.a := by
    apply add_left_cancel L.scalar
      (x := L.scalar.add (L.length q.b q.c) (L.length q.c q.d))
    calc
      L.scalar.add
          (L.scalar.add (L.length q.b q.c) (L.length q.c q.d))
          (L.length f q.a) =
        L.scalar.add (L.length q.a q.b) (L.length q.c q.d) := by
          rw [hab]
          simp only [OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
      _ = L.scalar.add (L.length q.a q.d) (L.length q.b q.c) := q.pitot
      _ = L.scalar.add
          (L.scalar.add (L.length q.b q.c) (L.length q.c q.d))
          (L.length e q.a) := by
          rw [had]
          simp only [OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
  have hae_len : L.length q.a e = L.length q.a f := by
      rw [LengthMeasurement.Axioms.length_symm q.a e,
        LengthMeasurement.Axioms.length_symm q.a f]
      exact hfa_ea.symm
  have hae_af : G.Congruent q.a e q.a f :=
    (LengthMeasurement.Axioms.congruent_iff (L := L) _ _ _ _).mpr hae_len
  exact ⟨{
    e := e
    f := f
    e_between_DA := hdea
    f_between_BA := hbfa
    de_eq_dc := congruent_trans G hde_cd
      (Plane.Axioms.congruenceReversal q.c q.d)
    bf_eq_bc := hbf_bc
    ae_eq_af := hae_af
  }⟩

/-- The symmetric three-isosceles-triangle construction for `AD ≤ CD`. -/
structure LongCDConstruction
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L) where
  e : G.Point
  f : G.Point
  e_between_BC : G.Bet q.b e q.c
  f_between_DC : G.Bet q.d f q.c
  be_eq_ba : G.Congruent q.b e q.b q.a
  df_eq_da : G.Congruent q.d f q.d q.a
  ce_eq_cf : G.Congruent q.c e q.c f

/-- Construct the symmetric equal-side pairs when `AD ≤ CD`. -/
theorem longCDConstruction_exists
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (had_cd : SegmentLE G q.a q.d q.c q.d) :
    Nonempty (LongCDConstruction G q) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨e, hbec, hbe_ab⟩ := ab_le_bc_of_ad_le_cd G L q had_cd
  have had_cd_reversed : SegmentLE G q.a q.d q.d q.c :=
    (segmentLE_reverse_right_iff G).mpr had_cd
  obtain ⟨f, hdfc, hdf_ad⟩ := had_cd_reversed
  have hbe_len : L.length q.b e = L.length q.a q.b :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hbe_ab
  have hdf_len : L.length q.d f = L.length q.a q.d :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hdf_ad
  have hbc :
      L.length q.b q.c =
        L.scalar.add (L.length q.a q.b) (L.length e q.c) := by
    calc
      L.length q.b q.c =
          L.scalar.add (L.length q.b e) (L.length e q.c) :=
        LengthMeasurement.Axioms.bet_additive _ _ _ hbec
      _ = _ := by rw [hbe_len]
  have hcd :
      L.length q.c q.d =
        L.scalar.add (L.length q.a q.d) (L.length f q.c) := by
    calc
      L.length q.c q.d = L.length q.d q.c :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.scalar.add (L.length q.d f) (L.length f q.c) :=
        LengthMeasurement.Axioms.bet_additive _ _ _ hdfc
      _ = _ := by rw [hdf_len]
  have hfc_ec : L.length f q.c = L.length e q.c := by
    apply add_left_cancel L.scalar
      (x := L.scalar.add (L.length q.a q.b) (L.length q.a q.d))
    calc
      L.scalar.add
          (L.scalar.add (L.length q.a q.b) (L.length q.a q.d))
          (L.length f q.c) =
        L.scalar.add (L.length q.a q.b) (L.length q.c q.d) := by
          rw [hcd]
          simp only [OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
      _ = L.scalar.add (L.length q.a q.d) (L.length q.b q.c) := q.pitot
      _ = L.scalar.add
          (L.scalar.add (L.length q.a q.b) (L.length q.a q.d))
          (L.length e q.c) := by
          rw [hbc]
          simp only [OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
  have hce_len : L.length q.c e = L.length q.c f := by
      rw [LengthMeasurement.Axioms.length_symm q.c e,
        LengthMeasurement.Axioms.length_symm q.c f]
      exact hfc_ec.symm
  have hce_cf : G.Congruent q.c e q.c f :=
    (LengthMeasurement.Axioms.congruent_iff (L := L) _ _ _ _).mpr hce_len
  exact ⟨{
    e := e
    f := f
    e_between_BC := hbec
    f_between_DC := hdfc
    be_eq_ba := congruent_trans G hbe_ab
      (Plane.Axioms.congruenceReversal q.a q.b)
    df_eq_da := congruent_trans G hdf_ad
      (Plane.Axioms.congruenceReversal q.a q.d)
    ce_eq_cf := hce_cf
  }⟩

end Soultions.Sharygin.Page14.Problem19.PitotComparison
