import Sharygin13Problem15.RightTriangle

/-!
# Problem-local one-dimensional midpoint square identity

This is the scalar calculation on the diagonal line needed by the parallelogram law.
-/

namespace Soultions.Sharygin.Page13.Problem15.MidpointSquares

open Euclid Plane
open Soultions.Sharygin.Page13.Problem15.Tarski
open Soultions.Sharygin.Page13.Problem15.Midpoint
open Soultions.Sharygin.Page13.Problem15.Scalar
open Soultions.Sharygin.Page13.Problem15.Similarity

variable (G : Plane) [G.Axioms]

theorem reflected_endpoint_square_sum
    (L : LengthMeasurement G) [L.Axioms]
    {a m c h : G.Point}
    (hac : PointReflection G m a c)
    (ham : a ≠ m)
    (hline : G.Collinear a m h) :
    L.scalar.add
        (L.scalar.square (L.length a h))
        (L.scalar.square (L.length c h)) =
      L.scalar.add
        (L.scalar.add
          (L.scalar.square (L.length a m))
          (L.scalar.square (L.length m h)))
        (L.scalar.add
          (L.scalar.square (L.length a m))
          (L.scalar.square (L.length m h))) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hcm_am :
      L.length c m = L.length a m := by
    calc
      L.length c m = L.length m c :=
        LengthMeasurement.Axioms.length_symm c m
      _ = L.length m a :=
        (LengthMeasurement.Axioms.congruent_iff
          m c m a).mp hac.radius
      _ = L.length a m :=
        LengthMeasurement.Axioms.length_symm m a
  have hmc_am :
      L.length m c = L.length a m := by
    rw [LengthMeasurement.Axioms.length_symm m c,
      hcm_am]
  have hhm_mh :
      L.length h m = L.length m h :=
    LengthMeasurement.Axioms.length_symm h m
  by_cases hhm : h = m
  · subst h
    have hmm_zero :
        L.length m m = L.scalar.zero :=
      (LengthMeasurement.Axioms.length_eq_zero m m).2 rfl
    rw [hmm_zero, hcm_am]
    change
      L.scalar.add
          (L.scalar.square (L.length a m))
          (L.scalar.square (L.length a m)) =
        L.scalar.add
          (L.scalar.add
            (L.scalar.square (L.length a m))
            (L.scalar.mul L.scalar.zero L.scalar.zero))
          (L.scalar.add
            (L.scalar.square (L.length a m))
            (L.scalar.mul L.scalar.zero L.scalar.zero))
    rw [OrderedScalar.Axioms.zero_mul,
      OrderedScalar.Axioms.add_zero]
  have hcm : c ≠ m :=
    pointReflection_other_ne G hac ham
  rcases hline with hamh | hmha | hham
  · have hmc_or_mh :
        G.Bet m c h ∨ G.Bet m h c := by
      have hmc_ray : G.SameRay m c h :=
        sameRay_of_common_opposite G
          ham hcm hhm
          hac.between hamh
      exact sameRay_order G hmc_ray
    have hah_add :
        L.length a h =
          L.scalar.add
            (L.length a m) (L.length m h) :=
      LengthMeasurement.Axioms.bet_additive a m h hamh
    rcases hmc_or_mh with hmch | hmhc
    · have hmh_add :
          L.length m h =
            L.scalar.add
              (L.length m c) (L.length c h) :=
        LengthMeasurement.Axioms.bet_additive m c h hmch
      have hch_sub :
          L.length c h =
            L.scalar.sub
              (L.length m h) (L.length a m) := by
        rw [← hmc_am]
        exact (sub_eq_of_eq_add L.scalar hmh_add).symm
      rw [hah_add, hch_sub]
      simpa only [OrderedScalar.Axioms.add_comm] using
        square_add_add_square_sub L.scalar
          (L.length m h) (L.length a m)
    · have hmc_add :
          L.length m c =
            L.scalar.add
              (L.length m h) (L.length h c) :=
        LengthMeasurement.Axioms.bet_additive m h c hmhc
      have hch_sub :
          L.length c h =
            L.scalar.sub
              (L.length a m) (L.length m h) := by
        rw [LengthMeasurement.Axioms.length_symm c h]
        symm
        apply sub_eq_of_eq_add L.scalar
        rw [← hmc_am]
        exact hmc_add
      rw [hah_add, hch_sub]
      exact square_add_add_square_sub L.scalar
        (L.length a m) (L.length m h)
  · have hhmc : G.Bet h m c :=
      bet_drop_left G (bet_symm G hmha) hac.between
    have ham_add :
        L.length a m =
          L.scalar.add
            (L.length a h) (L.length h m) :=
      LengthMeasurement.Axioms.bet_additive a h m
        (bet_symm G hmha)
    have hah_sub :
        L.length a h =
          L.scalar.sub
            (L.length a m) (L.length m h) := by
      rw [← hhm_mh]
      have ham_add' := ham_add
      rw [OrderedScalar.Axioms.add_comm] at ham_add'
      exact (sub_eq_of_eq_add L.scalar ham_add').symm
    have hhc_add :
        L.length h c =
          L.scalar.add
            (L.length h m) (L.length m c) :=
      LengthMeasurement.Axioms.bet_additive h m c hhmc
    rw [hah_sub, LengthMeasurement.Axioms.length_symm c h,
      hhc_add, hhm_mh, hmc_am,
      OrderedScalar.Axioms.add_comm
        (L.length m h) (L.length a m)]
    simpa only [OrderedScalar.Axioms.add_comm] using
      square_add_add_square_sub L.scalar
        (L.length a m) (L.length m h)
  · have hhmc : G.Bet h m c :=
      bet_chain G hham hac.between ham
    have hhm_add :
        L.length h m =
          L.scalar.add
            (L.length h a) (L.length a m) :=
      LengthMeasurement.Axioms.bet_additive h a m hham
    have hah_sub :
        L.length a h =
          L.scalar.sub
            (L.length m h) (L.length a m) := by
      rw [LengthMeasurement.Axioms.length_symm a h,
        ← hhm_mh]
      have hhm_add' := hhm_add
      rw [OrderedScalar.Axioms.add_comm] at hhm_add'
      exact (sub_eq_of_eq_add L.scalar hhm_add').symm
    have hhc_add :
        L.length h c =
          L.scalar.add
            (L.length h m) (L.length m c) :=
      LengthMeasurement.Axioms.bet_additive h m c hhmc
    rw [hah_sub, LengthMeasurement.Axioms.length_symm c h,
      hhc_add, hmc_am]
    rw [hhm_mh]
    simpa only [OrderedScalar.Axioms.add_comm] using
      square_add_add_square_sub L.scalar
        (L.length m h) (L.length a m)

end Soultions.Sharygin.Page13.Problem15.MidpointSquares
