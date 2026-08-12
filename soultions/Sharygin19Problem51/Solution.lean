import Sharygin19Problem51.Area

/-!
# Solution of Sharygin, PDF page 19, problem 51

The proof computes one equilateral center cell.  Its circle pieces are obtained from explicit
six- and eight-sector disk partitions; the lens is cut into two circular segments and two right
triangles.  All area identities below are derived from the global area axioms.
-/

namespace Soultions.Sharygin.Page19.Problem51.Solution

open Euclid Plane
open Soultions.Sharygin.Page19.Problem51.Scalar
open Soultions.Sharygin.Page19.Problem51.Similarity
open Soultions.Sharygin.Page19.Problem51.Pythagorean
open Soultions.Sharygin.Page19.Problem51.Partitions
open Soultions.Sharygin.Page19.Problem51.Configuration
open Soultions.Sharygin.Page19.Problem51.TriangleAltitudeArea
open Soultions.Sharygin.Page19.Problem51.Area

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.nsmul 2 x
def fourTimes (x : S.Carrier) := S.nsmul 4 x
def sixTimes (x : S.Carrier) := S.nsmul 6 x

private theorem nsmul_add (n : Nat) (x y : S.Carrier) :
    S.nsmul n (S.add x y) = S.add (S.nsmul n x) (S.nsmul n y) := by
  letI : Std.Associative S.add := ⟨OrderedScalar.Axioms.add_assoc⟩
  letI : Std.Commutative S.add := ⟨OrderedScalar.Axioms.add_comm⟩
  induction n with
  | zero => simp [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
  | succ n ih =>
      simp only [OrderedScalar.nsmul]
      rw [ih]
      ac_rfl

private theorem nsmul_nat_add (m n : Nat) (x : S.Carrier) :
    S.nsmul (m + n) x = S.add (S.nsmul m x) (S.nsmul n x) := by
  letI : Std.Associative S.add := ⟨OrderedScalar.Axioms.add_assoc⟩
  letI : Std.Commutative S.add := ⟨OrderedScalar.Axioms.add_comm⟩
  induction n with
  | zero => simp [OrderedScalar.nsmul, OrderedScalar.Axioms.add_zero]
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [OrderedScalar.nsmul, ih]
      ac_rfl

private theorem nsmul_nsmul (m n : Nat) (x : S.Carrier) :
    S.nsmul m (S.nsmul n x) = S.nsmul (m * n) x := by
  induction m with
  | zero => simp [OrderedScalar.nsmul]
  | succ m ih =>
      rw [Nat.succ_mul, nsmul_nat_add S]
      simp only [OrderedScalar.nsmul, ih, OrderedScalar.Axioms.zero_add]
      exact (nsmul_nat_add S _ _ _).symm

private theorem eq_sub_of_add_eq {x z y : S.Carrier}
    (h : S.add x z = y) : x = S.sub y z := by
  unfold OrderedScalar.sub
  apply add_right_cancel S (x := z)
  calc
    S.add x z = y := h
    _ = S.add y S.zero := (OrderedScalar.Axioms.add_zero y).symm
    _ = S.add y (S.add (S.neg z) z) := by rw [neg_add S]
    _ = S.add (S.add y (S.neg z)) z :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm

private theorem nsmul_mul (n : Nat) (x y : S.Carrier) :
    S.nsmul n (S.mul x y) = S.mul (S.nsmul n x) y := by
  induction n with
  | zero => simp [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_mul]
  | succ n ih =>
      simp only [OrderedScalar.nsmul, ih]
      exact (right_distrib S _ _ _).symm

private theorem mul_nsmul (n : Nat) (x y : S.Carrier) :
    S.nsmul n (S.mul x y) = S.mul x (S.nsmul n y) := by
  rw [OrderedScalar.Axioms.mul_comm x y, nsmul_mul S,
    OrderedScalar.Axioms.mul_comm]

private theorem nsmul_neg (n : Nat) (x : S.Carrier) :
    S.nsmul n (S.neg x) = S.neg (S.nsmul n x) := by
  induction n with
  | zero =>
      apply neg_unique S
      simp [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
  | succ n ih =>
      simp only [OrderedScalar.nsmul, ih]
      apply neg_unique S
      letI : Std.Associative S.add := ⟨OrderedScalar.Axioms.add_assoc⟩
      letI : Std.Commutative S.add := ⟨OrderedScalar.Axioms.add_comm⟩
      calc
        S.add (S.add (S.nsmul n x) x)
            (S.add (S.neg (S.nsmul n x)) (S.neg x)) =
          S.add
            (S.add (S.nsmul n x) (S.neg (S.nsmul n x)))
            (S.add x (S.neg x)) := by ac_rfl
        _ = S.zero := by
          rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.add_neg,
            OrderedScalar.Axioms.zero_add]

private theorem square_mul (x y : S.Carrier) :
    S.square (S.mul x y) = S.mul (S.square x) (S.square y) := by
  change S.mul (S.mul x y) (S.mul x y) = S.mul (S.mul x x) (S.mul y y)
  simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]

private theorem twice_nonnegative {x : S.Carrier}
    (hx : S.le S.zero x) : S.le S.zero (S.add x x) := by
  exact OrderedScalar.Axioms.le_trans S.zero x (S.add x x) hx
    (by simpa only [OrderedScalar.Axioms.zero_add] using
      OrderedScalar.Axioms.add_le_add_right S.zero x x hx)

private theorem height_times_two
    {a x h root : S.Carrier}
    (ha : a = S.add x x)
    (hpyth : S.add (S.square h) (S.square x) = S.square a)
    (hroot : S.square root = S.nsmul 3 S.one)
    (hh : S.le S.zero h) (hrootNonneg : S.le S.zero root)
    (haNonneg : S.le S.zero a) :
    S.add h h = S.mul root a := by
  have hhSquare : S.square h = S.nsmul 3 (S.square x) := by
    apply add_right_cancel S (x := S.square x)
    calc
      S.add (S.square h) (S.square x) = S.square a := hpyth
      _ = S.square (S.add x x) := by rw [ha]
      _ = S.nsmul 4 (S.square x) := by
        rw [square_double S]
        simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
        letI : Std.Associative S.add := ⟨OrderedScalar.Axioms.add_assoc⟩
        letI : Std.Commutative S.add := ⟨OrderedScalar.Axioms.add_comm⟩
        ac_rfl
      _ = S.add (S.nsmul 3 (S.square x)) (S.square x) := by rfl
  apply square_injective_nonnegative S (twice_nonnegative S hh)
    (OrderedScalar.Axioms.mul_nonneg root a hrootNonneg haNonneg)
  rw [square_double S, square_mul S, hroot, ha, square_double S, hhSquare]
  simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add,
    OrderedScalar.Axioms.left_distrib, right_distrib S,
    OrderedScalar.Axioms.one_mul, OrderedScalar.Axioms.add_comm, add_left_comm S]

private theorem equal_legs_from_radius
    {a x y r : S.Carrier}
    (ha : a = S.add x x)
    (hpyth : S.add (S.square x) (S.square y) = S.square r)
    (hradius : S.nsmul 2 (S.square r) = S.square a)
    (hx : S.le S.zero x) (hy : S.le S.zero y) : y = x := by
  have hr : S.square r = S.nsmul 2 (S.square x) := by
    apply add_self_injective S
    calc
      S.add (S.square r) (S.square r) = S.square a := by
        simpa only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add] using hradius
      _ = S.square (S.add x x) := by rw [ha]
      _ = S.add (S.nsmul 2 (S.square x)) (S.nsmul 2 (S.square x)) := by
        rw [square_double S]
        simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
  apply square_injective_nonnegative S hy hx
  apply add_left_cancel S (x := S.square x)
  calc
    S.add (S.square x) (S.square y) = S.square r := hpyth
    _ = S.nsmul 2 (S.square x) := hr
    _ = S.add (S.square x) (S.square x) := by
      simp [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]

private theorem scaled_disk_sector
    {sector radiusSq sideSq pi : S.Carrier} (pieces : Nat)
    (hdisk : S.nsmul pieces sector = S.mul pi radiusSq)
    (hradius : S.nsmul 2 radiusSq = sideSq) :
    S.nsmul (2 * pieces) sector = S.mul pi sideSq := by
  calc
    S.nsmul (2 * pieces) sector = S.nsmul 2 (S.nsmul pieces sector) := by
      exact (nsmul_nsmul S 2 pieces sector).symm
    _ = S.nsmul 2 (S.mul pi radiusSq) := congrArg (S.nsmul 2) hdisk
    _ = S.mul pi (S.nsmul 2 radiusSq) := mul_nsmul S 2 pi radiusSq
    _ = S.mul pi sideSq := by rw [hradius]

private theorem eight_triangle_area
    {triangle x y a : S.Carrier}
    (htriangle : S.add triangle triangle = S.mul x y)
    (hy : y = x) (ha : a = S.add x x) :
    S.nsmul 8 triangle = S.square a := by
  rw [hy] at htriangle
  calc
    S.nsmul 8 triangle = S.nsmul 4 (S.add triangle triangle) := by
      rw [← nsmul_nsmul S 4 2]
      congr 1
      simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
    _ = S.nsmul 4 (S.square x) := by rw [htriangle]; rfl
    _ = S.square (S.add x x) := by
      rw [square_double S]
      simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
      letI : Std.Associative S.add := ⟨OrderedScalar.Axioms.add_assoc⟩
      letI : Std.Commutative S.add := ⟨OrderedScalar.Axioms.add_comm⟩
      ac_rfl
    _ = S.square a := by rw [ha]

private theorem sixteen_injective {x y : S.Carrier}
    (h : S.nsmul 16 x = S.nsmul 16 y) : x = y := by
  have h8 : S.nsmul 8 x = S.nsmul 8 y := by
    apply add_self_injective S
    have h' := h
    rw [← nsmul_nsmul S 2 8 x, ← nsmul_nsmul S 2 8 y] at h'
    simpa only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add] using h'
  have h4 : S.nsmul 4 x = S.nsmul 4 y := by
    apply add_self_injective S
    have h' := h8
    rw [← nsmul_nsmul S 2 4 x, ← nsmul_nsmul S 2 4 y] at h'
    simpa only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add] using h'
  have h2 : S.nsmul 2 x = S.nsmul 2 y := by
    apply add_self_injective S
    have h' := h4
    rw [← nsmul_nsmul S 2 2 x, ← nsmul_nsmul S 2 2 y] at h'
    simpa only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add] using h'
  apply add_self_injective S
  simpa only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add] using h2

private theorem overlap_scaled
    {o t0 t1 q0 q1 sideSq pi : S.Carrier}
    (hlens : S.add o (S.add t0 t1) = S.add q0 q1)
    (ht0 : S.nsmul 8 t0 = sideSq)
    (ht1 : S.nsmul 8 t1 = sideSq)
    (hq0 : S.nsmul 16 q0 = S.mul pi sideSq)
    (hq1 : S.nsmul 16 q1 = S.mul pi sideSq) :
    S.nsmul 8 o = S.sub (S.mul pi sideSq) (S.nsmul 2 sideSq) := by
  have hq : q0 = q1 := sixteen_injective S (hq0.trans hq1.symm)
  apply eq_sub_of_add_eq S
  have hscaled := congrArg (S.nsmul 8) hlens
  rw [nsmul_add S, nsmul_add S, nsmul_add S, ht0, ht1, hq] at hscaled
  calc
    S.add (S.nsmul 8 o) (S.nsmul 2 sideSq) =
        S.add (S.nsmul 8 o) (S.add sideSq sideSq) := by
          simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
    _ = S.add (S.nsmul 8 q1) (S.nsmul 8 q1) := hscaled
    _ = S.nsmul 16 q1 := by
      rw [← nsmul_nsmul S 2 8]
      simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
    _ = S.mul pi sideSq := hq1

private theorem cell_area_scaled
    {area a h root : S.Carrier}
    (harea : S.add area area = S.mul a h)
    (hheight : S.add h h = S.mul root a) :
    S.nsmul 4 area = S.mul root (S.square a) := by
  calc
    S.nsmul 4 area = S.nsmul 2 (S.add area area) := by
      rw [nsmul_add S, ← nsmul_nsmul S 2 2]
      simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
    _ = S.nsmul 2 (S.mul a h) := by rw [harea]
    _ = S.mul a (S.nsmul 2 h) := mul_nsmul S 2 a h
    _ = S.mul a (S.mul root a) := by
      simpa only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add] using
        congrArg (S.mul a) hheight
    _ = S.mul root (S.square a) := by
      change S.mul a (S.mul root a) = S.mul root (S.mul a a)
      simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]

private theorem final_collection
    {u cellArea overlapArea left right sideSq root pi : S.Carrier}
    (hlocal : S.add u (S.add left right) = S.add cellArea overlapArea)
    (hcell : S.nsmul 4 cellArea = S.mul root sideSq)
    (hoverlap : S.nsmul 8 overlapArea =
      S.sub (S.mul pi sideSq) (S.nsmul 2 sideSq))
    (hleft : S.nsmul 12 left = S.mul pi sideSq)
    (hright : S.nsmul 12 right = S.mul pi sideSq) :
    S.nsmul 24 u =
      S.sub
        (S.mul (S.nsmul 6 root) sideSq)
        (S.mul (S.add (S.nsmul 6 S.one) pi) sideSq) := by
  apply eq_sub_of_add_eq S
  have hs := congrArg (S.nsmul 24) hlocal
  rw [nsmul_add S, nsmul_add S, nsmul_add S] at hs
  have hc24 : S.nsmul 24 cellArea = S.mul (S.nsmul 6 root) sideSq := by
    calc
      S.nsmul 24 cellArea = S.nsmul 6 (S.nsmul 4 cellArea) := by
        rw [nsmul_nsmul S]
      _ = S.nsmul 6 (S.mul root sideSq) := by rw [hcell]
      _ = S.mul (S.nsmul 6 root) sideSq := nsmul_mul S 6 root sideSq
  have ho24 : S.nsmul 24 overlapArea =
      S.nsmul 3 (S.sub (S.mul pi sideSq) (S.nsmul 2 sideSq)) := by
    calc
      S.nsmul 24 overlapArea = S.nsmul 3 (S.nsmul 8 overlapArea) := by
        rw [nsmul_nsmul S]
      _ = _ := by rw [hoverlap]
  have hl24 : S.nsmul 24 left = S.nsmul 2 (S.mul pi sideSq) := by
    calc
      S.nsmul 24 left = S.nsmul 2 (S.nsmul 12 left) := by
        rw [nsmul_nsmul S]
      _ = _ := by rw [hleft]
  have hr24 : S.nsmul 24 right = S.nsmul 2 (S.mul pi sideSq) := by
    calc
      S.nsmul 24 right = S.nsmul 2 (S.nsmul 12 right) := by
        rw [nsmul_nsmul S]
      _ = _ := by rw [hright]
  rw [hc24, ho24, hl24, hr24] at hs
  let P := S.mul pi sideSq
  let Q := sideSq
  let R := S.mul (S.nsmul 6 root) sideSq
  have hsCompact :
      S.add (S.nsmul 24 u) (S.nsmul 4 P) =
        S.add R (S.add (S.nsmul 3 P) (S.neg (S.nsmul 6 Q))) := by
    dsimp [P, Q, R]
    unfold OrderedScalar.sub at hs
    rw [nsmul_add S, nsmul_neg S, nsmul_nsmul S 3 2] at hs
    have hfour :
        S.add (S.nsmul 2 (S.mul pi sideSq))
            (S.nsmul 2 (S.mul pi sideSq)) =
          S.nsmul 4 (S.mul pi sideSq) := by
      rw [← nsmul_nsmul S 2 2]
      simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
    rwa [hfour] at hs
  have hcoefficient :
      S.mul (S.add (S.nsmul 6 S.one) pi) sideSq =
        S.add (S.nsmul 6 Q) P := by
    dsimp [P, Q]
    rw [right_distrib S, ← nsmul_mul S 6 S.one sideSq]
    simp only [OrderedScalar.Axioms.one_mul]
  rw [hcoefficient]
  apply add_right_cancel S
    (x := S.add (S.nsmul 3 P) (S.neg (S.nsmul 6 Q)))
  calc
    S.add
        (S.add (S.nsmul 24 u) (S.add (S.nsmul 6 Q) P))
        (S.add (S.nsmul 3 P) (S.neg (S.nsmul 6 Q))) =
      S.add (S.nsmul 24 u) (S.nsmul 4 P) := by
        letI : Std.Associative S.add := ⟨OrderedScalar.Axioms.add_assoc⟩
        letI : Std.Commutative S.add := ⟨OrderedScalar.Axioms.add_comm⟩
        calc
          S.add
              (S.add (S.nsmul 24 u) (S.add (S.nsmul 6 Q) P))
              (S.add (S.nsmul 3 P) (S.neg (S.nsmul 6 Q))) =
            S.add
              (S.add (S.nsmul 24 u) (S.nsmul 4 P))
              (S.add (S.nsmul 6 Q) (S.neg (S.nsmul 6 Q))) := by
                simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add]
                ac_rfl
          _ = S.add (S.nsmul 24 u) (S.nsmul 4 P) := by
            rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.add_zero]
    _ = S.add R (S.add (S.nsmul 3 P) (S.neg (S.nsmul 6 Q))) := hsCompact

/--
Sharygin, PDF page 19, problem 51.

If `U` is the part of the regular hexagon not covered by the six circles, then
`4U = (6√3 - 6 - π)a²`, stated without division.
-/
theorem problem51
    {G : Plane} [G.Axioms]
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L) [AreaMeasurement.Axioms A M]
    (d : Data M A) :
    fourTimes L.scalar
        (A.area (uncoveredRegion L d.center d.v0 d.v1 d.v2 d.v3 d.v4 d.v5
          d.radiusPoint0 d.radiusPoint1 d.radiusPoint2 d.radiusPoint3
          d.radiusPoint4 d.radiusPoint5)) =
      L.scalar.sub
        (L.scalar.mul (sixTimes L.scalar d.rootThree)
          (L.scalar.square (L.length d.v0 d.v1)))
        (L.scalar.mul
          (L.scalar.add (sixTimes L.scalar L.scalar.one) A.pi)
          (L.scalar.square (L.length d.v0 d.v1))) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  let a := L.length d.v0 d.v1
  let x := L.length d.v0 d.cellAltitude.foot
  let h := L.length d.cellAltitude.foot d.center
  let r0 := L.length d.v0 d.radiusPoint0
  let r1 := L.length d.v1 d.radiusPoint1
  let y := L.length d.midpoint d.intersectionPoint

  have ha : a = L.scalar.add x x := by
    dsimp [a, x]
    rw [LengthMeasurement.Axioms.bet_additive d.v0 d.cellAltitude.foot d.v1
      d.cellAltitude.between]
    exact congrArg (L.scalar.add (L.length d.v0 d.cellAltitude.foot))
      ((LengthMeasurement.Axioms.congruent_iff
        d.v0 d.cellAltitude.foot d.cellAltitude.foot d.v1).mp
          d.cell_foot_midpoint.2).symm
  have hpCell : L.scalar.add (L.scalar.square h) (L.scalar.square x) =
      L.scalar.square a := by
    have hp := pythagorean_of_internal_altitude G M L
      d.cellRightTriangle.noncollinear d.cellRightTriangle.foot_between
      d.cellRightTriangle.a_ne_foot d.cellRightTriangle.foot_ne_c
      d.cellRightTriangle.rightA d.cellRightTriangle.rightA_orientation
      d.cellRightTriangle.rightC d.cellRightTriangle.rightC_orientation
    dsimp [a, x, h]
    rw [LengthMeasurement.Axioms.length_symm d.center d.cellAltitude.foot,
      LengthMeasurement.Axioms.length_symm d.cellAltitude.foot d.v0,
      (LengthMeasurement.Axioms.congruent_iff d.center d.v0 d.v0 d.v1).mp
        d.center_v0_is_side] at hp
    exact hp
  have hheight : L.scalar.add h h = L.scalar.mul d.rootThree a :=
    height_times_two L.scalar ha hpCell d.root_three_square
      (LengthMeasurement.Axioms.length_nonnegative d.cellAltitude.foot d.center)
      d.rootThree_nonnegative
      (LengthMeasurement.Axioms.length_nonnegative d.v0 d.v1)

  have hCellArea := triangle_double_area_from_interior_altitude G M L A d.cellAltitude
  have hCellScaled : L.scalar.nsmul 4 (A.area (cell d.center d.v0 d.v1)) =
      L.scalar.mul d.rootThree (L.scalar.square a) := by
    change L.scalar.nsmul 4 (A.triangleArea d.center d.v0 d.v1) = _
    rw [AreaMeasurement.Axioms.cyclic M d.center d.v0 d.v1]
    dsimp [a]
    exact cell_area_scaled L.scalar hCellArea hheight

  have hLensPyth := pythagorean_of_internal_altitude G M L
    d.lensRightTriangle.noncollinear d.lensRightTriangle.foot_between
    d.lensRightTriangle.a_ne_foot d.lensRightTriangle.foot_ne_c
    d.lensRightTriangle.rightA d.lensRightTriangle.rightA_orientation
    d.lensRightTriangle.rightC d.lensRightTriangle.rightC_orientation
  have hmid : a = L.scalar.add (L.length d.v0 d.midpoint)
      (L.length d.v0 d.midpoint) := by
    dsimp [a]
    rw [LengthMeasurement.Axioms.bet_additive d.v0 d.midpoint d.v1
      d.midpoint_v0_v1.1]
    congr 1
    exact (LengthMeasurement.Axioms.congruent_iff
      d.v0 d.midpoint d.midpoint d.v1).mp d.midpoint_v0_v1.2 |>.symm
  have hLensPyth' :
      L.scalar.add (L.scalar.square (L.length d.v0 d.midpoint))
          (L.scalar.square y) = L.scalar.square r0 := by
    dsimp [y, r0]
    rw [(LengthMeasurement.Axioms.congruent_iff
      d.v0 d.intersectionPoint d.v0 d.radiusPoint0).mp
        d.intersection_on_circle0] at hLensPyth
    exact hLensPyth
  have hyx : y = L.length d.v0 d.midpoint :=
    equal_legs_from_radius L.scalar hmid hLensPyth' d.radius0_square
      (LengthMeasurement.Axioms.length_nonnegative d.v0 d.midpoint)
      (LengthMeasurement.Axioms.length_nonnegative d.midpoint d.intersectionPoint)

  obtain ⟨ht0, ht1⟩ := right_triangle_areas M A d
  have htri0 : L.scalar.nsmul 8
      (A.triangleArea d.v0 d.midpoint d.intersectionPoint) =
      L.scalar.square a :=
    eight_triangle_area L.scalar ht0 hyx hmid
  have hbaseRight : L.length d.v1 d.midpoint = L.length d.v0 d.midpoint := by
    rw [LengthMeasurement.Axioms.length_symm d.v1 d.midpoint]
    exact (LengthMeasurement.Axioms.congruent_iff
      d.v0 d.midpoint d.midpoint d.v1).mp d.midpoint_v0_v1.2 |>.symm
  have htri1 : L.scalar.nsmul 8
      (A.triangleArea d.v1 d.midpoint d.intersectionPoint) =
      L.scalar.square a := by
    rw [hbaseRight] at ht1
    exact eight_triangle_area L.scalar ht1 hyx hmid

  have hdisk0Six := six_partition_area M A d.disk0Six
  have hdisk1Six := six_partition_area M A d.disk1Six
  rw [d.disk0_sector, AreaMeasurement.Axioms.disk_area M] at hdisk0Six
  rw [d.disk1_sector, AreaMeasurement.Axioms.disk_area M] at hdisk1Six
  have hs0 : L.scalar.nsmul 12
      (A.area (leftSector L d.center d.v0 d.v1 d.radiusPoint0)) =
      L.scalar.mul A.pi (L.scalar.square a) :=
    scaled_disk_sector L.scalar 6 hdisk0Six.symm d.radius0_square
  have hs1 : L.scalar.nsmul 12
      (A.area (rightSector L d.center d.v0 d.v1 d.radiusPoint1)) =
      L.scalar.mul A.pi (L.scalar.square a) :=
    scaled_disk_sector L.scalar 6 hdisk1Six.symm d.radius1_square

  have hdisk0Eight := eight_partition_area M A d.disk0Eight
  have hdisk1Eight := eight_partition_area M A d.disk1Eight
  rw [d.disk0_sector45, AreaMeasurement.Axioms.disk_area M] at hdisk0Eight
  rw [d.disk1_sector45, AreaMeasurement.Axioms.disk_area M] at hdisk1Eight
  have hq0 : L.scalar.nsmul 16 (A.area d.sector45Left) =
      L.scalar.mul A.pi (L.scalar.square a) :=
    scaled_disk_sector L.scalar 8 hdisk0Eight.symm d.radius0_square
  have hq1 : L.scalar.nsmul 16 (A.area d.sector45Right) =
      L.scalar.mul A.pi (L.scalar.square a) :=
    scaled_disk_sector L.scalar 8 hdisk1Eight.symm d.radius1_square
  have hoverlap : L.scalar.nsmul 8
      (A.area (overlap L d.center d.v0 d.v1 d.radiusPoint0 d.radiusPoint1)) =
      L.scalar.sub (L.scalar.mul A.pi (L.scalar.square a))
        (L.scalar.nsmul 2 (L.scalar.square a)) :=
    overlap_scaled L.scalar (lens_decomposition M A d) htri0 htri1 hq0 hq1

  have hlocal := local_inclusion_exclusion M A
    d.center d.v0 d.v1 d.radiusPoint0 d.radiusPoint1
  have h24 := final_collection L.scalar hlocal hCellScaled hoverlap hs0 hs1
  have huncovered := six_partition_area M A d.uncoveredCells
  rw [d.representative_uncovered] at huncovered
  change L.scalar.nsmul 4
      (A.area (uncoveredRegion L d.center d.v0 d.v1 d.v2 d.v3 d.v4 d.v5
        d.radiusPoint0 d.radiusPoint1 d.radiusPoint2 d.radiusPoint3
        d.radiusPoint4 d.radiusPoint5)) = _
  rw [huncovered]
  rw [nsmul_nsmul L.scalar]
  change L.scalar.nsmul 24
      (A.area (localUncovered L d.center d.v0 d.v1 d.radiusPoint0 d.radiusPoint1)) = _
  exact h24

end Soultions.Sharygin.Page19.Problem51.Solution
