import Euclid
import Sharygin12Problem9.Ratio

/-!
# Sharygin, PDF page 12, problem 9

> Let `AM` be an angle bisector in triangle `ABC`. Prove that
> `|BM| : |CM| = |AB| : |AC|`. The same is true for the exterior angle bisector, when `M`
> lies on an extension of `BC`.
-/

namespace Soultions.Sharygin.Page12.Problem9

open Euclid Plane
open Soultions.Sharygin.Page12.Problem9.Bisector
open Soultions.Sharygin.Page12.Problem9.Ratio

def InteriorStatement (G : Plane) (L : LengthMeasurement G) : Prop :=
  ∀ config : InteriorConfiguration G,
    L.scalar.mul
        (L.length config.b config.m)
        (L.length config.a config.c) =
      L.scalar.mul
        (L.length config.m config.c)
        (L.length config.a config.b)

def ExteriorStatement (G : Plane) (L : LengthMeasurement G) : Prop :=
  ∀ config : ExteriorConfiguration G,
    L.scalar.mul
        (L.length config.b config.m)
        (L.length config.a config.c) =
      L.scalar.mul
        (L.length config.c config.m)
        (L.length config.a config.b)

theorem problem9_internal (G : Plane) (L : LengthMeasurement G)
    [G.Axioms] [L.Axioms] :
    InteriorStatement G L := by
  exact interior_ratio G L

theorem problem9_external (G : Plane) (L : LengthMeasurement G)
    [G.Axioms] [L.Axioms] :
    ExteriorStatement G L := by
  exact exterior_ratio G L

end Soultions.Sharygin.Page12.Problem9
