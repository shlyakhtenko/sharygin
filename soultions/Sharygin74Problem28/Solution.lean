import Sharygin74Problem28.Ratio

/-!
# Sharygin, PDF page 74, problem 28

The proof is kept entirely in this problem folder.  It compares the two transversals by
the product form of Menelaus derived in `Ratio`.
-/

namespace Soultions.Sharygin.Page74.Problem28.Solution

open Euclid Plane
open Soultions.Sharygin.Page74.Problem28.Tarski
open Soultions.Sharygin.Page74.Problem28.Midpoint
open Soultions.Sharygin.Page74.Problem28.Affine
open Soultions.Sharygin.Page74.Problem28.Similarity
open Soultions.Sharygin.Page74.Problem28.Projection
open Soultions.Sharygin.Page74.Problem28.Grid
open Soultions.Sharygin.Page74.Problem28.Ratio

variable (G : Plane) [G.Axioms]

private theorem Configuration.base_triangle_nondegenerate
    (config : Configuration G) :
    ¬G.Collinear config.c config.b config.d := by
  intro hcbd
  have hbcd : G.Collinear config.b config.c config.d :=
    collinear_swap G hcbd
  exact config.bc_parallel_da.2.2
    ⟨config.d, hbcd,
      collinear_cyclic G
        (collinear_refl_left G config.d config.a)⟩

private theorem Configuration.strict_side_facts
    (config : Configuration G)
    (hae : config.a ≠ config.e)
    (hhd : config.h ≠ config.d) :
    config.e ≠ config.b ∧
    config.a ≠ config.h ∧
    config.b ≠ config.g ∧
    config.g ≠ config.c ∧
    config.d ≠ config.f ∧
    config.f ≠ config.c := by
  obtain ⟨hae_df, heb_fc, hbg_ah, hgc_hd⟩ :=
    config.side_piece_congruences G
  have heb : config.e ≠ config.b := by
    intro heb
    exact config.ef_parallel_bc.2.2
      ⟨config.b,
        by
          rw [← heb]
          exact collinear_cyclic G
            (collinear_refl_left G config.e config.f),
        collinear_cyclic G
          (collinear_refl_left G config.b config.c)⟩
  have hah : config.a ≠ config.h := by
    intro hah
    exact config.gh_parallel_ab.2.2
      ⟨config.a,
        by
          rw [hah]
          exact collinear_refl_right G config.g config.h,
        collinear_cyclic G
          (collinear_refl_left G config.a config.b)⟩
  have hbg : config.b ≠ config.g := by
    intro hbg
    exact config.gh_parallel_ab.2.2
      ⟨config.b,
        by
          rw [hbg]
          exact collinear_cyclic G
            (collinear_refl_left G config.g config.h),
        collinear_refl_right G config.a config.b⟩
  have hgc : config.g ≠ config.c := by
    intro hgc
    have hzero :
        G.Congruent config.c config.c config.h config.d := by
      rw [hgc] at hgc_hd
      exact hgc_hd
    exact hhd
      (Plane.Axioms.congruenceIdentity
        config.h config.d config.c
        (congruent_symm G hzero))
  have hdf : config.d ≠ config.f := by
    intro hdf
    have hzero :
        G.Congruent config.a config.e config.d config.d := by
      rw [← hdf] at hae_df
      exact hae_df
    exact hae
      (Plane.Axioms.congruenceIdentity
        config.a config.e config.d hzero)
  have hfc : config.f ≠ config.c := by
    intro hfc
    exact config.ef_parallel_bc.2.2
      ⟨config.c,
        by
          rw [← hfc]
          exact collinear_refl_right G config.e config.f,
        collinear_refl_right G config.b config.c⟩
  exact ⟨heb, hah, hbg, hgc, hdf, hfc⟩

private theorem interior_intersection_endpoint_ne
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
    p ≠ b ∧ p ≠ c := by
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
    have hae_c : G.Collinear a e c := by
      exact collinear_three_on_line G hah
        (collinear_cyclic G
          (collinear_refl_left G a h))
        (collinear_swap_last G hae_h)
        (Or.inl hahc)
    exact hnondegenerate
      (collinear_three_on_line G hae
        (collinear_cyclic G
          (collinear_refl_left G a e))
        (Or.inl haeb) hae_c)
  have hb_off_eh : ¬G.Collinear e h b := by
    intro hehb
    have heb_h : G.Collinear e b h :=
      collinear_swap_last G hehb
    have heb_a : G.Collinear e b a :=
      collinear_cyclic G (Or.inl haeb)
    exact ha_off_eh
      (collinear_three_on_line G heb
        (collinear_cyclic G
          (collinear_refl_left G e b))
        heb_h heb_a)
  have hc_off_eh : ¬G.Collinear e h c := by
    intro hehc
    have hhc_e : G.Collinear h c e :=
      collinear_cyclic G hehc
    have hhc_a : G.Collinear h c a :=
      collinear_cyclic G (Or.inl hahc)
    exact ha_off_eh
      (collinear_three_on_line G hhc
        hhc_e
        (collinear_cyclic G
          (collinear_refl_left G h c))
        hhc_a)
  constructor
  · intro hpb
    subst p
    exact hb_off_eh hehp
  · intro hpc
    subst p
    exact hc_off_eh hehp

/-- The non-endpoint case of the stated configuration. -/
private theorem strict_case
    (L : LengthMeasurement G) [L.Axioms]
    (config : Configuration G)
    (hae : config.a ≠ config.e)
    (hhd : config.h ≠ config.d) :
    Conclusion G config := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨heb, hah, hbg, hgc, hdf, hfc⟩ :=
    Configuration.strict_side_facts G config hae hhd
  have habd := config.nondegenerate
  have hcbd := Configuration.base_triangle_nondegenerate G config
  have hbd := config.b_ne_d G
  obtain ⟨hae_df, heb_fc, hbg_ah, hgc_hd⟩ :=
    config.side_piece_congruences G
  have lAE_DF :
      L.length config.a config.e =
        L.length config.d config.f :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mp hae_df
  have lEB_FC :
      L.length config.e config.b =
        L.length config.f config.c :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mp heb_fc
  have lBG_AH :
      L.length config.b config.g =
        L.length config.a config.h :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mp hbg_ah
  have lGC_HD :
      L.length config.g config.c =
        L.length config.h config.d :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mp hgc_hd
  have lCG_HD :
      L.length config.c config.g =
        L.length config.h config.d := by
    rw [LengthMeasurement.Axioms.length_symm
      config.c config.g]
    exact lGC_HD
  have lFD_AE :
      L.length config.f config.d =
        L.length config.a config.e := by
    rw [LengthMeasurement.Axioms.length_symm
      config.f config.d]
    exact lAE_DF.symm
  have lGB_AH :
      L.length config.g config.b =
        L.length config.a config.h := by
    rw [LengthMeasurement.Axioms.length_symm
      config.g config.b]
    exact lBG_AH
  have lCF_EB :
      L.length config.c config.f =
        L.length config.e config.b := by
    rw [LengthMeasurement.Axioms.length_symm
      config.c config.f]
    exact lEB_FC.symm
  have lAE_ne :
      L.length config.a config.e ≠ L.scalar.zero := by
    intro hzero
    exact hae
      ((LengthMeasurement.Axioms.length_eq_zero
        config.a config.e).mp hzero)
  have lHD_ne :
      L.length config.h config.d ≠ L.scalar.zero := by
    intro hzero
    exact hhd
      ((LengthMeasurement.Axioms.length_eq_zero
        config.h config.d).mp hzero)
  have hleft_ne :
      L.scalar.mul
          (L.length config.a config.e)
          (L.length config.h config.d) ≠
        L.scalar.zero :=
    scalar_mul_nonzero L.scalar lAE_ne lHD_ne
  rcases lines_meet_or_parallel G
      config.e_ne_h hbd with
    ⟨p, hehp, hbdp⟩ | heh_parallel_bd
  · have hp_ext :
        G.Bet p config.b config.d ∨
          G.Bet config.b config.d p :=
      interior_transversal_exterior G habd
        config.e_on_ab config.h_on_da
        hae heb hah hhd hehp hbdp
    obtain ⟨hpb, hpd⟩ :=
      interior_intersection_endpoint_ne G habd
        config.e_on_ab config.h_on_da
        hae heb hah hhd hehp hbdp
    have hp_menelaus :=
      menelaus_product G L habd
        config.e_on_ab config.h_on_da
        hae heb hah hhd hehp config.e_ne_h
        hpb hpd hp_ext
    have hp_product :
        L.scalar.mul
            (L.scalar.mul
              (L.length config.a config.e)
              (L.length config.h config.d))
            (L.length config.b p) =
          L.scalar.mul
            (L.scalar.mul
              (L.length config.e config.b)
              (L.length config.a config.h))
            (L.length config.d p) := by
      simpa only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        scalar_mul_left_comm L.scalar] using hp_menelaus
    rcases lines_meet_or_parallel G
        config.g_ne_f hbd with
      ⟨q, hgfq, hbdq⟩ | hgf_parallel_bd
    · have hq_ext :
          G.Bet q config.b config.d ∨
            G.Bet config.b config.d q :=
        interior_transversal_exterior G hcbd
          (bet_symm G config.g_on_bc)
          (bet_symm G config.f_on_cd)
          hgc.symm hbg.symm hfc.symm hdf.symm
          hgfq hbdq
      obtain ⟨hqb, hqd⟩ :=
        interior_intersection_endpoint_ne G hcbd
          (bet_symm G config.g_on_bc)
          (bet_symm G config.f_on_cd)
          hgc.symm hbg.symm hfc.symm hdf.symm
          hgfq hbdq
      have hq_menelaus :=
        menelaus_product G L hcbd
          (bet_symm G config.g_on_bc)
          (bet_symm G config.f_on_cd)
          hgc.symm hbg.symm hfc.symm hdf.symm
          hgfq config.g_ne_f hqb hqd hq_ext
      have hq_product :
          L.scalar.mul
              (L.scalar.mul
                (L.length config.a config.e)
                (L.length config.h config.d))
              (L.length config.b q) =
            L.scalar.mul
              (L.scalar.mul
                (L.length config.e config.b)
                (L.length config.a config.h))
              (L.length config.d q) := by
        rw [lCG_HD, lFD_AE, lGB_AH, lCF_EB] at hq_menelaus
        simpa only [OrderedScalar.Axioms.mul_assoc,
          OrderedScalar.Axioms.mul_comm,
          scalar_mul_left_comm L.scalar] using hq_menelaus
      have hscaled_p :=
        congrArg
          (fun x =>
            L.scalar.mul x (L.length config.d q))
          hp_product
      have hscaled_q :=
        congrArg
          (fun x =>
            L.scalar.mul x (L.length config.d p))
          hq_product
      have hcross_scaled :
          L.scalar.mul
              (L.scalar.mul
                (L.length config.a config.e)
                (L.length config.h config.d))
              (L.scalar.mul
                (L.length config.b p)
                (L.length config.d q)) =
            L.scalar.mul
              (L.scalar.mul
                (L.length config.a config.e)
                (L.length config.h config.d))
              (L.scalar.mul
                (L.length config.b q)
                (L.length config.d p)) := by
        calc
          _ = L.scalar.mul
              (L.scalar.mul
                (L.scalar.mul
                  (L.length config.e config.b)
                  (L.length config.a config.h))
                (L.length config.d p))
              (L.length config.d q) := by
                simpa only [OrderedScalar.Axioms.mul_assoc]
                  using hscaled_p
          _ = L.scalar.mul
              (L.scalar.mul
                (L.scalar.mul
                  (L.length config.e config.b)
                  (L.length config.a config.h))
                (L.length config.d q))
              (L.length config.d p) := by
                simp only [OrderedScalar.Axioms.mul_comm,
                  scalar_mul_left_comm L.scalar]
          _ = _ := by
                simpa only [OrderedScalar.Axioms.mul_assoc]
                  using hscaled_q.symm
      have hcross :
          L.scalar.mul
              (L.length config.b p)
              (L.length config.d q) =
            L.scalar.mul
              (L.length config.b q)
              (L.length config.d p) :=
        scalar_mul_left_cancel L.scalar hleft_ne
          hcross_scaled
      have hpq :
          p = q :=
        exterior_ratio_unique G L hbd
          hpb hpd hqb hqd hp_ext hq_ext hcross
      subst q
      exact Or.inl ⟨p, hehp, hgfq, hbdp⟩
    · have hparallel_product :=
        interior_parallel_product G L hcbd
          (bet_symm G config.g_on_bc)
          (bet_symm G config.f_on_cd)
          hgc.symm hbg.symm hfc.symm hdf.symm
          hgf_parallel_bd
      rw [lCG_HD, lFD_AE, lGB_AH, lCF_EB] at hparallel_product
      have hcoeff :
          L.scalar.mul
              (L.length config.a config.e)
              (L.length config.h config.d) =
            L.scalar.mul
              (L.length config.e config.b)
              (L.length config.a config.h) := by
        simpa only [OrderedScalar.Axioms.mul_comm]
          using hparallel_product
      rw [hcoeff] at hp_product
      have hequal :
          L.length config.b p =
            L.length config.d p :=
        scalar_mul_left_cancel L.scalar
          (by
            rw [← hcoeff]
            exact hleft_ne)
          hp_product
      exact False.elim
        ((exterior_endpoint_lengths_ne G L hbd hp_ext)
          hequal)
  · have hparallel_product :=
      interior_parallel_product G L habd
        config.e_on_ab config.h_on_da
        hae heb hah hhd heh_parallel_bd
    rcases lines_meet_or_parallel G
        config.g_ne_f hbd with
      ⟨q, hgfq, hbdq⟩ | hgf_parallel_bd
    · have hq_ext :
          G.Bet q config.b config.d ∨
            G.Bet config.b config.d q :=
        interior_transversal_exterior G hcbd
          (bet_symm G config.g_on_bc)
          (bet_symm G config.f_on_cd)
          hgc.symm hbg.symm hfc.symm hdf.symm
          hgfq hbdq
      obtain ⟨hqb, hqd⟩ :=
        interior_intersection_endpoint_ne G hcbd
          (bet_symm G config.g_on_bc)
          (bet_symm G config.f_on_cd)
          hgc.symm hbg.symm hfc.symm hdf.symm
          hgfq hbdq
      have hq_menelaus :=
        menelaus_product G L hcbd
          (bet_symm G config.g_on_bc)
          (bet_symm G config.f_on_cd)
          hgc.symm hbg.symm hfc.symm hdf.symm
          hgfq config.g_ne_f hqb hqd hq_ext
      rw [lCG_HD, lFD_AE, lGB_AH, lCF_EB] at hq_menelaus
      have hq_product :
          L.scalar.mul
              (L.scalar.mul
                (L.length config.a config.e)
                (L.length config.h config.d))
              (L.length config.b q) =
            L.scalar.mul
              (L.scalar.mul
                (L.length config.e config.b)
                (L.length config.a config.h))
              (L.length config.d q) := by
        simpa only [OrderedScalar.Axioms.mul_assoc,
          OrderedScalar.Axioms.mul_comm,
          scalar_mul_left_comm L.scalar] using hq_menelaus
      rw [hparallel_product] at hq_product
      have hq_product' :
          L.scalar.mul
              (L.scalar.mul
                (L.length config.a config.h)
                (L.length config.e config.b))
              (L.length config.b q) =
            L.scalar.mul
              (L.scalar.mul
                (L.length config.a config.h)
                (L.length config.e config.b))
              (L.length config.d q) := by
        simpa only [OrderedScalar.Axioms.mul_comm
          (L.length config.e config.b)
          (L.length config.a config.h)] using hq_product
      have hequal :
          L.length config.b q =
            L.length config.d q :=
        scalar_mul_left_cancel L.scalar
          (x := L.scalar.mul
            (L.length config.a config.h)
            (L.length config.e config.b))
          (by
            rw [← hparallel_product]
            exact hleft_ne)
          hq_product'
      exact False.elim
        ((exterior_endpoint_lengths_ne G L hbd hq_ext)
          hequal)
    · exact Or.inr ⟨heh_parallel_bd, hgf_parallel_bd⟩

/-- Sharygin, PDF page 74, problem 28. -/
theorem problem28
    (L : LengthMeasurement G) [L.Axioms]
    (config : Configuration G) :
    Conclusion G config := by
  by_cases hae : config.a = config.e
  · obtain ⟨hae_df, _, _, _⟩ :=
      config.side_piece_congruences G
    have hdf : config.d = config.f := by
      have hzero :
          G.Congruent config.a config.a
            config.d config.f := by
        rw [← hae] at hae_df
        exact hae_df
      exact
        (Plane.Axioms.congruenceIdentity
          config.d config.f config.a
          (congruent_symm G hzero))
    apply Or.inl
    refine ⟨config.d, ?_, ?_, ?_⟩
    · rw [← hae]
      exact Or.inl config.h_on_da
    · rw [← hdf]
      exact collinear_refl_right G config.g config.d
    · exact collinear_refl_right G config.b config.d
  · by_cases hhd : config.h = config.d
    · obtain ⟨_, _, _, hgc_hd⟩ :=
        config.side_piece_congruences G
      have hgc : config.g = config.c := by
        have hzero :
            G.Congruent config.g config.c
              config.d config.d := by
          rw [hhd] at hgc_hd
          exact hgc_hd
        exact
          Plane.Axioms.congruenceIdentity
            config.g config.c config.d hzero
      apply Or.inl
      refine ⟨config.d, ?_, ?_, ?_⟩
      · rw [hhd]
        exact collinear_refl_right G config.e config.d
      · rw [hgc]
        exact Or.inl (bet_symm G config.f_on_cd)
      · exact collinear_refl_right G config.b config.d
    · exact strict_case G L config hae hhd

end Soultions.Sharygin.Page74.Problem28.Solution
