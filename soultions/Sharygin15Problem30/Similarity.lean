import Sharygin15Problem30.Affine

/-!
# Problem-local synthetic similarity for Sharygin, page 15, problem 30

This file develops angle congruence directly from rays and segment congruence.  Problem 7 has
no angle-measurement parameter, so its similarity argument must remain within the Tarski plane.
-/

namespace Soultions.Sharygin.Page15.Problem30.Similarity

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Tarski
open Soultions.Sharygin.Page15.Problem30.Midpoint
open Soultions.Sharygin.Page15.Problem30.Affine

variable (G : Plane) [G.Axioms]

theorem sameRay_refl {o a : G.Point} (h : a ≠ o) :
    G.SameRay o a a := by
  refine ⟨h, h, Or.inl (bet_endpoint_refl G o a), ?_⟩
  intro hbetween
  exact h (Plane.Axioms.betweennessIdentity a o hbetween)

theorem sameRay_symm {o a b : G.Point} (h : G.SameRay o a b) :
    G.SameRay o b a := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · rcases h.2.2.1 with hoab | habo | hboa
    · exact Or.inr (Or.inl (bet_symm G hoab))
    · exact Or.inl (bet_symm G habo)
    · exact Or.inr (Or.inr (bet_symm G hboa))
  · intro hboa
    exact h.2.2.2 (bet_symm G hboa)

theorem sameRay_from_far_endpoint {a b c : G.Point}
    (h : G.Bet a b c) (hbc : b ≠ c) :
    G.SameRay c b a := by
  have hac : a ≠ c := by
    intro hac
    subst a
    exact hbc (Plane.Axioms.betweennessIdentity c b h).symm
  refine ⟨hbc, hac, Or.inl (bet_symm G h), ?_⟩
  intro hbetween
  exact hbc (bet_antisymm G h (bet_symm G hbetween))

theorem sameRay_from_near_endpoint {a b c : G.Point}
    (h : G.Bet a b c) (hab : a ≠ b) (hbc : b ≠ c) :
    G.SameRay a b c := by
  have hac : a ≠ c := by
    intro hac
    subst c
    exact hab (Plane.Axioms.betweennessIdentity a b h)
  refine ⟨hab.symm, hac.symm, Or.inl h, ?_⟩
  intro hbac
  have hcycle : G.Bet c a c :=
    bet_outer_trans G (bet_symm G hbac) h hab
  exact hac (Plane.Axioms.betweennessIdentity c a hcycle).symm

theorem sameRay_order {o a b : G.Point} (h : G.SameRay o a b) :
    G.Bet o a b ∨ G.Bet o b a := by
  rcases h.2.2.1 with hoab | habo | hboa
  · exact Or.inl hoab
  · exact Or.inr (bet_symm G habo)
  · exact False.elim (h.2.2.2 (bet_symm G hboa))

theorem sameRay_of_order {o a b : G.Point}
    (hao : a ≠ o) (hbo : b ≠ o)
    (h : G.Bet o a b ∨ G.Bet o b a) :
    G.SameRay o a b := by
  by_cases hab : a = b
  · subst b
    exact sameRay_refl G hao
  rcases h with hoab | hoba
  · exact sameRay_from_near_endpoint G hoab hao.symm hab
  · exact sameRay_symm G
      (sameRay_from_near_endpoint G hoba hbo.symm (fun h => hab h.symm))

theorem sameRay_trans {o a b c : G.Point}
    (hab : G.SameRay o a b) (hbc : G.SameRay o b c) :
    G.SameRay o a c := by
  have hoa : a ≠ o := hab.1
  have hob : b ≠ o := hab.2.1
  have hoc : c ≠ o := hbc.2.1
  rcases sameRay_order G hab with hoab | hoba <;>
    rcases sameRay_order G hbc with hobc | hocb
  · by_cases hab_eq : a = b
    · subst b
      exact hbc
    have habc : G.Bet a b c :=
      bet_drop_left G hoab hobc
    have hoac : G.Bet o a c :=
      bet_outer_trans G hoab habc hab_eq
    exact sameRay_of_order G hoa hoc (Or.inl hoac)
  · exact sameRay_of_order G hoa hoc
      (bounded_connectivity G hoab hocb)
  · exact sameRay_of_order G hoa hoc
      (ray_connectivity G o b a c hob.symm hoba hobc)
  · by_cases hcb_eq : c = b
    · subst c
      exact hab
    have hcba : G.Bet c b a :=
      bet_drop_left G hocb hoba
    have hoca : G.Bet o c a :=
      bet_outer_trans G hocb hcba hcb_eq
    exact sameRay_of_order G hoa hoc (Or.inr hoca)

theorem sameRay_congruent_unique {o a b : G.Point}
    (hray : G.SameRay o a b)
    (hcongruent : G.Congruent o a o b) :
    a = b := by
  rcases sameRay_order G hray with hoab | hoba
  · exact bet_equal_initial_collapse G (fun h => hray.1 h.symm) hoab
      (congruent_symm G hcongruent)
  · exact
      (bet_equal_initial_collapse G
        (fun h => hray.2.1 h.symm) hoba hcongruent).symm

theorem sameRay_of_common_opposite
    {a o c x : G.Point}
    (hao : a ≠ o) (hco : c ≠ o) (hxo : x ≠ o)
    (haoc : G.Bet a o c) (haox : G.Bet a o x) :
    G.SameRay o c x := by
  rcases ray_connectivity G a o c x hao haoc haox with hacx | haxc
  · have hocx : G.Bet o c x :=
      bet_drop_left G haoc hacx
    exact sameRay_of_order G hco hxo (Or.inl hocx)
  · have hoxc : G.Bet o x c :=
      bet_drop_left G haox haxc
    exact sameRay_of_order G hco hxo (Or.inr hoxc)

/-- A point on the ray opposite `a` is also opposite every point on the ray from `o` through `a`. -/
theorem bet_opposite_of_sameRay
    {a o b x : G.Point}
    (haob : G.Bet a o b)
    (hax : G.SameRay o a x) :
    G.Bet x o b := by
  rcases sameRay_order G hax with hoax | hoxa
  · exact bet_chain G (bet_symm G hoax) haob hax.1
  · exact bet_drop_left G (bet_symm G hoxa) haob

/--
Two undirected angles are congruent when congruent nonzero samples can be chosen on their
corresponding rays and the segments joining those samples are congruent.

This is the standard ruler-and-compass meaning of angle congruence; no numerical measure is
introduced.
-/
def AngleCongruent (a o b c p d : G.Point) : Prop :=
  ∃ x y z w,
    G.SameRay o a x ∧
      G.SameRay o b y ∧
        G.SameRay p c z ∧
          G.SameRay p d w ∧
            G.Congruent o x p z ∧
              G.Congruent o y p w ∧
                G.Congruent x y z w

/--
The synthetic equality relation on undirected angles.

`AngleCongruent` is a single SSS certificate.  `SameAngle` is its reflexive, symmetric, and
transitive closure, so proofs may compose certificates obtained from different choices of
sample points without assuming numerical angle measurement.
-/
inductive SameAngle : G.Point → G.Point → G.Point →
    G.Point → G.Point → G.Point → Prop where
  | basic {a o b c p d} :
      AngleCongruent G a o b c p d →
      SameAngle a o b c p d
  | refl {a o b} :
      SameAngle a o b a o b
  | reverse {a o b} :
      SameAngle a o b b o a
  | symm {a o b c p d} :
      SameAngle a o b c p d →
      SameAngle c p d a o b
  | trans {a o b c p d e q f} :
      SameAngle a o b c p d →
      SameAngle c p d e q f →
      SameAngle a o b e q f

/-- Both rays of an angle have nonvertex sample points. -/
def AngleNondegenerate (a o b : G.Point) : Prop :=
  a ≠ o ∧ b ≠ o

omit [G.Axioms] in
theorem sameAngle_nondegenerate_iff
    {a o b c p d : G.Point}
    (h : SameAngle G a o b c p d) :
    AngleNondegenerate G a o b ↔
      AngleNondegenerate G c p d := by
  induction h with
  | basic hbasic =>
      obtain ⟨_, _, _, _, hax, hby, hcz, hdw, _⟩ := hbasic
      constructor
      · intro _
        exact ⟨hcz.1, hdw.1⟩
      · intro _
        exact ⟨hax.1, hby.1⟩
  | refl =>
      exact Iff.rfl
  | reverse =>
      constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩
  | symm _ ih =>
      exact ih.symm
  | trans _ _ ih₁ ih₂ =>
      exact Iff.trans ih₁ ih₂

omit [G.Axioms] in
theorem sameAngle_of_angleCongruent
    {a o b c p d : G.Point}
    (h : AngleCongruent G a o b c p d) :
    SameAngle G a o b c p d :=
  SameAngle.basic h

omit [G.Axioms] in
theorem sameAngle_symm
    {a o b c p d : G.Point}
    (h : SameAngle G a o b c p d) :
    SameAngle G c p d a o b :=
  SameAngle.symm h

omit [G.Axioms] in
theorem sameAngle_trans
    {a o b c p d e q f : G.Point}
    (h₁ : SameAngle G a o b c p d)
    (h₂ : SameAngle G c p d e q f) :
    SameAngle G a o b e q f :=
  SameAngle.trans h₁ h₂

theorem angleCongruent_of_sss
    {a o b c p d : G.Point}
    (hao : a ≠ o) (hbo : b ≠ o)
    (hcp : c ≠ p) (hdp : d ≠ p)
    (hoa : G.Congruent o a p c)
    (hob : G.Congruent o b p d)
    (hab : G.Congruent a b c d) :
    AngleCongruent G a o b c p d := by
  exact
    ⟨a, b, c, d,
      sameRay_refl G hao,
      sameRay_refl G hbo,
      sameRay_refl G hcp,
      sameRay_refl G hdp,
      hoa, hob, hab⟩

theorem straight_angles_congruent
    {a o b c p d : G.Point}
    (hao : a ≠ o) (hbo : b ≠ o)
    (hcp : c ≠ p) (hdp : d ≠ p)
    (haob : G.Bet a o b)
    (hcpd : G.Bet c p d) :
    AngleCongruent G a o b c p d := by
  obtain ⟨cOpp, hcReflection⟩ :=
    pointReflection_exists G p c
  obtain ⟨dOpp, hdReflection⟩ :=
    pointReflection_exists G p d
  obtain ⟨z, hcOpp_p_z, hpz_oa⟩ :=
    Plane.Axioms.segmentConstruction p o a cOpp
  obtain ⟨w, hdOpp_p_w, hpw_ob⟩ :=
    Plane.Axioms.segmentConstruction p o b dOpp
  have hcOpp_p : cOpp ≠ p :=
    pointReflection_other_ne G hcReflection hcp
  have hdOpp_p : dOpp ≠ p :=
    pointReflection_other_ne G hdReflection hdp
  have hzp : z ≠ p := by
    intro hzp
    subst z
    exact hao
      (Plane.Axioms.congruenceIdentity o a p
        (congruent_symm G hpz_oa)).symm
  have hwp : w ≠ p := by
    intro hwp
    subst w
    exact hbo
      (Plane.Axioms.congruenceIdentity o b p
        (congruent_symm G hpw_ob)).symm
  have hcz : G.SameRay p c z :=
    sameRay_of_common_opposite G
      hcOpp_p hcp hzp
      (bet_symm G hcReflection.between)
      hcOpp_p_z
  have hdw : G.SameRay p d w :=
    sameRay_of_common_opposite G
      hdOpp_p hdp hwp
      (bet_symm G hdReflection.between)
      hdOpp_p_w
  have hzpd : G.Bet z p d :=
    bet_opposite_of_sameRay G hcpd hcz
  have hzpw : G.Bet z p w := by
    rcases sameRay_order G hdw with hpdw | hpwd
    · exact bet_outer_trans G hzpd hpdw hdp.symm
    · exact bet_inner_trans G hzpd hpwd
  have hao_pz : G.Congruent a o z p :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal a o)
      (congruent_trans G (congruent_symm G hpz_oa)
        (Plane.Axioms.congruenceReversal p z))
  have hob_pw : G.Congruent o b p w :=
    congruent_symm G hpw_ob
  have hab_zw : G.Congruent a b z w :=
    segment_add G hao haob hzpw hao_pz hob_pw
  exact
    ⟨a, b, z, w,
      sameRay_refl G hao,
      sameRay_refl G hbo,
      hcz, hdw,
      congruent_symm G hpz_oa,
      hob_pw,
      hab_zw⟩

theorem angleCongruent_refl {a o b : G.Point}
    (hao : a ≠ o) (hbo : b ≠ o) :
    AngleCongruent G a o b a o b := by
  exact angleCongruent_of_sss G hao hbo hao hbo
    (congruent_refl G o a)
    (congruent_refl G o b)
    (congruent_refl G a b)

theorem angleCongruent_symm
    {a o b c p d : G.Point}
    (h : AngleCongruent G a o b c p d) :
    AngleCongruent G c p d a o b := by
  obtain ⟨x, y, z, w, hax, hby, hcz, hdw, hxz, hyw, hxyzw⟩ := h
  exact
    ⟨z, w, x, y,
      hcz, hdw, hax, hby,
      congruent_symm G hxz,
      congruent_symm G hyw,
      congruent_symm G hxyzw⟩

theorem angleCongruent_change_rays
    {a a' o b b' c c' p d d' : G.Point}
    (haa' : G.SameRay o a a')
    (hbb' : G.SameRay o b b')
    (hcc' : G.SameRay p c c')
    (hdd' : G.SameRay p d d')
    (h : AngleCongruent G a o b c p d) :
    AngleCongruent G a' o b' c' p d' := by
  obtain ⟨x, y, z, w, hax, hby, hcz, hdw, hxz, hyw, hxyzw⟩ := h
  exact
    ⟨x, y, z, w,
      sameRay_trans G (sameRay_symm G haa') hax,
      sameRay_trans G (sameRay_symm G hbb') hby,
      sameRay_trans G (sameRay_symm G hcc') hcz,
      sameRay_trans G (sameRay_symm G hdd') hdw,
      hxz, hyw, hxyzw⟩

theorem sameAngle_change_rays
    {a a' o b b' c c' p d d' : G.Point}
    (haa' : G.SameRay o a a')
    (hbb' : G.SameRay o b b')
    (hcc' : G.SameRay p c c')
    (hdd' : G.SameRay p d d')
    (h : SameAngle G a o b c p d) :
    SameAngle G a' o b' c' p d' := by
  have hleftRaw : AngleCongruent G a' o b' a o b := by
    exact
      ⟨a, b, a, b,
        sameRay_symm G haa',
        sameRay_symm G hbb',
        sameRay_refl G haa'.1,
        sameRay_refl G hbb'.1,
        congruent_refl G o a,
        congruent_refl G o b,
        congruent_refl G a b⟩
  have hrightRaw : AngleCongruent G c p d c' p d' := by
    exact
      ⟨c, d, c, d,
        sameRay_refl G hcc'.1,
        sameRay_refl G hdd'.1,
        sameRay_symm G hcc',
        sameRay_symm G hdd',
        congruent_refl G p c,
        congruent_refl G p d,
        congruent_refl G c d⟩
  exact SameAngle.trans (SameAngle.basic hleftRaw)
    (SameAngle.trans h (SameAngle.basic hrightRaw))

theorem angleCongruent_reverse_both
    {a o b c p d : G.Point}
    (h : AngleCongruent G a o b c p d) :
    AngleCongruent G b o a d p c := by
  obtain ⟨x, y, z, w, hax, hby, hcz, hdw, hxz, hyw, hxyzw⟩ := h
  have hyxwz : G.Congruent y x w z :=
    congruent_trans G
      (congruent_trans G
        (Plane.Axioms.congruenceReversal y x)
        hxyzw)
      (Plane.Axioms.congruenceReversal z w)
  exact
    ⟨y, x, w, z,
      hby, hax, hdw, hcz,
      hyw, hxz, hyxwz⟩

/--
Taking the opposite of the first ray preserves a single SSS angle-congruence certificate.

The reflected sample endpoints give the supplementary rays. Five-segment proves the new
joining segments congruent.
-/
theorem angleCongruent_supplements
    {a o b aOpp c p d cOpp : G.Point}
    (haOpp : aOpp ≠ o) (hcOpp : cOpp ≠ p)
    (haoaOpp : G.Bet a o aOpp)
    (hcpcOpp : G.Bet c p cOpp)
    (h : AngleCongruent G a o b c p d) :
    AngleCongruent G aOpp o b cOpp p d := by
  obtain ⟨x, y, z, w, hax, hby, hcz, hdw, hxz, hyw, hxyzw⟩ := h
  obtain ⟨x', hxx'⟩ := pointReflection_exists G o x
  obtain ⟨z', hzz'⟩ := pointReflection_exists G p z
  have hxo : x ≠ o := hax.2.1
  have hzp : z ≠ p := hcz.2.1
  have hx'o : x' ≠ o := pointReflection_other_ne G hxx' hxo
  have hz'p : z' ≠ p := pointReflection_other_ne G hzz' hzp
  have hxo_aOpp : G.Bet x o aOpp :=
    bet_opposite_of_sameRay G haoaOpp hax
  have hzp_cOpp : G.Bet z p cOpp :=
    bet_opposite_of_sameRay G hcpcOpp hcz
  have haOpp_x' : G.SameRay o aOpp x' :=
    sameRay_of_common_opposite G hxo haOpp hx'o
      hxo_aOpp hxx'.between
  have hcOpp_z' : G.SameRay p cOpp z' :=
    sameRay_of_common_opposite G hzp hcOpp hz'p
      hzp_cOpp hzz'.between
  have hxo_zp : G.Congruent x o z p :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal x o)
      (congruent_trans G hxz
        (Plane.Axioms.congruenceReversal p z))
  have hox'_pz' : G.Congruent o x' p z' :=
    congruent_trans G hxx'.radius
      (congruent_trans G hxz
        (congruent_symm G hzz'.radius))
  have hx'y_z'w : G.Congruent x' y z' w :=
    Plane.Axioms.fiveSegment x o x' y z p z' w
      hxo hxx'.between hzz'.between
      hxo_zp hox'_pz' hxyzw hyw
  exact
    ⟨x', y, z', w,
      haOpp_x', hby, hcOpp_z', hdw,
      hox'_pz', hyw, hx'y_z'w⟩

theorem sameAngle_reverse_both
    {a o b c p d : G.Point}
    (h : SameAngle G a o b c p d) :
    SameAngle G b o a d p c := by
  induction h with
  | basic hbasic =>
      exact SameAngle.basic (angleCongruent_reverse_both G hbasic)
  | refl =>
      exact SameAngle.refl
  | reverse =>
      exact SameAngle.reverse
  | symm _ ih =>
      exact SameAngle.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact SameAngle.trans ih₁ ih₂

theorem vertical_angles
    {a o b c d : G.Point}
    (hao : a ≠ o) (hbo : b ≠ o)
    (hco : c ≠ o) (hdo : d ≠ o)
    (haoc : G.Bet a o c) (hbod : G.Bet b o d) :
    SameAngle G a o b c o d := by
  obtain ⟨x, hax⟩ := pointReflection_exists G o a
  obtain ⟨y, hby⟩ := pointReflection_exists G o b
  have hxo : x ≠ o := pointReflection_other_ne G hax hao
  have hyo : y ≠ o := pointReflection_other_ne G hby hbo
  have hcx : G.SameRay o c x :=
    sameRay_of_common_opposite G hao hco hxo haoc hax.between
  have hdy : G.SameRay o d y :=
    sameRay_of_common_opposite G hbo hdo hyo hbod hby.between
  apply SameAngle.basic
  exact
    ⟨a, b, x, y,
      sameRay_refl G hao,
      sameRay_refl G hbo,
      hcx, hdy,
      congruent_symm G hax.radius,
      congruent_symm G hby.radius,
      pointReflection_cross_congruent G hax hby⟩

theorem sameAngle_supplements
    {a o b aOpp c p d cOpp : G.Point}
    (hleft : AngleNondegenerate G a o b)
    (hright : AngleNondegenerate G c p d)
    (haOpp : aOpp ≠ o) (hcOpp : cOpp ≠ p)
    (haoaOpp : G.Bet a o aOpp)
    (hcpcOpp : G.Bet c p cOpp)
    (h : SameAngle G a o b c p d) :
    SameAngle G aOpp o b cOpp p d := by
  induction h generalizing aOpp cOpp with
  | basic hbasic =>
      exact SameAngle.basic
        (angleCongruent_supplements G haOpp hcOpp
          haoaOpp hcpcOpp hbasic)
  | refl =>
      have hopposites :=
        sameRay_of_common_opposite G hleft.1 haOpp hcOpp
          haoaOpp hcpcOpp
      exact sameAngle_change_rays G
        (sameRay_refl G haOpp)
        (sameRay_refl G hleft.2)
        hopposites
        (sameRay_refl G hleft.2)
        (SameAngle.refl (G := G))
  | reverse =>
      have hvertical :=
        vertical_angles G
          haOpp hleft.2 hleft.1 hcOpp
          (bet_symm G haoaOpp) hcpcOpp
      exact SameAngle.trans hvertical SameAngle.reverse
  | symm h ih =>
      exact SameAngle.symm
        (ih hright hleft hcOpp haOpp hcpcOpp haoaOpp)
  | trans h₁ h₂ ih₁ ih₂ =>
      have hmiddle : AngleNondegenerate G _ _ _ :=
        (sameAngle_nondegenerate_iff G h₁).mp hleft
      obtain ⟨middleOpp, hmiddleReflection⟩ :=
        pointReflection_exists G _ _
      have hmiddleOpp : middleOpp ≠ _ :=
        pointReflection_other_ne G hmiddleReflection hmiddle.1
      exact SameAngle.trans
        (ih₁ hleft hmiddle haOpp hmiddleOpp
          haoaOpp hmiddleReflection.between)
        (ih₂ hmiddle hright hmiddleOpp hcOpp
          hmiddleReflection.between hcpcOpp)

theorem sameAngle_supplements_second
    {a o b bOpp c p d dOpp : G.Point}
    (hleft : AngleNondegenerate G a o b)
    (hright : AngleNondegenerate G c p d)
    (hbOpp : bOpp ≠ o) (hdOpp : dOpp ≠ p)
    (hbobOpp : G.Bet b o bOpp)
    (hdpdOpp : G.Bet d p dOpp)
    (h : SameAngle G a o b c p d) :
    SameAngle G a o bOpp c p dOpp := by
  have hreversed : SameAngle G b o a d p c :=
    sameAngle_reverse_both G h
  have hsupplements : SameAngle G bOpp o a dOpp p c :=
    sameAngle_supplements G
      ⟨hleft.2, hleft.1⟩
      ⟨hright.2, hright.1⟩
      hbOpp hdOpp hbobOpp hdpdOpp hreversed
  exact sameAngle_reverse_both G hsupplements

theorem secant_vertex_angles
    {m a b c d : G.Point}
    (hab : G.Bet m a b) (hcd : G.Bet m c d)
    (hma : m ≠ a) (hmc : m ≠ c)
    (hab_ne : a ≠ b) (hcd_ne : c ≠ d) :
    SameAngle G a m d c m b := by
  have hab_ray : G.SameRay m a b :=
    sameRay_from_near_endpoint G hab hma hab_ne
  have hcd_ray : G.SameRay m c d :=
    sameRay_from_near_endpoint G hcd hmc hcd_ne
  have hreverse : SameAngle G a m d d m a :=
    SameAngle.reverse
  exact sameAngle_change_rays G
    (sameRay_refl G hma.symm)
    (sameRay_refl G hcd_ray.2.1)
    (sameRay_symm G hcd_ray)
    hab_ray
    hreverse

/--
Equal inscribed angles subtending `bd` give the corresponding exterior angles in the two
ordered secant triangles. This is the exact supplement conversion used by problem 13.
-/
theorem exterior_secant_endpoint_angles_of_same_chord
    {m a b c d : G.Point}
    (hab : G.Bet m a b) (hcd : G.Bet m c d)
    (hma : m ≠ a) (hmc : m ≠ c)
    (hab_ne : a ≠ b) (hcd_ne : c ≠ d)
    (had : a ≠ d) (hcb : c ≠ b)
    (hsameChord : SameAngle G b a d b c d) :
    SameAngle G m a d m c b := by
  have hrightReversed : SameAngle G b a d d c b :=
    SameAngle.trans hsameChord SameAngle.reverse
  exact sameAngle_supplements G
    ⟨hab_ne.symm, had.symm⟩
    ⟨hcd_ne.symm, hcb.symm⟩
    hma hmc
    (bet_symm G hab) (bet_symm G hcd)
    hrightReversed

theorem isosceles_base_angles
    {a b c : G.Point}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h : G.Congruent a b a c) :
    AngleCongruent G a b c a c b := by
  have hba_ca : G.Congruent b a c a :=
    congruent_trans G
      (congruent_trans G
        (Plane.Axioms.congruenceReversal b a)
        h)
      (Plane.Axioms.congruenceReversal a c)
  exact
    angleCongruent_of_sss G
      hab hbc.symm hac hbc
      hba_ca
      (Plane.Axioms.congruenceReversal b c)
      (congruent_symm G h)

theorem circle_radii_congruent
    {circle : Circle G} {p q : G.Point}
    (hp : G.OnCircle circle p) (hq : G.OnCircle circle q) :
    G.Congruent circle.center p circle.center q := by
  exact congruent_trans G hp (congruent_symm G hq)

theorem center_ne_onCircle
    {circle : Circle G} {p : G.Point}
    (hp : G.OnCircle circle p) :
    circle.center ≠ p := by
  intro hop
  subst p
  have hradius_zero :
      G.Congruent circle.center circle.radiusPoint
        circle.center circle.center :=
    congruent_symm G hp
  exact circle.radius_ne
    (Plane.Axioms.congruenceIdentity
      circle.center circle.radiusPoint circle.center hradius_zero)

theorem circle_radius_triangle_base_angles
    {circle : Circle G} {p q : G.Point}
    (hp : G.OnCircle circle p) (hq : G.OnCircle circle q)
    (hpq : p ≠ q) :
    AngleCongruent G circle.center p q circle.center q p := by
  exact isosceles_base_angles G
    (center_ne_onCircle G hp)
    hpq
    (center_ne_onCircle G hq)
    (circle_radii_congruent G hp hq)

theorem circle_radius_triangle_base_sameAngle
    {circle : Circle G} {p q : G.Point}
    (hp : G.OnCircle circle p) (hq : G.OnCircle circle q)
    (hpq : p ≠ q) :
    SameAngle G circle.center p q circle.center q p := by
  exact SameAngle.basic
    (circle_radius_triangle_base_angles G hp hq hpq)

/--
A straight-line layout of the three angles of a nondegenerate triangle.

At vertex `a`, the ray to `c` separates two copied rays. The left copied angle is the angle
at `c`, the middle angle is the original angle at `a`, and the right copied angle is the angle
at `b`; `leftPoint-a-rightPoint` is straight.
-/
structure TriangleAngleLayout (a b c : G.Point) where
  leftPoint : G.Point
  rightPoint : G.Point
  leftCenter : G.Point
  rightCenter : G.Point
  straight : G.Bet leftPoint a rightPoint
  leftPoint_opposite_b :
    G.OppositeSides a c leftPoint b
  rightPoint_opposite_c :
    G.OppositeSides a b rightPoint c
  leftPoint_reflects_to_b :
    PointReflection G leftCenter leftPoint b
  a_reflects_to_c :
    PointReflection G leftCenter a c
  b_reflects_to_a :
    PointReflection G rightCenter b a
  rightPoint_reflects_to_c :
    PointReflection G rightCenter rightPoint c
  leftAngleRaw :
    AngleCongruent G leftPoint a c b c a
  rightAngleRaw :
    AngleCongruent G b a rightPoint a b c
  leftAngle : SameAngle G leftPoint a c b c a
  rightAngle : SameAngle G b a rightPoint a b c

theorem TriangleAngleLayout.left_plus_middle
    {a b c : G.Point}
    (layout : TriangleAngleLayout G a b c) :
    AngleCongruent G layout.leftPoint a b b c layout.leftPoint := by
  have hleft_a : layout.leftPoint ≠ a := by
    intro h
    apply layout.leftPoint_opposite_b.1
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G a c)
  have hba : b ≠ a := by
    intro h
    apply layout.leftPoint_opposite_b.2.1
    subst b
    exact collinear_cyclic G (collinear_refl_left G a c)
  have hbc : b ≠ c := by
    intro h
    apply layout.leftPoint_opposite_b.2.1
    subst b
    exact collinear_refl_right G a c
  have hleft_c : layout.leftPoint ≠ c := by
    intro h
    apply layout.leftPoint_opposite_b.1
    rw [h]
    exact collinear_refl_right G a c
  have haLeft_cb :
      G.Congruent a layout.leftPoint c b :=
    pointReflection_cross_congruent G
      layout.a_reflects_to_c
      layout.leftPoint_reflects_to_b
  have hab_cLeft :
      G.Congruent a b c layout.leftPoint :=
    pointReflection_cross_congruent G
      layout.a_reflects_to_c
      (pointReflection_symm G layout.leftPoint_reflects_to_b)
  exact angleCongruent_of_sss G
    hleft_a hba hbc hleft_c
    haLeft_cb hab_cLeft
    (Plane.Axioms.congruenceReversal layout.leftPoint b)

theorem TriangleAngleLayout.middle_plus_right
    {a b c : G.Point}
    (layout : TriangleAngleLayout G a b c) :
    AngleCongruent G c a layout.rightPoint
      layout.rightPoint b c := by
  have hca : c ≠ a := by
    intro h
    apply layout.rightPoint_opposite_c.2.1
    subst c
    exact collinear_cyclic G (collinear_refl_left G a b)
  have hright_a : layout.rightPoint ≠ a := by
    intro h
    apply layout.rightPoint_opposite_c.1
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G a b)
  have hright_b : layout.rightPoint ≠ b := by
    intro h
    apply layout.rightPoint_opposite_c.1
    rw [h]
    exact collinear_refl_right G a b
  have hcb : c ≠ b := by
    intro h
    apply layout.rightPoint_opposite_c.2.1
    subst c
    exact collinear_refl_right G a b
  have ha_to_b : PointReflection G layout.rightCenter a b :=
    pointReflection_symm G layout.b_reflects_to_a
  have hc_to_right :
      PointReflection G layout.rightCenter c layout.rightPoint :=
    pointReflection_symm G layout.rightPoint_reflects_to_c
  have hac_bRight :
      G.Congruent a c b layout.rightPoint :=
    pointReflection_cross_congruent G ha_to_b hc_to_right
  have haRight_bc :
      G.Congruent a layout.rightPoint b c :=
    pointReflection_cross_congruent G
      ha_to_b layout.rightPoint_reflects_to_c
  exact angleCongruent_of_sss G
    hca hright_a hright_b hcb
    hac_bRight haRight_bc
    (Plane.Axioms.congruenceReversal c layout.rightPoint)

theorem triangle_angle_layout
    {a b c : G.Point}
    (habc : ¬G.Collinear a b c) :
    Nonempty (TriangleAngleLayout G a b c) := by
  have hab : a ≠ b := by
    intro hab
    subst b
    exact habc (collinear_refl_left G a c)
  have hac : a ≠ c := by
    intro hac
    subst c
    exact habc
      (collinear_cyclic G (collinear_refl_left G a b))
  have hbc : b ≠ c := by
    intro hbc
    subst c
    exact habc (collinear_refl_right G a b)
  obtain ⟨copies, hstraight⟩ :=
    triangleCopies_aligned G habc
  have hyc_ba : G.Congruent copies.y c b a :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal copies.y c)
      (congruent_trans G copies.cy_ab
        (Plane.Axioms.congruenceReversal a b))
  have hleftRaw :
      AngleCongruent G copies.y a c b c a :=
    angleCongruent_of_sss G
      (by
        intro h
        apply copies.y_opposite_b.1
        rw [h]
        exact collinear_cyclic G (collinear_refl_left G a c))
      hac.symm hbc hac
      copies.ay_cb
      (Plane.Axioms.congruenceReversal a c)
      hyc_ba
  have hrightRaw :
      AngleCongruent G b a copies.x a b c :=
    angleCongruent_of_sss G
      hab.symm
      (by
        intro h
        apply copies.x_opposite_c.1
        rw [h]
        exact collinear_cyclic G (collinear_refl_left G a b))
      hab
      hbc.symm
      (Plane.Axioms.congruenceReversal a b)
      copies.ax_bc
      copies.bx_ac
  exact
    ⟨{
      leftPoint := copies.y
      rightPoint := copies.x
      leftCenter := copies.midpointAC
      rightCenter := copies.midpointAB
      straight := hstraight
      leftPoint_opposite_b := copies.y_opposite_b
      rightPoint_opposite_c := copies.x_opposite_c
      leftPoint_reflects_to_b :=
        pointReflection_symm G copies.b_reflects_to_y
      a_reflects_to_c :=
        midpoint_as_pointReflection G copies.midpointAC_isMidpoint
      b_reflects_to_a :=
        pointReflection_symm G
          (midpoint_as_pointReflection G
            copies.midpointAB_isMidpoint)
      rightPoint_reflects_to_c :=
        pointReflection_symm G copies.c_reflects_to_x
      leftAngleRaw := hleftRaw
      rightAngleRaw := hrightRaw
      leftAngle := SameAngle.basic hleftRaw
      rightAngle := SameAngle.basic hrightRaw
    }⟩

/--
Corresponding equal-radius samples on two pairs of rays have the same order from their
vertices.
-/
theorem congruent_ray_samples_order
    {o x x' p z z' : G.Point}
    (hxx' : G.SameRay o x x')
    (hzz' : G.SameRay p z z')
    (hxz : G.Congruent o x p z)
    (hx'z' : G.Congruent o x' p z') :
    (G.Bet o x x' ∧ G.Bet p z z') ∨
      (G.Bet o x' x ∧ G.Bet p z' z) := by
  rcases sameRay_order G hxx' with hoxx' | hox'x <;>
    rcases sameRay_order G hzz' with hpzz' | hpz'z
  · exact Or.inl ⟨hoxx', hpzz'⟩
  · have hpz_le_pz' : SegmentLE G p z p z' := by
      have hox_le_ox' : SegmentLE G o x o x' :=
        segmentLE_of_bet G hoxx'
      have hpz_le_ox' : SegmentLE G p z o x' :=
        segmentLE_congruent_left G hxz hox_le_ox'
      exact
        segmentLE_congruent_right G hx'z' hpz_le_ox'
    have hpz'_le_pz : SegmentLE G p z' p z :=
      segmentLE_of_bet G hpz'z
    have hpz_pz' : G.Congruent p z p z' :=
      segmentLE_antisymm G hpz_le_pz' hpz'_le_pz
    have hz'z : z' = z :=
      bet_equal_initial_collapse G
        (fun h => hzz'.2.1 h.symm)
        hpz'z hpz_pz'
    subst z'
    have hox_ox' : G.Congruent o x o x' :=
      congruent_trans G hxz
        (congruent_symm G hx'z')
    have hxx_eq : x = x' :=
      sameRay_congruent_unique G hxx' hox_ox'
    subst x'
    exact Or.inl
      ⟨bet_endpoint_refl G o x,
        bet_endpoint_refl G p z⟩
  · have hpz'_le_pz : SegmentLE G p z' p z := by
      have hox'_le_ox : SegmentLE G o x' o x :=
        segmentLE_of_bet G hox'x
      have hpz'_le_ox : SegmentLE G p z' o x :=
        segmentLE_congruent_left G hx'z' hox'_le_ox
      exact
        segmentLE_congruent_right G
          hxz hpz'_le_ox
    have hpz_le_pz' : SegmentLE G p z p z' :=
      segmentLE_of_bet G hpzz'
    have hpz'_pz : G.Congruent p z' p z :=
      segmentLE_antisymm G hpz'_le_pz hpz_le_pz'
    have hzz' : z = z' :=
      bet_equal_initial_collapse G
        (fun h => hzz'.1 h.symm)
        hpzz' hpz'_pz
    subst z'
    have hox_ox' : G.Congruent o x o x' :=
      congruent_trans G hxz
        (congruent_symm G hx'z')
    have hxx_eq : x = x' :=
      sameRay_congruent_unique G hxx' hox_ox'
    subst x'
    exact Or.inr
      ⟨bet_endpoint_refl G o x,
        bet_endpoint_refl G p z⟩
  · exact Or.inr ⟨hox'x, hpz'z⟩

/--
An SSS angle certificate remains valid when its first pair of ray samples is replaced by
corresponding equal-radius samples.
-/
theorem angle_certificate_move_first_sample
    {o x x' y p z z' w : G.Point}
    (hxx' : G.SameRay o x x')
    (hzz' : G.SameRay p z z')
    (hxz : G.Congruent o x p z)
    (hx'z' : G.Congruent o x' p z')
    (hyw : G.Congruent o y p w)
    (hxy_zw : G.Congruent x y z w) :
    G.Congruent x' y z' w := by
  rcases congruent_ray_samples_order G
      hxx' hzz' hxz hx'z' with
    houter | hinner
  · have hxx'_zz' : G.Congruent x x' z z' :=
      segment_cancel_left G
        (fun h => hxx'.1 h.symm)
        houter.1 houter.2 hxz hx'z'
    exact Plane.Axioms.fiveSegment
      o x x' y p z z' w
      (fun h => hxx'.1 h.symm)
      houter.1 houter.2
      hxz hxx'_zz' hyw hxy_zw
  · have hx'x_z'z : G.Congruent x' x z' z :=
      segment_cancel_left G
        (fun h => hxx'.2.1 h.symm)
        hinner.1 hinner.2 hx'z' hxz
    have hxx'_zz' : G.Congruent x x' z z' :=
      congruent_trans G
        (Plane.Axioms.congruenceReversal x x')
        (congruent_trans G hx'x_z'z
          (Plane.Axioms.congruenceReversal z' z))
    obtain ⟨t, hoxt, hxt_pz⟩ :=
      Plane.Axioms.segmentConstruction x p z o
    have htx : t ≠ x := by
      intro h
      subst t
      exact hzz'.1
        (Plane.Axioms.congruenceIdentity
          p z x (congruent_symm G hxt_pz)).symm
    obtain ⟨t', hpzt', hzt'_xt⟩ :=
      Plane.Axioms.segmentConstruction z x t p
    have hxt_zt' : G.Congruent x t z t' :=
      congruent_symm G hzt'_xt
    have ht_y_t'_w : G.Congruent t y t' w :=
      Plane.Axioms.fiveSegment
        o x t y p z t' w
        (fun h => hxx'.1 h.symm)
        hoxt hpzt'
        hxz hxt_zt' hyw hxy_zw
    have htxx' : G.Bet t x x' :=
      bet_symm G
        (bet_drop_left G hinner.1 hoxt)
    have ht'zz' : G.Bet t' z z' :=
      bet_symm G
        (bet_drop_left G hinner.2 hpzt')
    have htx_t'z : G.Congruent t x t' z :=
      congruent_trans G
        (Plane.Axioms.congruenceReversal t x)
        (congruent_trans G hxt_zt'
          (Plane.Axioms.congruenceReversal z t'))
    exact Plane.Axioms.fiveSegment
      t x x' y t' z z' w
      htx htxx' ht'zz'
      htx_t'z hxx'_zz'
      ht_y_t'_w hxy_zw

/-- Rescale both ray samples in one SSS angle certificate. -/
theorem angle_certificate_move_samples
    {o x x' y y' p z z' w w' : G.Point}
    (hxx' : G.SameRay o x x')
    (hyy' : G.SameRay o y y')
    (hzz' : G.SameRay p z z')
    (hww' : G.SameRay p w w')
    (hxz : G.Congruent o x p z)
    (hyw : G.Congruent o y p w)
    (hx'z' : G.Congruent o x' p z')
    (hy'w' : G.Congruent o y' p w')
    (hxy_zw : G.Congruent x y z w) :
    G.Congruent x' y' z' w' := by
  have hx'y_z'w : G.Congruent x' y z' w :=
    angle_certificate_move_first_sample G
      hxx' hzz' hxz hx'z' hyw hxy_zw
  have hyx'_wz' : G.Congruent y x' w z' :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal y x')
      (congruent_trans G hx'y_z'w
        (Plane.Axioms.congruenceReversal z' w))
  have hy'x'_w'z' : G.Congruent y' x' w' z' :=
    angle_certificate_move_first_sample G
      hyy' hww' hyw hy'w' hx'z' hyx'_wz'
  exact congruent_trans G
    (Plane.Axioms.congruenceReversal x' y')
    (congruent_trans G hy'x'_w'z'
      (Plane.Axioms.congruenceReversal w' z'))

/-- Raw SSS angle congruence is transitive. -/
theorem angleCongruent_trans
    {a o b c p d e q f : G.Point}
    (h₁ : AngleCongruent G a o b c p d)
    (h₂ : AngleCongruent G c p d e q f) :
    AngleCongruent G a o b e q f := by
  obtain
    ⟨x, y, z, w, hax, hby, hcz, hdw,
      hxz, hyw, hxy_zw⟩ := h₁
  obtain
    ⟨z₂, w₂, u, v, hcz₂, hdw₂, heu, hfv,
      hz₂u, hw₂v, hz₂w₂_uv⟩ := h₂
  obtain ⟨xOpposite, hxOpposite⟩ :=
    pointReflection_exists G o x
  obtain ⟨x₂, hxOpposite_o_x₂, hx₂_z₂⟩ :=
    Plane.Axioms.segmentConstruction o p z₂ xOpposite
  have hxOpposite_o : xOpposite ≠ o :=
    pointReflection_other_ne G hxOpposite hax.2.1
  have hx₂_o : x₂ ≠ o := by
    intro h
    subst x₂
    exact hcz₂.2.1
      (Plane.Axioms.congruenceIdentity
        p z₂ o (congruent_symm G hx₂_z₂)).symm
  have hxx₂ : G.SameRay o x x₂ :=
    sameRay_of_common_opposite G
      hxOpposite_o hax.2.1 hx₂_o
      (bet_symm G hxOpposite.between)
      hxOpposite_o_x₂
  obtain ⟨yOpposite, hyOpposite⟩ :=
    pointReflection_exists G o y
  obtain ⟨y₂, hyOpposite_o_y₂, hy₂_w₂⟩ :=
    Plane.Axioms.segmentConstruction o p w₂ yOpposite
  have hyOpposite_o : yOpposite ≠ o :=
    pointReflection_other_ne G hyOpposite hby.2.1
  have hy₂_o : y₂ ≠ o := by
    intro h
    subst y₂
    exact hdw₂.2.1
      (Plane.Axioms.congruenceIdentity
        p w₂ o (congruent_symm G hy₂_w₂)).symm
  have hyy₂ : G.SameRay o y y₂ :=
    sameRay_of_common_opposite G
      hyOpposite_o hby.2.1 hy₂_o
      (bet_symm G hyOpposite.between)
      hyOpposite_o_y₂
  have hzz₂ : G.SameRay p z z₂ :=
    sameRay_trans G
      (sameRay_symm G hcz) hcz₂
  have hww₂ : G.SameRay p w w₂ :=
    sameRay_trans G
      (sameRay_symm G hdw) hdw₂
  have hx₂y₂_z₂w₂ :
      G.Congruent x₂ y₂ z₂ w₂ :=
    angle_certificate_move_samples G
      hxx₂ hyy₂ hzz₂ hww₂
      hxz hyw hx₂_z₂ hy₂_w₂ hxy_zw
  exact
    ⟨x₂, y₂, u, v,
      sameRay_trans G hax hxx₂,
      sameRay_trans G hby hyy₂,
      heu, hfv,
      congruent_trans G hx₂_z₂ hz₂u,
      congruent_trans G hy₂_w₂ hw₂v,
      congruent_trans G hx₂y₂_z₂w₂
        hz₂w₂_uv⟩

/-- Reversing the two rays does not change an undirected angle. -/
theorem angleCongruent_swap_rays
    {a o b : G.Point}
    (hao : a ≠ o) (hbo : b ≠ o) :
    AngleCongruent G a o b b o a := by
  obtain ⟨bOpposite, hbOpposite⟩ :=
    pointReflection_exists G o b
  obtain ⟨y, hbOpposite_o_y, hoy_oa⟩ :=
    Plane.Axioms.segmentConstruction o o a bOpposite
  have hbOpposite_o : bOpposite ≠ o :=
    pointReflection_other_ne G hbOpposite hbo
  have hyo : y ≠ o := by
    intro h
    subst y
    exact hao
      (Plane.Axioms.congruenceIdentity
        o a o (congruent_symm G hoy_oa)).symm
  have hby : G.SameRay o b y :=
    sameRay_of_common_opposite G
      hbOpposite_o hbo hyo
      (bet_symm G hbOpposite.between)
      hbOpposite_o_y
  exact
    ⟨a, y, y, a,
      sameRay_refl G hao,
      hby, hby,
      sameRay_refl G hao,
      congruent_symm G hoy_oa,
      hoy_oa,
      Plane.Axioms.congruenceReversal a y⟩

/-- Every `SameAngle` proof yields one direct SSS certificate for nondegenerate rays. -/
theorem sameAngle_to_angleCongruent
    {a o b c p d : G.Point}
    (h : SameAngle G a o b c p d)
    (hleft : AngleNondegenerate G a o b) :
    AngleCongruent G a o b c p d := by
  induction h with
  | basic hbasic =>
      exact hbasic
  | refl =>
      exact angleCongruent_refl G hleft.1 hleft.2
  | reverse =>
      exact angleCongruent_swap_rays G
        hleft.1 hleft.2
  | @symm a o b c p d h ih =>
      have horiginal :
          AngleNondegenerate G a o b :=
        (sameAngle_nondegenerate_iff G h).mpr hleft
      exact angleCongruent_symm G
        (ih horiginal)
  | @trans a o b c p d e q f h₁ h₂ ih₁ ih₂ =>
      have hmiddle :
          AngleNondegenerate G c p d :=
        (sameAngle_nondegenerate_iff G h₁).mp hleft
      exact angleCongruent_trans G
        (ih₁ hleft) (ih₂ hmiddle)

/--
Two distinct points having equal distances from two fixed centers lie on opposite sides of the
line through those centers, provided neither point is on that line.

The midpoint of the two points is equidistant from them.  Upper dimension therefore puts that
midpoint on the line through the centers, where it witnesses the crossing.
-/
theorem equal_two_center_distances_eq_or_oppositeSides
    {o x y w : G.Point}
    (hy_off : ¬G.Collinear o x y)
    (hw_off : ¬G.Collinear o x w)
    (hoy_ow : G.Congruent o y o w)
    (hxy_xw : G.Congruent x y x w) :
    y = w ∨ G.OppositeSides o x y w := by
  by_cases hyw : y = w
  · exact Or.inl hyw
  obtain ⟨n, hn⟩ := midpoint_exists G y w
  have hny_nw : G.Congruent n y n w :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal n y) hn.2
  have honx : G.Collinear o x n :=
    Plane.Axioms.upperDimension o x n y w
      hyw hoy_ow hxy_xw hny_nw
  exact Or.inr ⟨hy_off, hw_off, n, honx, hn.1⟩

/--
Replacing an endpoint of an opposite-side pair by a point on the same ray from a point of the
separating line preserves the opposite-side relation.
-/
theorem oppositeSides_replace_sameRay
    {o linePoint a x e : G.Point}
    (hax : G.SameRay o a x)
    (hopposite : G.OppositeSides o linePoint a e) :
    G.OppositeSides o linePoint x e := by
  have holine : o ≠ linePoint :=
    oppositeSides_line_ne G hopposite
  have hox : o ≠ x := fun h => hax.2.1 h.symm
  have hxoff : ¬G.Collinear o linePoint x := by
    intro hline
    apply hopposite.1
    exact
      (collinear_on_same_line_iff G holine hox hline).mpr
        (collinear_swap_last G hax.2.2.1)
  have hnot_ax : ¬G.OppositeSides o linePoint a x := by
    intro hcontra
    obtain ⟨haoff, _, z, hzline, hazx⟩ := hcontra
    by_cases hax_eq : a = x
    · subst x
      have hza : z = a :=
        (Plane.Axioms.betweennessIdentity a z hazx).symm
      subst z
      exact haoff hzline
    by_cases hzo : z = o
    · subst z
      exact hax.2.2.2 hazx
    have ho_ax : G.Collinear a x o :=
      collinear_cyclic G hax.2.2.1
    have hz_ax : G.Collinear a x z :=
      collinear_swap_last G (Or.inl hazx)
    have ha_ax : G.Collinear a x a :=
      collinear_cyclic G (collinear_refl_left G a x)
    have hoza : G.Collinear o z a :=
      collinear_three_on_line G hax_eq ho_ax hz_ax ha_ax
    have holinea : G.Collinear o linePoint a :=
      (collinear_on_same_line_iff G holine
        (fun h => hzo h.symm) hzline).mpr hoza
    exact haoff holinea
  rcases Plane.Axioms.planeSeparation o linePoint a e x
      hopposite hxoff with haxOpposite | hexOpposite
  · exact False.elim (hnot_ax haxOpposite)
  · exact oppositeSides_symm G hexOpposite

/-- Two points of one ray cannot lie on opposite sides of a line through the ray vertex. -/
theorem not_oppositeSides_of_sameRay
    {o linePoint a x : G.Point}
    (hax : G.SameRay o a x)
    (ha_off : ¬G.Collinear o linePoint a) :
    ¬G.OppositeSides o linePoint a x := by
  intro hcontra
  obtain ⟨_, _, z, hzline, hazx⟩ := hcontra
  by_cases hax_eq : a = x
  · subst x
    have hza : z = a :=
      (Plane.Axioms.betweennessIdentity a z hazx).symm
    subst z
    exact ha_off hzline
  by_cases hzo : z = o
  · subst z
    exact hax.2.2.2 hazx
  have ho_ax : G.Collinear a x o :=
    collinear_cyclic G hax.2.2.1
  have hz_ax : G.Collinear a x z :=
    collinear_swap_last G (Or.inl hazx)
  have ha_ax : G.Collinear a x a :=
    collinear_cyclic G (collinear_refl_left G a x)
  have hoza : G.Collinear o z a :=
    collinear_three_on_line G hax_eq ho_ax hz_ax ha_ax
  have holine : o ≠ linePoint := by
    intro h
    subst linePoint
    exact ha_off (collinear_refl_left G o a)
  have holinea : G.Collinear o linePoint a :=
    (collinear_on_same_line_iff G holine
      (fun h => hzo h.symm) hzline).mpr hoza
  exact ha_off holinea

/--
Congruent nonstraight angles sharing their first ray have either the same second ray or second
rays on opposite sides of the common line.
-/
theorem angleCongruent_shared_first_ray_sameRay_or_oppositeSides
    {a o b c : G.Point}
    (hb_off : ¬G.Collinear o a b)
    (hc_off : ¬G.Collinear o a c)
    (hangle : AngleCongruent G a o b a o c) :
    G.SameRay o b c ∨ G.OppositeSides o a b c := by
  obtain
    ⟨x, y, z, w, hax, hby, haz, hcw,
      hxz, hyw, hxy_zw⟩ := hangle
  have hxz_ray : G.SameRay o x z :=
    sameRay_trans G (sameRay_symm G hax) haz
  have hxz_eq : x = z :=
    sameRay_congruent_unique G hxz_ray hxz
  subst z
  have hy_off : ¬G.Collinear o x y := by
    intro hoxy
    have hoa_y : G.Collinear o a y :=
      (collinear_on_same_line_iff G
        hax.1.symm hax.2.1.symm hax.2.2.1).mpr hoxy
    have hoy : o ≠ y := hby.2.1.symm
    have hoy_a : G.Collinear o y a :=
      collinear_swap_last G hoa_y
    have hoy_b : G.Collinear o y b :=
      collinear_swap_last G hby.2.2.1
    exact hb_off
      (collinear_three_on_line G hoy
        (Or.inr (Or.inr (bet_start_refl G o y)))
        hoy_a hoy_b)
  have hw_off : ¬G.Collinear o x w := by
    intro hoxw
    have hoa_w : G.Collinear o a w :=
      (collinear_on_same_line_iff G
        hax.1.symm hax.2.1.symm hax.2.2.1).mpr hoxw
    have how : o ≠ w := hcw.2.1.symm
    have how_a : G.Collinear o w a :=
      collinear_swap_last G hoa_w
    have how_c : G.Collinear o w c :=
      collinear_swap_last G hcw.2.2.1
    exact hc_off
      (collinear_three_on_line G how
        (Or.inr (Or.inr (bet_start_refl G o w)))
        how_a how_c)
  rcases equal_two_center_distances_eq_or_oppositeSides G
      hy_off hw_off hyw hxy_zw with hyw_eq | hopposite
  · subst w
    exact Or.inl
      (sameRay_trans G hby (sameRay_symm G hcw))
  · have hopposite_oa : G.OppositeSides o a y w :=
      (oppositeSides_on_same_line_iff G
        hax.2.1.symm hax.1.symm
        (collinear_swap_last G hax.2.2.1)).mp
        hopposite
    have hby_opposite : G.OppositeSides o a b w :=
      oppositeSides_replace_sameRay G
        (sameRay_symm G hby) hopposite_oa
    have hcw_opposite : G.OppositeSides o a c b :=
      oppositeSides_replace_sameRay G
        (sameRay_symm G hcw)
        (oppositeSides_symm G hby_opposite)
    exact Or.inr (oppositeSides_symm G hcw_opposite)

/-- On a fixed side of the common first ray, a congruent nonstraight angle determines one ray. -/
theorem angleCongruent_shared_first_ray_unique
    {a o b c : G.Point}
    (hb_off : ¬G.Collinear o a b)
    (hc_off : ¬G.Collinear o a c)
    (hnot_opposite : ¬G.OppositeSides o a b c)
    (hangle : AngleCongruent G a o b a o c) :
    G.SameRay o b c := by
  rcases angleCongruent_shared_first_ray_sameRay_or_oppositeSides G
      hb_off hc_off hangle with hray | hopposite
  · exact hray
  · exact False.elim (hnot_opposite hopposite)

/-- Swapping the two names of the separating line preserves opposite sides. -/
theorem oppositeSides_swap_line
    {a b p q : G.Point}
    (h : G.OppositeSides a b p q) :
    G.OppositeSides b a p q := by
  obtain ⟨hp, hq, x, hx, hpxq⟩ := h
  exact
    ⟨fun hline => hp (collinear_swap G hline),
      fun hline => hq (collinear_swap G hline),
      x, collinear_swap G hx, hpxq⟩

/--
ASA congruence for two noncollinear triangles, derived by constructing the second triangle's
third vertex at the first triangle's corresponding distance.
-/
theorem triangle_asa_congruent
    {o a b p c d : G.Point}
    (hleft : ¬G.Collinear o a b)
    (hright : ¬G.Collinear p c d)
    (hoa_pc : G.Congruent o a p c)
    (hvertex : SameAngle G a o b c p d)
    (hbase : SameAngle G o a b p c d) :
    G.Congruent o b p d ∧ G.Congruent a b c d := by
  have hao : a ≠ o := by
    intro h
    subst a
    exact hleft (collinear_refl_left G o b)
  have hbo : b ≠ o := by
    intro h
    subst b
    exact hleft (Or.inr (Or.inr (bet_start_refl G o a)))
  have hab : a ≠ b := by
    intro h
    subst b
    exact hleft (collinear_refl_right G o a)
  have hcp : c ≠ p := by
    intro h
    subst c
    exact hright (collinear_refl_left G p d)
  have hdp : d ≠ p := by
    intro h
    subst d
    exact hright (Or.inr (Or.inr (bet_start_refl G p c)))
  have hcd : c ≠ d := by
    intro h
    subst d
    exact hright (collinear_refl_right G p c)
  obtain ⟨dOpposite, hdOpposite⟩ :=
    pointReflection_exists G p d
  obtain ⟨d', hdOpposite_p_d', hpd'_ob⟩ :=
    Plane.Axioms.segmentConstruction p o b dOpposite
  have hdOpposite_p : dOpposite ≠ p :=
    pointReflection_other_ne G hdOpposite hdp
  have hd'p : d' ≠ p := by
    intro h
    subst d'
    exact hbo
      (Plane.Axioms.congruenceIdentity
        o b p (congruent_symm G hpd'_ob)).symm
  have hdd' : G.SameRay p d d' :=
    sameRay_of_common_opposite G
      hdOpposite_p hdp hd'p
      (bet_symm G hdOpposite.between)
      hdOpposite_p_d'
  have hvertexRaw :
      AngleCongruent G a o b c p d :=
    sameAngle_to_angleCongruent G hvertex ⟨hao, hbo⟩
  obtain
    ⟨x, y, z, w, hax, hby, hcz, hdw,
      hxz, hyw, hxy_zw⟩ := hvertexRaw
  have hx_a : G.SameRay o x a :=
    sameRay_symm G hax
  have hy_b : G.SameRay o y b :=
    sameRay_symm G hby
  have hz_c : G.SameRay p z c :=
    sameRay_symm G hcz
  have hw_d' : G.SameRay p w d' :=
    sameRay_trans G (sameRay_symm G hdw) hdd'
  have hob_pd' : G.Congruent o b p d' :=
    congruent_symm G hpd'_ob
  have hab_cd' : G.Congruent a b c d' :=
    angle_certificate_move_samples G
      hx_a hy_b hz_c hw_d'
      hxz hyw hoa_pc hob_pd' hxy_zw
  have hao_cp : G.Congruent a o c p :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal a o)
      (congruent_trans G hoa_pc
        (Plane.Axioms.congruenceReversal p c))
  have hbaseConstructed :
      AngleCongruent G o a b p c d' :=
    angleCongruent_of_sss G
      hao.symm
      (by
        intro h
        subst b
        exact hleft (collinear_refl_right G o a))
      hcp.symm
      (by
        intro h
        subst d'
        exact hab
          (Plane.Axioms.congruenceIdentity
            a b c hab_cd'))
      hao_cp hab_cd' hob_pd'
  have hbaseRaw :
      AngleCongruent G o a b p c d :=
    sameAngle_to_angleCongruent G hbase
      ⟨hao.symm,
        by
          intro h
          subst b
          exact hleft (collinear_refl_right G o a)⟩
  have hcompare :
      AngleCongruent G p c d' p c d :=
    angleCongruent_trans G
      (angleCongruent_symm G hbaseConstructed)
      hbaseRaw
  have hd_off_cp : ¬G.Collinear c p d := by
    intro h
    exact hright (collinear_swap G h)
  have hd'_off_cp : ¬G.Collinear c p d' := by
    intro hcpd'
    have hpd'c : G.Collinear p d' c :=
      collinear_cyclic G hcpd'
    have hpd'd : G.Collinear p d' d :=
      collinear_swap_last G hdd'.2.2.1
    have hpd'p : G.Collinear p d' p :=
      Or.inr (Or.inr (bet_start_refl G p d'))
    exact hright
      (collinear_three_on_line G hd'p.symm
        hpd'p hpd'c hpd'd)
  have hnotOpposite : ¬G.OppositeSides c p d' d := by
    intro hopposite
    have hopposite_pc : G.OppositeSides p c d d' :=
      oppositeSides_swap_line G
        (oppositeSides_symm G hopposite)
    exact
      (not_oppositeSides_of_sameRay G hdd' hright)
        hopposite_pc
  have hcd'd : G.SameRay c d' d :=
    angleCongruent_shared_first_ray_unique G
      hd'_off_cp hd_off_cp hnotOpposite hcompare
  have hd'd : d' = d := by
    apply Classical.byContradiction
    intro hd'd
    have hdd'p : G.Collinear d d' p :=
      collinear_cyclic G hdd'.2.2.1
    have hdd'c : G.Collinear d d' c :=
      collinear_swap G
        (collinear_cyclic G hcd'd.2.2.1)
    have hdd'd : G.Collinear d d' d :=
      Or.inr (Or.inr (bet_start_refl G d d'))
    exact hright
      (collinear_three_on_line G (fun h => hd'd h.symm)
        hdd'p hdd'c hdd'd)
  subst d'
  exact ⟨hob_pd', hab_cd'⟩

/--
Reflecting the vertex of two points on one ray across their midpoint puts the reflected vertex
beyond either point of the pair.
-/
theorem midpoint_reflection_beyond_sameRay
    {p e c n p' : G.Point}
    (hec : G.SameRay p e c)
    (hn : G.Midpoint e n c)
    (hpp' : PointReflection G n p p') :
    G.Bet p c p' := by
  by_cases hec_ne : e = c
  · subst c
    have hen : e = n :=
      Plane.Axioms.betweennessIdentity e n hn.1
    subst n
    exact hpp'.between
  have hecReflection : PointReflection G n e c :=
    midpoint_as_pointReflection G hn
  have hceReflection : PointReflection G n c e :=
    pointReflection_symm G hecReflection
  rcases sameRay_order G hec with hpec | hpce
  · have hp'ce : G.Bet p' c e :=
      pointReflection_preserves_bet G
        hpp' hecReflection hceReflection hpec
    exact bet_chain G hpec (bet_symm G hp'ce) hec_ne
  · have hp'ec : G.Bet p' e c :=
      pointReflection_preserves_bet G
        hpp' hceReflection hecReflection hpce
    exact bet_outer_trans G hpce (bet_symm G hp'ec)
      (fun h => hec_ne h.symm)

/--
Two points lying opposite the same off-line point cannot themselves lie on opposite sides.
-/
theorem not_oppositeSides_of_common_opposite
    {a b p q r : G.Point}
    (hpr : G.OppositeSides a b p r)
    (hqr : G.OppositeSides a b q r) :
    ¬G.OppositeSides a b p q := by
  have hpq_orientation :
      G.Orientation a b p = G.Orientation a b q := by
    rw [Plane.Axioms.orientation_opposite_sides (G := G) hpr,
      Plane.Axioms.orientation_opposite_sides (G := G) hqr]
  intro hpq
  have hopposite :
      G.Orientation a b p =
        (G.Orientation a b q).map RotationSense.reverse :=
    Plane.Axioms.orientation_opposite_sides (G := G) hpq
  rw [hpq_orientation] at hopposite
  cases hqOrientation : G.Orientation a b q with
  | none =>
      exact hpq.2.1
        ((Plane.Axioms.orientation_collinear a b q).mp
          hqOrientation)
  | some sense =>
      cases sense <;>
        simp [hqOrientation, RotationSense.reverse] at hopposite

/-- The relation of not being separated by a line is transitive among off-line points. -/
theorem not_oppositeSides_trans
    {a b p q r : G.Point}
    (hq_off : ¬G.Collinear a b q)
    (hpq : ¬G.OppositeSides a b p q)
    (hqr : ¬G.OppositeSides a b q r) :
    ¬G.OppositeSides a b p r := by
  intro hpr
  rcases Plane.Axioms.planeSeparation a b p r q
      hpr hq_off with hpq' | hrq'
  · exact hpq hpq'
  · exact hqr (oppositeSides_symm G hrq')

/--
Two off-line points not separated by a line have the same orientation relative to that line.
-/
theorem orientation_eq_of_not_oppositeSides
    {a b p q : G.Point}
    (hp_off : ¬G.Collinear a b p)
    (hq_off : ¬G.Collinear a b q)
    (hnot : ¬G.OppositeSides a b p q) :
    G.Orientation a b p = G.Orientation a b q := by
  obtain ⟨r, hpr⟩ := pointReflection_exists G a p
  have ha_line : G.Collinear a b a :=
    collinear_cyclic G (collinear_refl_left G a b)
  have hp_r : G.OppositeSides a b p r :=
    pointReflection_oppositeSides G ha_line hp_off hpr
  rcases Plane.Axioms.planeSeparation a b p r q
      hp_r hq_off with hp_q | hr_q
  · exact False.elim (hnot hp_q)
  · rw [Plane.Axioms.orientation_opposite_sides (G := G) hp_r,
      Plane.Axioms.orientation_opposite_sides (G := G)
        (oppositeSides_symm G hr_q)]

/-- Moving an off-line point along a ray from a point of the line preserves orientation. -/
theorem orientation_eq_of_sameRay_from_line_point
    {a b p q : G.Point}
    (hpq : G.SameRay a p q)
    (hp_off : ¬G.Collinear a b p) :
    G.Orientation a b p = G.Orientation a b q := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact hp_off (collinear_refl_left G a p)
  have haq : a ≠ q := hpq.2.1.symm
  have hq_off : ¬G.Collinear a b q := by
    intro habq
    have haqp : G.Collinear a q p :=
      collinear_swap_last G hpq.2.2.1
    exact hp_off
      (collinear_three_on_line G haq
        (Or.inr (Or.inr (bet_start_refl G a q)))
        (collinear_swap_last G habq) haqp)
  exact orientation_eq_of_not_oppositeSides G
    hp_off hq_off
    (not_oppositeSides_of_sameRay G hpq hp_off)

/-- Moving either endpoint along its ray preserves the orientation of a nonstraight angle. -/
theorem orientation_sameRay_invariant
    {a a' o b b' : G.Point}
    (haa' : G.SameRay o a a')
    (hbb' : G.SameRay o b b')
    (hoff : ¬G.Collinear a o b) :
    G.Orientation a o b = G.Orientation a' o b' := by
  have hb_off_oa : ¬G.Collinear o a b := by
    intro h
    exact hoff (collinear_swap G h)
  have hb'_off_oa : ¬G.Collinear o a b' := by
    intro hoab'
    have hob'a : G.Collinear o b' a :=
      collinear_swap_last G hoab'
    have hoba : G.Collinear o b a :=
      (collinear_on_same_line_iff G
        hbb'.2.1.symm hbb'.1.symm
        (collinear_swap_last G hbb'.2.2.1)).mp hob'a
    exact hoff (collinear_cyclic G (collinear_cyclic G hoba))
  have hsecond :
      G.Orientation a o b = G.Orientation a o b' := by
    calc
      G.Orientation a o b =
          (G.Orientation o a b).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap a o b
      _ = (G.Orientation o a b').map RotationSense.reverse := by
        rw [orientation_eq_of_sameRay_from_line_point G hbb' hb_off_oa]
      _ = G.Orientation a o b' :=
        (Plane.Axioms.orientation_swap a o b').symm
  have hfirst :
      G.Orientation a o b' = G.Orientation a' o b' := by
    calc
      G.Orientation a o b' = G.Orientation o b' a := by
        rw [Plane.Axioms.orientation_cyclic a o b',
          Plane.Axioms.orientation_cyclic o b' a]
      _ = G.Orientation o b' a' :=
        orientation_eq_of_sameRay_from_line_point G haa'
          (fun h => hb'_off_oa (collinear_swap_last G h))
      _ = G.Orientation a' o b' := by
        rw [Plane.Axioms.orientation_cyclic a' o b',
          Plane.Axioms.orientation_cyclic o b' a']
  exact hsecond.trans hfirst

/--
A problem-local synthetic angle certificate has equal directed measures when the two
orientations agree.
-/
theorem measure_eq_of_sameAngle_same_orientation
    (M : AngleMeasurement G) [M.Axioms]
    {a o b c p d : G.Point}
    (sense : RotationSense)
    (hleft : ¬G.Collinear a o b)
    (hangle : SameAngle G a o b c p d)
    (horientation :
      G.Orientation a o b = G.Orientation c p d) :
    M.measure ⟨a, o, b, sense⟩ =
      M.measure ⟨c, p, d, sense⟩ := by
  have hraw :
      AngleCongruent G a o b c p d :=
    sameAngle_to_angleCongruent G hangle
      ⟨by
        intro h
        subst a
        exact hleft (collinear_refl_left G o b),
       by
        intro h
        subst b
        exact hleft (collinear_refl_right G a o)⟩
  obtain
    ⟨x, y, z, w, hax, hby, hcz, hdw,
      hxz, hyw, hxy_zw⟩ := hraw
  have hright : ¬G.Collinear c p d := by
    intro hcpd
    have hrightOrientation :
        G.Orientation c p d = none :=
      (Plane.Axioms.orientation_collinear c p d).2 hcpd
    have hleftOrientation :
        G.Orientation a o b = none :=
      horientation.trans hrightOrientation
    exact hleft
      ((Plane.Axioms.orientation_collinear a o b).1
        hleftOrientation)
  have hsampleOrientation :
      G.Orientation x o y = G.Orientation z p w := by
    calc
      G.Orientation x o y = G.Orientation a o b :=
        (orientation_sameRay_invariant G hax hby hleft).symm
      _ = G.Orientation c p d := horientation
      _ = G.Orientation z p w :=
        orientation_sameRay_invariant G hcz hdw hright
  have hsamples :
      M.measure ⟨x, o, y, sense⟩ =
        M.measure ⟨z, p, w, sense⟩ :=
    AngleMeasurement.Axioms.sss_preserving
      x o y z p w sense hxz hyw hxy_zw hsampleOrientation
  calc
    M.measure ⟨a, o, b, sense⟩ =
        M.measure ⟨x, o, y, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        a x b y o sense hax hby
    _ = M.measure ⟨z, p, w, sense⟩ := hsamples
    _ = M.measure ⟨c, p, d, sense⟩ :=
      (AngleMeasurement.Axioms.same_ray_invariant
        c z d w p sense hcz hdw).symm

/--
The two inscribed angles determined by noncollinear ordered secants from one vertex have the
same orientation.
-/
theorem ordered_secant_inscribed_orientations
    {m a b c d : G.Point}
    (hab : G.Bet m a b)
    (hcd : G.Bet m c d)
    (hab_ne : a ≠ b)
    (hcd_ne : c ≠ d)
    (hmac : ¬G.Collinear m a c) :
    G.Orientation b a d = G.Orientation b c d := by
  have hma : m ≠ a := by
    intro h
    subst a
    exact hmac (collinear_refl_left G m c)
  have hmc : m ≠ c := by
    intro h
    subst c
    exact hmac
      (Or.inr (Or.inr (bet_start_refl G m a)))
  have hmd : m ≠ d := by
    intro h
    subst d
    exact hmc
      (Plane.Axioms.betweennessIdentity m c hcd)
  have hmb : m ≠ b := by
    intro h
    subst b
    exact hma
      (Plane.Axioms.betweennessIdentity m a hab)
  have hmad : ¬G.Collinear m a d := by
    intro hmad
    have hmcd : G.Collinear m c d := Or.inl hcd
    have hmca : G.Collinear m c a :=
      (collinear_on_same_line_iff G
        hmc hmd hmcd).mpr
        (collinear_swap_last G hmad)
    exact hmac (collinear_swap_last G hmca)
  have hmcb : ¬G.Collinear m c b := by
    intro hmcb
    have hmab : G.Collinear m a b := Or.inl hab
    have hmac' : G.Collinear m a c :=
      (collinear_on_same_line_iff G
        hma hmb hmab).mpr
        (collinear_swap_last G hmcb)
    exact hmac hmac'
  have hm_off_ad : ¬G.Collinear a d m := by
    intro h
    exact hmad
      (collinear_cyclic G (collinear_cyclic G h))
  have hb_off_ad : ¬G.Collinear a d b :=
    crossing_right_not_collinear G hm_off_ad
      (collinear_cyclic G (collinear_refl_left G a d))
      hab hab_ne
  have hmb_opposite :
      G.OppositeSides a d m b :=
    ⟨hm_off_ad, hb_off_ad, a,
      collinear_cyclic G (collinear_refl_left G a d),
      hab⟩
  have hm_off_cb : ¬G.Collinear c b m := by
    intro h
    exact hmcb
      (collinear_cyclic G (collinear_cyclic G h))
  have hd_off_cb : ¬G.Collinear c b d :=
    crossing_right_not_collinear G hm_off_cb
      (collinear_cyclic G (collinear_refl_left G c b))
      hcd hcd_ne
  have hmd_opposite :
      G.OppositeSides c b m d :=
    ⟨hm_off_cb, hd_off_cb, c,
      collinear_cyclic G (collinear_refl_left G c b),
      hcd⟩
  have hfirstCross :
      G.Orientation m a d =
        (G.Orientation b a d).map RotationSense.reverse := by
    calc
      G.Orientation m a d = G.Orientation a d m :=
        ((Plane.Axioms.orientation_cyclic a d m).trans
          (Plane.Axioms.orientation_cyclic d m a)).symm
      _ = (G.Orientation a d b).map RotationSense.reverse :=
        Plane.Axioms.orientation_opposite_sides (G := G)
          hmb_opposite
      _ = (G.Orientation b a d).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic a d b,
          Plane.Axioms.orientation_cyclic d b a]
  have hsecondCross :
      G.Orientation m c b = G.Orientation b c d := by
    calc
      G.Orientation m c b = G.Orientation c b m :=
        ((Plane.Axioms.orientation_cyclic c b m).trans
          (Plane.Axioms.orientation_cyclic b m c)).symm
      _ = (G.Orientation c b d).map RotationSense.reverse :=
        Plane.Axioms.orientation_opposite_sides (G := G)
          hmd_opposite
      _ = G.Orientation b c d :=
        (Plane.Axioms.orientation_swap b c d).symm
  have hcdRay : G.SameRay m c d :=
    sameRay_from_near_endpoint G hcd hmc hcd_ne
  have habRay : G.SameRay m a b :=
    sameRay_from_near_endpoint G hab hma hab_ne
  have hfirstRay :
      G.Orientation m a c = G.Orientation m a d :=
    orientation_eq_of_sameRay_from_line_point G
      hcdRay hmac
  have hsecondRay :
      G.Orientation m c a = G.Orientation m c b :=
    orientation_eq_of_sameRay_from_line_point G
      habRay
      (fun h => hmac (collinear_swap_last G h))
  have hswap :
      G.Orientation m c a =
        (G.Orientation m a c).map RotationSense.reverse := by
    calc
      G.Orientation m c a =
          (G.Orientation c m a).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap m c a
      _ = (G.Orientation m a c).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic c m a]
  have reverse_twice (x : Option RotationSense) :
      (x.map RotationSense.reverse).map RotationSense.reverse = x := by
    cases x with
    | none => rfl
    | some sense =>
        cases sense <;> rfl
  have hfirstTarget :
      G.Orientation b a d =
        (G.Orientation m a d).map RotationSense.reverse := by
    calc
      G.Orientation b a d =
          ((G.Orientation b a d).map RotationSense.reverse).map
            RotationSense.reverse :=
        (reverse_twice (G.Orientation b a d)).symm
      _ = (G.Orientation m a d).map RotationSense.reverse :=
        congrArg (Option.map RotationSense.reverse)
          hfirstCross.symm
  calc
    G.Orientation b a d =
        (G.Orientation m a d).map RotationSense.reverse :=
      hfirstTarget
    _ = (G.Orientation m a c).map RotationSense.reverse := by
      rw [hfirstRay]
    _ = G.Orientation m c a := hswap.symm
    _ = G.Orientation m c b := hsecondRay
    _ = G.Orientation b c d := hsecondCross

/--
Equal corresponding angles made by two rays from a common vertex force the joining segments
to be parallel.
-/
theorem parallel_of_corresponding_angles
    (M : AngleMeasurement G) [M.Axioms]
    {p e c f d : G.Point}
    (sense : RotationSense)
    (hec : G.SameRay p e c)
    (hfd : G.SameRay p f d)
    (hec_ne : e ≠ c)
    (hleft : ¬G.Collinear p e f)
    (hmeasure :
      M.measure ⟨p, e, f, sense⟩ =
        M.measure ⟨p, c, d, sense⟩)
    (horientation :
      G.Orientation p e f = G.Orientation p c d) :
    Parallel G e f c d := by
  have hpe : p ≠ e := hec.1.symm
  have hpc : p ≠ c := hec.2.1.symm
  have hpf : p ≠ f := hfd.1.symm
  have hpd : p ≠ d := hfd.2.1.symm
  have hef : e ≠ f := by
    intro h
    subst f
    exact hleft (collinear_refl_right G p e)
  have hcpd : ¬G.Collinear c p d := by
    intro hcpd
    have hpcd : G.Collinear p c d :=
      collinear_swap G hcpd
    have hpef : G.Collinear p e f := by
      have hpfd : G.Collinear p f d := hfd.2.2.1
      have hped : G.Collinear p e d :=
        (collinear_on_same_line_iff G
          hpc hpe
          (collinear_swap_last G hec.2.2.1)).mp hpcd
      have hpde : G.Collinear p d e :=
        collinear_swap_last G hped
      have hpdf : G.Collinear p d f :=
        collinear_swap_last G hpfd
      exact collinear_three_on_line G hpd
        (Or.inr (Or.inr (bet_start_refl G p d)))
        hpde hpdf
    exact hleft hpef
  obtain ⟨n, hn⟩ := midpoint_exists G e c
  have he_n : e ≠ n := by
    intro h
    subst n
    exact hec_ne
      (Plane.Axioms.congruenceIdentity e c e
        (congruent_symm G hn.2))
  have hecReflection : PointReflection G n e c :=
    midpoint_as_pointReflection G hn
  obtain ⟨p', hpp'⟩ := pointReflection_exists G n p
  obtain ⟨f', hff'⟩ := pointReflection_exists G n f
  obtain ⟨f'', hf'f''⟩ := pointReflection_exists G c f'
  have henc : G.Collinear e n c :=
    Or.inl hn.1
  have hecp : G.Collinear e c p :=
    collinear_cyclic G hec.2.2.1
  have hecn : G.Collinear e c n :=
    collinear_swap_last G henc
  have henp : G.Collinear e n p :=
    (collinear_on_same_line_iff G
      hec_ne he_n hecn).mp hecp
  have hn_off_ef : ¬G.Collinear e f n := by
    intro hefn
    have henf : G.Collinear e n f :=
      collinear_swap_last G hefn
    have hene : G.Collinear e n e :=
      Or.inr (Or.inr (bet_start_refl G e n))
    have hpef : G.Collinear p e f :=
      collinear_three_on_line G he_n
        henp hene henf
    exact hleft hpef
  have hef_parallel_cf' : Parallel G e f c f' :=
    pointReflection_image_parallel G hef hn_off_ef
      hecReflection hff'
  have hep_cp' : G.Congruent e p c p' :=
    pointReflection_cross_congruent G hecReflection hpp'
  have hef_cf' : G.Congruent e f c f' :=
    pointReflection_cross_congruent G hecReflection hff'
  have hpf_p'f' : G.Congruent p f p' f' :=
    pointReflection_cross_congruent G hpp' hff'
  have hp'c : p' ≠ c := by
    intro h
    subst p'
    exact hpe
      (Plane.Axioms.congruenceIdentity e p c hep_cp').symm
  have hf'c : f' ≠ c := by
    intro h
    subst f'
    exact hef
      (Plane.Axioms.congruenceIdentity e f c hef_cf')
  have hf''c : f'' ≠ c :=
    pointReflection_other_ne G hf'f'' hf'c
  have hreflectionAngle :
      SameAngle G p e f p' c f' :=
    SameAngle.basic
      (angleCongruent_of_sss G
        hpe hef.symm hp'c hf'c
        hep_cp' hef_cf' hpf_p'f')
  have hpcp' : G.Bet p c p' :=
    midpoint_reflection_beyond_sameRay G hec hn hpp'
  have hvertical :
      SameAngle G p' c f' p c f'' :=
    vertical_angles G hp'c hf'c hpc hf''c
      (bet_symm G hpcp') hf'f''.between
  have hconstructed :
      SameAngle G p e f p c f'' :=
    SameAngle.trans hreflectionAngle hvertical
  have hf_off_cp : ¬G.Collinear c p f := by
    intro hcpf
    exact hleft
      ((collinear_on_same_line_iff G
        hpe hpc hec.2.2.1).mpr
        (collinear_swap G hcpf))
  have hn_line_cp : G.Collinear c p n := by
    exact collinear_three_on_line G hec_ne
      (collinear_refl_right G e c)
      hecp hecn
  have hf'_off_cp : ¬G.Collinear c p f' :=
    pointReflection_off_line G hn_line_cp
      hf_off_cp hff'
  have hf''_off : ¬G.Collinear c p f'' :=
    pointReflection_off_line G
      (collinear_cyclic G (collinear_refl_left G c p))
      hf'_off_cp hf'f''
  have hf_f' : G.OppositeSides c p f f' :=
    pointReflection_oppositeSides G hn_line_cp
      hf_off_cp hff'
  have hf''_f' : G.OppositeSides c p f'' f' :=
    oppositeSides_symm G
      (pointReflection_oppositeSides G
        (collinear_cyclic G (collinear_refl_left G c p))
        hf'_off_cp hf'f'')
  have hnot_f_f'' : ¬G.OppositeSides c p f f'' :=
    not_oppositeSides_of_common_opposite G hf_f' hf''_f'
  have hnot_f_d : ¬G.OppositeSides c p f d := by
    intro hopposite
    have hopposite_pe : G.OppositeSides p e f d := by
      have hopposite_pc : G.OppositeSides p c f d :=
        oppositeSides_swap_line G hopposite
      exact
        (oppositeSides_on_same_line_iff G
          hpc hpe
          (collinear_swap_last G hec.2.2.1)).mp
          hopposite_pc
    exact (not_oppositeSides_of_sameRay G hfd hleft)
      hopposite_pe
  have hnot_f''_d : ¬G.OppositeSides c p f'' d :=
    not_oppositeSides_trans G hf_off_cp
      (fun h => hnot_f_f'' (oppositeSides_symm G h))
      hnot_f_d
  have hsource_cf :
      G.Orientation p e f = G.Orientation p c f := by
    calc
      G.Orientation p e f =
          (G.Orientation p f e).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_swap p e f,
          Plane.Axioms.orientation_cyclic e p f]
      _ = (G.Orientation p f c).map RotationSense.reverse := by
        rw [orientation_eq_of_sameRay_from_line_point G hec
          (fun h => hleft (collinear_swap_last G h))]
      _ = G.Orientation p c f := by
        rw [Plane.Axioms.orientation_swap p c f,
          Plane.Axioms.orientation_cyclic c p f]
  have hcf_cf'' :
      G.Orientation p c f = G.Orientation p c f'' := by
    have hlineOrientation :
        G.Orientation c p f = G.Orientation c p f'' :=
      orientation_eq_of_not_oppositeSides G
        hf_off_cp hf''_off hnot_f_f''
    calc
      G.Orientation p c f =
          (G.Orientation c p f).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap p c f
      _ = (G.Orientation c p f'').map RotationSense.reverse := by
        rw [hlineOrientation]
      _ = G.Orientation p c f'' :=
        (Plane.Axioms.orientation_swap p c f'').symm
  have hconstructedOrientation :
      G.Orientation p e f = G.Orientation p c f'' :=
    hsource_cf.trans hcf_cf''
  have hconstructedMeasure :
      M.measure ⟨p, e, f, sense⟩ =
        M.measure ⟨p, c, f'', sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      hleft hconstructed hconstructedOrientation
  have hconstructedTargetOrientation :
      G.Orientation p c f'' = G.Orientation p c d :=
    hconstructedOrientation.symm.trans horientation
  have hconstructedTargetMeasure :
      M.measure ⟨p, c, f'', sense⟩ =
        M.measure ⟨p, c, d, sense⟩ :=
    hconstructedMeasure.symm.trans hmeasure
  have hf''d : G.SameRay c f'' d :=
    AngleMeasurement.Axioms.ray_determined_by_measure_same_side
      p c f'' d sense
      (fun h => hf''_off (collinear_swap G h))
      (fun h => hcpd (collinear_swap G h))
      hconstructedTargetOrientation
      hconstructedTargetMeasure
  have hcf'' : c ≠ f'' := hf''d.1.symm
  have hcfd : G.Collinear c f'' d :=
    hf''d.2.2.1
  have hcff' : G.Collinear c f'' f' :=
    Or.inr (Or.inr hf'f''.between)
  have hcf''c : G.Collinear c f'' c :=
    Or.inr (Or.inr (bet_start_refl G c f''))
  have hcdf' : G.Collinear c d f' :=
    collinear_three_on_line G hcf''
      hcf''c hcfd hcff'
  refine ⟨hef, hf''d.2.1.symm, ?_⟩
  rintro ⟨x, hefx, hcdx⟩
  have hcf'x : G.Collinear c f' x :=
    (collinear_on_same_line_iff G
      hf''d.2.1.symm hf'c.symm hcdf').mp hcdx
  exact hef_parallel_cf'.2.2 ⟨x, hefx, hcf'x⟩

/--
Two noncollinear triangles with two corresponding angles equal either have equal corresponding
radial sides, or determine a genuine fourth-proportional configuration.
-/
theorem aa_equal_scale_or_fourthProportional
    (M : AngleMeasurement G) [M.Axioms]
    {o a b c d : G.Point}
    (sense : RotationSense)
    (hleft : ¬G.Collinear o a b)
    (hright : ¬G.Collinear o c d)
    (hvertex : SameAngle G a o b c o d)
    (hbaseMeasure :
      M.measure ⟨o, a, b, sense⟩ =
        M.measure ⟨o, c, d, sense.reverse⟩)
    (hbaseOrientation :
      G.Orientation o a b =
        (G.Orientation o c d).map RotationSense.reverse) :
    (G.Congruent o a o c ∧ G.Congruent o b o d) ∨
      ∃ e f,
        G.FourthProportionalConfiguration o e f c d ∧
          G.Congruent o e o a ∧
          G.Congruent o f o b := by
  have hao : a ≠ o := by
    intro h
    subst a
    exact hleft (collinear_refl_left G o b)
  have hbo : b ≠ o := by
    intro h
    subst b
    exact hleft (Or.inr (Or.inr (bet_start_refl G o a)))
  have hco : c ≠ o := by
    intro h
    subst c
    exact hright (collinear_refl_left G o d)
  have hdo : d ≠ o := by
    intro h
    subst d
    exact hright (Or.inr (Or.inr (bet_start_refl G o c)))
  obtain ⟨cOpposite, hcOpposite⟩ :=
    pointReflection_exists G o c
  obtain ⟨e, hcOpposite_o_e, hoe_oa⟩ :=
    Plane.Axioms.segmentConstruction o o a cOpposite
  have hcOpposite_o : cOpposite ≠ o :=
    pointReflection_other_ne G hcOpposite hco
  have heo : e ≠ o := by
    intro h
    subst e
    exact hao
      (Plane.Axioms.congruenceIdentity
        o a o (congruent_symm G hoe_oa)).symm
  have hce : G.SameRay o c e :=
    sameRay_of_common_opposite G
      hcOpposite_o hco heo
      (bet_symm G hcOpposite.between)
      hcOpposite_o_e
  obtain ⟨dOpposite, hdOpposite⟩ :=
    pointReflection_exists G o d
  obtain ⟨f, hdOpposite_o_f, hof_ob⟩ :=
    Plane.Axioms.segmentConstruction o o b dOpposite
  have hdOpposite_o : dOpposite ≠ o :=
    pointReflection_other_ne G hdOpposite hdo
  have hfo : f ≠ o := by
    intro h
    subst f
    exact hbo
      (Plane.Axioms.congruenceIdentity
        o b o (congruent_symm G hof_ob)).symm
  have hdf : G.SameRay o d f :=
    sameRay_of_common_opposite G
      hdOpposite_o hdo hfo
      (bet_symm G hdOpposite.between)
      hdOpposite_o_f
  by_cases hec : e = c
  · subst e
    have hoa_oc : G.Congruent o a o c :=
      congruent_symm G hoe_oa
    have hvertexCopied :
        SameAngle G a o b c o f :=
      sameAngle_change_rays G
        (sameRay_refl G hao)
        (sameRay_refl G hbo)
        (sameRay_refl G hco)
        hdf hvertex
    have hvertexRaw :
        AngleCongruent G a o b c o f :=
      sameAngle_to_angleCongruent G hvertexCopied
        ⟨hao, hbo⟩
    obtain
      ⟨x, y, z, w, hax, hby, hcz, hfw,
        hxz, hyw, hxy_zw⟩ := hvertexRaw
    have hab_cf : G.Congruent a b c f :=
      angle_certificate_move_samples G
        (sameRay_symm G hax)
        (sameRay_symm G hby)
        (sameRay_symm G hcz)
        (sameRay_symm G hfw)
        hxz hyw hoa_oc
        (congruent_symm G hof_ob)
        hxy_zw
    have hf_off_oc : ¬G.Collinear o c f := by
      intro hocf
      have hodc : G.Collinear o d c :=
        (collinear_on_same_line_iff G
          hfo.symm hdo.symm
          (collinear_swap_last G hdf.2.2.1)).mp
          (collinear_swap_last G hocf)
      exact hright (collinear_swap_last G hodc)
    have hconstructedOrientation :
        G.Orientation o c f = G.Orientation o c d :=
      orientation_eq_of_sameRay_from_line_point G
        (sameRay_symm G hdf) hf_off_oc
    have hsourceConstructedOrientation :
        G.Orientation o a b =
          (G.Orientation o c f).map RotationSense.reverse := by
      calc
        G.Orientation o a b =
            (G.Orientation o c d).map RotationSense.reverse :=
          hbaseOrientation
        _ = (G.Orientation o c f).map RotationSense.reverse := by
          rw [hconstructedOrientation]
    have hsourceConstructedMeasure :
        M.measure ⟨o, a, b, sense⟩ =
          M.measure ⟨o, c, f, sense.reverse⟩ :=
      AngleMeasurement.Axioms.sss_reversing
        o a b o c f sense
        (congruent_trans G
          (Plane.Axioms.congruenceReversal a o)
          (congruent_trans G hoa_oc
            (Plane.Axioms.congruenceReversal o c)))
        hab_cf (congruent_symm G hof_ob)
        hsourceConstructedOrientation
    have hconstructedTargetMeasure :
        M.measure ⟨o, c, f, sense.reverse⟩ =
          M.measure ⟨o, c, d, sense.reverse⟩ :=
      hsourceConstructedMeasure.symm.trans hbaseMeasure
    have hcfd : G.SameRay c f d :=
      AngleMeasurement.Axioms.ray_determined_by_measure_same_side
        o c f d sense.reverse
        hf_off_oc hright
        hconstructedOrientation hconstructedTargetMeasure
    have hfd_eq : f = d := by
      apply Classical.byContradiction
      intro hfd_ne
      have hfd_o : G.Collinear f d o := by
        exact collinear_cyclic G
          (collinear_cyclic G
            (collinear_swap G hdf.2.2.1))
      have hfd_c : G.Collinear f d c :=
        collinear_cyclic G hcfd.2.2.1
      have hfd_f : G.Collinear f d f :=
        collinear_cyclic G (collinear_refl_left G f d)
      exact hf_off_oc
        (collinear_three_on_line G hfd_ne
          hfd_o hfd_c hfd_f)
    subst f
    exact Or.inl
      ⟨hoa_oc, congruent_symm G hof_ob⟩
  have hvertexCopied :
      SameAngle G a o b e o f :=
    sameAngle_change_rays G
      (sameRay_refl G hao)
      (sameRay_refl G hbo)
      hce hdf hvertex
  have hvertexRaw :
      AngleCongruent G a o b e o f :=
    sameAngle_to_angleCongruent G hvertexCopied
      ⟨hao, hbo⟩
  obtain
    ⟨x, y, z, w, hax, hby, hez, hfw,
      hxz, hyw, hxy_zw⟩ := hvertexRaw
  have hxy_ef : G.Congruent a b e f :=
    angle_certificate_move_samples G
      (sameRay_symm G hax)
      (sameRay_symm G hby)
      (sameRay_symm G hez)
      (sameRay_symm G hfw)
      hxz hyw
      (congruent_symm G hoe_oa)
      (congruent_symm G hof_ob)
      hxy_zw
  have hae : a ≠ b := by
    intro h
    subst b
    exact hleft (collinear_refl_right G o a)
  have hef : e ≠ f := by
    intro h
    subst f
    exact hae
      (Plane.Axioms.congruenceIdentity
        a b e hxy_ef)
  have hao_eo : G.Congruent a o e o :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal a o)
      (congruent_trans G
        (congruent_symm G hoe_oa)
        (Plane.Axioms.congruenceReversal o e))
  have hob_of : G.Congruent o b o f :=
    congruent_symm G hof_ob
  have hbaseConstructed :
      SameAngle G o a b o e f :=
    SameAngle.basic
      (angleCongruent_of_sss G
        hao.symm hae.symm heo.symm hef.symm
        hao_eo hxy_ef hob_of)
  have hoef : ¬G.Collinear o e f := by
    intro hoef
    have hocf : G.Collinear o c f :=
      (collinear_on_same_line_iff G
        hco.symm heo.symm hce.2.2.1).mpr hoef
    have hocd : G.Collinear o c d := by
      have hofd : G.Collinear o f d :=
        collinear_swap_last G hdf.2.2.1
      exact collinear_trans G hfo.symm
        (collinear_swap_last G hocf) hofd
    exact hright hocd
  have hcorrespondingOrientation :
      G.Orientation o e f = G.Orientation o c d := by
    have he_off_of : ¬G.Collinear o f e := by
      intro h
      exact hoef (collinear_swap_last G h)
    have hf_off_oc : ¬G.Collinear o c f := by
      intro hocf
      exact hoef
        ((collinear_on_same_line_iff G
          hco.symm heo.symm hce.2.2.1).mp hocf)
    calc
      G.Orientation o e f =
          (G.Orientation o f e).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_swap o e f,
          Plane.Axioms.orientation_cyclic e o f]
      _ = (G.Orientation o f c).map RotationSense.reverse := by
        rw [orientation_eq_of_sameRay_from_line_point G
          (sameRay_symm G hce) he_off_of]
      _ = G.Orientation o c f := by
        rw [Plane.Axioms.orientation_swap o c f,
          Plane.Axioms.orientation_cyclic c o f]
      _ = G.Orientation o c d :=
        orientation_eq_of_sameRay_from_line_point G
          (sameRay_symm G hdf) hf_off_oc
  have hsourceConstructedOrientation :
      G.Orientation o a b =
        (G.Orientation o e f).map RotationSense.reverse := by
    calc
      G.Orientation o a b =
          (G.Orientation o c d).map RotationSense.reverse :=
        hbaseOrientation
      _ = (G.Orientation o e f).map RotationSense.reverse := by
        rw [hcorrespondingOrientation]
  have hsourceConstructedMeasure :
      M.measure ⟨o, a, b, sense⟩ =
        M.measure ⟨o, e, f, sense.reverse⟩ := by
    exact AngleMeasurement.Axioms.sss_reversing
      o a b o e f sense
      hao_eo hxy_ef hob_of hsourceConstructedOrientation
  have hcorrespondingMeasure :
      M.measure ⟨o, e, f, sense.reverse⟩ =
        M.measure ⟨o, c, d, sense.reverse⟩ :=
    hsourceConstructedMeasure.symm.trans hbaseMeasure
  have hparallel : Parallel G e f c d :=
    parallel_of_corresponding_angles G M sense.reverse
      (sameRay_symm G hce)
      (sameRay_symm G hdf)
      hec hoef
      hcorrespondingMeasure hcorrespondingOrientation
  have hstrict : G.StrictlyParallel e f c d :=
    (strictlyParallel_iff_no_intersection G).mpr hparallel
  exact Or.inr
    ⟨e, f,
      ⟨sameRay_symm G hce,
        sameRay_symm G hdf,
        hoef, hstrict⟩,
      hoe_oa, hof_ob⟩

end Soultions.Sharygin.Page15.Problem30.Similarity
