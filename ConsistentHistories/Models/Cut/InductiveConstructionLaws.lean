import ConsistentHistories.Models.Cut.InductiveConstruction

/-!
Paper section 3.4: located-semilattice laws for the inductive
construction.

This module packages the deterministic construction from
`InductiveConstruction` as a located semilattice.
-/

namespace ConsistentHistories.Models.Cut.InductiveConstruction

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.LocatedSemilattices.TopTrees

universe u

namespace LocalStateData

theorem attest_medial_of_same_controller {D : LocalStateData.{u}} {a b c d : Time D}
    (hab : Time.controller a = Time.controller b)
    (hbc : Time.controller b = Time.controller c)
    (hcd : Time.controller c = Time.controller d) :
    attest (attest a b) (attest c d) = attest (attest a c) (attest b d) := by
  calc
    attest (attest a b) (attest c d) =
        attest a (attest b (attest c d)) := by
      rw [attest_assoc_of_same_controller hab (hbc.trans (attest_controller c d).symm)]
    _ = attest a (attest (attest b c) d) := by
      rw [← attest_assoc_of_same_controller hbc hcd]
    _ = attest a (attest (attest c b) d) := by
      rw [attest_comm_of_same_controller hbc.symm]
    _ = attest a (attest c (attest b d)) := by
      rw [attest_assoc_of_same_controller hbc.symm (hbc.trans hcd)]
    _ = attest (attest a c) (attest b d) := by
      rw [← attest_assoc_of_same_controller (hab.trans hbc)
        (hbc.symm.trans (attest_controller b d).symm)]

theorem attest_contradiction_top_of_same_controller {D : LocalStateData.{u}}
    {t t' s s' : Time D}
    (htt' : Time.controller t = Time.controller t')
    (hts : Time.controller t = Time.controller s)
    (hss' : Time.controller s = Time.controller s')
    (hcontr : attest s s' = top D (Time.controller s)) :
    attest (attest t s) (attest t' s') = top D (Time.controller t) := by
  calc
    attest (attest t s) (attest t' s') =
        attest (attest t t') (attest s s') := by
      rw [attest_medial_of_same_controller hts (hts.symm.trans htt')
        (htt'.symm.trans (hts.trans hss'))]
    _ = attest (attest t t') (top D (Time.controller s)) := by rw [hcontr]
    _ = top D (Time.controller t) := by
      rw [← hts]
      exact attest_top_right_same_controller (Time.controller t) (attest t t')
        (attest_controller t t')

/-- Proposition 3.4.5: contradiction preservation for the deterministic attestation. -/
theorem attest_contradiction_preserving_of_top {D : LocalStateData.{u}} {t t' s s' : Time D}
    (htt' : Time.controller t = Time.controller t')
    (hss' : Time.controller s = Time.controller s')
    (hcontr : attest s s' = top D (Time.controller s)) :
    RawContradicts Time.controller attest (top D) (attest t s) (attest t' s') := by
  constructor
  · exact (attest_controller t s).trans (htt'.trans (attest_controller t' s').symm)
  · by_cases hts : Time.controller t = Time.controller s
    · have htop :=
        attest_contradiction_top_of_same_controller htt' hts hss' hcontr
      simpa [attest_controller t s] using htop
    · cases t with
      | top p =>
          rfl
      | consistent tct =>
          cases t' with
          | top p' =>
              simp [Time.controller] at htt'
              cases htt'
              simpa [attest, attestAtTime, top, Time.controller] using
                attest_right_top_clause (attest (CTime.toTime tct) s)
                  (Time.controller (CTime.toTime tct))
          | consistent tct' =>
              simp [Time.controller] at htt'
              cases htt'
              cases s with
              | top q =>
                  have hfirst :
                      attest (CTime.toTime tct) (Time.top q) =
                        Time.top (Time.controller (CTime.toTime tct)) := by
                    simpa [top] using attest_right_top_clause (CTime.toTime tct) q
                  have hfirst' :
                      attest (Time.consistent tct) (Time.top q) =
                        Time.top (Time.controller (Time.consistent tct)) := by
                    simpa [CTime.toTime] using hfirst
                  rw [hfirst']
                  rfl
              | consistent sct =>
                  cases s' with
                  | top q' =>
                      simp [Time.controller] at hss'
                      cases hss'
                      have hsecond :
                          attest (CTime.toTime tct')
                              (Time.top (Time.controller (CTime.toTime sct))) =
                            Time.top (Time.controller (CTime.toTime tct')) := by
                        simpa [top] using attest_right_top_clause (CTime.toTime tct')
                          (Time.controller (CTime.toTime sct))
                      have hsecond' :
                          attest (Time.consistent tct')
                              (Time.top (Time.controller (Time.consistent sct))) =
                            Time.top (Time.controller (Time.consistent tct')) := by
                        simpa [CTime.toTime] using hsecond
                      simp [Time.controller] at hsecond'
                      rw [hsecond']
                      simpa [top, Time.controller] using
                        attest_right_top_clause
                          (attest (CTime.toTime tct) (CTime.toTime sct))
                          (Time.controller (CTime.toTime tct'))
                  | consistent sct' =>
                      simp [Time.controller] at hss'
                      cases hss'
                      cases tct with
                      | bot p =>
                          cases tct' with
                          | bot p' =>
                              simp [Time.controller] at hts
                              have hsource :
                                  (attestAtCTime sct (Time.consistent sct')).1 =
                                    Time.top (Time.controller (CTime.toTime sct)) := by
                                simpa [attest, attestAtTime, attest_ctime_eq, top,
                                  Time.controller, CTime.toTime] using hcontr
                              simp [Time.controller, CTime.toTime] at hsource
                              have hst := Ne.symm hts
                              have hfirst := attest_left_bot_cross_clause (D := D) hst sct
                              have hsecond := attest_left_bot_cross_clause (D := D) hst sct'
                              simp [bot, CTime.toTime] at hfirst hsecond
                              rw [hfirst, hsecond]
                              simp only [attest, attestAtTime, attestAtCTime, CTime.toTime,
                                Time.controller, CTime.crossBotNode]
                              rw [dif_pos trivial]
                              have hbot_not : ¬ D.semilattice.join D.semilattice.bot D.semilattice.bot = D.semilattice.top := by
                                intro htop
                                exact D.bot_ne_top ((D.semilattice.join_idem D.semilattice.bot).symm.trans htop)
                              have hview :
                                  ∃ k hkj,
                                    (attestAtCTime (CTime.botViewsWith hst sct k hkj)
                                        (Time.consistent (CTime.botViewsWith hst sct' k hkj))).1 =
                                      Time.top k := by
                                refine ⟨Time.controller (CTime.toTime sct), hst, ?_⟩
                                simpa [Time.controller, CTime.toTime, CTime.botViewsWith_same]
                                  using hsource
                              rw [dif_neg hbot_not, dif_pos hview]
                              rfl
                          | node p' x' hx' m =>
                              rename_i j p
                              simp [Time.controller] at hts
                              have hst := Ne.symm hts
                              have hsource :
                                  attest (CTime.toTime sct) (CTime.toTime sct') =
                                    top D p := by
                                simpa [CTime.toTime, Time.controller] using hcontr
                              have hfirst := attest_left_bot_cross_clause (D := D) hst sct
                              simp [bot, CTime.toTime] at hfirst
                              rw [hfirst]
                              cases sct' with
                              | bot _ =>
                                  have hright :
                                      attest (CTime.toTime sct) (bot D p) =
                                        CTime.toTime sct :=
                                    attest_bot_right_same_controller p (CTime.toTime sct) rfl
                                  have htop_sct : CTime.toTime sct = top D p := by
                                    calc
                                      CTime.toTime sct =
                                          attest (CTime.toTime sct) (bot D p) := hright.symm
                                      _ = top D p := by
                                        simpa [bot, CTime.toTime] using hsource
                                  cases htop_sct
                              | node _ y hy n =>
                                  by_cases htop :
                                      (attestAtCTime (m p hst)
                                        (CTime.toTime (CTime.node p y hy n))).1 =
                                        Time.top p
                                  · have hviewTop :
                                        Attests D (CTime.toTime (m p hst))
                                          (CTime.toTime (CTime.node p y hy n)) (top D p) := by
                                      have htopEq :
                                          attest (CTime.toTime (m p hst))
                                            (CTime.toTime (CTime.node p y hy n)) = top D p := by
                                        simpa [attest_ctime_eq, CTime.toTime, top] using htop
                                      have hg := Attests.attest_graph (D := D)
                                        (CTime.toTime (m p hst))
                                        (CTime.toTime (CTime.node p y hy n))
                                      rwa [htopEq] at hg
                                    have hsecond :=
                                      attest_node_cross_top_clause (D := D) (j := j) (i := p)
                                        (x := x') (y := y) (hx := hx') (hy := hy)
                                        (l := m) (m := n) hst hviewTop
                                    have hsecond' :
                                        attest (Time.consistent (CTime.node j x' hx' m))
                                            (Time.consistent (CTime.node p y hy n)) =
                                          top D j := by
                                      simpa [CTime.toTime] using hsecond
                                    rw [hsecond']
                                    simpa [top, Time.controller, CTime.toTime, CTime.crossBotNode]
                                      using
                                        attest_right_top_clause
                                          (CTime.toTime (CTime.crossBotNode j p hst sct)) j
                                  · let r : CTime D p :=
                                      Time.toCTimeOfNonTop
                                        (attestAtCTime (m p hst)
                                          (CTime.toTime (CTime.node p y hy n))) htop
                                    have hr :
                                        CTime.toTime r =
                                          attest (CTime.toTime (m p hst))
                                            (CTime.toTime (CTime.node p y hy n)) := by
                                      calc
                                        CTime.toTime r =
                                            (attestAtCTime (m p hst)
                                              (CTime.toTime (CTime.node p y hy n))).1 := by
                                          exact Time.toCTimeOfNonTop_toTime
                                            (attestAtCTime (m p hst)
                                              (CTime.toTime (CTime.node p y hy n))) htop
                                        _ = attest (CTime.toTime (m p hst))
                                            (CTime.toTime (CTime.node p y hy n)) := by
                                          exact (attest_ctime_eq (m p hst)
                                            (CTime.toTime (CTime.node p y hy n))).symm
                                    have hviewR :
                                        Attests D (CTime.toTime (m p hst))
                                          (CTime.toTime (CTime.node p y hy n))
                                          (CTime.toTime r) := by
                                      have hg := Attests.attest_graph (D := D)
                                        (CTime.toTime (m p hst))
                                        (CTime.toTime (CTime.node p y hy n))
                                      rw [← hr] at hg
                                      exact hg
                                    have hsecond :=
                                      attest_node_cross_consistent_clause (D := D) (j := j)
                                        (i := p) (x := x') (y := y) (hx := hx') (hy := hy)
                                        (l := m) (m := n) hst hviewR
                                    have hsecond' :
                                        attest (Time.consistent (CTime.node j x' hx' m))
                                            (Time.consistent (CTime.node p y hy n)) =
                                          CTime.toTime (CTime.node j x' hx'
                                            (CTime.viewsUpdate m hst r)) := by
                                      simpa [CTime.toTime] using hsecond
                                    rw [hsecond']
                                    have hviewEq :
                                        attest (CTime.toTime sct) (CTime.toTime r) =
                                          top D p := by
                                      have hraw := attest_contradiction_top_of_same_controller
                                        (D := D) (t := CTime.toTime sct)
                                        (t' := CTime.toTime (m p hst))
                                        (s := CTime.toTime sct)
                                        (s' := CTime.toTime (CTime.node p y hy n))
                                        rfl rfl rfl (by simpa [CTime.toTime] using hsource)
                                      simpa [attest_self_time (CTime.toTime sct), hr]
                                        using hraw
                                    have hviewTop :
                                        Attests D
                                          (CTime.toTime (CTime.botViewsWith hst sct p hst))
                                          (CTime.toTime (CTime.viewsUpdate m hst r p hst))
                                          (top D p) := by
                                      have htopEq :
                                          attest
                                            (CTime.toTime (CTime.botViewsWith hst sct p hst))
                                            (CTime.toTime (CTime.viewsUpdate m hst r p hst)) =
                                            top D p := by
                                        simpa [CTime.botViewsWith_same, CTime.viewsUpdate_same]
                                          using hviewEq
                                      have hg := Attests.attest_graph (D := D)
                                        (CTime.toTime (CTime.botViewsWith hst sct p hst))
                                        (CTime.toTime (CTime.viewsUpdate m hst r p hst))
                                      rwa [htopEq] at hg
                                    simpa [top, Time.controller, CTime.toTime, CTime.crossBotNode]
                                      using
                                        attest_node_same_view_top_clause (D := D) (j := j)
                                          (k := p)
                                          (x := D.semilattice.bot) (y := x')
                                          (hx := CTime.botX_consistent D) (hy := hx')
                                          (l := CTime.botViewsWith hst sct)
                                          (m := CTime.viewsUpdate m hst r) hst hviewTop
                      | node p x hx l =>
                          cases tct' with
                          | bot p' =>
                              rename_i j p
                              simp [Time.controller] at hts
                              have hst := Ne.symm hts
                              have hsource :
                                  attest (CTime.toTime sct) (CTime.toTime sct') =
                                    top D p := by
                                simpa [CTime.toTime, Time.controller] using hcontr
                              have hsecond := attest_left_bot_cross_clause (D := D) hst sct'
                              simp [bot, CTime.toTime] at hsecond
                              rw [hsecond]
                              cases sct with
                              | bot _ =>
                                  have hleft :
                                      attest (bot D p) (CTime.toTime sct') =
                                        CTime.toTime sct' :=
                                    attest_bot_left_same_controller p (CTime.toTime sct') rfl
                                  have htop_sct' : CTime.toTime sct' = top D p := by
                                    calc
                                      CTime.toTime sct' =
                                          attest (bot D p) (CTime.toTime sct') := hleft.symm
                                      _ = top D p := by
                                        simpa [bot, CTime.toTime] using hsource
                                  cases htop_sct'
                              | node _ y hy n =>
                                  by_cases htop :
                                      (attestAtCTime (l p hst)
                                        (CTime.toTime (CTime.node p y hy n))).1 =
                                        Time.top p
                                  · have hviewTop :
                                        Attests D (CTime.toTime (l p hst))
                                          (CTime.toTime (CTime.node p y hy n)) (top D p) := by
                                      have htopEq :
                                          attest (CTime.toTime (l p hst))
                                            (CTime.toTime (CTime.node p y hy n)) = top D p := by
                                        simpa [attest_ctime_eq, CTime.toTime, top] using htop
                                      have hg := Attests.attest_graph (D := D)
                                        (CTime.toTime (l p hst))
                                        (CTime.toTime (CTime.node p y hy n))
                                      rwa [htopEq] at hg
                                    have hfirst :=
                                      attest_node_cross_top_clause (D := D) (j := j) (i := p)
                                        (x := x) (y := y) (hx := hx) (hy := hy)
                                        (l := l) (m := n) hst hviewTop
                                    have hfirst' :
                                        attest (Time.consistent (CTime.node j x hx l))
                                            (Time.consistent (CTime.node p y hy n)) =
                                          top D j := by
                                      simpa [CTime.toTime] using hfirst
                                    rw [hfirst']
                                    exact attest_left_top_clause j
                                      (CTime.toTime (CTime.crossBotNode j p hst sct'))
                                  · let r : CTime D p :=
                                      Time.toCTimeOfNonTop
                                        (attestAtCTime (l p hst)
                                          (CTime.toTime (CTime.node p y hy n))) htop
                                    have hr :
                                        CTime.toTime r =
                                          attest (CTime.toTime (l p hst))
                                            (CTime.toTime (CTime.node p y hy n)) := by
                                      calc
                                        CTime.toTime r =
                                            (attestAtCTime (l p hst)
                                              (CTime.toTime (CTime.node p y hy n))).1 := by
                                          exact Time.toCTimeOfNonTop_toTime
                                            (attestAtCTime (l p hst)
                                              (CTime.toTime (CTime.node p y hy n))) htop
                                        _ = attest (CTime.toTime (l p hst))
                                            (CTime.toTime (CTime.node p y hy n)) := by
                                          exact (attest_ctime_eq (l p hst)
                                            (CTime.toTime (CTime.node p y hy n))).symm
                                    have hviewR :
                                        Attests D (CTime.toTime (l p hst))
                                          (CTime.toTime (CTime.node p y hy n))
                                          (CTime.toTime r) := by
                                      have hg := Attests.attest_graph (D := D)
                                        (CTime.toTime (l p hst))
                                        (CTime.toTime (CTime.node p y hy n))
                                      rw [← hr] at hg
                                      exact hg
                                    have hfirst :=
                                      attest_node_cross_consistent_clause (D := D) (j := j)
                                        (i := p) (x := x) (y := y) (hx := hx) (hy := hy)
                                        (l := l) (m := n) hst hviewR
                                    have hfirst' :
                                        attest (Time.consistent (CTime.node j x hx l))
                                            (Time.consistent (CTime.node p y hy n)) =
                                          CTime.toTime (CTime.node j x hx
                                            (CTime.viewsUpdate l hst r)) := by
                                      simpa [CTime.toTime] using hfirst
                                    rw [hfirst']
                                    have hviewEq :
                                        attest (CTime.toTime r) (CTime.toTime sct') =
                                          top D p := by
                                      have hraw := attest_contradiction_top_of_same_controller
                                        (D := D) (t := CTime.toTime (l p hst))
                                        (t' := CTime.toTime sct')
                                        (s := CTime.toTime (CTime.node p y hy n))
                                        (s' := CTime.toTime sct') rfl rfl rfl
                                        (by simpa [CTime.toTime] using hsource)
                                      simpa [hr, attest_self_time (CTime.toTime sct')]
                                        using hraw
                                    have hviewTop :
                                        Attests D
                                          (CTime.toTime (CTime.viewsUpdate l hst r p hst))
                                          (CTime.toTime (CTime.botViewsWith hst sct' p hst))
                                          (top D p) := by
                                      have htopEq :
                                          attest
                                            (CTime.toTime (CTime.viewsUpdate l hst r p hst))
                                            (CTime.toTime
                                              (CTime.botViewsWith hst sct' p hst)) =
                                            top D p := by
                                        simpa [CTime.viewsUpdate_same, CTime.botViewsWith_same]
                                          using hviewEq
                                      have hg := Attests.attest_graph (D := D)
                                        (CTime.toTime (CTime.viewsUpdate l hst r p hst))
                                        (CTime.toTime (CTime.botViewsWith hst sct' p hst))
                                      rwa [htopEq] at hg
                                    simpa [top, Time.controller, CTime.toTime, CTime.crossBotNode]
                                      using
                                        attest_node_same_view_top_clause (D := D) (j := j)
                                          (k := p) (x := x) (y := D.semilattice.bot) (hx := hx)
                                          (hy := CTime.botX_consistent D)
                                          (l := CTime.viewsUpdate l hst r)
                                          (m := CTime.botViewsWith hst sct') hst hviewTop
                          | node p' x' hx' m =>
                              rename_i j p
                              simp [Time.controller] at hts
                              have hst := Ne.symm hts
                              have hsource :
                                  attest (CTime.toTime sct) (CTime.toTime sct') =
                                    top D p := by
                                simpa [CTime.toTime, Time.controller] using hcontr
                              cases sct with
                              | bot _ =>
                                  have hleft :
                                      attest (bot D p) (CTime.toTime sct') =
                                        CTime.toTime sct' :=
                                    attest_bot_left_same_controller p (CTime.toTime sct') rfl
                                  have htop_sct' : CTime.toTime sct' = top D p := by
                                    calc
                                      CTime.toTime sct' =
                                          attest (bot D p) (CTime.toTime sct') := hleft.symm
                                      _ = top D p := by
                                        simpa [bot, CTime.toTime] using hsource
                                  cases htop_sct'
                              | node _ y hy n =>
                                  cases sct' with
                                  | bot _ =>
                                      have hright :
                                          attest (CTime.toTime (CTime.node p y hy n)) (bot D p) =
                                            CTime.toTime (CTime.node p y hy n) :=
                                        attest_bot_right_same_controller p
                                          (CTime.toTime (CTime.node p y hy n)) rfl
                                      have htop_sct : CTime.toTime (CTime.node p y hy n) =
                                          top D p := by
                                        calc
                                          CTime.toTime (CTime.node p y hy n) =
                                              attest (CTime.toTime (CTime.node p y hy n))
                                                (bot D p) := hright.symm
                                          _ = top D p := by
                                            simpa [bot, CTime.toTime] using hsource
                                      cases htop_sct
                                  | node _ z hz o =>
                                      by_cases htopL :
                                          (attestAtCTime (l p hst)
                                            (CTime.toTime (CTime.node p y hy n))).1 =
                                            Time.top p
                                      · have hviewTopL :
                                            Attests D (CTime.toTime (l p hst))
                                              (CTime.toTime (CTime.node p y hy n))
                                              (top D p) := by
                                          have htopEq :
                                              attest (CTime.toTime (l p hst))
                                                (CTime.toTime (CTime.node p y hy n)) =
                                                top D p := by
                                            simpa [attest_ctime_eq, CTime.toTime, top]
                                              using htopL
                                          have hg := Attests.attest_graph (D := D)
                                            (CTime.toTime (l p hst))
                                            (CTime.toTime (CTime.node p y hy n))
                                          rwa [htopEq] at hg
                                        have hfirst :=
                                          attest_node_cross_top_clause (D := D) (j := j)
                                            (i := p) (x := x) (y := y) (hx := hx) (hy := hy)
                                            (l := l) (m := n) hst hviewTopL
                                        have hfirst' :
                                            attest (Time.consistent (CTime.node j x hx l))
                                                (Time.consistent (CTime.node p y hy n)) =
                                              top D j := by
                                          simpa [CTime.toTime] using hfirst
                                        rw [hfirst']
                                        exact attest_left_top_clause j
                                          (attest (Time.consistent (CTime.node j x' hx' m))
                                            (Time.consistent (CTime.node p z hz o)))
                                      · let rL : CTime D p :=
                                          Time.toCTimeOfNonTop
                                            (attestAtCTime (l p hst)
                                              (CTime.toTime (CTime.node p y hy n))) htopL
                                        have hrL :
                                            CTime.toTime rL =
                                              attest (CTime.toTime (l p hst))
                                                (CTime.toTime (CTime.node p y hy n)) := by
                                          calc
                                            CTime.toTime rL =
                                                (attestAtCTime (l p hst)
                                                  (CTime.toTime (CTime.node p y hy n))).1 := by
                                              exact Time.toCTimeOfNonTop_toTime
                                                (attestAtCTime (l p hst)
                                                  (CTime.toTime (CTime.node p y hy n))) htopL
                                            _ = attest (CTime.toTime (l p hst))
                                                (CTime.toTime (CTime.node p y hy n)) := by
                                              exact (attest_ctime_eq (l p hst)
                                                (CTime.toTime (CTime.node p y hy n))).symm
                                        have hviewRL :
                                            Attests D (CTime.toTime (l p hst))
                                              (CTime.toTime (CTime.node p y hy n))
                                              (CTime.toTime rL) := by
                                          have hg := Attests.attest_graph (D := D)
                                            (CTime.toTime (l p hst))
                                            (CTime.toTime (CTime.node p y hy n))
                                          rw [← hrL] at hg
                                          exact hg
                                        have hfirst :=
                                          attest_node_cross_consistent_clause (D := D) (j := j)
                                            (i := p) (x := x) (y := y) (hx := hx) (hy := hy)
                                            (l := l) (m := n) hst hviewRL
                                        have hfirst' :
                                            attest (Time.consistent (CTime.node j x hx l))
                                                (Time.consistent (CTime.node p y hy n)) =
                                              CTime.toTime (CTime.node j x hx
                                                (CTime.viewsUpdate l hst rL)) := by
                                          simpa [CTime.toTime] using hfirst
                                        rw [hfirst']
                                        by_cases htopR :
                                            (attestAtCTime (m p hst)
                                              (CTime.toTime (CTime.node p z hz o))).1 =
                                              Time.top p
                                        · have hviewTopR :
                                              Attests D (CTime.toTime (m p hst))
                                                (CTime.toTime (CTime.node p z hz o))
                                                (top D p) := by
                                            have htopEq :
                                                attest (CTime.toTime (m p hst))
                                                  (CTime.toTime (CTime.node p z hz o)) =
                                                  top D p := by
                                              simpa [attest_ctime_eq, CTime.toTime, top]
                                                using htopR
                                            have hg := Attests.attest_graph (D := D)
                                              (CTime.toTime (m p hst))
                                              (CTime.toTime (CTime.node p z hz o))
                                            rwa [htopEq] at hg
                                          have hsecond :=
                                            attest_node_cross_top_clause (D := D) (j := j)
                                              (i := p) (x := x') (y := z) (hx := hx') (hy := hz)
                                              (l := m) (m := o) hst hviewTopR
                                          have hsecond' :
                                              attest (Time.consistent (CTime.node j x' hx' m))
                                                  (Time.consistent (CTime.node p z hz o)) =
                                                top D j := by
                                            simpa [CTime.toTime] using hsecond
                                          rw [hsecond']
                                          simpa [top, Time.controller, CTime.toTime]
                                            using
                                              attest_right_top_clause
                                                (CTime.toTime
                                                  (CTime.node j x hx
                                                    (CTime.viewsUpdate l hst rL))) j
                                        · let rR : CTime D p :=
                                            Time.toCTimeOfNonTop
                                              (attestAtCTime (m p hst)
                                                (CTime.toTime (CTime.node p z hz o))) htopR
                                          have hrR :
                                              CTime.toTime rR =
                                                attest (CTime.toTime (m p hst))
                                                  (CTime.toTime (CTime.node p z hz o)) := by
                                            calc
                                              CTime.toTime rR =
                                                  (attestAtCTime (m p hst)
                                                    (CTime.toTime (CTime.node p z hz o))).1 := by
                                                exact Time.toCTimeOfNonTop_toTime
                                                  (attestAtCTime (m p hst)
                                                    (CTime.toTime (CTime.node p z hz o))) htopR
                                              _ = attest (CTime.toTime (m p hst))
                                                  (CTime.toTime (CTime.node p z hz o)) := by
                                                exact (attest_ctime_eq (m p hst)
                                                  (CTime.toTime (CTime.node p z hz o))).symm
                                          have hviewRR :
                                              Attests D (CTime.toTime (m p hst))
                                                (CTime.toTime (CTime.node p z hz o))
                                                (CTime.toTime rR) := by
                                            have hg := Attests.attest_graph (D := D)
                                              (CTime.toTime (m p hst))
                                              (CTime.toTime (CTime.node p z hz o))
                                            rw [← hrR] at hg
                                            exact hg
                                          have hsecond :=
                                            attest_node_cross_consistent_clause (D := D)
                                              (j := j) (i := p) (x := x') (y := z)
                                              (hx := hx') (hy := hz) (l := m) (m := o)
                                              hst hviewRR
                                          have hsecond' :
                                              attest (Time.consistent (CTime.node j x' hx' m))
                                                  (Time.consistent (CTime.node p z hz o)) =
                                                CTime.toTime (CTime.node j x' hx'
                                                  (CTime.viewsUpdate m hst rR)) := by
                                            simpa [CTime.toTime] using hsecond
                                          rw [hsecond']
                                          have hviewEq :
                                              attest (CTime.toTime rL) (CTime.toTime rR) =
                                                top D p := by
                                            have hraw := attest_contradiction_top_of_same_controller
                                              (D := D) (t := CTime.toTime (l p hst))
                                              (t' := CTime.toTime (m p hst))
                                              (s := CTime.toTime (CTime.node p y hy n))
                                              (s' := CTime.toTime (CTime.node p z hz o))
                                              rfl rfl rfl
                                              (by simpa [CTime.toTime] using hsource)
                                            simpa [hrL, hrR] using hraw
                                          have hviewTop :
                                              Attests D
                                                (CTime.toTime
                                                  (CTime.viewsUpdate l hst rL p hst))
                                                (CTime.toTime
                                                  (CTime.viewsUpdate m hst rR p hst))
                                                (top D p) := by
                                            have htopEq :
                                                attest
                                                  (CTime.toTime
                                                    (CTime.viewsUpdate l hst rL p hst))
                                                  (CTime.toTime
                                                    (CTime.viewsUpdate m hst rR p hst)) =
                                                  top D p := by
                                              simpa [CTime.viewsUpdate_same]
                                                using hviewEq
                                            have hg := Attests.attest_graph (D := D)
                                              (CTime.toTime (CTime.viewsUpdate l hst rL p hst))
                                              (CTime.toTime (CTime.viewsUpdate m hst rR p hst))
                                            rwa [htopEq] at hg
                                          simpa [top, Time.controller, CTime.toTime]
                                            using
                                              attest_node_same_view_top_clause (D := D)
                                                (j := j) (k := p) (x := x) (y := x')
                                                (hx := hx) (hy := hx')
                                                (l := CTime.viewsUpdate l hst rL)
                                                (m := CTime.viewsUpdate m hst rR)
                                                hst hviewTop

/-- Proposition 3.4.5: contradiction preservation for the deterministic attestation. -/
theorem attest_contradiction_preserving {D : LocalStateData.{u}} {t t' s s' : Time D}
    (htt' : Time.controller t = Time.controller t')
    (hss' : Time.controller s = Time.controller s')
    (hcontr : RawContradicts Time.controller attest (top D) s s') :
    RawContradicts Time.controller attest (top D) (attest t s) (attest t' s') := by
  exact attest_contradiction_preserving_of_top htt' hss' hcontr.2

/-- Proposition 3.4.5: the located semilattice L of Definition 3.4.3. -/
noncomputable def locatedSemilattice (D : LocalStateData.{u}) :
    LocatedSemilattice (Time D) D.Ctrl where
  attest := attest
  controller := Time.controller
  bot := bot D
  top := top D
  bot_controller := bot_controller D
  top_controller := top_controller D
  controller_preserving := attest_controller
  self_join_idem := attest_self_time
  self_join_comm := by
    intro _t _t' hctrl
    exact attest_comm_of_same_controller hctrl
  self_join_assoc := by
    intro _t _t' _u htt' ht'u
    exact attest_assoc_of_same_controller htt' ht'u
  self_bot_le := by
    intro p t hctrl
    exact attest_bot_left_same_controller p t hctrl
  self_le_top := by
    intro p t hctrl
    exact attest_top_right_same_controller p t hctrl
  expansive := attest_expansive
  contradiction_preserving := by
    intro _t _t' _s _s' htt' hss' hcontr
    exact attest_contradiction_preserving htt' hss' hcontr

/-- Proposition 3.4.5: the packaged attestation is the deterministic figure function. -/
theorem locatedSemilattice_attest (D : LocalStateData.{u}) (t s : Time D) :
    (locatedSemilattice D).attest t s = attest t s := by
  rfl

/-- Proposition 3.4.5: the packaged controller map is the time controller. -/
theorem locatedSemilattice_controller (D : LocalStateData.{u}) (t : Time D) :
    (locatedSemilattice D).controller t = Time.controller t := by
  rfl

/-- Proposition 3.4.5: the packaged bottom time is `bot_j`. -/
theorem locatedSemilattice_bot (D : LocalStateData.{u}) (j : D.Ctrl) :
    (locatedSemilattice D).bot j = bot D j := by
  rfl

/-- Proposition 3.4.5: the packaged top time is `top_j`. -/
theorem locatedSemilattice_top (D : LocalStateData.{u}) (j : D.Ctrl) :
    (locatedSemilattice D).top j = top D j := by
  rfl

/--
Proposition 3.4.5: order in the packaged located semilattice is exactly
the deterministic attestation order.
-/
theorem locatedSemilattice_le_iff (D : LocalStateData.{u}) (t s : Time D) :
    (locatedSemilattice D).le t s ↔
      Time.controller t = Time.controller s ∧ attest t s = s := by
  rfl

/--
Proposition 3.4.5: consistency in the packaged located semilattice is
exactly non-topness.
-/
theorem locatedSemilattice_consistentTime_iff (D : LocalStateData.{u}) (t : Time D) :
    (locatedSemilattice D).ConsistentTime t ↔ Time.Consistent t := by
  rfl

/--
Proposition 3.4.5: if a node is below another node, then each lower stored view slot is
below the corresponding upper stored view slot.
-/
theorem locatedSemilattice_node_view_le_of_node_le
    {D : LocalStateData.{u}} {j i : D.Ctrl} (hij : i ≠ j)
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {views views' : (k : D.Ctrl) → k ≠ j → CTime D k}
    (hle :
      (locatedSemilattice D).le
        (CTime.toTime (CTime.node j y hy views'))
        (CTime.toTime (CTime.node j x hx views))) :
    (locatedSemilattice D).le
      (CTime.toTime (views' i hij)) (CTime.toTime (views i hij)) := by
  constructor
  · rfl
  · by_cases hlocal : D.semilattice.join y x = D.semilattice.top
    · have htop_eq :
          top D j = CTime.toTime (CTime.node j x hx views) := by
        have hout :
            attest
              (CTime.toTime (CTime.node j y hy views'))
              (CTime.toTime (CTime.node j x hx views)) = top D j :=
          attest_node_same_local_top_clause (D := D) (j := j)
            (x := y) (y := x) (hx := hy) (hy := hx)
            (l := views') (m := views) hlocal
        calc
          top D j =
              attest
                (CTime.toTime (CTime.node j y hy views'))
                (CTime.toTime (CTime.node j x hx views)) := hout.symm
          _ = CTime.toTime (CTime.node j x hx views) := hle.2
      cases htop_eq
    ·
      by_cases hview :
          ∃ (k : D.Ctrl) (hkj : k ≠ j),
            (attestAtCTime (views' k hkj) (CTime.toTime (views k hkj))).1 =
              Time.top k
      · have htop_eq :
            top D j = CTime.toTime (CTime.node j x hx views) := by
          rcases hview with ⟨k, hkj, hk_top⟩
          have hviewTop :
              Attests D (CTime.toTime (views' k hkj)) (CTime.toTime (views k hkj))
                (top D k) := by
            have htopEq :
                attest (CTime.toTime (views' k hkj)) (CTime.toTime (views k hkj)) =
                  top D k := by
              simpa [attest_ctime_eq, top] using hk_top
            have hgraph := Attests.attest_graph (D := D)
              (CTime.toTime (views' k hkj)) (CTime.toTime (views k hkj))
            rwa [htopEq] at hgraph
          have hout :
              attest
                (CTime.toTime (CTime.node j y hy views'))
                (CTime.toTime (CTime.node j x hx views)) = top D j :=
            attest_node_same_view_top_clause (D := D) (j := j) (k := k)
              (x := y) (y := x) (hx := hy) (hy := hx) (l := views') (m := views)
              hkj hviewTop
          calc
            top D j =
                attest
                  (CTime.toTime (CTime.node j y hy views'))
                  (CTime.toTime (CTime.node j x hx views)) := hout.symm
            _ = CTime.toTime (CTime.node j x hx views) := hle.2
        cases htop_eq
      · let updated : (k : D.Ctrl) → k ≠ j → CTime D k :=
          fun k hkj =>
            Time.toCTimeOfNonTop
              (attestAtCTime (views' k hkj) (CTime.toTime (views k hkj)))
              (by
                intro htop
                exact hview ⟨k, hkj, htop⟩)
        have hnode :
          CTime.toTime (CTime.node j (D.semilattice.join y x) hlocal updated) =
              CTime.toTime (CTime.node j x hx views) := by
          have hviews :
              ∀ k hkj,
                Attests D (CTime.toTime (views' k hkj)) (CTime.toTime (views k hkj))
                  (CTime.toTime (updated k hkj)) := by
            intro k hkj
            have hupdated :
                CTime.toTime (updated k hkj) =
                  attest (CTime.toTime (views' k hkj)) (CTime.toTime (views k hkj)) := by
              calc
                CTime.toTime (updated k hkj) =
                    (attestAtCTime (views' k hkj) (CTime.toTime (views k hkj))).1 := by
                  exact Time.toCTimeOfNonTop_toTime
                    (attestAtCTime (views' k hkj) (CTime.toTime (views k hkj)))
                    (by
                      intro htop
                      exact hview ⟨k, hkj, htop⟩)
                _ = attest (CTime.toTime (views' k hkj)) (CTime.toTime (views k hkj)) := by
                  exact (attest_ctime_eq (views' k hkj)
                    (CTime.toTime (views k hkj))).symm
            have hgraph := Attests.attest_graph (D := D)
              (CTime.toTime (views' k hkj)) (CTime.toTime (views k hkj))
            rw [← hupdated] at hgraph
            exact hgraph
          have hraw :
              CTime.toTime (CTime.node j (D.semilattice.join y x) hlocal updated) =
                CTime.toTime (CTime.node j x hx views) := by
            have hout :
                attest
                  (CTime.toTime (CTime.node j y hy views'))
                  (CTime.toTime (CTime.node j x hx views)) =
                    CTime.toTime (CTime.node j (D.semilattice.join y x) hlocal updated) :=
              attest_node_same_consistent_clause (D := D) (j := j)
                (x := y) (y := x) (hx := hy) (hy := hx)
                (l := views') (m := views) (r := updated) hlocal hviews
            exact hout.symm.trans hle.2
          exact hraw
        have hslot : updated i hij = views i hij :=
          CTime.node_views_eq_of_toTime_eq_any hnode i hij
        have hupdated :
            CTime.toTime (updated i hij) =
              attest (CTime.toTime (views' i hij)) (CTime.toTime (views i hij)) := by
          calc
            CTime.toTime (updated i hij) =
                (attestAtCTime (views' i hij) (CTime.toTime (views i hij))).1 := by
              exact Time.toCTimeOfNonTop_toTime
                (attestAtCTime (views' i hij) (CTime.toTime (views i hij)))
                (by
                  intro htop
                  exact hview ⟨i, hij, htop⟩)
            _ = attest (CTime.toTime (views' i hij)) (CTime.toTime (views i hij)) := by
              exact (attest_ctime_eq (views' i hij) (CTime.toTime (views i hij))).symm
        exact hupdated.symm.trans (congrArg CTime.toTime hslot)

/--
Proposition 3.4.5: attesting a node to the time already stored in a cross-controller view
slot leaves the node unchanged.
-/
theorem locatedSemilattice_cross_node_attest_stored_view_eq_self
    {D : LocalStateData.{u}} {j i : D.Ctrl} (hij : i ≠ j)
    {x : D.X} {hx : D.semilattice.Consistent x}
    {views : (k : D.Ctrl) → k ≠ j → CTime D k} :
    attest (CTime.toTime (CTime.node j x hx views))
        (CTime.toTime (views i hij)) =
      CTime.toTime (CTime.node j x hx views) := by
  cases hslot : views i hij with
  | bot i =>
      simpa [bot] using
        (attest_right_bot_clause (D := D)
          (CTime.toTime (CTime.node j x hx views)) i (by
            intro h
            cases h))
  | node i y hy targetViews =>
      have hviewSelf :
          Attests D
            (CTime.toTime (CTime.node i y hy targetViews))
            (CTime.toTime (CTime.node i y hy targetViews))
            (CTime.toTime (CTime.node i y hy targetViews)) :=
        Attests.self_ctime (CTime.node i y hy targetViews)
      have hview :
          Attests D
            (CTime.toTime (views i hij))
            (CTime.toTime (CTime.node i y hy targetViews))
            (CTime.toTime (CTime.node i y hy targetViews)) := by
        rwa [hslot]
      have hfirst :
          attest (CTime.toTime (CTime.node j x hx views))
              (CTime.toTime (CTime.node i y hy targetViews)) =
            CTime.toTime
              (CTime.node j x hx
                (CTime.viewsUpdate views hij (CTime.node i y hy targetViews))) :=
        attest_node_cross_consistent_clause (D := D) (j := j) (i := i)
          (x := x) (y := y) (hx := hx) (hy := hy)
          (l := views) (m := targetViews) hij hview
      have hviews :
          CTime.viewsUpdate views hij (CTime.node i y hy targetViews) = views := by
        funext k hk
        by_cases hki : k = i
        · subst k
          simp [hslot]
        · exact CTime.viewsUpdate_ne views hij hk (CTime.node i y hy targetViews) hki
      calc
        attest (CTime.toTime (CTime.node j x hx views))
            (CTime.toTime (CTime.node i y hy targetViews)) =
          CTime.toTime
            (CTime.node j x hx
              (CTime.viewsUpdate views hij (CTime.node i y hy targetViews))) := hfirst
        _ = CTime.toTime (CTime.node j x hx views) := by rw [hviews]

theorem locatedSemilattice_cross_node_attest_stored_view_le_self
    {D : LocalStateData.{u}} {j i : D.Ctrl} (hij : i ≠ j)
    {x : D.X} {hx : D.semilattice.Consistent x}
    {views : (k : D.Ctrl) → k ≠ j → CTime D k} :
    (locatedSemilattice D).le
      ((locatedSemilattice D).attest
        (CTime.toTime (CTime.node j x hx views)) (CTime.toTime (views i hij)))
      (CTime.toTime (CTime.node j x hx views)) := by
  have hself := locatedSemilattice_cross_node_attest_stored_view_eq_self
    (D := D) (j := j) (i := i) hij (x := x) (hx := hx) (views := views)
  simpa [locatedSemilattice, hself] using
    ((locatedSemilattice D).le_refl (CTime.toTime (CTime.node j x hx views)))

/--
If a `j`-controlled input attests to an `i`-controlled time and the result is below a
`j`-node, then the target time is below the node's stored `i`-view.
-/
theorem locatedSemilattice_attest_le_node_stored_view_of_controller
    {D : LocalStateData.{u}} {j i : D.Ctrl} (hij : i ≠ j)
    {x : D.X} {hx : D.semilattice.Consistent x}
    {views : (k : D.Ctrl) → k ≠ j → CTime D k}
    {r s : Time D}
    (hctrlr : Time.controller r = j) (hctrls : Time.controller s = i)
    (hle :
      (locatedSemilattice D).le
        ((locatedSemilattice D).attest r s)
        (CTime.toTime (CTime.node j x hx views))) :
    (locatedSemilattice D).le s (CTime.toTime (views i hij)) := by
  let target := CTime.toTime (CTime.node j x hx views)
  have htop_not_le_target : ¬ (locatedSemilattice D).le (top D j) target := by
    intro htop_le
    have htop_eq : top D j = target := by
      calc
        top D j = attest (top D j) target :=
          (attest_left_top_clause (D := D) j target).symm
        _ = target := htop_le.2
    dsimp [target] at htop_eq
    cases htop_eq
  cases r with
  | top rj =>
      simp [Time.controller] at hctrlr
      cases hctrlr
      have hfirst :
          (locatedSemilattice D).attest (top D j) s = top D j := by
        simpa [locatedSemilattice] using attest_left_top_clause (D := D) j s
      exact False.elim (htop_not_le_target (by simpa [target, hfirst] using hle))
  | consistent rct =>
      simp [Time.controller] at hctrlr
      cases hctrlr
      cases rct with
      | bot j =>
          cases s with
          | top si =>
              simp [Time.controller] at hctrls
              cases hctrls
              have hfirst :
                  (locatedSemilattice D).attest (bot D j) (top D i) = top D j := by
                simpa [locatedSemilattice, bot] using
                  attest_left_bot_cross_top_clause (D := D) hij
              exact False.elim (htop_not_le_target (by simpa [target, hfirst] using hle))
          | consistent sct =>
              simp [Time.controller] at hctrls
              cases hctrls
              cases sct with
              | bot i =>
                  simpa [locatedSemilattice, LocatedSemilattice.botTime, bot] using
                    ((locatedSemilattice D).botTime_le
                      (p := i) (t := CTime.toTime (views i hij)) rfl)
              | node i y hy targetViews =>
                  have hfirst :
                      (locatedSemilattice D).attest (bot D j)
                          (CTime.toTime (CTime.node i y hy targetViews)) =
                        CTime.toTime
                          (CTime.crossBotNode j i hij
                            (CTime.node i y hy targetViews)) := by
                    simpa [locatedSemilattice, bot] using
                      attest_left_bot_cross_clause (D := D) hij
                        (CTime.node i y hy targetViews)
                  have hnode_le :
                      (locatedSemilattice D).le
                        (CTime.toTime
                          (CTime.crossBotNode j i hij
                            (CTime.node i y hy targetViews)))
                        target := by
                    have hle' :
                        (locatedSemilattice D).le
                          ((locatedSemilattice D).attest (bot D j)
                            (CTime.toTime (CTime.node i y hy targetViews)))
                          target := by
                      simpa [target, bot] using hle
                    rwa [hfirst] at hle'
                  have hslot_le :
                      (locatedSemilattice D).le
                        (CTime.toTime
                          (CTime.botViewsWith hij
                            (CTime.node i y hy targetViews) i hij))
                        (CTime.toTime (views i hij)) :=
                    locatedSemilattice_node_view_le_of_node_le
                      (D := D) (j := j) (i := i) hij
                      (x := x) (y := D.semilattice.bot) (hx := hx)
                      (hy := CTime.botX_consistent D) (views := views)
                      (views' := CTime.botViewsWith hij
                        (CTime.node i y hy targetViews)) hnode_le
                  simpa [CTime.botViewsWith_same] using hslot_le
      | node j y hy rviews =>
          cases s with
          | top si =>
              simp [Time.controller] at hctrls
              cases hctrls
              have hfirst :
                  (locatedSemilattice D).attest
                      (CTime.toTime (CTime.node j y hy rviews)) (top D i) =
                    top D j := by
                simpa [locatedSemilattice, top, Time.controller, CTime.toTime] using
                  attest_right_top_clause (D := D)
                    (CTime.toTime (CTime.node j y hy rviews)) i
              exact False.elim (htop_not_le_target (by simpa [target, hfirst] using hle))
          | consistent sct =>
              simp [Time.controller] at hctrls
              cases hctrls
              cases sct with
              | bot i =>
                  simpa [locatedSemilattice, LocatedSemilattice.botTime, bot] using
                    ((locatedSemilattice D).botTime_le
                      (p := i) (t := CTime.toTime (views i hij)) rfl)
              | node i z hz targetViews =>
                  by_cases htop :
                      (attestAtCTime (rviews i hij)
                        (CTime.toTime (CTime.node i z hz targetViews))).1 =
                        Time.top i
                  · have hviewTop :
                        Attests D (CTime.toTime (rviews i hij))
                          (CTime.toTime (CTime.node i z hz targetViews)) (top D i) := by
                      have htopEq :
                          attest (CTime.toTime (rviews i hij))
                              (CTime.toTime (CTime.node i z hz targetViews)) =
                            top D i := by
                        simpa [attest_ctime_eq, top] using htop
                      have hgraph := Attests.attest_graph (D := D)
                        (CTime.toTime (rviews i hij))
                        (CTime.toTime (CTime.node i z hz targetViews))
                      rwa [htopEq] at hgraph
                    have hfirst :
                        (locatedSemilattice D).attest
                            (CTime.toTime (CTime.node j y hy rviews))
                            (CTime.toTime (CTime.node i z hz targetViews)) =
                          top D j := by
                      simpa [locatedSemilattice] using
                        attest_node_cross_top_clause (D := D) (j := j) (i := i)
                          (x := y) (y := z) (hx := hy) (hy := hz)
                          (l := rviews) (m := targetViews) hij hviewTop
                    exact False.elim
                      (htop_not_le_target (by
                        have hle' :
                            (locatedSemilattice D).le
                              ((locatedSemilattice D).attest
                                (CTime.toTime (CTime.node j y hy rviews))
                                (CTime.toTime (CTime.node i z hz targetViews)))
                              target := by
                          simpa [target] using hle
                        rwa [hfirst] at hle'))
                  · let updated : CTime D i :=
                      Time.toCTimeOfNonTop
                        (attestAtCTime (rviews i hij)
                          (CTime.toTime (CTime.node i z hz targetViews))) htop
                    have hupdated_toTime :
                        CTime.toTime updated =
                          attest (CTime.toTime (rviews i hij))
                            (CTime.toTime (CTime.node i z hz targetViews)) := by
                      calc
                        CTime.toTime updated =
                            (attestAtCTime (rviews i hij)
                              (CTime.toTime (CTime.node i z hz targetViews))).1 := by
                          exact Time.toCTimeOfNonTop_toTime
                            (attestAtCTime (rviews i hij)
                              (CTime.toTime (CTime.node i z hz targetViews))) htop
                        _ = attest (CTime.toTime (rviews i hij))
                            (CTime.toTime (CTime.node i z hz targetViews)) := by
                          exact (attest_ctime_eq (rviews i hij)
                            (CTime.toTime (CTime.node i z hz targetViews))).symm
                    have hviewR :
                        Attests D (CTime.toTime (rviews i hij))
                          (CTime.toTime (CTime.node i z hz targetViews))
                          (CTime.toTime updated) := by
                      have hgraph := Attests.attest_graph (D := D)
                        (CTime.toTime (rviews i hij))
                        (CTime.toTime (CTime.node i z hz targetViews))
                      rw [← hupdated_toTime] at hgraph
                      exact hgraph
                    have hfirst :
                        (locatedSemilattice D).attest
                            (CTime.toTime (CTime.node j y hy rviews))
                            (CTime.toTime (CTime.node i z hz targetViews)) =
                          CTime.toTime
                            (CTime.node j y hy (CTime.viewsUpdate rviews hij updated)) := by
                      simpa [locatedSemilattice] using
                        attest_node_cross_consistent_clause (D := D) (j := j) (i := i)
                          (x := y) (y := z) (hx := hy) (hy := hz)
                          (l := rviews) (m := targetViews) hij hviewR
                    have hnode_le :
                        (locatedSemilattice D).le
                          (CTime.toTime
                            (CTime.node j y hy (CTime.viewsUpdate rviews hij updated)))
                          target := by
                      have hle' :
                          (locatedSemilattice D).le
                            ((locatedSemilattice D).attest
                              (CTime.toTime (CTime.node j y hy rviews))
                              (CTime.toTime (CTime.node i z hz targetViews)))
                            target := by
                        simpa [target] using hle
                      rwa [hfirst] at hle'
                    have hslot_le :
                        (locatedSemilattice D).le
                          (CTime.toTime updated) (CTime.toTime (views i hij)) := by
                      simpa [CTime.viewsUpdate_same] using
                        (locatedSemilattice_node_view_le_of_node_le
                          (D := D) (j := j) (i := i) hij
                          (x := x) (y := y) (hx := hx) (hy := hy)
                          (views := views)
                          (views' := CTime.viewsUpdate rviews hij updated) hnode_le)
                    have htarget_le_updated :
                        (locatedSemilattice D).le
                          (CTime.toTime (CTime.node i z hz targetViews))
                          (CTime.toTime updated) := by
                      have hright :=
                        (locatedSemilattice D).le_right_attest_of_same_controller
                          (t := CTime.toTime (rviews i hij))
                          (s := CTime.toTime (CTime.node i z hz targetViews)) rfl
                      simpa [locatedSemilattice, hupdated_toTime] using hright
                    exact (locatedSemilattice D).le_trans htarget_le_updated hslot_le

end LocalStateData

end ConsistentHistories.Models.Cut.InductiveConstruction
