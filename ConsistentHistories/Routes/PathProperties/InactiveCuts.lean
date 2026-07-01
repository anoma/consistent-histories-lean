import ConsistentHistories.Routes.PathProperties.FlagNesting

/-!
Paper section 5.3: Inactive if and only if Cut.

-/

namespace ConsistentHistories.Routes.PathProperties.InactiveCuts

open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.Cut.Flags
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Routes.Paths.Circuits
open ConsistentHistories.Foundation.Paths.InitialPrefixes
open ConsistentHistories.Routes.PathProperties.FlagNesting
open ConsistentHistories.Routes.PathProperties.CutmePersistence

universe u v

/-- The upper endpoint of a final Cut has the new `nextIndex` label. -/
theorem final_cut_upper_has_nextIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    HasCutLabelAt Time (T.paperIndex i)
      ((Derivation.root (Derivation.cut deriv hij hjk hk hj hi hconsistent)).get k) := by
  exact ⟨CutFlagKind.nextIndex, tk, by
    simp [Derivation.root, Prepath.replace_get_same, Prepath.paperIndex,
      LocatedSemilatticeWithCut.nextIndex]⟩

/-- The center of a final Cut keeps the `cutMe` label aimed at the lower endpoint. -/
theorem final_cut_center_has_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    HasCutLabelAt Time (T.paperIndex i)
      ((Derivation.root (Derivation.cut deriv hij hjk hk hj hi hconsistent)).get j) := by
  have hj_ne_k : j ≠ k := by
    intro h
    cases h
    exact Nat.lt_irrefl j.val hjk
  exact
    ⟨CutFlagKind.cutMe, tj # (⋉ (T.paperIndex j) tk), by
      simp [Derivation.root, Prepath.replace_get_ne T hj_ne_k, hj,
        LocatedSemilatticeWithCut.cutMe]⟩

/-- The lower endpoint of a final Cut is an attestation to the Cut center. -/
theorem final_cut_lower_eq_attest_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    ((Derivation.root (Derivation.cut deriv hij hjk hk hj hi hconsistent)).get i) =
      ti # ((Derivation.root (Derivation.cut deriv hij hjk hk hj hi hconsistent)).get j) := by
  have hi_ne_k : i ≠ k := by
    intro h
    cases h
    exact Nat.lt_irrefl i.val (Nat.lt_trans hij hjk)
  have hj_ne_k : j ≠ k := by
    intro h
    cases h
    exact Nat.lt_irrefl j.val hjk
  simp [Derivation.root, Prepath.replace_get_ne T hi_ne_k,
    Prepath.replace_get_ne T hj_ne_k, hi, hj]

/--
Final-step case of Lemma 5.3.1: if the final derivation-step is `(Cut_{k,j,i})`,
then every index `m` bracketed by that Cut (`i < m < k`) is inactive in the
resulting root.
-/
theorem final_cut_brackets_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    {m : T.Index} (him : i.val < m.val) (hmk : m.val < k.val)
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).Inactive m := by
  exact
    ⟨k, i, him, hmk, CutFlagKind.nextIndex, tk, by
      simp [Prepath.replace_get_same, Prepath.paperIndex,
        LocatedSemilatticeWithCut.nextIndex]⟩

/--
Center-index case of Lemma 5.3.1: if the final derivation-step is
`(Cut_{k,j,i})`, then its center `j` is inactive in the resulting root.
-/
theorem final_cut_implies_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).Inactive j := by
  exact final_cut_brackets_inactive deriv hij hjk hij hjk hk hj hi hconsistent

/--
Lemma 5.3.1 (Cut implies inactive): if `(Cut_{k',j',i'}) ∈ Π` for some
`k', j', i' ∈ index(Π)` with `k' > j > i'` (that is, `j` is bracketed by some
Cut in `Π`), then `j` is inactive in `Π`.
-/
theorem containsCut_brackets_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat},
      ContainsCut deriv cutK cutJ cutI →
        ∀ {m : T.Index}, cutI < T.paperIndex m → T.paperIndex m < cutK →
          deriv.Inactive m := by
  intro T deriv cutK cutJ cutI hcut
  induction hcut with
  | here deriv hij hjk hk hj hi hconsistent =>
      intro m him hmk
      exact final_cut_brackets_inactive deriv hij hjk
        (Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using him))
        (Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hmk))
        hk hj hi hconsistent
  | inc h changed hlt hflag hconsistent ih =>
      intro m him hmk
      rename_i Tmid deriv cutK cutJ cutI tnew
      rcases ih (m := m) (by simpa [Prepath.paperIndex] using him)
          (by simpa [Prepath.paperIndex] using hmk) with
        ⟨upper, lower, hlowm, hmup, kind, base, hlabel⟩
      by_cases hsame : upper = changed
      · subst upper
        have hnew := hasCutLabel_transfer_of_flag_eq hlabel hflag
        exact ⟨changed, lower, hlowm, hmup, by
          simpa [Prepath.replace_get_same] using hnew⟩
      · exact ⟨upper, lower, hlowm, hmup, kind, base, by
          rw [Prepath.replace_get_ne Tmid hsame tnew hlt.1.1.symm hconsistent]
          exact hlabel⟩
  | cutMeIntro h changed introTarget hshape hconsistent ih =>
      intro m him hmk
      rename_i Tmid deriv cutK cutJ cutI baseNew
      rcases ih (m := m) (by simpa [Prepath.paperIndex] using him)
          (by simpa [Prepath.paperIndex] using hmk) with
        ⟨upper, lower, hlowm, hmup, kind, oldBase, hlabel⟩
      by_cases hsame : upper = changed
      · subst upper
        have hleft :
            ConsistentTime
              (cutting kind (Tmid.paperIndex lower) oldBase) := by
          rw [← hlabel]
          exact Tmid.consistent changed
        have hright :
            ConsistentTime (↱ introTarget baseNew) := by
          rw [← hshape]
          exact Tmid.consistent changed
        have htarget := flag_target_eq_of_eq_consistent hleft hright
          (hlabel.symm.trans hshape)
        exact
          ⟨changed, lower, hlowm, hmup, CutFlagKind.cutMe, baseNew, by
            subst introTarget
            simp only [Prepath.replace_get_same, Prepath.paperIndex]
            simp [LocatedSemilatticeWithCut.cutMe]⟩
      · exact
          ⟨upper, lower, hlowm, hmup, kind, oldBase, by
            rw [Prepath.replace_get_ne Tmid hsame
              (⋊ introTarget baseNew) _ hconsistent]
            exact hlabel⟩
  | cutYouIntro h changed introTarget hshape hconsistent ih =>
      intro m him hmk
      rename_i Tmid deriv cutK cutJ cutI baseNew
      rcases ih (m := m) (by simpa [Prepath.paperIndex] using him)
          (by simpa [Prepath.paperIndex] using hmk) with
        ⟨upper, lower, hlowm, hmup, kind, oldBase, hlabel⟩
      by_cases hsame : upper = changed
      · subst upper
        have hleft :
            ConsistentTime
              (cutting kind (Tmid.paperIndex lower) oldBase) := by
          rw [← hlabel]
          exact Tmid.consistent changed
        have hright :
            ConsistentTime (↱ introTarget baseNew) := by
          rw [← hshape]
          exact Tmid.consistent changed
        have htarget := flag_target_eq_of_eq_consistent hleft hright
          (hlabel.symm.trans hshape)
        exact
          ⟨changed, lower, hlowm, hmup, CutFlagKind.cutYou, baseNew, by
            subst introTarget
            simp only [Prepath.replace_get_same, Prepath.paperIndex]
            simp [LocatedSemilatticeWithCut.cutYou]⟩
      · exact
          ⟨upper, lower, hlowm, hmup, kind, oldBase, by
            rw [Prepath.replace_get_ne Tmid hsame
              (⋉ introTarget baseNew) _ hconsistent]
            exact hlabel⟩
  | cutStep h hij hjk hk hj hi hconsistent ih =>
      intro m him hmk
      rename_i Tmid deriv cutK cutJ cutI i j k ti tj tk
      rcases ih (m := m) (by simpa [Prepath.paperIndex] using him)
          (by simpa [Prepath.paperIndex] using hmk) with
        ⟨upper, lower, hlowm, hmup, kind, oldBase, hlabel⟩
      by_cases hsame : upper = k
      · subst upper
        have hleft :
            ConsistentTime
              (cutting kind (Tmid.paperIndex lower) oldBase) := by
          rw [← hlabel]
          exact Tmid.consistent k
        have hright :
            ConsistentTime (⋉ (Tmid.paperIndex j) tk) := by
          rw [← hk]
          exact Tmid.consistent k
        have htarget := flag_target_eq_of_eq_consistent hleft hright
          (hlabel.symm.trans hk)
        have hlow_eq_j : lower.val = j.val := by
          exact Nat.succ.inj (by simpa [Prepath.paperIndex] using htarget)
        have hj_lt_m : j.val < m.val := by
          simpa [hlow_eq_j] using hlowm
        exact
          ⟨k, i, Nat.lt_trans hij hj_lt_m, hmup, CutFlagKind.nextIndex, tk, by
            simp [Prepath.replace_get_same, Prepath.paperIndex,
              LocatedSemilatticeWithCut.nextIndex]⟩
      · exact
          ⟨upper, lower, hlowm, hmup, kind, oldBase, by
            rw [Prepath.replace_get_ne Tmid hsame
              (↱ (Tmid.paperIndex i) tk) _ hconsistent]
            exact hlabel⟩

/-- Center-index specialization of Lemma 5.3.1. -/
theorem containsCut_center_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) {center : T.Index}
    (hcenter : T.paperIndex center = cutJ) :
    deriv.Inactive center := by
  have horder := containsCut_order hcut
  exact containsCut_brackets_inactive hcut
    (by simpa [hcenter] using horder.1)
    (by simpa [hcenter] using horder.2)

theorem hasCutLabelAt_target_eq_of_eq_cutting {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {target target' : Nat} {t base : Time} {kind : CutFlagKind}
    (hlabel : HasCutLabelAt Time target t)
    (hshape : t = cutting kind target' base)
    (hconsistent : ConsistentTime t) :
    target = target' := by
  rcases hlabel with ⟨oldKind, oldBase, hold⟩
  have hleft : ConsistentTime (cutting oldKind target oldBase) := by
    rw [← hold]
    exact hconsistent
  have hright : ConsistentTime (cutting kind target' base) := by
    rw [← hshape]
    exact hconsistent
  exact flag_target_eq_of_eq_consistent hleft hright (hold.symm.trans hshape)

theorem hasCutLabelAt_transfer_back_of_flag_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (j : T.Index) {target : Nat} {kind : CutFlagKind} {base tnew : Time}
    (hlabel : tnew = cutting kind target base)
    (hconsistent : ConsistentTime tnew)
    (hflag :
      flagOf cuttingFlagSet (T.get j) =
        flagOf cuttingFlagSet tnew) :
    HasCutLabelAt Time target (T.get j) := by
  have hform_new : HasForm (cutting kind target) tnew :=
    ⟨hconsistent, ⟨base, hlabel⟩⟩
  have hform_old := flagOf_transfer_hasForm cuttingFlagSet
    (cutting_mem kind target) hform_new hflag.symm
  rcases hform_old.2 with ⟨oldBase, hold⟩
  exact ⟨kind, oldBase, hold⟩

/--
Lemma 5.3.2 (Jump implies Cut exists): if `Π[k] = Q_i⊖` for some
`i ∈ index(Π)` with `k ≥ i + 2`, then `(Cut_{k,j,i}) ∈ Π` for some
`j ∈ index(Π)` with `k > j > i`.
-/
theorem jump_implies_cut_exists {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T),
      ∀ {k i : T.Index},
        T.paperIndex i + 1 < T.paperIndex k →
          HasCutLabelAt Time (T.paperIndex i) (T.get k) →
            ∃ j : T.Index,
              T.paperIndex i < T.paperIndex j ∧
              T.paperIndex j < T.paperIndex k ∧
              ContainsCut deriv (T.paperIndex k) (T.paperIndex j) (T.paperIndex i) := by
  intro T deriv
  induction deriv with
  | init hpos base hconsistent =>
      intro k i hgap hlabel
      by_cases hkzero : k.val = 0
      · simp [Prepath.paperIndex, hkzero] at hgap
      · have hkshape : (initPrepath Time hpos base hconsistent).get k =
            ↱ k.val (base k) := by
          simp [initPrepath, initTime, Prepath.get, hkzero,
            LocatedSemilatticeWithCut.nextIndex]
        have htarget := hasCutLabelAt_target_eq_of_eq_cutting hlabel hkshape
          ((initPrepath Time hpos base hconsistent).consistent k)
        simp [Prepath.paperIndex] at htarget hgap
        omega
  | inc deriv changed hlt hflag hconsistent ih =>
      intro k i hgap hlabel
      rename_i Tmid tnew
      by_cases hkchanged : k = changed
      · subst k
        rcases hlabel with ⟨kind, base, hnew⟩
        have hnew_t : tnew = cutting kind (Tmid.paperIndex i) base := by
          simpa [Prepath.replace_get_same] using hnew
        have hold : HasCutLabelAt Time (Tmid.paperIndex i) (Tmid.get changed) :=
          hasCutLabelAt_transfer_back_of_flag_eq changed hnew_t hconsistent hflag
        rcases ih (k := changed) (i := i)
            (by simpa [Prepath.paperIndex] using hgap) hold with
          ⟨j, hij, hjk, hcut⟩
        exact ⟨j, by simpa [Prepath.paperIndex] using hij,
          by simpa [Prepath.paperIndex] using hjk,
          ContainsCut.inc hcut changed hlt hflag hconsistent⟩
      · have hold : HasCutLabelAt Time (Tmid.paperIndex i) (Tmid.get k) := by
          rcases hlabel with ⟨kind, base, hnew⟩
          exact ⟨kind, base, by
            have hget := Prepath.replace_get_ne Tmid hkchanged tnew hlt.1.1.symm hconsistent
            simpa [hget, Prepath.paperIndex] using hnew⟩
        rcases ih (k := k) (i := i)
            (by simpa [Prepath.paperIndex] using hgap) hold with
          ⟨j, hij, hjk, hcut⟩
        exact ⟨j, by simpa [Prepath.paperIndex] using hij,
          by simpa [Prepath.paperIndex] using hjk,
          ContainsCut.inc hcut changed hlt hflag hconsistent⟩
  | cutMeIntro deriv changed introTarget hshape hconsistent ih =>
      intro k i hgap hlabel
      rename_i Tmid baseNew
      by_cases hkchanged : k = changed
      · subst k
        have hnewshape :
            (Derivation.root
              (Derivation.cutMeIntro deriv changed introTarget hshape hconsistent)).get
              changed = ⋊ introTarget baseNew := by
          simp [Derivation.root, Prepath.replace_get_same]
        have htarget := hasCutLabelAt_target_eq_of_eq_cutting hlabel hnewshape
          ((Derivation.root
              (Derivation.cutMeIntro deriv changed introTarget hshape hconsistent)).consistent
            changed)
        have htarget_mid : Tmid.paperIndex i = introTarget := by
          simpa [Prepath.paperIndex] using htarget
        have hold : HasCutLabelAt Time (Tmid.paperIndex i) (Tmid.get changed) := by
          exact ⟨CutFlagKind.nextIndex, baseNew, by
            rw [htarget_mid]
            simpa [LocatedSemilatticeWithCut.nextIndex] using hshape⟩
        rcases ih (k := changed) (i := i)
            (by simpa [Prepath.paperIndex] using hgap) hold with
          ⟨j, hij, hjk, hcut⟩
        exact ⟨j, by simpa [Prepath.paperIndex] using hij,
          by simpa [Prepath.paperIndex] using hjk,
          ContainsCut.cutMeIntro hcut changed introTarget hshape hconsistent⟩
      · have hold : HasCutLabelAt Time (Tmid.paperIndex i) (Tmid.get k) := by
          rcases hlabel with ⟨kind, base, hnew⟩
          exact ⟨kind, base, by
            simpa [Prepath.replace_get_ne Tmid hkchanged, Prepath.paperIndex] using hnew⟩
        rcases ih (k := k) (i := i)
            (by simpa [Prepath.paperIndex] using hgap) hold with
          ⟨j, hij, hjk, hcut⟩
        exact ⟨j, by simpa [Prepath.paperIndex] using hij,
          by simpa [Prepath.paperIndex] using hjk,
          ContainsCut.cutMeIntro hcut changed introTarget hshape hconsistent⟩
  | cutYouIntro deriv changed introTarget hshape hconsistent ih =>
      intro k i hgap hlabel
      rename_i Tmid baseNew
      by_cases hkchanged : k = changed
      · subst k
        have hnewshape :
            (Derivation.root
              (Derivation.cutYouIntro deriv changed introTarget hshape hconsistent)).get
              changed = ⋉ introTarget baseNew := by
          simp [Derivation.root, Prepath.replace_get_same]
        have htarget := hasCutLabelAt_target_eq_of_eq_cutting hlabel hnewshape
          ((Derivation.root
              (Derivation.cutYouIntro deriv changed introTarget hshape hconsistent)).consistent
            changed)
        have htarget_mid : Tmid.paperIndex i = introTarget := by
          simpa [Prepath.paperIndex] using htarget
        have hold : HasCutLabelAt Time (Tmid.paperIndex i) (Tmid.get changed) := by
          exact ⟨CutFlagKind.nextIndex, baseNew, by
            rw [htarget_mid]
            simpa [LocatedSemilatticeWithCut.nextIndex] using hshape⟩
        rcases ih (k := changed) (i := i)
            (by simpa [Prepath.paperIndex] using hgap) hold with
          ⟨j, hij, hjk, hcut⟩
        exact ⟨j, by simpa [Prepath.paperIndex] using hij,
          by simpa [Prepath.paperIndex] using hjk,
          ContainsCut.cutYouIntro hcut changed introTarget hshape hconsistent⟩
      · have hold : HasCutLabelAt Time (Tmid.paperIndex i) (Tmid.get k) := by
          rcases hlabel with ⟨kind, base, hnew⟩
          exact ⟨kind, base, by
            simpa [Prepath.replace_get_ne Tmid hkchanged, Prepath.paperIndex] using hnew⟩
        rcases ih (k := k) (i := i)
            (by simpa [Prepath.paperIndex] using hgap) hold with
          ⟨j, hij, hjk, hcut⟩
        exact ⟨j, by simpa [Prepath.paperIndex] using hij,
          by simpa [Prepath.paperIndex] using hjk,
          ContainsCut.cutYouIntro hcut changed introTarget hshape hconsistent⟩
  | cut deriv hij hjk hk hj hi hconsistent ih =>
      intro queryK queryI hgap hlabel
      rename_i Tmid i j k ti tj tk
      by_cases hkquery : queryK = k
      · subst queryK
        have hnewshape :
            (Derivation.root (Derivation.cut deriv hij hjk hk hj hi hconsistent)).get
              k = ↱ (Tmid.paperIndex i) tk := by
          simp [Derivation.root, Prepath.replace_get_same]
        have htarget := hasCutLabelAt_target_eq_of_eq_cutting hlabel hnewshape
          ((Derivation.root (Derivation.cut deriv hij hjk hk hj hi hconsistent)).consistent k)
        have htarget_val : queryI.val = i.val := by
          exact Nat.succ.inj (by simpa [Prepath.paperIndex] using htarget)
        exact ⟨j, by simpa [Prepath.paperIndex, htarget_val] using Nat.succ_lt_succ hij,
          by simpa [Prepath.paperIndex] using Nat.succ_lt_succ hjk, by
            have hhere := ContainsCut.here deriv hij hjk hk hj hi hconsistent
            simpa [Prepath.paperIndex, htarget_val] using hhere⟩
      · have hold : HasCutLabelAt Time (Tmid.paperIndex queryI) (Tmid.get queryK) := by
          rcases hlabel with ⟨kind, base, hnew⟩
          exact ⟨kind, base, by
            simpa [Prepath.replace_get_ne Tmid hkquery, Prepath.paperIndex] using hnew⟩
        rcases ih (k := queryK) (i := queryI)
            (by simpa [Prepath.paperIndex] using hgap) hold with
          ⟨jWitness, hijWitness, hjkWitness, hcut⟩
        exact ⟨jWitness, by simpa [Prepath.paperIndex] using hijWitness,
          by simpa [Prepath.paperIndex] using hjkWitness,
          ContainsCut.cutStep hcut hij hjk hk hj hi hconsistent⟩

/--
Lemma 5.3.2, in derivation notation:
if `Π[k]` has a Cut label whose target is at least two positions below `k`,
then the corresponding `Cut[k,j,i]` occurs in `Π` for some intermediate `j`.
-/
theorem derivation_jump_implies_cut_exists {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {k i : deriv.Index}
    (hgap : T.paperIndex i + 1 < T.paperIndex k)
    (hlabel : HasCutLabelAt Time (T.paperIndex i) (deriv.get k)) :
    ∃ j : deriv.Index,
      T.paperIndex i < T.paperIndex j ∧
      T.paperIndex j < T.paperIndex k ∧
      ContainsCut deriv (T.paperIndex k) (T.paperIndex j) (T.paperIndex i) := by
  simpa [Derivation.get] using
    jump_implies_cut_exists (Time := Time) deriv (k := k) (i := i) hgap hlabel

/--
Proposition 5.3.3 (Inactive implies Cut): if `j` is `k,i`-inactive
(Definition 4.1.5) for some `k` and `i`, then `Π` contains a (by
Proposition 5.2.3 unique) cut `(Cut_{k',j,i'})` for some `k', i' ∈ index(Π)`
with `k ≥ k' > j > i' ≥ i`.
-/
theorem inactiveBetween_implies_containsCut_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T) {upper center lower : T.Index},
      T.InactiveBetween upper center lower →
        ∃ cutUpper cutLower : T.Index,
          cutUpper.val ≤ upper.val ∧ lower.val ≤ cutLower.val ∧
          cutLower.val < center.val ∧ center.val < cutUpper.val ∧
          ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex center)
            (T.paperIndex cutLower) := by
  intro T deriv
  induction deriv with
  | init hpos base hconsistent =>
      intro upper center lower hinactive
      rcases hinactive with ⟨hlower_center, hcenter_upper, hlabel⟩
      by_cases hupper_zero : upper.val = 0
      · omega
      · have hshape : (initPrepath Time hpos base hconsistent).get upper =
            ↱ upper.val (base upper) := by
          simp [initPrepath, initTime, Prepath.get, hupper_zero,
            LocatedSemilatticeWithCut.nextIndex]
        have htarget := hasCutLabelAt_target_eq_of_eq_cutting hlabel hshape
          ((initPrepath Time hpos base hconsistent).consistent upper)
        simp [Prepath.paperIndex] at htarget
        omega
  | inc deriv changed hlt hflag hconsistent ih =>
      intro upper center lower hinactive
      rename_i Tmid tnew
      rcases hinactive with ⟨hlower_center, hcenter_upper, hlabel⟩
      have hlabel_old : HasCutLabelAt Time (Tmid.paperIndex lower) (Tmid.get upper) := by
        by_cases hupper_changed : upper = changed
        · subst upper
          rcases hlabel with ⟨kind, base, hnew⟩
          have hnew_t : tnew = cutting kind (Tmid.paperIndex lower) base := by
            simpa [Prepath.replace_get_same, Prepath.paperIndex] using hnew
          exact hasCutLabelAt_transfer_back_of_flag_eq changed hnew_t hconsistent hflag
        · rcases hlabel with ⟨kind, base, hnew⟩
          exact ⟨kind, base, by
            have hget := Prepath.replace_get_ne Tmid hupper_changed tnew hlt.1.1.symm
              hconsistent
            simpa [hget, Prepath.paperIndex] using hnew⟩
      rcases ih (upper := upper) (center := center) (lower := lower)
          ⟨hlower_center, hcenter_upper, hlabel_old⟩ with
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
          hcenter_cutUpper, hcut⟩
      exact
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
          hcenter_cutUpper, ContainsCut.inc hcut changed hlt hflag hconsistent⟩
  | cutMeIntro deriv changed introTarget hshape hconsistent ih =>
      intro upper center lower hinactive
      rename_i Tmid baseNew
      rcases hinactive with ⟨hlower_center, hcenter_upper, hlabel⟩
      have hlabel_old : HasCutLabelAt Time (Tmid.paperIndex lower) (Tmid.get upper) := by
        by_cases hupper_changed : upper = changed
        · subst upper
          have hnewshape :
              (Derivation.root
                (Derivation.cutMeIntro deriv changed introTarget hshape hconsistent)).get
                changed = ⋊ introTarget baseNew := by
            simp [Derivation.root, Prepath.replace_get_same]
          have htarget := hasCutLabelAt_target_eq_of_eq_cutting hlabel hnewshape
            ((Derivation.root
                (Derivation.cutMeIntro deriv changed introTarget hshape hconsistent)).consistent
              changed)
          have htarget_mid : Tmid.paperIndex lower = introTarget := by
            simpa [Prepath.paperIndex] using htarget
          exact ⟨CutFlagKind.nextIndex, baseNew, by
            rw [htarget_mid]
            simpa [LocatedSemilatticeWithCut.nextIndex] using hshape⟩
        · rcases hlabel with ⟨kind, base, hnew⟩
          exact ⟨kind, base, by
            simpa [Prepath.replace_get_ne Tmid hupper_changed, Prepath.paperIndex] using hnew⟩
      rcases ih (upper := upper) (center := center) (lower := lower)
          ⟨hlower_center, hcenter_upper, hlabel_old⟩ with
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
          hcenter_cutUpper, hcut⟩
      exact
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
          hcenter_cutUpper,
          ContainsCut.cutMeIntro hcut changed introTarget hshape hconsistent⟩
  | cutYouIntro deriv changed introTarget hshape hconsistent ih =>
      intro upper center lower hinactive
      rename_i Tmid baseNew
      rcases hinactive with ⟨hlower_center, hcenter_upper, hlabel⟩
      have hlabel_old : HasCutLabelAt Time (Tmid.paperIndex lower) (Tmid.get upper) := by
        by_cases hupper_changed : upper = changed
        · subst upper
          have hnewshape :
              (Derivation.root
                (Derivation.cutYouIntro deriv changed introTarget hshape hconsistent)).get
                changed = ⋉ introTarget baseNew := by
            simp [Derivation.root, Prepath.replace_get_same]
          have htarget := hasCutLabelAt_target_eq_of_eq_cutting hlabel hnewshape
            ((Derivation.root
                (Derivation.cutYouIntro deriv changed introTarget hshape hconsistent)).consistent
              changed)
          have htarget_mid : Tmid.paperIndex lower = introTarget := by
            simpa [Prepath.paperIndex] using htarget
          exact ⟨CutFlagKind.nextIndex, baseNew, by
            rw [htarget_mid]
            simpa [LocatedSemilatticeWithCut.nextIndex] using hshape⟩
        · rcases hlabel with ⟨kind, base, hnew⟩
          exact ⟨kind, base, by
            simpa [Prepath.replace_get_ne Tmid hupper_changed, Prepath.paperIndex] using hnew⟩
      rcases ih (upper := upper) (center := center) (lower := lower)
          ⟨hlower_center, hcenter_upper, hlabel_old⟩ with
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
          hcenter_cutUpper, hcut⟩
      exact
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
          hcenter_cutUpper,
          ContainsCut.cutYouIntro hcut changed introTarget hshape hconsistent⟩
  | cut deriv hij hjk hk hj hi hconsistent ih =>
      intro upper center lower hinactive
      rename_i Tmid cutLower cutCenter cutUpper ti tj tk
      rcases hinactive with ⟨hlower_center, hcenter_upper, hlabel⟩
      by_cases hupper_changed : upper = cutUpper
      · subst upper
        have hnewshape :
            (Derivation.root
              (Derivation.cut deriv hij hjk hk hj hi hconsistent)).get cutUpper =
              ↱ (Tmid.paperIndex cutLower) tk := by
          simp [Derivation.root, Prepath.replace_get_same]
        have htarget := hasCutLabelAt_target_eq_of_eq_cutting hlabel hnewshape
          ((Derivation.root
              (Derivation.cut deriv hij hjk hk hj hi hconsistent)).consistent cutUpper)
        have htarget_val : lower.val = cutLower.val := by
          exact Nat.succ.inj (by simpa [Prepath.paperIndex] using htarget)
        rcases Nat.lt_trichotomy center.val cutCenter.val with hcenter_lt | hcenter_eq | hcenter_gt
        · have hprefix_label :
              HasCutLabelAt Time (Tmid.paperIndex cutLower) (Tmid.get cutCenter) := by
            exact
              ⟨CutFlagKind.cutMe,
                tj # (⋉ (Tmid.paperIndex cutCenter) tk), by
                  simpa [LocatedSemilatticeWithCut.cutMe] using hj⟩
          rcases ih (upper := cutCenter) (center := center) (lower := cutLower)
              ⟨by simpa [htarget_val] using hlower_center, hcenter_lt, hprefix_label⟩ with
            ⟨foundUpper, foundLower, hfoundUpper, hfoundLower, hfoundLower_center,
              hcenter_foundUpper, hcut⟩
          exact
            ⟨foundUpper, foundLower, Nat.le_trans hfoundUpper (Nat.le_of_lt hjk),
              by
                have hle : lower.val ≤ cutLower.val := by omega
                exact Nat.le_trans hle hfoundLower,
              hfoundLower_center, hcenter_foundUpper,
              ContainsCut.cutStep hcut hij hjk hk hj hi hconsistent⟩
        · have hcenter_val : center.val = cutCenter.val := hcenter_eq
          exact
            ⟨cutUpper, cutLower, Nat.le_refl _, by omega,
              by simpa [hcenter_val] using hij,
              by simpa [hcenter_val] using hjk, by
                have hhere := ContainsCut.here deriv hij hjk hk hj hi hconsistent
                simpa [Prepath.paperIndex, hcenter_val, htarget_val] using hhere⟩
        · have hprefix_label :
              HasCutLabelAt Time (Tmid.paperIndex cutCenter) (Tmid.get cutUpper) := by
            exact ⟨CutFlagKind.cutYou, tk, by
              simpa [LocatedSemilatticeWithCut.cutYou] using hk⟩
          rcases ih (upper := cutUpper) (center := center) (lower := cutCenter)
              ⟨hcenter_gt, hcenter_upper, hprefix_label⟩ with
            ⟨foundUpper, foundLower, hfoundUpper, hfoundLower, hfoundLower_center,
              hcenter_foundUpper, hcut⟩
          exact
            ⟨foundUpper, foundLower, hfoundUpper,
              by
                have hle_lower_cutCenter : lower.val ≤ cutCenter.val := by omega
                exact Nat.le_trans hle_lower_cutCenter hfoundLower,
              hfoundLower_center, hcenter_foundUpper,
              ContainsCut.cutStep hcut hij hjk hk hj hi hconsistent⟩
      · have hlabel_old : HasCutLabelAt Time (Tmid.paperIndex lower) (Tmid.get upper) := by
          rcases hlabel with ⟨kind, base, hnew⟩
          exact ⟨kind, base, by
            simpa [Prepath.replace_get_ne Tmid hupper_changed, Prepath.paperIndex] using hnew⟩
        rcases ih (upper := upper) (center := center) (lower := lower)
            ⟨hlower_center, hcenter_upper, hlabel_old⟩ with
          ⟨foundUpper, foundLower, hfoundUpper, hfoundLower, hfoundLower_center,
            hcenter_foundUpper, hcut⟩
        exact
          ⟨foundUpper, foundLower, hfoundUpper, hfoundLower, hfoundLower_center,
            hcenter_foundUpper,
            ContainsCut.cutStep hcut hij hjk hk hj hi hconsistent⟩

/-- Lean-indexed form of Proposition 5.3.3. -/
theorem inactiveBetween_implies_containsCut_center_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T) {upper center lower : T.Index},
      T.InactiveBetween upper center lower →
        ∃ cutUpper cutLower : T.Index,
          T.paperIndex cutUpper ≤ T.paperIndex upper ∧
          T.paperIndex lower ≤ T.paperIndex cutLower ∧
          T.paperIndex cutLower < T.paperIndex center ∧
          T.paperIndex center < T.paperIndex cutUpper ∧
          ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex center)
            (T.paperIndex cutLower) := by
  intro T deriv upper center lower hinactive
  rcases inactiveBetween_implies_containsCut_center deriv hinactive with
    ⟨cutUpper, cutLower, hupper, hlower, hcutLower_center, hcenter_cutUpper,
      hcut⟩
  exact
    ⟨cutUpper, cutLower, Nat.succ_le_succ hupper, Nat.succ_le_succ hlower,
      Nat.succ_lt_succ hcutLower_center, Nat.succ_lt_succ hcenter_cutUpper,
      hcut⟩

/-- Corollary 5.1.2. -/
theorem inactiveBetween_implies_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {upper center lower : T.Index}
    (hinactive : T.InactiveBetween upper center lower) :
    ∃ cutLower : T.Index,
      lower.val ≤ cutLower.val ∧ cutLower.val < center.val ∧
      HasCutMe (T.paperIndex cutLower) (T.get center) := by
  rcases inactiveBetween_implies_containsCut_center deriv hinactive with
    ⟨_cutUpper, cutLower, _hupper, hlower, hcutLower_center, _hcenter_upper, hcut⟩
  exact
    ⟨cutLower, hlower, hcutLower_center,
      containsCut_center_hasCutMe hcut center rfl⟩

/-- Lean-indexed form of Corollary 5.1.2. -/
theorem inactiveBetween_implies_hasCutMe_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {upper center lower : T.Index}
    (hinactive : T.InactiveBetween upper center lower) :
    ∃ cutLower : T.Index,
      T.paperIndex lower ≤ T.paperIndex cutLower ∧
      T.paperIndex cutLower < T.paperIndex center ∧
      HasCutMe (T.paperIndex cutLower) (T.get center) := by
  rcases inactiveBetween_implies_hasCutMe deriv hinactive with
    ⟨cutLower, hlower, hcutLower_center, hcutMe⟩
  exact
    ⟨cutLower, Nat.succ_le_succ hlower, Nat.succ_lt_succ hcutLower_center,
      hcutMe⟩

/--
Corollary 5.1.2 (Inactive implies ⋈), in derivation notation: if `j'` is
`k,i`-inactive in `Π`, then `Π[j'] = ⋈_{i'}⊖` for some `i'` with `j' > i' ≥ i`.
-/
theorem derivation_inactiveBetween_implies_hasCutMe_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {upper center lower : T.Index}
    (hinactive : T.InactiveBetween upper center lower) :
    ∃ cutLower : T.Index,
      T.paperIndex lower ≤ T.paperIndex cutLower ∧
      T.paperIndex cutLower < T.paperIndex center ∧
      HasCutMe (T.paperIndex cutLower) (deriv.get center) := by
  simpa [Derivation.get] using
    inactiveBetween_implies_hasCutMe_indexed deriv hinactive

/--
Corollary 5.1.2, with the displayed
`Π[j'] = cutMe_{i'} _` equality and the `i' ≥ i` bound explicit.
-/
theorem derivation_inactiveBetween_implies_eq_cutMe_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {upper center lower : T.Index}
    (hinactive : T.InactiveBetween upper center lower) :
    ∃ cutLower : T.Index, ∃ base : Time,
      T.paperIndex lower ≤ T.paperIndex cutLower ∧
      T.paperIndex cutLower < T.paperIndex center ∧
      deriv.get center = ⋊ (T.paperIndex cutLower) base := by
  rcases derivation_inactiveBetween_implies_hasCutMe_indexed deriv hinactive with
    ⟨cutLower, hlower, hcutLower_center, base, hshape⟩
  exact ⟨cutLower, base, hlower, hcutLower_center, hshape⟩

/--
Same-derivation component of Lemma 5.2.2: if one index
already has a Cut label aimed at `i`, then any later-or-equal index has a Cut
label whose target does not lie strictly between `i` and the original index.
-/
theorem skip_cuts_same_derivation {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {k k' i : T.Index}
    (hik : i.val < k.val) (hkk' : k.val ≤ k'.val)
    (hlabel : HasCutLabelAt Time (T.paperIndex i) (T.get k)) :
    ∃ j : T.Index,
      HasCutLabelAt Time (T.paperIndex j) (T.get k') ∧
      ¬ (i.val < j.val ∧ j.val < k.val) := by
  rcases Nat.eq_or_lt_of_le hkk' with hsame | hlt
  · have hidx : k' = k := Fin.ext hsame.symm
    subst k'
    exact
      ⟨i, hlabel, by
        intro hbad
        exact Nat.lt_irrefl i.val hbad.1⟩
  · have hk'_positive : 0 < k'.val :=
      Nat.lt_of_le_of_lt (Nat.zero_le i.val) (Nat.lt_trans hik hlt)
    have hk'_noninitial : 1 < T.paperIndex k' := by
      simpa [Prepath.paperIndex] using Nat.succ_lt_succ hk'_positive
    rcases time_flag_indexed deriv k' hk'_noninitial with ⟨j, _hj_lt_k', hlabel_k'⟩
    exact
      ⟨j, hlabel_k', by
        intro hbad
        rcases inactiveBetween_implies_hasCutMe deriv
            (upper := k') (center := k) (lower := j)
            ⟨hbad.2, hlt, hlabel_k'⟩ with
          ⟨cutLower, hj_le_cutLower, _hcutLower_lt_k, hcutMe⟩
        rcases hcutMe with ⟨base, hcutMe_eq⟩
        have htarget : T.paperIndex i = T.paperIndex cutLower :=
          hasCutLabelAt_target_eq_of_eq_cutting hlabel hcutMe_eq (T.consistent k)
        have hval : i.val = cutLower.val := by
          exact Nat.succ.inj (by simpa [Prepath.paperIndex] using htarget)
        have hi_lt_i : i.val < i.val := by
          exact Nat.lt_of_lt_of_le hbad.1 (by simpa [← hval] using hj_le_cutLower)
        exact Nat.lt_irrefl i.val hi_lt_i⟩

/--
Disjunctive form of Lemma 5.2.2: the later target is at
or above the original center, or at or below the original target.
-/
theorem skip_cuts_same_derivation_disjunct {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {k k' i : T.Index}
    (hik : i.val < k.val) (hkk' : k.val ≤ k'.val)
    (hlabel : HasCutLabelAt Time (T.paperIndex i) (T.get k)) :
    ∃ j : T.Index,
      HasCutLabelAt Time (T.paperIndex j) (T.get k') ∧
      (k.val ≤ j.val ∨ j.val ≤ i.val) := by
  rcases skip_cuts_same_derivation deriv hik hkk' hlabel with
    ⟨j, hlabel_j, hnot_between⟩
  refine ⟨j, hlabel_j, ?_⟩
  by_cases hkj : k.val ≤ j.val
  · exact Or.inl hkj
  · have hjk : j.val < k.val := Nat.lt_of_not_ge hkj
    exact Or.inr (Nat.le_of_not_gt (by
      intro hij
      exact hnot_between ⟨hij, hjk⟩))

/--
Corollary 5.2.4 (Active points to active): if `j` is active in `Π`
(Definition 4.1.5) and `Π[j] = Q_i⊖` for some lower index `i`, then `i` is
active in `Π`.
-/
theorem active_points_to_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j i : T.Index}
    (hij : i.val < j.val)
    (hactive : deriv.Active j)
    (hlabel : HasCutLabelAt Time (T.paperIndex i) (T.get j)) :
    deriv.Active i := by
  intro hinactive_i
  rcases Derivation.inactive_has_witness deriv hinactive_i with
    ⟨upper, lower, hlower_i, hi_upper, hlabel_upper⟩
  rcases Nat.lt_trichotomy upper.val j.val with hupper_lt_j | hupper_eq_j | hj_lt_upper
  · rcases skip_cuts_same_derivation deriv (k := upper) (k' := j) (i := lower)
        (Nat.lt_trans hlower_i hi_upper) (Nat.le_of_lt hupper_lt_j) hlabel_upper with
      ⟨target, hlabel_j, hnot_between⟩
    rcases hlabel_j with ⟨kind, base, hshape⟩
    have htarget : T.paperIndex i = T.paperIndex target :=
      hasCutLabelAt_target_eq_of_eq_cutting hlabel hshape (T.consistent j)
    have hval : i.val = target.val := by
      exact Nat.succ.inj (by simpa [Prepath.paperIndex] using htarget)
    exact hnot_between
      ⟨by simpa [hval] using hlower_i, by simpa [hval] using hi_upper⟩
  · have hupper_idx : upper = j := Fin.ext hupper_eq_j
    subst upper
    rcases hlabel_upper with ⟨kind, base, hshape⟩
    have htarget : T.paperIndex i = T.paperIndex lower :=
      hasCutLabelAt_target_eq_of_eq_cutting hlabel hshape (T.consistent j)
    have hval : i.val = lower.val := by
      exact Nat.succ.inj (by simpa [Prepath.paperIndex] using htarget)
    have hi_lt_i : i.val < i.val := by
      rw [hval.symm] at hlower_i
      exact hlower_i
    exact Nat.lt_irrefl i.val hi_lt_i
  · exact hactive
      ⟨upper, lower,
        ⟨Nat.lt_trans hlower_i hij, hj_lt_upper, hlabel_upper⟩⟩

/-- Lean-indexed form of Corollary 5.2.4. -/
theorem active_points_to_active_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j i : T.Index}
    (hij : T.paperIndex i < T.paperIndex j)
    (hactive : deriv.Active j)
    (hlabel : HasCutLabelAt Time (T.paperIndex i) (T.get j)) :
    deriv.Active i := by
  exact active_points_to_active deriv
    (Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hij))
    hactive hlabel

/--
Corollary 5.2.4, combined with flag-indexing of non-initial indices: every
active non-initial index carries a Cut label aimed at an earlier index, and by
Corollary 5.2.4 that earlier index is itself active.
-/
theorem active_noninitial_points_to_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index}
    (hactive : deriv.Active j) (hj : 1 < T.paperIndex j) :
    ∃ i : T.Index,
      i.val < j.val ∧ deriv.Active i ∧
        HasCutLabelAt Time (T.paperIndex i) (T.get j) := by
  rcases time_flag_indexed deriv j hj with ⟨i, hi_lt_j, hlabel⟩
  exact ⟨i, hi_lt_j, active_points_to_active deriv hi_lt_j hactive hlabel, hlabel⟩

/-- Lean-indexed form of `active_noninitial_points_to_active`. -/
theorem active_noninitial_points_to_active_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index}
    (hactive : deriv.Active j) (hj : 1 < T.paperIndex j) :
    ∃ i : T.Index,
      T.paperIndex i < T.paperIndex j ∧ deriv.Active i ∧
        HasCutLabelAt Time (T.paperIndex i) (T.get j) := by
  rcases active_noninitial_points_to_active deriv hactive hj with
    ⟨i, hi_lt_j, hactive_i, hlabel⟩
  exact ⟨i, by simpa [Prepath.paperIndex] using Nat.succ_lt_succ hi_lt_j,
    hactive_i, hlabel⟩

/-- Proposition 5.3.3, for the existential inactive predicate. -/
theorem inactive_implies_containsCut_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {center : T.Index}
    (hinactive : T.Inactive center) :
    ∃ cutUpper cutLower : T.Index,
      cutLower.val < center.val ∧ center.val < cutUpper.val ∧
      ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex center)
        (T.paperIndex cutLower) := by
  rcases hinactive with ⟨upper, lower, hinactiveBetween⟩
  rcases inactiveBetween_implies_containsCut_center deriv hinactiveBetween with
    ⟨cutUpper, cutLower, _hupper, _hlower, hcutLower_center, hcenter_cutUpper, hcut⟩
  exact ⟨cutUpper, cutLower, hcutLower_center, hcenter_cutUpper, hcut⟩

/--
Local initial-prefix support lemma: along an initial-prefix extension, a Cut
label at the same index remains a Cut label, and its target can only move to a
no-greater paper index.
-/
theorem cutLabel_target_weakens_of_initialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T1 T2 : Prepath Time} {d1 : Derivation Time T1} {d2 : Derivation Time T2}
      (hprefix : InitialPrefix d1 d2),
        ∀ {upper lower : T1.Index},
          HasCutLabelAt Time (T1.paperIndex lower) (T1.get upper) →
            ∃ lower' : T2.Index,
              T2.paperIndex lower' ≤ T1.paperIndex lower ∧
                HasCutLabelAt Time (T2.paperIndex lower')
                  (T2.get (Fin.cast hprefix.length_eq upper)) := by
  intro T1 T2 d1 d2 hprefix
  induction hprefix with
  | refl _deriv =>
      intro upper lower hlabel
      exact ⟨lower, Nat.le_refl _, hlabel⟩
  | inc deriv hp changed hlt hflag hconsistent ih =>
      intro upper lower hlabel
      rename_i tnew
      let Tmid := Derivation.root deriv
      let finalPath := Tmid.replace changed tnew hlt.1.1.symm hconsistent
      rcases ih hlabel with ⟨lowerMid, hlowerMid, hlabelMid⟩
      let upperMid : Tmid.Index := Fin.cast hp.length_eq upper
      change ∃ lower' : finalPath.Index,
        finalPath.paperIndex lower' ≤ T1.paperIndex lower ∧
          HasCutLabelAt Time (finalPath.paperIndex lower') (finalPath.get upperMid)
      by_cases hsame : upperMid = changed
      · subst changed
        have hlabelAtUpper :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid) (Tmid.get upperMid) := by
          simpa [upperMid] using hlabelMid
        rcases hlabelAtUpper with ⟨kind, base, hshape⟩
        have hnew :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid)
              (finalPath.get upperMid) := by
          have htransferred :
              HasCutLabelAt Time (Tmid.paperIndex lowerMid) tnew :=
            hasCutLabel_transfer_of_flag_eq hshape hflag
          simpa [finalPath, Prepath.replace_get_same] using htransferred
        exact ⟨lowerMid, hlowerMid, hnew⟩
      · have hnew :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid)
              (finalPath.get upperMid) := by
          simpa [finalPath, upperMid, Prepath.replace_get_ne Tmid hsame] using hlabelMid
        exact ⟨lowerMid, hlowerMid, hnew⟩
  | cutMeIntro deriv hp changed target hshape hconsistent ih =>
      intro upper lower hlabel
      rename_i baseNew
      let Tmid := Derivation.root deriv
      have hctrl : controller (⋊ target baseNew) =
          controller (Tmid.get changed) := by
        calc
          controller (⋊ target baseNew) =
              controller baseNew :=
            (⋊ target).controller_preserving baseNew
          _ = controller (↱ target baseNew) :=
            ((↱ target).controller_preserving baseNew).symm
          _ = controller (Tmid.get changed) := by
            simpa [Tmid] using congrArg controller hshape.symm
      let finalPath := Tmid.replace changed (⋊ target baseNew) hctrl hconsistent
      rcases ih hlabel with ⟨lowerMid, hlowerMid, hlabelMid⟩
      let upperMid : Tmid.Index := Fin.cast hp.length_eq upper
      change ∃ lower' : finalPath.Index,
        finalPath.paperIndex lower' ≤ T1.paperIndex lower ∧
          HasCutLabelAt Time (finalPath.paperIndex lower') (finalPath.get upperMid)
      by_cases hsame : upperMid = changed
      · subst changed
        have hlabelAtUpper :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid) (Tmid.get upperMid) := by
          simpa [upperMid] using hlabelMid
        have htarget : Tmid.paperIndex lowerMid = target :=
          hasCutLabelAt_target_eq_of_eq_cutting hlabelAtUpper hshape
            (Tmid.consistent upperMid)
        have hnew :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid)
              (finalPath.get upperMid) := by
          exact
            ⟨CutFlagKind.cutMe, baseNew, by
              simp [finalPath, Prepath.replace_get_same, htarget,
                LocatedSemilatticeWithCut.cutMe]⟩
        exact ⟨lowerMid, hlowerMid, hnew⟩
      · have hnew :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid)
              (finalPath.get upperMid) := by
          simpa [finalPath, upperMid, Prepath.replace_get_ne Tmid hsame] using hlabelMid
        exact ⟨lowerMid, hlowerMid, hnew⟩
  | cutYouIntro deriv hp changed target hshape hconsistent ih =>
      intro upper lower hlabel
      rename_i baseNew
      let Tmid := Derivation.root deriv
      have hctrl : controller (⋉ target baseNew) =
          controller (Tmid.get changed) := by
        calc
          controller (⋉ target baseNew) =
              controller baseNew :=
            (⋉ target).controller_preserving baseNew
          _ = controller (↱ target baseNew) :=
            ((↱ target).controller_preserving baseNew).symm
          _ = controller (Tmid.get changed) := by
            simpa [Tmid] using congrArg controller hshape.symm
      let finalPath := Tmid.replace changed (⋉ target baseNew) hctrl hconsistent
      rcases ih hlabel with ⟨lowerMid, hlowerMid, hlabelMid⟩
      let upperMid : Tmid.Index := Fin.cast hp.length_eq upper
      change ∃ lower' : finalPath.Index,
        finalPath.paperIndex lower' ≤ T1.paperIndex lower ∧
          HasCutLabelAt Time (finalPath.paperIndex lower') (finalPath.get upperMid)
      by_cases hsame : upperMid = changed
      · subst changed
        have hlabelAtUpper :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid) (Tmid.get upperMid) := by
          simpa [upperMid] using hlabelMid
        have htarget : Tmid.paperIndex lowerMid = target :=
          hasCutLabelAt_target_eq_of_eq_cutting hlabelAtUpper hshape
            (Tmid.consistent upperMid)
        have hnew :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid)
              (finalPath.get upperMid) := by
          exact
            ⟨CutFlagKind.cutYou, baseNew, by
              simp [finalPath, Prepath.replace_get_same, htarget,
                LocatedSemilatticeWithCut.cutYou]⟩
        exact ⟨lowerMid, hlowerMid, hnew⟩
      · have hnew :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid)
              (finalPath.get upperMid) := by
          simpa [finalPath, upperMid, Prepath.replace_get_ne Tmid hsame] using hlabelMid
        exact ⟨lowerMid, hlowerMid, hnew⟩
  | cut deriv hp hij hjk hk hj hi hconsistent ih =>
      intro upper lower hlabel
      rename_i cutLower cutCenter cutUpper ti tj tk
      let Tmid := Derivation.root deriv
      have hctrl : controller (↱ (Tmid.paperIndex cutLower) tk) =
          controller (Tmid.get cutUpper) := by
        calc
          controller (↱ (Tmid.paperIndex cutLower) tk) =
              controller tk :=
            (↱ (Tmid.paperIndex cutLower)).controller_preserving tk
          _ = controller (⋉ (Tmid.paperIndex cutCenter) tk) :=
            ((⋉ (Tmid.paperIndex cutCenter)).controller_preserving tk).symm
          _ = controller (Tmid.get cutUpper) := by
            simpa [Tmid] using congrArg controller hk.symm
      let finalPath :=
        Tmid.replace cutUpper (↱ (Tmid.paperIndex cutLower) tk) hctrl
          hconsistent
      rcases ih hlabel with ⟨lowerMid, hlowerMid, hlabelMid⟩
      let upperMid : Tmid.Index := Fin.cast hp.length_eq upper
      change ∃ lower' : finalPath.Index,
        finalPath.paperIndex lower' ≤ T1.paperIndex lower ∧
          HasCutLabelAt Time (finalPath.paperIndex lower') (finalPath.get upperMid)
      by_cases hsame : upperMid = cutUpper
      · have hlabelAtUpper :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid) (Tmid.get cutUpper) := by
          simpa [upperMid, hsame] using hlabelMid
        have htarget : Tmid.paperIndex lowerMid = Tmid.paperIndex cutCenter :=
          hasCutLabelAt_target_eq_of_eq_cutting hlabelAtUpper hk (Tmid.consistent cutUpper)
        have hcutLower_le_lowerMid :
            Tmid.paperIndex cutLower ≤ Tmid.paperIndex lowerMid := by
          exact Nat.le_of_lt (by
            have hlt : Tmid.paperIndex cutLower < Tmid.paperIndex cutCenter := by
              simpa [Prepath.paperIndex] using Nat.succ_lt_succ hij
            simpa [htarget] using hlt)
        have hnew :
            HasCutLabelAt Time (Tmid.paperIndex cutLower)
              (finalPath.get upperMid) := by
          exact
            ⟨CutFlagKind.nextIndex, tk, by
              simp [finalPath, hsame, Prepath.replace_get_same,
                LocatedSemilatticeWithCut.nextIndex]⟩
        exact ⟨cutLower, Nat.le_trans hcutLower_le_lowerMid hlowerMid, hnew⟩
      · have hnew :
            HasCutLabelAt Time (Tmid.paperIndex lowerMid)
              (finalPath.get upperMid) := by
          simpa [finalPath, upperMid, Prepath.replace_get_ne Tmid hsame] using hlabelMid
        exact ⟨lowerMid, hlowerMid, hnew⟩

/--
A contained Cut leaves, at its final upper endpoint, a later Cut label whose
target is no greater than the Cut's lower endpoint. This is the persistent
upper-endpoint datum needed for the affine-cuts argument (Proposition 5.2.3).
-/
theorem containsCut_upper_hasCutLabel_le_lower {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) {upper : T.Index}
    (hupper : T.paperIndex upper = cutK) :
    ∃ lower : T.Index,
      T.paperIndex lower ≤ cutI ∧
        HasCutLabelAt Time (T.paperIndex lower) (T.get upper) := by
  rcases containsCut_prefixData hcut with ⟨data⟩
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hlabelPrefix :
      HasCutLabelAt Time (data.base.paperIndex data.idxI)
        ((Derivation.root dcut).get data.idxK) :=
    final_cut_upper_has_nextIndex data.baseDeriv data.hij data.hjk data.hk data.hj
      data.hi data.hconsistent
  rcases cutLabel_target_weakens_of_initialPrefix data.hprefix hlabelPrefix with
    ⟨lower, hlower_le, hlabel⟩
  have hidxK_cast : Fin.cast data.hprefix.length_eq data.idxK = upper := by
    apply Fin.ext
    have hpaper : data.base.paperIndex data.idxK = T.paperIndex upper :=
      data.cutK_eq.symm.trans hupper.symm
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hpaper)
  exact
    ⟨lower, by simpa [data.cutI_eq] using hlower_le,
      by simpa [dcut, hidxK_cast] using hlabel⟩

/--
Initial-prefix form of Lemma 5.2.2: if a prefix index
already has a Cut label aimed at `i`, then any later-or-equal final index has a
Cut label whose target does not lie strictly between `i` and the original
center.
-/
theorem skip_cuts_initialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T2 : Prepath Time}
    {d1 : Derivation Time T1} {d2 : Derivation Time T2}
    (hprefix : InitialPrefix d1 d2)
    {i k k' : T1.Index}
    (hik : i.val < k.val) (hkk' : k.val ≤ k'.val)
    (hlabel : HasCutLabelAt Time (T1.paperIndex i) (T1.get k)) :
    ∃ j : T2.Index,
      HasCutLabelAt Time (T2.paperIndex j) (T2.get (Fin.cast hprefix.length_eq k')) ∧
      ¬ (i.val < j.val ∧ j.val < k.val) := by
  rcases cutLabel_target_weakens_of_initialPrefix hprefix hlabel with
    ⟨iFinal, hiFinal_le_i, hlabelFinal⟩
  let kFinal : T2.Index := Fin.cast hprefix.length_eq k
  let kFinal' : T2.Index := Fin.cast hprefix.length_eq k'
  have hiFinal_le_val : iFinal.val ≤ i.val := by
    exact Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hiFinal_le_i)
  have hiFinal_lt_kFinal : iFinal.val < kFinal.val := by
    simpa [kFinal] using Nat.lt_of_le_of_lt hiFinal_le_val hik
  have hkFinal_le_kFinal' : kFinal.val ≤ kFinal'.val := by
    simpa [kFinal, kFinal'] using hkk'
  rcases skip_cuts_same_derivation d2 hiFinal_lt_kFinal hkFinal_le_kFinal'
      hlabelFinal with
    ⟨j, hlabel_j, hnot_between_final⟩
  exact
    ⟨j, by simpa [kFinal'] using hlabel_j, by
      intro hbad
      exact hnot_between_final
        ⟨Nat.lt_of_le_of_lt hiFinal_le_val hbad.1, by simpa [kFinal] using hbad.2⟩⟩

/--
Lemma 5.2.2, in derivation notation:
from `Π₁[k] = Q_i _`, the later `Π[k']` has a Cut label whose target does not
lie strictly between `i` and `k`.
-/
theorem derivation_skip_cuts_initialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T2 : Prepath Time} {d1 : Derivation Time T1} {d2 : Derivation Time T2}
    (hprefix : InitialPrefix d1 d2)
    {i k k' : d1.Index}
    (hik : i.val < k.val) (hkk' : k.val ≤ k'.val)
    (hlabel : HasCutLabelAt Time (T1.paperIndex i) (d1.get k)) :
    ∃ j : d2.Index,
      HasCutLabelAt Time (T2.paperIndex j) (d2.get (Fin.cast hprefix.length_eq k')) ∧
      ¬ (i.val < j.val ∧ j.val < k.val) := by
  simpa [Derivation.get] using
    skip_cuts_initialPrefix hprefix hik hkk' hlabel

/--
Disjunctive initial-prefix form of Lemma 5.2.2.
-/
theorem skip_cuts_initialPrefix_disjunct {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T2 : Prepath Time}
    {d1 : Derivation Time T1} {d2 : Derivation Time T2}
    (hprefix : InitialPrefix d1 d2)
    {i k k' : T1.Index}
    (hik : i.val < k.val) (hkk' : k.val ≤ k'.val)
    (hlabel : HasCutLabelAt Time (T1.paperIndex i) (T1.get k)) :
    ∃ j : T2.Index,
      HasCutLabelAt Time (T2.paperIndex j) (T2.get (Fin.cast hprefix.length_eq k')) ∧
      (k.val ≤ j.val ∨ j.val ≤ i.val) := by
  rcases skip_cuts_initialPrefix hprefix hik hkk' hlabel with
    ⟨j, hlabel_j, hnot_between⟩
  refine ⟨j, hlabel_j, ?_⟩
  by_cases hkj : k.val ≤ j.val
  · exact Or.inl hkj
  · have hjk : j.val < k.val := Nat.lt_of_not_ge hkj
    exact Or.inr (Nat.le_of_not_gt (by
      intro hij
      exact hnot_between ⟨hij, hjk⟩))

/--
Lemma 5.2.2, in derivation notation and disjunctive
form: the later target is at-or-above `k` or at-or-below `i`.
-/
theorem derivation_skip_cuts_initialPrefix_disjunct {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T2 : Prepath Time} {d1 : Derivation Time T1} {d2 : Derivation Time T2}
    (hprefix : InitialPrefix d1 d2)
    {i k k' : d1.Index}
    (hik : i.val < k.val) (hkk' : k.val ≤ k'.val)
    (hlabel : HasCutLabelAt Time (T1.paperIndex i) (d1.get k)) :
    ∃ j : d2.Index,
      HasCutLabelAt Time (T2.paperIndex j) (d2.get (Fin.cast hprefix.length_eq k')) ∧
      (k.val ≤ j.val ∨ j.val ≤ i.val) := by
  simpa [Derivation.get] using
    skip_cuts_initialPrefix_disjunct hprefix hik hkk' hlabel

/--
Local initial-prefix support lemma: a concrete inactive witness in an initial
prefix grows to a later inactive witness whose upper endpoint has not moved
left and whose lower endpoint has not moved right.
-/
theorem inactiveBetween_grows_of_initialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T2 : Prepath Time} {d1 : Derivation Time T1} {d2 : Derivation Time T2}
    (hprefix : InitialPrefix d1 d2) {upper center lower : T1.Index}
    (hinactive : T1.InactiveBetween upper center lower) :
    ∃ upper' lower' : T2.Index,
      T1.paperIndex upper ≤ T2.paperIndex upper' ∧
        T2.paperIndex lower' ≤ T1.paperIndex lower ∧
          T2.InactiveBetween upper' (Fin.cast hprefix.length_eq center) lower' := by
  rcases hinactive with ⟨hlower_center, hcenter_upper, hlabel⟩
  rcases cutLabel_target_weakens_of_initialPrefix hprefix hlabel with
    ⟨lower', hlower', hlabel'⟩
  let upper' : T2.Index := Fin.cast hprefix.length_eq upper
  let center' : T2.Index := Fin.cast hprefix.length_eq center
  have hupper_bound : T1.paperIndex upper ≤ T2.paperIndex upper' := by
    simp [upper', Prepath.paperIndex]
  have hlower'_center : lower'.val < center'.val := by
    have hpaper_lt : T2.paperIndex lower' < T2.paperIndex center' := by
      exact Nat.lt_of_le_of_lt hlower' (by
        simpa [center', Prepath.paperIndex] using Nat.succ_lt_succ hlower_center)
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ_iff.mp hpaper_lt
  have hcenter_upper' : center'.val < upper'.val := by
    simpa [center', upper'] using hcenter_upper
  exact
    ⟨upper', lower', hupper_bound, hlower',
      ⟨hlower'_center, hcenter_upper', hlabel'⟩⟩

/--
Local initial-prefix support lemma: a contained Cut occurrence gives a later
inactive witness whose upper endpoint is no lower than the Cut upper endpoint
and whose lower endpoint is no greater than the Cut lower endpoint.
-/
theorem containsCut_center_inactiveBetween_grows {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) {center : T.Index}
    (hcenter : cutJ = T.paperIndex center) :
    ∃ upper lower : T.Index,
      cutK ≤ T.paperIndex upper ∧
        T.paperIndex lower ≤ cutI ∧
          T.InactiveBetween upper center lower := by
  rcases containsCut_prefixData hcut with ⟨data⟩
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hinactivePrefix :
      (Derivation.root dcut).InactiveBetween data.idxK data.idxJ data.idxI := by
    exact
      ⟨data.hij, data.hjk,
        final_cut_upper_has_nextIndex data.baseDeriv data.hij data.hjk data.hk data.hj
          data.hi data.hconsistent⟩
  rcases inactiveBetween_grows_of_initialPrefix data.hprefix hinactivePrefix with
    ⟨upper, lower, hupper, hlower, hinactiveCast⟩
  have hcenterCast : Fin.cast data.hprefix.length_eq data.idxJ = center := by
    apply Fin.ext
    have hpaper : data.base.paperIndex data.idxJ = T.paperIndex center := by
      exact data.cutJ_eq.symm.trans hcenter
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hpaper)
  have hinactive : T.InactiveBetween upper center lower := by
    simpa [hcenterCast] using hinactiveCast
  exact
    ⟨upper, lower, by simpa [data.cutK_eq] using hupper,
      by simpa [data.cutI_eq] using hlower, hinactive⟩

/--
Local initial-prefix support lemma: an inactive index remains inactive after
later derivation steps.
-/
theorem inactive_of_initialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T2 : Prepath Time} {d1 : Derivation Time T1} {d2 : Derivation Time T2}
    (hprefix : InitialPrefix d1 d2) {j : T1.Index}
    (hinactive : d1.Inactive j) :
    d2.Inactive (Fin.cast hprefix.length_eq j) := by
  rcases inactive_implies_containsCut_center d1 hinactive with
    ⟨cutUpper, cutLower, _hcutLower, _hcutUpper, hcut⟩
  have hcutLater :
      ContainsCut d2 (T1.paperIndex cutUpper) (T1.paperIndex j)
        (T1.paperIndex cutLower) :=
    containsCut_of_initialPrefix hprefix hcut
  exact containsCut_center_inactive hcutLater (center := Fin.cast hprefix.length_eq j)
    (by simp [Prepath.paperIndex])

/--
Local projection from refined Cut-prefix data: the final derivation is inactive
at the center named by the Cut occurrence.
-/
theorem cutPrefixData_center_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    {center : T.Index} (hcenter : cutJ = T.paperIndex center) :
    deriv.Inactive center := by
  have hinactiveCast :
      deriv.Inactive (Fin.cast data.hprefix.length_eq data.idxJ) := by
    exact inactive_of_initialPrefix data.hprefix
      (final_cut_implies_inactive data.baseDeriv data.hij data.hjk data.hk
        data.hj data.hi data.hconsistent)
  have hcenterCast : Fin.cast data.hprefix.length_eq data.idxJ = center := by
    apply Fin.ext
    have hpaper : data.base.paperIndex data.idxJ = T.paperIndex center := by
      exact data.cutJ_eq.symm.trans hcenter
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hpaper)
  simpa [hcenterCast] using hinactiveCast

/--
Post-Cut center projection for a prefix-packaged Cut: in the derivation ending
with the selected Cut rule, the Cut center is inactive.
-/
theorem cutPrefixData_final_cut_center_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) :
    (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent).Inactive data.idxJ := by
  exact final_cut_implies_inactive data.baseDeriv data.hij data.hjk data.hk
    data.hj data.hi data.hconsistent

/--
Greatest-active-prefix component for a prefix-packaged Cut: any initial prefix
of the final derivation that is still active at the Cut center must be an
initial prefix of the selected pre-Cut base.
-/
theorem cutPrefixData_active_prefix_before_base {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T Pref : Prepath Time} {deriv : Derivation Time T}
    {prefDeriv : Derivation Time Pref} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hpref : InitialPrefix prefDeriv deriv)
    {center : T.Index} (hcenter : cutJ = T.paperIndex center)
    (hactive : prefDeriv.Active (Fin.cast hpref.length_eq.symm center)) :
    InitialPrefix prefDeriv data.baseDeriv := by
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hcutToFinal : InitialPrefix dcut deriv := by
    simpa [dcut] using data.hprefix
  have hbaseToCut : InitialPrefix data.baseDeriv dcut := by
    simpa [dcut] using data.base_initialPrefix_cut
  have hcenterVal : data.idxJ.val = center.val := by
    apply Nat.succ.inj
    have hpaper : data.base.paperIndex data.idxJ = T.paperIndex center := by
      exact data.cutJ_eq.symm.trans hcenter
    simpa [Prepath.paperIndex] using hpaper
  have hnotCutToPref : ¬ InitialPrefix dcut prefDeriv := by
    intro hcutToPref
    have hinactive :
        prefDeriv.Inactive (Fin.cast hcutToPref.length_eq data.idxJ) := by
      exact inactive_of_initialPrefix hcutToPref
        (by simpa [dcut] using cutPrefixData_final_cut_center_inactive data)
    have hidx :
        Fin.cast hcutToPref.length_eq data.idxJ =
          Fin.cast hpref.length_eq.symm center := by
      apply Fin.ext
      exact hcenterVal
    exact hactive (by simpa [hidx] using hinactive)
  rcases InitialPrefix.comparable hpref hcutToFinal with hprefToCut | hcutToPref
  · rcases InitialPrefix.comparable hprefToCut hbaseToCut with hprefToBase | hbaseToPref
    · exact hprefToBase
    · have hheight : dcut.height = data.baseDeriv.height + 1 := by
        simp [dcut, Derivation.height]
      rcases InitialPrefix.no_intermediate_of_height_succ hbaseToPref hprefToCut
          hheight with hprefToBase | hcutToPref'
      · exact hprefToBase
      · exact False.elim (hnotCutToPref hcutToPref')
  · exact False.elim (hnotCutToPref hcutToPref)

/--
Prefix-ending-Cut component of Corollary 5.3.4.
-/
theorem inactiveBetween_implies_cutPrefix_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T) {upper center lower : T.Index},
      T.InactiveBetween upper center lower →
        ∃ cutUpper cutLower : T.Index,
          cutUpper.val ≤ upper.val ∧ lower.val ≤ cutLower.val ∧
          cutLower.val < center.val ∧ center.val < cutUpper.val ∧
          CutPrefixWitness deriv (T.paperIndex cutUpper) (T.paperIndex center)
            (T.paperIndex cutLower) := by
  intro T deriv upper center lower hinactive
  rcases inactiveBetween_implies_containsCut_center deriv hinactive with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
      hcenter_cutUpper, hcut⟩
  exact
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
      hcenter_cutUpper, containsCut_prefixWitness hcut⟩

/-- Lean-indexed form of Corollary 5.3.4. -/
theorem inactiveBetween_implies_cutPrefix_center_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T) {upper center lower : T.Index},
      T.InactiveBetween upper center lower →
        ∃ cutUpper cutLower : T.Index,
          T.paperIndex cutUpper ≤ T.paperIndex upper ∧
          T.paperIndex lower ≤ T.paperIndex cutLower ∧
          T.paperIndex cutLower < T.paperIndex center ∧
          T.paperIndex center < T.paperIndex cutUpper ∧
          CutPrefixWitness deriv (T.paperIndex cutUpper) (T.paperIndex center)
            (T.paperIndex cutLower) := by
  intro T deriv upper center lower hinactive
  rcases inactiveBetween_implies_cutPrefix_center deriv hinactive with
    ⟨cutUpper, cutLower, hupper, hlower, hcutLower_center, hcenter_cutUpper,
      hprefix⟩
  exact
    ⟨cutUpper, cutLower, Nat.succ_le_succ hupper, Nat.succ_le_succ hlower,
      Nat.succ_lt_succ hcutLower_center, Nat.succ_lt_succ hcenter_cutUpper,
      hprefix⟩

/--
Prefix-ending-Cut component for the existential inactive
predicate.
-/
theorem inactive_implies_cutPrefix_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {center : T.Index}
    (hinactive : T.Inactive center) :
    ∃ cutUpper cutLower : T.Index,
      cutLower.val < center.val ∧ center.val < cutUpper.val ∧
      CutPrefixWitness deriv (T.paperIndex cutUpper) (T.paperIndex center)
        (T.paperIndex cutLower) := by
  rcases hinactive with ⟨upper, lower, hinactiveBetween⟩
  rcases inactiveBetween_implies_cutPrefix_center deriv hinactiveBetween with
    ⟨cutUpper, cutLower, _hupper_bound, _hlower_bound, hcutLower_center,
      hcenter_cutUpper, hprefix⟩
  exact ⟨cutUpper, cutLower, hcutLower_center, hcenter_cutUpper, hprefix⟩

/-- Corollary 5.1.2, for inactive indices. -/
theorem inactive_implies_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {center : T.Index}
    (hinactive : T.Inactive center) :
    ∃ cutLower : T.Index,
      cutLower.val < center.val ∧
      HasCutMe (T.paperIndex cutLower) (T.get center) := by
  rcases hinactive with ⟨upper, lower, hinactiveBetween⟩
  rcases inactiveBetween_implies_hasCutMe deriv hinactiveBetween with
    ⟨cutLower, _hlower_bound, hcutLower_center, hcutMe⟩
  exact ⟨cutLower, hcutLower_center, hcutMe⟩

/--
Corollary 5.1.2, in derivation
notation for inactive indexes.
-/
theorem derivation_inactive_implies_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T)
    {center : T.Index} (hinactive : deriv.Inactive center) :
    ∃ cutLower : T.Index,
      cutLower.val < center.val ∧
      HasCutMe (T.paperIndex cutLower) (deriv.get center) := by
  simpa [Derivation.get] using inactive_implies_hasCutMe deriv hinactive

/--
Corollary 5.1.2, existential inactive-index form with the displayed
`Π[j'] = cutMe_{i'} _` equality.
-/
theorem derivation_inactive_implies_eq_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T)
    {center : T.Index} (hinactive : deriv.Inactive center) :
    ∃ cutLower : T.Index, ∃ base : Time,
      cutLower.val < center.val ∧
      deriv.get center = ⋊ (T.paperIndex cutLower) base := by
  rcases derivation_inactive_implies_hasCutMe deriv hinactive with
    ⟨cutLower, hcutLower_center, base, hshape⟩
  exact ⟨cutLower, base, hcutLower_center, hshape⟩

/--
Pre-Cut upper-endpoint component of Lemma 5.2.5: if a Cut rule is applicable, then the upper endpoint `k`
is already active in the premise derivation.
-/
theorem pre_cut_upper_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (_hij : i.val < j.val) (_hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (_hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (_hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (_hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    deriv.Active k := by
  intro hinactive
  rcases inactive_implies_hasCutMe deriv hinactive with
    ⟨_cutLower, _hcutLower_k, hcutMe⟩
  rcases hcutMe with ⟨cutBase, hcutMe_eq⟩
  exact not_cutMe_eq_cutYou_at_consistent k hcutMe_eq hk

/--
No earlier Cut in the premise of a final `Cut[k,j,i]` step can already be
centered at `j`. This is a local affine-cuts component.
-/
theorem no_containsCut_before_final_same_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk))
    {cutK cutI : Nat}
    (hprior : ContainsCut deriv cutK (T.paperIndex j) cutI) :
    False := by
  rcases containsCut_indices hprior with
    ⟨priorUpper, priorCenter, _priorLower, hpriorUpper, hpriorCenter,
      _hpriorLower, _hpriorLower_center, hpriorCenter_upper⟩
  have hpriorCenter_eq : priorCenter = j := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hpriorCenter)
  subst priorCenter
  rcases containsCut_upper_hasCutLabel_le_lower hprior hpriorUpper with
    ⟨labelLower, hlabelLower_le_cutI, hlabelUpper⟩
  have horder := containsCut_order hprior
  have hlabelLower_lt_j_paper : T.paperIndex labelLower < T.paperIndex j :=
    Nat.lt_of_le_of_lt hlabelLower_le_cutI horder.1
  have hlabelLower_lt_j : labelLower.val < j.val := by
    exact Nat.succ_lt_succ_iff.mp (by
      simpa [Prepath.paperIndex] using hlabelLower_lt_j_paper)
  rcases Nat.lt_trichotomy priorUpper.val k.val with hprior_lt_k | hprior_eq_k | hk_lt_prior
  · rcases skip_cuts_same_derivation deriv
        (k := priorUpper) (k' := k) (i := labelLower)
        (Nat.lt_trans hlabelLower_lt_j hpriorCenter_upper)
        (Nat.le_of_lt hprior_lt_k) hlabelUpper with
      ⟨found, hlabelFound, hnot_between⟩
    have hfound_paper : T.paperIndex found = T.paperIndex j :=
      hasCutLabelAt_target_eq_of_eq_cutting hlabelFound hk (T.consistent k)
    have hfound_val : found.val = j.val :=
      Nat.succ.inj (by simpa [Prepath.paperIndex] using hfound_paper)
    exact hnot_between
      ⟨by simpa [hfound_val] using hlabelLower_lt_j,
        by simpa [hfound_val] using hpriorCenter_upper⟩
  · have hpriorUpper_eq : priorUpper = k := Fin.ext hprior_eq_k
    subst priorUpper
    have htarget : T.paperIndex labelLower = T.paperIndex j :=
      hasCutLabelAt_target_eq_of_eq_cutting hlabelUpper hk (T.consistent k)
    have hbad : T.paperIndex j < T.paperIndex j := by
      rw [htarget] at hlabelLower_lt_j_paper
      exact hlabelLower_lt_j_paper
    exact Nat.lt_irrefl (T.paperIndex j) hbad
  · have hkinactive : deriv.Inactive k := by
      exact containsCut_brackets_inactive hprior
        (Nat.lt_trans horder.1 (Nat.succ_lt_succ hjk))
        (by
          rw [← hpriorUpper]
          exact Nat.succ_lt_succ hk_lt_prior)
    exact (pre_cut_upper_active deriv hij hjk hk hj hi hconsistent) hkinactive

/--
Arbitrary-prefix form of the affine-cuts component (Proposition 5.2.3): in the
premise of the Cut represented by `data`, no earlier Cut is already centered at
the same index.
-/
theorem cutPrefixData_no_prior_same_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) {priorK priorI : Nat}
    (hprior : ContainsCut data.baseDeriv priorK cutJ priorI) :
    False := by
  have hprior_base :
      ContainsCut data.baseDeriv priorK (data.base.paperIndex data.idxJ) priorI := by
    simpa [data.cutJ_eq] using hprior
  exact no_containsCut_before_final_same_center data.baseDeriv data.hij data.hjk
    data.hk data.hj data.hi data.hconsistent hprior_base

/--
Pre-Cut active-center component of Corollary 5.3.4: in the prefix immediately before the
selected Cut, its center is active.
-/
theorem cutPrefixData_pre_cut_center_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) :
    data.baseDeriv.Active data.idxJ := by
  intro hinactive
  rcases inactive_implies_containsCut_center data.baseDeriv hinactive with
    ⟨priorUpper, priorLower, _hlower_center, _hcenter_upper, hprior⟩
  exact
    cutPrefixData_no_prior_same_center data
      (priorK := data.base.paperIndex priorUpper)
      (priorI := data.base.paperIndex priorLower)
      (by simpa [data.cutJ_eq] using hprior)

/--
Decomposable active-prefix component of Corollary 5.3.4, for a concrete inactive witness.
-/
theorem inactiveBetween_implies_cutPrefixData_center_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T) {upper center lower : T.Index},
      T.InactiveBetween upper center lower →
        ∃ cutUpper cutLower : T.Index,
          cutUpper.val ≤ upper.val ∧ lower.val ≤ cutLower.val ∧
          cutLower.val < center.val ∧ center.val < cutUpper.val ∧
          ∃ data : CutPrefixData deriv (T.paperIndex cutUpper) (T.paperIndex center)
            (T.paperIndex cutLower),
            data.baseDeriv.Active data.idxJ := by
  intro T deriv upper center lower hinactive
  rcases inactiveBetween_implies_containsCut_center deriv hinactive with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
      hcenter_cutUpper, hcut⟩
  rcases containsCut_prefixData hcut with ⟨data⟩
  exact
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
      hcenter_cutUpper, data, cutPrefixData_pre_cut_center_active data⟩

/--
Corollary 5.3.4, packed for a concrete
inactive witness. The pre-Cut prefix is `data.baseDeriv`; the post-Cut
derivation is the source of `data.hprefix`, and final inactivity follows by
initial-prefix monotonicity.
-/
theorem inactiveBetween_implies_cutPrefixData_refined {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T) {upper center lower : T.Index},
      T.InactiveBetween upper center lower →
        ∃ cutUpper cutLower : T.Index,
          cutUpper.val ≤ upper.val ∧ lower.val ≤ cutLower.val ∧
          cutLower.val < center.val ∧ center.val < cutUpper.val ∧
          ∃ data : CutPrefixData deriv (T.paperIndex cutUpper) (T.paperIndex center)
            (T.paperIndex cutLower),
            data.baseDeriv.Active data.idxJ ∧ deriv.Inactive center := by
  intro T deriv upper center lower hinactive
  rcases inactiveBetween_implies_cutPrefixData_center_active deriv hinactive with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
      hcenter_cutUpper, data, hactive⟩
  exact
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_center,
      hcenter_cutUpper, data, hactive, cutPrefixData_center_inactive data rfl⟩

/--
Decomposable active-prefix component of Corollary 5.3.4, for the existential inactive predicate.
-/
theorem inactive_implies_cutPrefixData_center_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {center : T.Index}
    (hinactive : T.Inactive center) :
    ∃ cutUpper cutLower : T.Index,
      cutLower.val < center.val ∧ center.val < cutUpper.val ∧
      ∃ data : CutPrefixData deriv (T.paperIndex cutUpper) (T.paperIndex center)
        (T.paperIndex cutLower),
        data.baseDeriv.Active data.idxJ := by
  rcases hinactive with ⟨upper, lower, hinactiveBetween⟩
  rcases inactiveBetween_implies_cutPrefixData_center_active deriv hinactiveBetween with
    ⟨cutUpper, cutLower, _hupper_bound, _hlower_bound, hcutLower_center,
      hcenter_cutUpper, data, hactive⟩
  exact ⟨cutUpper, cutLower, hcutLower_center, hcenter_cutUpper, data, hactive⟩

/--
Corollary 5.3.4, packed for the
existential inactive predicate.
-/
theorem inactive_implies_cutPrefixData_refined {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {center : T.Index}
    (hinactive : deriv.Inactive center) :
    ∃ cutUpper cutLower : T.Index,
      cutLower.val < center.val ∧ center.val < cutUpper.val ∧
      ∃ data : CutPrefixData deriv (T.paperIndex cutUpper) (T.paperIndex center)
        (T.paperIndex cutLower),
        data.baseDeriv.Active data.idxJ ∧ deriv.Inactive center := by
  rcases inactive_implies_cutPrefixData_center_active deriv hinactive with
    ⟨cutUpper, cutLower, hcutLower_center, hcenter_cutUpper, data, hactive⟩
  exact
    ⟨cutUpper, cutLower, hcutLower_center, hcenter_cutUpper, data, hactive, hinactive⟩

/--
Internal Cut-occurrence uniqueness used by the affine-cuts argument: two Cut
triples introduced in one derivation cannot have the same center unless they are
the same triple.
-/
theorem cutTriples_center_unique {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T)
      {a b : Nat × Nat × Nat},
      a ∈ cutTriples deriv →
      b ∈ cutTriples deriv →
      a.2.1 = b.2.1 →
      a = b := by
  intro T deriv
  induction deriv with
  | init _hpos _base _hconsistent =>
      intro a _b ha _hb _hcenter
      simp [cutTriples] at ha
  | inc _deriv _changed _hlt _hflag _hconsistent ih =>
      intro _a _b ha hb hcenter
      exact ih ha hb hcenter
  | cutMeIntro _deriv _changed _target _hshape _hconsistent ih =>
      intro _a _b ha hb hcenter
      exact ih ha hb hcenter
  | cutYouIntro _deriv _changed _target _hshape _hconsistent ih =>
      intro _a _b ha hb hcenter
      exact ih ha hb hcenter
  | cut deriv hij hjk hk hj hi hconsistent ih =>
      intro a b ha hb hcenter
      rename_i T i j k _ti _tj _tk
      simp [cutTriples] at ha hb
      rcases ha with haHead | haTail
      · rcases hb with hbHead | hbTail
        · subst a
          subst b
          rfl
        · subst a
          rcases b with ⟨bK, bJ, bI⟩
          have hbcut_bJ : ContainsCut deriv bK bJ bI :=
            containsCut_of_mem_cutTriples deriv (by simpa using hbTail)
          have hcenter' : T.paperIndex j = bJ := by
            simpa using hcenter
          have hbcut : ContainsCut deriv bK (T.paperIndex j) bI := by
            rw [← hcenter'] at hbcut_bJ
            exact hbcut_bJ
          exact False.elim
            (no_containsCut_before_final_same_center deriv hij hjk hk hj hi
              hconsistent hbcut)
      · rcases hb with hbHead | hbTail
        · subst b
          rcases a with ⟨aK, aJ, aI⟩
          have hacut_aJ : ContainsCut deriv aK aJ aI :=
            containsCut_of_mem_cutTriples deriv (by simpa using haTail)
          have hcenter' : aJ = T.paperIndex j := by
            simpa using hcenter
          have hacut : ContainsCut deriv aK (T.paperIndex j) aI := by
            rw [hcenter'] at hacut_aJ
            exact hacut_aJ
          exact False.elim
            (no_containsCut_before_final_same_center deriv hij hjk hk hj hi
              hconsistent hacut)
        · exact ih haTail hbTail hcenter

/--
Proposition 5.2.3: two Cut occurrences in one derivation
with the same center are the same Cut triple.
-/
theorem containsCut_same_center_triple_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutK' cutJ cutI cutI' : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    (hcut' : ContainsCut deriv cutK' cutJ cutI') :
    (cutK, cutJ, cutI) = (cutK', cutJ, cutI') :=
  cutTriples_center_unique deriv
    (mem_cutTriples_of_containsCut hcut)
    (mem_cutTriples_of_containsCut hcut')
    rfl

/--
Endpoint component of Proposition 5.2.3: two Cut occurrences
in one derivation with the same center have the same upper and lower endpoints.
-/
theorem containsCut_same_center_endpoints_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutK' cutJ cutI cutI' : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    (hcut' : ContainsCut deriv cutK' cutJ cutI') :
    cutK = cutK' ∧ cutI = cutI' := by
  have htriple :
      (cutK, cutJ, cutI) = (cutK', cutJ, cutI') :=
    containsCut_same_center_triple_eq hcut hcut'
  cases htriple
  exact ⟨rfl, rfl⟩

/--
Lean-indexed endpoint component of Proposition 5.2.3.
-/
theorem containsCut_same_center_endpoints_index_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {upper upper' center lower lower' : T.Index}
    (hcut : ContainsCut deriv (T.paperIndex upper) (T.paperIndex center)
      (T.paperIndex lower))
    (hcut' : ContainsCut deriv (T.paperIndex upper') (T.paperIndex center)
      (T.paperIndex lower')) :
    upper = upper' ∧ lower = lower' := by
  rcases containsCut_same_center_endpoints_eq hcut hcut' with ⟨hupper, hlower⟩
  constructor
  · apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hupper)
  · apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hlower)

/--
Upper-endpoint component of Lemma 5.2.5: if the
final derivation step is `Cut[k,j,i]`, then `k` is active in the result.
-/
theorem final_cut_upper_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).Active k := by
  intro hinactive
  let dcut := Derivation.cut deriv hij hjk hk hj hi hconsistent
  rcases inactive_implies_hasCutMe dcut hinactive with ⟨cutLower, _hcutLower_k, hcutMe⟩
  rcases hcutMe with ⟨base, hcutMe_eq⟩
  have hnext :
      (Derivation.root dcut).get k = ↱ (T.paperIndex i) tk := by
    simp [dcut, Derivation.root, Prepath.replace_get_same]
  exact not_cutMe_eq_nextIndex_at_consistent (T := Derivation.root dcut) k hcutMe_eq hnext

/-- A prefix-packaged Cut exposes pre-Cut upper-endpoint activity. -/
theorem cutPrefixData_pre_cut_upper_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) :
    data.baseDeriv.Active data.idxK := by
  exact pre_cut_upper_active data.baseDeriv data.hij data.hjk data.hk data.hj
    data.hi data.hconsistent

/-- A prefix-packaged Cut exposes post-Cut upper-endpoint activity. -/
theorem cutPrefixData_final_cut_upper_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) :
    (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent).Active data.idxK := by
  exact final_cut_upper_active data.baseDeriv data.hij data.hjk data.hk data.hj
    data.hi data.hconsistent

/--
Lemma 5.2.5 (Cut endpoints active): if the final derivation-step in `Π` is
`(Cut_{k,j,i})`, then both endpoints `k` and `i` are active in `Π`.
-/
theorem final_cut_endpoints_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).Active k ∧
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).Active i := by
  let dcut := Derivation.cut deriv hij hjk hk hj hi hconsistent
  have hupper : dcut.Active k :=
    final_cut_upper_active deriv hij hjk hk hj hi hconsistent
  have hlabel : HasCutLabelAt Time (T.paperIndex i) ((Derivation.root dcut).get k) :=
    final_cut_upper_has_nextIndex deriv hij hjk hk hj hi hconsistent
  exact
    ⟨hupper,
      active_points_to_active dcut (Nat.lt_trans hij hjk) hupper hlabel⟩

/--
Lower-endpoint component of Lemma 5.2.5: if the
final derivation step is `Cut[k,j,i]`, then `i` is active in the result.
-/
theorem final_cut_lower_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).Active i := by
  exact (final_cut_endpoints_active deriv hij hjk hk hj hi hconsistent).2

/-- A prefix-packaged Cut exposes post-Cut lower-endpoint activity. -/
theorem cutPrefixData_final_cut_lower_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) :
    (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent).Active data.idxI := by
  exact final_cut_lower_active data.baseDeriv data.hij data.hjk data.hk data.hj
    data.hi data.hconsistent

end ConsistentHistories.Routes.PathProperties.InactiveCuts
