import ContForm.Routes.Paths.Circuits

/-!
Paper subsection 5.1: Persistence of ⋈.

Lemma 5.1.1 (⋈ persists): once a time displays a `cutMe` flag `⋈ᵢ⊙` at an
index, no later derivation step can change it. The file also formalizes the
Cut-center component behind Corollaries 5.1.2 and 5.1.3 (a Cut centered on `j`
leaves `j` displaying `⋈ᵢ⊙`), and the Remark 5.1.4 counterexample showing the
reverse implications fail (a `cutMe` flag can sit on an active, uncut index).
-/

namespace ContForm.Routes.PathProperties.CutmePersistence

open ContForm.Foundation.LocatedSemilattices.Basic
open ContForm.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ContForm.Foundation.Cut.Flags
open ContForm.Foundation.Cut.Structure
open ContForm.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ContForm.Foundation.Paths.Basic
open ContForm.Foundation.Paths.InitialPrefixes
open ContForm.Routes.Paths.Circuits

universe u v

/-- A time has a `cutMe_target` flag. -/
def HasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (target : Nat) (t : Time) : Prop :=
  ∃ base : Time, t = ⋊ target base

/-- Direct `cutMe` times have their displayed `cutMe` target. -/
theorem hasCutMe_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (target : Nat) (base : Time) :
    HasCutMe target (⋊ target base) :=
  ⟨base, rfl⟩

/-- Expanding the `HasCutMe` definition. -/
theorem hasCutMe_iff_exists_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (target : Nat)
    (t : Time) :
    HasCutMe target t ↔ ∃ base : Time, t = ⋊ target base :=
  Iff.rfl

/-- A displayed `cutMe` equality gives a `HasCutMe` witness. -/
theorem hasCutMe_of_eq_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {target : Nat}
    {t base : Time} (h : t = ⋊ target base) :
    HasCutMe target t :=
  ⟨base, h⟩

/-- A `cutMe` witness is a Cut-label witness with kind `cutMe`. -/
theorem hasCutLabelAt_of_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {target : Nat}
    {t : Time} (h : HasCutMe target t) :
    HasCutLabelAt Time target t := by
  rcases h with ⟨base, hbase⟩
  exact ⟨CutFlagKind.cutMe, base, hbase⟩

/-- At a prepath index a `cutMe_target` witness gives the visible `⋊ target` form,
using the index's consistency. -/
theorem hasForm_cutMe_of_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (j : T.Index) {target : Nat} (h : HasCutMe target (T.get j)) :
    HasForm (⋊ target) (T.get j) := by
  exact ⟨T.consistent j, h⟩

/-- A time with a `cutMe_target` witness has the corresponding cutting flag. -/
theorem flagOf_eq_cutMe_of_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (j : T.Index) {target : Nat} (h : HasCutMe target (T.get j)) :
    flagOf cuttingFlagSet (T.get j) =
      some ⟨⋊ target, cutMe_mem target⟩ :=
  flagOf_eq_some_of_hasForm cuttingFlagSet
    (cutMe_mem target) (hasForm_cutMe_of_hasCutMe j h)

/-- Lemma 5.1.1 proof detail: a `cutMe_target` flag lookup exposes a `cutMe` witness. -/
theorem hasCutMe_of_flagOf_eq_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (j : T.Index) {target : Nat}
    (hflag :
      flagOf cuttingFlagSet (T.get j) =
        some ⟨⋊ target, cutMe_mem target⟩) :
    HasCutMe target (T.get j) := by
  exact (flagOf_eq_some_hasForm cuttingFlagSet hflag).2

/--
Lemma 5.1.1 proof detail: at a prepath index, visible `cutMe_target` form
is equivalent to the corresponding flag lookup.
-/
theorem hasCutMe_iff_flagOf_eq_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (j : T.Index) {target : Nat} :
    HasCutMe target (T.get j) ↔
      flagOf cuttingFlagSet (T.get j) =
        some ⟨⋊ target, cutMe_mem target⟩ := by
  constructor
  · exact flagOf_eq_cutMe_of_hasCutMe j
  · exact hasCutMe_of_flagOf_eq_cutMe j

/--
Lemma 5.1.1 proof detail: a consistent time carries at most one flag
(Lemma 3.2.5), so it cannot display two different `cutMe` targets.
-/
theorem hasCutMe_target_eq_of_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {target target' : Nat} {t : Time}
    (hconsistent : ConsistentTime t)
    (h : HasCutMe target t) (h' : HasCutMe target' t) :
    target = target' := by
  have hform : HasForm (⋊ target) t :=
    ⟨hconsistent, h⟩
  have hform' : HasForm (⋊ target') t :=
    ⟨hconsistent, h'⟩
  have hflag :
      ⋊ target = ⋊ target' :=
    flag_unique_of_hasForm cuttingFlagSet
      (cutMe_mem target) (cutMe_mem target') hform hform'
  exact (cutting_eq_iff.mp hflag).2

/--
Lemma 5.1.1 proof detail at a prepath index: visible `cutMe` targets are
unique.
-/
theorem hasCutMe_target_eq_at_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (j : T.Index) {target target' : Nat}
    (h : HasCutMe target (T.get j)) (h' : HasCutMe target' (T.get j)) :
    target = target' := by
  exact hasCutMe_target_eq_of_consistent (T.consistent j) h h'

/-- Lemma 5.1.1 proof detail (⋈Intro case): a consistent time cannot be both a
`cutMe` (`⋊`) and a `nextIndex` (`↱`) time, so an equality `⋊ᵢt = ↱ⱼt'` is
impossible (Lemma 3.2.5). -/
theorem not_cutMe_eq_nextIndex_at_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (j : T.Index) {cutTarget nextTarget : Nat} {cutBase nextBase : Time}
    (hcut : T.get j = ⋊ cutTarget cutBase)
    (hnext : T.get j = ↱ nextTarget nextBase) : False := by
  have hleft : ConsistentTime (⋊ cutTarget cutBase) := by
    rw [← hcut]
    exact T.consistent j
  have hright : ConsistentTime (↱ nextTarget nextBase) := by
    rw [← hnext]
    exact T.consistent j
  exact cutMe_ne_nextIndex_of_consistent hleft hright (hcut.symm.trans hnext)

/-- Lemma 5.1.1 proof detail (Cut case): a consistent time cannot be both a
`cutMe` (`⋊`) and a `cutYou` (`⋉`) time, so an equality `⋊ᵢt = ⋉ⱼt'` is
impossible (Lemma 3.2.5). -/
theorem not_cutMe_eq_cutYou_at_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (j : T.Index) {cutTarget youTarget : Nat} {cutBase youBase : Time}
    (hcut : T.get j = ⋊ cutTarget cutBase)
    (hyou : T.get j = ⋉ youTarget youBase) : False := by
  have hleft : ConsistentTime (⋊ cutTarget cutBase) := by
    rw [← hcut]
    exact T.consistent j
  have hright : ConsistentTime (⋉ youTarget youBase) := by
    rw [← hyou]
    exact T.consistent j
  exact cutMe_ne_cutYou_of_consistent hleft hright (hcut.symm.trans hyou)

/-- Form of the Cut derivation rule: applying `Cut` at the triple `i < j < k`
sets the center `j` to `⋊ (paperIndex i) …`, so `j` displays `⋊ᵢ⊙`. This is the
base fact behind Corollary 5.1.3 (Cut implies ⋈). -/
theorem final_cut_center_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    HasCutMe (T.paperIndex i)
      ((Derivation.root (Derivation.cut deriv hij hjk hk hj hi hconsistent)).get j) := by
  have hj_ne_k : j ≠ k := by
    intro h
    cases h
    exact Nat.lt_irrefl j.val hjk
  exact
    ⟨tj # (⋉ (T.paperIndex j) tk), by
      simp [Derivation.root, Prepath.replace_get_ne T hj_ne_k, hj,
        LocatedSemilatticeWithCut.cutMe]⟩

/-- Lemma 5.1.1 (⋈ persists): if the initial prefix `T1` displays `⋊ target` at
an index, the full derivation `T` still displays `⋊ target` at that index.
Proved by induction over the initial-prefix derivation steps (`Init`, `Inc`,
`⋈Intro`, `⋉Intro`, `Cut`), each of which cannot alter an existing `cutMe`
flag. -/
theorem cutme_forever {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (hprefix : InitialPrefix d1 d) :
    ∀ j0 : T1.Index, ∀ target : Nat,
      HasCutMe target (T1.get j0) →
        HasCutMe target (T.get (Fin.cast hprefix.length_eq j0)) := by
  induction hprefix with
  | refl _deriv =>
    intro j0 target hcut
    exact hcut
  | inc _deriv hp changed hlt hflag hconsistent ih =>
    intro j0 target hcut
    rename_i Tmid _d1mid tnew
    let jmid := Fin.cast (InitialPrefix.length_eq hp) j0
    have hprev : HasCutMe target (Tmid.get jmid) := ih j0 target hcut
    change HasCutMe target ((Tmid.replace changed tnew hlt.1.1.symm hconsistent).get jmid)
    by_cases hsame : jmid = changed
    · have hform_old_jmid : HasForm (⋊ target) (Tmid.get jmid) :=
        hasForm_cutMe_of_hasCutMe jmid hprev
      have hform_old_changed :
          HasForm (⋊ target) (Tmid.get changed) := by
        simpa [hsame] using hform_old_jmid
      have hform_new := flagOf_transfer_hasForm cuttingFlagSet
        (cutting_mem CutFlagKind.cutMe target) hform_old_changed hflag
      simpa [Prepath.replace, Prepath.get, hsame] using hform_new.2
    · have hget := Prepath.replace_get_ne Tmid hsame tnew hlt.1.1.symm hconsistent
      rw [hget]
      exact hprev
  | cutMeIntro _deriv hp changed introTarget hshape hconsistent ih =>
    intro j0 target hcut
    rename_i Tmid _d1mid base
    let jmid := Fin.cast (InitialPrefix.length_eq hp) j0
    have hprev : HasCutMe target (Tmid.get jmid) := ih j0 target hcut
    have hctrl : controller (⋊ introTarget base) =
        controller (Tmid.get changed) := by
      calc
        controller (⋊ introTarget base) = controller base :=
          (⋊ introTarget).controller_preserving base
        _ = controller (↱ introTarget base) :=
          ((↱ introTarget).controller_preserving base).symm
        _ = controller (Tmid.get changed) := by rw [hshape]
    change HasCutMe target ((Tmid.replace changed (⋊ introTarget base)
      hctrl hconsistent).get jmid)
    by_cases hsame : jmid = changed
    · rcases hprev with ⟨baseCut, hbase⟩
      have hbase_changed : Tmid.get changed = ⋊ target baseCut := by
        simpa [hsame] using hbase
      exact False.elim (not_cutMe_eq_nextIndex_at_consistent changed hbase_changed hshape)
    · have hget := Prepath.replace_get_ne Tmid hsame (⋊ introTarget base)
        hctrl hconsistent
      rw [hget]
      exact hprev
  | cutYouIntro _deriv hp changed introTarget hshape hconsistent ih =>
    intro j0 target hcut
    rename_i Tmid _d1mid base
    let jmid := Fin.cast (InitialPrefix.length_eq hp) j0
    have hprev : HasCutMe target (Tmid.get jmid) := ih j0 target hcut
    have hctrl : controller (⋉ introTarget base) =
        controller (Tmid.get changed) := by
      calc
        controller (⋉ introTarget base) = controller base :=
          (⋉ introTarget).controller_preserving base
        _ = controller (↱ introTarget base) :=
          ((↱ introTarget).controller_preserving base).symm
        _ = controller (Tmid.get changed) := by rw [hshape]
    change HasCutMe target ((Tmid.replace changed (⋉ introTarget base)
      hctrl hconsistent).get jmid)
    by_cases hsame : jmid = changed
    · rcases hprev with ⟨baseCut, hbase⟩
      have hbase_changed : Tmid.get changed = ⋊ target baseCut := by
        simpa [hsame] using hbase
      exact False.elim (not_cutMe_eq_nextIndex_at_consistent changed hbase_changed hshape)
    · have hget := Prepath.replace_get_ne Tmid hsame (⋉ introTarget base)
        hctrl hconsistent
      rw [hget]
      exact hprev
  | cut _deriv hp _hij _hjk hk _hj _hi hconsistent ih =>
    intro j0 target hcut
    rename_i Tmid _d1mid i j k _ti _tj tk
    let jmid := Fin.cast (InitialPrefix.length_eq hp) j0
    have hprev : HasCutMe target (Tmid.get jmid) := ih j0 target hcut
    have hctrl : controller (↱ (Tmid.paperIndex i) tk) =
        controller (Tmid.get k) := by
      calc
        controller (↱ (Tmid.paperIndex i) tk) =
            controller tk :=
          (↱ (Tmid.paperIndex i)).controller_preserving tk
        _ = controller (⋉ (Tmid.paperIndex j) tk) :=
          ((⋉ (Tmid.paperIndex j)).controller_preserving tk).symm
        _ = controller (Tmid.get k) := by rw [hk]
    change HasCutMe target ((Tmid.replace k (↱ (Tmid.paperIndex i) tk)
      hctrl hconsistent).get jmid)
    by_cases hsame : jmid = k
    · rcases hprev with ⟨baseCut, hbase⟩
      have hbase_changed : Tmid.get k = ⋊ target baseCut := by
        simpa [hsame] using hbase
      exact False.elim (not_cutMe_eq_cutYou_at_consistent k hbase_changed hk)
    · have hget := Prepath.replace_get_ne Tmid hsame
        (↱ (Tmid.paperIndex i) tk) hctrl hconsistent
      rw [hget]
      exact hprev

/--
Lemma 5.1.1 in the paper's derivation notation:
`Π₁[j] = ⋈ᵢ⊙` implies `Π[j] = ⋈ᵢ⊙`.
-/
theorem derivation_cutme_forever {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (hprefix : InitialPrefix d1 d) :
    ∀ j0 : d1.Index, ∀ target : Nat,
      HasCutMe target (d1.get j0) →
        HasCutMe target (d.get (Fin.cast hprefix.length_eq j0)) := by
  intro j0 target hcut
  simpa [Derivation.get] using cutme_forever hprefix j0 target hcut

/--
Lemma 5.1.1, displayed implication form: an explicit `cutMe_i` equality in
the prefix yields a `cutMe_i` witness in the later derivation.
-/
theorem derivation_cutme_forever_of_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T : Prepath Time} {d1 : Derivation Time T1} {d : Derivation Time T}
    (hprefix : InitialPrefix d1 d) (j0 : d1.Index) (target : Nat)
    {base : Time}
    (hcut : d1.get j0 = ⋊ target base) :
    HasCutMe target (d.get (Fin.cast hprefix.length_eq j0)) :=
  derivation_cutme_forever hprefix j0 target ⟨base, hcut⟩

/--
Lemma 5.1.1, displayed implication form exposing the later base time: the
persisted flag is `⋊ target laterBase` for some `laterBase`.
-/
theorem derivation_cutme_forever_exists_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T : Prepath Time} {d1 : Derivation Time T1} {d : Derivation Time T}
    (hprefix : InitialPrefix d1 d) (j0 : d1.Index) (target : Nat)
    {base : Time}
    (hcut : d1.get j0 = ⋊ target base) :
    ∃ laterBase : Time,
      d.get (Fin.cast hprefix.length_eq j0) = ⋊ target laterBase := by
  exact derivation_cutme_forever_of_eq hprefix j0 target hcut

/-- Corollary 5.1.3 component: the `⋊ᵢ⊙` flag that a `Cut` places on its center
`j` (from `final_cut_center_hasCutMe`) persists (Lemma 5.1.1) to every later
derivation that has the `Cut` step as an initial prefix. -/
theorem final_cut_center_cutMe_forever {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T0 T : Prepath Time}
    (deriv : Derivation Time T0) {i j k : T0.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T0.get k = ⋉ (T0.paperIndex j) tk)
    (hj : T0.get j =
      ⋊ (T0.paperIndex i) (tj # (⋉ (T0.paperIndex j) tk)))
    (hi : T0.get i =
      ti # (⋊ (T0.paperIndex i)
        (tj # (⋉ (T0.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T0.paperIndex i) tk))
    {d : Derivation Time T}
    (hprefix : InitialPrefix (Derivation.cut deriv hij hjk hk hj hi hconsistent) d) :
    HasCutMe (T0.paperIndex i) (T.get (Fin.cast hprefix.length_eq j)) := by
  exact cutme_forever hprefix j (T0.paperIndex i)
    (final_cut_center_hasCutMe deriv hij hjk hk hj hi hconsistent)

/-- Corollary 5.1.3 component: whenever a derivation contains a `Cut` centered on
`j` (paper index `cutJ`, cutting `i = cutI`), that center displays `⋊ᵢ⊙`. Proved
by induction over the derivation steps following the `Cut`, each preserving the
flag (Lemma 5.1.1). -/
theorem containsCut_center_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat},
      ContainsCut deriv cutK cutJ cutI →
        ∀ center : T.Index, T.paperIndex center = cutJ →
          HasCutMe cutI (T.get center) := by
  intro T deriv cutK cutJ cutI hcut
  induction hcut with
  | here deriv hij hjk hk hj hi hconsistent =>
      intro center hcenter
      rename_i Tmid i j k ti tj tk
      have hcenter_eq : center = j := by
        exact Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hcenter))
      subst center
      exact final_cut_center_hasCutMe deriv hij hjk hk hj hi hconsistent
  | inc h changed hlt hflag hconsistent ih =>
      intro center hcenter
      rename_i Tmid deriv cutK cutJ cutI tnew
      have hprev : HasCutMe cutI (Tmid.get center) :=
        ih center (by simpa [Prepath.paperIndex] using hcenter)
      by_cases hsame : center = changed
      · have hform_old_center : HasForm (⋊ cutI) (Tmid.get center) :=
          hasForm_cutMe_of_hasCutMe (T := Tmid) center hprev
        have hform_old_changed :
            HasForm (⋊ cutI) (Tmid.get changed) := by
          simpa [hsame] using hform_old_center
        have hform_new := flagOf_transfer_hasForm cuttingFlagSet
          (cutting_mem CutFlagKind.cutMe cutI) hform_old_changed hflag
        simpa [Prepath.replace, Prepath.get, hsame] using hform_new.2
      · rw [Prepath.replace_get_ne Tmid hsame tnew hlt.1.1.symm hconsistent]
        exact hprev
  | cutMeIntro h changed introTarget hshape hconsistent ih =>
      intro center hcenter
      rename_i Tmid deriv cutK cutJ cutI base
      have hprev : HasCutMe cutI (Tmid.get center) :=
        ih center (by simpa [Prepath.paperIndex] using hcenter)
      change HasCutMe cutI ((Tmid.replace changed (⋊ introTarget base)
        _ hconsistent).get center)
      by_cases hsame : center = changed
      · rcases hprev with ⟨baseCut, hbase⟩
        have hbase_changed : Tmid.get changed = ⋊ cutI baseCut := by
          simpa [hsame] using hbase
        exact False.elim (not_cutMe_eq_nextIndex_at_consistent changed hbase_changed hshape)
      · rw [Prepath.replace_get_ne Tmid hsame (⋊ introTarget base) _ hconsistent]
        exact hprev
  | cutYouIntro h changed introTarget hshape hconsistent ih =>
      intro center hcenter
      rename_i Tmid deriv cutK cutJ cutI base
      have hprev : HasCutMe cutI (Tmid.get center) :=
        ih center (by simpa [Prepath.paperIndex] using hcenter)
      change HasCutMe cutI ((Tmid.replace changed (⋉ introTarget base)
        _ hconsistent).get center)
      by_cases hsame : center = changed
      · rcases hprev with ⟨baseCut, hbase⟩
        have hbase_changed : Tmid.get changed = ⋊ cutI baseCut := by
          simpa [hsame] using hbase
        exact False.elim (not_cutMe_eq_nextIndex_at_consistent changed hbase_changed hshape)
      · rw [Prepath.replace_get_ne Tmid hsame (⋉ introTarget base) _ hconsistent]
        exact hprev
  | cutStep h hij hjk hk hj hi hconsistent ih =>
      intro center hcenter
      rename_i Tmid deriv cutK cutJ cutI i j k ti tj tk
      have hprev : HasCutMe cutI (Tmid.get center) :=
        ih center (by simpa [Prepath.paperIndex] using hcenter)
      change HasCutMe cutI ((Tmid.replace k (↱ (Tmid.paperIndex i) tk)
        _ hconsistent).get center)
      by_cases hsame : center = k
      · rcases hprev with ⟨baseCut, hbase⟩
        have hbase_changed : Tmid.get k = ⋊ cutI baseCut := by
          simpa [hsame] using hbase
        exact False.elim (not_cutMe_eq_cutYou_at_consistent k hbase_changed hk)
      · rw [Prepath.replace_get_ne Tmid hsame
          (↱ (Tmid.paperIndex i) tk) _ hconsistent]
        exact hprev

/--
Corollary 5.1.3 component, flag-lookup form: a contained `Cut` fixes the
center's visible cutting flag as the `cutMe` flag `⋊ cutI`.
-/
theorem containsCut_center_flagOf_eq_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat},
      ContainsCut deriv cutK cutJ cutI →
        ∀ center : T.Index, T.paperIndex center = cutJ →
          flagOf cuttingFlagSet (T.get center) =
            some ⟨⋊ cutI, cutMe_mem cutI⟩ := by
  intro T deriv cutK cutJ cutI hcut center hcenter
  exact flagOf_eq_cutMe_of_hasCutMe center
    (containsCut_center_hasCutMe hcut center hcenter)

/-- A contained Cut gives the center a Cut label aimed at its lower endpoint. -/
theorem containsCut_center_hasCutLabelAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat},
      ContainsCut deriv cutK cutJ cutI →
        ∀ center : T.Index, T.paperIndex center = cutJ →
          HasCutLabelAt Time cutI (T.get center) := by
  intro T deriv cutK cutJ cutI hcut center hcenter
  exact hasCutLabelAt_of_hasCutMe (containsCut_center_hasCutMe hcut center hcenter)

/--
Remark 5.1.4 counterexample component: the reverse of Corollaries 5.1.2 and
5.1.3 fails. An `Init` derivation followed by `⋈Intro` on the second index
(paper `⋈Intro₂`) makes that index display `⋈₁⊙` while it stays active and no
`Cut` occurrence is present.
-/
theorem cutMeIntro_after_init_has_cutMe_active_uncut
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (base : Fin 2 → Time)
    (hinit : ∀ i, ConsistentTime (initTime Time base i))
    (hcut : ConsistentTime (⋊ 1 (base ⟨1, by decide⟩))) :
    let T0 := initPrepath Time (by decide : 0 < 2) base hinit
    let top : T0.Index := ⟨1, by dsimp [T0, initPrepath]; decide⟩
    let d0 : Derivation Time T0 := Derivation.init (Time := Time) (by decide : 0 < 2) base hinit
    let d := Derivation.cutMeIntro d0 top 1 (by
      simp [T0, top, initPrepath, initTime, Prepath.get]) hcut
    HasCutMe 1 (d.get top) ∧ d.Active top ∧
      (∀ k i, ¬ ContainsCut d k (d.root.paperIndex top) i) := by
  dsimp
  constructor
  · exact ⟨base ⟨1, by decide⟩, by simp [Derivation.get]⟩
  constructor
  · intro hinactive
    rcases hinactive with ⟨upper, _lower, hbetween⟩
    have hlt : 1 < upper.val := by
      simpa using hbetween.2.1
    have hupper : upper.val < 2 := upper.isLt
    omega
  · intro _k _i hcontains
    have hmem := mem_cutTriples_of_containsCut hcontains
    simp [cutTriples] at hmem

/--
Remark 5.1.4 counterexample package: in the displayed two-index derivation
(`Init` then `⋈Intro₂`), the second index displays `⋈₁⊙`, both indexes are
active, and no `Cut` rule occurs — so `⋈` neither implies inactivity
(Corollary 5.1.2) nor a containing Cut (Corollary 5.1.3).
-/
theorem cutMeIntro_after_init_two_index_active_uncut
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (base : Fin 2 → Time)
    (hinit : ∀ i, ConsistentTime (initTime Time base i))
    (hcut : ConsistentTime (⋊ 1 (base ⟨1, by decide⟩))) :
    let T0 := initPrepath Time (by decide : 0 < 2) base hinit
    let top : T0.Index := ⟨1, by dsimp [T0, initPrepath]; decide⟩
    let d0 : Derivation Time T0 := Derivation.init (Time := Time) (by decide : 0 < 2) base hinit
    let d := Derivation.cutMeIntro d0 top 1 (by
      simp [T0, top, initPrepath, initTime, Prepath.get]) hcut
    HasCutMe 1 (d.get top) ∧ (∀ idx : d.Index, d.Active idx) ∧
      (∀ k j i, ¬ ContainsCut d k j i) := by
  dsimp
  constructor
  · exact ⟨base ⟨1, by decide⟩, by simp [Derivation.get]⟩
  constructor
  · intro idx hinactive
    rcases hinactive with ⟨upper, lower, hbetween⟩
    have hlower_idx : lower.val < idx.val := hbetween.1
    have hidx_upper : idx.val < upper.val := hbetween.2.1
    have hidx_bound : idx.val < 2 := idx.isLt
    have hupper_bound : upper.val < 2 := upper.isLt
    omega
  · intro _k _j _i hcontains
    have hmem := mem_cutTriples_of_containsCut hcontains
    simp [cutTriples] at hmem

end ContForm.Routes.PathProperties.CutmePersistence
