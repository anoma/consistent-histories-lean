import ConsistentHistories.Routes.PathProperties.CutmePersistence

/-!
Paper section 5.2: Flag nesting and affine cuts.

-/

namespace ConsistentHistories.Routes.PathProperties.FlagNesting

open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.Cut.Flags
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Foundation.Paths.InitialPrefixes
open ConsistentHistories.Routes.Paths.Circuits
open ConsistentHistories.Routes.PathProperties.CutmePersistence

universe u v

/-- The conclusion shape of Lemma 5.2.1: the time at index `j` carries a cutting
flag aimed at a paper index `target` with `0 < target < Π[j]`, i.e. `Π[j] = Q_target⊝`
for some cutting flag `Q` and some earlier index `target < j`. -/
def HasPriorCutLabel {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) (j : T.Index) : Prop :=
  ∃ target : Nat, 0 < target ∧ target < T.paperIndex j ∧ HasCutLabelAt Time target (T.get j)

/-- Definitional characterisation of `HasPriorCutLabel` as the existence of a
target that is positive, below `Π[j]`, and labelling the time at `j`. -/
theorem hasPriorCutLabel_iff_exists {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) :
    HasPriorCutLabel T j ↔
      ∃ target : Nat, 0 < target ∧ target < T.paperIndex j ∧
        HasCutLabelAt Time target (T.get j) :=
  Iff.rfl

/-- A `HasPriorCutLabel` witness supplies a target with `0 < target < Π[j]`. -/
theorem hasPriorCutLabel_target_pos {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {j : T.Index} (h : HasPriorCutLabel T j) :
    ∃ target : Nat, 0 < target ∧ target < T.paperIndex j := by
  rcases h with ⟨target, hpos, hlt, _hlabel⟩
  exact ⟨target, hpos, hlt⟩

/-- A `HasPriorCutLabel` witness supplies a concrete target labelling the time at `j`. -/
theorem hasPriorCutLabel_hasCutLabelAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {j : T.Index} (h : HasPriorCutLabel T j) :
    ∃ target : Nat, HasCutLabelAt Time target (T.get j) := by
  rcases h with ⟨target, _hpos, _hlt, hlabel⟩
  exact ⟨target, hlabel⟩

theorem positive_val_of_noninitial {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {j : T.Index} (hj : 1 < T.paperIndex j) : 0 < j.val := by
  cases j with
  | mk _val _isLt =>
    dsimp [Prepath.paperIndex] at hj ⊢
    exact Nat.succ_lt_succ_iff.mp hj

theorem hasPrior_of_eq_cutting {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {j : T.Index} {kind : CutFlagKind} {target : Nat} {base : Time}
    (hprior : HasPriorCutLabel T j)
    (hshape : T.get j = cutting kind target base) :
    0 < target ∧ target < T.paperIndex j := by
  rcases hprior with ⟨oldTarget, oldPos, oldLt, oldKind, oldBase, hold⟩
  have hleft : ConsistentTime (cutting oldKind oldTarget oldBase) := by
    rw [← hold]
    exact T.consistent j
  have hright : ConsistentTime (cutting kind target base) := by
    rw [← hshape]
    exact T.consistent j
  have htarget := flag_target_eq_of_eq_consistent hleft hright
    (hold.symm.trans hshape)
  exact ⟨by simpa [← htarget] using oldPos, by simpa [← htarget] using oldLt⟩

theorem hasPrior_of_eq_nextIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {j : T.Index} {target : Nat} {base : Time}
    (hprior : HasPriorCutLabel T j)
    (hshape : T.get j = ↱ target base) :
    0 < target ∧ target < T.paperIndex j := by
  exact hasPrior_of_eq_cutting hprior hshape

theorem hasPrior_of_eq_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {j : T.Index} {target : Nat} {base : Time}
    (hprior : HasPriorCutLabel T j)
    (hshape : T.get j = ⋊ target base) :
    0 < target ∧ target < T.paperIndex j := by
  exact hasPrior_of_eq_cutting hprior hshape

theorem hasPrior_of_eq_cutYou {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {j : T.Index} {target : Nat} {base : Time}
    (hprior : HasPriorCutLabel T j)
    (hshape : T.get j = ⋉ target base) :
    0 < target ∧ target < T.paperIndex j := by
  exact hasPrior_of_eq_cutting hprior hshape

theorem hasCutLabel_transfer_of_flag_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {j : T.Index} {target : Nat} {kind : CutFlagKind} {base tnew : Time}
    (hlabel : T.get j = cutting kind target base)
    (hflag : flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet tnew) :
    HasCutLabelAt Time target tnew := by
  have hform_old : HasForm (cutting kind target) (T.get j) :=
    ⟨T.consistent j, ⟨base, hlabel⟩⟩
  have hform_new := flagOf_transfer_hasForm cuttingFlagSet
    (cutting_mem kind target) hform_old hflag
  rcases hform_new.2 with ⟨newBase, hnew⟩
  exact ⟨kind, newBase, hnew⟩

/-- Lemma 5.2.1 (Flag of non-initial index): if `T` is derived and `j` is a
non-initial index (`1 < Π[j]`), then the time at `j` carries a cutting flag aimed
at a strictly earlier paper index, i.e. `Π[j] = Q_i⊝` for some `i` with `j > i`.
Proved by induction on the derivation. -/
theorem time_flag {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (d : Derivation Time T) :
    ∀ j : T.Index, 1 < T.paperIndex j → HasPriorCutLabel T j := by
  induction d with
  | init _hpos base _hconsistent =>
    intro j hj
    have hjpos : 0 < j.val := positive_val_of_noninitial hj
    exact
      ⟨j.val, hjpos, Nat.lt_succ_self j.val, CutFlagKind.nextIndex, base j, by
        simp [initPrepath, initTime, Prepath.get, Nat.ne_of_gt hjpos,
          LocatedSemilatticeWithCut.nextIndex]⟩
  | inc _deriv changed hlt hflag hconsistent ih =>
    intro idx hidx
    rename_i Tmid tnew
    change HasPriorCutLabel (Tmid.replace changed tnew hlt.1.1.symm hconsistent) idx
    by_cases hsame : idx = changed
    · have hidxChanged : 1 < Tmid.paperIndex changed := by
        simpa [hsame] using hidx
      have hold := ih changed hidxChanged
      rcases hold with ⟨target, hpos, hltarget, kind, base, hlabel⟩
      have hnew := hasCutLabel_transfer_of_flag_eq hlabel hflag
      exact
        ⟨target, hpos, by simpa [hsame] using hltarget, by
          simpa [Prepath.replace, Prepath.get, hsame] using hnew⟩
    · have hold := ih idx hidx
      rcases hold with ⟨target, hpos, hltarget, hlabel⟩
      exact
        ⟨target, hpos, hltarget, by
          rw [Prepath.replace_get_ne Tmid hsame tnew hlt.1.1.symm hconsistent]
          exact hlabel⟩
  | cutMeIntro _deriv changed introTarget hshape hconsistent ih =>
    intro idx hidx
    rename_i Tmid base
    have hctrl : controller (⋊ introTarget base) =
        controller (Tmid.get changed) := by
      calc
        controller (⋊ introTarget base) = controller base :=
          (⋊ introTarget).controller_preserving base
        _ = controller (↱ introTarget base) :=
          ((↱ introTarget).controller_preserving base).symm
        _ = controller (Tmid.get changed) := by rw [hshape]
    change HasPriorCutLabel (Tmid.replace changed (⋊ introTarget base)
      hctrl hconsistent) idx
    by_cases hsame : idx = changed
    · have hidxChanged : 1 < Tmid.paperIndex changed := by
        simpa [hsame] using hidx
      have hold := ih changed hidxChanged
      have hbounds := hasPrior_of_eq_nextIndex hold hshape
      exact
        ⟨introTarget, hbounds.1, by simpa [hsame] using hbounds.2,
          CutFlagKind.cutMe, base, by
            simp [Prepath.replace, Prepath.get, hsame, LocatedSemilatticeWithCut.cutMe]⟩
    · have hold := ih idx hidx
      rcases hold with ⟨target, hpos, hltarget, hlabel⟩
      exact
        ⟨target, hpos, hltarget, by
          rw [Prepath.replace_get_ne Tmid hsame (⋊ introTarget base)
            hctrl hconsistent]
          exact hlabel⟩
  | cutYouIntro _deriv changed introTarget hshape hconsistent ih =>
    intro idx hidx
    rename_i Tmid base
    have hctrl : controller (⋉ introTarget base) =
        controller (Tmid.get changed) := by
      calc
        controller (⋉ introTarget base) = controller base :=
          (⋉ introTarget).controller_preserving base
        _ = controller (↱ introTarget base) :=
          ((↱ introTarget).controller_preserving base).symm
        _ = controller (Tmid.get changed) := by rw [hshape]
    change HasPriorCutLabel (Tmid.replace changed (⋉ introTarget base)
      hctrl hconsistent) idx
    by_cases hsame : idx = changed
    · have hidxChanged : 1 < Tmid.paperIndex changed := by
        simpa [hsame] using hidx
      have hold := ih changed hidxChanged
      have hbounds := hasPrior_of_eq_nextIndex hold hshape
      exact
        ⟨introTarget, hbounds.1, by simpa [hsame] using hbounds.2,
          CutFlagKind.cutYou, base, by
            simp [Prepath.replace, Prepath.get, hsame, LocatedSemilatticeWithCut.cutYou]⟩
    · have hold := ih idx hidx
      rcases hold with ⟨target, hpos, hltarget, hlabel⟩
      exact
        ⟨target, hpos, hltarget, by
          rw [Prepath.replace_get_ne Tmid hsame (⋉ introTarget base)
            hctrl hconsistent]
          exact hlabel⟩
  | cut _deriv hij hjk hk _hj _hi hconsistent ih =>
    intro idx hidx
    rename_i Tmid i j k _ti _tj tk
    have hctrl : controller (↱ (Tmid.paperIndex i) tk) =
        controller (Tmid.get k) := by
      calc
        controller (↱ (Tmid.paperIndex i) tk) =
            controller tk :=
          (↱ (Tmid.paperIndex i)).controller_preserving tk
        _ = controller (⋉ (Tmid.paperIndex j) tk) :=
          ((⋉ (Tmid.paperIndex j)).controller_preserving tk).symm
        _ = controller (Tmid.get k) := by rw [hk]
    change HasPriorCutLabel (Tmid.replace k (↱ (Tmid.paperIndex i) tk)
      hctrl hconsistent) idx
    by_cases hsame : idx = k
    · have hik : i.val < k.val := Nat.lt_trans hij hjk
      exact
        ⟨Tmid.paperIndex i, Nat.succ_pos i.val,
          by simpa [Prepath.paperIndex, hsame] using Nat.succ_lt_succ hik,
          CutFlagKind.nextIndex, tk, by
            simp [Prepath.replace, Prepath.get, hsame,
              LocatedSemilatticeWithCut.nextIndex]⟩
    · have hold := ih idx hidx
      rcases hold with ⟨target, hpos, hltarget, hlabel⟩
      exact
        ⟨target, hpos, hltarget, by
          rw [Prepath.replace_get_ne Tmid hsame (↱ (Tmid.paperIndex i) tk)
            hctrl hconsistent]
          exact hlabel⟩

/-- Lemma 5.2.1, flag-membership form: a non-initial derived index `j` has a
defined cutting flag, i.e. `flagOf cuttingFlagSet (T.get j)` is `some Q` for a
member `Q` of the cutting flag set. -/
theorem time_flag_flagOf_some {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (d : Derivation Time T) (j : T.Index) (hj : 1 < T.paperIndex j) :
    ∃ Q : {Q : Flag Time // cuttingFlagSet.member Q},
      flagOf cuttingFlagSet (T.get j) = some Q := by
  rcases time_flag d j hj with ⟨target, _hpos, _hltarget, kind, base, hlabel⟩
  let Q : {Q : Flag Time // cuttingFlagSet.member Q} :=
    ⟨cutting kind target, cutting_mem kind target⟩
  have hform : HasForm Q.1 (T.get j) :=
    ⟨T.consistent j, ⟨base, hlabel⟩⟩
  exact ⟨Q, flagOf_eq_some_of_hasForm cuttingFlagSet Q.2 hform⟩

/-- Lemma 5.2.1, with the target `i` presented as an actual earlier index of `T`:
a non-initial index `j` has some index `i` with `i.val < j.val` whose paper index
`Π[i]` labels the time at `j`. -/
theorem time_flag_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (d : Derivation Time T) :
    ∀ j : T.Index, 1 < T.paperIndex j →
      ∃ i : T.Index, i.val < j.val ∧
        HasCutLabelAt Time (T.paperIndex i) (T.get j) := by
  intro j hj
  rcases time_flag d j hj with ⟨target, hpos, hltarget, hlabel⟩
  have htarget_le_j : target ≤ j.val := by
    exact Nat.lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hltarget)
  let i : T.Index :=
    ⟨target - 1,
      Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.sub_le target 1) htarget_le_j) j.isLt⟩
  have hi_lt_j : i.val < j.val := by
    exact Nat.lt_of_lt_of_le (Nat.sub_lt hpos Nat.zero_lt_one) htarget_le_j
  have hi_paper : T.paperIndex i = target := by
    simp [i, Prepath.paperIndex, Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
  exact ⟨i, hi_lt_j, by simpa [hi_paper] using hlabel⟩

/--
Lemma 5.2.1, in derivation notation: a non-initial index `j` has a cutting flag on
`d.get j` aimed at a paper index `target` with `0 < target < Π[j]`.
-/
theorem derivation_time_flag {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (d : Derivation Time T) :
    ∀ j : d.Index, 1 < T.paperIndex j →
      ∃ target : Nat, 0 < target ∧ target < T.paperIndex j ∧
        HasCutLabelAt Time target (d.get j) := by
  intro j hj
  simpa [Derivation.get] using time_flag d j hj

/--
Lemma 5.2.1, in derivation notation, flag-membership form: a non-initial index has
a defined cutting flag on `d.get j`.
-/
theorem derivation_time_flag_flagOf_some {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (d : Derivation Time T) :
    ∀ j : d.Index, 1 < T.paperIndex j →
      ∃ Q : {Q : Flag Time // cuttingFlagSet.member Q},
        flagOf cuttingFlagSet (d.get j) = some Q := by
  intro j hj
  simpa [Derivation.get] using time_flag_flagOf_some d j hj

/--
Lemma 5.2.1, in derivation notation, with the target represented as an actual
earlier index `i` of the derivation.
-/
theorem derivation_time_flag_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (d : Derivation Time T) :
    ∀ j : d.Index, 1 < T.paperIndex j →
      ∃ i : d.Index, i.val < j.val ∧
        HasCutLabelAt Time (T.paperIndex i) (d.get j) := by
  intro j hj
  simpa [Derivation.get] using time_flag_indexed d j hj

/--
Consequence of Proposition 5.2.3 (Affine cuts): since a derivation contains at most
one cut centred on a given index, two cuts sharing the center `cutJ` must have the
same lower endpoint (`cutI = cutI'`).
-/
theorem containsCut_same_center_lower_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutK' cutJ cutI cutI' : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    (hcut' : ContainsCut deriv cutK' cutJ cutI') :
    cutI = cutI' := by
  rcases containsCut_indices hcut with
    ⟨_upper, center, _lower, _hupper, hcenter, _hlower, _hlower_center,
      _hcenter_upper⟩
  rcases containsCut_center_hasCutMe hcut center hcenter with ⟨base, hcutMe⟩
  rcases containsCut_center_hasCutMe hcut' center hcenter with ⟨base', hcutMe'⟩
  have hleft : ConsistentTime (⋊ cutI base) := by
    rw [← hcutMe]
    exact T.consistent center
  have hright : ConsistentTime (⋊ cutI' base') := by
    rw [← hcutMe']
    exact T.consistent center
  exact flag_target_eq_of_eq_consistent hleft hright
    (hcutMe.symm.trans hcutMe')

/--
Indexed form of the same-center lower-endpoint consequence of Proposition 5.2.3:
two cuts sharing the center index have the same lower index.
-/
theorem containsCut_same_center_lower_index_eq
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {upper upper' center lower lower' : T.Index}
    (hcut : ContainsCut deriv (T.paperIndex upper) (T.paperIndex center)
      (T.paperIndex lower))
    (hcut' : ContainsCut deriv (T.paperIndex upper') (T.paperIndex center)
      (T.paperIndex lower')) :
    lower = lower' := by
  have hpaper : T.paperIndex lower = T.paperIndex lower' :=
    containsCut_same_center_lower_eq hcut hcut'
  apply Fin.ext
  exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hpaper)

end ConsistentHistories.Routes.PathProperties.FlagNesting
