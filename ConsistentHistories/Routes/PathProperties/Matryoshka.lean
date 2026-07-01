import ConsistentHistories.Routes.PathProperties.InactiveCuts

/-!
Paper section 5.4: Matryoshka cut geometry.

Two cuts in a derivation can never cross: they are disjoint, equal, or nested,
and every index inside a cut interval is itself the center of a nested cut. This
file formalizes Proposition 5.4.1 (Matryoshka Cuts), Corollary 5.4.3 (cuts are
ordered by derivation), and Corollary 5.4.4 (cuts nest). Corollary 5.1.3 (Cut
implies ⋊) is also proved here, since its proof uses the Matryoshka geometry
established below.
-/

namespace ConsistentHistories.Routes.PathProperties.Matryoshka

open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Routes.Paths.Circuits
open ConsistentHistories.Routes.PathProperties.CutmePersistence
open ConsistentHistories.Routes.PathProperties.InactiveCuts

universe u v

/--
Lower-side case of Proposition 5.4.1 (Matryoshka Cuts): for a Cut with center
`j` and lower endpoint `i`, any index `i'` with `j > i' > i` is the center of a
nested Cut `(Cut_{j'',i',i''})` with `j ≥ j'' > i' > i'' ≥ i`.
-/
theorem matryoshka_cuts_lower_side {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    {outerCenter outerLower inner : T.Index}
    (hcenter : T.paperIndex outerCenter = cutJ)
    (hlower : T.paperIndex outerLower = cutI)
    (hlower_inner : outerLower.val < inner.val)
    (hinner_center : inner.val < outerCenter.val) :
    ∃ cutUpper cutLower : T.Index,
      cutUpper.val ≤ outerCenter.val ∧ outerLower.val ≤ cutLower.val ∧
      cutLower.val < inner.val ∧ inner.val < cutUpper.val ∧
      ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex inner)
        (T.paperIndex cutLower) := by
  rcases containsCut_center_hasCutMe hcut outerCenter hcenter with ⟨base, hcutMe⟩
  have hlabel : HasCutLabelAt Time (T.paperIndex outerLower) (T.get outerCenter) := by
    exact ⟨CutFlagKind.cutMe, base, by simpa [hlower] using hcutMe⟩
  exact inactiveBetween_implies_containsCut_center deriv
    ⟨hlower_inner, hinner_center, hlabel⟩

/--
Upper-side case of Proposition 5.4.1 (Matryoshka Cuts): for a Cut with center
`j` and upper endpoint `k`, any index `i'` with `k > i' > j` is the center of a
nested Cut `(Cut_{j'',i',i''})` with `k ≥ j'' > i' > i'' ≥ j`.
-/
theorem matryoshka_cuts_upper_side {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat},
      ContainsCut deriv cutK cutJ cutI →
        ∀ {outerUpper outerCenter inner : T.Index},
          T.paperIndex outerUpper = cutK →
          T.paperIndex outerCenter = cutJ →
          outerCenter.val < inner.val →
          inner.val < outerUpper.val →
          ∃ cutUpper cutLower : T.Index,
            cutUpper.val ≤ outerUpper.val ∧ outerCenter.val ≤ cutLower.val ∧
            cutLower.val < inner.val ∧ inner.val < cutUpper.val ∧
            ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex inner)
              (T.paperIndex cutLower) := by
  intro T deriv cutK cutJ cutI hcut
  induction hcut with
  | here deriv hij hjk hk hj hi hconsistent =>
      intro outerUpper outerCenter inner hupper hcenter hcenter_inner hinner_upper
      rename_i Tmid i j k ti tj tk
      have hupper_eq : outerUpper = k := by
        exact Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hupper))
      have hcenter_eq : outerCenter = j := by
        exact Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hcenter))
      subst outerUpper
      subst outerCenter
      have hlabel : HasCutLabelAt Time (Tmid.paperIndex j) (Tmid.get k) := by
        exact ⟨CutFlagKind.cutYou, tk, by
          simpa [LocatedSemilatticeWithCut.cutYou] using hk⟩
      rcases inactiveBetween_implies_containsCut_center deriv
          ⟨hcenter_inner, hinner_upper, hlabel⟩ with
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper, hnested⟩
      exact
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper,
          ContainsCut.cutStep hnested hij hjk hk hj hi hconsistent⟩
  | inc h changed hlt hflag hconsistent ih =>
      intro outerUpper outerCenter inner hupper hcenter hcenter_inner hinner_upper
      rename_i Tmid deriv cutK cutJ cutI tnew
      rcases ih (outerUpper := outerUpper) (outerCenter := outerCenter) (inner := inner)
          (by simpa [Prepath.paperIndex] using hupper)
          (by simpa [Prepath.paperIndex] using hcenter)
          hcenter_inner hinner_upper with
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper, hnested⟩
      exact
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper, ContainsCut.inc hnested changed hlt hflag hconsistent⟩
  | cutMeIntro h changed introTarget hshape hconsistent ih =>
      intro outerUpper outerCenter inner hupper hcenter hcenter_inner hinner_upper
      rename_i Tmid deriv cutK cutJ cutI base
      rcases ih (outerUpper := outerUpper) (outerCenter := outerCenter) (inner := inner)
          (by simpa [Prepath.paperIndex] using hupper)
          (by simpa [Prepath.paperIndex] using hcenter)
          hcenter_inner hinner_upper with
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper, hnested⟩
      exact
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper,
          ContainsCut.cutMeIntro hnested changed introTarget hshape hconsistent⟩
  | cutYouIntro h changed introTarget hshape hconsistent ih =>
      intro outerUpper outerCenter inner hupper hcenter hcenter_inner hinner_upper
      rename_i Tmid deriv cutK cutJ cutI base
      rcases ih (outerUpper := outerUpper) (outerCenter := outerCenter) (inner := inner)
          (by simpa [Prepath.paperIndex] using hupper)
          (by simpa [Prepath.paperIndex] using hcenter)
          hcenter_inner hinner_upper with
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper, hnested⟩
      exact
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper,
          ContainsCut.cutYouIntro hnested changed introTarget hshape hconsistent⟩
  | cutStep h hij hjk hk hj hi hconsistent ih =>
      intro outerUpper outerCenter inner hupper hcenter hcenter_inner hinner_upper
      rename_i Tmid deriv cutK cutJ cutI i j k ti tj tk
      rcases ih (outerUpper := outerUpper) (outerCenter := outerCenter) (inner := inner)
          (by simpa [Prepath.paperIndex] using hupper)
          (by simpa [Prepath.paperIndex] using hcenter)
          hcenter_inner hinner_upper with
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper, hnested⟩
      exact
        ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
          hinner_cutUpper,
          ContainsCut.cutStep hnested hij hjk hk hj hi hconsistent⟩

/--
Lower-side case of Proposition 5.4.1 (Matryoshka Cuts), stated with the paper
indices of the inner center and cut endpoints rather than raw Lean indices.
-/
theorem matryoshka_cuts_lower_side_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    {inner : T.Index}
    (hlower_inner : cutI < T.paperIndex inner)
    (hinner_center : T.paperIndex inner < cutJ) :
    ∃ cutUpper cutLower : T.Index,
      T.paperIndex cutUpper ≤ cutJ ∧ cutI ≤ T.paperIndex cutLower ∧
      T.paperIndex cutLower < T.paperIndex inner ∧
      T.paperIndex inner < T.paperIndex cutUpper ∧
      ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex inner)
        (T.paperIndex cutLower) := by
  rcases containsCut_indices hcut with
    ⟨_outerUpper, outerCenter, outerLower, _hupper, hcenter, hlower, _hij, _hjk⟩
  have hlower_inner_val : outerLower.val < inner.val := by
    have hlower_eq : outerLower.val + 1 = cutI := by
      simpa [Prepath.paperIndex] using hlower
    have hinner_eq : inner.val + 1 = T.paperIndex inner := by
      rfl
    omega
  have hinner_center_val : inner.val < outerCenter.val := by
    have hcenter_eq : outerCenter.val + 1 = cutJ := by
      simpa [Prepath.paperIndex] using hcenter
    have hinner_eq : inner.val + 1 = T.paperIndex inner := by
      rfl
    omega
  rcases matryoshka_cuts_lower_side deriv hcut hcenter hlower
      hlower_inner_val hinner_center_val with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested⟩
  exact
    ⟨cutUpper, cutLower,
      by
        have hcenter_eq : outerCenter.val + 1 = cutJ := by
          simpa [Prepath.paperIndex] using hcenter
        change cutUpper.val + 1 ≤ cutJ
        rw [← hcenter_eq]
        exact Nat.succ_le_succ hupper_bound,
      by
        have hlower_eq : outerLower.val + 1 = cutI := by
          simpa [Prepath.paperIndex] using hlower
        change cutI ≤ cutLower.val + 1
        rw [← hlower_eq]
        exact Nat.succ_le_succ hlower_bound,
      by
        exact Nat.succ_lt_succ hcutLower_inner,
      by
        exact Nat.succ_lt_succ hinner_cutUpper,
      hnested⟩

/--
Upper-side case of Proposition 5.4.1 (Matryoshka Cuts), stated with the paper
indices of the inner center and cut endpoints rather than raw Lean indices.
-/
theorem matryoshka_cuts_upper_side_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    {inner : T.Index}
    (hcenter_inner : cutJ < T.paperIndex inner)
    (hinner_upper : T.paperIndex inner < cutK) :
    ∃ cutUpper cutLower : T.Index,
      T.paperIndex cutUpper ≤ cutK ∧ cutJ ≤ T.paperIndex cutLower ∧
      T.paperIndex cutLower < T.paperIndex inner ∧
      T.paperIndex inner < T.paperIndex cutUpper ∧
      ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex inner)
        (T.paperIndex cutLower) := by
  rcases containsCut_indices hcut with
    ⟨outerUpper, outerCenter, _outerLower, hupper, hcenter, _hlower, _hij, _hjk⟩
  have hcenter_inner_val : outerCenter.val < inner.val := by
    have hcenter_eq : outerCenter.val + 1 = cutJ := by
      simpa [Prepath.paperIndex] using hcenter
    have hinner_eq : inner.val + 1 = T.paperIndex inner := by
      rfl
    omega
  have hinner_upper_val : inner.val < outerUpper.val := by
    have hupper_eq : outerUpper.val + 1 = cutK := by
      simpa [Prepath.paperIndex] using hupper
    have hinner_eq : inner.val + 1 = T.paperIndex inner := by
      rfl
    omega
  rcases matryoshka_cuts_upper_side hcut hupper hcenter
      hcenter_inner_val hinner_upper_val with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested⟩
  exact
    ⟨cutUpper, cutLower,
      by
        have hupper_eq : outerUpper.val + 1 = cutK := by
          simpa [Prepath.paperIndex] using hupper
        change cutUpper.val + 1 ≤ cutK
        rw [← hupper_eq]
        exact Nat.succ_le_succ hupper_bound,
      by
        have hcenter_eq : outerCenter.val + 1 = cutJ := by
          simpa [Prepath.paperIndex] using hcenter
        change cutJ ≤ cutLower.val + 1
        rw [← hcenter_eq]
        exact Nat.succ_le_succ hlower_bound,
      by
        exact Nat.succ_lt_succ hcutLower_inner,
      by
        exact Nat.succ_lt_succ hinner_cutUpper,
      hnested⟩

/--
Proposition 5.4.1 (Matryoshka Cuts): both the lower-side and upper-side cases
together. The nested Cut is asserted to exist; the paper's parenthetical
uniqueness of that Cut is Proposition 5.2.3 (Affine cuts).
-/
theorem matryoshka_cuts_exist {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) :
    (∀ {inner : T.Index}, cutI < T.paperIndex inner → T.paperIndex inner < cutJ →
      ∃ cutUpper cutLower : T.Index,
        T.paperIndex cutUpper ≤ cutJ ∧ cutI ≤ T.paperIndex cutLower ∧
        T.paperIndex cutLower < T.paperIndex inner ∧
        T.paperIndex inner < T.paperIndex cutUpper ∧
        ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex inner)
          (T.paperIndex cutLower)) ∧
    (∀ {inner : T.Index}, cutJ < T.paperIndex inner → T.paperIndex inner < cutK →
      ∃ cutUpper cutLower : T.Index,
        T.paperIndex cutUpper ≤ cutK ∧ cutJ ≤ T.paperIndex cutLower ∧
        T.paperIndex cutLower < T.paperIndex inner ∧
        T.paperIndex inner < T.paperIndex cutUpper ∧
        ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex inner)
          (T.paperIndex cutLower)) := by
  constructor
  · intro inner hlower_inner hinner_center
    exact matryoshka_cuts_lower_side_indexed deriv hcut hlower_inner hinner_center
  · intro inner hcenter_inner hinner_upper
    exact matryoshka_cuts_upper_side_indexed deriv hcut hcenter_inner hinner_upper

/-- Lower-side case of Proposition 5.4.1 (Matryoshka Cuts), projected out of
`matryoshka_cuts_exist`. -/
theorem matryoshka_cuts_exist_lower {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) :
    ∀ {inner : T.Index}, cutI < T.paperIndex inner → T.paperIndex inner < cutJ →
      ∃ cutUpper cutLower : T.Index,
        T.paperIndex cutUpper ≤ cutJ ∧ cutI ≤ T.paperIndex cutLower ∧
        T.paperIndex cutLower < T.paperIndex inner ∧
        T.paperIndex inner < T.paperIndex cutUpper ∧
        ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex inner)
          (T.paperIndex cutLower) :=
  (matryoshka_cuts_exist deriv hcut).1

/-- Upper-side case of Proposition 5.4.1 (Matryoshka Cuts), projected out of
`matryoshka_cuts_exist`. -/
theorem matryoshka_cuts_exist_upper {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) :
    ∀ {inner : T.Index}, cutJ < T.paperIndex inner → T.paperIndex inner < cutK →
      ∃ cutUpper cutLower : T.Index,
        T.paperIndex cutUpper ≤ cutK ∧ cutJ ≤ T.paperIndex cutLower ∧
        T.paperIndex cutLower < T.paperIndex inner ∧
        T.paperIndex inner < T.paperIndex cutUpper ∧
        ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex inner)
          (T.paperIndex cutLower) :=
  (matryoshka_cuts_exist deriv hcut).2

/--
Lower-side case of Proposition 5.4.1 (Matryoshka Cuts) established inside the
premise of the outer Cut: every index strictly between the outer lower endpoint
and the outer center is already the center of a nested Cut in that premise. The
nested Cut is obtained from Proposition 5.3.3 (Inactive implies Cut).
-/
theorem cutPrefixData_lower_side_nested_before {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    {inner : data.base.Index}
    (hlower_inner : cutI < data.base.paperIndex inner)
    (hinner_center : data.base.paperIndex inner < cutJ) :
    ∃ cutUpper cutLower : data.base.Index,
      data.base.paperIndex cutUpper ≤ cutJ ∧
      cutI ≤ data.base.paperIndex cutLower ∧
      data.base.paperIndex cutLower < data.base.paperIndex inner ∧
      data.base.paperIndex inner < data.base.paperIndex cutUpper ∧
      ContainsCut data.baseDeriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
  have hlower_inner_val : data.idxI.val < inner.val := by
    have hpaper :
        data.base.paperIndex data.idxI < data.base.paperIndex inner := by
      simpa [data.cutI_eq] using hlower_inner
    exact Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hpaper)
  have hinner_center_val : inner.val < data.idxJ.val := by
    have hpaper :
        data.base.paperIndex inner < data.base.paperIndex data.idxJ := by
      simpa [data.cutJ_eq] using hinner_center
    exact Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hpaper)
  have hlabel :
      HasCutLabelAt Time (data.base.paperIndex data.idxI)
        (data.base.get data.idxJ) := by
    rw [data.hj]
    exact
      hasCutLabelAt_cutMe (Time := Time) (data.base.paperIndex data.idxI)
        (data.tj # (⋉ (data.base.paperIndex data.idxJ) data.tk))
  rcases inactiveBetween_implies_containsCut_center data.baseDeriv
      ⟨hlower_inner_val, hinner_center_val, hlabel⟩ with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested⟩
  exact
    ⟨cutUpper, cutLower,
      by
        calc
          data.base.paperIndex cutUpper ≤ data.base.paperIndex data.idxJ :=
            Nat.succ_le_succ hupper_bound
          _ = cutJ := data.cutJ_eq.symm,
      by
        calc
          cutI = data.base.paperIndex data.idxI := data.cutI_eq
          _ ≤ data.base.paperIndex cutLower := Nat.succ_le_succ hlower_bound,
      Nat.succ_lt_succ hcutLower_inner,
      Nat.succ_lt_succ hinner_cutUpper,
      hnested⟩

/--
Upper-side case of Proposition 5.4.1 (Matryoshka Cuts) established inside the
premise of the outer Cut: every index strictly between the outer center and
upper endpoint is already the center of a nested Cut in that premise. The nested
Cut is obtained from Proposition 5.3.3 (Inactive implies Cut).
-/
theorem cutPrefixData_upper_side_nested_before {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    {inner : data.base.Index}
    (hcenter_inner : cutJ < data.base.paperIndex inner)
    (hinner_upper : data.base.paperIndex inner < cutK) :
    ∃ cutUpper cutLower : data.base.Index,
      data.base.paperIndex cutUpper ≤ cutK ∧
      cutJ ≤ data.base.paperIndex cutLower ∧
      data.base.paperIndex cutLower < data.base.paperIndex inner ∧
      data.base.paperIndex inner < data.base.paperIndex cutUpper ∧
      ContainsCut data.baseDeriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
  have hcenter_inner_val : data.idxJ.val < inner.val := by
    have hpaper :
        data.base.paperIndex data.idxJ < data.base.paperIndex inner := by
      simpa [data.cutJ_eq] using hcenter_inner
    exact Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hpaper)
  have hinner_upper_val : inner.val < data.idxK.val := by
    have hpaper :
        data.base.paperIndex inner < data.base.paperIndex data.idxK := by
      simpa [data.cutK_eq] using hinner_upper
    exact Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hpaper)
  have hlabel :
      HasCutLabelAt Time (data.base.paperIndex data.idxJ)
        (data.base.get data.idxK) := by
    rw [data.hk]
    exact hasCutLabelAt_cutYou (Time := Time) (data.base.paperIndex data.idxJ) data.tk
  rcases inactiveBetween_implies_containsCut_center data.baseDeriv
      ⟨hcenter_inner_val, hinner_upper_val, hlabel⟩ with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested⟩
  exact
    ⟨cutUpper, cutLower,
      by
        calc
          data.base.paperIndex cutUpper ≤ data.base.paperIndex data.idxK :=
            Nat.succ_le_succ hupper_bound
          _ = cutK := data.cutK_eq.symm,
      by
        calc
          cutJ = data.base.paperIndex data.idxJ := data.cutJ_eq
          _ ≤ data.base.paperIndex cutLower := Nat.succ_le_succ hlower_bound,
      Nat.succ_lt_succ hcutLower_inner,
      Nat.succ_lt_succ hinner_cutUpper,
      hnested⟩

/--
Lower-side case of Proposition 5.4.1 (Matryoshka Cuts): the nested Cut already
present in the premise of the outer Cut has the same lower endpoint as any final
Cut centered at that same inner index. The lower endpoints agree by Proposition
5.2.3 (Affine cuts), which forces cuts with a common center to share endpoints.
-/
theorem cutPrefixData_lower_side_nested_before_same_lower {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI innerK innerJ innerI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    {inner : data.base.Index}
    (hinner_eq : innerJ = data.base.paperIndex inner)
    (hlower_inner : cutI < innerJ)
    (hinner_center : innerJ < cutJ) :
    ∃ cutUpper cutLower : data.base.Index,
      data.base.paperIndex cutUpper ≤ cutJ ∧
      cutI ≤ data.base.paperIndex cutLower ∧
      data.base.paperIndex cutLower < data.base.paperIndex inner ∧
      data.base.paperIndex inner < data.base.paperIndex cutUpper ∧
      ContainsCut data.baseDeriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) ∧
      innerI = data.base.paperIndex cutLower := by
  rcases cutPrefixData_lower_side_nested_before data
      (by simpa [hinner_eq] using hlower_inner)
      (by simpa [hinner_eq] using hinner_center) with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested⟩
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hnested_cut :
      ContainsCut dcut (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
    exact ContainsCut.cutStep hnested data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hnested_final_base :
      ContainsCut deriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
    exact containsCut_of_initialPrefix data.hprefix hnested_cut
  have hnested_final :
      ContainsCut deriv (data.base.paperIndex cutUpper) innerJ
        (data.base.paperIndex cutLower) := by
    simpa [hinner_eq] using hnested_final_base
  have hlower_eq : innerI = data.base.paperIndex cutLower :=
    ConsistentHistories.Routes.PathProperties.FlagNesting.containsCut_same_center_lower_eq
      hinner hnested_final
  exact
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested, hlower_eq⟩

/--
Upper-side case of Proposition 5.4.1 (Matryoshka Cuts): the nested Cut already
present in the premise of the outer Cut has the same lower endpoint as any final
Cut centered at that same inner index. The lower endpoints agree by Proposition
5.2.3 (Affine cuts), which forces cuts with a common center to share endpoints.
-/
theorem cutPrefixData_upper_side_nested_before_same_lower {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI innerK innerJ innerI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    {inner : data.base.Index}
    (hinner_eq : innerJ = data.base.paperIndex inner)
    (hcenter_inner : cutJ < innerJ)
    (hinner_upper : innerJ < cutK) :
    ∃ cutUpper cutLower : data.base.Index,
      data.base.paperIndex cutUpper ≤ cutK ∧
      cutJ ≤ data.base.paperIndex cutLower ∧
      data.base.paperIndex cutLower < data.base.paperIndex inner ∧
      data.base.paperIndex inner < data.base.paperIndex cutUpper ∧
      ContainsCut data.baseDeriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) ∧
      innerI = data.base.paperIndex cutLower := by
  rcases cutPrefixData_upper_side_nested_before data
      (by simpa [hinner_eq] using hcenter_inner)
      (by simpa [hinner_eq] using hinner_upper) with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested⟩
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hnested_cut :
      ContainsCut dcut (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
    exact ContainsCut.cutStep hnested data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hnested_final_base :
      ContainsCut deriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
    exact containsCut_of_initialPrefix data.hprefix hnested_cut
  have hnested_final :
      ContainsCut deriv (data.base.paperIndex cutUpper) innerJ
        (data.base.paperIndex cutLower) := by
    simpa [hinner_eq] using hnested_final_base
  have hlower_eq : innerI = data.base.paperIndex cutLower :=
    ConsistentHistories.Routes.PathProperties.FlagNesting.containsCut_same_center_lower_eq
      hinner hnested_final
  exact
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested, hlower_eq⟩

/--
Lower-side case of Proposition 5.4.1 (Matryoshka Cuts): the nested Cut already
present in the premise of the outer Cut has the same upper and lower endpoints
as any final Cut centered at that same inner index. Both endpoints agree by
Proposition 5.2.3 (Affine cuts).
-/
theorem cutPrefixData_lower_side_nested_before_same_endpoints {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI innerK innerJ innerI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    {inner : data.base.Index}
    (hinner_eq : innerJ = data.base.paperIndex inner)
    (hlower_inner : cutI < innerJ)
    (hinner_center : innerJ < cutJ) :
    ∃ cutUpper cutLower : data.base.Index,
      data.base.paperIndex cutUpper ≤ cutJ ∧
      cutI ≤ data.base.paperIndex cutLower ∧
      data.base.paperIndex cutLower < data.base.paperIndex inner ∧
      data.base.paperIndex inner < data.base.paperIndex cutUpper ∧
      ContainsCut data.baseDeriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) ∧
      innerK = data.base.paperIndex cutUpper ∧
      innerI = data.base.paperIndex cutLower := by
  rcases cutPrefixData_lower_side_nested_before data
      (by simpa [hinner_eq] using hlower_inner)
      (by simpa [hinner_eq] using hinner_center) with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested⟩
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hnested_cut :
      ContainsCut dcut (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
    exact ContainsCut.cutStep hnested data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hnested_final_base :
      ContainsCut deriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
    exact containsCut_of_initialPrefix data.hprefix hnested_cut
  have hnested_final :
      ContainsCut deriv (data.base.paperIndex cutUpper) innerJ
        (data.base.paperIndex cutLower) := by
    simpa [hinner_eq] using hnested_final_base
  rcases containsCut_same_center_endpoints_eq hinner hnested_final with
    ⟨hupper_eq, hlower_eq⟩
  exact
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested, hupper_eq, hlower_eq⟩

/--
Upper-side case of Proposition 5.4.1 (Matryoshka Cuts): the nested Cut already
present in the premise of the outer Cut has the same upper and lower endpoints
as any final Cut centered at that same inner index. Both endpoints agree by
Proposition 5.2.3 (Affine cuts).
-/
theorem cutPrefixData_upper_side_nested_before_same_endpoints {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI innerK innerJ innerI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    {inner : data.base.Index}
    (hinner_eq : innerJ = data.base.paperIndex inner)
    (hcenter_inner : cutJ < innerJ)
    (hinner_upper : innerJ < cutK) :
    ∃ cutUpper cutLower : data.base.Index,
      data.base.paperIndex cutUpper ≤ cutK ∧
      cutJ ≤ data.base.paperIndex cutLower ∧
      data.base.paperIndex cutLower < data.base.paperIndex inner ∧
      data.base.paperIndex inner < data.base.paperIndex cutUpper ∧
      ContainsCut data.baseDeriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) ∧
      innerK = data.base.paperIndex cutUpper ∧
      innerI = data.base.paperIndex cutLower := by
  rcases cutPrefixData_upper_side_nested_before data
      (by simpa [hinner_eq] using hcenter_inner)
      (by simpa [hinner_eq] using hinner_upper) with
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested⟩
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hnested_cut :
      ContainsCut dcut (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
    exact ContainsCut.cutStep hnested data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hnested_final_base :
      ContainsCut deriv (data.base.paperIndex cutUpper)
        (data.base.paperIndex inner) (data.base.paperIndex cutLower) := by
    exact containsCut_of_initialPrefix data.hprefix hnested_cut
  have hnested_final :
      ContainsCut deriv (data.base.paperIndex cutUpper) innerJ
        (data.base.paperIndex cutLower) := by
    simpa [hinner_eq] using hnested_final_base
  rcases containsCut_same_center_endpoints_eq hinner hnested_final with
    ⟨hupper_eq, hlower_eq⟩
  exact
    ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_cutUpper, hnested, hupper_eq, hlower_eq⟩

/--
Step toward Corollary 5.4.3 (Cuts ordered by derivation), base-indexed
lower-endpoint trichotomy. If a final Cut center is represented by an index of
the outer Cut's pre-Cut base, then either it equals the outer center, or by
Proposition 5.4.1 (Matryoshka Cuts) the pre-Cut base already contains the
corresponding lower-side or upper-side nested Cut. In the two strict cases the
final Cut's lower endpoint coincides with the nested Cut's lower endpoint (by
Proposition 5.2.3, Affine cuts). This tracks only the lower endpoint, not the
full ordering of Corollary 5.4.3.
-/
theorem cutPrefixData_inner_center_lower_trichotomy_at_base {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI innerK innerJ innerI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    {inner : data.base.Index}
    (hinner_eq : innerJ = data.base.paperIndex inner)
    (hinside_left : cutI < innerJ)
    (hinside_right : innerJ < cutK) :
    (innerJ = cutJ ∧ innerI = cutI) ∨
      (innerJ < cutJ ∧
        ∃ cutUpper cutLower : data.base.Index,
          data.base.paperIndex cutUpper ≤ cutJ ∧
          cutI ≤ data.base.paperIndex cutLower ∧
          data.base.paperIndex cutLower < innerJ ∧
          innerJ < data.base.paperIndex cutUpper ∧
          ContainsCut data.baseDeriv (data.base.paperIndex cutUpper) innerJ
            (data.base.paperIndex cutLower) ∧
          innerI = data.base.paperIndex cutLower) ∨
      (cutJ < innerJ ∧
        ∃ cutUpper cutLower : data.base.Index,
          data.base.paperIndex cutUpper ≤ cutK ∧
          cutJ ≤ data.base.paperIndex cutLower ∧
          data.base.paperIndex cutLower < innerJ ∧
          innerJ < data.base.paperIndex cutUpper ∧
          ContainsCut data.baseDeriv (data.base.paperIndex cutUpper) innerJ
            (data.base.paperIndex cutLower) ∧
          innerI = data.base.paperIndex cutLower) := by
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have houter_cut : ContainsCut dcut cutK cutJ cutI := by
    have hhere :
        ContainsCut dcut (data.base.paperIndex data.idxK)
          (data.base.paperIndex data.idxJ) (data.base.paperIndex data.idxI) := by
      exact ContainsCut.here data.baseDeriv data.hij data.hjk data.hk data.hj
        data.hi data.hconsistent
    simpa [data.cutK_eq, data.cutJ_eq, data.cutI_eq] using hhere
  have houter : ContainsCut deriv cutK cutJ cutI :=
    containsCut_of_initialPrefix data.hprefix houter_cut
  rcases Nat.lt_trichotomy innerJ cutJ with hlt | heq | hgt
  · rcases cutPrefixData_lower_side_nested_before_same_lower data hinner
        hinner_eq hinside_left hlt with
      ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
        hinner_cutUpper, hnested, hlower_eq⟩
    exact Or.inr
      (Or.inl
        ⟨hlt, cutUpper, cutLower, hupper_bound, hlower_bound,
          by simpa [hinner_eq] using hcutLower_inner,
          by simpa [hinner_eq] using hinner_cutUpper,
          by simpa [hinner_eq] using hnested,
          hlower_eq⟩)
  · have hinner_cutJ : ContainsCut deriv innerK cutJ innerI := by
      simpa [heq] using hinner
    have hlower_eq : cutI = innerI :=
      ConsistentHistories.Routes.PathProperties.FlagNesting.containsCut_same_center_lower_eq
        houter hinner_cutJ
    exact Or.inl ⟨heq, hlower_eq.symm⟩
  · rcases cutPrefixData_upper_side_nested_before_same_lower data hinner
        hinner_eq hgt hinside_right with
      ⟨cutUpper, cutLower, hupper_bound, hlower_bound, hcutLower_inner,
        hinner_cutUpper, hnested, hlower_eq⟩
    exact Or.inr
      (Or.inr
        ⟨hgt, cutUpper, cutLower, hupper_bound, hlower_bound,
          by simpa [hinner_eq] using hcutLower_inner,
          by simpa [hinner_eq] using hinner_cutUpper,
          by simpa [hinner_eq] using hnested,
          hlower_eq⟩)

/--
Step toward Corollary 5.4.3 (Cuts ordered by derivation), final-root-indexed
lower-endpoint trichotomy. This removes the caller-supplied base-index
hypothesis from `cutPrefixData_inner_center_lower_trichotomy_at_base` by
extracting the inner center index from the final `ContainsCut` occurrence and
casting it back through the outer Cut prefix length equality. It still tracks
only the lower endpoint, not the full ordering of Corollary 5.4.3.
-/
theorem cutPrefixData_inner_center_lower_trichotomy {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI innerK innerJ innerI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hinside_left : cutI < innerJ)
    (hinside_right : innerJ < cutK) :
    (innerJ = cutJ ∧ innerI = cutI) ∨
      (innerJ < cutJ ∧
        ∃ cutUpper cutLower : data.base.Index,
          data.base.paperIndex cutUpper ≤ cutJ ∧
          cutI ≤ data.base.paperIndex cutLower ∧
          data.base.paperIndex cutLower < innerJ ∧
          innerJ < data.base.paperIndex cutUpper ∧
          ContainsCut data.baseDeriv (data.base.paperIndex cutUpper) innerJ
            (data.base.paperIndex cutLower) ∧
          innerI = data.base.paperIndex cutLower) ∨
      (cutJ < innerJ ∧
        ∃ cutUpper cutLower : data.base.Index,
          data.base.paperIndex cutUpper ≤ cutK ∧
          cutJ ≤ data.base.paperIndex cutLower ∧
          data.base.paperIndex cutLower < innerJ ∧
          innerJ < data.base.paperIndex cutUpper ∧
          ContainsCut data.baseDeriv (data.base.paperIndex cutUpper) innerJ
            (data.base.paperIndex cutLower) ∧
          innerI = data.base.paperIndex cutLower) := by
  rcases containsCut_indices hinner with
    ⟨_innerUpper, innerCenter, _innerLower, _hupper, hcenter, _hlower, _hij, _hjk⟩
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hbase_length_eq : data.base.length = T.length := by
    calc
      data.base.length = (Derivation.root dcut).length := by rfl
      _ = T.length := data.hprefix.length_eq
  let innerBase : data.base.Index := Fin.cast hbase_length_eq.symm innerCenter
  have hinner_eq : innerJ = data.base.paperIndex innerBase := by
    rw [← hcenter]
    simp [innerBase, Prepath.paperIndex]
  exact
    cutPrefixData_inner_center_lower_trichotomy_at_base data hinner hinner_eq
      hinside_left hinside_right

/--
Step toward Corollary 5.4.3 (Cuts ordered by derivation). From a plain outer
`ContainsCut`, this exposes a prefix ending in that outer Cut and then applies
the lower-endpoint trichotomy. It still tracks only the prefix nested Cut and
its lower endpoint, not the full ordering of Corollary 5.4.3.
-/
theorem containsCut_inner_center_prefix_lower_trichotomy {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hinside_left : cutI < innerJ)
    (hinside_right : innerJ < cutK) :
    ∃ data : CutPrefixData deriv cutK cutJ cutI,
      (innerJ = cutJ ∧ innerI = cutI) ∨
        (innerJ < cutJ ∧
          ∃ cutUpper cutLower : data.base.Index,
            data.base.paperIndex cutUpper ≤ cutJ ∧
            cutI ≤ data.base.paperIndex cutLower ∧
            data.base.paperIndex cutLower < innerJ ∧
            innerJ < data.base.paperIndex cutUpper ∧
            ContainsCut data.baseDeriv (data.base.paperIndex cutUpper) innerJ
              (data.base.paperIndex cutLower) ∧
            innerI = data.base.paperIndex cutLower) ∨
        (cutJ < innerJ ∧
          ∃ cutUpper cutLower : data.base.Index,
            data.base.paperIndex cutUpper ≤ cutK ∧
            cutJ ≤ data.base.paperIndex cutLower ∧
            data.base.paperIndex cutLower < innerJ ∧
            innerJ < data.base.paperIndex cutUpper ∧
            ContainsCut data.baseDeriv (data.base.paperIndex cutUpper) innerJ
              (data.base.paperIndex cutLower) ∧
            innerI = data.base.paperIndex cutLower) := by
  rcases containsCut_prefixData houter with ⟨data⟩
  exact
    ⟨data,
      cutPrefixData_inner_center_lower_trichotomy data hinner hinside_left
        hinside_right⟩

/--
Step toward Corollary 5.4.3 (Cuts ordered by derivation), the same prefix
nested-Cut and lower-endpoint statement as
`containsCut_inner_center_prefix_lower_trichotomy`, with the top-level
trichotomy expressed using actual final-root indices.
-/
theorem containsCut_inner_center_prefix_lower_trichotomy_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {outerUpper outerCenter outerLower innerUpper innerCenter innerLower : T.Index}
    (houter :
      ContainsCut deriv (T.paperIndex outerUpper) (T.paperIndex outerCenter)
        (T.paperIndex outerLower))
    (hinner :
      ContainsCut deriv (T.paperIndex innerUpper) (T.paperIndex innerCenter)
        (T.paperIndex innerLower))
    (hinside_left : outerLower.val < innerCenter.val)
    (hinside_right : innerCenter.val < outerUpper.val) :
    ∃ data : CutPrefixData deriv (T.paperIndex outerUpper) (T.paperIndex outerCenter)
        (T.paperIndex outerLower),
      (innerCenter = outerCenter ∧ innerLower = outerLower) ∨
        (innerCenter.val < outerCenter.val ∧
          ∃ cutUpper cutLower : data.base.Index,
            data.base.paperIndex cutUpper ≤ T.paperIndex outerCenter ∧
            T.paperIndex outerLower ≤ data.base.paperIndex cutLower ∧
            data.base.paperIndex cutLower < T.paperIndex innerCenter ∧
            T.paperIndex innerCenter < data.base.paperIndex cutUpper ∧
            ContainsCut data.baseDeriv (data.base.paperIndex cutUpper)
              (T.paperIndex innerCenter) (data.base.paperIndex cutLower) ∧
            T.paperIndex innerLower = data.base.paperIndex cutLower) ∨
        (outerCenter.val < innerCenter.val ∧
          ∃ cutUpper cutLower : data.base.Index,
            data.base.paperIndex cutUpper ≤ T.paperIndex outerUpper ∧
            T.paperIndex outerCenter ≤ data.base.paperIndex cutLower ∧
            data.base.paperIndex cutLower < T.paperIndex innerCenter ∧
            T.paperIndex innerCenter < data.base.paperIndex cutUpper ∧
            ContainsCut data.baseDeriv (data.base.paperIndex cutUpper)
              (T.paperIndex innerCenter) (data.base.paperIndex cutLower) ∧
            T.paperIndex innerLower = data.base.paperIndex cutLower) := by
  rcases containsCut_inner_center_prefix_lower_trichotomy houter hinner
      (Nat.succ_lt_succ hinside_left) (Nat.succ_lt_succ hinside_right) with
    ⟨data, htri⟩
  refine ⟨data, ?_⟩
  rcases htri with hsame | hlowerOrUpper
  · rcases hsame with ⟨hcenter, hlower⟩
    exact Or.inl
      ⟨Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hcenter)),
        Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hlower))⟩
  · rcases hlowerOrUpper with hlower | hupper
    · rcases hlower with
        ⟨hcenter_lt, cutUpper, cutLower, hupper_bound, hlower_bound,
          hcutLower_inner, hinner_cutUpper, hnested, hlower_eq⟩
      exact Or.inr
        (Or.inl
          ⟨Nat.succ_lt_succ_iff.mp (by
              simpa [Prepath.paperIndex] using hcenter_lt),
            cutUpper, cutLower, hupper_bound, hlower_bound,
            by simpa [Prepath.paperIndex] using hcutLower_inner,
            by simpa [Prepath.paperIndex] using hinner_cutUpper,
            by simpa [Prepath.paperIndex] using hnested,
            hlower_eq⟩)
    · rcases hupper with
        ⟨hcenter_lt, cutUpper, cutLower, hupper_bound, hlower_bound,
          hcutLower_inner, hinner_cutUpper, hnested, hlower_eq⟩
      exact Or.inr
        (Or.inr
          ⟨Nat.succ_lt_succ_iff.mp (by
              simpa [Prepath.paperIndex] using hcenter_lt),
            cutUpper, cutLower, hupper_bound, hlower_bound,
            by simpa [Prepath.paperIndex] using hcutLower_inner,
            by simpa [Prepath.paperIndex] using hinner_cutUpper,
            by simpa [Prepath.paperIndex] using hnested,
            hlower_eq⟩)

/--
Lower-side endpoint ordering of Proposition 5.4.1 (Matryoshka Cuts): a cut
centered between the lower endpoint `i` and center `j` of an outer Cut has its
own lower endpoint `i'' ≥ i` (the `i'' ≥ i` clause of the lower-side case).
-/
theorem matryoshka_lower_side_inner_lower_bound {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hleft : cutI < innerJ) (hright : innerJ < cutJ) :
    cutI ≤ innerI := by
  rcases containsCut_indices hinner with
    ⟨_innerUpper, innerCenter, _innerLower, _hupper, hcenter, _hlower, _hij, _hjk⟩
  have hleft_center : cutI < T.paperIndex innerCenter := by
    simpa [hcenter] using hleft
  have hright_center : T.paperIndex innerCenter < cutJ := by
    simpa [hcenter] using hright
  rcases matryoshka_cuts_lower_side_indexed (deriv := deriv) houter
      hleft_center hright_center with
    ⟨nestedUpper, nestedLower, _hupper_bound, hlower_bound, _hnestedLower_center,
      _hcenter_nestedUpper, hnested⟩
  have hnested_center :
      ContainsCut deriv (T.paperIndex nestedUpper) innerJ (T.paperIndex nestedLower) := by
    simpa [hcenter] using hnested
  have hlower_eq : innerI = T.paperIndex nestedLower :=
    ConsistentHistories.Routes.PathProperties.FlagNesting.containsCut_same_center_lower_eq
      hinner hnested_center
  rw [hlower_eq]
  exact hlower_bound

/--
Upper-side endpoint ordering of Proposition 5.4.1 (Matryoshka Cuts): a cut
centered between the center `j` and upper endpoint `k` of an outer Cut has its
own lower endpoint `i'' ≥ j` (the `i'' ≥ j` clause of the upper-side case).
-/
theorem matryoshka_upper_side_inner_lower_bound {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hleft : cutJ < innerJ) (hright : innerJ < cutK) :
    cutJ ≤ innerI := by
  rcases containsCut_indices hinner with
    ⟨_innerUpper, innerCenter, _innerLower, _hupper, hcenter, _hlower, _hij, _hjk⟩
  have hleft_center : cutJ < T.paperIndex innerCenter := by
    simpa [hcenter] using hleft
  have hright_center : T.paperIndex innerCenter < cutK := by
    simpa [hcenter] using hright
  rcases matryoshka_cuts_upper_side_indexed (deriv := deriv) houter
      hleft_center hright_center with
    ⟨nestedUpper, nestedLower, _hupper_bound, hlower_bound, _hnestedLower_center,
      _hcenter_nestedUpper, hnested⟩
  have hnested_center :
      ContainsCut deriv (T.paperIndex nestedUpper) innerJ (T.paperIndex nestedLower) := by
    simpa [hcenter] using hnested
  have hlower_eq : innerI = T.paperIndex nestedLower :=
    ConsistentHistories.Routes.PathProperties.FlagNesting.containsCut_same_center_lower_eq
      hinner hnested_center
  rw [hlower_eq]
  exact hlower_bound

/--
Lower-side case of Proposition 5.4.1 (Matryoshka Cuts) with the nested Cut
identified: if the inner Cut center `i'` lies between the lower endpoint `i` and
center `j` of the outer Cut, then the full ordering `j'' ≤ j`, `i ≤ i''`,
`i'' < i' < j''` holds, the inner Cut's endpoints being identified with the
nested Cut of the proposition by Proposition 5.2.3 (Affine cuts).
-/
theorem matryoshka_lower_side_inner_endpoint_bounds {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hleft : cutI < innerJ) (hright : innerJ < cutJ) :
    innerK ≤ cutJ ∧ cutI ≤ innerI ∧ innerI < innerJ ∧ innerJ < innerK := by
  rcases containsCut_indices hinner with
    ⟨_innerUpper, innerCenter, _innerLower, _hupper, hcenter, _hlower, _hij, _hjk⟩
  have hleft_center : cutI < T.paperIndex innerCenter := by
    simpa [hcenter] using hleft
  have hright_center : T.paperIndex innerCenter < cutJ := by
    simpa [hcenter] using hright
  rcases matryoshka_cuts_lower_side_indexed (deriv := deriv) houter
      hleft_center hright_center with
    ⟨nestedUpper, nestedLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_nestedUpper, hnested⟩
  have hnested_center :
      ContainsCut deriv (T.paperIndex nestedUpper) innerJ (T.paperIndex nestedLower) := by
    simpa [hcenter] using hnested
  rcases containsCut_same_center_endpoints_eq hinner hnested_center with
    ⟨hupper_eq, hlower_eq⟩
  exact
    ⟨by
      rw [hupper_eq]
      exact hupper_bound,
    by
      rw [hlower_eq]
      exact hlower_bound,
    by
      rw [hlower_eq]
      simpa [hcenter] using hcutLower_inner,
    by
      rw [hupper_eq]
      simpa [hcenter] using hinner_nestedUpper⟩

/--
Upper-side case of Proposition 5.4.1 (Matryoshka Cuts) with the nested Cut
identified: if the inner Cut center `i'` lies between the center `j` and upper
endpoint `k` of the outer Cut, then the full ordering `j'' ≤ k`, `j ≤ i''`,
`i'' < i' < j''` holds, the inner Cut's endpoints being identified with the
nested Cut of the proposition by Proposition 5.2.3 (Affine cuts).
-/
theorem matryoshka_upper_side_inner_endpoint_bounds {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hleft : cutJ < innerJ) (hright : innerJ < cutK) :
    innerK ≤ cutK ∧ cutJ ≤ innerI ∧ innerI < innerJ ∧ innerJ < innerK := by
  rcases containsCut_indices hinner with
    ⟨_innerUpper, innerCenter, _innerLower, _hupper, hcenter, _hlower, _hij, _hjk⟩
  have hleft_center : cutJ < T.paperIndex innerCenter := by
    simpa [hcenter] using hleft
  have hright_center : T.paperIndex innerCenter < cutK := by
    simpa [hcenter] using hright
  rcases matryoshka_cuts_upper_side_indexed (deriv := deriv) houter
      hleft_center hright_center with
    ⟨nestedUpper, nestedLower, hupper_bound, hlower_bound, hcutLower_inner,
      hinner_nestedUpper, hnested⟩
  have hnested_center :
      ContainsCut deriv (T.paperIndex nestedUpper) innerJ (T.paperIndex nestedLower) := by
    simpa [hcenter] using hnested
  rcases containsCut_same_center_endpoints_eq hinner hnested_center with
    ⟨hupper_eq, hlower_eq⟩
  exact
    ⟨by
      rw [hupper_eq]
      exact hupper_bound,
    by
      rw [hlower_eq]
      exact hlower_bound,
    by
      rw [hlower_eq]
      simpa [hcenter] using hcutLower_inner,
    by
      rw [hupper_eq]
      simpa [hcenter] using hinner_nestedUpper⟩

/--
Inner lower-endpoint bounds of Proposition 5.4.1 (Matryoshka Cuts), packaged as
both sides at once, used toward Corollary 5.4.4 (Cuts nest): a cut whose center
lies strictly inside another cut has lower endpoint at or above the outer lower
endpoint (lower side) or at or above the outer center (upper side).
-/
theorem cuts_nested_lower_constraints {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI) :
    (cutI < innerJ → innerJ < cutJ → cutI ≤ innerI) ∧
    (cutJ < innerJ → innerJ < cutK → cutJ ≤ innerI) := by
  constructor
  · intro hleft hright
    exact matryoshka_lower_side_inner_lower_bound houter hinner hleft hright
  · intro hleft hright
    exact matryoshka_upper_side_inner_lower_bound houter hinner hleft hright

/--
Step toward Corollaries 5.4.3 and 5.4.4, lower-endpoint trichotomy: if the
center of one Cut lies strictly inside another Cut, its lower endpoint is
constrained by whether that center is below, equal to, or above the outer
center. This tracks only the lower endpoint of the nested cut.
-/
theorem cuts_ordered_inner_center_lower_trichotomy {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hinside_left : cutI < innerJ) (hinside_right : innerJ < cutK) :
    (innerJ = cutJ ∧ cutI = innerI) ∨
      (innerJ < cutJ ∧ cutI ≤ innerI) ∨
      (cutJ < innerJ ∧ cutJ ≤ innerI) := by
  rcases Nat.lt_trichotomy innerJ cutJ with hlt | heq | hgt
  · exact Or.inr
      (Or.inl
        ⟨hlt, matryoshka_lower_side_inner_lower_bound houter hinner
          hinside_left hlt⟩)
  · subst innerJ
    exact Or.inl
      ⟨rfl,
        ConsistentHistories.Routes.PathProperties.FlagNesting.containsCut_same_center_lower_eq
          houter hinner⟩
  · exact Or.inr
      (Or.inr
        ⟨hgt, matryoshka_upper_side_inner_lower_bound houter hinner
          hgt hinside_right⟩)

/--
Step toward Corollary 5.4.3 (Cuts ordered by derivation), endpoint trichotomy:
if the center of one Cut lies strictly inside another Cut, then it is the same
Cut (equal endpoints), nested on the lower side, or nested on the upper side,
with all endpoint inequalities from Proposition 5.4.1 (Matryoshka Cuts). The
initial-prefix ordering part of Corollary 5.4.3 is added separately.
-/
theorem cuts_ordered_inner_center_endpoint_trichotomy {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hinside_left : cutI < innerJ) (hinside_right : innerJ < cutK) :
    (innerK = cutK ∧ innerJ = cutJ ∧ innerI = cutI) ∨
      (innerJ < cutJ ∧ innerK ≤ cutJ ∧ innerJ < innerK ∧
        innerI < innerJ ∧ cutI ≤ innerI) ∨
      (cutJ < innerJ ∧ innerK ≤ cutK ∧ innerJ < innerK ∧
        innerI < innerJ ∧ cutJ ≤ innerI) := by
  rcases Nat.lt_trichotomy innerJ cutJ with hlt | heq | hgt
  · rcases matryoshka_lower_side_inner_endpoint_bounds houter hinner
      hinside_left hlt with ⟨hupper_bound, hlower_bound, hlower_inner, hinner_upper⟩
    exact Or.inr
      (Or.inl ⟨hlt, hupper_bound, hinner_upper, hlower_inner, hlower_bound⟩)
  · subst innerJ
    rcases containsCut_same_center_endpoints_eq houter hinner with
      ⟨hupper_eq, hlower_eq⟩
    exact Or.inl ⟨hupper_eq.symm, rfl, hlower_eq.symm⟩
  · rcases matryoshka_upper_side_inner_endpoint_bounds houter hinner
      hgt hinside_right with ⟨hupper_bound, hlower_bound, hlower_inner, hinner_upper⟩
    exact Or.inr
      (Or.inr ⟨hgt, hupper_bound, hinner_upper, hlower_inner, hlower_bound⟩)

/--
Corollary 5.4.3 (Cuts ordered by derivation), prefix-and-endpoint form: if the
center of one Cut lies strictly inside another Cut, there is an initial prefix
ending in the outer Cut and an initial prefix of that prefix ending in the inner
Cut, with the endpoint alternatives forced by Proposition 5.4.1 (Matryoshka
Cuts) and Proposition 5.2.3 (Affine cuts).
-/
theorem containsCut_ordered_prefix_endpoint_component {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hinside_left : cutI < innerJ)
    (hinside_right : innerJ < cutK) :
    ∃ outerData : CutPrefixData deriv cutK cutJ cutI,
      let outerDeriv :=
        Derivation.cut outerData.baseDeriv outerData.hij outerData.hjk
          outerData.hk outerData.hj outerData.hi outerData.hconsistent
      ∃ _innerData : CutPrefixData outerDeriv innerK innerJ innerI,
        (innerK = cutK ∧ innerJ = cutJ ∧ innerI = cutI) ∨
          (innerJ < cutJ ∧ innerK ≤ cutJ ∧ innerJ < innerK ∧
            innerI < innerJ ∧ cutI ≤ innerI) ∨
          (cutJ < innerJ ∧ innerK ≤ cutK ∧ innerJ < innerK ∧
            innerI < innerJ ∧ cutJ ≤ innerI) := by
  rcases containsCut_prefixData houter with ⟨outerData⟩
  let outerDeriv :=
    Derivation.cut outerData.baseDeriv outerData.hij outerData.hjk
      outerData.hk outerData.hj outerData.hi outerData.hconsistent
  have houter_here :
      ContainsCut outerDeriv cutK cutJ cutI := by
    have hhere :
        ContainsCut outerDeriv (outerData.base.paperIndex outerData.idxK)
          (outerData.base.paperIndex outerData.idxJ)
          (outerData.base.paperIndex outerData.idxI) := by
      exact ContainsCut.here outerData.baseDeriv outerData.hij outerData.hjk
        outerData.hk outerData.hj outerData.hi outerData.hconsistent
    simpa [outerDeriv, outerData.cutK_eq, outerData.cutJ_eq, outerData.cutI_eq]
      using hhere
  have htri :=
    cuts_ordered_inner_center_endpoint_trichotomy houter hinner hinside_left
      hinside_right
  refine ⟨outerData, ?_⟩
  dsimp [outerDeriv]
  rcases htri with hsame | hlowerOrUpper
  · rcases hsame with ⟨hupper_eq, hcenter_eq, hlower_eq⟩
    have hinner_outer : ContainsCut outerDeriv innerK innerJ innerI := by
      simpa [hupper_eq, hcenter_eq, hlower_eq] using houter_here
    rcases containsCut_prefixData hinner_outer with ⟨innerData⟩
    exact ⟨innerData, Or.inl ⟨hupper_eq, hcenter_eq, hlower_eq⟩⟩
  · rcases hlowerOrUpper with hlower | hupper
    · rcases containsCut_indices hinner with
        ⟨_innerUpper, innerCenter, _innerLower, _hupper, hcenter, _hlower,
          _hij, _hjk⟩
      have hbase_length_eq : outerData.base.length = T.length := by
        calc
          outerData.base.length = (Derivation.root outerDeriv).length := by rfl
          _ = T.length := outerData.hprefix.length_eq
      let innerBase : outerData.base.Index := Fin.cast hbase_length_eq.symm innerCenter
      have hinner_eq : innerJ = outerData.base.paperIndex innerBase := by
        rw [← hcenter]
        simp [innerBase, Prepath.paperIndex]
      rcases cutPrefixData_lower_side_nested_before_same_endpoints outerData hinner
          hinner_eq hinside_left hlower.1 with
        ⟨cutUpper, cutLower, _hupper_bound, _hlower_bound, _hcutLower_inner,
          _hinner_cutUpper, hnested, hupper_eq, hlower_eq⟩
      have hnested_outer_base :
          ContainsCut outerDeriv (outerData.base.paperIndex cutUpper)
            (outerData.base.paperIndex innerBase)
            (outerData.base.paperIndex cutLower) := by
        exact ContainsCut.cutStep hnested outerData.hij outerData.hjk
          outerData.hk outerData.hj outerData.hi outerData.hconsistent
      have hnested_outer :
          ContainsCut outerDeriv innerK innerJ innerI := by
        simpa [hupper_eq, hinner_eq, hlower_eq] using hnested_outer_base
      rcases containsCut_prefixData hnested_outer with ⟨innerData⟩
      exact ⟨innerData, Or.inr (Or.inl hlower)⟩
    · rcases containsCut_indices hinner with
        ⟨_innerUpper, innerCenter, _innerLower, _hupper, hcenter, _hlower,
          _hij, _hjk⟩
      have hbase_length_eq : outerData.base.length = T.length := by
        calc
          outerData.base.length = (Derivation.root outerDeriv).length := by rfl
          _ = T.length := outerData.hprefix.length_eq
      let innerBase : outerData.base.Index := Fin.cast hbase_length_eq.symm innerCenter
      have hinner_eq : innerJ = outerData.base.paperIndex innerBase := by
        rw [← hcenter]
        simp [innerBase, Prepath.paperIndex]
      rcases cutPrefixData_upper_side_nested_before_same_endpoints outerData hinner
          hinner_eq hupper.1 hinside_right with
        ⟨cutUpper, cutLower, _hupper_bound, _hlower_bound, _hcutLower_inner,
          _hinner_cutUpper, hnested, hupper_eq, hlower_eq⟩
      have hnested_outer_base :
          ContainsCut outerDeriv (outerData.base.paperIndex cutUpper)
            (outerData.base.paperIndex innerBase)
            (outerData.base.paperIndex cutLower) := by
        exact ContainsCut.cutStep hnested outerData.hij outerData.hjk
          outerData.hk outerData.hj outerData.hi outerData.hconsistent
      have hnested_outer :
          ContainsCut outerDeriv innerK innerJ innerI := by
        simpa [hupper_eq, hinner_eq, hlower_eq] using hnested_outer_base
      rcases containsCut_prefixData hnested_outer with ⟨innerData⟩
      exact ⟨innerData, Or.inr (Or.inr hupper)⟩

/--
Corollary 5.4.3: two Cut occurrences whose second center
lies strictly inside the first Cut have nested initial prefixes, and their
endpoints satisfy the paper's three ordered alternatives.
-/
theorem cuts_ordered_by_derivation {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hinside_left : cutI < innerJ)
    (hinside_right : innerJ < cutK) :
    ∃ outerData : CutPrefixData deriv cutK cutJ cutI,
      let outerDeriv :=
        Derivation.cut outerData.baseDeriv outerData.hij outerData.hjk
          outerData.hk outerData.hj outerData.hi outerData.hconsistent
      ∃ _innerData : CutPrefixData outerDeriv innerK innerJ innerI,
        (cutK = innerK ∧ cutJ = innerJ ∧ cutI = innerI) ∨
          (cutK ≥ innerK ∧ innerK > innerJ ∧ innerJ > innerI ∧ innerI ≥ cutJ) ∨
          (cutJ ≥ innerK ∧ innerK > innerJ ∧ innerJ > innerI ∧ innerI ≥ cutI) := by
  rcases containsCut_ordered_prefix_endpoint_component houter hinner hinside_left
      hinside_right with
    ⟨outerData, innerData, hcases⟩
  refine ⟨outerData, innerData, ?_⟩
  rcases hcases with hsame | hlowerOrUpper
  · rcases hsame with ⟨hupper, hcenter, hlower⟩
    exact Or.inl ⟨hupper.symm, hcenter.symm, hlower.symm⟩
  · rcases hlowerOrUpper with hlower | hupper
    · rcases hlower with
        ⟨_hcenter_lt, hupper_bound, hcenter_upper, hlower_center, hlower_bound⟩
      exact Or.inr
        (Or.inr ⟨hupper_bound, hcenter_upper, hlower_center, hlower_bound⟩)
    · rcases hupper with
        ⟨_hcenter_lt, hupper_bound, hcenter_upper, hlower_center, hlower_bound⟩
      exact Or.inr
        (Or.inl ⟨hupper_bound, hcenter_upper, hlower_center, hlower_bound⟩)

/--
Step toward Corollary 5.4.4 (Cuts nest), center-inside case: when the second
Cut's center lies strictly inside the first Cut, the two Cuts are equal, nested
on the first Cut's upper side, or nested on its lower side. These are three of
the seven displayed alternatives; the full disjunction is assembled in
`cuts_ordered_nesting_seven_cases_component`.
-/
theorem cuts_ordered_nesting_center_inside_component {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI innerK innerJ innerI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hinner : ContainsCut deriv innerK innerJ innerI)
    (hinside_left : cutI < innerJ)
    (hinside_right : innerJ < cutK) :
    (cutK = innerK ∧ cutJ = innerJ ∧ cutI = innerI) ∨
      (cutK ≥ innerK ∧ innerK > innerJ ∧ innerJ > innerI ∧
        innerI ≥ cutJ ∧ cutJ > cutI) ∨
      (cutK > cutJ ∧ cutJ ≥ innerK ∧ innerK > innerJ ∧
        innerJ > innerI ∧ innerI ≥ cutI) := by
  rcases cuts_ordered_by_derivation houter hinner hinside_left hinside_right with
    ⟨_outerData, _innerData, hcases⟩
  have houter_order := containsCut_order houter
  rcases hcases with hsame | hnested
  · exact Or.inl hsame
  · rcases hnested with hupper | hlower
    · rcases hupper with ⟨hupper_bound, hcenter_upper, hlower_center, hlower_bound⟩
      exact Or.inr
        (Or.inl
          ⟨hupper_bound, hcenter_upper, hlower_center, hlower_bound,
            houter_order.1⟩)
    · rcases hlower with ⟨hcenter_bound, hcenter_upper, hlower_center, hlower_bound⟩
      exact Or.inr
        (Or.inr
          ⟨houter_order.2, hcenter_bound, hcenter_upper, hlower_center,
            hlower_bound⟩)

/--
Step toward Corollary 5.4.4 (Cuts nest), symmetric center-inside case: when the
first Cut's center lies strictly inside the second Cut, the two Cuts are equal,
the first Cut is nested on the second Cut's upper side, or nested on its lower
side. Obtained from `cuts_ordered_nesting_center_inside_component` by swapping
the two Cuts.
-/
theorem cuts_ordered_nesting_symmetric_center_inside_component
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI otherK otherJ otherI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    (hother : ContainsCut deriv otherK otherJ otherI)
    (hinside_left : otherI < cutJ)
    (hinside_right : cutJ < otherK) :
    (cutK = otherK ∧ cutJ = otherJ ∧ cutI = otherI) ∨
      (otherK ≥ cutK ∧ cutK > cutJ ∧ cutJ > cutI ∧
        cutI ≥ otherJ ∧ otherJ > otherI) ∨
      (otherK > otherJ ∧ otherJ ≥ cutK ∧ cutK > cutJ ∧
        cutJ > cutI ∧ cutI ≥ otherI) := by
  rcases cuts_ordered_nesting_center_inside_component hother hcut hinside_left
      hinside_right with hsame | hnested
  · rcases hsame with ⟨hK, hJ, hI⟩
    exact Or.inl ⟨hK.symm, hJ.symm, hI.symm⟩
  · rcases hnested with hupper | hlower
    · exact Or.inr (Or.inl hupper)
    · exact Or.inr (Or.inr hlower)

/--
Step toward Corollary 5.4.4 (Cuts nest), side-by-side case: if one Cut lies
wholly at or above the other by endpoints, then the corresponding side-by-side
alternative in the seven-case display holds. This case assumes endpoint
separation as a hypothesis.
-/
theorem cuts_ordered_nesting_side_by_side_component {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI otherK otherJ otherI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    (hother : ContainsCut deriv otherK otherJ otherI)
    (hsep : otherI ≥ cutK ∨ cutI ≥ otherK) :
    (otherK > otherJ ∧ otherJ > otherI ∧ otherI ≥ cutK ∧
      cutK > cutJ ∧ cutJ > cutI) ∨
      (cutK > cutJ ∧ cutJ > cutI ∧ cutI ≥ otherK ∧
        otherK > otherJ ∧ otherJ > otherI) := by
  have hcut_order := containsCut_order hcut
  have hother_order := containsCut_order hother
  rcases hsep with habove | hbelow
  · exact Or.inl
      ⟨hother_order.2, hother_order.1, habove, hcut_order.2,
        hcut_order.1⟩
  · exact Or.inr
      ⟨hcut_order.2, hcut_order.1, hbelow, hother_order.2,
        hother_order.1⟩

/--
Lean-indexed form of the ordered-prefix endpoint component for Corollary 5.4.3.
-/
theorem containsCut_ordered_prefix_endpoint_component_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {outerUpper outerCenter outerLower innerUpper innerCenter innerLower : T.Index}
    (houter :
      ContainsCut deriv (T.paperIndex outerUpper) (T.paperIndex outerCenter)
        (T.paperIndex outerLower))
    (hinner :
      ContainsCut deriv (T.paperIndex innerUpper) (T.paperIndex innerCenter)
        (T.paperIndex innerLower))
    (hinside_left : outerLower.val < innerCenter.val)
    (hinside_right : innerCenter.val < outerUpper.val) :
    ∃ outerData :
      CutPrefixData deriv (T.paperIndex outerUpper) (T.paperIndex outerCenter)
        (T.paperIndex outerLower),
      let outerDeriv :=
        Derivation.cut outerData.baseDeriv outerData.hij outerData.hjk
          outerData.hk outerData.hj outerData.hi outerData.hconsistent
      ∃ _innerData :
        CutPrefixData outerDeriv (T.paperIndex innerUpper) (T.paperIndex innerCenter)
          (T.paperIndex innerLower),
        (innerUpper = outerUpper ∧ innerCenter = outerCenter ∧ innerLower = outerLower) ∨
          (innerCenter.val < outerCenter.val ∧
            innerUpper.val ≤ outerCenter.val ∧ innerCenter.val < innerUpper.val ∧
            innerLower.val < innerCenter.val ∧ outerLower.val ≤ innerLower.val) ∨
          (outerCenter.val < innerCenter.val ∧
            innerUpper.val ≤ outerUpper.val ∧ innerCenter.val < innerUpper.val ∧
            innerLower.val < innerCenter.val ∧ outerCenter.val ≤ innerLower.val) := by
  rcases containsCut_ordered_prefix_endpoint_component houter hinner
      (Nat.succ_lt_succ hinside_left) (Nat.succ_lt_succ hinside_right) with
    ⟨outerData, innerData, hcases⟩
  refine ⟨outerData, innerData, ?_⟩
  rcases hcases with hsame | hlowerOrUpper
  · rcases hsame with ⟨hupper, hcenter, hlower⟩
    exact Or.inl
      ⟨Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hupper)),
        Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hcenter)),
        Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hlower))⟩
  · rcases hlowerOrUpper with hlower | hupper
    · rcases hlower with
        ⟨hcenter_lt, hupper_bound, hcenter_upper, hlower_center, hlower_bound⟩
      exact Or.inr
        (Or.inl
          ⟨Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hcenter_lt),
            Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hupper_bound),
            Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hcenter_upper),
            Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hlower_center),
            Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hlower_bound)⟩)
    · rcases hupper with
        ⟨hcenter_lt, hupper_bound, hcenter_upper, hlower_center, hlower_bound⟩
      exact Or.inr
        (Or.inr
          ⟨Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hcenter_lt),
            Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hupper_bound),
            Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hcenter_upper),
            Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hlower_center),
            Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hlower_bound)⟩)

/--
Step toward Corollaries 5.4.3 and 5.4.4, lower-endpoint trichotomy: the same
statement as `cuts_ordered_inner_center_lower_trichotomy`, with endpoints
expressed as actual indices of the final root.
-/
theorem cuts_ordered_inner_center_lower_trichotomy_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {outerUpper outerCenter outerLower innerUpper innerCenter innerLower : T.Index}
    (houter :
      ContainsCut deriv (T.paperIndex outerUpper) (T.paperIndex outerCenter)
        (T.paperIndex outerLower))
    (hinner :
      ContainsCut deriv (T.paperIndex innerUpper) (T.paperIndex innerCenter)
        (T.paperIndex innerLower))
    (hinside_left : outerLower.val < innerCenter.val)
    (hinside_right : innerCenter.val < outerUpper.val) :
    (innerCenter = outerCenter ∧ outerLower = innerLower) ∨
      (innerCenter.val < outerCenter.val ∧ outerLower.val ≤ innerLower.val) ∨
      (outerCenter.val < innerCenter.val ∧ outerCenter.val ≤ innerLower.val) := by
  rcases cuts_ordered_inner_center_lower_trichotomy houter hinner
      (Nat.succ_lt_succ hinside_left) (Nat.succ_lt_succ hinside_right) with
    hsame | hlowerOrUpper
  · rcases hsame with ⟨hcenter, hlower⟩
    exact Or.inl
      ⟨Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hcenter)),
        Fin.ext (Nat.succ.inj (by simpa [Prepath.paperIndex] using hlower))⟩
  · rcases hlowerOrUpper with hlower | hupper
    · rcases hlower with ⟨hcenter, hlower⟩
      exact Or.inr
        (Or.inl
          ⟨Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hcenter),
            Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hlower)⟩)
    · rcases hupper with ⟨hcenter, hlower⟩
      exact Or.inr
        (Or.inr
          ⟨Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hcenter),
            Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hlower)⟩)

/--
Corollary 5.1.3: every index bracketed by
a Cut has a `cutMe` label whose target is still inside the Cut and no lower
than the Cut's lower endpoint. This is proved here because the formal proof uses
the Matryoshka geometry above.
-/
theorem containsCut_bracketed_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    {m : T.Index} (him : cutI < T.paperIndex m) (hmk : T.paperIndex m < cutK) :
    ∃ cutLower : T.Index,
      cutI ≤ T.paperIndex cutLower ∧
      T.paperIndex cutLower < T.paperIndex m ∧
      HasCutMe (T.paperIndex cutLower) (T.get m) := by
  have horder := containsCut_order hcut
  rcases Nat.lt_trichotomy (T.paperIndex m) cutJ with hlt | heq | hgt
  · rcases matryoshka_cuts_lower_side_indexed (deriv := deriv) hcut him hlt with
      ⟨_cutUpper, cutLower, _hupper_bound, hlower_bound, hcutLower_m, _hm_upper,
        hnested⟩
    exact
      ⟨cutLower, hlower_bound, hcutLower_m,
        containsCut_center_hasCutMe hnested m rfl⟩
  · rcases containsCut_indices hcut with
      ⟨_outerUpper, _outerCenter, outerLower, _hupper, _hcenter, hlower, _hij, _hjk⟩
    exact
      ⟨outerLower,
        by omega,
        by
          rw [heq]
          simpa [hlower] using horder.1,
        by
          have hm_center : T.paperIndex m = cutJ := heq
          simpa [hlower] using containsCut_center_hasCutMe hcut m hm_center⟩
  · rcases matryoshka_cuts_upper_side_indexed (deriv := deriv) hcut hgt hmk with
      ⟨_cutUpper, cutLower, _hupper_bound, hlower_bound, hcutLower_m, _hm_upper,
        hnested⟩
    exact
      ⟨cutLower, Nat.le_trans (Nat.le_of_lt horder.1) hlower_bound,
        hcutLower_m, containsCut_center_hasCutMe hnested m rfl⟩

/--
Step toward Corollary 5.4.4 (Cuts nest), lower crossing exclusion: a second Cut
cannot have its center at or below the first Cut's lower endpoint while its
upper endpoint lies above that lower endpoint and at or below the first Cut's
center. This rules out the crossing configurations absent from the seven-case
display.
-/
theorem cuts_ordered_nesting_no_lower_crossing {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI otherK otherJ otherI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hother : ContainsCut deriv otherK otherJ otherI)
    (hother_center_le_outer_lower : otherJ ≤ cutI)
    (houter_lower_lt_other_upper : cutI < otherK)
    (hother_upper_le_outer_center : otherK ≤ cutJ) :
    False := by
  rcases containsCut_indices hother with
    ⟨otherUpper, _otherCenter, _otherLower, hotherUpper, _hotherCenter,
      _hotherLower, _hotherIJ, _hotherJK⟩
  have houter_label :
      ∃ target : Nat,
        cutI ≤ target ∧ HasCutLabelAt Time target (T.get otherUpper) := by
    rcases Nat.eq_or_lt_of_le hother_upper_le_outer_center with hcenter_eq | hcenter_lt
    · refine ⟨cutI, Nat.le_refl cutI, ?_⟩
      exact containsCut_center_hasCutLabelAt houter otherUpper
        (hotherUpper.trans hcenter_eq)
    · have hotherUpper_left : cutI < T.paperIndex otherUpper := by
        simpa [hotherUpper] using houter_lower_lt_other_upper
      have hotherUpper_right : T.paperIndex otherUpper < cutK := by
        have houter_order := containsCut_order houter
        have hotherK_lt_cutK : otherK < cutK :=
          Nat.lt_trans hcenter_lt houter_order.2
        simpa [hotherUpper] using hotherK_lt_cutK
      rcases containsCut_bracketed_hasCutMe houter
          (m := otherUpper) hotherUpper_left hotherUpper_right with
        ⟨outerLower, hcutI_le_outerLower, _houterLower_otherUpper, hcutMe⟩
      exact
        ⟨T.paperIndex outerLower, hcutI_le_outerLower,
          hasCutLabelAt_of_hasCutMe hcutMe⟩
  rcases houter_label with ⟨outerTarget, hcutI_le_outerTarget, hlabelOuter⟩
  rcases containsCut_upper_hasCutLabel_le_lower hother (upper := otherUpper)
      hotherUpper with
    ⟨otherLower, hotherLower_le_otherI, hlabelOther⟩
  rcases hlabelOther with ⟨kind, base, hshape⟩
  have htarget_eq : outerTarget = T.paperIndex otherLower :=
    hasCutLabelAt_target_eq_of_eq_cutting hlabelOuter hshape
      (T.consistent otherUpper)
  have hother_order := containsCut_order hother
  have hotherI_lt_cutI : otherI < cutI :=
    Nat.lt_of_lt_of_le hother_order.1 hother_center_le_outer_lower
  have hcutI_le_otherI : cutI ≤ otherI := by
    calc
      cutI ≤ outerTarget := hcutI_le_outerTarget
      _ = T.paperIndex otherLower := htarget_eq
      _ ≤ otherI := hotherLower_le_otherI
  exact Nat.not_lt_of_ge hcutI_le_otherI hotherI_lt_cutI

/--
Step toward Corollary 5.4.4 (Cuts nest), upper crossing exclusion: a second Cut
cannot have its lower endpoint at or above the first Cut's center and below the
first Cut's upper endpoint while its center is at or above that upper endpoint.
This rules out the crossing configurations absent from the seven-case display.
-/
theorem cuts_ordered_nesting_no_upper_crossing {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI otherK otherJ otherI : Nat}
    (houter : ContainsCut deriv cutK cutJ cutI)
    (hother : ContainsCut deriv otherK otherJ otherI)
    (houter_center_le_other_lower : cutJ ≤ otherI)
    (hother_lower_lt_outer_upper : otherI < cutK)
    (houter_upper_le_other_center : cutK ≤ otherJ) :
    False := by
  rcases containsCut_indices houter with
    ⟨outerUpper, _outerCenter, _outerLower, houterUpper, _houterCenter,
      _houterLower, _houterIJ, _houterJK⟩
  rcases containsCut_indices hother with
    ⟨_otherUpper, otherCenter, _otherLower, _hotherUpper, hotherCenter,
      _hotherLower, _hotherIJ, _hotherJK⟩
  rcases containsCut_upper_hasCutLabel_le_lower houter (upper := outerUpper)
      houterUpper with
    ⟨outerLabelLower, houterLabelLower_le_cutI, hlabelOuterUpper⟩
  have houterLabelLower_lt_outerUpper : outerLabelLower.val < outerUpper.val := by
    have houter_order := containsCut_order houter
    have hpaper_lt : T.paperIndex outerLabelLower < T.paperIndex outerUpper := by
      calc
        T.paperIndex outerLabelLower ≤ cutI := houterLabelLower_le_cutI
        _ < cutK := Nat.lt_trans houter_order.1 houter_order.2
        _ = T.paperIndex outerUpper := houterUpper.symm
    exact Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hpaper_lt)
  have houterUpper_le_otherCenter : outerUpper.val ≤ otherCenter.val := by
    have hpaper_le : T.paperIndex outerUpper ≤ T.paperIndex otherCenter := by
      calc
        T.paperIndex outerUpper = cutK := houterUpper
        _ ≤ otherJ := houter_upper_le_other_center
        _ = T.paperIndex otherCenter := hotherCenter.symm
    exact Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hpaper_le)
  rcases skip_cuts_same_derivation deriv houterLabelLower_lt_outerUpper
      houterUpper_le_otherCenter hlabelOuterUpper with
    ⟨foundTarget, hlabelFound, hnot_between⟩
  have hlabelOtherCenter :
      HasCutLabelAt Time otherI (T.get otherCenter) :=
    containsCut_center_hasCutLabelAt hother otherCenter hotherCenter
  rcases hlabelOtherCenter with ⟨kind, base, hshape⟩
  have hfound_eq_otherI : T.paperIndex foundTarget = otherI :=
    hasCutLabelAt_target_eq_of_eq_cutting hlabelFound hshape
      (T.consistent otherCenter)
  have hfound_gt_lower : outerLabelLower.val < foundTarget.val := by
    have houter_order := containsCut_order houter
    have hpaper_lt : T.paperIndex outerLabelLower < T.paperIndex foundTarget := by
      calc
        T.paperIndex outerLabelLower ≤ cutI := houterLabelLower_le_cutI
        _ < cutJ := houter_order.1
        _ ≤ otherI := houter_center_le_other_lower
        _ = T.paperIndex foundTarget := hfound_eq_otherI.symm
    exact Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hpaper_lt)
  have hfound_lt_outer : foundTarget.val < outerUpper.val := by
    have hpaper_lt : T.paperIndex foundTarget < T.paperIndex outerUpper := by
      calc
        T.paperIndex foundTarget = otherI := hfound_eq_otherI
        _ < cutK := hother_lower_lt_outer_upper
        _ = T.paperIndex outerUpper := houterUpper.symm
    exact Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hpaper_lt)
  exact hnot_between ⟨hfound_gt_lower, hfound_lt_outer⟩

/--
The seven alternatives displayed in Corollary 5.4.4 (Cuts nest), indexed by
`Fin 7`: case 0 is equality, cases 1 and 6 are side-by-side, and cases 2–5 are
the four nestings. Used to state the `precisely one` conclusion of the
corollary.
-/
def CutsOrderedNestingCase
    (cutK cutJ cutI otherK otherJ otherI : Nat) : Fin 7 → Prop
  | ⟨0, _⟩ => cutK = otherK ∧ cutJ = otherJ ∧ cutI = otherI
  | ⟨1, _⟩ =>
      otherK > otherJ ∧ otherJ > otherI ∧ otherI ≥ cutK ∧
        cutK > cutJ ∧ cutJ > cutI
  | ⟨2, _⟩ =>
      cutK ≥ otherK ∧ otherK > otherJ ∧ otherJ > otherI ∧
        otherI ≥ cutJ ∧ cutJ > cutI
  | ⟨3, _⟩ =>
      cutK > cutJ ∧ cutJ ≥ otherK ∧ otherK > otherJ ∧
        otherJ > otherI ∧ otherI ≥ cutI
  | ⟨4, _⟩ =>
      otherK ≥ cutK ∧ cutK > cutJ ∧ cutJ > cutI ∧
        cutI ≥ otherJ ∧ otherJ > otherI
  | ⟨5, _⟩ =>
      otherK > otherJ ∧ otherJ ≥ cutK ∧ cutK > cutJ ∧
        cutJ > cutI ∧ cutI ≥ otherI
  | ⟨6, _⟩ =>
      cutK > cutJ ∧ cutJ > cutI ∧ cutI ≥ otherK ∧
        otherK > otherJ ∧ otherJ > otherI
  | ⟨_ + 7, _⟩ => False

/--
Existence component of Corollary 5.4.4: for two
Cut occurrences in the same derivation, at least one of the seven displayed
nesting alternatives holds. This does not prove the exclusivity or
`precisely one` part of the paper corollary.
-/
theorem cuts_ordered_nesting_seven_cases_component {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI otherK otherJ otherI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    (hother : ContainsCut deriv otherK otherJ otherI) :
    (cutK = otherK ∧ cutJ = otherJ ∧ cutI = otherI) ∨
      (otherK > otherJ ∧ otherJ > otherI ∧ otherI ≥ cutK ∧
        cutK > cutJ ∧ cutJ > cutI) ∨
      (cutK ≥ otherK ∧ otherK > otherJ ∧ otherJ > otherI ∧
        otherI ≥ cutJ ∧ cutJ > cutI) ∨
      (cutK > cutJ ∧ cutJ ≥ otherK ∧ otherK > otherJ ∧
        otherJ > otherI ∧ otherI ≥ cutI) ∨
      (otherK ≥ cutK ∧ cutK > cutJ ∧ cutJ > cutI ∧
        cutI ≥ otherJ ∧ otherJ > otherI) ∨
      (otherK > otherJ ∧ otherJ ≥ cutK ∧ cutK > cutJ ∧
        cutJ > cutI ∧ cutI ≥ otherI) ∨
      (cutK > cutJ ∧ cutJ > cutI ∧ cutI ≥ otherK ∧
        otherK > otherJ ∧ otherJ > otherI) := by
  have hcut_order := containsCut_order hcut
  have hother_order := containsCut_order hother
  by_cases hsep : otherI ≥ cutK ∨ cutI ≥ otherK
  · rcases cuts_ordered_nesting_side_by_side_component hcut hother hsep with
      habove | hbelow
    · exact Or.inr (Or.inl habove)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbelow)))))
  have hotherI_lt_cutK : otherI < cutK := by
    exact Nat.lt_of_not_ge (fun hge => hsep (Or.inl hge))
  have hcutI_lt_otherK : cutI < otherK := by
    exact Nat.lt_of_not_ge (fun hge => hsep (Or.inr hge))
  by_cases hcenter_inside : cutI < otherJ ∧ otherJ < cutK
  · rcases cuts_ordered_nesting_center_inside_component hcut hother
        hcenter_inside.1 hcenter_inside.2 with hsame | hnested
    · exact Or.inl hsame
    · rcases hnested with hupper | hlower
      · exact Or.inr (Or.inr (Or.inl hupper))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hlower)))
  by_cases hsym_inside : otherI < cutJ ∧ cutJ < otherK
  · rcases cuts_ordered_nesting_symmetric_center_inside_component hcut hother
        hsym_inside.1 hsym_inside.2 with hsame | hnested
    · exact Or.inl hsame
    · rcases hnested with hupper | hlower
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hupper))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlower)))))
  have hcenter_split : otherJ ≤ cutI ∨ cutK ≤ otherJ := by
    by_cases hleft : otherJ ≤ cutI
    · exact Or.inl hleft
    · by_cases hright : cutK ≤ otherJ
      · exact Or.inr hright
      · exact False.elim
          (hcenter_inside
            ⟨Nat.lt_of_not_ge hleft, Nat.lt_of_not_ge hright⟩)
  have hsym_split : cutJ ≤ otherI ∨ otherK ≤ cutJ := by
    by_cases hleft : cutJ ≤ otherI
    · exact Or.inl hleft
    · by_cases hright : otherK ≤ cutJ
      · exact Or.inr hright
      · exact False.elim
          (hsym_inside
            ⟨Nat.lt_of_not_ge hleft, Nat.lt_of_not_ge hright⟩)
  rcases hcenter_split with hotherJ_le_cutI | hcutK_le_otherJ
  · rcases hsym_split with hcutJ_le_otherI | hotherK_le_cutJ
    · have hcutJ_lt_cutJ : cutJ < cutJ :=
        Nat.lt_of_le_of_lt hcutJ_le_otherI
          (Nat.lt_trans hother_order.1
            (Nat.lt_of_le_of_lt hotherJ_le_cutI hcut_order.1))
      exact False.elim ((Nat.lt_irrefl cutJ) hcutJ_lt_cutJ)
    · exact False.elim
        (cuts_ordered_nesting_no_lower_crossing hcut hother
          hotherJ_le_cutI hcutI_lt_otherK hotherK_le_cutJ)
  · rcases hsym_split with hcutJ_le_otherI | hotherK_le_cutJ
    · exact False.elim
        (cuts_ordered_nesting_no_upper_crossing hcut hother
          hcutJ_le_otherI hotherI_lt_cutK hcutK_le_otherJ)
    · have hcutK_lt_cutK : cutK < cutK :=
        Nat.lt_of_le_of_lt hcutK_le_otherJ
          (Nat.lt_trans hother_order.2
            (Nat.lt_of_le_of_lt hotherK_le_cutJ hcut_order.2))
      exact False.elim ((Nat.lt_irrefl cutK) hcutK_lt_cutK)

/--
Exclusivity component of Corollary 5.4.4: the
seven displayed nesting alternatives are pairwise disjoint.
-/
theorem cuts_ordered_nesting_cases_pairwise_disjoint
    {cutK cutJ cutI otherK otherJ otherI : Nat} :
    ∀ a b : Fin 7, a ≠ b →
      ¬ (CutsOrderedNestingCase cutK cutJ cutI otherK otherJ otherI a ∧
        CutsOrderedNestingCase cutK cutJ cutI otherK otherJ otherI b) := by
  intro a b hne hboth
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  have ha_cases :
      a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by
    omega
  have hb_cases :
      b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 := by
    omega
  rcases ha_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CutsOrderedNestingCase] at hne hboth ⊢ <;>
    omega

/--
Packed form of Corollary 5.4.4: for two
Cut occurrences in the same derivation, precisely one of the seven displayed
nesting alternatives holds.
-/
theorem cuts_ordered_nesting_precisely_one_component {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI otherK otherJ otherI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    (hother : ContainsCut deriv otherK otherJ otherI) :
    (∃ a : Fin 7,
      CutsOrderedNestingCase cutK cutJ cutI otherK otherJ otherI a) ∧
      ∀ a b : Fin 7, a ≠ b →
        ¬ (CutsOrderedNestingCase cutK cutJ cutI otherK otherJ otherI a ∧
          CutsOrderedNestingCase cutK cutJ cutI otherK otherJ otherI b) := by
  constructor
  · rcases cuts_ordered_nesting_seven_cases_component hcut hother with
      h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact ⟨⟨0, by decide⟩, h1⟩
    · exact ⟨⟨1, by decide⟩, h2⟩
    · exact ⟨⟨2, by decide⟩, h3⟩
    · exact ⟨⟨3, by decide⟩, h4⟩
    · exact ⟨⟨4, by decide⟩, h5⟩
    · exact ⟨⟨5, by decide⟩, h6⟩
    · exact ⟨⟨6, by decide⟩, h7⟩
  · exact cuts_ordered_nesting_cases_pairwise_disjoint

/--
Direct unique-existence form of Corollary 5.4.4: exactly one displayed nesting alternative holds.
-/
theorem cuts_ordered_nesting_unique_case {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T}
    {cutK cutJ cutI otherK otherJ otherI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI)
    (hother : ContainsCut deriv otherK otherJ otherI) :
    ∃ a : Fin 7,
      CutsOrderedNestingCase cutK cutJ cutI otherK otherJ otherI a ∧
        ∀ b : Fin 7,
          CutsOrderedNestingCase cutK cutJ cutI otherK otherJ otherI b → b = a := by
  rcases cuts_ordered_nesting_precisely_one_component hcut hother with
    ⟨hexists, hdisjoint⟩
  rcases hexists with ⟨a, ha⟩
  refine ⟨a, ha, ?_⟩
  intro b hb
  by_cases hba : b = a
  · exact hba
  · have hab : a ≠ b := by
      intro hab
      exact hba hab.symm
    exact False.elim (hdisjoint a b hab ⟨ha, hb⟩)

/--
Corollary 5.1.3, in derivation notation:
if `Cut[k,j,i] ∈ Π` brackets `j'`, then `Π[j']` has a `cutMe` label at a
target `i'` with `i' ≥ i`.
-/
theorem derivation_containsCut_bracketed_hasCutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) {m : T.Index}
    (him : cutI < T.paperIndex m) (hmk : T.paperIndex m < cutK) :
    ∃ cutLower : T.Index,
      T.paperIndex cutLower < T.paperIndex m ∧
      cutI ≤ T.paperIndex cutLower ∧
      HasCutMe (T.paperIndex cutLower) (deriv.get m) := by
  rcases containsCut_bracketed_hasCutMe hcut him hmk with
    ⟨cutLower, hlower_bound, hcutLower_m, hcutMe⟩
  exact ⟨cutLower, hcutLower_m, hlower_bound, by simpa [Derivation.get] using hcutMe⟩

/--
Corollary 5.1.3, with the displayed
`Π[j'] = cutMe_{i'} qtime` equality made explicit.
-/
theorem derivation_containsCut_bracketed_eq_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) {m : T.Index}
    (him : cutI < T.paperIndex m) (hmk : T.paperIndex m < cutK) :
    ∃ cutLower : T.Index, ∃ base : Time,
      T.paperIndex cutLower < T.paperIndex m ∧
      cutI ≤ T.paperIndex cutLower ∧
      deriv.get m = ⋊ (T.paperIndex cutLower) base := by
  rcases derivation_containsCut_bracketed_hasCutMe hcut him hmk with
    ⟨cutLower, hcutLower_m, hlower_bound, base, hshape⟩
  exact ⟨cutLower, base, hcutLower_m, hlower_bound, hshape⟩

/--
Corollary 5.1.3, with the strict
`j' > i'` part stated on Lean indices.
-/
theorem derivation_containsCut_bracketed_hasCutMe_val {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) {m : T.Index}
    (him : cutI < T.paperIndex m) (hmk : T.paperIndex m < cutK) :
    ∃ cutLower : T.Index,
      cutLower.val < m.val ∧ cutI ≤ T.paperIndex cutLower ∧
      HasCutMe (T.paperIndex cutLower) (deriv.get m) := by
  rcases derivation_containsCut_bracketed_hasCutMe hcut him hmk with
    ⟨cutLower, hcutLower_m, hlower_bound, hcutMe⟩
  exact
    ⟨cutLower, Nat.succ_lt_succ_iff.mp hcutLower_m, hlower_bound, hcutMe⟩

/--
Corollary 5.1.3, with both
`Π[j'] = cutMe_{i'} qtime` and the strict Lean-index inequality `j' > i'`
made explicit.
-/
theorem derivation_containsCut_bracketed_eq_cutMe_val {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) {m : T.Index}
    (him : cutI < T.paperIndex m) (hmk : T.paperIndex m < cutK) :
    ∃ cutLower : T.Index, ∃ base : Time,
      cutLower.val < m.val ∧
      cutI ≤ T.paperIndex cutLower ∧
      deriv.get m = ⋊ (T.paperIndex cutLower) base := by
  rcases derivation_containsCut_bracketed_eq_cutMe hcut him hmk with
    ⟨cutLower, base, hcutLower_m, hlower_bound, hshape⟩
  exact
    ⟨cutLower, base, Nat.succ_lt_succ_iff.mp hcutLower_m, hlower_bound, hshape⟩

end ConsistentHistories.Routes.PathProperties.Matryoshka
