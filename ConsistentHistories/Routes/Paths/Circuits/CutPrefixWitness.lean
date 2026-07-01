import ConsistentHistories.Routes.Paths.Circuits.CutPrefixData

namespace ConsistentHistories.Routes.Paths.Circuits

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.Cut.Flags
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Foundation.Paths.InitialPrefixes

namespace CutPrefixWitness

/--
Support lemma reconstructing a Cut's lower-endpoint datum in the final path.
Given a `CutPrefixWitness` for an occurrence of `(Cut_{k,j,i})` whose pre-Cut
derivation is an initial prefix of `deriv`, with the paper indices `cutJ` and
`cutI` identified as the final-path indices `center` (the `j` the Cut is centred
on) and `lower` (the `i`), it produces a `centerTime` and a `source` such that
the final lower entry `T.get lower` lies above the attestation
`source # centerTime`, and `centerTime` carries the controller of the final
centre entry `T.get center`. Both facts follow from times-increase along the
initial prefix (Lemma 4.2.2); this is a witness helper, not a numbered paper item.
-/
theorem attest_lower_bound {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (h : CutPrefixWitness deriv cutK cutJ cutI)
    {center lower : T.Index}
    (hcenter : cutJ = T.paperIndex center)
    (hlower : cutI = T.paperIndex lower) :
    ∃ source centerTime : Time,
      (source # centerTime) ≼ (T.get lower) ∧
        controller centerTime = controller (T.get center) := by
  rcases h with
    ⟨base, baseDeriv, idxI, idxJ, idxK, ti, tj, tk, hij, hjk, hk, hj, hi,
      hconsistent, _hcutK, hcutJ, hcutI, hprefix⟩
  let dcut := Derivation.cut baseDeriv hij hjk hk hj hi hconsistent
  let centerTime : Time := (Derivation.root dcut).get idxJ
  have hidxI_paper : base.paperIndex idxI = T.paperIndex lower := by
    exact hcutI.symm.trans hlower
  have hidxJ_paper : base.paperIndex idxJ = T.paperIndex center := by
    exact hcutJ.symm.trans hcenter
  have hidxI_cast : Fin.cast hprefix.length_eq idxI = lower := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hidxI_paper)
  have hidxJ_cast : Fin.cast hprefix.length_eq idxJ = center := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hidxJ_paper)
  have hshape :
      (Derivation.root dcut).get idxI = ti # centerTime := by
    have hi_ne_k : idxI ≠ idxK := by
      intro h
      cases h
      exact Nat.lt_irrefl idxI.val (Nat.lt_trans hij hjk)
    have hj_ne_k : idxJ ≠ idxK := by
      intro h
      cases h
      exact Nat.lt_irrefl idxJ.val hjk
    simp [dcut, centerTime, Derivation.root, Prepath.replace_get_ne base hi_ne_k,
      Prepath.replace_get_ne base hj_ne_k, hi, hj]
  have hlowerBound :
      (ti # centerTime) ≼ (T.get lower) := by
    have hle := InitialPrefix.times_increase hprefix idxI
    change (dcut.root.get idxI) ≼ (T.get (Fin.cast hprefix.length_eq idxI)) at hle
    rw [hshape] at hle
    simpa [hidxI_cast] using hle
  have hcenterBound := InitialPrefix.times_increase hprefix idxJ
  have hcenterController :
      controller centerTime = controller (T.get center) := by
    simpa [centerTime, dcut, hidxJ_cast] using hcenterBound.1
  exact ⟨ti, centerTime, hlowerBound, hcenterController⟩

end CutPrefixWitness

/-- Definition 4.3.6(2): the local (non-Cut) rule names
`(rulename) ∈ {(Inc), (⋈Intro), (⋉Intro)}`, each centred on a single index. -/
inductive LocalRuleKind where
  | inc
  | cutMeIntro
  | cutYouIntro
  deriving DecidableEq

/-- Definition 4.3.6(2), `(rulename_j) ∈ Π`: an instance of the local rule
`(rulename_j)` appears in `Π`, so `Π` contains an instance of `(rulename)`
centred on `j`. -/
inductive ContainsLocalRule {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    {T : Prepath Time} → Derivation Time T → LocalRuleKind → Nat → Prop where
  | here_inc {T : Prepath Time} (deriv : Derivation Time T) (j : T.Index) {t' : Time}
      (hlt : (T.get j) ≺ t')
      (hflag : flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
      (hconsistent : ConsistentTime t') :
      ContainsLocalRule (Derivation.inc deriv j hlt hflag hconsistent)
        LocalRuleKind.inc (T.paperIndex j)
  | here_cutMeIntro {T : Prepath Time} (deriv : Derivation Time T) (j : T.Index)
      (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋊ target t)) :
      ContainsLocalRule (Derivation.cutMeIntro deriv j target hshape hconsistent)
        LocalRuleKind.cutMeIntro (T.paperIndex j)
  | here_cutYouIntro {T : Prepath Time} (deriv : Derivation Time T) (j : T.Index)
      (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋉ target t)) :
      ContainsLocalRule (Derivation.cutYouIntro deriv j target hshape hconsistent)
        LocalRuleKind.cutYouIntro (T.paperIndex j)
  | inc {T : Prepath Time} {deriv : Derivation Time T} {kind : LocalRuleKind} {center : Nat}
      (h : ContainsLocalRule deriv kind center) (j : T.Index) {t' : Time}
      (hlt : (T.get j) ≺ t')
      (hflag : flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
      (hconsistent : ConsistentTime t') :
      ContainsLocalRule (Derivation.inc deriv j hlt hflag hconsistent) kind center
  | cutMeIntro {T : Prepath Time} {deriv : Derivation Time T}
      {kind : LocalRuleKind} {center : Nat}
      (h : ContainsLocalRule deriv kind center) (j : T.Index) (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋊ target t)) :
      ContainsLocalRule (Derivation.cutMeIntro deriv j target hshape hconsistent) kind center
  | cutYouIntro {T : Prepath Time} {deriv : Derivation Time T}
      {kind : LocalRuleKind} {center : Nat}
      (h : ContainsLocalRule deriv kind center) (j : T.Index) (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋉ target t)) :
      ContainsLocalRule (Derivation.cutYouIntro deriv j target hshape hconsistent) kind center
  | cut {T : Prepath Time} {deriv : Derivation Time T} {kind : LocalRuleKind} {center : Nat}
      (h : ContainsLocalRule deriv kind center) {i j k : T.Index}
      (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
      (hk : T.get k = ⋉ (T.paperIndex j) tk)
      (hj : T.get j =
        ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
      (hi : T.get i =
        ti # (⋊ (T.paperIndex i)
          (tj # (⋉ (T.paperIndex j) tk))))
      (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
      ContainsLocalRule (Derivation.cut deriv hij hjk hk hj hi hconsistent) kind center

/-- Definition 4.3.6(2): appending an `(Inc_j)` step yields a derivation
containing an instance of `(Inc)` centred on `j`. -/
theorem containsLocalRule_here_inc {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    ContainsLocalRule (Derivation.inc deriv j hlt hflag hconsistent)
      LocalRuleKind.inc (T.paperIndex j) := by
  exact ContainsLocalRule.here_inc deriv j hlt hflag hconsistent

/-- Definition 4.3.6(2): appending a `(⋈Intro_j)` step yields a derivation
containing an instance of `(⋈Intro)` centred on `j`. -/
theorem containsLocalRule_here_cutMeIntro {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    ContainsLocalRule (Derivation.cutMeIntro deriv j target hshape hconsistent)
      LocalRuleKind.cutMeIntro (T.paperIndex j) := by
  exact ContainsLocalRule.here_cutMeIntro deriv j target hshape hconsistent

/-- Definition 4.3.6(2): appending a `(⋉Intro_j)` step yields a derivation
containing an instance of `(⋉Intro)` centred on `j`. -/
theorem containsLocalRule_here_cutYouIntro {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    ContainsLocalRule (Derivation.cutYouIntro deriv j target hshape hconsistent)
      LocalRuleKind.cutYouIntro (T.paperIndex j) := by
  exact ContainsLocalRule.here_cutYouIntro deriv j target hshape hconsistent

/--
Computational witness for `ContainsLocalRule`: the list of local (non-Cut) rule
occurrences of a derivation, each recorded as its kind together with the paper
index it is centred on, most recent step first (Cut steps contribute nothing).
A support definition backing Definition 4.3.6(2), not a separate paper item.
-/
def localRuleOccurrences {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    {T : Prepath Time} → Derivation Time T → List (LocalRuleKind × Nat)
  | _, Derivation.init _ _ _ => []
  | _, Derivation.inc deriv changed _ _ _ =>
      (LocalRuleKind.inc, deriv.root.paperIndex changed) :: localRuleOccurrences deriv
  | _, Derivation.cutMeIntro deriv changed _ _ _ =>
      (LocalRuleKind.cutMeIntro, deriv.root.paperIndex changed) ::
        localRuleOccurrences deriv
  | _, Derivation.cutYouIntro deriv changed _ _ _ =>
      (LocalRuleKind.cutYouIntro, deriv.root.paperIndex changed) ::
        localRuleOccurrences deriv
  | _, Derivation.cut deriv _ _ _ _ _ _ => localRuleOccurrences deriv

theorem mem_localRuleOccurrences_of_containsLocalRule {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {kind : LocalRuleKind}
    {center : Nat} (hlocal : ContainsLocalRule deriv kind center) :
    (kind, center) ∈ localRuleOccurrences deriv := by
  induction hlocal with
  | here_inc _deriv _j _hlt _hflag _hconsistent =>
      simp [localRuleOccurrences, Derivation.root]
  | here_cutMeIntro _deriv _j _target _hshape _hconsistent =>
      simp [localRuleOccurrences, Derivation.root]
  | here_cutYouIntro _deriv _j _target _hshape _hconsistent =>
      simp [localRuleOccurrences, Derivation.root]
  | inc _h _changed _hlt _hflag _hconsistent ih =>
      simp [localRuleOccurrences, Derivation.root, ih]
  | cutMeIntro _h _changed _target _hshape _hconsistent ih =>
      simp [localRuleOccurrences, Derivation.root, ih]
  | cutYouIntro _h _changed _target _hshape _hconsistent ih =>
      simp [localRuleOccurrences, Derivation.root, ih]
  | cut _h _hij _hjk _hk _hj _hi _hconsistent ih =>
      simpa [localRuleOccurrences, Derivation.root] using ih

theorem containsLocalRule_of_mem_localRuleOccurrences {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T) {kind : LocalRuleKind}
      {center : Nat},
      (kind, center) ∈ localRuleOccurrences deriv →
        ContainsLocalRule deriv kind center := by
  intro T deriv
  induction deriv with
  | init _hpos _base _hconsistent =>
      intro _kind _center hmem
      simp [localRuleOccurrences] at hmem
  | inc deriv changed hlt hflag hconsistent ih =>
      intro kind center hmem
      simp [localRuleOccurrences, Derivation.root] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        exact ContainsLocalRule.here_inc deriv changed hlt hflag hconsistent
      · exact ContainsLocalRule.inc (ih htail) changed hlt hflag hconsistent
  | cutMeIntro deriv changed target hshape hconsistent ih =>
      intro kind center hmem
      simp [localRuleOccurrences, Derivation.root] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        exact ContainsLocalRule.here_cutMeIntro deriv changed target hshape hconsistent
      · exact ContainsLocalRule.cutMeIntro (ih htail) changed target hshape hconsistent
  | cutYouIntro deriv changed target hshape hconsistent ih =>
      intro kind center hmem
      simp [localRuleOccurrences, Derivation.root] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        exact ContainsLocalRule.here_cutYouIntro deriv changed target hshape hconsistent
      · exact ContainsLocalRule.cutYouIntro (ih htail) changed target hshape hconsistent
  | cut deriv hij hjk hk hj hi hconsistent ih =>
      intro kind center hmem
      exact ContainsLocalRule.cut (ih hmem) hij hjk hk hj hi hconsistent

theorem containsLocalRule_iff_mem_localRuleOccurrences {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {kind : LocalRuleKind}
    {center : Nat} :
    ContainsLocalRule deriv kind center ↔
      (kind, center) ∈ localRuleOccurrences deriv := by
  constructor
  · exact mem_localRuleOccurrences_of_containsLocalRule
  · exact containsLocalRule_of_mem_localRuleOccurrences deriv

/-- A local rule occurrence in an initial prefix remains present in every extension. -/
theorem containsLocalRule_of_initialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T1 T2 : Prepath Time} {d1 : Derivation Time T1} {d2 : Derivation Time T2}
      {kind : LocalRuleKind} {center : Nat},
      InitialPrefix d1 d2 →
        ContainsLocalRule d1 kind center →
          ContainsLocalRule d2 kind center := by
  intro T1 T2 d1 d2 kind center hprefix hlocal
  induction hprefix with
  | refl _deriv =>
      exact hlocal
  | inc _deriv _hp changed hlt hflag hconsistent ih =>
      exact ContainsLocalRule.inc (ih hlocal) changed hlt hflag hconsistent
  | cutMeIntro _deriv _hp changed target hshape hconsistent ih =>
      exact ContainsLocalRule.cutMeIntro (ih hlocal) changed target hshape hconsistent
  | cutYouIntro _deriv _hp changed target hshape hconsistent ih =>
      exact ContainsLocalRule.cutYouIntro (ih hlocal) changed target hshape hconsistent
  | cut _deriv _hp hij hjk hk hj hi hconsistent ih =>
      exact ContainsLocalRule.cut (ih hlocal) hij hjk hk hj hi hconsistent

/--
Prefix reformulation of `ContainsLocalRule`: an instance of `(rulename_j)`
occurs in `deriv` exactly when some initial prefix of `deriv` (Definition 4.2.1)
ends with that very `(rulename_j)` step centred on `j`. Support definition for
Definition 4.3.6(2), not a separate paper item.
-/
def LocalRulePrefixWitness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (kind : LocalRuleKind) (center : Nat) : Prop :=
  (∃ (base : Prepath Time) (baseDeriv : Derivation Time base) (idx : base.Index)
      (t' : Time)
      (hlt : lt (base.get idx) t')
      (hflag : flagOf cuttingFlagSet (base.get idx) =
        flagOf cuttingFlagSet t')
      (hconsistent : ConsistentTime t'),
      kind = LocalRuleKind.inc ∧
        center = base.paperIndex idx ∧
        InitialPrefix (Derivation.inc baseDeriv idx hlt hflag hconsistent) deriv) ∨
  (∃ (base : Prepath Time) (baseDeriv : Derivation Time base) (idx : base.Index)
      (target : Nat) (t : Time)
      (hshape : base.get idx = ↱ target t)
      (hconsistent : ConsistentTime (⋊ target t)),
      kind = LocalRuleKind.cutMeIntro ∧
        center = base.paperIndex idx ∧
        InitialPrefix
          (Derivation.cutMeIntro baseDeriv idx target hshape hconsistent) deriv) ∨
  (∃ (base : Prepath Time) (baseDeriv : Derivation Time base) (idx : base.Index)
      (target : Nat) (t : Time)
      (hshape : base.get idx = ↱ target t)
      (hconsistent : ConsistentTime (⋉ target t)),
      kind = LocalRuleKind.cutYouIntro ∧
        center = base.paperIndex idx ∧
        InitialPrefix
          (Derivation.cutYouIntro baseDeriv idx target hshape hconsistent) deriv)

theorem localRulePrefixWitness_of_containsLocalRule {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {kind : LocalRuleKind}
    {center : Nat} :
    ContainsLocalRule deriv kind center →
      LocalRulePrefixWitness deriv kind center := by
  intro hlocal
  induction hlocal with
  | here_inc deriv idx hlt hflag hconsistent =>
      left
      exact
        ⟨_, deriv, idx, _, hlt, hflag, hconsistent, rfl, rfl,
          InitialPrefix.refl
            (Derivation.inc deriv idx hlt hflag hconsistent)⟩
  | here_cutMeIntro deriv idx target hshape hconsistent =>
      right
      left
      exact
        ⟨_, deriv, idx, target, _, hshape, hconsistent, rfl, rfl,
          InitialPrefix.refl
            (Derivation.cutMeIntro deriv idx target hshape hconsistent)⟩
  | here_cutYouIntro deriv idx target hshape hconsistent =>
      right
      right
      exact
        ⟨_, deriv, idx, target, _, hshape, hconsistent, rfl, rfl,
          InitialPrefix.refl
            (Derivation.cutYouIntro deriv idx target hshape hconsistent)⟩
  | inc _h changed hlt hflag hconsistent ih =>
      rcases ih with hinc | hcutMe | hcutYou
      · rcases hinc with
          ⟨base, baseDeriv, idx, t', hlt0, hflag0, hconsistent0, hkind,
            hcenter, hprefix⟩
        left
        exact
          ⟨base, baseDeriv, idx, t', hlt0, hflag0, hconsistent0, hkind,
            hcenter, InitialPrefix.inc _ hprefix changed hlt hflag hconsistent⟩
      · rcases hcutMe with
          ⟨base, baseDeriv, idx, target, t, hshape, hconsistent0, hkind,
            hcenter, hprefix⟩
        right
        left
        exact
          ⟨base, baseDeriv, idx, target, t, hshape, hconsistent0, hkind,
            hcenter, InitialPrefix.inc _ hprefix changed hlt hflag hconsistent⟩
      · rcases hcutYou with
          ⟨base, baseDeriv, idx, target, t, hshape, hconsistent0, hkind,
            hcenter, hprefix⟩
        right
        right
        exact
          ⟨base, baseDeriv, idx, target, t, hshape, hconsistent0, hkind,
            hcenter, InitialPrefix.inc _ hprefix changed hlt hflag hconsistent⟩
  | cutMeIntro _h changed target hshape hconsistent ih =>
      rcases ih with hinc | hcutMe | hcutYou
      · rcases hinc with
          ⟨base, baseDeriv, idx, t', hlt0, hflag0, hconsistent0, hkind,
            hcenter, hprefix⟩
        left
        exact
          ⟨base, baseDeriv, idx, t', hlt0, hflag0, hconsistent0, hkind,
            hcenter,
            InitialPrefix.cutMeIntro _ hprefix changed target hshape hconsistent⟩
      · rcases hcutMe with
          ⟨base, baseDeriv, idx, target0, t, hshape0, hconsistent0, hkind,
            hcenter, hprefix⟩
        right
        left
        exact
          ⟨base, baseDeriv, idx, target0, t, hshape0, hconsistent0, hkind,
            hcenter,
            InitialPrefix.cutMeIntro _ hprefix changed target hshape hconsistent⟩
      · rcases hcutYou with
          ⟨base, baseDeriv, idx, target0, t, hshape0, hconsistent0, hkind,
            hcenter, hprefix⟩
        right
        right
        exact
          ⟨base, baseDeriv, idx, target0, t, hshape0, hconsistent0, hkind,
            hcenter,
            InitialPrefix.cutMeIntro _ hprefix changed target hshape hconsistent⟩
  | cutYouIntro _h changed target hshape hconsistent ih =>
      rcases ih with hinc | hcutMe | hcutYou
      · rcases hinc with
          ⟨base, baseDeriv, idx, t', hlt0, hflag0, hconsistent0, hkind,
            hcenter, hprefix⟩
        left
        exact
          ⟨base, baseDeriv, idx, t', hlt0, hflag0, hconsistent0, hkind,
            hcenter,
            InitialPrefix.cutYouIntro _ hprefix changed target hshape hconsistent⟩
      · rcases hcutMe with
          ⟨base, baseDeriv, idx, target0, t, hshape0, hconsistent0, hkind,
            hcenter, hprefix⟩
        right
        left
        exact
          ⟨base, baseDeriv, idx, target0, t, hshape0, hconsistent0, hkind,
            hcenter,
            InitialPrefix.cutYouIntro _ hprefix changed target hshape hconsistent⟩
      · rcases hcutYou with
          ⟨base, baseDeriv, idx, target0, t, hshape0, hconsistent0, hkind,
            hcenter, hprefix⟩
        right
        right
        exact
          ⟨base, baseDeriv, idx, target0, t, hshape0, hconsistent0, hkind,
            hcenter,
            InitialPrefix.cutYouIntro _ hprefix changed target hshape hconsistent⟩
  | cut _h hij hjk hk hj hi hconsistent ih =>
      rcases ih with hinc | hcutMe | hcutYou
      · rcases hinc with
          ⟨base, baseDeriv, idx, t', hlt0, hflag0, hconsistent0, hkind,
            hcenter, hprefix⟩
        left
        exact
          ⟨base, baseDeriv, idx, t', hlt0, hflag0, hconsistent0, hkind,
            hcenter,
            InitialPrefix.cut _ hprefix hij hjk hk hj hi hconsistent⟩
      · rcases hcutMe with
          ⟨base, baseDeriv, idx, target, t, hshape, hconsistent0, hkind,
            hcenter, hprefix⟩
        right
        left
        exact
          ⟨base, baseDeriv, idx, target, t, hshape, hconsistent0, hkind,
            hcenter,
            InitialPrefix.cut _ hprefix hij hjk hk hj hi hconsistent⟩
      · rcases hcutYou with
          ⟨base, baseDeriv, idx, target, t, hshape, hconsistent0, hkind,
            hcenter, hprefix⟩
        right
        right
        exact
          ⟨base, baseDeriv, idx, target, t, hshape, hconsistent0, hkind,
            hcenter,
            InitialPrefix.cut _ hprefix hij hjk hk hj hi hconsistent⟩

theorem containsLocalRule_of_localRulePrefixWitness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {kind : LocalRuleKind}
    {center : Nat} :
    LocalRulePrefixWitness deriv kind center →
      ContainsLocalRule deriv kind center := by
  intro hwitness
  rcases hwitness with hinc | hcutMe | hcutYou
  · rcases hinc with
      ⟨base, baseDeriv, idx, t', hlt, hflag, hconsistent, hkind, hcenter,
        hprefix⟩
    subst kind
    subst center
    exact containsLocalRule_of_initialPrefix hprefix
      (ContainsLocalRule.here_inc baseDeriv idx hlt hflag hconsistent)
  · rcases hcutMe with
      ⟨base, baseDeriv, idx, target, t, hshape, hconsistent, hkind, hcenter,
        hprefix⟩
    subst kind
    subst center
    exact containsLocalRule_of_initialPrefix hprefix
      (ContainsLocalRule.here_cutMeIntro baseDeriv idx target hshape hconsistent)
  · rcases hcutYou with
      ⟨base, baseDeriv, idx, target, t, hshape, hconsistent, hkind, hcenter,
        hprefix⟩
    subst kind
    subst center
    exact containsLocalRule_of_initialPrefix hprefix
      (ContainsLocalRule.here_cutYouIntro baseDeriv idx target hshape hconsistent)

theorem containsLocalRule_iff_prefixWitness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {kind : LocalRuleKind}
    {center : Nat} :
    ContainsLocalRule deriv kind center ↔
      LocalRulePrefixWitness deriv kind center := by
  constructor
  · exact localRulePrefixWitness_of_containsLocalRule
  · exact containsLocalRule_of_localRulePrefixWitness

/-- The centre recorded by `ContainsLocalRule` is a genuine index of the final
root: it equals `T.paperIndex` of some `T.Index`. A local rule is centred on an
index `j` (Definition 4.3.6(2)), and `index(T) = {1,…,length(T)}`
(Definition 4.1.1(3b)). -/
theorem containsLocalRule_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {kind : LocalRuleKind} {center : Nat}
    (h : ContainsLocalRule deriv kind center) :
    ∃ idx : T.Index, T.paperIndex idx = center := by
  induction h with
  | here_inc _deriv j _hlt _hflag _hconsistent =>
      exact ⟨j, rfl⟩
  | here_cutMeIntro _deriv j _target _hshape _hconsistent =>
      exact ⟨j, rfl⟩
  | here_cutYouIntro _deriv j _target _hshape _hconsistent =>
      exact ⟨j, rfl⟩
  | inc _h _changed _hlt _hflag _hconsistent ih =>
      rcases ih with ⟨idx, hidx⟩
      exact ⟨idx, hidx⟩
  | cutMeIntro _h _changed _target _hshape _hconsistent ih =>
      rcases ih with ⟨idx, hidx⟩
      exact ⟨idx, hidx⟩
  | cutYouIntro _h _changed _target _hshape _hconsistent ih =>
      rcases ih with ⟨idx, hidx⟩
      exact ⟨idx, hidx⟩
  | cut _h _hij _hjk _hk _hj _hi _hconsistent ih =>
      rcases ih with ⟨idx, hidx⟩
      exact ⟨idx, hidx⟩

/-- A local-rule centre (Definition 4.3.6(2)) is a positive, one-based paper
index, since `index(T) = {1,…,length(T)}` (Definition 4.1.1(3b)). -/
theorem containsLocalRule_center_pos {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {kind : LocalRuleKind} {center : Nat}
    (h : ContainsLocalRule deriv kind center) :
    0 < center := by
  rcases containsLocalRule_index h with ⟨idx, hidx⟩
  rw [← hidx]
  exact T.paperIndex_pos idx

/-- A local-rule centre (Definition 4.3.6(2)) is bounded by the final root
length, since `index(T) = {1,…,length(T)}` (Definition 4.1.1(3b)). -/
theorem containsLocalRule_center_le_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {kind : LocalRuleKind} {center : Nat}
    (h : ContainsLocalRule deriv kind center) :
    center <= T.length := by
  rcases containsLocalRule_index h with ⟨idx, hidx⟩
  rw [← hidx]
  exact T.paperIndex_le_length idx

end ConsistentHistories.Routes.Paths.Circuits
