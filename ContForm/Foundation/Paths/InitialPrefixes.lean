import ContForm.Foundation.Paths.Basic

/-!
Paper section 4.2: Initial prefixes.

-/

namespace ContForm.Foundation.Paths.InitialPrefixes

open ContForm.Foundation.LocatedSemilattices.Basic
open ContForm.Foundation.Cut.Flags
open ContForm.Foundation.Cut.Structure
open ContForm.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ContForm.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ContForm.Foundation.Paths.Basic

universe u v

/-- Definition 4.2.1(1): `Π₁` is an initial prefix of a derivation `Π` when `Π₁`,
viewed as a list, is a nonempty initial segment of `Π`. -/
inductive InitialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    {T1 T : Prepath Time} → Derivation Time T1 → Derivation Time T → Prop where
  | refl {T : Prepath Time} (deriv : Derivation Time T) : InitialPrefix deriv deriv
  | inc {T1 T : Prepath Time} {d1 : Derivation Time T1} (deriv : Derivation Time T)
      (h : InitialPrefix d1 deriv) (j : T.Index) {t' : Time}
      (hlt : (T.get j) ≺ t')
      (hflag : flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
      (hconsistent : ConsistentTime t') :
      InitialPrefix d1 (Derivation.inc deriv j hlt hflag hconsistent)
  | cutMeIntro {T1 T : Prepath Time} {d1 : Derivation Time T1} (deriv : Derivation Time T)
      (h : InitialPrefix d1 deriv) (j : T.Index) (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋊ target t)) :
      InitialPrefix d1 (Derivation.cutMeIntro deriv j target hshape hconsistent)
  | cutYouIntro {T1 T : Prepath Time} {d1 : Derivation Time T1} (deriv : Derivation Time T)
      (h : InitialPrefix d1 deriv) (j : T.Index) (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋉ target t)) :
      InitialPrefix d1 (Derivation.cutYouIntro deriv j target hshape hconsistent)
  | cut {T1 T : Prepath Time} {d1 : Derivation Time T1} (deriv : Derivation Time T)
      (h : InitialPrefix d1 deriv) {i j k : T.Index}
      (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
      (hk : T.get k = ⋉ (T.paperIndex j) tk)
      (hj : T.get j =
        ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
      (hi : T.get i =
        ti # (⋊ (T.paperIndex i)
          (tj # (⋉ (T.paperIndex j) tk))))
      (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
      InitialPrefix d1 (Derivation.cut deriv hij hjk hk hj hi hconsistent)

namespace InitialPrefix

theorem length_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (h : InitialPrefix d1 d) : T1.length = T.length := by
  induction h with
  | refl _deriv => rfl
  | inc _deriv _hp _j _hlt _hflag _hconsistent ih => simpa using ih
  | cutMeIntro _deriv _hp _j _target _hshape _hconsistent ih => simpa using ih
  | cutYouIntro _deriv _hp _j _target _hshape _hconsistent ih => simpa using ih
  | cut _deriv _hp _hij _hjk _hk _hj _hi _hconsistent ih => simpa using ih

/-- Under an initial prefix (Definition 4.2.1(1)) the prefix and its target derive
paths of the same length; casting an index of the prefix into the target path
preserves its paper index number. -/
theorem paperIndex_cast {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (h : InitialPrefix d1 d) (i : T1.Index) :
    T.paperIndex (Fin.cast h.length_eq i) = T1.paperIndex i := by
  simp [Prepath.paperIndex]

theorem trans {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T0 T1 T2 : Prepath Time}
    {d0 : Derivation Time T0} {d1 : Derivation Time T1} {d2 : Derivation Time T2}
    (h01 : InitialPrefix d0 d1) (h12 : InitialPrefix d1 d2) :
    InitialPrefix d0 d2 := by
  induction h12 generalizing T0 d0 with
  | refl _deriv =>
      exact h01
  | inc deriv h j hlt hflag hconsistent ih =>
      exact InitialPrefix.inc deriv (ih h01) j hlt hflag hconsistent
  | cutMeIntro deriv h j target hshape hconsistent ih =>
      exact InitialPrefix.cutMeIntro deriv (ih h01) j target hshape hconsistent
  | cutYouIntro deriv h j target hshape hconsistent ih =>
      exact InitialPrefix.cutYouIntro deriv (ih h01) j target hshape hconsistent
  | cut deriv h hij hjk hk hj hi hconsistent ih =>
      exact InitialPrefix.cut deriv (ih h01) hij hjk hk hj hi hconsistent

/-- Initial prefixes cannot have greater derivation height than their target. -/
theorem height_le {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (h : InitialPrefix d1 d) : d1.height ≤ d.height := by
  induction h with
  | refl _deriv =>
      exact Nat.le_refl _
  | inc _deriv _hp _j _hlt _hflag _hconsistent ih =>
      exact Nat.le_trans ih (Nat.le_succ _)
  | cutMeIntro _deriv _hp _j _target _hshape _hconsistent ih =>
      exact Nat.le_trans ih (Nat.le_succ _)
  | cutYouIntro _deriv _hp _j _target _hshape _hconsistent ih =>
      exact Nat.le_trans ih (Nat.le_succ _)
  | cut _deriv _hp _hij _hjk _hk _hj _hi _hconsistent ih =>
      exact Nat.le_trans ih (Nat.le_succ _)

/--
If an initial prefix has the same derivation height as its target, then it is
also an initial prefix in the reverse direction.
-/
theorem reverse_of_height_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (h : InitialPrefix d1 d) (heq : d1.height = d.height) :
    InitialPrefix d d1 := by
  induction h with
  | refl deriv =>
      exact InitialPrefix.refl deriv
  | inc _deriv hp _j _hlt _hflag _hconsistent _ih =>
      have hle := height_le hp
      simp [Derivation.height] at heq
      omega
  | cutMeIntro _deriv hp _j _target _hshape _hconsistent _ih =>
      have hle := height_le hp
      simp [Derivation.height] at heq
      omega
  | cutYouIntro _deriv hp _j _target _hshape _hconsistent _ih =>
      have hle := height_le hp
      simp [Derivation.height] at heq
      omega
  | cut _deriv hp _hij _hjk _hk _hj _hi _hconsistent _ih =>
      have hle := height_le hp
      simp [Derivation.height] at heq
      omega

/--
There is no strict initial prefix strictly between two derivations whose
heights differ by one.
-/
theorem no_intermediate_of_height_succ {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T0 Tmid T1 : Prepath Time}
    {d0 : Derivation Time T0} {dm : Derivation Time Tmid} {d1 : Derivation Time T1}
    (h0m : InitialPrefix d0 dm) (hm1 : InitialPrefix dm d1)
    (hheight : d1.height = d0.height + 1) :
    InitialPrefix dm d0 ∨ InitialPrefix d1 dm := by
  have h0m_le := height_le h0m
  have hm1_le := height_le hm1
  have hcases : dm.height = d0.height ∨ dm.height = d1.height := by
    omega
  rcases hcases with hmid_eq_start | hmid_eq_end
  · exact Or.inl (reverse_of_height_eq h0m (by omega))
  · exact Or.inr (reverse_of_height_eq hm1 hmid_eq_end)

/-- A derivation is a member of its own packed ancestor chain. -/
theorem self_mem_ancestors {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) :
    Derivation.pack deriv ∈ Derivation.ancestors deriv := by
  cases deriv <;> simp [Derivation.ancestors, Derivation.pack]

/-- Equality of packed derivations gives initial-prefix reflexivity after transport. -/
theorem initialPrefix_of_pack_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (h : Derivation.pack d1 = Derivation.pack d) : InitialPrefix d1 d := by
  cases h
  exact InitialPrefix.refl _

/-- Equality of packed derivations preserves derivation height. -/
theorem height_eq_of_pack_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (h : Derivation.pack d1 = Derivation.pack d) : d1.height = d.height := by
  cases h
  rfl

/-- Initial-prefix evidence places the prefix derivation in the target's ancestor chain. -/
theorem mem_ancestors_of_initialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T : Prepath Time} {d1 : Derivation Time T1} {d : Derivation Time T}
    (h : InitialPrefix d1 d) :
    Derivation.pack d1 ∈ Derivation.ancestors d := by
  induction h with
  | refl deriv =>
      exact self_mem_ancestors deriv
  | inc _deriv _hp _j _hlt _hflag _hconsistent ih =>
      simp [Derivation.ancestors, ih]
  | cutMeIntro _deriv _hp _j _target _hshape _hconsistent ih =>
      simp [Derivation.ancestors, ih]
  | cutYouIntro _deriv _hp _j _target _hshape _hconsistent ih =>
      simp [Derivation.ancestors, ih]
  | cut _deriv _hp _hij _hjk _hk _hj _hi _hconsistent ih =>
      simp [Derivation.ancestors, ih]

/-- Packed ancestor-chain membership recovers initial-prefix evidence. -/
theorem initialPrefix_of_mem_ancestors {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T1 T : Prepath Time} {d1 : Derivation Time T1} {d : Derivation Time T},
      Derivation.pack d1 ∈ Derivation.ancestors d → InitialPrefix d1 d := by
  intro T1 T d1 d hmem
  induction d generalizing T1 d1 with
  | init _hpos _base _hconsistent =>
      have hpack :
          Derivation.pack d1 =
            Derivation.pack (Derivation.init _hpos _base _hconsistent) := by
        simpa [Derivation.ancestors] using hmem
      exact initialPrefix_of_pack_eq hpack
  | inc deriv j hlt hflag hconsistent ih =>
      simp [Derivation.ancestors] at hmem
      rcases hmem with hhead | htail
      · exact initialPrefix_of_pack_eq hhead
      · exact InitialPrefix.inc deriv (ih htail) j hlt hflag hconsistent
  | cutMeIntro deriv j target hshape hconsistent ih =>
      simp [Derivation.ancestors] at hmem
      rcases hmem with hhead | htail
      · exact initialPrefix_of_pack_eq hhead
      · exact InitialPrefix.cutMeIntro deriv (ih htail) j target hshape hconsistent
  | cutYouIntro deriv j target hshape hconsistent ih =>
      simp [Derivation.ancestors] at hmem
      rcases hmem with hhead | htail
      · exact initialPrefix_of_pack_eq hhead
      · exact InitialPrefix.cutYouIntro deriv (ih htail) j target hshape hconsistent
  | cut deriv hij hjk hk hj hi hconsistent ih =>
      simp [Derivation.ancestors] at hmem
      rcases hmem with hhead | htail
      · exact initialPrefix_of_pack_eq hhead
      · exact InitialPrefix.cut deriv (ih htail) hij hjk hk hj hi hconsistent

/--
For two packed ancestors of the same derivation, the lower-height ancestor is
an initial prefix of the higher-height ancestor.
-/
theorem initialPrefix_of_mem_ancestors_height_le {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T0 T1 T : Prepath Time} {d0 : Derivation Time T0}
      {d1 : Derivation Time T1} {d : Derivation Time T},
      Derivation.pack d0 ∈ Derivation.ancestors d →
      Derivation.pack d1 ∈ Derivation.ancestors d →
      d0.height ≤ d1.height →
        InitialPrefix d0 d1 := by
  intro T0 T1 T d0 d1 d h0 h1 hle
  induction d generalizing T0 T1 d0 d1 with
  | init _hpos _base _hconsistent =>
      have h0pack :
          Derivation.pack d0 =
            Derivation.pack (Derivation.init _hpos _base _hconsistent) := by
        simpa [Derivation.ancestors] using h0
      have h1pack :
          Derivation.pack d1 =
            Derivation.pack (Derivation.init _hpos _base _hconsistent) := by
        simpa [Derivation.ancestors] using h1
      exact initialPrefix_of_pack_eq (h0pack.trans h1pack.symm)
  | inc deriv j hlt hflag hconsistent ih =>
      simp [Derivation.ancestors] at h0 h1
      rcases h1 with h1head | h1tail
      · have h0Current :
            InitialPrefix d0 (Derivation.inc deriv j hlt hflag hconsistent) := by
          rcases h0 with h0head | h0tail
          · exact initialPrefix_of_pack_eq h0head
          · exact InitialPrefix.inc deriv (initialPrefix_of_mem_ancestors h0tail)
              j hlt hflag hconsistent
        exact InitialPrefix.trans h0Current
          (initialPrefix_of_pack_eq h1head.symm)
      · rcases h0 with h0head | h0tail
        · have hd0Height := height_eq_of_pack_eq h0head
          have hd1PrefixDeriv : InitialPrefix d1 deriv :=
            initialPrefix_of_mem_ancestors h1tail
          have hd1Height := height_le hd1PrefixDeriv
          simp [Derivation.height] at hd0Height
          omega
        · exact ih h0tail h1tail hle
  | cutMeIntro deriv j target hshape hconsistent ih =>
      simp [Derivation.ancestors] at h0 h1
      rcases h1 with h1head | h1tail
      · have h0Current :
            InitialPrefix d0
              (Derivation.cutMeIntro deriv j target hshape hconsistent) := by
          rcases h0 with h0head | h0tail
          · exact initialPrefix_of_pack_eq h0head
          · exact InitialPrefix.cutMeIntro deriv
              (initialPrefix_of_mem_ancestors h0tail) j target hshape hconsistent
        exact InitialPrefix.trans h0Current
          (initialPrefix_of_pack_eq h1head.symm)
      · rcases h0 with h0head | h0tail
        · have hd0Height := height_eq_of_pack_eq h0head
          have hd1PrefixDeriv : InitialPrefix d1 deriv :=
            initialPrefix_of_mem_ancestors h1tail
          have hd1Height := height_le hd1PrefixDeriv
          simp [Derivation.height] at hd0Height
          omega
        · exact ih h0tail h1tail hle
  | cutYouIntro deriv j target hshape hconsistent ih =>
      simp [Derivation.ancestors] at h0 h1
      rcases h1 with h1head | h1tail
      · have h0Current :
            InitialPrefix d0
              (Derivation.cutYouIntro deriv j target hshape hconsistent) := by
          rcases h0 with h0head | h0tail
          · exact initialPrefix_of_pack_eq h0head
          · exact InitialPrefix.cutYouIntro deriv
              (initialPrefix_of_mem_ancestors h0tail) j target hshape hconsistent
        exact InitialPrefix.trans h0Current
          (initialPrefix_of_pack_eq h1head.symm)
      · rcases h0 with h0head | h0tail
        · have hd0Height := height_eq_of_pack_eq h0head
          have hd1PrefixDeriv : InitialPrefix d1 deriv :=
            initialPrefix_of_mem_ancestors h1tail
          have hd1Height := height_le hd1PrefixDeriv
          simp [Derivation.height] at hd0Height
          omega
        · exact ih h0tail h1tail hle
  | cut deriv hij hjk hk hj hi hconsistent ih =>
      simp [Derivation.ancestors] at h0 h1
      rcases h1 with h1head | h1tail
      · have h0Current :
            InitialPrefix d0
              (Derivation.cut deriv hij hjk hk hj hi hconsistent) := by
          rcases h0 with h0head | h0tail
          · exact initialPrefix_of_pack_eq h0head
          · exact InitialPrefix.cut deriv (initialPrefix_of_mem_ancestors h0tail)
              hij hjk hk hj hi hconsistent
        exact InitialPrefix.trans h0Current
          (initialPrefix_of_pack_eq h1head.symm)
      · rcases h0 with h0head | h0tail
        · have hd0Height := height_eq_of_pack_eq h0head
          have hd1PrefixDeriv : InitialPrefix d1 deriv :=
            initialPrefix_of_mem_ancestors h1tail
          have hd1Height := height_le hd1PrefixDeriv
          simp [Derivation.height] at hd0Height
          omega
        · exact ih h0tail h1tail hle

/--
Initial prefixes of a fixed derivation are linearly ordered by the
initial-prefix relation.
-/
theorem comparable {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T0 T1 T : Prepath Time} {d0 : Derivation Time T0}
      {d1 : Derivation Time T1} {d : Derivation Time T},
      InitialPrefix d0 d → InitialPrefix d1 d →
        InitialPrefix d0 d1 ∨ InitialPrefix d1 d0 := by
  intro _T0 _T1 _T d0 d1 d h0 h1
  have h0mem := mem_ancestors_of_initialPrefix h0
  have h1mem := mem_ancestors_of_initialPrefix h1
  rcases Nat.le_total d0.height d1.height with hle | hle
  · exact Or.inl (initialPrefix_of_mem_ancestors_height_le h0mem h1mem hle)
  · exact Or.inr (initialPrefix_of_mem_ancestors_height_le h1mem h0mem hle)

/--
Initial-prefix support for one-step derivation extensions: a prefix of a
derivation whose height is exactly one more than `d0` either lies before `d0`
or reaches the final derivation.
-/
theorem immediate_extension_cases {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T0 Tmid T1 : Prepath Time}
    {d0 : Derivation Time T0} {dm : Derivation Time Tmid} {d1 : Derivation Time T1}
    (h0Final : InitialPrefix d0 d1) (hmFinal : InitialPrefix dm d1)
    (hheight : d1.height = d0.height + 1) :
    InitialPrefix dm d0 ∨ InitialPrefix d1 dm := by
  rcases comparable hmFinal h0Final with hmidBefore | hbeforeMid
  · exact Or.inl hmidBefore
  · exact no_intermediate_of_height_succ hbeforeMid hmFinal hheight

/--
Initial-prefix support for a final `Inc` step: every prefix of the extended
derivation either lies before the `Inc`, or contains the whole extended
derivation.
-/
theorem inc_cases {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {Tmid Tpref : Prepath Time}
    {deriv : Derivation Time Tmid} {pref : Derivation Time Tpref}
    (j : Tmid.Index) {t' : Time}
    (hlt : (Tmid.get j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (Tmid.get j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t')
    (hpref : InitialPrefix pref (Derivation.inc deriv j hlt hflag hconsistent)) :
    InitialPrefix pref deriv ∨
      InitialPrefix (Derivation.inc deriv j hlt hflag hconsistent) pref := by
  exact
    immediate_extension_cases
      (InitialPrefix.inc deriv (InitialPrefix.refl deriv) j hlt hflag hconsistent)
      hpref rfl

theorem replace_le_of {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) (t : Time) (hctrl hconsistent)
    (hle : (T.get j) ≼ t) (i : T.Index) :
    (T.get i) ≼ ((T.replace j t hctrl hconsistent).get i) := by
  by_cases hij : i = j
  · subst hij
    simpa using hle
  · rw [Prepath.replace_get_ne T hij]
    exact le_refl (T.get i)

/-- Lemma 4.2.2 (Times increase): if `Π₁` is an initial prefix of `Π` and
`i ∈ index(Π₁)` then `Π₁[i] ≤ Π[i]`. -/
theorem times_increase {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (h : InitialPrefix d1 d) :
    ∀ i : T1.Index, (T1.get i) ≼ (T.get (Fin.cast h.length_eq i)) := by
  induction h with
  | refl _deriv =>
    intro _i
    exact le_refl _
  | inc _deriv hp j hlt _hflag _hconsistent ih =>
    intro i
    exact le_trans (ih i)
      (replace_le_of _ _ _ _ _ hlt.1 (Fin.cast (length_eq hp) i))
  | cutMeIntro _deriv hp j target hshape _hconsistent ih =>
    intro i
    rename_i Tmid _d1mid base
    have hle : (Tmid.get j) ≼ (⋊ target base) := by
      rw [hshape]
      exact next_le_cutme target base
    exact le_trans (ih i)
      (replace_le_of _ _ _ _ _ hle (Fin.cast (length_eq hp) i))
  | cutYouIntro _deriv hp j target hshape _hconsistent ih =>
    intro i
    rename_i Tmid _d1mid base
    have hle : (Tmid.get j) ≼ (⋉ target base) := by
      rw [hshape]
      exact next_le_cutyou target base
    exact le_trans (ih i)
      (replace_le_of _ _ _ _ _ hle (Fin.cast (length_eq hp) i))
  | cut _deriv hp hij _hjk hk _hj _hi _hconsistent ih =>
    intro idx
    rename_i Tmid _d1mid i j k _ti _tj tk
    have htarget : Tmid.paperIndex i < Tmid.paperIndex j := Nat.succ_lt_succ hij
    have hle : (Tmid.get k) ≼ (↱ (Tmid.paperIndex i) tk) := by
      rw [hk]
      exact cutyou_le_next htarget tk
    exact le_trans (ih idx)
      (replace_le_of _ _ _ _ _ hle (Fin.cast (length_eq hp) idx))

/-- Lemma 4.2.2, in the derivation notation `Π₁[i] ≤ Π[i]`. -/
theorem derivation_times_increase {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T : Prepath Time}
    {d1 : Derivation Time T1} {d : Derivation Time T}
    (h : InitialPrefix d1 d) :
    ∀ i : d1.Index, (d1.get i) ≼ (d.get (Fin.cast h.length_eq i)) := by
  intro i
  simpa [Derivation.get] using times_increase h i

/--
Mutual initial prefixes have the same pointwise derivation times. This packages
the antisymmetry step needed when prefix case splits return a derivation that
is also an initial prefix of the original derivation.
-/
theorem derivation_get_eq_of_mutual {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T0 T1 : Prepath Time} {d0 : Derivation Time T0} {d1 : Derivation Time T1}
    (h01 : InitialPrefix d0 d1) (h10 : InitialPrefix d1 d0) :
    ∀ i : d0.Index,
      d0.get i = d1.get (Fin.cast h01.length_eq i) := by
  intro i
  let j : d1.Index := Fin.cast h01.length_eq i
  have hback : Fin.cast h10.length_eq j = i := by
    apply Fin.ext
    simp [j]
  have hle01 : (d0.get i) ≼ (d1.get j) := by
    simpa [j] using InitialPrefix.derivation_times_increase h01 i
  have hle10 : (d1.get j) ≼ (d0.get i) := by
    have hraw := InitialPrefix.derivation_times_increase h10 j
    simpa [hback] using hraw
  exact le_antisymm hle01 hle10

/-- Symmetric pointwise equality form for mutual initial prefixes. -/
theorem derivation_get_eq_of_mutual_symm {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T0 T1 : Prepath Time} {d0 : Derivation Time T0} {d1 : Derivation Time T1}
    (h01 : InitialPrefix d0 d1) (h10 : InitialPrefix d1 d0) :
    ∀ i : d1.Index,
      d1.get i = d0.get (Fin.cast h10.length_eq i) := by
  exact derivation_get_eq_of_mutual h10 h01

/--
Mutual initial prefixes transport inactive witnesses. This is the structural
counterpart to `derivation_get_eq_of_mutual`: an inactive witness only depends
on index order, paper indexes, and the upper-index time.
-/
theorem inactive_of_mutual {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T0 T1 : Prepath Time} {d0 : Derivation Time T0} {d1 : Derivation Time T1}
    (h01 : InitialPrefix d0 d1) (h10 : InitialPrefix d1 d0)
    {i : d0.Index} (hinactive : d0.Inactive i) :
    d1.Inactive (Fin.cast h01.length_eq i) := by
  rcases hinactive with ⟨upper, lower, hinactiveBetween⟩
  refine
    ⟨Fin.cast h01.length_eq upper, Fin.cast h01.length_eq lower, ?_⟩
  refine ⟨by simpa using hinactiveBetween.1, by simpa using hinactiveBetween.2.1, ?_⟩
  have hpaper :
      T1.paperIndex (Fin.cast h01.length_eq lower) =
        T0.paperIndex lower :=
    InitialPrefix.paperIndex_cast h01 lower
  have hupper :
      T1.get (Fin.cast h01.length_eq upper) = T0.get upper := by
    simpa [Derivation.get] using
      (InitialPrefix.derivation_get_eq_of_mutual h01 h10 upper).symm
  simpa [hpaper, hupper] using
    hinactiveBetween.2.2

end InitialPrefix

/-- Definition 4.2.1(2): a pair `(Π₁, Π₁')` is an initial prefix of `(Π, Π')` when
`Π₁` is an initial prefix of `Π` and `Π₁'` is an initial prefix of `Π'`. -/
def PairInitialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T T1' T' : Prepath Time}
    (d1 : Derivation Time T1) (d1' : Derivation Time T1')
    (d : Derivation Time T) (d' : Derivation Time T') : Prop :=
  InitialPrefix d1 d ∧ InitialPrefix d1' d'

/-- Definition 4.2.1(2): the left component of a pair initial prefix is an initial
prefix. -/
theorem PairInitialPrefix.left_prefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') :
    InitialPrefix d1 d := by
  exact h.1

/-- Definition 4.2.1(2): the right component of a pair initial prefix is an initial
prefix. -/
theorem PairInitialPrefix.right_prefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') :
    InitialPrefix d1' d' := by
  exact h.2

theorem PairInitialPrefix.refl {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T T' : Prepath Time}
    (d : Derivation Time T) (d' : Derivation Time T') :
    PairInitialPrefix d d' d d' := by
  exact ⟨InitialPrefix.refl d, InitialPrefix.refl d'⟩

theorem PairInitialPrefix.trans {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T0 T1 T2 T0' T1' T2' : Prepath Time}
    {d0 : Derivation Time T0} {d1 : Derivation Time T1} {d2 : Derivation Time T2}
    {d0' : Derivation Time T0'} {d1' : Derivation Time T1'} {d2' : Derivation Time T2'}
    (h01 : PairInitialPrefix d0 d0' d1 d1')
    (h12 : PairInitialPrefix d1 d1' d2 d2') :
    PairInitialPrefix d0 d0' d2 d2' := by
  exact ⟨InitialPrefix.trans h01.1 h12.1, InitialPrefix.trans h01.2 h12.2⟩

/-- In a pair initial prefix (Definition 4.2.1(2)), the two left derivations derive
paths of the same length. -/
theorem PairInitialPrefix.left_length_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') :
    T1.length = T.length :=
  InitialPrefix.length_eq h.1

/-- In a pair initial prefix (Definition 4.2.1(2)), the two right derivations derive
paths of the same length. -/
theorem PairInitialPrefix.right_length_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') :
    T1'.length = T'.length :=
  InitialPrefix.length_eq h.2

/-- In a pair initial prefix (Definition 4.2.1(2)), casting a left index into the target
left path preserves its paper index number. -/
theorem PairInitialPrefix.left_paperIndex_cast {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') (i : T1.Index) :
    T.paperIndex (Fin.cast (InitialPrefix.length_eq h.1) i) = T1.paperIndex i :=
  InitialPrefix.paperIndex_cast h.1 i

/-- In a pair initial prefix (Definition 4.2.1(2)), casting a right index into the target
right path preserves its paper index number. -/
theorem PairInitialPrefix.right_paperIndex_cast {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') (i : T1'.Index) :
    T'.paperIndex (Fin.cast (InitialPrefix.length_eq h.2) i) = T1'.paperIndex i :=
  InitialPrefix.paperIndex_cast h.2 i

/-- Lemma 4.2.2 (Times increase) for the left component of a pair initial prefix
(Definition 4.2.1(2)). -/
theorem PairInitialPrefix.left_times_increase {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') :
    ∀ i : T1.Index, (T1.get i) ≼ (T.get (Fin.cast (InitialPrefix.length_eq h.1) i)) :=
  InitialPrefix.times_increase h.1

/-- Lemma 4.2.2 (Times increase) for the right component of a pair initial prefix
(Definition 4.2.1(2)). -/
theorem PairInitialPrefix.right_times_increase {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') :
    ∀ i : T1'.Index, (T1'.get i) ≼ (T'.get (Fin.cast (InitialPrefix.length_eq h.2) i)) :=
  InitialPrefix.times_increase h.2

/-- Lemma 4.2.2 (Times increase) for the left component of a pair initial prefix,
in derivation notation (Definition 4.2.1(2)). -/
theorem PairInitialPrefix.left_derivation_times_increase {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') :
    ∀ i : d1.Index, (d1.get i) ≼ (d.get (Fin.cast (InitialPrefix.length_eq h.1) i)) := by
  intro i
  simpa [Derivation.get] using PairInitialPrefix.left_times_increase h i

/-- Lemma 4.2.2 (Times increase) for the right component of a pair initial prefix,
in derivation notation (Definition 4.2.1(2)). -/
theorem PairInitialPrefix.right_derivation_times_increase {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T1 T T1' T' : Prepath Time}
    {d1 : Derivation Time T1} {d1' : Derivation Time T1'}
    {d : Derivation Time T} {d' : Derivation Time T'}
    (h : PairInitialPrefix d1 d1' d d') :
    ∀ i : d1'.Index, (d1'.get i) ≼ (d'.get (Fin.cast (InitialPrefix.length_eq h.2) i)) := by
  intro i
  simpa [Derivation.get] using PairInitialPrefix.right_times_increase h i

end ContForm.Foundation.Paths.InitialPrefixes
