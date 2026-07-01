import ConsistentHistories.Foundation.LocatedSemilattices.Basic

/-!
Paper section 3.1: Flags and flag-sets.

-/

namespace ConsistentHistories.Foundation.Cut.Flags

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice

universe u v

/-- Definition 3.1.1: a flag is a controller-preserving, expansive operator on times. -/
structure Flag (Time : Type v) {Ctrl : Type u} [LocatedSemilattice Time Ctrl] where
  toFun : Time → Time
  controller_preserving : ∀ t : Time, controller (toFun t) = controller t
  expansive : ∀ t : Time, t ≼ (toFun t)

instance {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] :
    CoeFun (Flag Time) (fun _ => Time → Time) where
  coe Q := Q.toFun

/-- Definition 3.1.3: a flag-set — flag application is injective where consistent. -/
structure FlagSet (Time : Type v) {Ctrl : Type u} [LocatedSemilattice Time Ctrl] where
  member : Flag Time → Prop
  injective_where_consistent :
    ∀ {Q Q' : Flag Time} {t t' : Time}, member Q → member Q' →
      ConsistentTime (Q t) → Q t = Q' t' → Q = Q'

variable {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]

/-- Definition 3.1.1: flags preserve controllers. -/
theorem Flag.apply_controller (Q : Flag Time) (t : Time) :
    controller (Q t) = controller t := by
  exact Q.controller_preserving t

/-- Definition 3.1.1(2): flags are expansive — `t ≼ Q t`. -/
theorem Flag.apply_le (Q : Flag Time) (t : Time) :
    t ≼ (Q t) := by
  exact Q.expansive t

/-- Definition 3.1.2: `t` has the form `Q⊖` — `t` is consistent and equals `Q t'` for some
`t'`. -/
def HasForm (Q : Flag Time) (t : Time) : Prop :=
  ConsistentTime t ∧ ∃ t' : Time, t = Q t'

/-- Definition 3.1.2: a time of flag form is consistent. -/
theorem hasForm_consistent
    {Q : Flag Time} {t : Time}
    (hform : HasForm Q t) : ConsistentTime t :=
  hform.1

/-- Definition 3.1.2: a time of flag form has a base time. -/
theorem hasForm_exists_eq
    {Q : Flag Time} {t : Time}
    (hform : HasForm Q t) : ∃ base : Time, t = Q base :=
  hform.2

/-- Definition 3.1.2: a time of flag form preserves the base controller. -/
theorem hasForm_controller_eq
    {Q : Flag Time} {t : Time}
    (hform : HasForm Q t) :
    ∃ base : Time, t = Q base ∧ controller t = controller base := by
  rcases hasForm_exists_eq hform with ⟨base, hbase⟩
  refine ⟨base, hbase, ?_⟩
  rw [hbase]
  exact Q.controller_preserving base

/-- Definition 3.1.3: equal consistent flag applications determine equal flags. -/
theorem flag_eq_of_hasForm_eq
    (Qset : FlagSet Time)
    {Q Q' : Flag Time} (hQ : Qset.member Q) (hQ' : Qset.member Q')
    {t t' : Time} (hform : HasForm Q t) (hform' : HasForm Q' t')
    (heq : t = t') : Q = Q' := by
  rcases hform with ⟨hconsistent, ⟨base, hbase⟩⟩
  rcases hform' with ⟨_hconsistent', ⟨base', hbase'⟩⟩
  apply Qset.injective_where_consistent hQ hQ'
  · rw [← hbase]
    exact hconsistent
  · calc
      Q base = t := hbase.symm
      _ = t' := heq
      _ = Q' base' := hbase'

/-- Definition 3.1.3: a time's flag is unique, when it exists. -/
theorem flag_unique_of_hasForm
    (Qset : FlagSet Time)
    {Q Q' : Flag Time} (hQ : Qset.member Q) (hQ' : Qset.member Q')
    {t : Time} (hform : HasForm Q t) (hform' : HasForm Q' t) :
    Q = Q' :=
  flag_eq_of_hasForm_eq Qset hQ hQ' hform hform' rfl

/--
Definition 3.1.4.

The paper's `undef` value is represented by `Option.none`; a present flag is
represented by `Option.some`.
-/
noncomputable def flagOf (Qset : FlagSet Time) (t : Time) :
    Option {Q : Flag Time // Qset.member Q} := by
  classical
  exact
    if h : ∃ Q : Flag Time, Qset.member Q ∧ HasForm Q t then
      some ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    else
      none

/-- Definition 3.1.4: `flagOf` is undefined when no member flag has the given form. -/
theorem flagOf_eq_none_of_no_hasForm
    (Qset : FlagSet Time) {t : Time}
    (h : ∀ Q : Flag Time, Qset.member Q → ¬ HasForm Q t) :
    flagOf Qset t = none := by
  classical
  have hnone : ¬ ∃ Q : Flag Time, Qset.member Q ∧ HasForm Q t := by
    intro hex
    rcases hex with ⟨Q, hmem, hform⟩
    exact h Q hmem hform
  unfold flagOf
  simp [hnone]

/-- Definition 3.1.4: `flagOf` returns the member flag whose form `t` has. -/
theorem flagOf_eq_some_of_hasForm
    (Qset : FlagSet Time)
    {Q : Flag Time} (hmem : Qset.member Q) {t : Time}
    (hform : HasForm Q t) : flagOf Qset t = some ⟨Q, hmem⟩ := by
  classical
  unfold flagOf
  have hex : ∃ Q : Flag Time, Qset.member Q ∧ HasForm Q t := ⟨Q, hmem, hform⟩
  simp [hex]
  have hchosen : Classical.choose hex = Q := by
    rcases (Classical.choose_spec hex).2.2 with ⟨baseChosen, hbaseChosen⟩
    rcases hform.2 with ⟨baseQ, hbaseQ⟩
    apply Qset.injective_where_consistent (Classical.choose_spec hex).1 hmem
    · rw [← hbaseChosen]
      exact (Classical.choose_spec hex).2.1
    · exact hbaseChosen.symm.trans hbaseQ
  exact hchosen

/-- Definition 3.1.4: a defined `flagOf` value certifies that `t` has that flag's form. -/
theorem flagOf_eq_some_hasForm
    (Qset : FlagSet Time)
    {t : Time} {Q : {Q : Flag Time // Qset.member Q}}
    (h : flagOf Qset t = some Q) : HasForm Q.1 t := by
  classical
  unfold flagOf at h
  by_cases hex : ∃ Q : Flag Time, Qset.member Q ∧ HasForm Q t
  · simp [hex] at h
    rw [← h]
    exact (Classical.choose_spec hex).2
  · simp [hex] at h

/-- Definition 3.1.4: a defined `flagOf` value certifies consistency. -/
theorem flagOf_eq_some_consistent
    (Qset : FlagSet Time)
    {t : Time} {Q : {Q : Flag Time // Qset.member Q}}
    (h : flagOf Qset t = some Q) : ConsistentTime t :=
  hasForm_consistent (flagOf_eq_some_hasForm Qset h)

/-- Definition 3.1.4: a defined `flagOf` value has a base time witness. -/
theorem flagOf_eq_some_exists_eq
    (Qset : FlagSet Time)
    {t : Time} {Q : {Q : Flag Time // Qset.member Q}}
    (h : flagOf Qset t = some Q) : ∃ base : Time, t = Q.1 base :=
  hasForm_exists_eq (flagOf_eq_some_hasForm Qset h)

/-- Definition 3.1.4: a defined `flagOf` value preserves the base controller. -/
theorem flagOf_eq_some_controller_eq
    (Qset : FlagSet Time)
    {t : Time} {Q : {Q : Flag Time // Qset.member Q}}
    (h : flagOf Qset t = some Q) :
    ∃ base : Time, t = Q.1 base ∧ controller t = controller base :=
  hasForm_controller_eq (flagOf_eq_some_hasForm Qset h)

theorem flagOf_eq_some_iff_hasForm
    (Qset : FlagSet Time)
    {Q : Flag Time} (hmem : Qset.member Q) {t : Time} :
    flagOf Qset t = some ⟨Q, hmem⟩ ↔ HasForm Q t := by
  constructor
  · intro h
    exact flagOf_eq_some_hasForm Qset h
  · intro hform
    exact flagOf_eq_some_of_hasForm Qset hmem hform

/-- Definition 3.1.4: `flagOf` is undefined iff no member flag has the given form. -/
theorem flagOf_eq_none_iff_no_hasForm
    (Qset : FlagSet Time) {t : Time} :
    flagOf Qset t = none ↔
      ∀ Q : Flag Time, Qset.member Q → ¬ HasForm Q t := by
  constructor
  · intro hnone Q hmem hform
    have hsome : flagOf Qset t = some ⟨Q, hmem⟩ :=
      flagOf_eq_some_of_hasForm Qset hmem hform
    rw [hnone] at hsome
    cases hsome
  · exact flagOf_eq_none_of_no_hasForm Qset

/--
Definition 3.1.4: the lookup is defined exactly when some
member flag has the requested form.
-/
theorem flagOf_ne_none_iff_exists_hasForm
    (Qset : FlagSet Time) {t : Time} :
    flagOf Qset t ≠ none ↔
      ∃ Q : Flag Time, Qset.member Q ∧ HasForm Q t := by
  constructor
  · intro hne
    classical
    by_cases hex : ∃ Q : Flag Time, Qset.member Q ∧ HasForm Q t
    · exact hex
    · exact False.elim (hne (flagOf_eq_none_of_no_hasForm Qset (by
        intro Q hmem hform
        exact hex ⟨Q, hmem, hform⟩)))
  · intro hex hnone
    rcases hex with ⟨Q, hmem, hform⟩
    have hsome : flagOf Qset t = some ⟨Q, hmem⟩ :=
      flagOf_eq_some_of_hasForm Qset hmem hform
    rw [hnone] at hsome
    cases hsome

/--
Definition 3.1.4: the lookup returns a present member flag
exactly when the time has some member flag form.
-/
theorem flagOf_exists_some_iff_exists_hasForm
    (Qset : FlagSet Time) {t : Time} :
    (∃ Q : {Q : Flag Time // Qset.member Q}, flagOf Qset t = some Q) ↔
      ∃ Q : Flag Time, Qset.member Q ∧ HasForm Q t := by
  constructor
  · intro hsome
    rcases hsome with ⟨Q, hQ⟩
    exact ⟨Q.1, Q.2, flagOf_eq_some_hasForm Qset hQ⟩
  · intro hex
    rcases hex with ⟨Q, hmem, hform⟩
    exact ⟨⟨Q, hmem⟩, flagOf_eq_some_of_hasForm Qset hmem hform⟩

/-- Definition 3.1.4: inconsistent times have no defined flag. -/
theorem flagOf_eq_none_of_not_consistent
    (Qset : FlagSet Time) {t : Time}
    (ht : ¬ ConsistentTime t) :
    flagOf Qset t = none := by
  apply flagOf_eq_none_of_no_hasForm
  intro _Q _hmem hform
  exact ht hform.1

/-- Definition 3.1.4: times with equal `flagOf` share the same flag form. -/
theorem flagOf_transfer_hasForm
    (Qset : FlagSet Time)
    {Q : Flag Time} (hmem : Qset.member Q) {t t' : Time}
    (hform : HasForm Q t) (heq : flagOf Qset t = flagOf Qset t') :
    HasForm Q t' := by
  have hsome : flagOf Qset t' = some ⟨Q, hmem⟩ := by
    rw [← heq]
    exact flagOf_eq_some_of_hasForm Qset hmem hform
  exact flagOf_eq_some_hasForm Qset hsome

/-- Lemma 3.1.5(1): flags fix top times — `Q ⊤_p = ⊤_p`. -/
theorem apply_top (Q : Flag Time) (p : Ctrl) :
    Q (top p) = top p := by
  have hqctrl : controller (Q (top p)) = p := by
    calc
      controller (Q (top p)) = controller (top p) :=
        Q.controller_preserving (top p)
      _ = p := top_controller p
  have htop_le_q : attest (top p) (Q (top p)) = Q (top p) :=
    (Q.expansive (top p)).2
  calc
    Q (top p) = attest (top p) (Q (top p)) := htop_le_q.symm
    _ = attest (Q (top p)) (top p) :=
      self_join_comm ((top_controller p).trans hqctrl.symm)
    _ = top p := self_le_top p (Q (top p)) hqctrl

/-- Lemma 3.1.5(1), in `topTime` notation. -/
theorem apply_topTime (Q : Flag Time) (p : Ctrl) :
    Q (topTime p) = topTime p := by
  exact apply_top Q p

/-- Lemma 3.1.5(2): a top time does not have the form `Q⊖` (it is inconsistent). -/
theorem not_hasForm_top (Q : Flag Time) (p : Ctrl) :
    ¬ HasForm Q (top p) := by
  intro hform
  apply hform.1
  rw [top_controller p]

/-- Lemma 3.1.5(2): a top time does not have the form `Q⊖`, in `topTime` notation. -/
theorem not_hasForm_topTime (Q : Flag Time) (p : Ctrl) :
    ¬ HasForm Q (topTime p) := by
  exact not_hasForm_top Q p

/-- Remark 3.1.6: a top time is a flag application `⊤_p = Q ⊤_p`, yet it does not have the
form `Q⊖`. -/
theorem top_eq_apply_top_and_not_hasForm
    (Q : Flag Time) (p : Ctrl) :
    top p = Q (top p) ∧ ¬ HasForm Q (top p) := by
  exact ⟨(apply_top Q p).symm, not_hasForm_top Q p⟩

/-- Remark 3.1.6, in `topTime` notation: a top time is a flag application, yet it does not
have the form `Q⊖`. -/
theorem topTime_eq_apply_topTime_and_not_hasForm
    (Q : Flag Time) (p : Ctrl) :
    topTime p = Q (topTime p) ∧ ¬ HasForm Q (topTime p) := by
  exact ⟨(apply_topTime Q p).symm, not_hasForm_topTime Q p⟩

/-- Lemma 3.1.5(2): `flag(⊤_p)` is undefined. -/
theorem flagOf_top_none
    (Qset : FlagSet Time) (p : Ctrl) :
    flagOf Qset (top p) = none := by
  apply flagOf_eq_none_of_no_hasForm
  intro Q _hmem
  exact not_hasForm_top Q p

/-- Lemma 3.1.5(2), in `topTime` notation. -/
theorem flagOf_topTime_none
    (Qset : FlagSet Time) (p : Ctrl) :
    flagOf Qset (topTime p) = none := by
  exact flagOf_top_none Qset p

/-- Lemma 3.1.7(1): a controller's top time has no flag, so some time lacks a flag. -/
theorem exists_time_flagOf_none_of_controller
    (Qset : FlagSet Time) (p : Ctrl) :
    ∃ t : Time, flagOf Qset t = none := by
  exact ⟨top p, flagOf_top_none Qset p⟩

/-- Lemma 3.1.7(2): the top flag `TopFlag(t) = ⊤_ctrl(t)`, sending every time to its
controller's top time. -/
def topFlag : Flag Time where
  toFun t := top (controller t)
  controller_preserving := by
    intro t
    exact top_controller (controller t)
  expansive := by
    intro t
    constructor
    · exact (top_controller (controller t)).symm
    · exact self_le_top (controller t) t rfl

/-- Lemma 3.1.7(2): no time has the top-flag form. -/
theorem not_hasForm_topFlag (t : Time) :
    ¬ HasForm (topFlag) t := by
  intro hform
  rcases hform.2 with ⟨base, hbase⟩
  apply hform.1
  have hctrl : controller t = controller base := by
    calc
      controller t = controller (topFlag base) := by rw [hbase]
      _ = controller base := (topFlag).controller_preserving base
  calc
    t = topFlag base := hbase
    _ = top (controller base) := rfl
    _ = top (controller t) := by rw [← hctrl]

/-- Lemma 3.1.7(2): the singleton flag-set containing only `topFlag`. -/
def topFlagSet : FlagSet Time where
  member Q := Q = topFlag
  injective_where_consistent := by
    intro Q Q' _t _t' hQ hQ' _hconsistent _heq
    exact hQ.trans hQ'.symm

/-- Lemma 3.1.7(2): it is possible for a flag to exist but no time to have it. -/
theorem exists_flag_no_time_hasForm :
    ∃ Q : Flag Time, (topFlagSet).member Q ∧ ∀ t : Time, ¬ HasForm Q t := by
  exact ⟨topFlag, rfl, not_hasForm_topFlag⟩

/-- Lemma 3.1.7(2): under the singleton top-flag set, no time's `flagOf` is defined. -/
theorem topFlagSet_flagOf_none (t : Time) :
    flagOf (topFlagSet) t = none := by
  apply flagOf_eq_none_of_no_hasForm
  intro Q hmem
  rw [hmem]
  exact not_hasForm_topFlag t

/-- Lemma 3.1.7(2), at the lookup level: the singleton top-flag set contains a flag, but no
time's `flagOf` lookup returns a defined flag. -/
theorem exists_flagSet_member_flagOf_none_for_all_times :
    ∃ Qset : FlagSet Time,
      ∃ Q : Flag Time,
        Qset.member Q ∧ ∀ t : Time, flagOf Qset t = none := by
  exact ⟨topFlagSet, topFlag, rfl, topFlagSet_flagOf_none⟩

end ConsistentHistories.Foundation.Cut.Flags
