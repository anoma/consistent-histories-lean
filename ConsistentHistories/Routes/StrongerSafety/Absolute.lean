import ConsistentHistories.Routes.StrongerSafety.Chains
import ConsistentHistories.Models.Cut.InductiveConstructionLaws

/-!
Paper section 6.4: Absolute consistency results.

-/

namespace ConsistentHistories.Routes.StrongerSafety.Absolute

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Routes.Paths.Circuits
open ConsistentHistories.Foundation.Paths.InitialPrefixes
open ConsistentHistories.Models.Cut.InductiveConstruction
open ConsistentHistories.Routes.StrongerSafety.Chains
open ConsistentHistories.Routes.StrongerSafety.Closure

attribute [instance] LocalStateData.locatedSemilattice

universe u v

/-- Definition 6.4.1, `actIndex(T)`. -/
def ActiveIndexPath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (i : T.Index) : Prop :=
  deriv.Active i

/-- Definition 6.4.1: `actIndex(T)` is exactly the active indexes of `T`. -/
theorem activeIndexPath_iff_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (i : T.Index) :
    ActiveIndexPath deriv i ↔ deriv.Active i := by
  exact Iff.rfl

/-- Definition 6.4.1: an active path index belongs to `actIndex(T)`. -/
theorem active_index_mem_activeIndexPath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (i : T.Index)
    (hactive : deriv.Active i) :
    ActiveIndexPath deriv i := by
  exact hactive

theorem activeIndexPath_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {i : T.Index}
    (h : ActiveIndexPath deriv i) :
    deriv.Active i := by
  exact h

/-- Definition 6.4.1, `actTime(T)`. -/
def ActiveTimePath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (t : Time) : Prop :=
  ∃ i : T.Index, deriv.Active i ∧ T.get i = t

/-- Definition 6.4.1: `actTime(T)` is exactly the times at active indexes of `T`. -/
theorem activeTimePath_iff_exists_active_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (t : Time) :
    ActiveTimePath deriv t ↔
      ∃ i : T.Index, deriv.Active i ∧ T.get i = t := by
  exact Iff.rfl

/-- Definition 6.4.1: an active path index contributes its time to `actTime(T)`. -/
theorem active_index_mem_activeTimePath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (i : T.Index)
    (hactive : deriv.Active i) :
    ActiveTimePath deriv (T.get i) := by
  exact ⟨i, hactive, rfl⟩

theorem activeTimePath_has_active_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {t : Time}
    (h : ActiveTimePath deriv t) :
    ∃ i : T.Index, deriv.Active i ∧ T.get i = t := by
  exact h

/-- Definition 6.4.1, `actCtrl(T)`. -/
def ActiveCtrlPath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (p : Ctrl) : Prop :=
  ∃ t : Time, ActiveTimePath deriv t ∧ controller t = p

/-- Definition 6.4.1: `actCtrl(T)` is exactly the controllers of active indexes. -/
theorem activeCtrlPath_iff_exists_active_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) (p : Ctrl) :
    ActiveCtrlPath deriv p ↔
      ∃ i : T.Index, deriv.Active i ∧ controller (T.get i) = p := by
  constructor
  · intro h
    rcases h with ⟨t, ht, hctrl⟩
    rcases ht with ⟨i, hactive, htime⟩
    exact ⟨i, hactive, by simpa [← htime] using hctrl⟩
  · intro h
    rcases h with ⟨i, hactive, hctrl⟩
    exact ⟨T.get i, ⟨i, hactive, rfl⟩, hctrl⟩

theorem activeTimePath_consistentTime {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {t : Time}
    (h : ActiveTimePath deriv t) :
    ConsistentTime t := by
  rcases h with ⟨i, _hactive, htime⟩
  rw [← htime]
  exact T.consistent i

theorem activeTimePath_controller_mem {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {t : Time}
    (h : ActiveTimePath deriv t) :
    ActiveCtrlPath deriv (controller t) := by
  exact ⟨t, h, rfl⟩

/-- Definition 6.4.1: an active path index contributes its controller to `actCtrl(T)`. -/
theorem active_index_ctrl_mem_activeCtrlPath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (i : T.Index)
    (hactive : deriv.Active i) :
    ActiveCtrlPath deriv (controller (T.get i)) := by
  exact activeTimePath_controller_mem deriv
    (active_index_mem_activeTimePath deriv i hactive)

theorem activeCtrlPath_has_active_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {p : Ctrl}
    (h : ActiveCtrlPath deriv p) :
    ∃ i : T.Index, deriv.Active i ∧ controller (T.get i) = p := by
  exact (activeCtrlPath_iff_exists_active_index deriv p).mp h

theorem activeCtrlPath_has_consistent_activeTime
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {p : Ctrl} (h : ActiveCtrlPath deriv p) :
    ∃ t : Time,
      ActiveTimePath deriv t ∧ controller t = p ∧
        ConsistentTime t := by
  rcases h with ⟨t, ht, hctrl⟩
  exact ⟨t, ht, hctrl, activeTimePath_consistentTime ht⟩

/-- Definition 6.4.1, `actIndex(Π,Π')`. -/
def ActiveIndexCircuit {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) : Prop :=
  cd.Active i

/-- Definition 6.4.1: `actIndex(Π,Π')` is exactly the active circuit indexes. -/
theorem activeIndexCircuit_iff_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index) :
    ActiveIndexCircuit cd i ↔ cd.Active i := by
  exact Iff.rfl

/-- Definition 6.4.1: `actIndex(Π,Π')` is the union of left and right active indexes. -/
theorem activeIndexCircuit_iff_left_or_right_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index) :
    ActiveIndexCircuit cd i ↔
      cd.leftDerivation.Active i ∨ cd.rightDerivation.Active (cd.rightIndex i) := by
  exact Iff.rfl

theorem activeIndexCircuit_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (h : ActiveIndexCircuit cd i) :
    cd.Active i := by
  exact h

theorem activeIndexCircuit_has_left_or_right_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (h : ActiveIndexCircuit cd i) :
    cd.leftDerivation.Active i ∨ cd.rightDerivation.Active (cd.rightIndex i) := by
  exact (activeIndexCircuit_iff_left_or_right_active cd i).mp h

/-- Definition 6.4.1, `actTime(Π,Π')`. -/
def ActiveTimeCircuit {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (t : Time) : Prop :=
  (∃ i : cd.Index, cd.leftDerivation.Active i ∧ cd.leftTime i = t) ∨
    ∃ i : cd.Index, cd.rightDerivation.Active (cd.rightIndex i) ∧ cd.rightTime i = t

/-- Definition 6.4.1, `actCtrl(Π,Π')`. -/
def ActiveCtrlCircuit {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (p : Ctrl) : Prop :=
  ∃ t : Time, ActiveTimeCircuit cd t ∧ controller t = p

/-- Definition 6.4.1: `actTime(Π,Π')` is the union of left and right active times. -/
theorem activeTimeCircuit_iff_left_or_right_activeTimePath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (t : Time) :
    ActiveTimeCircuit cd t ↔
      ActiveTimePath cd.leftDerivation t ∨ ActiveTimePath cd.rightDerivation t := by
  constructor
  · intro h
    cases h with
    | inl hleft =>
        rcases hleft with ⟨i, hactive, htime⟩
        exact Or.inl ⟨i, hactive, htime⟩
    | inr hright =>
        rcases hright with ⟨i, hactive, htime⟩
        exact Or.inr ⟨cd.rightIndex i, hactive, by
          simpa [CircuitDerivation.rightTime] using htime⟩
  · intro h
    cases h with
    | inl hleft =>
        rcases hleft with ⟨i, hactive, htime⟩
        exact Or.inl ⟨i, hactive, htime⟩
    | inr hright =>
        rcases hright with ⟨i, hactive, htime⟩
        let leftI : cd.Index := Fin.cast cd.circuit.length_eq.symm i
        have hrightIndex : cd.rightIndex leftI = i := cd.rightIndex_castLeft i
        exact Or.inr ⟨leftI, by
          simpa [hrightIndex] using hactive, by
          simpa [CircuitDerivation.rightTime, hrightIndex] using htime⟩

theorem activeTimeCircuit_has_left_or_right_activeTimePath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {t : Time}
    (h : ActiveTimeCircuit cd t) :
    ActiveTimePath cd.leftDerivation t ∨ ActiveTimePath cd.rightDerivation t := by
  exact (activeTimeCircuit_iff_left_or_right_activeTimePath cd t).mp h

/-- Definition 6.4.1: `actCtrl(Π,Π')` is the union of left and right active controllers. -/
theorem activeCtrlCircuit_iff_left_or_right_activeCtrlPath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (p : Ctrl) :
    ActiveCtrlCircuit cd p ↔
      ActiveCtrlPath cd.leftDerivation p ∨ ActiveCtrlPath cd.rightDerivation p := by
  constructor
  · intro h
    rcases h with ⟨t, ht, hctrl⟩
    rcases (activeTimeCircuit_iff_left_or_right_activeTimePath cd t).mp ht with
      htleft | htright
    · exact Or.inl ⟨t, htleft, hctrl⟩
    · exact Or.inr ⟨t, htright, hctrl⟩
  · intro h
    rcases h with hleft | hright
    · rcases hleft with ⟨t, ht, hctrl⟩
      exact ⟨t, (activeTimeCircuit_iff_left_or_right_activeTimePath cd t).mpr
        (Or.inl ht), hctrl⟩
    · rcases hright with ⟨t, ht, hctrl⟩
      exact ⟨t, (activeTimeCircuit_iff_left_or_right_activeTimePath cd t).mpr
        (Or.inr ht), hctrl⟩

theorem activeCtrlCircuit_has_left_or_right_activeCtrlPath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {p : Ctrl}
    (h : ActiveCtrlCircuit cd p) :
    ActiveCtrlPath cd.leftDerivation p ∨ ActiveCtrlPath cd.rightDerivation p := by
  exact (activeCtrlCircuit_iff_left_or_right_activeCtrlPath cd p).mp h

/--
Definition 6.4.1: circuit active controllers are exactly controllers appearing at
active left or right circuit indexes.
-/
theorem activeCtrlCircuit_iff_exists_left_or_right_active_index
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (p : Ctrl) :
    ActiveCtrlCircuit cd p ↔
      (∃ i : cd.Index,
        cd.leftDerivation.Active i ∧ controller (cd.leftTime i) = p) ∨
        ∃ i : cd.Index,
          cd.rightDerivation.Active (cd.rightIndex i) ∧
            controller (cd.rightTime i) = p := by
  constructor
  · intro h
    rcases h with ⟨t, htime, hctrl⟩
    cases htime with
    | inl hleft =>
        rcases hleft with ⟨i, hactive, htime⟩
        exact Or.inl ⟨i, hactive, by simpa [← htime] using hctrl⟩
    | inr hright =>
        rcases hright with ⟨i, hactive, htime⟩
        exact Or.inr ⟨i, hactive, by simpa [← htime] using hctrl⟩
  · intro h
    cases h with
    | inl hleft =>
        rcases hleft with ⟨i, hactive, hctrl⟩
        exact ⟨cd.leftTime i, Or.inl ⟨i, hactive, rfl⟩, hctrl⟩
    | inr hright =>
        rcases hright with ⟨i, hactive, hctrl⟩
        exact ⟨cd.rightTime i, Or.inr ⟨i, hactive, rfl⟩, hctrl⟩

theorem activeCtrlCircuit_has_left_or_right_active_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {p : Ctrl}
    (h : ActiveCtrlCircuit cd p) :
    (∃ i : cd.Index,
      cd.leftDerivation.Active i ∧ controller (cd.leftTime i) = p) ∨
      ∃ i : cd.Index,
        cd.rightDerivation.Active (cd.rightIndex i) ∧
          controller (cd.rightTime i) = p := by
  exact (activeCtrlCircuit_iff_exists_left_or_right_active_index cd p).mp h

/-- Definition 6.4.1: left-path activity contributes to `actIndex(Π,Π')`. -/
theorem left_active_index_mem_activeIndexCircuit {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hactive : cd.leftDerivation.Active i) :
    ActiveIndexCircuit cd i := by
  exact cd.active_of_left_active hactive

/-- Definition 6.4.1: right-path activity contributes to `actIndex(Π,Π')`. -/
theorem right_active_index_mem_activeIndexCircuit {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hactive : cd.rightDerivation.Active (cd.rightIndex i)) :
    ActiveIndexCircuit cd i := by
  exact cd.active_of_right_active hactive

theorem left_active_time_mem_activeTimeCircuit {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index)
    (hactive : cd.leftDerivation.Active i) :
    ActiveTimeCircuit cd (cd.leftTime i) := by
  exact Or.inl ⟨i, hactive, rfl⟩

theorem right_active_time_mem_activeTimeCircuit {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index)
    (hactive : cd.rightDerivation.Active (cd.rightIndex i)) :
    ActiveTimeCircuit cd (cd.rightTime i) := by
  exact Or.inr ⟨i, hactive, rfl⟩

theorem activeTimeCircuit_controller_mem {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {t : Time}
    (h : ActiveTimeCircuit cd t) :
    ActiveCtrlCircuit cd (controller t) := by
  exact ⟨t, h, rfl⟩

/-- Definition 6.4.1: an active left circuit entry contributes an active controller. -/
theorem left_active_ctrl_mem_activeCtrlCircuit {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index)
    (hactive : cd.leftDerivation.Active i) :
    ActiveCtrlCircuit cd (controller (cd.leftTime i)) := by
  exact activeTimeCircuit_controller_mem cd
    (left_active_time_mem_activeTimeCircuit cd i hactive)

/-- Definition 6.4.1: an active right circuit entry contributes an active controller. -/
theorem right_active_ctrl_mem_activeCtrlCircuit {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index)
    (hactive : cd.rightDerivation.Active (cd.rightIndex i)) :
    ActiveCtrlCircuit cd (controller (cd.rightTime i)) := by
  exact activeTimeCircuit_controller_mem cd
    (right_active_time_mem_activeTimeCircuit cd i hactive)

/--
Containment (2) in the proof of Theorem 6.4.3, in chain-position form: for the
left-inactive branch, if every non-final node of the left chain of Cuts is
active on the right, then the right-side controller at each chain position lies
in `actCtrl(Π,Π')` (Definition 6.4.1(2)). The final position uses the chain's
left-active endpoint together with the circuit's controller agreement.
-/
theorem left_chain_right_controller_mem_activeCtrlCircuit
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hrightActive :
      ∀ l : Fin chain.edgeCount,
        cd.rightDerivation.Active (cd.rightIndex (chain.current l))) :
    ∀ pos : Fin (chain.edgeCount + 1),
      ActiveCtrlCircuit cd
        (controller (cd.rightTime (chain.node pos))) := by
  intro pos
  by_cases hpos : pos.val < chain.edgeCount
  · let l : Fin chain.edgeCount := ⟨pos.val, hpos⟩
    have hpos_eq : pos = Fin.castSucc l := by
      apply Fin.ext
      rfl
    have hnode : chain.node pos = chain.current l := by
      simp [ChainOfCuts.current, hpos_eq]
    have hactive :
        cd.rightDerivation.Active (cd.rightIndex (chain.node pos)) := by
      simpa [hnode] using hrightActive l
    exact right_active_ctrl_mem_activeCtrlCircuit cd (chain.node pos) hactive
  · have hpos_eq :
        pos = ⟨chain.edgeCount, Nat.lt_succ_self chain.edgeCount⟩ := by
      apply Fin.ext
      have hle : pos.val ≤ chain.edgeCount := Nat.le_of_lt_succ pos.isLt
      exact Nat.le_antisymm hle (Nat.le_of_not_gt hpos)
    have hnode_last : chain.node pos = chain.last := by
      simp [ChainOfCuts.last, hpos_eq]
    have hleftActive : cd.leftDerivation.Active (chain.node pos) := by
      simpa [hnode_last] using chain.last_active'
    have hleftCtrl :
        ActiveCtrlCircuit cd
          (controller (cd.leftTime (chain.node pos))) :=
      left_active_ctrl_mem_activeCtrlCircuit cd (chain.node pos) hleftActive
    have hbefore :
        cd.circuit.left.1.paperIndex (chain.node pos) < cd.circuit.length := by
      calc
        cd.circuit.left.1.paperIndex (chain.node pos) =
            cd.circuit.left.1.paperIndex chain.last := by
              rw [hnode_last]
        _ < cd.circuit.left.1.paperIndex start :=
            chain.last_paperIndex_lt_start
        _ < cd.circuit.length := by
            simpa [Circuit.length] using chain.start_paperIndex_lt_length
    have hctrlEq :
        controller (cd.leftTime (chain.node pos)) =
          controller (cd.rightTime (chain.node pos)) :=
      cd.controller_eq_before_last (chain.node pos) hbefore
    rwa [← hctrlEq]

/--
Containment (2) in the proof of Theorem 6.4.3, symmetric (right-inactive)
branch: if every non-final node of the right chain of Cuts is active on the
left, then the controller at each chain position lies in `actCtrl(Π,Π')`
(Definition 6.4.1(2)). The final position uses the chain's right-active endpoint.
-/
theorem right_chain_left_controller_mem_activeCtrlCircuit
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start)
    (hleftActive :
      ∀ l : Fin chain.edgeCount,
        cd.leftDerivation.Active
          (Fin.cast cd.circuit.length_eq.symm (chain.current l))) :
    ∀ pos : Fin (chain.edgeCount + 1),
      ActiveCtrlCircuit cd
        (controller (cd.circuit.right.1.get (chain.node pos))) := by
  intro pos
  by_cases hpos : pos.val < chain.edgeCount
  · let l : Fin chain.edgeCount := ⟨pos.val, hpos⟩
    have hpos_eq : pos = Fin.castSucc l := by
      apply Fin.ext
      rfl
    have hnode : chain.node pos = chain.current l := by
      simp [ChainOfCuts.current, hpos_eq]
    let leftCurrent : cd.Index :=
      Fin.cast cd.circuit.length_eq.symm (chain.node pos)
    have hleftIndex :
        leftCurrent =
          Fin.cast cd.circuit.length_eq.symm (chain.current l) := by
      simp [leftCurrent, hnode]
    have hleftCtrl :
        ActiveCtrlCircuit cd
          (controller (cd.leftTime leftCurrent)) := by
      have hactive :
          cd.leftDerivation.Active leftCurrent := by
        simpa [hleftIndex] using hleftActive l
      exact left_active_ctrl_mem_activeCtrlCircuit cd leftCurrent hactive
    have hrightIndex : cd.rightIndex leftCurrent = chain.node pos := by
      simpa [leftCurrent] using cd.rightIndex_castLeft (chain.node pos)
    have hbefore :
        cd.circuit.left.1.paperIndex leftCurrent < cd.circuit.length := by
      have hrightBefore := chain.current_paperIndex_lt_length l
      have hpaper :
          cd.circuit.left.1.paperIndex leftCurrent =
            cd.circuit.right.1.paperIndex (chain.current l) := by
        simp [leftCurrent, hnode, Prepath.paperIndex]
      have hlen : cd.circuit.right.1.length = cd.circuit.length := by
        simpa [Circuit.length] using cd.circuit.length_eq.symm
      calc
        cd.circuit.left.1.paperIndex leftCurrent =
            cd.circuit.right.1.paperIndex (chain.current l) := hpaper
        _ < cd.circuit.right.1.length := hrightBefore
        _ = cd.circuit.length := hlen
    have hctrlEq :
        controller (cd.leftTime leftCurrent) =
          controller (cd.circuit.right.1.get (chain.node pos)) := by
      have hcontroller := cd.controller_eq_before_last leftCurrent hbefore
      simpa [CircuitDerivation.rightTime, hrightIndex] using hcontroller
    rwa [← hctrlEq]
  · have hpos_eq :
        pos = ⟨chain.edgeCount, Nat.lt_succ_self chain.edgeCount⟩ := by
      apply Fin.ext
      have hle : pos.val ≤ chain.edgeCount := Nat.le_of_lt_succ pos.isLt
      exact Nat.le_antisymm hle (Nat.le_of_not_gt hpos)
    have hnode_last : chain.node pos = chain.last := by
      simp [ChainOfCuts.last, hpos_eq]
    let leftLast : cd.Index := Fin.cast cd.circuit.length_eq.symm (chain.node pos)
    have hrightIndex : cd.rightIndex leftLast = chain.node pos := by
      simpa [leftLast] using cd.rightIndex_castLeft (chain.node pos)
    have hrightActive :
        cd.rightDerivation.Active (cd.rightIndex leftLast) := by
      simpa [hrightIndex, hnode_last] using chain.last_active'
    have hrightCtrl :
        ActiveCtrlCircuit cd (controller (cd.rightTime leftLast)) :=
      right_active_ctrl_mem_activeCtrlCircuit cd leftLast hrightActive
    simpa [CircuitDerivation.rightTime, hrightIndex] using hrightCtrl

/--
Every active circuit time lies in the active-controller C-closure of the active
times: the `init` rule of the C-closure (Definition 6.2.1(1)) applied to a time
in `actTime(Π,Π')`, whose controller is therefore in `actCtrl(Π,Π')`.
-/
theorem activeTimeCircuit_mem_cClosure {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {t : Time}
    (h : ActiveTimeCircuit cd t) :
    CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd) t := by
  exact CClosure.init h (activeTimeCircuit_controller_mem cd h)

theorem activeTimeCircuit_consistentTime {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {t : Time}
    (h : ActiveTimeCircuit cd t) :
    ConsistentTime t := by
  cases h with
  | inl hleft =>
      rcases hleft with ⟨i, _hactive, htime⟩
      rw [← htime]
      exact cd.circuit.left.1.consistent i
  | inr hright =>
      rcases hright with ⟨i, _hactive, htime⟩
      rw [← htime]
      exact cd.circuit.right.1.consistent (cd.rightIndex i)

theorem activeCtrlCircuit_has_consistent_activeTime
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {cd : CircuitDerivation Time}
    {p : Ctrl} (h : ActiveCtrlCircuit cd p) :
    ∃ t : Time,
      ActiveTimeCircuit cd t ∧ controller t = p ∧
        ConsistentTime t := by
  rcases h with ⟨t, ht, hctrl⟩
  exact ⟨t, ht, hctrl, activeTimeCircuit_consistentTime cd ht⟩

/-- Definition 6.4.2, inconsistent set of times. -/
def TimesInconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (times : Time → Prop) : Prop :=
  ∃ t t' : Time, times t ∧ times t' ∧ Contradicts t t'

/-- Definition 6.4.2, consistent set of times. -/
def TimesConsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (times : Time → Prop) : Prop :=
  ¬ TimesInconsistent times

/-- Definition 6.4.2: inconsistent time sets are exactly sets with contradictory member witnesses. -/
theorem timesInconsistent_iff_exists_contradicts
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (times : Time → Prop) :
    TimesInconsistent times ↔
      ∃ t t' : Time, times t ∧ times t' ∧ Contradicts t t' := by
  exact Iff.rfl

/-- Definition 6.4.2: contradictory members make a time set inconsistent. -/
theorem timesInconsistent_of_contradicts
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times : Time → Prop}
    {t t' : Time} (ht : times t) (ht' : times t') (hcontr : Contradicts t t') :
    TimesInconsistent times := by
  exact ⟨t, t', ht, ht', hcontr⟩

/-- Definition 6.4.2: an inconsistent time set has contradictory member witnesses. -/
theorem timesInconsistent_has_witnesses
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times : Time → Prop}
    (hinconsistent : TimesInconsistent times) :
    ∃ t t' : Time, times t ∧ times t' ∧ Contradicts t t' := by
  exact hinconsistent

/-- Definition 6.4.2: consistency excludes contradictory pairs in the time set. -/
theorem timesConsistent_not_contradicts
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times : Time → Prop}
    (hconsistent : TimesConsistent times) {t t' : Time}
    (ht : times t) (ht' : times t') :
    ¬ Contradicts t t' := by
  intro hcontr
  exact hconsistent (timesInconsistent_of_contradicts ht ht' hcontr)

/--
Definition 6.4.2 note: contradiction witnesses for an inconsistent set have the
same controller.
-/
theorem timesInconsistent_witnesses_controller_eq
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times : Time → Prop}
    (hinconsistent : TimesInconsistent times) :
    ∃ t t' : Time,
      times t ∧ times t' ∧ Contradicts t t' ∧
        controller t = controller t' := by
  rcases hinconsistent with ⟨t, t', ht, ht', hcontr⟩
  exact ⟨t, t', ht, ht', hcontr, hcontr.1⟩

/--
Definition 6.4.2 note: if a set of times is consistent, then each member is
strictly below its controller top time.
-/
theorem timesConsistent_member_not_top
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times : Time → Prop}
    (hconsistent : TimesConsistent times) {t : Time} (ht : times t) :
    t ≠ top (controller t) := by
  intro htop
  have hcontr : Contradicts t t := by
    exact ⟨rfl, (self_join_idem t).trans htop⟩
  exact hconsistent ⟨t, t, ht, ht, hcontr⟩

/-- Definition 6.4.2 note, strict-order form. -/
theorem timesConsistent_member_lt_topTime
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times : Time → Prop}
    (hconsistent : TimesConsistent times) {t : Time} (ht : times t) :
    lt t (topTime (controller t)) := by
  exact
    ⟨le_topTime rfl, by
      simpa [LocatedSemilattice.topTime] using
        timesConsistent_member_not_top hconsistent ht⟩

/--
Proof-local times `t_r` attached to the positions of a chain of cuts in the
proof of Theorem 6.4.3.

The paper's reverse induction is over the time at each chain index immediately
before that index is cut, not necessarily over the final path time at that
index.
-/
structure ChainCutTimes {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) where
  time : Fin (chain.edgeCount + 1) → Time
  last_eq :
    time ⟨chain.edgeCount, Nat.lt_succ_self chain.edgeCount⟩ = T.get chain.last
  controller_eq :
    ∀ pos : Fin (chain.edgeCount + 1),
      controller (time pos) =
        controller (T.get (chain.node pos))
  edge_attest_le :
    ∀ l : Fin chain.edgeCount,
      ∃ source : Time,
        (source # (time (Fin.castSucc l))) ≼ (time ⟨l.val + 1, Nat.succ_lt_succ l.isLt⟩)

/-- Final path times instantiate `ChainCutTimes` under final-time edge bounds. -/
def ChainCutTimes.ofFinalEdgeBounds
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start)
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          le
            (source # (T.get (chain.current l)))
            (T.get (chain.next l))) :
    ChainCutTimes chain :=
  { time := fun pos => T.get (chain.node pos)
    last_eq := rfl
    controller_eq := by
      intro _pos
      rfl
    edge_attest_le := by
      intro l
      simpa [ChainOfCuts.current, ChainOfCuts.next] using hattest_le l }

/--
Proof-local constructor for the chain times from the pre-Cut
center of each chain-edge Cut. The remaining nontrivial glue is explicit: each
edge's post-Cut prefix must precede the next edge's pre-Cut base.
-/
def ChainCutTimes.ofEdgePrefixData
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start)
    (edgeData :
      ∀ l : Fin chain.edgeCount,
        Σ upper : T.Index,
          CutPrefixData deriv (T.paperIndex upper) (T.paperIndex (chain.current l))
            (T.paperIndex (chain.next l)))
    (hadjacent :
      ∀ (l : Fin chain.edgeCount) (hnext : l.val + 1 < chain.edgeCount),
        let data := (edgeData l).2
        let nextData := (edgeData ⟨l.val + 1, hnext⟩).2
        InitialPrefix
          (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj
            data.hi data.hconsistent)
          nextData.baseDeriv) :
    ChainCutTimes chain := by
  let edgeTime : Fin chain.edgeCount → Time :=
    fun l => (edgeData l).2.base.get (edgeData l).2.idxJ
  let chainTime : Fin (chain.edgeCount + 1) → Time :=
    fun pos =>
      if h : pos.val < chain.edgeCount then
        edgeTime ⟨pos.val, h⟩
      else
        T.get chain.last
  refine
    { time := chainTime
      last_eq := ?_
      controller_eq := ?_
      edge_attest_le := ?_ }
  · dsimp [chainTime]
    simp
  · intro pos
    by_cases hpos : pos.val < chain.edgeCount
    · let l : Fin chain.edgeCount := ⟨pos.val, hpos⟩
      have hcast : (Fin.castSucc l : Fin (chain.edgeCount + 1)) = pos := by
        apply Fin.ext
        rfl
      have hctrl :
          controller ((edgeData l).2.base.get (edgeData l).2.idxJ) =
            controller (T.get (chain.current l)) :=
        (edgeData l).2.base_center_controller_eq_final_center rfl
      dsimp [chainTime, edgeTime]
      rw [dif_pos hpos]
      simpa [l, ChainOfCuts.current, hcast] using hctrl
    · have hle : pos.val ≤ chain.edgeCount := Nat.le_of_lt_succ pos.isLt
      have hval : pos.val = chain.edgeCount := by omega
      have hpos_eq :
          pos = ⟨chain.edgeCount, Nat.lt_succ_self chain.edgeCount⟩ := by
        apply Fin.ext
        exact hval
      dsimp [chainTime]
      rw [dif_neg hpos]
      simp [hpos_eq, ChainOfCuts.last]
  · intro l
    let data := (edgeData l).2
    by_cases hnext : l.val + 1 < chain.edgeCount
    · let nextL : Fin chain.edgeCount := ⟨l.val + 1, hnext⟩
      let nextData := (edgeData nextL).2
      have hcurrent_next : chain.current nextL = chain.next l := by
        rfl
      have hlower :
          T.paperIndex (chain.next l) = nextData.base.paperIndex nextData.idxJ := by
        simpa [nextL, nextData, hcurrent_next] using nextData.cutJ_eq
      rcases
          data.attest_lower_bound_to_prefix_base_center
            (hadjacent l hnext) (center := chain.current l)
            (lower := nextData.idxJ) rfl hlower with
        ⟨source, hle, _hctrl⟩
      refine ⟨source, ?_⟩
      simpa [chainTime, edgeTime, data, nextData, nextL, hnext, l.isLt] using hle
    · have hnext_eq_edgeCount : l.val + 1 = chain.edgeCount := by omega
      have hnext_last : chain.next l = chain.last := by
        have hpos_eq :
            (⟨l.val + 1, Nat.succ_lt_succ l.isLt⟩ :
              Fin (chain.edgeCount + 1)) =
              ⟨chain.edgeCount, Nat.lt_succ_self chain.edgeCount⟩ := by
          apply Fin.ext
          exact hnext_eq_edgeCount
        simp [ChainOfCuts.next, ChainOfCuts.last, hpos_eq]
      rcases
          data.attest_lower_bound_to_prefix_base_center data.hprefix
            (center := chain.current l) (lower := chain.next l) rfl rfl with
        ⟨source, hle, _hctrl⟩
      refine ⟨source, ?_⟩
      simpa [chainTime, edgeTime, data, hnext, l.isLt, hnext_last] using hle

/--
Proof-local ordering lemma for the chain times: if one
prefix-packaged Cut has lower endpoint equal to the next prefix-packaged Cut's
center, then the first post-Cut derivation is an initial prefix of the second
pre-Cut base.
-/
theorem cutPrefixData_postCut_initialPrefix_next_base_of_adjacent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {firstK firstJ shared secondK secondI : Nat}
    (firstData : CutPrefixData deriv firstK firstJ shared)
    (secondData : CutPrefixData deriv secondK shared secondI) :
    InitialPrefix
      (Derivation.cut firstData.baseDeriv firstData.hij firstData.hjk
        firstData.hk firstData.hj firstData.hi firstData.hconsistent)
      secondData.baseDeriv := by
  let firstCut :=
    Derivation.cut firstData.baseDeriv firstData.hij firstData.hjk
      firstData.hk firstData.hj firstData.hi firstData.hconsistent
  let center : T.Index := Fin.cast firstData.hprefix.length_eq firstData.idxI
  have hfirstPrefix : InitialPrefix firstCut deriv := by
    simpa [firstCut] using firstData.hprefix
  have hcenter : shared = T.paperIndex center := by
    simpa [center, Prepath.paperIndex] using firstData.cutI_eq
  have hactiveLower : firstCut.Active firstData.idxI := by
    simpa [firstCut] using
      ConsistentHistories.Routes.PathProperties.InactiveCuts.cutPrefixData_final_cut_lower_active
        firstData
  have hidx :
      Fin.cast hfirstPrefix.length_eq.symm center = firstData.idxI := by
    apply Fin.ext
    rfl
  have hactive :
      firstCut.Active (Fin.cast hfirstPrefix.length_eq.symm center) := by
    simpa [hidx] using hactiveLower
  exact
    ConsistentHistories.Routes.PathProperties.InactiveCuts.cutPrefixData_active_prefix_before_base
      secondData hfirstPrefix (center := center) hcenter hactive

/--
Proof-local constructor for the chain times from the
Cut-prefix data already exposed by each chain link. Consecutive link
Cut-prefixes are ordered by the active lower-endpoint/greatest-active-prefix
argument used in the paper's chain proof.
-/
noncomputable def ChainCutTimes.ofChainLinks
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) :
    ChainCutTimes chain := by
  exact
    ChainCutTimes.ofEdgePrefixData chain
      (fun l => Classical.choice (chain.link_cutPrefixData l))
      (by
        intro l hnext
        exact
          cutPrefixData_postCut_initialPrefix_next_base_of_adjacent
            (Classical.choice (chain.link_cutPrefixData l)).2
            (Classical.choice
              (chain.link_cutPrefixData ⟨l.val + 1, hnext⟩)).2)

/--
First pre-Cut contradiction bridge for the left-inactive branch of the proof of
Theorem 6.4.3: the inconsistent-index witness prefix lies before the first
chain-link pre-Cut base at the active center, so its contradiction (the `t₁ 🗲 t'`
of the proof) persists to the canonical proof-local first chain time.
-/
theorem left_first_chain_link_time_contradicts_right_of_activeInconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (chain : ChainOfCuts cd.leftDerivation i) :
    ((ChainCutTimes.ofChainLinks chain).time
        ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime i) := by
  rcases hactiveInconsistent with ⟨_hactive, hinconsistent⟩
  rcases hinconsistent with ⟨pref, hprefix, hactivePref, hcontrPref⟩
  let firstLink : Fin chain.edgeCount := ⟨0, chain.edgeCount_pos⟩
  let firstData :=
    (Classical.choice (chain.link_cutPrefixData firstLink)).2
  have hcurrent_first : chain.current firstLink = i := by
    simpa [ChainOfCuts.current, ChainOfCuts.first, firstLink] using
      chain.first_eq_start
  have hidxJ_val : firstData.idxJ.val = (chain.current firstLink).val := by
    apply Nat.succ.inj
    have hpaper :
        firstData.base.paperIndex firstData.idxJ =
          cd.circuit.left.1.paperIndex (chain.current firstLink) := by
      exact firstData.cutJ_eq.symm
    simpa [Prepath.paperIndex] using hpaper
  have hprefixBeforeBase :
      InitialPrefix pref.leftDerivation firstData.baseDeriv := by
    have hcenter :
        cd.circuit.left.1.paperIndex (chain.current firstLink) =
          cd.circuit.left.1.paperIndex i := by
      simp [hcurrent_first]
    have hactiveLeft :
        pref.leftDerivation.Active (Fin.cast hprefix.1.length_eq.symm i) := by
      simpa [CircuitDerivation.prefixIndex] using hactivePref.1
    exact
      ConsistentHistories.Routes.PathProperties.InactiveCuts.cutPrefixData_active_prefix_before_base
        firstData hprefix.1 (center := i) hcenter hactiveLeft
  have hfirst_idx :
      Fin.cast hprefixBeforeBase.length_eq (pref.prefixIndex hprefix i) =
        firstData.idxJ := by
    apply Fin.ext
    calc
      (Fin.cast hprefixBeforeBase.length_eq
          (pref.prefixIndex hprefix i)).val =
          (pref.prefixIndex hprefix i).val := rfl
      _ = i.val := by rfl
      _ = (chain.current firstLink).val := by rw [hcurrent_first]
      _ = firstData.idxJ.val := hidxJ_val.symm
  have hleft_le_base :
      (pref.leftTime (pref.prefixIndex hprefix i)) ≼ (firstData.base.get firstData.idxJ) := by
    have hraw :=
      InitialPrefix.derivation_times_increase hprefixBeforeBase
        (pref.prefixIndex hprefix i)
    simpa [CircuitDerivation.leftTime, Derivation.get, hfirst_idx] using hraw
  have hright_le_final :
      (pref.rightTime (pref.prefixIndex hprefix i)) ≼ (cd.rightTime i) :=
    CircuitDerivation.rightTime_increases_from_prefix hprefix i
  have hcontrBase :
      (firstData.base.get firstData.idxJ) 🗲 (cd.rightTime i) :=
    contradicts_of_le_both hleft_le_base hright_le_final hcontrPref
  have hzero_lt : (0 : Nat) < chain.edgeCount := chain.edgeCount_pos
  simpa [ChainCutTimes.ofChainLinks, ChainCutTimes.ofEdgePrefixData, firstLink,
    firstData, hzero_lt] using hcontrBase

/--
First pre-Cut contradiction bridge for the right-inactive branch of the proof of
Theorem 6.4.3, obtained by applying the left bridge to the swapped circuit
derivation.
-/
theorem right_first_chain_link_time_contradicts_left_of_activeInconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (chain : ChainOfCuts cd.rightDerivation (cd.rightIndex i)) :
    (cd.leftTime i) 🗲 ((ChainCutTimes.ofChainLinks chain).time
        ⟨0, Nat.succ_pos chain.edgeCount⟩) := by
  have hswap :
      ((ChainCutTimes.ofChainLinks chain).time
          ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.swap.rightTime (cd.rightIndex i)) :=
    left_first_chain_link_time_contradicts_right_of_activeInconsistent
      cd.swap (cd.swap_activeInconsistentIndex hactiveInconsistent) chain
  have hcast : Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i) = i := by
    ext
    rfl
  exact contradicts_symm (by
    simpa [CircuitDerivation.swap_rightTime, hcast] using hswap)

/-!
The bridge theorems above discharge the first pre-Cut contradiction obligation
of the proof of Theorem 6.4.3 (the contradiction `t₁ 🗲 t'` at the chain start),
which the chain-link constructions below feed into the C-closure induction.
-/

/--
A left-chain edge Cut prefix supplies a lower bound into the final next-node
time. Upgrading this to the paper's pre-Cut next time still requires explicit
prefix-order evidence between consecutive Cut prefixes.
-/
theorem left_chain_edge_final_next_attest_lower_bound
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start) (l : Fin chain.edgeCount)
    {cutUpper : cd.circuit.left.1.Index}
    (hprefix :
      CutPrefixWitness cd.leftDerivation
        (cd.circuit.left.1.paperIndex cutUpper)
        (cd.circuit.left.1.paperIndex (chain.current l))
        (cd.circuit.left.1.paperIndex (chain.next l))) :
    ∃ source centerTime : Time,
      (source # centerTime) ≼ (cd.leftTime (chain.next l)) ∧
        controller centerTime =
          controller (cd.leftTime (chain.current l)) := by
  exact hprefix.attest_lower_bound rfl rfl

/--
A right-chain edge Cut prefix supplies a lower bound into the final next-node
time. Upgrading this to the paper's pre-Cut next time still requires explicit
prefix-order evidence between consecutive Cut prefixes.
-/
theorem right_chain_edge_final_next_attest_lower_bound
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start) (l : Fin chain.edgeCount)
    {cutUpper : cd.circuit.right.1.Index}
    (hprefix :
      CutPrefixWitness cd.rightDerivation
        (cd.circuit.right.1.paperIndex cutUpper)
        (cd.circuit.right.1.paperIndex (chain.current l))
        (cd.circuit.right.1.paperIndex (chain.next l))) :
    ∃ source centerTime : Time,
      (source # centerTime) ≼ (cd.circuit.right.1.get (chain.next l)) ∧
        controller centerTime =
          controller (cd.circuit.right.1.get (chain.current l)) := by
  exact hprefix.attest_lower_bound rfl rfl

/--
A left-chain edge Cut prefix supplies a lower bound into an explicitly later
prefix endpoint. This is the proof-local version needed for the paper's
pre-Cut chain times; the caller supplies the prefix-order evidence.
-/
theorem left_chain_edge_prefix_next_attest_lower_bound
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start) (l : Fin chain.edgeCount)
    {cutUpper : cd.circuit.left.1.Index}
    (data :
      CutPrefixData cd.leftDerivation
        (cd.circuit.left.1.paperIndex cutUpper)
        (cd.circuit.left.1.paperIndex (chain.current l))
        (cd.circuit.left.1.paperIndex (chain.next l)))
    {U : Prepath Time} {laterDeriv : Derivation Time U}
    (hlater :
      InitialPrefix
        (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
          data.hconsistent)
        laterDeriv)
    {laterLower : U.Index}
    (hlower : cd.circuit.left.1.paperIndex (chain.next l) = U.paperIndex laterLower) :
    ∃ source centerTime : Time,
      (source # centerTime) ≼ (U.get laterLower) ∧
      controller centerTime =
          controller (cd.leftTime (chain.current l)) := by
  exact data.attest_lower_bound_to_prefix hlater rfl hlower

/--
Left-chain edge lower bound in the form used to build the pre-Cut chain times,
exposing the pre-Cut center time `data.base.get data.idxJ` named in the proof of
Theorem 6.4.3 instead of an anonymous center witness.
-/
theorem left_chain_edge_prefix_next_attest_lower_bound_base_center
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start) (l : Fin chain.edgeCount)
    {cutUpper : cd.circuit.left.1.Index}
    (data :
      CutPrefixData cd.leftDerivation
        (cd.circuit.left.1.paperIndex cutUpper)
        (cd.circuit.left.1.paperIndex (chain.current l))
        (cd.circuit.left.1.paperIndex (chain.next l)))
    {U : Prepath Time} {laterDeriv : Derivation Time U}
    (hlater :
      InitialPrefix
        (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
          data.hconsistent)
        laterDeriv)
    {laterLower : U.Index}
    (hlower : cd.circuit.left.1.paperIndex (chain.next l) = U.paperIndex laterLower) :
    ∃ source : Time,
      (source # (data.base.get data.idxJ)) ≼ (U.get laterLower) ∧
        controller (data.base.get data.idxJ) =
          controller (cd.leftTime (chain.current l)) := by
  exact data.attest_lower_bound_to_prefix_base_center hlater rfl hlower

/--
Left-chain controller equality used to build the pre-Cut chain times: the
pre-Cut center time has the same controller as the final chain entry.
-/
theorem left_chain_edge_base_center_controller_eq
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start) (l : Fin chain.edgeCount)
    {cutUpper : cd.circuit.left.1.Index}
    (data :
      CutPrefixData cd.leftDerivation
        (cd.circuit.left.1.paperIndex cutUpper)
        (cd.circuit.left.1.paperIndex (chain.current l))
        (cd.circuit.left.1.paperIndex (chain.next l))) :
    controller (data.base.get data.idxJ) =
      controller (cd.leftTime (chain.current l)) := by
  exact data.base_center_controller_eq_final_center rfl

/--
A right-chain edge Cut prefix supplies a lower bound into an explicitly later
prefix endpoint. This is the proof-local version needed for the paper's
pre-Cut chain times; the caller supplies the prefix-order evidence.
-/
theorem right_chain_edge_prefix_next_attest_lower_bound
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start) (l : Fin chain.edgeCount)
    {cutUpper : cd.circuit.right.1.Index}
    (data :
      CutPrefixData cd.rightDerivation
        (cd.circuit.right.1.paperIndex cutUpper)
        (cd.circuit.right.1.paperIndex (chain.current l))
        (cd.circuit.right.1.paperIndex (chain.next l)))
    {U : Prepath Time} {laterDeriv : Derivation Time U}
    (hlater :
      InitialPrefix
        (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
          data.hconsistent)
        laterDeriv)
    {laterLower : U.Index}
    (hlower : cd.circuit.right.1.paperIndex (chain.next l) = U.paperIndex laterLower) :
    ∃ source centerTime : Time,
      (source # centerTime) ≼ (U.get laterLower) ∧
      controller centerTime =
          controller (cd.circuit.right.1.get (chain.current l)) := by
  exact data.attest_lower_bound_to_prefix hlater rfl hlower

/--
Right-chain edge lower bound in the form used to build the pre-Cut chain times,
exposing the pre-Cut center time `data.base.get data.idxJ` named in the proof of
Theorem 6.4.3 instead of an anonymous center witness.
-/
theorem right_chain_edge_prefix_next_attest_lower_bound_base_center
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start) (l : Fin chain.edgeCount)
    {cutUpper : cd.circuit.right.1.Index}
    (data :
      CutPrefixData cd.rightDerivation
        (cd.circuit.right.1.paperIndex cutUpper)
        (cd.circuit.right.1.paperIndex (chain.current l))
        (cd.circuit.right.1.paperIndex (chain.next l)))
    {U : Prepath Time} {laterDeriv : Derivation Time U}
    (hlater :
      InitialPrefix
        (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
          data.hconsistent)
        laterDeriv)
    {laterLower : U.Index}
    (hlower : cd.circuit.right.1.paperIndex (chain.next l) = U.paperIndex laterLower) :
    ∃ source : Time,
      (source # (data.base.get data.idxJ)) ≼ (U.get laterLower) ∧
        controller (data.base.get data.idxJ) =
          controller (cd.circuit.right.1.get (chain.current l)) := by
  exact data.attest_lower_bound_to_prefix_base_center hlater rfl hlower

/--
Right-chain controller equality used to build the pre-Cut chain times: the
pre-Cut center time has the same controller as the final chain entry.
-/
theorem right_chain_edge_base_center_controller_eq
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start) (l : Fin chain.edgeCount)
    {cutUpper : cd.circuit.right.1.Index}
    (data :
      CutPrefixData cd.rightDerivation
        (cd.circuit.right.1.paperIndex cutUpper)
        (cd.circuit.right.1.paperIndex (chain.current l))
        (cd.circuit.right.1.paperIndex (chain.next l))) :
    controller (data.base.get data.idxJ) =
      controller (cd.circuit.right.1.get (chain.current l)) := by
  exact data.base_center_controller_eq_final_center rfl

/--
Base case for the left-inactive one-sided branch: the final
active node of a left chain of cuts contributes its time to the active
controller C-closure.
-/
theorem left_chain_last_time_mem_cClosure {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start) :
    CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (cd.leftTime chain.last) := by
  have htime : ActiveTimeCircuit cd (cd.leftTime chain.last) :=
    left_active_time_mem_activeTimeCircuit cd chain.last chain.last_active'
  exact activeTimeCircuit_mem_cClosure cd htime

/--
Base case for the right-inactive one-sided branch: the final
active node of a right chain of cuts contributes its time to the active
controller C-closure.
-/
theorem right_chain_last_time_mem_cClosure {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start) :
    CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (cd.circuit.right.1.get chain.last) := by
  let leftLast : cd.Index := Fin.cast cd.circuit.length_eq.symm chain.last
  have hrightIndex : cd.rightIndex leftLast = chain.last :=
    cd.rightIndex_castLeft chain.last
  have htime : ActiveTimeCircuit cd (cd.circuit.right.1.get chain.last) := by
    have hrightActive : cd.rightDerivation.Active (cd.rightIndex leftLast) := by
      simpa [hrightIndex] using chain.last_active'
    have hmem := right_active_time_mem_activeTimeCircuit cd leftLast hrightActive
    simpa [CircuitDerivation.rightTime, hrightIndex] using hmem
  exact activeTimeCircuit_mem_cClosure cd htime

/--
For a left chain, if a non-final node is active on the right side, then the
controller of the corresponding left time is an active controller of the
circuit.
-/
theorem left_chain_current_controller_mem_of_right_active
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start) (l : Fin chain.edgeCount)
    (hrightActive : cd.rightDerivation.Active (cd.rightIndex (chain.current l))) :
    ActiveCtrlCircuit cd (controller (cd.leftTime (chain.current l))) := by
  have hrightTime : ActiveTimeCircuit cd (cd.rightTime (chain.current l)) :=
    right_active_time_mem_activeTimeCircuit cd (chain.current l) hrightActive
  have hrightCtrl : ActiveCtrlCircuit cd
      (controller (cd.rightTime (chain.current l))) :=
    activeTimeCircuit_controller_mem cd hrightTime
  have hctrlEq :
      controller (cd.leftTime (chain.current l)) =
        controller (cd.rightTime (chain.current l)) :=
    cd.controller_eq_before_last (chain.current l) (chain.current_paperIndex_lt_length l)
  rwa [hctrlEq]

/--
For a right chain, if a non-final node is active on the left side, then the
controller of the corresponding right time is an active controller of the
circuit.
-/
theorem right_chain_current_controller_mem_of_left_active
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start) (l : Fin chain.edgeCount)
    (hleftActive :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm (chain.current l))) :
    ActiveCtrlCircuit cd
      (controller (cd.circuit.right.1.get (chain.current l))) := by
  let leftCurrent : cd.Index := Fin.cast cd.circuit.length_eq.symm (chain.current l)
  have hrightIndex : cd.rightIndex leftCurrent = chain.current l :=
    cd.rightIndex_castLeft (chain.current l)
  have hleftTime : ActiveTimeCircuit cd (cd.leftTime leftCurrent) :=
    left_active_time_mem_activeTimeCircuit cd leftCurrent hleftActive
  have hleftCtrl : ActiveCtrlCircuit cd (controller (cd.leftTime leftCurrent)) :=
    activeTimeCircuit_controller_mem cd hleftTime
  have hctrlEq :
      controller (cd.leftTime leftCurrent) =
        controller (cd.circuit.right.1.get (chain.current l)) := by
    have hbefore : cd.circuit.left.1.paperIndex leftCurrent < cd.circuit.length := by
      have hrightBefore := chain.current_paperIndex_lt_length l
      have hpaper :
          cd.circuit.left.1.paperIndex leftCurrent =
            cd.circuit.right.1.paperIndex (chain.current l) := by
        simp [leftCurrent, Prepath.paperIndex]
      have hlen : cd.circuit.right.1.length = cd.circuit.length := by
        simpa [Circuit.length] using cd.circuit.length_eq.symm
      calc
        cd.circuit.left.1.paperIndex leftCurrent =
            cd.circuit.right.1.paperIndex (chain.current l) := hpaper
        _ < cd.circuit.right.1.length := hrightBefore
        _ = cd.circuit.length := hlen
    have hcontroller := cd.controller_eq_before_last leftCurrent hbefore
    simpa [CircuitDerivation.rightTime, hrightIndex] using hcontroller
  rwa [← hctrlEq]

/--
Left-chain induction step: if the next chain time is closed,
and a Cut-shape attestation to the current time lies below it, then the current
time is closed once its controller is active via the right side.
-/
theorem left_chain_step_current_mem_cClosure
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start) (l : Fin chain.edgeCount)
    {source : Time}
    (hattest_le :
      (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hnextClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.leftTime (chain.next l)))
    (hrightActive : cd.rightDerivation.Active (cd.rightIndex (chain.current l))) :
    CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (cd.leftTime (chain.current l)) := by
  have hctrl :
      ActiveCtrlCircuit cd (controller (cd.leftTime (chain.current l))) :=
    left_chain_current_controller_mem_of_right_active cd chain l hrightActive
  exact CClosure.right_of_attest_le hattest_le hnextClosed hctrl

/--
The final start time of a left chain lies in the active-controller C-closure
only after every final-time edge supplies an attestation lower bound and the
matching right index is active.
-/
theorem left_chain_start_time_mem_cClosure_of_steps
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightActive :
      ∀ l : Fin chain.edgeCount,
        cd.rightDerivation.Active (cd.rightIndex (chain.current l))) :
    CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (cd.leftTime start) := by
  have hfirst :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.leftTime chain.first) := by
    exact chain.reverse_induction
      (P := fun i =>
        CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
          (cd.leftTime i))
      (left_chain_last_time_mem_cClosure cd chain)
      (by
        intro l hnextClosed
        rcases hattest_le l with ⟨_source, hle⟩
        exact left_chain_step_current_mem_cClosure cd chain l hle hnextClosed
          (hrightActive l))
  simpa [chain.first_eq_start] using hfirst

/--
Right-chain induction step: if the next right-chain time is
closed, and a Cut-shape attestation to the current right time lies below it,
then the current right time is closed once its controller is active via the left
side.
-/
theorem right_chain_step_current_mem_cClosure
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start) (l : Fin chain.edgeCount)
    {source : Time}
    (hattest_le :
      (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l)))
    (hnextClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.circuit.right.1.get (chain.next l)))
    (hleftActive :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm (chain.current l))) :
    CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (cd.circuit.right.1.get (chain.current l)) := by
  have hctrl :
      ActiveCtrlCircuit cd
        (controller (cd.circuit.right.1.get (chain.current l))) :=
    right_chain_current_controller_mem_of_left_active cd chain l hleftActive
  exact CClosure.right_of_attest_le hattest_le hnextClosed hctrl

/--
The final start time of a right chain lies in the active-controller C-closure
only after every final-time edge supplies an attestation lower bound and the
matching left index is active.
-/
theorem right_chain_start_time_mem_cClosure_of_steps
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start)
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l)))
    (hleftActive :
      ∀ l : Fin chain.edgeCount,
        cd.leftDerivation.Active
          (Fin.cast cd.circuit.length_eq.symm (chain.current l))) :
    CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (cd.circuit.right.1.get start) := by
  have hfirst :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.circuit.right.1.get chain.first) := by
    exact chain.reverse_induction
      (P := fun i =>
        CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
          (cd.circuit.right.1.get i))
      (right_chain_last_time_mem_cClosure cd chain)
      (by
        intro l hnextClosed
        rcases hattest_le l with ⟨_source, hle⟩
        exact right_chain_step_current_mem_cClosure cd chain l hle hnextClosed
          (hleftActive l))
  simpa [chain.first_eq_start] using hfirst

/--
Proof-local left-chain induction component over the
pre-Cut times `t_r` described in the paper proof. The opposite-side activity is
an explicit hypothesis.
-/
theorem left_chain_start_cutTime_mem_cClosure
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (cutTimes : ChainCutTimes chain)
    (hrightActive :
      ∀ l : Fin chain.edgeCount,
        cd.rightDerivation.Active (cd.rightIndex (chain.current l))) :
    CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) := by
  exact chain.reverse_induction_positions
    (P := fun pos =>
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cutTimes.time pos))
    (by
      have hlast := left_chain_last_time_mem_cClosure cd chain
      simpa [cutTimes.last_eq] using hlast)
    (by
      intro l hnextClosed
      rcases cutTimes.edge_attest_le l with ⟨_source, hle⟩
      have hctrlFinal :
          ActiveCtrlCircuit cd
            (controller (cd.leftTime (chain.current l))) :=
        left_chain_current_controller_mem_of_right_active cd chain l
          (hrightActive l)
      have hctrl :
          ActiveCtrlCircuit cd
            (controller (cutTimes.time (Fin.castSucc l))) := by
        rw [cutTimes.controller_eq (Fin.castSucc l)]
        simpa [ChainOfCuts.current, CircuitDerivation.leftTime] using hctrlFinal
      exact CClosure.right_of_attest_le hle hnextClosed hctrl)

/--
Proof-local right-chain induction component over the
pre-Cut times `t_r` described in the paper proof. The opposite-side activity is
an explicit hypothesis.
-/
theorem right_chain_start_cutTime_mem_cClosure
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start)
    (cutTimes : ChainCutTimes chain)
    (hleftActive :
      ∀ l : Fin chain.edgeCount,
        cd.leftDerivation.Active
          (Fin.cast cd.circuit.length_eq.symm (chain.current l))) :
    CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) := by
  exact chain.reverse_induction_positions
    (P := fun pos =>
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cutTimes.time pos))
    (by
      have hlast := right_chain_last_time_mem_cClosure cd chain
      simpa [cutTimes.last_eq] using hlast)
    (by
      intro l hnextClosed
      rcases cutTimes.edge_attest_le l with ⟨_source, hle⟩
      have hctrlFinal :
          ActiveCtrlCircuit cd
            (controller
              (cd.circuit.right.1.get (chain.current l))) :=
        right_chain_current_controller_mem_of_left_active cd chain l
          (hleftActive l)
      have hctrl :
          ActiveCtrlCircuit cd
            (controller (cutTimes.time (Fin.castSucc l))) := by
        rw [cutTimes.controller_eq (Fin.castSucc l)]
        simpa [ChainOfCuts.current] using hctrlFinal
      exact CClosure.right_of_attest_le hle hnextClosed hctrl)

/--
Closure of the chain start plus the opposite active time gives an
inconsistent active-controller C-closure.
-/
theorem left_chain_cutTime_cClosure_inconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation i)
    (cutTimes : ChainCutTimes chain)
    (hrightActive :
      ∀ l : Fin chain.edgeCount,
        cd.rightDerivation.Active (cd.rightIndex (chain.current l)))
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex i))
    (hcontr :
      (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime i)) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hleftClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) :=
    left_chain_start_cutTime_mem_cClosure cd chain cutTimes hrightActive
  have hrightTime : ActiveTimeCircuit cd (cd.rightTime i) :=
    right_active_time_mem_activeTimeCircuit cd i hrightActiveStart
  have hrightClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.rightTime i) :=
    activeTimeCircuit_mem_cClosure cd hrightTime
  exact
    ⟨cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩, cd.rightTime i,
      hleftClosed, hrightClosed, hcontr⟩

/--
Closure of the chain start plus the opposite active time gives an
inconsistent active-controller C-closure.
-/
theorem right_chain_cutTime_cClosure_inconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (chain : ChainOfCuts cd.rightDerivation (cd.rightIndex i))
    (cutTimes : ChainCutTimes chain)
    (hleftActive :
      ∀ l : Fin chain.edgeCount,
        cd.leftDerivation.Active
          (Fin.cast cd.circuit.length_eq.symm (chain.current l)))
    (hleftActiveStart : cd.leftDerivation.Active i)
    (hcontr :
      (cd.leftTime i) 🗲 (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hrightClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) :=
    right_chain_start_cutTime_mem_cClosure cd chain cutTimes hleftActive
  have hleftTime : ActiveTimeCircuit cd (cd.leftTime i) :=
    left_active_time_mem_activeTimeCircuit cd i hleftActiveStart
  have hleftClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.leftTime i) :=
    activeTimeCircuit_mem_cClosure cd hleftTime
  exact
    ⟨cd.leftTime i, cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩,
      hleftClosed, hrightClosed, hcontr⟩

/--
One-sided inconsistency bridge: if the left final time is
already in the active-controller C-closure and the matching right time is
active, then an inconsistent index makes the active-controller C-closure
inconsistent.
-/
theorem cClosure_inconsistent_of_left_closed_right_active
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hleftClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.leftTime i))
    (hrightActive : cd.rightDerivation.Active (cd.rightIndex i))
    (hinconsistent : cd.InconsistentIndex i) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hrightTime : ActiveTimeCircuit cd (cd.rightTime i) :=
    right_active_time_mem_activeTimeCircuit cd i hrightActive
  have hrightClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.rightTime i) :=
    activeTimeCircuit_mem_cClosure cd hrightTime
  have hcontr : (cd.leftTime i) 🗲 (cd.rightTime i) :=
    cd.inconsistentIndex_contradicts_final hinconsistent
  exact ⟨cd.leftTime i, cd.rightTime i, hleftClosed, hrightClosed, hcontr⟩

/--
One-sided inconsistency bridge: if the right final time is
already in the active-controller C-closure and the matching left time is active,
then an inconsistent index makes the active-controller C-closure inconsistent.
-/
theorem cClosure_inconsistent_of_left_active_right_closed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hleftActive : cd.leftDerivation.Active i)
    (hrightClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.rightTime i))
    (hinconsistent : cd.InconsistentIndex i) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hleftTime : ActiveTimeCircuit cd (cd.leftTime i) :=
    left_active_time_mem_activeTimeCircuit cd i hleftActive
  have hleftClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.leftTime i) :=
    activeTimeCircuit_mem_cClosure cd hleftTime
  have hcontr : (cd.leftTime i) 🗲 (cd.rightTime i) :=
    cd.inconsistentIndex_contradicts_final hinconsistent
  exact ⟨cd.leftTime i, cd.rightTime i, hleftClosed, hrightClosed, hcontr⟩

/--
Left-inactive branch of the proof of Theorem 6.4.3, with explicit chain
attestation bounds and right-chain activity as hypotheses: an active
inconsistent index that is inactive on the left makes the active-controller
C-closure inconsistent (Definition 6.4.2).
-/
theorem leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_steps
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hleftInactive : cd.leftDerivation.Inactive i)
    (chain : ChainOfCuts cd.leftDerivation i)
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightActive :
      ∀ l : Fin chain.edgeCount,
        cd.rightDerivation.Active (cd.rightIndex (chain.current l))) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hrightActiveStart :
      cd.rightDerivation.Active (cd.rightIndex i) := by
    cases hactiveInconsistent.1 with
    | inl hleftActive =>
        exact False.elim (hleftActive hleftInactive)
    | inr hrightActiveStart =>
        exact hrightActiveStart
  have hleftClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.leftTime i) :=
    left_chain_start_time_mem_cClosure_of_steps cd chain hattest_le hrightActive
  exact cClosure_inconsistent_of_left_closed_right_active cd hleftClosed
    hrightActiveStart hactiveInconsistent.2

/--
Left-inactive branch of the proof of Theorem 6.4.3, with explicit chain
attestation bounds and a no-final-contradiction premise below the chain start;
right compatibility then supplies the right-chain activity, yielding an
inconsistent active-controller C-closure (Definition 6.4.2).
-/
theorem leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_no_final_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hleftInactive : cd.leftDerivation.Inactive i)
    (chain : ChainOfCuts cd.leftDerivation i)
    (hcompat : cd.RightCompatibleUpTo i)
    (hnoContr :
      ∀ upper : cd.Index, upper.val ≤ i.val →
        ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l))) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hrightActiveStart :
      cd.rightDerivation.Active (cd.rightIndex i) := by
    cases hactiveInconsistent.1 with
    | inl hleftActive =>
        exact False.elim (hleftActive hleftInactive)
    | inr hrightActive =>
        exact hrightActive
  have hrightActive :
      ∀ l : Fin chain.edgeCount,
        cd.rightDerivation.Active (cd.rightIndex (chain.current l)) :=
    ChainOfCuts.left_chain_right_active_of_no_final_contradiction
      cd chain hcompat hrightActiveStart hnoContr
  exact leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_steps
    cd hactiveInconsistent hleftInactive chain hattest_le hrightActive

/--
Left-inactive branch of the proof of Theorem 6.4.3 in the form matching the
paper: leastness of the inconsistent index supplies the right-chain activity,
leaving only the chain attestation bounds as an explicit hypothesis.
-/
theorem leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_least
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound i : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound i)
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hleftInactive : cd.leftDerivation.Inactive i)
    (chain : ChainOfCuts cd.leftDerivation i)
    (hcompat : cd.RightCompatibleUpTo i)
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l))) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hrightActive :
      ∀ l : Fin chain.edgeCount,
        cd.rightDerivation.Active (cd.rightIndex (chain.current l)) :=
    ChainOfCuts.left_chain_right_active_of_least_inconsistent_active
      cd hleast hactiveInconsistent.1 chain hcompat
  exact leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_steps
    cd hactiveInconsistent hleftInactive chain hattest_le hrightActive

/--
Right-inactive branch of the proof of Theorem 6.4.3, with explicit chain
attestation bounds and left-chain activity as hypotheses: an active
inconsistent index that is inactive on the right makes the active-controller
C-closure inconsistent (Definition 6.4.2).
-/
theorem rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_steps
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hrightInactive : cd.rightDerivation.Inactive (cd.rightIndex i))
    (chain : ChainOfCuts cd.rightDerivation (cd.rightIndex i))
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l)))
    (hleftActive :
      ∀ l : Fin chain.edgeCount,
        cd.leftDerivation.Active
          (Fin.cast cd.circuit.length_eq.symm (chain.current l))) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hleftActiveStart : cd.leftDerivation.Active i := by
    cases hactiveInconsistent.1 with
    | inl hleftActiveStart =>
        exact hleftActiveStart
    | inr hrightActive =>
        exact False.elim (hrightActive hrightInactive)
  have hrightClosed :
      CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
        (cd.rightTime i) := by
    have hclosed :
        CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
          (cd.circuit.right.1.get (cd.rightIndex i)) :=
      right_chain_start_time_mem_cClosure_of_steps cd chain hattest_le hleftActive
    simpa [CircuitDerivation.rightTime] using hclosed
  exact cClosure_inconsistent_of_left_active_right_closed cd hleftActiveStart
    hrightClosed hactiveInconsistent.2

/--
Right-inactive branch of the proof of Theorem 6.4.3, with explicit chain
attestation bounds and a no-final-contradiction premise below the right-chain
start; right compatibility then supplies the left-chain activity, yielding an
inconsistent active-controller C-closure (Definition 6.4.2).
-/
theorem rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_no_final_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hrightInactive : cd.rightDerivation.Inactive (cd.rightIndex i))
    (chain : ChainOfCuts cd.rightDerivation (cd.rightIndex i))
    (hcompat : cd.RightCompatibleUpTo i)
    (hnoContr :
      ∀ upper : cd.circuit.right.1.Index, upper.val ≤ (cd.rightIndex i).val →
        ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hleftActiveStart : cd.leftDerivation.Active i := by
    cases hactiveInconsistent.1 with
    | inl hleftActive =>
        exact hleftActive
    | inr hrightActive =>
        exact False.elim (hrightActive hrightInactive)
  have hcompatStart :
      cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i)) := by
    simpa [CircuitDerivation.rightIndex] using hcompat
  have hleftActiveStartCast :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i)) := by
    simpa [CircuitDerivation.rightIndex] using hleftActiveStart
  have hleftActive :
      ∀ l : Fin chain.edgeCount,
        cd.leftDerivation.Active
          (Fin.cast cd.circuit.length_eq.symm (chain.current l)) :=
    ChainOfCuts.right_chain_left_active_of_no_final_contradiction
      cd chain hcompatStart hleftActiveStartCast hnoContr
  exact rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_steps
    cd hactiveInconsistent hrightInactive chain hattest_le hleftActive

/--
Right-inactive branch of the proof of Theorem 6.4.3 in the form matching the
paper: leastness of the inconsistent index on the swapped side supplies the
left-chain activity, leaving only the chain attestation bounds as an explicit
hypothesis.
-/
theorem rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_least
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound i : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound i)
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hrightInactive : cd.rightDerivation.Inactive (cd.rightIndex i))
    (chain : ChainOfCuts cd.rightDerivation (cd.rightIndex i))
    (hcompat : cd.RightCompatibleUpTo i)
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hleftActiveStart : cd.leftDerivation.Active i := by
    cases hactiveInconsistent.1 with
    | inl hleftActive =>
        exact hleftActive
    | inr hrightActive =>
        exact False.elim (hrightActive hrightInactive)
  have hcompatStart :
      cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i)) := by
    simpa [CircuitDerivation.rightIndex] using hcompat
  have hleftActiveStartCast :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i)) := by
    simpa [CircuitDerivation.rightIndex] using hleftActiveStart
  have hleftActive :
      ∀ l : Fin chain.edgeCount,
        cd.leftDerivation.Active
          (Fin.cast cd.circuit.length_eq.symm (chain.current l)) :=
    ChainOfCuts.right_chain_left_active_of_least_inconsistent
      cd (cd.swap_leastInconsistentAtOrBelow hleast) chain hcompatStart
      hleftActiveStartCast
  exact rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_steps
    cd hactiveInconsistent hrightInactive chain hattest_le hleftActive

/--
Left-inactive branch of the proof of Theorem 6.4.3 over the proof-local pre-Cut
chain times `t_r`: leastness supplies the right-chain activity, and the start
contradiction `t₁ 🗲 t'` is taken as an explicit hypothesis.
-/
theorem leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_cutTimes_least
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound i : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound i)
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hleftInactive : cd.leftDerivation.Inactive i)
    (chain : ChainOfCuts cd.leftDerivation i)
    (cutTimes : ChainCutTimes chain)
    (hcompat : cd.RightCompatibleUpTo i)
    (hcontr :
      (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime i)) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hrightActiveStart :
      cd.rightDerivation.Active (cd.rightIndex i) := by
    cases hactiveInconsistent.1 with
    | inl hleftActive =>
        exact False.elim (hleftActive hleftInactive)
    | inr hrightActive =>
        exact hrightActive
  have hrightActive :
      ∀ l : Fin chain.edgeCount,
        cd.rightDerivation.Active (cd.rightIndex (chain.current l)) :=
    ChainOfCuts.left_chain_right_active_of_least_inconsistent_active
      cd hleast hactiveInconsistent.1 chain hcompat
  exact left_chain_cutTime_cClosure_inconsistent cd chain cutTimes hrightActive
    hrightActiveStart hcontr

/--
Right-inactive branch of the proof of Theorem 6.4.3 over the proof-local pre-Cut
chain times `t_r`: swapped leastness supplies the left-chain activity, and the
start contradiction is taken as an explicit hypothesis.
-/
theorem rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_cutTimes_least
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound i : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound i)
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hrightInactive : cd.rightDerivation.Inactive (cd.rightIndex i))
    (chain : ChainOfCuts cd.rightDerivation (cd.rightIndex i))
    (cutTimes : ChainCutTimes chain)
    (hcompat : cd.RightCompatibleUpTo i)
    (hcontr :
      (cd.leftTime i) 🗲 (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hleftActiveStart : cd.leftDerivation.Active i := by
    cases hactiveInconsistent.1 with
    | inl hleftActive =>
        exact hleftActive
    | inr hrightActive =>
        exact False.elim (hrightActive hrightInactive)
  have hcompatStart :
      cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i)) := by
    simpa [CircuitDerivation.rightIndex] using hcompat
  have hleftActiveStartCast :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i)) := by
    simpa [CircuitDerivation.rightIndex] using hleftActiveStart
  have hleftActive :
      ∀ l : Fin chain.edgeCount,
        cd.leftDerivation.Active
          (Fin.cast cd.circuit.length_eq.symm (chain.current l)) :=
    ChainOfCuts.right_chain_left_active_of_least_inconsistent
      cd (cd.swap_leastInconsistentAtOrBelow hleast) chain hcompatStart
      hleftActiveStartCast
  exact right_chain_cutTime_cClosure_inconsistent cd chain cutTimes hleftActive
    hleftActiveStart hcontr

/--
Left-inactive branch of the proof of Theorem 6.4.3 with the
no-final-contradiction premise phrased over paper indices. The
no-final-contradiction premise and chain attestation bounds remain explicit
hypotheses.
-/
theorem leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_no_final_contradiction_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hleftInactive : cd.leftDerivation.Inactive i)
    (chain : ChainOfCuts cd.leftDerivation i)
    (hcompat : cd.RightCompatibleUpTo i)
    (hnoContr :
      ∀ upper : cd.Index,
        cd.circuit.left.1.paperIndex upper ≤ cd.circuit.left.1.paperIndex i →
        ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l))) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hrightActiveStart :
      cd.rightDerivation.Active (cd.rightIndex i) := by
    cases hactiveInconsistent.1 with
    | inl hleftActive =>
        exact False.elim (hleftActive hleftInactive)
    | inr hrightActive =>
        exact hrightActive
  have hrightActive :
      ∀ l : Fin chain.edgeCount,
        cd.rightDerivation.Active (cd.rightIndex (chain.current l)) :=
    ChainOfCuts.left_chain_right_active_of_no_final_contradiction_indexed
      cd chain hcompat hrightActiveStart hnoContr
  exact leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_steps
    cd hactiveInconsistent hleftInactive chain hattest_le hrightActive

/--
Right-inactive branch of the proof of Theorem 6.4.3 with the
no-final-contradiction premise phrased over paper indices on the swapped side.
The no-final-contradiction premise and chain attestation bounds remain explicit
hypotheses.
-/
theorem rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_no_final_contradiction_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hrightInactive : cd.rightDerivation.Inactive (cd.rightIndex i))
    (chain : ChainOfCuts cd.rightDerivation (cd.rightIndex i))
    (hcompat : cd.RightCompatibleUpTo i)
    (hnoContr :
      ∀ upper : cd.circuit.right.1.Index,
        cd.circuit.right.1.paperIndex upper ≤
          cd.circuit.right.1.paperIndex (cd.rightIndex i) →
        ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hattest_le :
      ∀ l : Fin chain.edgeCount,
        ∃ source : Time,
          (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hleftActiveStart : cd.leftDerivation.Active i := by
    cases hactiveInconsistent.1 with
    | inl hleftActive =>
        exact hleftActive
    | inr hrightActive =>
        exact False.elim (hrightActive hrightInactive)
  have hcompatStart :
      cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i)) := by
    simpa [CircuitDerivation.rightIndex] using hcompat
  have hleftActiveStartCast :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i)) := by
    simpa [CircuitDerivation.rightIndex] using hleftActiveStart
  have hleftActive :
      ∀ l : Fin chain.edgeCount,
        cd.leftDerivation.Active
          (Fin.cast cd.circuit.length_eq.symm (chain.current l)) :=
    ChainOfCuts.right_chain_left_active_of_no_final_contradiction_indexed
      cd chain hcompatStart hleftActiveStartCast hnoContr
  exact rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_steps
    cd hactiveInconsistent hrightInactive chain hattest_le hleftActive

/--
Active-on-both branch of the proof of Theorem 6.4.3 (paper p. 47, the case
"if l is active in both Π and Π'"): when the inconsistent index i is active in
both final derivations, its two contradictory times Π[i], Π'[i] are active times
whose controllers are active, so both already lie in the C-closure by
Definition 6.2.1(1); hence the active-controller closure of the active times is
inconsistent.
-/
theorem doublyActive_inconsistentIndex_cClosure_inconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hactive : cd.DoublyActive i)
    (hinconsistent : cd.InconsistentIndex i) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hcontr : (cd.leftTime i) 🗲 (cd.rightTime i) :=
    cd.inconsistentIndex_contradicts_final hinconsistent
  have hleftTime : ActiveTimeCircuit cd (cd.leftTime i) :=
    left_active_time_mem_activeTimeCircuit cd i hactive.1
  have hrightTime : ActiveTimeCircuit cd (cd.rightTime i) :=
    right_active_time_mem_activeTimeCircuit cd i hactive.2
  have hleftCtrl : ActiveCtrlCircuit cd (controller (cd.leftTime i)) :=
    activeTimeCircuit_controller_mem cd hleftTime
  have hrightCtrl : ActiveCtrlCircuit cd (controller (cd.rightTime i)) :=
    activeTimeCircuit_controller_mem cd hrightTime
  exact
    ⟨cd.leftTime i, cd.rightTime i, CClosure.init hleftTime hleftCtrl,
      CClosure.init hrightTime hrightCtrl, hcontr⟩

/--
Case split in the proof of Theorem 6.4.3 over an active inconsistent index i:
the doubly-active case is closed by
`doublyActive_inconsistentIndex_cClosure_inconsistent`, and the two one-sided
cases (active on one side, inactive/cut on the other, per Proposition 5.3.3) are
discharged by the supplied branch hypotheses `hleftInactive`, `hrightInactive`.
Yields C-closure inconsistency for every active inconsistent index.
-/
theorem activeInconsistentIndex_cClosure_inconsistent_of_one_sided_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hleftInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Inactive i →
          cd.rightDerivation.Active (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)))
    (hrightInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Active i →
          cd.rightDerivation.Inactive (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))) :
    ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  intro i hactiveInconsistent
  rcases hactiveInconsistent with ⟨hactive, hinconsistent⟩
  cases hactive with
  | inl hleftActive =>
      by_cases hrightActive : cd.rightDerivation.Active (cd.rightIndex i)
      · exact doublyActive_inconsistentIndex_cClosure_inconsistent cd
          ⟨hleftActive, hrightActive⟩ hinconsistent
      · have hrightInactive_i : cd.rightDerivation.Inactive (cd.rightIndex i) :=
          Classical.not_not.mp hrightActive
        exact hrightInactive i ⟨Or.inl hleftActive, hinconsistent⟩ hleftActive
          hrightInactive_i
  | inr hrightActive =>
      by_cases hleftActive : cd.leftDerivation.Active i
      · exact doublyActive_inconsistentIndex_cClosure_inconsistent cd
          ⟨hleftActive, hrightActive⟩ hinconsistent
      · have hleftInactive_i : cd.leftDerivation.Inactive i :=
          Classical.not_not.mp hleftActive
        exact hleftInactive i ⟨Or.inr hrightActive, hinconsistent⟩
          hleftInactive_i hrightActive

/--
Theorem 6.4.3(1) for the active-controller closure of the active times,
assembled from `hmain` (the Corollary 5.6.4 reduction: an inconsistent
circuit-derivation has an active inconsistent index) and `hactive` (every active
inconsistent index forces C-closure inconsistency). Concludes that inconsistency
of the circuit-derivation implies inconsistency of the C-closure.
-/
theorem cClosure_inconsistent_of_active_inconsistent_index_result
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hmain : cd.Inconsistent → cd.ActiveInconsistent)
    (hactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        TimesInconsistent
          (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  intro hinconsistent
  rcases hmain hinconsistent with ⟨i, hactiveInconsistent⟩
  exact hactive i hactiveInconsistent

/--
Theorem 6.4.3(2), the contrapositive of clause (1): if the active-controller
closure of the active times is consistent then the circuit-derivation is
consistent. Uses the same `hmain`/`hactive` hypotheses as
`cClosure_inconsistent_of_active_inconsistent_index_result`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_active_index_result
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hmain : cd.Inconsistent → cd.ActiveInconsistent)
    (hactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        TimesInconsistent
          (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_active_inconsistent_index_result cd hmain hactive
      hinconsistent)

/--
Theorem 6.4.3(1) with the active-inconsistent-index case split already applied:
the only remaining hypotheses are `hmain` (the Corollary 5.6.4 reduction to an
active inconsistent index) and the two one-sided closure branches
`hleftInactive`, `hrightInactive`.
-/
theorem cClosure_inconsistent_of_one_sided_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hmain : cd.Inconsistent → cd.ActiveInconsistent)
    (hleftInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Inactive i →
          cd.rightDerivation.Active (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)))
    (hrightInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Active i →
          cd.rightDerivation.Inactive (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_active_inconsistent_index_result cd hmain
    (activeInconsistentIndex_cClosure_inconsistent_of_one_sided_branches cd
      hleftInactive hrightInactive)

/--
Intermediate step toward Theorem 6.4.3(1); NOT the full theorem. The reduction
from inconsistency to an active inconsistent index (Corollary 5.6.4) is obtained
from the three ordered same-center hypotheses `hdirectSameCenterBranch`,
`hswapSameCenterBranch`, `hrightConsistent`; the two one-sided C-closure branches
`hleftInactive`, `hrightInactive` (the chain-of-cuts argument of Definition 6.3.1
with Lemmas 6.3.2–6.3.3) remain explicit hypotheses. Concludes that
inconsistency of the circuit-derivation implies inconsistency of the C-closure.
-/
theorem cClosure_inconsistent_of_ordered_incompatible_branches_and_right_consistent_and_one_sided_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hdirectSameCenterBranch :
      ∀ {center leftLower rightLower cutLower : cd.Index}
          {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        leftLower.val < rightLower.val →
        leftLower.val ≤ cutLower.val →
        cutLower.val < rightLower.val →
        ContainsCut cd.leftDerivation
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower)
          (cd.circuit.left.1.paperIndex cutLower) →
        ∃ l : cd.Index,
          l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
            cd.ActiveInconsistentIndex l)
    (hswapSameCenterBranch :
      ∀ {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        rightLower.val < leftLower.val →
          ∀ {cutLower : cd.swap.Index},
            (cd.rightIndex rightLower).val ≤ cutLower.val →
            cutLower.val < (cd.rightIndex leftLower).val →
            ContainsCut cd.swap.leftDerivation
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex center))
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower))
              (cd.swap.circuit.left.1.paperIndex cutLower) →
            ∃ l : cd.swap.Index,
              l.val < (cd.rightIndex center).val ∧
                cd.swap.RightCompatibleUpTo l ∧
                  cd.swap.ActiveInconsistentIndex l)
    (hrightConsistent :
      ∀ j : cd.Index, cd.RightCompatibleUpTo j → cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Inactive i →
          cd.rightDerivation.Active (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)))
    (hrightInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Active i →
          cd.rightDerivation.Inactive (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_one_sided_branches cd
      (ConsistentHistories.Routes.PathProperties.MainResult.inconsistent_activeInconsistent_of_ordered_incompatible_branches_and_right_consistent
        cd hdirectSameCenterBranch hswapSameCenterBranch hrightConsistent)
      hleftInactive hrightInactive

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_one_sided_branches`: with the Corollary 5.6.4
reduction `hmain` and the two one-sided closure branches supplied, consistency
of the C-closure implies consistency of the circuit-derivation.
-/
theorem circuit_consistent_of_cClosure_consistent_and_one_sided_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hmain : cd.Inconsistent → cd.ActiveInconsistent)
    (hleftInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Inactive i →
          cd.rightDerivation.Active (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)))
    (hrightInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Active i →
          cd.rightDerivation.Inactive (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  exact circuit_consistent_of_cClosure_consistent_and_active_index_result cd hmain
    (activeInconsistentIndex_cClosure_inconsistent_of_one_sided_branches cd
      hleftInactive hrightInactive)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_ordered_incompatible_branches_and_right_consistent_and_one_sided_branches`;
carries the same explicit ordered same-center and one-sided closure hypotheses.
-/
theorem circuit_consistent_of_cClosure_consistent_and_ordered_incompatible_branches_and_right_consistent_and_one_sided_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hdirectSameCenterBranch :
      ∀ {center leftLower rightLower cutLower : cd.Index}
          {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        leftLower.val < rightLower.val →
        leftLower.val ≤ cutLower.val →
        cutLower.val < rightLower.val →
        ContainsCut cd.leftDerivation
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower)
          (cd.circuit.left.1.paperIndex cutLower) →
        ∃ l : cd.Index,
          l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
            cd.ActiveInconsistentIndex l)
    (hswapSameCenterBranch :
      ∀ {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        rightLower.val < leftLower.val →
          ∀ {cutLower : cd.swap.Index},
            (cd.rightIndex rightLower).val ≤ cutLower.val →
            cutLower.val < (cd.rightIndex leftLower).val →
            ContainsCut cd.swap.leftDerivation
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex center))
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower))
              (cd.swap.circuit.left.1.paperIndex cutLower) →
            ∃ l : cd.swap.Index,
              l.val < (cd.rightIndex center).val ∧
                cd.swap.RightCompatibleUpTo l ∧
                  cd.swap.ActiveInconsistentIndex l)
    (hrightConsistent :
      ∀ j : cd.Index, cd.RightCompatibleUpTo j → cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Inactive i →
          cd.rightDerivation.Active (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)))
    (hrightInactive :
      ∀ i : cd.Index, cd.ActiveInconsistentIndex i →
        cd.leftDerivation.Active i →
          cd.rightDerivation.Inactive (cd.rightIndex i) →
            TimesInconsistent
              (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  exact
    circuit_consistent_of_cClosure_consistent_and_one_sided_branches cd
      (ConsistentHistories.Routes.PathProperties.MainResult.inconsistent_activeInconsistent_of_ordered_incompatible_branches_and_right_consistent
        cd hdirectSameCenterBranch hswapSameCenterBranch hrightConsistent)
      hleftInactive hrightInactive

/--
Theorem 6.4.3(1) after reducing to the least inconsistent index: `hindex` is the
Corollary 5.6.4 reduction (an inconsistent index has an active inconsistent index
at or below it); the least inconsistent index is then extracted, its
doubly-active case is closed internally, and the two one-sided cases are left as
the least-index branch hypotheses `hleftInactive`, `hrightInactive`.
-/
theorem cClosure_inconsistent_of_least_one_sided_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftInactive :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  TimesInconsistent
                    (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)))
    (hrightInactive :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  TimesInconsistent
                    (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  rintro ⟨bound, hinconsistentBound⟩
  rcases cd.exists_leastInconsistentAtOrBelow hinconsistentBound with
    ⟨least, hleast⟩
  have hleastResult :
      cd.RightCompatibleUpTo least ∧ cd.ActiveInconsistentIndex least :=
    ConsistentHistories.Routes.PathProperties.MainResult.least_inconsistent_activeInconsistent_of_index_result
      cd hleast hindex
  rcases hleastResult with ⟨hcompatLeast, hactiveInconsistentLeast⟩
  rcases hactiveInconsistentLeast with ⟨hactiveLeast, hinconsistentLeast⟩
  cases hactiveLeast with
  | inl hleftActive =>
      by_cases hrightActive : cd.rightDerivation.Active (cd.rightIndex least)
      · exact doublyActive_inconsistentIndex_cClosure_inconsistent cd
          ⟨hleftActive, hrightActive⟩ hinconsistentLeast
      · have hrightInactiveLeast :
            cd.rightDerivation.Inactive (cd.rightIndex least) :=
          Classical.not_not.mp hrightActive
        exact hrightInactive hleast hcompatLeast
          ⟨Or.inl hleftActive, hinconsistentLeast⟩ hleftActive hrightInactiveLeast
  | inr hrightActive =>
      by_cases hleftActive : cd.leftDerivation.Active least
      · exact doublyActive_inconsistentIndex_cClosure_inconsistent cd
          ⟨hleftActive, hrightActive⟩ hinconsistentLeast
      · have hleftInactiveLeast : cd.leftDerivation.Inactive least :=
          Classical.not_not.mp hleftActive
        exact hleftInactive hleast hcompatLeast
          ⟨Or.inr hrightActive, hinconsistentLeast⟩ hleftInactiveLeast hrightActive

/--
Theorem 6.4.3(1) via the chain of Cuts (Definition 6.3.1). Chain activity along
the reverse induction is supplied by leastness of the inconsistent index; the
Corollary 5.6.4 active-index reduction `hindex` and the per-edge Cut-step bounds
`hleftEdges`, `hrightEdges` (each edge time factors as `source # current ≼ next`,
the Cut rule of Figure 9 together with Lemma 4.2.2) remain explicit hypotheses.
-/
theorem cClosure_inconsistent_of_least_chain_branches_from_edges
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_least_one_sided_branches cd hindex
    (hleftInactive := by
      intro bound least hleast hcompat hactiveInconsistent hleftInactive hrightActive
      rcases ChainOfCuts.exists_of_inactive hleftInactive with ⟨chain⟩
      exact
        leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_least
          cd hleast hactiveInconsistent hleftInactive chain hcompat
          (hleftEdges hleast hcompat hactiveInconsistent hleftInactive hrightActive chain))
    (hrightInactive := by
      intro bound least hleast hcompat hactiveInconsistent hleftActive hrightInactive
      rcases ChainOfCuts.exists_of_inactive hrightInactive with ⟨chain⟩
      exact
        rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_least
          cd hleast hactiveInconsistent hrightInactive chain hcompat
          (hrightEdges hleast hcompat hactiveInconsistent hleftActive hrightInactive chain))

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_least_chain_branches_from_edges`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_least_chain_branches_from_edges
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_least_chain_branches_from_edges
      cd hindex hleftEdges hrightEdges hinconsistent)

/--
Theorem 6.4.3(1) via the chain of Cuts (Definition 6.3.1), packaging each chain
with a `ChainCutTimes` structure (the times `t_r` at each chain index just before
it is cut). Chain activity is supplied by leastness; the Corollary 5.6.4
active-index reduction `hindex` and the two chain-time packages `hleftCutTimes`,
`hrightCutTimes` — each providing the first pre-Cut time `t_1` and its
contradiction with the opposite side — remain explicit hypotheses.
-/
theorem cClosure_inconsistent_of_least_chain_cutTimes
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftCutTimes :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∃ cutTimes : ChainCutTimes chain,
                      (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime least))
    (hrightCutTimes :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∃ cutTimes : ChainCutTimes chain,
                      (cd.leftTime least) 🗲 (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_least_one_sided_branches cd hindex
    (hleftInactive := by
      intro bound least hleast hcompat hactiveInconsistent hleftInactive hrightActive
      rcases ChainOfCuts.exists_of_inactive hleftInactive with ⟨chain⟩
      rcases hleftCutTimes hleast hcompat hactiveInconsistent hleftInactive
          hrightActive chain with
        ⟨cutTimes, hcontr⟩
      exact
        leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_cutTimes_least
          cd hleast hactiveInconsistent hleftInactive chain cutTimes hcompat hcontr)
    (hrightInactive := by
      intro bound least hleast hcompat hactiveInconsistent hleftActive hrightInactive
      rcases ChainOfCuts.exists_of_inactive hrightInactive with ⟨chain⟩
      rcases hrightCutTimes hleast hcompat hactiveInconsistent hleftActive
          hrightInactive chain with
        ⟨cutTimes, hcontr⟩
      exact
        rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_cutTimes_least
          cd hleast hactiveInconsistent hrightInactive chain cutTimes hcompat hcontr)

/--
Left-inactive branch of the proof of Theorem 6.4.3 (paper p. 47–48: the WLOG
case where l is active in Π' and inactive, hence cut by Proposition 5.3.3, in Π,
using the chain of Cuts of Definition 6.3.1 and Lemma 6.3.3). Uses the canonical
`ChainCutTimes.ofChainLinks` built from the chain links; the one remaining
explicit premise `hcontr` is the first pre-Cut contradiction `t_1 🗲 Π'[l]`
(the paper's `t_1 🗲 t'`).
-/
theorem leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_links_least
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound i : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound i)
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hleftInactive : cd.leftDerivation.Inactive i)
    (chain : ChainOfCuts cd.leftDerivation i)
    (hcompat : cd.RightCompatibleUpTo i)
    (hcontr :
      ((ChainCutTimes.ofChainLinks chain).time
          ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime i)) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_cutTimes_least
      cd hleast hactiveInconsistent hleftInactive chain
      (ChainCutTimes.ofChainLinks chain) hcompat hcontr

/--
Right-inactive branch of the proof of Theorem 6.4.3, the mirror of
`leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_links_least`
(l active in Π and inactive/cut in Π'), by the symmetric chain of Cuts. Uses the
canonical `ChainCutTimes.ofChainLinks`; the one remaining explicit premise
`hcontr` is the first pre-Cut contradiction `Π[l] 🗲 t_1`.
-/
theorem rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_links_least
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound i : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound i)
    (hactiveInconsistent : cd.ActiveInconsistentIndex i)
    (hrightInactive : cd.rightDerivation.Inactive (cd.rightIndex i))
    (chain : ChainOfCuts cd.rightDerivation (cd.rightIndex i))
    (hcompat : cd.RightCompatibleUpTo i)
    (hcontr :
      (cd.leftTime i) 🗲 ((ChainCutTimes.ofChainLinks chain).time
          ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    TimesInconsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_cutTimes_least
      cd hleast hactiveInconsistent hrightInactive chain
      (ChainCutTimes.ofChainLinks chain) hcompat hcontr

/--
Theorem 6.4.3(1) using the canonical `ChainCutTimes.ofChainLinks` for each chain
of Cuts (Definition 6.3.1). The Corollary 5.6.4 active-index reduction `hindex`
and the two first pre-Cut contradiction bridges `hleftContr`, `hrightContr` (the
paper's `t_1 🗲 t'`) remain explicit hypotheses.
-/
theorem cClosure_inconsistent_of_least_chain_links
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ((ChainCutTimes.ofChainLinks chain).time
                        ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime least))
    (hrightContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    (cd.leftTime least) 🗲 ((ChainCutTimes.ofChainLinks chain).time
                        ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_cutTimes cd hindex
      (hleftCutTimes := by
        intro bound least hleast hcompat hactiveInconsistent hleftInactive
          hrightActive chain
        exact
          ⟨ChainCutTimes.ofChainLinks chain,
            hleftContr hleast hcompat hactiveInconsistent hleftInactive
              hrightActive chain⟩)
      (hrightCutTimes := by
        intro bound least hleast hcompat hactiveInconsistent hleftActive
          hrightInactive chain
        exact
          ⟨ChainCutTimes.ofChainLinks chain,
            hrightContr hleast hcompat hactiveInconsistent hleftActive
              hrightInactive chain⟩)

/-- Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_least_chain_links`. -/
theorem circuit_consistent_of_cClosure_consistent_and_least_chain_links
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ((ChainCutTimes.ofChainLinks chain).time
                        ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime least))
    (hrightContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    (cd.leftTime least) 🗲 ((ChainCutTimes.ofChainLinks chain).time
                        ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_least_chain_links
      cd hindex hleftContr hrightContr hinconsistent)

/--
Theorem 6.4.3(1) with both one-sided chain branches fully discharged: the first
pre-Cut contradiction bridges are supplied internally by
`left_first_chain_link_time_contradicts_right_of_activeInconsistent` and its
mirror, so the only remaining hypothesis is the Corollary 5.6.4 active-index
reduction `hindex`.
-/
theorem cClosure_inconsistent_of_least_chain_links_closed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_links cd hindex
      (hleftContr := by
        intro _bound least _hleast _hcompat hactiveInconsistent _hleftInactive
          _hrightActive chain
        exact
          left_first_chain_link_time_contradicts_right_of_activeInconsistent
            cd hactiveInconsistent chain)
      (hrightContr := by
        intro _bound least _hleast _hcompat hactiveInconsistent _hleftActive
          _hrightInactive chain
        exact
          right_first_chain_link_time_contradicts_left_of_activeInconsistent
            cd hactiveInconsistent chain)

/-- Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_least_chain_links_closed`. -/
theorem circuit_consistent_of_cClosure_consistent_and_least_chain_links_closed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_least_chain_links_closed
      cd hindex hinconsistent)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_least_chain_cutTimes`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_least_chain_cutTimes
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftCutTimes :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∃ cutTimes : ChainCutTimes chain,
                      (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime least))
    (hrightCutTimes :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∃ cutTimes : ChainCutTimes chain,
                      (cd.leftTime least) 🗲 (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_least_chain_cutTimes
      cd hindex hleftCutTimes hrightCutTimes hinconsistent)

/--
Theorem 6.4.3(1) with each one-sided branch reduced to two explicit chain
obligations: a no-contradiction condition below the least inconsistent index
(`hleftNoContr`, `hrightNoContr`) and the per-edge Cut-step bounds (`hleftEdges`,
`hrightEdges`). The Corollary 5.6.4 active-index reduction `hindex` remains
explicit.
-/
theorem cClosure_inconsistent_of_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_least_one_sided_branches cd hindex
    (hleftInactive := by
      intro bound least hleast hcompat hactiveInconsistent hleftInactive hrightActive
      rcases ChainOfCuts.exists_of_inactive hleftInactive with ⟨chain⟩
      exact
        leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_no_final_contradiction
          cd hactiveInconsistent hleftInactive chain hcompat
          (hleftNoContr hleast hcompat hactiveInconsistent hleftInactive hrightActive)
          (hleftEdges hleast hcompat hactiveInconsistent hleftInactive hrightActive chain))
    (hrightInactive := by
      intro bound least hleast hcompat hactiveInconsistent hleftActive hrightInactive
      rcases ChainOfCuts.exists_of_inactive hrightInactive with ⟨chain⟩
      exact
        rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_no_final_contradiction
          cd hactiveInconsistent hrightInactive chain hcompat
          (hrightNoContr hleast hcompat hactiveInconsistent hleftActive hrightInactive)
          (hrightEdges hleast hcompat hactiveInconsistent hleftActive hrightInactive chain))

/--
Theorem 6.4.3(1) with the Corollary 5.6.4 active-index reduction obtained from
the concrete Section 5 right-incompatible (`hrightIncompatible`) and
right-consistent (`hrightConsistent`) hypotheses; the four Section 6 least-chain
obligations remain explicit.
-/
theorem cClosure_inconsistent_of_right_incompatible_and_right_consistent_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hrightConsistent :
      ∀ j : cd.Index, cd.RightCompatibleUpTo j → cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_least_chain_branches cd
    (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_right_incompatible_and_right_consistent
      cd hrightIncompatible hrightConsistent)
    hleftNoContr hleftEdges hrightNoContr hrightEdges

/--
Theorem 6.4.3(1) with the Corollary 5.6.4 active-index reduction obtained from
the concrete Section 5 right-incompatible hypothesis `hrightIncompatible` alone
(the right-consistent case is discharged internally); the four Section 6
least-chain obligations remain explicit.
-/
theorem cClosure_inconsistent_of_right_incompatible_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_branches cd
      (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_right_incompatible
        cd hrightIncompatible)
      hleftNoContr hleftEdges hrightNoContr hrightEdges

/--
Intermediate step toward Theorem 6.4.3(1); NOT the full theorem. The Corollary
5.6.4 active-index reduction is obtained from the three ordered same-center
hypotheses `hdirectSameCenterBranch`, `hswapSameCenterBranch`,
`hrightConsistent`; the four Section 6 least-chain obligations (`hleftNoContr`,
`hleftEdges`, `hrightNoContr`, `hrightEdges`) remain explicit hypotheses.
-/
theorem cClosure_inconsistent_of_ordered_incompatible_branches_and_right_consistent_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hdirectSameCenterBranch :
      ∀ {center leftLower rightLower cutLower : cd.Index}
          {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        leftLower.val < rightLower.val →
        leftLower.val ≤ cutLower.val →
        cutLower.val < rightLower.val →
        ContainsCut cd.leftDerivation
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower)
          (cd.circuit.left.1.paperIndex cutLower) →
        ∃ l : cd.Index,
          l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
            cd.ActiveInconsistentIndex l)
    (hswapSameCenterBranch :
      ∀ {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        rightLower.val < leftLower.val →
          ∀ {cutLower : cd.swap.Index},
            (cd.rightIndex rightLower).val ≤ cutLower.val →
            cutLower.val < (cd.rightIndex leftLower).val →
            ContainsCut cd.swap.leftDerivation
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex center))
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower))
              (cd.swap.circuit.left.1.paperIndex cutLower) →
            ∃ l : cd.swap.Index,
              l.val < (cd.rightIndex center).val ∧
                cd.swap.RightCompatibleUpTo l ∧
                  cd.swap.ActiveInconsistentIndex l)
    (hrightConsistent :
      ∀ j : cd.Index, cd.RightCompatibleUpTo j → cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_least_chain_branches cd
    (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_ordered_incompatible_branches_and_right_consistent
      cd hdirectSameCenterBranch hswapSameCenterBranch hrightConsistent)
    hleftNoContr hleftEdges hrightNoContr hrightEdges

/--
Theorem 6.4.3(1) with the Corollary 5.6.4 active-index reduction obtained from
the concrete Section 5 right-incompatible hypothesis `hrightIncompatible` and a
pre-circuit-prefix center-contradiction condition `hcontrPreCircuit` for the
right-consistent case; the four Section 6 least-chain obligations remain
explicit.
-/
theorem cClosure_inconsistent_of_right_incompatible_and_preCircuit_center_contradiction_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hcontrPreCircuit :
      ∀ {bound least : cd.Index},
        cd.RightCompatibleUpTo bound →
        cd.LeastInconsistentAtOrBelow bound least →
        cd.Inactive least →
          ∀ (preCd : CircuitDerivation Time) (hprefix : preCd.IsInitialPrefix cd),
            preCd.DoublyActive (preCd.prefixIndex hprefix least) →
              (preCd.leftTime (preCd.prefixIndex hprefix least)) 🗲 (preCd.rightTime (preCd.prefixIndex hprefix least)))
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_least_chain_branches cd
    (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_right_incompatible_and_preCircuit_center_contradiction
      cd hrightIncompatible hcontrPreCircuit)
    hleftNoContr hleftEdges hrightNoContr hrightEdges

/--
Theorem 6.4.3(1) as for
`cClosure_inconsistent_of_right_incompatible_and_preCircuit_center_contradiction_and_least_chain_branches`,
but the right-consistent case is discharged from an explicit Cut-prefix
center-contradiction condition `hcontrCutPrefixes` on matching left/right
`CutPrefixData`; the four Section 6 least-chain obligations remain explicit.
-/
theorem cClosure_inconsistent_of_right_incompatible_and_cutPrefix_center_contradiction_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hcontrCutPrefixes :
      ∀ {bound least : cd.Index},
        cd.RightCompatibleUpTo bound →
        cd.LeastInconsistentAtOrBelow bound least →
        cd.Inactive least →
          ∀ {leftCutK rightCutK cutI : Nat},
            (leftData :
              CutPrefixData cd.leftDerivation leftCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            (rightData :
              CutPrefixData cd.rightDerivation rightCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            (leftData.base.get leftData.idxJ) 🗲 (rightData.base.get rightData.idxJ))
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_least_chain_branches cd
    (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_right_incompatible_and_cutPrefix_center_contradiction
      cd hrightIncompatible hcontrCutPrefixes)
    hleftNoContr hleftEdges hrightNoContr hrightEdges

/--
Theorem 6.4.3(1) as for the two preceding right-incompatible routes, with the
right-consistent case discharged from an explicit witness-before-cut-base
condition `hwitnessBefore` (each contradiction-witness prefix precedes the
matching left/right Cut bases); the four Section 6 least-chain obligations remain
explicit.
-/
theorem cClosure_inconsistent_of_right_incompatible_and_witnesses_before_cut_bases_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hwitnessBefore :
      ∀ {bound least : cd.Index},
        cd.RightCompatibleUpTo bound →
        cd.LeastInconsistentAtOrBelow bound least →
        cd.Inactive least →
          ∀ {leftCutK rightCutK cutI : Nat},
            (leftData :
              CutPrefixData cd.leftDerivation leftCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            (rightData :
              CutPrefixData cd.rightDerivation rightCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            ∀ {pref : CircuitDerivation Time} (hpref : pref.IsInitialPrefix cd),
              pref.DoublyActive (pref.prefixIndex hpref least) →
              (pref.leftTime (pref.prefixIndex hpref least)) 🗲 (pref.rightTime (pref.prefixIndex hpref least)) →
              InitialPrefix pref.leftDerivation leftData.baseDeriv ∧
                InitialPrefix pref.rightDerivation rightData.baseDeriv)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_least_chain_branches cd
    (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_right_incompatible_and_witnesses_before_cut_bases
      cd hrightIncompatible hwitnessBefore)
    hleftNoContr hleftEdges hrightNoContr hrightEdges

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_right_incompatible_and_right_consistent_and_least_chain_branches`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_right_incompatible_and_right_consistent_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hrightConsistent :
      ∀ j : cd.Index, cd.RightCompatibleUpTo j → cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_right_incompatible_and_right_consistent_and_least_chain_branches
      cd hrightIncompatible hrightConsistent hleftNoContr hleftEdges
      hrightNoContr hrightEdges hinconsistent)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_right_incompatible_and_least_chain_branches`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_right_incompatible_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_right_incompatible_and_least_chain_branches
      cd hrightIncompatible hleftNoContr hleftEdges hrightNoContr hrightEdges
      hinconsistent)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_ordered_incompatible_branches_and_right_consistent_and_least_chain_branches`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_ordered_incompatible_branches_and_right_consistent_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hdirectSameCenterBranch :
      ∀ {center leftLower rightLower cutLower : cd.Index}
          {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        leftLower.val < rightLower.val →
        leftLower.val ≤ cutLower.val →
        cutLower.val < rightLower.val →
        ContainsCut cd.leftDerivation
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower)
          (cd.circuit.left.1.paperIndex cutLower) →
        ∃ l : cd.Index,
          l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
            cd.ActiveInconsistentIndex l)
    (hswapSameCenterBranch :
      ∀ {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        rightLower.val < leftLower.val →
          ∀ {cutLower : cd.swap.Index},
            (cd.rightIndex rightLower).val ≤ cutLower.val →
            cutLower.val < (cd.rightIndex leftLower).val →
            ContainsCut cd.swap.leftDerivation
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex center))
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower))
              (cd.swap.circuit.left.1.paperIndex cutLower) →
            ∃ l : cd.swap.Index,
              l.val < (cd.rightIndex center).val ∧
                cd.swap.RightCompatibleUpTo l ∧
                  cd.swap.ActiveInconsistentIndex l)
    (hrightConsistent :
      ∀ j : cd.Index, cd.RightCompatibleUpTo j → cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_ordered_incompatible_branches_and_right_consistent_and_least_chain_branches
      cd hdirectSameCenterBranch hswapSameCenterBranch hrightConsistent hleftNoContr hleftEdges
      hrightNoContr hrightEdges hinconsistent)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_right_incompatible_and_preCircuit_center_contradiction_and_least_chain_branches`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_right_incompatible_and_preCircuit_center_contradiction_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hcontrPreCircuit :
      ∀ {bound least : cd.Index},
        cd.RightCompatibleUpTo bound →
        cd.LeastInconsistentAtOrBelow bound least →
        cd.Inactive least →
          ∀ (preCd : CircuitDerivation Time) (hprefix : preCd.IsInitialPrefix cd),
            preCd.DoublyActive (preCd.prefixIndex hprefix least) →
              (preCd.leftTime (preCd.prefixIndex hprefix least)) 🗲 (preCd.rightTime (preCd.prefixIndex hprefix least)))
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_right_incompatible_and_preCircuit_center_contradiction_and_least_chain_branches
      cd hrightIncompatible hcontrPreCircuit hleftNoContr hleftEdges
      hrightNoContr hrightEdges hinconsistent)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_right_incompatible_and_cutPrefix_center_contradiction_and_least_chain_branches`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_right_incompatible_and_cutPrefix_center_contradiction_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hcontrCutPrefixes :
      ∀ {bound least : cd.Index},
        cd.RightCompatibleUpTo bound →
        cd.LeastInconsistentAtOrBelow bound least →
        cd.Inactive least →
          ∀ {leftCutK rightCutK cutI : Nat},
            (leftData :
              CutPrefixData cd.leftDerivation leftCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            (rightData :
              CutPrefixData cd.rightDerivation rightCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            (leftData.base.get leftData.idxJ) 🗲 (rightData.base.get rightData.idxJ))
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_right_incompatible_and_cutPrefix_center_contradiction_and_least_chain_branches
      cd hrightIncompatible hcontrCutPrefixes hleftNoContr hleftEdges
      hrightNoContr hrightEdges hinconsistent)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_right_incompatible_and_witnesses_before_cut_bases_and_least_chain_branches`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_right_incompatible_and_witnesses_before_cut_bases_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hwitnessBefore :
      ∀ {bound least : cd.Index},
        cd.RightCompatibleUpTo bound →
        cd.LeastInconsistentAtOrBelow bound least →
        cd.Inactive least →
          ∀ {leftCutK rightCutK cutI : Nat},
            (leftData :
              CutPrefixData cd.leftDerivation leftCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            (rightData :
              CutPrefixData cd.rightDerivation rightCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            ∀ {pref : CircuitDerivation Time} (hpref : pref.IsInitialPrefix cd),
              pref.DoublyActive (pref.prefixIndex hpref least) →
              (pref.leftTime (pref.prefixIndex hpref least)) 🗲 (pref.rightTime (pref.prefixIndex hpref least)) →
              InitialPrefix pref.leftDerivation leftData.baseDeriv ∧
                InitialPrefix pref.rightDerivation rightData.baseDeriv)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_right_incompatible_and_witnesses_before_cut_bases_and_least_chain_branches
      cd hrightIncompatible hwitnessBefore hleftNoContr hleftEdges
      hrightNoContr hrightEdges hinconsistent)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_least_chain_branches`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_least_chain_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_least_chain_branches cd hindex hleftNoContr
      hleftEdges hrightNoContr hrightEdges hinconsistent)

/--
Theorem 6.4.3(1); reindexes `cClosure_inconsistent_of_least_one_sided_branches`
so that the Corollary 5.6.4 active-index reduction `hindex` is stated with paper
indices (`paperIndex`). Both one-sided C-closure branches remain explicit
hypotheses.
-/
theorem cClosure_inconsistent_of_least_one_sided_branches_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftInactive :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  TimesInconsistent
                    (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)))
    (hrightInactive :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  TimesInconsistent
                    (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_one_sided_branches cd (by
      intro j hinconsistent
      rcases hindex j hinconsistent with
        ⟨l, hle, hcompat_l, hactiveInconsistent_l⟩
      exact
        ⟨l, Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hle),
          hcompat_l, hactiveInconsistent_l⟩)
      hleftInactive hrightInactive

/--
Theorem 6.4.3(1) via the chain of Cuts (Definition 6.3.1), reindexed so that the
Corollary 5.6.4 active-index reduction `hindex` uses paper indices. The per-edge
Cut-step bounds `hleftEdges`, `hrightEdges` remain explicit; chain activity is
supplied by leastness.
-/
theorem cClosure_inconsistent_of_least_chain_branches_indexed_from_edges
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_branches_from_edges cd (by
      intro j hinconsistent
      rcases hindex j hinconsistent with
        ⟨l, hle, hcompat_l, hactiveInconsistent_l⟩
      exact
        ⟨l, Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hle),
          hcompat_l, hactiveInconsistent_l⟩)
      hleftEdges hrightEdges

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_least_chain_branches_indexed_from_edges`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_least_chain_branches_indexed_from_edges
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_least_chain_branches_indexed_from_edges
      cd hindex hleftEdges hrightEdges hinconsistent)

/--
Theorem 6.4.3(1) via the chain of Cuts (Definition 6.3.1) with `ChainCutTimes`
packages, reindexed so that the Corollary 5.6.4 active-index reduction `hindex`
uses paper indices. The two chain-time packages remain explicit; chain activity
is supplied by leastness.
-/
theorem cClosure_inconsistent_of_least_chain_cutTimes_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftCutTimes :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∃ cutTimes : ChainCutTimes chain,
                      (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime least))
    (hrightCutTimes :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∃ cutTimes : ChainCutTimes chain,
                      (cd.leftTime least) 🗲 (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_cutTimes cd (by
      intro j hinconsistent
      rcases hindex j hinconsistent with
        ⟨l, hle, hcompat_l, hactiveInconsistent_l⟩
      exact
        ⟨l, Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hle),
          hcompat_l, hactiveInconsistent_l⟩)
      hleftCutTimes hrightCutTimes

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_least_chain_cutTimes_indexed`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_least_chain_cutTimes_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftCutTimes :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∃ cutTimes : ChainCutTimes chain,
                      (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime least))
    (hrightCutTimes :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∃ cutTimes : ChainCutTimes chain,
                      (cd.leftTime least) 🗲 (cutTimes.time ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_least_chain_cutTimes_indexed
      cd hindex hleftCutTimes hrightCutTimes hinconsistent)

/--
Theorem 6.4.3(1) using the canonical `ChainCutTimes.ofChainLinks`, reindexed so
that the Corollary 5.6.4 active-index reduction `hindex` uses paper indices. The
two first pre-Cut contradiction bridges `hleftContr`, `hrightContr` remain
explicit hypotheses.
-/
theorem cClosure_inconsistent_of_least_chain_links_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ((ChainCutTimes.ofChainLinks chain).time
                        ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime least))
    (hrightContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    (cd.leftTime least) 🗲 ((ChainCutTimes.ofChainLinks chain).time
                        ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_links cd (by
      intro j hinconsistent
      rcases hindex j hinconsistent with
        ⟨l, hle, hcompat_l, hactiveInconsistent_l⟩
      exact
        ⟨l, Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hle),
          hcompat_l, hactiveInconsistent_l⟩)
      hleftContr hrightContr

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_least_chain_links_indexed`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_least_chain_links_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ((ChainCutTimes.ofChainLinks chain).time
                        ⟨0, Nat.succ_pos chain.edgeCount⟩) 🗲 (cd.rightTime least))
    (hrightContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    (cd.leftTime least) 🗲 ((ChainCutTimes.ofChainLinks chain).time
                        ⟨0, Nat.succ_pos chain.edgeCount⟩)) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_least_chain_links_indexed
      cd hindex hleftContr hrightContr hinconsistent)

/--
Theorem 6.4.3(1) with both one-sided chain branches discharged internally
(canonical chain links), reindexed. The only remaining premise is the Corollary
5.6.4 active-index reduction `hindex`, stated with paper indices.
-/
theorem cClosure_inconsistent_of_least_chain_links_indexed_closed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_links_closed cd (by
      intro j hinconsistent
      rcases hindex j hinconsistent with
        ⟨l, hle, hcompat_l, hactiveInconsistent_l⟩
      exact
        ⟨l, Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hle),
          hcompat_l, hactiveInconsistent_l⟩)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_least_chain_links_indexed_closed`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_least_chain_links_indexed_closed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_least_chain_links_indexed_closed
      cd hindex hinconsistent)

/--
Theorem 6.4.3(1) with both one-sided chain branches discharged internally
(canonical chain links), whose only premise is the concrete Section 5
right-incompatible index result `hrightIncompatible` (in paper-index form). The
right-consistent case is discharged internally via
`index_result_of_right_incompatible_indexed`.
-/
theorem cClosure_inconsistent_of_right_incompatible_and_chain_links_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_links_indexed_closed cd
      (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_right_incompatible_indexed
        cd hrightIncompatible)

/--
Theorem 6.4.3(2), the contrapositive of
`cClosure_inconsistent_of_right_incompatible_and_chain_links_indexed`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_right_incompatible_and_chain_links_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_right_incompatible_and_chain_links_indexed
      cd hrightIncompatible hinconsistent)

section OrderedTechnicalChainLinks

variable {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
variable
    (hdirectSameCenterBranch :
      ∀ {center leftLower rightLower cutLower : cd.Index}
          {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        cd.circuit.left.1.paperIndex leftLower <
          cd.circuit.left.1.paperIndex rightLower →
        cd.circuit.left.1.paperIndex leftLower ≤
          cd.circuit.left.1.paperIndex cutLower →
        cd.circuit.left.1.paperIndex cutLower <
          cd.circuit.left.1.paperIndex rightLower →
        ContainsCut cd.leftDerivation
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower)
          (cd.circuit.left.1.paperIndex cutLower) →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l <
            cd.circuit.left.1.paperIndex center ∧
          cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hswapSameCenterBranch :
      ∀ {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        cd.circuit.left.1.paperIndex rightLower <
          cd.circuit.left.1.paperIndex leftLower →
          ∀ {cutLower : cd.swap.Index},
            cd.swap.circuit.left.1.paperIndex (cd.rightIndex rightLower) ≤
              cd.swap.circuit.left.1.paperIndex cutLower →
            cd.swap.circuit.left.1.paperIndex cutLower <
              cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower) →
            ContainsCut cd.swap.leftDerivation
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex center))
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower))
              (cd.swap.circuit.left.1.paperIndex cutLower) →
            ∃ l : cd.swap.Index,
              cd.swap.circuit.left.1.paperIndex l <
                cd.swap.circuit.left.1.paperIndex (cd.rightIndex center) ∧
                cd.swap.RightCompatibleUpTo l ∧
                  cd.swap.ActiveInconsistentIndex l)

include hdirectSameCenterBranch hswapSameCenterBranch

/--
Ordered-technical Section 5 route with canonical chain links. The
right-consistent branch and Section 6 chain-link obligations are discharged;
the remaining explicit obligations are the same-center branch
obligations.
-/
theorem cClosure_inconsistent_of_ordered_incompatible_branches_and_chain_links_indexed :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_links_indexed_closed cd
      (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_ordered_incompatible_branches_indexed
        cd hdirectSameCenterBranch hswapSameCenterBranch)

/--
Contrapositive of
`cClosure_inconsistent_of_ordered_incompatible_branches_and_chain_links_indexed`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_ordered_incompatible_branches_and_chain_links_indexed :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_ordered_incompatible_branches_and_chain_links_indexed
      cd hdirectSameCenterBranch hswapSameCenterBranch hinconsistent)

end OrderedTechnicalChainLinks

/--
This only
reindexes `cClosure_inconsistent_of_least_chain_branches`; the Section 5
active-index reduction and both least-chain no-final-contradiction and edge
obligations remain explicit hypotheses.
-/
theorem cClosure_inconsistent_of_least_chain_branches_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_branches cd (by
      intro j hinconsistent
      rcases hindex j hinconsistent with
        ⟨l, hle, hcompat_l, hactiveInconsistent_l⟩
      exact
        ⟨l, Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hle),
          hcompat_l, hactiveInconsistent_l⟩)
      hleftNoContr hleftEdges hrightNoContr hrightEdges

/--
Theorem 6.4.3(1) route indexed by paper indices. The right-consistent branch is
supplied by the Section 5 right-incompatible index result; the right-incompatible
branch and the Section 6 least-chain obligations remain explicit hypotheses.
-/
theorem cClosure_inconsistent_of_right_incompatible_and_least_chain_branches_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_branches_indexed cd
      (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_right_incompatible_indexed
        cd hrightIncompatible)
      hleftNoContr hleftEdges hrightNoContr hrightEdges

/--
Contrapositive indexed form of
`cClosure_inconsistent_of_right_incompatible_and_least_chain_branches_indexed`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_right_incompatible_and_least_chain_branches_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index, upper.val ≤ least.val →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    upper.val ≤ (cd.rightIndex least).val →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_right_incompatible_and_least_chain_branches_indexed
      cd hrightIncompatible hleftNoContr hleftEdges hrightNoContr hrightEdges
      hinconsistent)

/--
With
index-translated no-final-contradiction obligations. The Section 5 active-index
reduction, both least-chain edge obligations, and the indexed no-final
obligations remain explicit hypotheses.
-/
theorem cClosure_inconsistent_of_least_chain_branches_indexed_no_final_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index,
                    cd.circuit.left.1.paperIndex upper ≤
                      cd.circuit.left.1.paperIndex least →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    cd.circuit.right.1.paperIndex upper ≤
                      cd.circuit.right.1.paperIndex (cd.rightIndex least) →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact cClosure_inconsistent_of_least_one_sided_branches_indexed cd hindex
    (hleftInactive := by
      intro bound least hleast hcompat hactiveInconsistent hleftInactive hrightActive
      rcases ChainOfCuts.exists_of_inactive hleftInactive with ⟨chain⟩
      exact
        leftInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_no_final_contradiction_indexed
          cd hactiveInconsistent hleftInactive chain hcompat
          (hleftNoContr hleast hcompat hactiveInconsistent hleftInactive hrightActive)
          (hleftEdges hleast hcompat hactiveInconsistent hleftInactive hrightActive chain))
    (hrightInactive := by
      intro bound least hleast hcompat hactiveInconsistent hleftActive hrightInactive
      rcases ChainOfCuts.exists_of_inactive hrightInactive with ⟨chain⟩
      exact
        rightInactive_activeInconsistentIndex_cClosure_inconsistent_of_chain_no_final_contradiction_indexed
          cd hactiveInconsistent hrightInactive chain hcompat
          (hrightNoContr hleast hcompat hactiveInconsistent hleftActive hrightInactive)
          (hrightEdges hleast hcompat hactiveInconsistent hleftActive hrightInactive chain))

/--
Theorem 6.4.3(1) route stated with paper-index translations and using
index-translated no-final-contradiction obligations. The right-consistent branch
is supplied by the Section 5 right-incompatible index result; the
right-incompatible branch and the least-chain edge obligations remain explicit
hypotheses.
-/
theorem cClosure_inconsistent_of_right_incompatible_and_least_chain_branches_indexed_no_final_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index,
                    cd.circuit.left.1.paperIndex upper ≤
                      cd.circuit.left.1.paperIndex least →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    cd.circuit.right.1.paperIndex upper ≤
                      cd.circuit.right.1.paperIndex (cd.rightIndex least) →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_branches_indexed_no_final_contradiction cd
      (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_right_incompatible_indexed
        cd hrightIncompatible)
      hleftNoContr hleftEdges hrightNoContr hrightEdges

/--
Contrapositive form of
`cClosure_inconsistent_of_right_incompatible_and_least_chain_branches_indexed_no_final_contradiction`.
-/
theorem circuit_consistent_of_cClosure_consistent_and_right_incompatible_and_least_chain_branches_indexed_no_final_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hleftNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ upper : cd.Index,
                    cd.circuit.left.1.paperIndex upper ≤
                      cd.circuit.left.1.paperIndex least →
                    ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper))
    (hleftEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Inactive least →
                cd.rightDerivation.Active (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.leftDerivation least,
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.leftTime (chain.current l))) ≼ (cd.leftTime (chain.next l)))
    (hrightNoContr :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ upper : cd.circuit.right.1.Index,
                    cd.circuit.right.1.paperIndex upper ≤
                      cd.circuit.right.1.paperIndex (cd.rightIndex least) →
                      ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper)))
    (hrightEdges :
      ∀ {bound least : cd.Index},
        cd.LeastInconsistentAtOrBelow bound least →
          cd.RightCompatibleUpTo least →
            cd.ActiveInconsistentIndex least →
              cd.leftDerivation.Active least →
                cd.rightDerivation.Inactive (cd.rightIndex least) →
                  ∀ chain : ChainOfCuts cd.rightDerivation (cd.rightIndex least),
                    ∀ l : Fin chain.edgeCount,
                      ∃ source : Time,
                        (source # (cd.circuit.right.1.get (chain.current l))) ≼ (cd.circuit.right.1.get (chain.next l))) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hclosureConsistent hinconsistent
  exact hclosureConsistent
    (cClosure_inconsistent_of_right_incompatible_and_least_chain_branches_indexed_no_final_contradiction
      cd hrightIncompatible hleftNoContr hleftEdges hrightNoContr hrightEdges
      hinconsistent)

theorem timesConsistent_iff_pairwise_not_contradicts
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (times : Time → Prop) :
    TimesConsistent times ↔
      ∀ t t' : Time, times t → times t' → ¬ Contradicts t t' := by
  constructor
  · intro hconsistent t t' ht ht' hcontr
    exact hconsistent ⟨t, t', ht, ht', hcontr⟩
  · intro hpair hinconsistent
    rcases hinconsistent with ⟨t, t', ht, ht', hcontr⟩
    exact hpair t t' ht ht' hcontr

/-- Definition 6.4.2: inconsistent time sets remain inconsistent after enlarging the set. -/
theorem timesInconsistent_mono
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times larger : Time → Prop}
    (hsub : ∀ {t : Time}, times t → larger t)
    (hinconsistent : TimesInconsistent times) :
    TimesInconsistent larger := by
  rcases hinconsistent with ⟨t, t', ht, ht', hcontr⟩
  exact ⟨t, t', hsub ht, hsub ht', hcontr⟩

/-- Definition 6.4.2: a subset of a consistent time set is consistent. -/
theorem timesConsistent_mono
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {smaller larger : Time → Prop}
    (hsub : ∀ {t : Time}, smaller t → larger t)
    (hconsistent : TimesConsistent larger) :
    TimesConsistent smaller := by
  intro hinconsistent
  exact hconsistent (timesInconsistent_mono hsub hinconsistent)

theorem timesConsistent_member_consistentTime
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times : Time → Prop}
    (hconsistent : TimesConsistent times) {t : Time} (ht : times t) :
    ConsistentTime t := by
  exact timesConsistent_member_not_top hconsistent ht

/-- Notation 6.4.4, `t ≼ R`. -/
def UpperBoundedBy {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (bounds : Time → Prop) (t : Time) :
    Prop :=
  ∃ r : Time, bounds r ∧ le t r

/-- Notation 6.4.4: `t ≼ R` means `t` precedes some member of `R`. -/
theorem upperBoundedBy_iff_exists_le
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (bounds : Time → Prop) (t : Time) :
    UpperBoundedBy bounds t ↔ ∃ r : Time, bounds r ∧ le t r :=
  Iff.rfl

/-- Notation 6.4.4: `t ≼ R` has an explicit upper-bound witness. -/
theorem upperBoundedBy_has_bound
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {bounds : Time → Prop} {t : Time}
    (hupper : UpperBoundedBy bounds t) :
    ∃ r : Time, bounds r ∧ le t r := by
  exact hupper

/--
Notation 6.4.4: an upper-bound witness is controlled by the same controller
as the bounded time, because `t ≼ r` includes the located-order controller
equality.
-/
theorem upperBoundedBy_has_bound_with_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {bounds : Time → Prop} {t : Time}
    (hupper : UpperBoundedBy bounds t) :
    ∃ r : Time, bounds r ∧ controller t = controller r ∧ le t r := by
  rcases hupper with ⟨r, hr, hle⟩
  exact ⟨r, hr, hle.1, hle⟩

theorem upperBoundedBy_of_mem
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {bounds : Time → Prop} {t : Time}
    (ht : bounds t) :
    UpperBoundedBy bounds t := by
  exact ⟨t, ht, le_refl t⟩

theorem upperBoundedBy_of_le
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {bounds : Time → Prop} {t s : Time}
    (hle : le t s) (hupper : UpperBoundedBy bounds s) :
    UpperBoundedBy bounds t := by
  rcases hupper with ⟨r, hr, hsr⟩
  exact ⟨r, hr, le_trans hle hsr⟩

/--
Notation 6.4.4 consequence: if an attestation output is upper-bounded, then
its attesting input is also upper-bounded by expansiveness.
-/
theorem upperBoundedBy_left_of_attest_upperBounded
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {bounds : Time → Prop} {r q : Time}
    (hupper : UpperBoundedBy bounds (attest r q)) :
    UpperBoundedBy bounds r :=
  upperBoundedBy_of_le (le_attest r q) hupper

theorem upperBoundedBy_right_of_attest_upperBounded_same_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {bounds : Time → Prop} {r q : Time}
    (hctrl : controller r = controller q)
    (hupper : UpperBoundedBy bounds (attest r q)) :
    UpperBoundedBy bounds q := by
  rcases hupper with ⟨b, hb, hle⟩
  exact ⟨b, hb, le_trans (le_right_attest_of_same_controller hctrl) hle⟩

/-- Notation 6.4.4: enlarging the bounding set preserves `t ≼ R`. -/
theorem upperBoundedBy_mono_bounds
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {bounds larger : Time → Prop} {t : Time}
    (hsub : ∀ {r : Time}, bounds r → larger r)
    (hupper : UpperBoundedBy bounds t) :
    UpperBoundedBy larger t := by
  rcases hupper with ⟨r, hr, hle⟩
  exact ⟨r, hsub hr, hle⟩

/--
Auxiliary consequence: a time upper-bounded by a consistent
set of bounds is itself consistent.
-/
theorem upperBoundedBy_consistentTime_of_bounds_consistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {bounds : Time → Prop} {t : Time}
    (hconsistent : TimesConsistent bounds)
    (hupper : UpperBoundedBy bounds t) :
    ConsistentTime t := by
  rcases hupper with ⟨r, hr, hle⟩
  have hr_consistent : ConsistentTime r :=
    timesConsistent_member_consistentTime hconsistent hr
  intro ht_top
  have ht_contradicts : Contradicts t t :=
    (contradicts_self_iff_not_consistentTime t).mpr (by
      intro ht_consistent
      exact ht_consistent ht_top)
  have htr_contradicts : Contradicts t r :=
    contradicts_of_le_right hle ht_contradicts
  exact not_contradicts_right_of_le_of_consistentTime hle hr_consistent htr_contradicts

/-- Notation 6.4.4, `T ≼ R`. -/
def SetUpperBoundedBy {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (times bounds : Time → Prop) : Prop :=
  ∀ t : Time, times t → UpperBoundedBy bounds t

/-- Notation 6.4.4: `T ≼ R` means every member of `T` is upper-bounded by `R`. -/
theorem setUpperBoundedBy_iff_forall_upperBounded
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (times bounds : Time → Prop) :
    SetUpperBoundedBy times bounds ↔
      ∀ t : Time, times t → UpperBoundedBy bounds t :=
  Iff.rfl

/-- Notation 6.4.4: each member of an upper-bounded set is upper-bounded. -/
theorem setUpperBoundedBy_member
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times bounds : Time → Prop}
    (hupper : SetUpperBoundedBy times bounds) {t : Time} (ht : times t) :
    UpperBoundedBy bounds t := by
  exact hupper t ht

/--
Notation 6.4.4: a member of a set upper-bounded by `R` has a bound in `R`
with the same controller.
-/
theorem setUpperBoundedBy_member_has_bound_with_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times bounds : Time → Prop}
    (hupper : SetUpperBoundedBy times bounds) {t : Time} (ht : times t) :
    ∃ r : Time, bounds r ∧ controller t = controller r ∧ le t r := by
  exact upperBoundedBy_has_bound_with_controller (hupper t ht)

theorem setUpperBoundedBy_of_subset
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times bounds : Time → Prop}
    (hsub : ∀ {t : Time}, times t → bounds t) :
    SetUpperBoundedBy times bounds := by
  intro t ht
  exact upperBoundedBy_of_mem (hsub ht)

/-- Notation 6.4.4: enlarging the bounding set preserves `T ≼ R`. -/
theorem setUpperBoundedBy_mono_bounds
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times bounds larger : Time → Prop}
    (hsub : ∀ {r : Time}, bounds r → larger r)
    (hupper : SetUpperBoundedBy times bounds) :
    SetUpperBoundedBy times larger := by
  intro t ht
  exact upperBoundedBy_mono_bounds hsub (hupper t ht)

/-- Notation 6.4.4: a subset of an upper-bounded set is upper-bounded. -/
theorem setUpperBoundedBy_mono_times
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {smaller larger bounds : Time → Prop}
    (hsub : ∀ {t : Time}, smaller t → larger t)
    (hupper : SetUpperBoundedBy larger bounds) :
    SetUpperBoundedBy smaller bounds := by
  intro t ht
  exact hupper t (hsub ht)

/-- Definition 6.4.5. -/
def ConsistentCAttestationClosedUpperBounds {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (times bounds : Time → Prop) : Prop :=
  TimesConsistent bounds ∧
    SetUpperBoundedBy times bounds ∧
      ∀ {r' q' : Time}, UpperBoundedBy bounds (attest r' q') →
        controllers (controller r') → controllers (controller q') →
          UpperBoundedBy bounds q'

/-- Definition 6.4.5: the bundled upper-bound condition is exactly its three clauses. -/
theorem cAttestationClosedUpperBounds_iff
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (controllers : Ctrl → Prop)
    (times bounds : Time → Prop) :
    ConsistentCAttestationClosedUpperBounds controllers times bounds ↔
      TimesConsistent bounds ∧
        SetUpperBoundedBy times bounds ∧
          ∀ {r' q' : Time}, UpperBoundedBy bounds (attest r' q') →
            controllers (controller r') → controllers (controller q') →
              UpperBoundedBy bounds q' :=
  Iff.rfl

/-- Definition 6.4.5: the three clauses construct the bundled upper-bound condition. -/
theorem cAttestationClosedUpperBounds_of_clauses
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hconsistent : TimesConsistent bounds)
    (hupper : SetUpperBoundedBy times bounds)
    (hattest :
      ∀ {r' q' : Time}, UpperBoundedBy bounds (attest r' q') →
        controllers (controller r') → controllers (controller q') →
          UpperBoundedBy bounds q') :
    ConsistentCAttestationClosedUpperBounds controllers times bounds := by
  exact ⟨hconsistent, hupper, hattest⟩

theorem cAttestationClosedUpperBounds_bounds_consistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds) :
    TimesConsistent bounds := by
  exact hbounds.1

theorem cAttestationClosedUpperBounds_setUpperBoundedBy
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds) :
    SetUpperBoundedBy times bounds := by
  exact hbounds.2.1

/-- Definition 6.4.5: each original time has an upper bound in the bundled bounds. -/
theorem cAttestationClosedUpperBounds_time_upperBoundedBy
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds)
    {t : Time} (ht : times t) :
    UpperBoundedBy bounds t := by
  exact setUpperBoundedBy_member
    (cAttestationClosedUpperBounds_setUpperBoundedBy hbounds) ht

/--
Definition 6.4.5, clause 2: each original time has an upper-bound witness with
the same controller.
-/
theorem cAttestationClosedUpperBounds_time_has_bound_with_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds)
    {t : Time} (ht : times t) :
    ∃ r : Time, bounds r ∧ controller t = controller r ∧ le t r := by
  exact setUpperBoundedBy_member_has_bound_with_controller
    (cAttestationClosedUpperBounds_setUpperBoundedBy hbounds) ht

theorem cAttestationClosedUpperBounds_attest_closed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds)
    {r' q' : Time} :
    UpperBoundedBy bounds (attest r' q') →
      controllers (controller r') → controllers (controller q') →
        UpperBoundedBy bounds q' := by
  exact hbounds.2.2

theorem cAttestationClosedUpperBounds_bound_consistentTime
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds)
    {r : Time} (hr : bounds r) :
    ConsistentTime r := by
  exact timesConsistent_member_consistentTime
    (cAttestationClosedUpperBounds_bounds_consistent hbounds) hr

/--
Definition 6.4.5 consequence: every time upper-bounded by the bundled bounds is
consistent.
-/
theorem cAttestationClosedUpperBounds_upperBounded_consistentTime
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds)
    {t : Time} (hupper : UpperBoundedBy bounds t) :
    ConsistentTime t := by
  exact upperBoundedBy_consistentTime_of_bounds_consistent
    (cAttestationClosedUpperBounds_bounds_consistent hbounds) hupper

/-- Definition 6.4.5 consequence: every member of the original time set is consistent. -/
theorem cAttestationClosedUpperBounds_time_consistentTime
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds)
    {t : Time} (ht : times t) :
    ConsistentTime t := by
  exact cAttestationClosedUpperBounds_upperBounded_consistentTime hbounds
    ((cAttestationClosedUpperBounds_setUpperBoundedBy hbounds) t ht)

/-- Definition 6.4.8. -/
def MostRecentAttested {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (bounds : Time → Prop) (p : Ctrl) (s : Time) : Prop :=
  controllers p ∧
    (∃ r : Time, bounds r ∧ controller r = p ∧ UpperBoundedBy bounds (attest r s)) ∧
      ∀ r' s' : Time,
        controller r' = p ∧ controller s' = controller s ∧
          UpperBoundedBy bounds (attest r' s') →
            le s' s

/-- Definition 6.4.8: `MostRecentAttested` is exactly the displayed definition. -/
theorem mostRecentAttested_iff
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (controllers : Ctrl → Prop)
    (bounds : Time → Prop) (p : Ctrl) (s : Time) :
    MostRecentAttested controllers bounds p s ↔
      controllers p ∧
        (∃ r : Time, bounds r ∧ controller r = p ∧
          UpperBoundedBy bounds (attest r s)) ∧
          ∀ r' s' : Time,
            controller r' = p ∧ controller s' = controller s ∧
              UpperBoundedBy bounds (attest r' s') →
                le s' s :=
  Iff.rfl

/-- Definition 6.4.8: the displayed clauses construct `MostRecentAttested`. -/
theorem mostRecentAttested_of_clauses
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {bounds : Time → Prop} {p : Ctrl} {s : Time}
    (hp : controllers p)
    (hwitness :
      ∃ r : Time, bounds r ∧ controller r = p ∧
        UpperBoundedBy bounds (attest r s))
    (hmax :
      ∀ r' s' : Time,
        controller r' = p ∧ controller s' = controller s ∧
          UpperBoundedBy bounds (attest r' s') →
            le s' s) :
    MostRecentAttested controllers bounds p s := by
  exact ⟨hp, hwitness, hmax⟩

theorem mostRecentAttested_controller_mem
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {bounds : Time → Prop} {p : Ctrl} {s : Time}
    (hmr : MostRecentAttested controllers bounds p s) :
    controllers p := by
  exact hmr.1

theorem mostRecentAttested_has_witness
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {bounds : Time → Prop} {p : Ctrl} {s : Time}
    (hmr : MostRecentAttested controllers bounds p s) :
    ∃ r : Time, bounds r ∧ controller r = p ∧
      UpperBoundedBy bounds (attest r s) := by
  exact hmr.2.1

/-- Definition 6.4.8: a most-recent attestation has a bound controlled by `p`. -/
theorem mostRecentAttested_has_bound_at_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {bounds : Time → Prop} {p : Ctrl} {s : Time}
    (hmr : MostRecentAttested controllers bounds p s) :
    ∃ r : Time, bounds r ∧ controller r = p := by
  rcases mostRecentAttested_has_witness hmr with ⟨r, hr, hctrl, _hupper⟩
  exact ⟨r, hr, hctrl⟩

/--
Definition 6.4.8 consequence: if the bounding set is consistent, then the
controller witness supplied by `MostRecentAttested` can be chosen consistent.
-/
theorem mostRecentAttested_has_consistent_bound_at_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {bounds : Time → Prop} {p : Ctrl} {s : Time}
    (hconsistent : TimesConsistent bounds)
    (hmr : MostRecentAttested controllers bounds p s) :
    ∃ r : Time, bounds r ∧ controller r = p ∧ ConsistentTime r := by
  rcases mostRecentAttested_has_bound_at_controller hmr with ⟨r, hr, hctrl⟩
  exact ⟨r, hr, hctrl, timesConsistent_member_consistentTime hconsistent hr⟩

theorem mostRecentAttested_maximal
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {bounds : Time → Prop} {p : Ctrl} {s r' s' : Time}
    (hmr : MostRecentAttested controllers bounds p s)
    (hctrlr : controller r' = p)
    (hctrls : controller s' = controller s)
    (hupper : UpperBoundedBy bounds (attest r' s')) :
    le s' s := by
  exact hmr.2.2 r' s' ⟨hctrlr, hctrls, hupper⟩

/--
Example 6.4.9: the current Definition 6.4.8 maximality clause
applies directly to any attestation input whose attestation is upper-bounded
by the reported set, so `q' ≼ t_{pp'}` follows without a separate membership
premise for `r'`.
-/
theorem mostRecentAttested_target_le
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {bounds : Time → Prop} {r' q' s : Time}
    (hmr : MostRecentAttested controllers bounds (controller r') s)
    (hsctrl : controller s = controller q')
    (hupper : UpperBoundedBy bounds (attest r' q')) :
    le q' s := by
  exact mostRecentAttested_maximal hmr rfl hsctrl.symm hupper

theorem mostRecentAttested_upperBounded_of_member_at_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {bounds : Time → Prop} {p : Ctrl} {r' q' s : Time}
    (hmr : MostRecentAttested controllers bounds p s)
    (hctrlr : controller r' = p)
    (hsctrl : controller s = controller q')
    (hsupper : UpperBoundedBy bounds s)
    (hupper : UpperBoundedBy bounds (attest r' q')) :
    UpperBoundedBy bounds q' := by
  have hle : le q' s :=
    mostRecentAttested_maximal hmr hctrlr hsctrl.symm hupper
  exact upperBoundedBy_of_le hle hsupper

theorem cAttestationClosedUpperBounds_mostRecentAttested_upperBounded
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop} {p : Ctrl} {s : Time}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds)
    (hmr : MostRecentAttested controllers bounds p s)
    (hctrls : controllers (controller s)) :
    UpperBoundedBy bounds s := by
  rcases mostRecentAttested_has_witness hmr with ⟨r, _hr, hctrlr, hupper⟩
  have hctrlr_mem : controllers (controller r) := by
    rw [hctrlr]
    exact mostRecentAttested_controller_mem hmr
  exact cAttestationClosedUpperBounds_attest_closed hbounds hupper hctrlr_mem hctrls

/--
Example 6.4.9: once the reported most-recent time is
upper-bounded by the algorithm output set, maximality gives the target time
`q'` an upper bound too.
-/
theorem mostRecentAttested_upperBounded
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {bounds : Time → Prop} {r' q' s : Time}
    (hmr : MostRecentAttested controllers bounds (controller r') s)
    (hsctrl : controller s = controller q')
    (hsupper : UpperBoundedBy bounds s)
    (hupper : UpperBoundedBy bounds (attest r' q')) :
    UpperBoundedBy bounds q' := by
  have hle : le q' s :=
    mostRecentAttested_target_le hmr hsctrl hupper
  exact upperBoundedBy_of_le hle hsupper

/-- Example 6.4.9, algorithm output `R = {t_p | p ∈ C}`. -/
def ReportedControllerTimes {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (latest : Ctrl → Time) (t : Time) : Prop :=
  ∃ p : Ctrl, controllers p ∧ t = latest p

/-- Example 6.4.9: reported output times are exactly the selected latest times. -/
theorem reportedControllerTimes_iff_exists_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (controllers : Ctrl → Prop)
    (latest : Ctrl → Time) (t : Time) :
    ReportedControllerTimes controllers latest t ↔
      ∃ p : Ctrl, controllers p ∧ t = latest p := by
  exact Iff.rfl

theorem reportedControllerTimes_has_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {t : Time}
    (ht : ReportedControllerTimes controllers latest t) :
    ∃ p : Ctrl, controllers p ∧ t = latest p := by
  exact ht

theorem reportedControllerTimes_latest_mem
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {p : Ctrl}
    (hp : controllers p) :
    ReportedControllerTimes controllers latest (latest p) := by
  exact ⟨p, hp, rfl⟩

/-- Definition 6.4.1: reported output times are controlled by active controllers. -/
theorem reportedControllerTimes_controller_mem
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, controllers p → controller (latest p) = p)
    {r : Time} (hr : ReportedControllerTimes controllers latest r) :
    controllers (controller r) := by
  rcases hr with ⟨p, hp, rfl⟩
  simpa [hlatest_ctrl hp] using hp

theorem reportedControllerTimes_eq_latest_of_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, controllers p → controller (latest p) = p)
    {p : Ctrl} {r : Time}
    (hr : ReportedControllerTimes controllers latest r)
    (hctrl : controller r = p) :
    r = latest p := by
  rcases hr with ⟨q, hq, rfl⟩
  have hqp : q = p := (hlatest_ctrl hq).symm.trans hctrl
  cases hqp
  rfl

/-- Definition 6.4.1 and Definition 6.4.2: the non-failing algorithm outputs consistent times. -/
theorem reportedControllerTimes_member_consistentTime
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time}
    (hconsistent : ∀ {p : Ctrl}, controllers p → ConsistentTime (latest p))
    {r : Time} (hr : ReportedControllerTimes controllers latest r) :
    ConsistentTime r := by
  rcases hr with ⟨p, hp, rfl⟩
  exact hconsistent hp

/--
Definition 6.4.1 and Notation 6.4.4: if every seed time is below its controller's
reported latest time, the reported set upper-bounds the seed set.
-/
theorem reportedControllerTimes_setUpperBoundedBy_of_latest_proofs
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times : Time → Prop} {latest : Ctrl → Time}
    (hctrl : ∀ {t : Time}, times t → controllers (controller t))
    (hle : ∀ {t : Time}, times t → le t (latest (controller t))) :
    SetUpperBoundedBy times (ReportedControllerTimes controllers latest) := by
  intro t ht
  exact ⟨latest (controller t),
    reportedControllerTimes_latest_mem (hctrl ht), hle ht⟩

/--
Definition 6.4.1 and Notation 6.4.4, specialized to the active circuit controllers
and active circuit times used by the algorithm.
-/
theorem reportedControllerTimes_setUpperBoundedBy_activeTimeCircuit
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    (hle :
      ∀ {t : Time}, ActiveTimeCircuit cd t →
        t ≼ (latest (controller t))) :
    SetUpperBoundedBy (ActiveTimeCircuit cd)
      (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) := by
  exact reportedControllerTimes_setUpperBoundedBy_of_latest_proofs
    (fun ht => activeTimeCircuit_controller_mem cd ht) hle

theorem reportedControllerTimes_upperBoundedBy_of_le_latest
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {p : Ctrl} {s : Time}
    (hp : controllers p) (hle : le s (latest p)) :
    UpperBoundedBy (ReportedControllerTimes controllers latest) s := by
  exact ⟨latest p, reportedControllerTimes_latest_mem hp, hle⟩

/--
Remark 6.4.10 concrete proof-obligation remark, concrete theorem:
for the inductive construction of Section 3.4, a reported node whose `p'` view slot
contains `t_{pp'}` satisfies the cross-controller `MostRecentAttested`
maximality and witness clauses for that stored time. This is concrete support
for the paper's practical tuple check, not a proof of the general reported-controller
algorithmic closure claim.
-/
theorem concreteNode_reportedControllerTimes_mostRecentAttested_cross
    (D : LocalStateData.{u}) {controllers : D.Ctrl → Prop}
    {latest : D.Ctrl → LocalStateData.Time D}
    {p p' : D.Ctrl} (hp : controllers p) (hp_ne : p' ≠ p)
    {x : D.X} {hx : D.semilattice.Consistent x}
    {views : (k : D.Ctrl) → k ≠ p → LocalStateData.CTime D k}
    (hlatest_eq :
      latest p = LocalStateData.CTime.toTime (LocalStateData.CTime.node p x hx views))
    (hlatest_ctrl :
      ∀ {q : D.Ctrl}, controllers q → LocalStateData.Time.controller (latest q) = q)
    (hmaxConcrete :
      ∀ r' s' : LocalStateData.Time D,
        (LocalStateData.locatedSemilattice D).controller r' = p ∧
          (LocalStateData.locatedSemilattice D).controller s' =
            (LocalStateData.locatedSemilattice D).controller
              (LocalStateData.CTime.toTime (views p' hp_ne)) ∧
          UpperBoundedBy
            (ReportedControllerTimes controllers latest)
            ((LocalStateData.locatedSemilattice D).attest r' s') →
          (LocalStateData.locatedSemilattice D).le s'
            (LocalStateData.CTime.toTime (views p' hp_ne))) :
    MostRecentAttested controllers
      (ReportedControllerTimes controllers latest) p
      (LocalStateData.CTime.toTime (views p' hp_ne)) := by
  refine mostRecentAttested_of_clauses hp ?_ ?_
  · refine ⟨latest p, reportedControllerTimes_latest_mem hp, hlatest_ctrl hp, ?_⟩
    refine ⟨latest p, reportedControllerTimes_latest_mem hp, ?_⟩
    rw [hlatest_eq]
    exact LocalStateData.locatedSemilattice_cross_node_attest_stored_view_le_self
      (D := D) (j := p) (i := p') hp_ne (x := x) (hx := hx) (views := views)
  · intro r' s' hmax
    exact hmaxConcrete r' s' hmax

/--
Reported-controller: with the
reported most-recent property and the requested proof that the reported
attested time lies below the target controller's latest time both explicit, the
reported most-recent time is itself upper-bounded by the algorithm's output
set. This is not the concrete tuple-check proof promised by the paper remark.
-/
theorem reportedControllerTimes_reported_mostRecent_upperBounded
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {p p' : Ctrl} {s : Time}
    (hp' : controllers p')
    (hmr :
      MostRecentAttested controllers
        (ReportedControllerTimes controllers latest) p s)
    (hsctrl : controller s = p')
    (hle : le s (latest p')) :
    MostRecentAttested controllers
        (ReportedControllerTimes controllers latest) p s ∧
      controller s = p' ∧
        UpperBoundedBy (ReportedControllerTimes controllers latest) s := by
  exact ⟨hmr, hsctrl, reportedControllerTimes_upperBoundedBy_of_le_latest hp' hle⟩

/--
Example 6.4.9: the requested proof `t'_{pp'} ≼ t_{p'}` makes the
reported attested time upper-bounded by the active-controller output set.
-/
theorem reportedControllerTimes_attested_upperBounded_activeCtrlCircuit
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    {p p' : Ctrl}
    (_hp : ActiveCtrlCircuit cd p) (hp' : ActiveCtrlCircuit cd p')
    (hle : (attested p p') ≼ (latest p')) :
    UpperBoundedBy
      (ReportedControllerTimes (ActiveCtrlCircuit cd) latest)
      (attested p p') := by
  exact reportedControllerTimes_upperBoundedBy_of_le_latest hp' hle

/--
Definition 6.4.1 and Definition 6.4.2: controlled reported times that are all non-top form
a consistent output set.
-/
theorem reportedControllerTimes_timesConsistent_of_latest_consistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, controllers p → controller (latest p) = p)
    (hconsistent : ∀ {p : Ctrl}, controllers p → ConsistentTime (latest p)) :
    TimesConsistent (ReportedControllerTimes controllers latest) := by
  intro hinconsistent
  rcases hinconsistent with ⟨t, t', ht, ht', hcontr⟩
  rcases ht with ⟨p, hp, rfl⟩
  rcases ht' with ⟨p', hp', rfl⟩
  have hp_eq : p = p' := by
    have hctrl := hcontr.1
    rw [hlatest_ctrl hp, hlatest_ctrl hp'] at hctrl
    exact hctrl
  subst p'
  exact not_contradicts_self_of_consistentTime (hconsistent hp) hcontr

/--
Definition 6.4.1 and Definition 6.4.2, specialized to the active controllers of a circuit:
non-failing reported latest times form a consistent reported set.
-/
theorem reportedControllerTimes_timesConsistent_activeCtrlCircuit
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        controller (latest p) = p)
    (hconsistent :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        ConsistentTime (latest p)) :
    TimesConsistent
      (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) := by
  exact reportedControllerTimes_timesConsistent_of_latest_consistent
    hlatest_ctrl hconsistent

/--
Example 6.4.9, algorithmic example, proved components: when the reported
latest times are controlled by active controllers, are consistent, and bound
each active time, the output set is consistent and upper-bounds the active
times. The attestation-closure clause is supplied by the most-recent certificate wrappers below.
-/
theorem reportedControllerTimes_consistent_and_upperBounded_activeCircuit
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        controller (latest p) = p)
    (hconsistent :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        ConsistentTime (latest p))
    (hle :
      ∀ {t : Time}, ActiveTimeCircuit cd t →
        t ≼ (latest (controller t))) :
    TimesConsistent
        (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) ∧
      SetUpperBoundedBy (ActiveTimeCircuit cd)
        (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) := by
  exact
    ⟨reportedControllerTimes_timesConsistent_activeCtrlCircuit cd hlatest_ctrl hconsistent,
      reportedControllerTimes_setUpperBoundedBy_activeTimeCircuit cd hle⟩

theorem reportedControllerTimes_mostRecent_reports_upperBounded
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {attested : Ctrl → Ctrl → Time}
    (hmost :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        MostRecentAttested controllers
          (ReportedControllerTimes controllers latest) p (attested p p'))
    (hctrl :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        controller (attested p p') = p')
    (hle :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        le (attested p p') (latest p')) :
    ∀ {p p' : Ctrl}, controllers p → controllers p' →
      ∃ s : Time,
        MostRecentAttested controllers
            (ReportedControllerTimes controllers latest) p s ∧
          controller s = p' ∧
            UpperBoundedBy (ReportedControllerTimes controllers latest) s := by
  intro p p' hp hp'
  exact ⟨attested p p',
    reportedControllerTimes_reported_mostRecent_upperBounded hp'
      (hmost hp hp') (hctrl hp hp') (hle hp hp')⟩

/--
Paper-facing certificate interface for the most-recent algorithm: a reported
cross-controller attested time is usable by the closure proof only when its
`MostRecentAttested` witness, target controller, and reported-output
upper-bound certificate are all explicit. This is the relational certificate
shape that the paper text supports; it is not a certificate-free
functional computation of most-recent times.
-/
def ReportedMostRecentCertificate {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (latest : Ctrl → Time)
    (attested : Ctrl → Ctrl → Time) : Prop :=
  ∀ {p p' : Ctrl}, controllers p → controllers p' →
    MostRecentAttested controllers
        (ReportedControllerTimes controllers latest) p (attested p p') ∧
      controller (attested p p') = p' ∧
        UpperBoundedBy (ReportedControllerTimes controllers latest)
          (attested p p')

theorem reportedMostRecentCertificate_mostRecentAttested
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {attested : Ctrl → Ctrl → Time}
    (hcert : ReportedMostRecentCertificate controllers latest attested)
    {p p' : Ctrl} (hp : controllers p) (hp' : controllers p') :
    MostRecentAttested controllers
      (ReportedControllerTimes controllers latest) p (attested p p') := by
  exact (hcert hp hp').1

theorem reportedMostRecentCertificate_controller
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {attested : Ctrl → Ctrl → Time}
    (hcert : ReportedMostRecentCertificate controllers latest attested)
    {p p' : Ctrl} (hp : controllers p) (hp' : controllers p') :
    controller (attested p p') = p' := by
  exact (hcert hp hp').2.1

theorem reportedMostRecentCertificate_upperBounded
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {attested : Ctrl → Ctrl → Time}
    (hcert : ReportedMostRecentCertificate controllers latest attested)
    {p p' : Ctrl} (hp : controllers p) (hp' : controllers p') :
    UpperBoundedBy (ReportedControllerTimes controllers latest)
      (attested p p') := by
  exact (hcert hp hp').2.2

theorem reportedMostRecentCertificate_of_reported_mostRecent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {attested : Ctrl → Ctrl → Time}
    (hmost :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        MostRecentAttested controllers
          (ReportedControllerTimes controllers latest) p (attested p p'))
    (hctrl :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        controller (attested p p') = p')
    (hle :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        le (attested p p') (latest p')) :
    ReportedMostRecentCertificate controllers latest attested := by
  intro p p' hp hp'
  exact reportedControllerTimes_reported_mostRecent_upperBounded hp'
    (hmost hp hp') (hctrl hp hp') (hle hp hp')

theorem reportedControllerTimes_mostRecent_reports_upperBounded_of_certificate
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {latest : Ctrl → Time} {attested : Ctrl → Ctrl → Time}
    (hcert : ReportedMostRecentCertificate controllers latest attested) :
    ∀ {p p' : Ctrl}, controllers p → controllers p' →
      ∃ s : Time,
        MostRecentAttested controllers
            (ReportedControllerTimes controllers latest) p s ∧
          controller s = p' ∧
            UpperBoundedBy (ReportedControllerTimes controllers latest) s := by
  intro p p' hp hp'
  exact ⟨attested p p', hcert hp hp'⟩

/--
Example 6.4.9: if each active controller reports a
most-recent attested time for each target controller and that reported time is
itself upper-bounded by the output set, then the output set is
`C`-attestation-closed.
-/
theorem cAttestationClosedUpperBounds_of_mostRecentAttested
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hconsistent : TimesConsistent bounds)
    (hupper : SetUpperBoundedBy times bounds)
    (hreported :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        ∃ s : Time,
          MostRecentAttested controllers bounds p s ∧
            controller s = p' ∧ UpperBoundedBy bounds s) :
    ConsistentCAttestationClosedUpperBounds controllers times bounds := by
  constructor
  · exact hconsistent
  · constructor
    · exact hupper
    · intro r' q' hattest hctrl_r hctrl_q
      rcases hreported hctrl_r hctrl_q with ⟨s, hmr, hsctrl, hsupper⟩
      exact mostRecentAttested_upperBounded hmr hsctrl hsupper hattest

theorem reportedControllerTimes_cAttestationClosedUpperBounds_of_mostRecentAttested
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times : Time → Prop} {latest : Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, controllers p → controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, controllers p → ConsistentTime (latest p))
    (htimes_ctrl : ∀ {t : Time}, times t → controllers (controller t))
    (htimes_le : ∀ {t : Time}, times t → le t (latest (controller t)))
    (hreported :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        ∃ s : Time,
          MostRecentAttested controllers (ReportedControllerTimes controllers latest) p s ∧
            controller s = p' ∧
              UpperBoundedBy (ReportedControllerTimes controllers latest) s) :
    ConsistentCAttestationClosedUpperBounds controllers times
      (ReportedControllerTimes controllers latest) := by
  exact cAttestationClosedUpperBounds_of_mostRecentAttested
    (reportedControllerTimes_timesConsistent_of_latest_consistent hlatest_ctrl
      hlatest_consistent)
    (reportedControllerTimes_setUpperBoundedBy_of_latest_proofs htimes_ctrl htimes_le)
    hreported

theorem reportedControllerTimes_cAttestationClosedUpperBounds_of_certificate
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times : Time → Prop} {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, controllers p → controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, controllers p → ConsistentTime (latest p))
    (htimes_ctrl : ∀ {t : Time}, times t → controllers (controller t))
    (htimes_le : ∀ {t : Time}, times t → le t (latest (controller t)))
    (hcert : ReportedMostRecentCertificate controllers latest attested) :
    ConsistentCAttestationClosedUpperBounds controllers times
      (ReportedControllerTimes controllers latest) := by
  exact reportedControllerTimes_cAttestationClosedUpperBounds_of_mostRecentAttested
    hlatest_ctrl hlatest_consistent htimes_ctrl htimes_le
    (reportedControllerTimes_mostRecent_reports_upperBounded_of_certificate hcert)

theorem reportedControllerTimes_cAttestationClosedUpperBounds_of_reported_mostRecent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times : Time → Prop} {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, controllers p → controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, controllers p → ConsistentTime (latest p))
    (htimes_ctrl : ∀ {t : Time}, times t → controllers (controller t))
    (htimes_le : ∀ {t : Time}, times t → le t (latest (controller t)))
    (hmost :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        MostRecentAttested controllers
          (ReportedControllerTimes controllers latest) p (attested p p'))
    (hattested_ctrl :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        controller (attested p p') = p')
    (hattested_le_latest :
      ∀ {p p' : Ctrl}, controllers p → controllers p' →
        le (attested p p') (latest p')) :
    ConsistentCAttestationClosedUpperBounds controllers times
      (ReportedControllerTimes controllers latest) := by
  exact reportedControllerTimes_cAttestationClosedUpperBounds_of_certificate
    hlatest_ctrl hlatest_consistent htimes_ctrl htimes_le
    (reportedMostRecentCertificate_of_reported_mostRecent hmost
      hattested_ctrl hattested_le_latest)

/--
Induction step in Corollary 6.4.6: a
`C`-attestation-closed upper-bound set for `T` upper-bounds every member of the
`C`-closure of `T`.
-/
theorem cClosure_upperBoundedBy_of_upperBounds
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (times bounds : Time → Prop)
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds)
    {t : Time} (hclosure : CClosure controllers times t) :
    UpperBoundedBy bounds t := by
  rcases hbounds with ⟨_hconsistent, hupper, hattest⟩
  induction hclosure with
  | init hT _hC =>
      exact hupper _ hT
  | attest hAttested hC ih =>
      rename_i r s
      have hCr : controllers (controller r) := by
        have hCattested := CClosure.controller_mem hAttested
        simpa [controller_preserving r s] using hCattested
      exact hattest ih hCr hC

theorem cClosure_setUpperBoundedBy_of_upperBounds
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (times bounds : Time → Prop)
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds) :
    SetUpperBoundedBy (CClosure controllers times) bounds := by
  intro t hclosure
  exact cClosure_upperBoundedBy_of_upperBounds controllers times bounds hbounds hclosure

/-- First-clause component of Corollary 6.4.6. -/
theorem upper_bound_consistent_for_cClosure
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (times bounds : Time → Prop) :
    ConsistentCAttestationClosedUpperBounds controllers times bounds →
    ConsistentCAttestationClosedUpperBounds controllers
        (CClosure controllers times) bounds := by
  intro hbounds
  rcases hbounds with ⟨hconsistent, hupper, hattest⟩
  constructor
  · exact hconsistent
  · constructor
    · intro _t hclosure
      exact cClosure_setUpperBoundedBy_of_upperBounds controllers times bounds
        ⟨hconsistent, hupper, hattest⟩ _ hclosure
    · exact hattest

theorem timesConsistent_of_setUpperBoundedBy
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {times bounds : Time → Prop}
    (hconsistent : TimesConsistent bounds)
    (hupper : SetUpperBoundedBy times bounds) :
    TimesConsistent times := by
  intro hinconsistent
  rcases hinconsistent with ⟨t, t', ht, ht', hcontr⟩
  rcases hupper t ht with ⟨r, hr, hle⟩
  rcases hupper t' ht' with ⟨r', hr', hle'⟩
  exact hconsistent
    ⟨r, r', hr, hr', contradicts_of_le_both hle hle' hcontr⟩

/--
Auxiliary consequence of Definition 6.4.5: a consistent
`C`-attestation-closed upper-bound set for `T` makes `T` itself consistent.
-/
theorem cAttestationClosedUpperBounds_timesConsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {controllers : Ctrl → Prop}
    {times bounds : Time → Prop}
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds) :
    TimesConsistent times := by
  exact timesConsistent_of_setUpperBoundedBy hbounds.1 hbounds.2.1

theorem cClosure_timesConsistent_of_upperBounds
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (times bounds : Time → Prop)
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds) :
    TimesConsistent (CClosure controllers times) := by
  have hclosed := upper_bound_consistent_for_cClosure controllers times bounds hbounds
  exact timesConsistent_of_setUpperBoundedBy hclosed.1 hclosed.2.1

/--
Auxiliary consequence of Corollary 6.4.6: every
member of the `C`-closure is a consistent time under a consistent
`C`-attestation-closed upper-bound set.
-/
theorem cClosure_member_consistentTime_of_upperBounds
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (times bounds : Time → Prop)
    (hbounds : ConsistentCAttestationClosedUpperBounds controllers times bounds)
    {t : Time} (hclosure : CClosure controllers times t) :
    ConsistentTime t := by
  exact upperBoundedBy_consistentTime_of_bounds_consistent hbounds.1
    (cClosure_upperBoundedBy_of_upperBounds controllers times bounds hbounds hclosure)

/--
Corollary 6.4.6(2), parameterized: given a consistent
`actCtrl(Π,Π')`-attestation-closed set of upper bounds for `actTime(Π,Π')`
(Definition 6.4.5), the circuit-derivation `cd` is consistent. The
Theorem 6.4.3(2) closure-consistency contrapositive
(`TimesConsistent (|actTime|_{actCtrl}) → cd.Consistent`) is taken here as an
explicit premise; the fully discharged form is
`consistent_upperBounds_imply_circuit_consistent`.
-/
theorem circuit_consistent_of_upperBounds
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hclosureConsistent :
      TimesConsistent
          (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) →
        cd.Consistent)
    {bounds : Time → Prop}
    (hbounds :
      ConsistentCAttestationClosedUpperBounds
        (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd) bounds) :
    cd.Consistent := by
  exact hclosureConsistent
    (cClosure_timesConsistent_of_upperBounds
      (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd) bounds hbounds)

/--
Corollary 6.4.6, second clause, reduced to the Section 5 active-index result:
the canonical Section 6 chain-link route supplies the closure-consistency
contrapositive.
-/
theorem circuit_consistent_of_upperBounds_and_chain_links_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    {bounds : Time → Prop}
    (hbounds :
      ConsistentCAttestationClosedUpperBounds
        (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd) bounds) :
    cd.Consistent := by
  exact
    circuit_consistent_of_upperBounds cd
      (circuit_consistent_of_cClosure_consistent_and_least_chain_links_indexed_closed
        cd hindex)
      hbounds

/--
Corollary 6.4.6(2), with the Section 6 chain obligations discharged and the
right-consistent branch supplied. The remaining explicit premise is the Section 5
right-incompatible index result.
-/
theorem circuit_consistent_of_upperBounds_and_right_incompatible_and_chain_links_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    {bounds : Time → Prop}
    (hbounds :
      ConsistentCAttestationClosedUpperBounds
        (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd) bounds) :
    cd.Consistent := by
  exact
    circuit_consistent_of_upperBounds cd
      (circuit_consistent_of_cClosure_consistent_and_right_incompatible_and_chain_links_indexed
        cd hrightIncompatible)
      hbounds

/--
Corollary 6.4.6, second clause, with Section 6 chain obligations and the
right-consistent branch discharged. The remaining explicit obligations are the
same-center ordered branch obligations.
-/
theorem circuit_consistent_of_upperBounds_and_ordered_incompatible_branches_and_chain_links_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hdirectSameCenterBranch :
      ∀ {center leftLower rightLower cutLower : cd.Index}
          {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        cd.circuit.left.1.paperIndex leftLower <
          cd.circuit.left.1.paperIndex rightLower →
        cd.circuit.left.1.paperIndex leftLower ≤
          cd.circuit.left.1.paperIndex cutLower →
        cd.circuit.left.1.paperIndex cutLower <
          cd.circuit.left.1.paperIndex rightLower →
        ContainsCut cd.leftDerivation
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower)
          (cd.circuit.left.1.paperIndex cutLower) →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l <
            cd.circuit.left.1.paperIndex center ∧
          cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hswapSameCenterBranch :
      ∀ {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        cd.RightCompatibleBefore center →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower) →
        cd.circuit.left.1.paperIndex rightLower <
          cd.circuit.left.1.paperIndex leftLower →
          ∀ {cutLower : cd.swap.Index},
            cd.swap.circuit.left.1.paperIndex (cd.rightIndex rightLower) ≤
              cd.swap.circuit.left.1.paperIndex cutLower →
            cd.swap.circuit.left.1.paperIndex cutLower <
              cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower) →
            ContainsCut cd.swap.leftDerivation
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex center))
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower))
              (cd.swap.circuit.left.1.paperIndex cutLower) →
            ∃ l : cd.swap.Index,
              cd.swap.circuit.left.1.paperIndex l <
                cd.swap.circuit.left.1.paperIndex (cd.rightIndex center) ∧
                cd.swap.RightCompatibleUpTo l ∧
                  cd.swap.ActiveInconsistentIndex l)
    {bounds : Time → Prop}
    (hbounds :
      ConsistentCAttestationClosedUpperBounds
        (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd) bounds) :
    cd.Consistent := by
  exact
    circuit_consistent_of_upperBounds_and_chain_links_indexed cd
      (ConsistentHistories.Routes.PathProperties.MainResult.index_result_of_ordered_incompatible_branches_indexed
        cd hdirectSameCenterBranch hswapSameCenterBranch)
      hbounds

/--
Example 6.4.9 / Definition 6.4.5: the reported-controller output
`{t_p | p ∈ actCtrl}` is a consistent `actCtrl(Π,Π')`-attestation-closed set of
upper bounds for `actTime(Π,Π')`, once the reported most-recent-attestation
hypotheses are given explicitly.
-/
theorem reportedControllerTimes_cAttestationClosedUpperBounds_activeCircuit
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        ConsistentTime (latest p))
    (htimes_le :
      ∀ {t : Time}, ActiveTimeCircuit cd t →
        t ≼ (latest (controller t)))
    (hmost :
      ∀ {p p' : Ctrl}, ActiveCtrlCircuit cd p →
        ActiveCtrlCircuit cd p' →
          MostRecentAttested (ActiveCtrlCircuit cd)
            (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) p
            (attested p p'))
    (hattested_ctrl :
      ∀ {p p' : Ctrl}, ActiveCtrlCircuit cd p →
        ActiveCtrlCircuit cd p' →
          controller (attested p p') = p')
    (hattested_le_latest :
      ∀ {p p' : Ctrl}, ActiveCtrlCircuit cd p →
        ActiveCtrlCircuit cd p' →
          (attested p p') ≼ (latest p')) :
    ConsistentCAttestationClosedUpperBounds
      (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) := by
  exact reportedControllerTimes_cAttestationClosedUpperBounds_of_reported_mostRecent hlatest_ctrl hlatest_consistent
      (fun ht => activeTimeCircuit_controller_mem cd ht) htimes_le hmost
      hattested_ctrl hattested_le_latest

/--
Example 6.4.9 / Definition 6.4.5, certificate form: the reported-controller
output is a consistent `actCtrl(Π,Π')`-attestation-closed set of upper bounds for
`actTime(Π,Π')` when the relational reported-most-recent certificate
(`ReportedMostRecentCertificate`) and the reported-output data are given
explicitly.
-/
theorem reportedControllerTimes_cAttestationClosedUpperBounds_activeCircuit_of_certificate
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        ConsistentTime (latest p))
    (htimes_le :
      ∀ {t : Time}, ActiveTimeCircuit cd t →
        t ≼ (latest (controller t)))
    (hcert :
      ReportedMostRecentCertificate (ActiveCtrlCircuit cd) latest attested) :
    ConsistentCAttestationClosedUpperBounds
      (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) := by
  exact reportedControllerTimes_cAttestationClosedUpperBounds_of_certificate hlatest_ctrl hlatest_consistent
      (fun ht => activeTimeCircuit_controller_mem cd ht) htimes_le hcert

/--
Example 6.4.9 with Corollary 6.4.6(1): the reported-controller output
upper-bounds the `actCtrl(Π,Π')`-closure of `actTime(Π,Π')` when the relational
reported-most-recent certificate and the reported-output data are given
explicitly.
-/
theorem reportedControllerTimes_cClosure_setUpperBoundedBy_activeCircuit_of_certificate
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        ConsistentTime (latest p))
    (htimes_le :
      ∀ {t : Time}, ActiveTimeCircuit cd t →
        t ≼ (latest (controller t)))
    (hcert :
      ReportedMostRecentCertificate (ActiveCtrlCircuit cd) latest attested) :
    SetUpperBoundedBy
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))
      (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) := by
  have hbounds :=
    reportedControllerTimes_cAttestationClosedUpperBounds_activeCircuit_of_certificate
      cd hlatest_ctrl hlatest_consistent htimes_le hcert
  exact cClosure_setUpperBoundedBy_of_upperBounds
    (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
    (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) hbounds

/--
Example 6.4.9 with Corollary 6.4.6(1): under the relational reported-most-recent
certificate, the reported-controller output remains a consistent
`actCtrl(Π,Π')`-attestation-closed set of upper bounds after replacing the active
times by their `actCtrl(Π,Π')`-closure.
-/
theorem reportedControllerTimes_cClosure_cAttestationClosedUpperBounds_activeCircuit_of_certificate
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        ConsistentTime (latest p))
    (htimes_le :
      ∀ {t : Time}, ActiveTimeCircuit cd t →
        t ≼ (latest (controller t)))
    (hcert :
      ReportedMostRecentCertificate (ActiveCtrlCircuit cd) latest attested) :
    ConsistentCAttestationClosedUpperBounds
      (ActiveCtrlCircuit cd)
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd))
      (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) := by
  have hbounds :=
    reportedControllerTimes_cAttestationClosedUpperBounds_activeCircuit_of_certificate
      cd hlatest_ctrl hlatest_consistent htimes_le hcert
  exact upper_bound_consistent_for_cClosure
    (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
    (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) hbounds

/--
Example 6.4.9 with Theorem 6.4.3 and Corollary 6.4.6: the
`actCtrl(Π,Π')`-closure of `actTime(Π,Π')` is consistent when the relational
reported-most-recent certificate and the reported-output data are given
explicitly.
-/
theorem reportedControllerTimes_cClosure_timesConsistent_activeCircuit_of_certificate
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        ConsistentTime (latest p))
    (htimes_le :
      ∀ {t : Time}, ActiveTimeCircuit cd t →
        t ≼ (latest (controller t)))
    (hcert :
      ReportedMostRecentCertificate (ActiveCtrlCircuit cd) latest attested) :
    TimesConsistent
      (CClosure (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)) := by
  have hbounds :=
    reportedControllerTimes_cAttestationClosedUpperBounds_activeCircuit_of_certificate
      cd hlatest_ctrl hlatest_consistent htimes_le hcert
  exact cClosure_timesConsistent_of_upperBounds
    (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
    (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) hbounds

/--
Generic reported-controller certificate adapter for downstream paper endpoints: any route
that consumes the reported-controller set as a
`ConsistentCAttestationClosedUpperBounds` hypothesis can consume the relational
most-recent certificate instead. The reported-output certificate data remain explicit, and this theorem does not construct the certificate-free algorithmic
closure proof.
-/
theorem circuit_consistent_of_reportedControllerTimes_certificate_of_upperBounds_route
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        ConsistentTime (latest p))
    (htimes_le :
      ∀ {t : Time}, ActiveTimeCircuit cd t →
        t ≼ (latest (controller t)))
    (hcert :
      ReportedMostRecentCertificate (ActiveCtrlCircuit cd) latest attested)
    (hroute :
      ConsistentCAttestationClosedUpperBounds
          (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
          (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) →
        cd.Consistent) :
    cd.Consistent := by
  exact hroute
    (reportedControllerTimes_cAttestationClosedUpperBounds_activeCircuit_of_certificate
      cd hlatest_ctrl hlatest_consistent htimes_le hcert)

/--
Theorem 6.4.3(1): if the circuit-derivation `cd` is inconsistent
(Definition 4.3.2(2)), then the `actCtrl(Π,Π')`-closure of `actTime(Π,Π')` — the
C-closure `|actTime|_{actCtrl}` of Definition 6.2.1 — is inconsistent in the
sense of Definition 6.4.2. Unconditional: the sole hypothesis is
`cd.Inconsistent`, with no extra explicit obligations.
-/
theorem inconsistentCircuit_implies_cClosure_inconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    cd.Inconsistent →
      TimesInconsistent
        (CClosure (ActiveCtrlCircuit cd)
          (ActiveTimeCircuit cd)) := by
  exact
    cClosure_inconsistent_of_least_chain_links_closed cd
      (ConsistentHistories.Routes.PathProperties.MainResult.inconsistentIndex_implies_activeInconsistentIndex
        cd)

/--
Theorem 6.4.3(2): the contrapositive of clause (1). If the
`actCtrl(Π,Π')`-closure of `actTime(Π,Π')` is consistent, then the
circuit-derivation `cd` is consistent (Definition 4.3.2(2)).
-/
theorem cClosure_consistent_implies_circuit_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    TimesConsistent
        (CClosure (ActiveCtrlCircuit cd)
          (ActiveTimeCircuit cd)) →
      cd.Consistent := by
  intro hconsistent hinconsistent
  exact hconsistent (inconsistentCircuit_implies_cClosure_inconsistent cd hinconsistent)

/--
Corollary 6.4.6: a consistent
`actCtrl`-attestation-closed upper-bound set for `actTime` is also such an
upper-bound set for the `actCtrl`-closure of `actTime`, and the existence of
such a set implies consistency of the circuit derivation. The second clause
uses the contrapositive `cClosure_consistent_implies_circuit_consistent`.
-/
theorem consistent_upperBounds_imply_circuit_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    (∀ {bounds : Time → Prop},
      ConsistentCAttestationClosedUpperBounds
        (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd) bounds →
      ConsistentCAttestationClosedUpperBounds
        (ActiveCtrlCircuit cd)
        (CClosure (ActiveCtrlCircuit cd)
          (ActiveTimeCircuit cd))
        bounds) ∧
    (∀ {bounds : Time → Prop},
      ConsistentCAttestationClosedUpperBounds
        (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd) bounds →
      cd.Consistent) := by
  constructor
  · intro bounds hbounds
    exact
      upper_bound_consistent_for_cClosure
        (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd) bounds hbounds
  · intro bounds hbounds
    exact
      circuit_consistent_of_upperBounds cd
        (cClosure_consistent_implies_circuit_consistent cd) hbounds

/--
Example 6.4.9: if the reported
most-recent-times algorithm succeeds, then its output
`{t_p | p in actCtrl}` is a consistent `actCtrl`-attestation-closed set of
upper bounds for `actTime`.
-/
theorem algorithm_computes_consistent_upperBounds {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {latest : Ctrl → Time}
    {attested : Ctrl → Ctrl → Time}
    (hlatest_ctrl :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        controller (latest p) = p)
    (hlatest_consistent :
      ∀ {p : Ctrl}, ActiveCtrlCircuit cd p →
        ConsistentTime (latest p))
    (htimes_le :
      ∀ {t : Time}, ActiveTimeCircuit cd t →
        t ≼ (latest (controller t)))
    (hmost :
      ∀ {p p' : Ctrl}, ActiveCtrlCircuit cd p →
        ActiveCtrlCircuit cd p' →
          MostRecentAttested (ActiveCtrlCircuit cd)
            (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) p
            (attested p p'))
    (hattested_ctrl :
      ∀ {p p' : Ctrl}, ActiveCtrlCircuit cd p →
        ActiveCtrlCircuit cd p' →
          controller (attested p p') = p')
    (hattested_le_latest :
      ∀ {p p' : Ctrl}, ActiveCtrlCircuit cd p →
        ActiveCtrlCircuit cd p' →
          (attested p p') ≼ (latest p')) :
    ConsistentCAttestationClosedUpperBounds
      (ActiveCtrlCircuit cd) (ActiveTimeCircuit cd)
      (ReportedControllerTimes (ActiveCtrlCircuit cd) latest) := by
  exact
    reportedControllerTimes_cAttestationClosedUpperBounds_activeCircuit
      cd hlatest_ctrl hlatest_consistent htimes_le hmost hattested_ctrl
      hattested_le_latest

/--
Remark 6.4.10, most-recent proof-obligation remark: for the concrete
construction, checking that the reported time `t_p` is the tuple whose `p'`
view stores `t_{pp'}` suffices to establish the `MostRecentAttested` property
for that stored time.
-/
theorem mostRecentAttested_tuple_check
    (D : LocalStateData.{u}) {controllers : D.Ctrl → Prop}
    {latest : D.Ctrl → LocalStateData.Time D}
    {p p' : D.Ctrl} (hp : controllers p) (hp_ne : p' ≠ p)
    {x : D.X} {hx : D.semilattice.Consistent x}
    {views : (k : D.Ctrl) → k ≠ p → LocalStateData.CTime D k}
    (hlatest_eq :
      latest p = LocalStateData.CTime.toTime (LocalStateData.CTime.node p x hx views))
    (hlatest_ctrl :
      ∀ {q : D.Ctrl}, controllers q → LocalStateData.Time.controller (latest q) = q) :
    MostRecentAttested controllers
      (ReportedControllerTimes controllers latest) p
      (LocalStateData.CTime.toTime (views p' hp_ne)) := by
  refine
    concreteNode_reportedControllerTimes_mostRecentAttested_cross
      D hp hp_ne hlatest_eq hlatest_ctrl ?_
  intro r' s' hmax
  let L := LocalStateData.locatedSemilattice D
  rcases hmax with ⟨hctrlr, hctrls, hupper⟩
  rcases hupper with ⟨bound, hbound_mem, hle_bound⟩
  have hbound_ctrl : controller bound = p := by
    calc
      controller bound = controller (attest r' s') := hle_bound.1.symm
      _ = controller r' := controller_preserving r' s'
      _ = p := hctrlr
  have hlatest_ctrl_L :
      ∀ {q : D.Ctrl}, controllers q → controller (latest q) = q := by
    intro q hq
    exact hlatest_ctrl hq
  have hbound_eq : bound = latest p :=
    reportedControllerTimes_eq_latest_of_controller hlatest_ctrl_L hbound_mem hbound_ctrl
  have hle_latest : le (attest r' s') (latest p) := by
    simpa [hbound_eq] using hle_bound
  have hle_node :
      le (attest r' s')
        (LocalStateData.CTime.toTime (LocalStateData.CTime.node p x hx views)) := by
    simpa [hlatest_eq] using hle_latest
  have hctrlr_time : LocalStateData.Time.controller r' = p := by
    simpa [L, LocalStateData.locatedSemilattice] using hctrlr
  have hctrls_time : LocalStateData.Time.controller s' = p' := by
    simpa [L, LocalStateData.locatedSemilattice, LocalStateData.CTime.toTime] using hctrls
  exact
    LocalStateData.locatedSemilattice_attest_le_node_stored_view_of_controller
      (D := D) (j := p) (i := p') hp_ne
      (x := x) (hx := hx) (views := views)
      (r := r') (s := s') hctrlr_time hctrls_time hle_node

end ConsistentHistories.Routes.StrongerSafety.Absolute
