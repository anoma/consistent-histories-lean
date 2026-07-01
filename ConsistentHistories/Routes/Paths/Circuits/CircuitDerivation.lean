import ConsistentHistories.Routes.Paths.Circuits.CutPrefixWitness

namespace ConsistentHistories.Routes.Paths.Circuits

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.Cut.Flags
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Foundation.Paths.InitialPrefixes

namespace CircuitDerivation

/--
Extend the left side of a circuit derivation by one final Cut step.
-/
def cutLeft {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j k : cd.circuit.left.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : cd.circuit.left.1.get k = ⋉ (cd.circuit.left.1.paperIndex j) tk)
    (hj : cd.circuit.left.1.get j =
      ⋊ (cd.circuit.left.1.paperIndex i)
        (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk)))
    (hi : cd.circuit.left.1.get i =
      ti # (⋊ (cd.circuit.left.1.paperIndex i)
          (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk))))
    (hconsistent :
      ConsistentTime
        (↱ (cd.circuit.left.1.paperIndex i) tk)) :
    CircuitDerivation Time :=
  let leftNew := ↱ (cd.circuit.left.1.paperIndex i) tk
  let hleftCtrl :
      controller leftNew =
        controller (cd.circuit.left.1.get k) := by
    calc
      controller leftNew = controller tk :=
        (↱ (cd.circuit.left.1.paperIndex i)).controller_preserving tk
      _ = controller
            (⋉ (cd.circuit.left.1.paperIndex j) tk) :=
        ((⋉ (cd.circuit.left.1.paperIndex j)).controller_preserving tk).symm
      _ = controller (cd.circuit.left.1.get k) := by rw [hk]
  let leftCut :=
    Derivation.cut cd.leftDerivation hij hjk hk hj hi hconsistent
  { circuit :=
      { left := ⟨Derivation.root leftCut, ⟨leftCut⟩⟩
        right := cd.circuit.right
        length_eq := cd.circuit.length_eq
        controller_eq_before_last := by
          intro idx hidx_lt
          have hleftController :
              controller
                  ((cd.circuit.left.1.replace k leftNew hleftCtrl hconsistent).get idx) =
                controller (cd.circuit.left.1.get idx) := by
            by_cases hidx : idx = k
            · rw [hidx]
              exact Prepath.replace_get_same_controller cd.circuit.left.1 k leftNew
                hleftCtrl hconsistent
            · exact Prepath.replace_get_ne_controller cd.circuit.left.1 hidx leftNew
                hleftCtrl hconsistent
          have hidx_base :
              cd.circuit.left.1.paperIndex idx < cd.circuit.left.1.length := by
            simpa [Prepath.replace_paperIndex] using hidx_lt
          exact hleftController.trans
            (cd.circuit.controller_eq_before_last idx hidx_base) }
    leftDerivation := leftCut
    rightDerivation := cd.rightDerivation }

@[simp] theorem cutLeft_leftTime_upper_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    {i j k : cd.circuit.left.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : cd.circuit.left.1.get k = ⋉ (cd.circuit.left.1.paperIndex j) tk)
    (hj : cd.circuit.left.1.get j =
      ⋊ (cd.circuit.left.1.paperIndex i)
        (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk)))
    (hi : cd.circuit.left.1.get i =
      ti # (⋊ (cd.circuit.left.1.paperIndex i)
          (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk))))
    (hconsistent :
      ConsistentTime
        (↱ (cd.circuit.left.1.paperIndex i) tk)) :
    (cd.cutLeft hij hjk hk hj hi hconsistent).circuit.left.1.get k =
      ↱ (cd.circuit.left.1.paperIndex i) tk := by
  let leftNew := ↱ (cd.circuit.left.1.paperIndex i) tk
  let hleftCtrl :
      controller leftNew =
        controller (cd.circuit.left.1.get k) := by
    calc
      controller leftNew = controller tk :=
        (↱ (cd.circuit.left.1.paperIndex i)).controller_preserving tk
      _ = controller
            (⋉ (cd.circuit.left.1.paperIndex j) tk) :=
        ((⋉ (cd.circuit.left.1.paperIndex j)).controller_preserving tk).symm
      _ = controller (cd.circuit.left.1.get k) := by rw [hk]
  exact Prepath.replace_get_same cd.circuit.left.1 k leftNew hleftCtrl hconsistent

/--
The center of a one-sided final left Cut is inactive on the left side of the
resulting circuit derivation.
-/
theorem cutLeft_left_center_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    {i j k : cd.circuit.left.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : cd.circuit.left.1.get k = ⋉ (cd.circuit.left.1.paperIndex j) tk)
    (hj : cd.circuit.left.1.get j =
      ⋊ (cd.circuit.left.1.paperIndex i)
        (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk)))
    (hi : cd.circuit.left.1.get i =
      ti # (⋊ (cd.circuit.left.1.paperIndex i)
          (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk))))
    (hconsistent :
      ConsistentTime
        (↱ (cd.circuit.left.1.paperIndex i) tk)) :
    (cd.cutLeft hij hjk hk hj hi hconsistent).leftDerivation.Inactive j := by
  let leftNew := ↱ (cd.circuit.left.1.paperIndex i) tk
  let hleftCtrl :
      controller leftNew =
        controller (cd.circuit.left.1.get k) := by
    calc
      controller leftNew = controller tk :=
        (↱ (cd.circuit.left.1.paperIndex i)).controller_preserving tk
      _ = controller
            (⋉ (cd.circuit.left.1.paperIndex j) tk) :=
        ((⋉ (cd.circuit.left.1.paperIndex j)).controller_preserving tk).symm
      _ = controller (cd.circuit.left.1.get k) := by rw [hk]
  change
    (cd.circuit.left.1.replace k leftNew hleftCtrl hconsistent).Inactive j
  refine ⟨k, i, ?_⟩
  refine ⟨hij, hjk, ?_⟩
  simpa [leftNew, Prepath.replace_get_same, Prepath.replace_paperIndex] using
    hasCutLabelAt_nextIndex (Time := Time) (cd.circuit.left.1.paperIndex i) tk

/--
Extend both sides of a circuit derivation by final Cut steps. The Cut centers
and lower endpoints need not be syntactically aligned here; later theorems add
the alignment hypotheses they need.
-/
def cutPair {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j k : cd.circuit.left.1.Index} {i' j' k' : cd.circuit.right.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    (hij' : i'.val < j'.val) (hjk' : j'.val < k'.val)
    {ti tj tk ti' tj' tk' : Time}
    (hk : cd.circuit.left.1.get k = ⋉ (cd.circuit.left.1.paperIndex j) tk)
    (hj : cd.circuit.left.1.get j =
      ⋊ (cd.circuit.left.1.paperIndex i)
        (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk)))
    (hi : cd.circuit.left.1.get i =
      ti # (⋊ (cd.circuit.left.1.paperIndex i)
          (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk))))
    (hconsistent :
      ConsistentTime
        (↱ (cd.circuit.left.1.paperIndex i) tk))
    (hk' : cd.circuit.right.1.get k' =
      ⋉ (cd.circuit.right.1.paperIndex j') tk')
    (hj' : cd.circuit.right.1.get j' =
      ⋊ (cd.circuit.right.1.paperIndex i')
        (tj' # (⋉ (cd.circuit.right.1.paperIndex j') tk')))
    (hi' : cd.circuit.right.1.get i' =
      ti' # (⋊ (cd.circuit.right.1.paperIndex i')
          (tj' # (⋉ (cd.circuit.right.1.paperIndex j') tk'))))
    (hconsistent' :
      ConsistentTime
        (↱ (cd.circuit.right.1.paperIndex i') tk')) :
    CircuitDerivation Time :=
  let leftNew := ↱ (cd.circuit.left.1.paperIndex i) tk
  let rightNew := ↱ (cd.circuit.right.1.paperIndex i') tk'
  let hleftCtrl :
      controller leftNew =
        controller (cd.circuit.left.1.get k) := by
    calc
      controller leftNew = controller tk :=
        (↱ (cd.circuit.left.1.paperIndex i)).controller_preserving tk
      _ = controller
            (⋉ (cd.circuit.left.1.paperIndex j) tk) :=
        ((⋉ (cd.circuit.left.1.paperIndex j)).controller_preserving tk).symm
      _ = controller (cd.circuit.left.1.get k) := by rw [hk]
  let hrightCtrl :
      controller rightNew =
        controller (cd.circuit.right.1.get k') := by
    calc
      controller rightNew = controller tk' :=
        (↱ (cd.circuit.right.1.paperIndex i')).controller_preserving tk'
      _ = controller
            (⋉ (cd.circuit.right.1.paperIndex j') tk') :=
        ((⋉ (cd.circuit.right.1.paperIndex j')).controller_preserving tk').symm
      _ = controller (cd.circuit.right.1.get k') := by rw [hk']
  let leftCut :=
    Derivation.cut cd.leftDerivation hij hjk hk hj hi hconsistent
  let rightCut :=
    Derivation.cut cd.rightDerivation hij' hjk' hk' hj' hi' hconsistent'
  { circuit :=
      { left := ⟨Derivation.root leftCut, ⟨leftCut⟩⟩
        right := ⟨Derivation.root rightCut, ⟨rightCut⟩⟩
        length_eq := cd.circuit.length_eq
        controller_eq_before_last :=
          cd.circuit.replaceBoth_controller_eq_before_last k leftNew hleftCtrl
            hconsistent k' rightNew hrightCtrl hconsistent' }
    leftDerivation := leftCut
    rightDerivation := rightCut }

/-- The same circuit derivation with its two derivations exchanged. -/
def swap {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) : CircuitDerivation Time where
  circuit := cd.circuit.swap
  leftDerivation := cd.rightDerivation
  rightDerivation := cd.leftDerivation

/-- Indexes of a circuit derivation, represented on the left path. -/
abbrev Index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) : Type :=
  cd.circuit.left.1.Index

/-- The matching right-path index. -/
def rightIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index) :
    cd.circuit.right.1.Index :=
  Fin.cast cd.circuit.length_eq i

def leftTime {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index) :
    Time :=
  cd.circuit.left.1.get i

def rightTime {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index) :
    Time :=
  cd.circuit.right.1.get (cd.rightIndex i)

@[simp] theorem cutLeft_leftTime_center_unchanged {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    {i j k : cd.circuit.left.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : cd.circuit.left.1.get k = ⋉ (cd.circuit.left.1.paperIndex j) tk)
    (hj : cd.circuit.left.1.get j =
      ⋊ (cd.circuit.left.1.paperIndex i)
        (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk)))
    (hi : cd.circuit.left.1.get i =
      ti # (⋊ (cd.circuit.left.1.paperIndex i)
          (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk))))
    (hconsistent :
      ConsistentTime
        (↱ (cd.circuit.left.1.paperIndex i) tk)) :
    (cd.cutLeft hij hjk hk hj hi hconsistent).leftTime j = cd.leftTime j := by
  exact
    Derivation.cut_root_get_center_unchanged cd.leftDerivation hij hjk hk hj hi
      hconsistent

/-- Definition 4.3.1: length of a circuit derivation. -/
def length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) : Nat :=
  cd.circuit.length

/-- Definition 4.3.1: the left derivation root is the left path. -/
theorem left_root {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    cd.leftDerivation.root = cd.circuit.left.1 :=
  rfl

/-- Definition 4.3.1: the right derivation root is the right path. -/
theorem right_root {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    cd.rightDerivation.root = cd.circuit.right.1 :=
  rfl

/-- Definition 4.3.1: the left derivation root has the circuit-derivation length. -/
theorem left_root_length_eq_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    cd.leftDerivation.root.length = cd.length :=
  rfl

/-- Definition 4.3.1: the right derivation root has the circuit-derivation length. -/
theorem right_root_length_eq_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    cd.rightDerivation.root.length = cd.length :=
  cd.circuit.length_eq.symm

/-- Definition 4.3.1: a circuit derivation has positive length. -/
theorem length_pos {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    0 < cd.length :=
  cd.circuit.length_pos

/-- Exchanging the two sides of a circuit derivation preserves its length. -/
theorem swap_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    cd.swap.length = cd.length :=
  cd.circuit.swap_length

/-- Definition 4.3.1: left circuit time notation agrees with derivation notation. -/
theorem leftTime_eq_get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) :
    cd.leftTime i = cd.leftDerivation.get i :=
  rfl

/-- Definition 4.3.1: right circuit time notation agrees with derivation notation. -/
theorem rightTime_eq_get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) :
    cd.rightTime i = cd.rightDerivation.get (cd.rightIndex i) :=
  rfl

/-- Definition 4.3.1: every left circuit-derivation entry is consistent. -/
theorem leftTime_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) :
    ConsistentTime (cd.leftTime i) :=
  cd.circuit.left.1.consistent i

/-- Definition 4.3.1: every right circuit-derivation entry is consistent. -/
theorem rightTime_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) :
    ConsistentTime (cd.rightTime i) :=
  cd.circuit.right.1.consistent (cd.rightIndex i)

theorem rightIndex_val {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) :
    (cd.rightIndex i).val = i.val := by
  rfl

/-- Common circuit indexes have the same strict order on the right path. -/
theorem rightIndex_lt_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j : cd.Index} :
    (cd.rightIndex i).val < (cd.rightIndex j).val ↔ i.val < j.val := by
  simp [rightIndex]

/-- Common circuit indexes have the same weak order on the right path. -/
theorem rightIndex_le_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j : cd.Index} :
    (cd.rightIndex i).val ≤ (cd.rightIndex j).val ↔ i.val ≤ j.val := by
  simp [rightIndex]

/-- Every right-path index is the right index of its cast back to the left path. -/
theorem rightIndex_castLeft {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.circuit.right.1.Index) :
    cd.rightIndex (Fin.cast cd.circuit.length_eq.symm i) = i := by
  ext
  rfl

/-- Casting a circuit-derivation index to the right and back is identity. -/
theorem rightIndex_castRight {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) :
    Fin.cast cd.circuit.length_eq.symm (cd.rightIndex i) = i := by
  ext
  rfl

/-- The circuit-derivation right-index cast is injective. -/
theorem rightIndex_injective {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    Function.Injective cd.rightIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : cd.circuit.right.1.Index => x.val) h

/-- The circuit-derivation right-index cast is surjective. -/
theorem rightIndex_surjective {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    Function.Surjective cd.rightIndex := by
  intro i
  exact ⟨Fin.cast cd.circuit.length_eq.symm i, cd.rightIndex_castLeft i⟩

/-- Equality of right indexes is equality of circuit-derivation indexes. -/
theorem rightIndex_eq_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j : cd.Index} :
    cd.rightIndex i = cd.rightIndex j ↔ i = j := by
  constructor
  · intro h
    exact CircuitDerivation.rightIndex_injective cd h
  · intro h
    cases h
    rfl

/-- The right-index cast in a swapped circuit is the original inverse cast. -/
theorem swap_rightIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.circuit.right.1.Index) :
    cd.swap.rightIndex i = Fin.cast cd.circuit.length_eq.symm i := by
  ext
  rfl

/-- Left times in the swapped circuit derivation are original right times. -/
theorem swap_leftTime {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.swap.Index) :
    cd.swap.leftTime i =
      cd.rightTime (Fin.cast cd.circuit.length_eq.symm i) := by
  simp [leftTime, rightTime, rightIndex, CircuitDerivation.swap, Circuit.swap]

/-- Right times in the swapped circuit derivation are original left times. -/
theorem swap_rightTime {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.swap.Index) :
    cd.swap.rightTime i =
      cd.leftTime (Fin.cast cd.circuit.length_eq.symm i) := by
  simp [leftTime, rightTime, rightIndex, CircuitDerivation.swap, Circuit.swap]

theorem rightIndex_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) :
    cd.circuit.right.1.paperIndex (cd.rightIndex i) =
      cd.circuit.left.1.paperIndex i := by
  simp [Prepath.paperIndex, rightIndex]

/-- Common circuit indexes have the same strict paper-index order on the right path. -/
theorem rightIndex_paperIndex_lt_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i j : cd.Index} :
    cd.circuit.right.1.paperIndex (cd.rightIndex i) <
        cd.circuit.right.1.paperIndex (cd.rightIndex j) ↔
      cd.circuit.left.1.paperIndex i < cd.circuit.left.1.paperIndex j := by
  simp [Prepath.paperIndex, rightIndex]

/-- Common circuit indexes have the same weak paper-index order on the right path. -/
theorem rightIndex_paperIndex_le_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i j : cd.Index} :
    cd.circuit.right.1.paperIndex (cd.rightIndex i) ≤
        cd.circuit.right.1.paperIndex (cd.rightIndex j) ↔
      cd.circuit.left.1.paperIndex i ≤ cd.circuit.left.1.paperIndex j := by
  simp [Prepath.paperIndex, rightIndex]

/--
Definition 4.3.1(1): if the circuit index is before the final index, the two
circuit-derivation times have the same controller.
-/
theorem controller_eq_before_last {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) (hi : cd.circuit.left.1.paperIndex i < cd.circuit.length) :
    controller (cd.leftTime i) =
      controller (cd.rightTime i) := by
  exact cd.circuit.controller_eq_before_last i hi

/--
Definition 4.3.1(1): if the two circuit-derivation times at an index have
different controllers, that index is the final circuit index.
-/
theorem final_index_of_controller_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hctrl :
      controller (cd.leftTime i) ≠
        controller (cd.rightTime i)) :
    cd.circuit.left.1.paperIndex i = cd.circuit.length := by
  exact cd.circuit.final_index_of_controller_ne hctrl

/--
Notation 2.2.4: a contradiction `t 🗲 t'` between the two circuit times at an
index entails equality of their controllers.
-/
theorem final_contradiction_controller_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hcontr : (cd.leftTime i) 🗲 (cd.rightTime i)) :
    controller (cd.leftTime i) =
      controller (cd.rightTime i) := by
  exact hcontr.1

/--
Definition 4.3.1(1): a one-index circuit derivation, where the only index is the
final one and so carries no before-last controller-equality obligation (the note
that `T[n]` and `T'[n]` need not share a controller).
-/
def singleIndexOfTimes {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (left right : Time)
    (hleft : ConsistentTime left)
    (hright : ConsistentTime right) : CircuitDerivation Time :=
  let leftBase : Fin 1 → Time := fun _ => left
  let rightBase : Fin 1 → Time := fun _ => right
  let hleftInit : ∀ i, ConsistentTime (initTime Time leftBase i) := by
    intro i
    have hi : i.val = 0 := by omega
    rw [initTime_zero leftBase i hi]
    exact hleft
  let hrightInit : ∀ i, ConsistentTime (initTime Time rightBase i) := by
    intro i
    have hi : i.val = 0 := by omega
    rw [initTime_zero rightBase i hi]
    exact hright
  let leftPath := initPrepath Time (by decide : 0 < 1) leftBase hleftInit
  let rightPath := initPrepath Time (by decide : 0 < 1) rightBase hrightInit
  let leftDeriv : Derivation Time leftPath :=
    Derivation.init (Time := Time) (by decide : 0 < 1) leftBase hleftInit
  let rightDeriv : Derivation Time rightPath :=
    Derivation.init (Time := Time) (by decide : 0 < 1) rightBase hrightInit
  { circuit :=
      { left := ⟨leftPath, ⟨leftDeriv⟩⟩
        right := ⟨rightPath, ⟨rightDeriv⟩⟩
        length_eq := rfl
        controller_eq_before_last := by
          intro i hi
          change i.val + 1 < 1 at hi
          omega }
    leftDerivation := leftDeriv
    rightDerivation := rightDeriv }

/--
Definition 4.3.1(1): two consistent times with different controllers form a
one-index circuit whose final paired controllers differ (permitted by the note
that the final controllers need not be equal).
-/
theorem exists_singleIndex_final_controller_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {left right : Time}
    (hleft : ConsistentTime left)
    (hright : ConsistentTime right)
    (hctrl : controller left ≠ controller right) :
    ∃ cd : CircuitDerivation Time, ∃ i : cd.Index,
      cd.circuit.left.1.paperIndex i = cd.length ∧
        controller (cd.leftTime i) ≠ controller (cd.rightTime i) := by
  let cd := singleIndexOfTimes left right hleft hright
  let i : cd.Index := ⟨0, by
    dsimp [cd, singleIndexOfTimes, CircuitDerivation.Index, initPrepath]
    decide⟩
  refine ⟨cd, i, ?_⟩
  constructor
  · rfl
  · simpa [cd, i, singleIndexOfTimes, leftTime, rightTime, rightIndex,
      Derivation.get, Prepath.get, initPrepath, initTime] using hctrl

/-- Definition 4.3.1(4)(b): an index of a circuit-derivation is active when it is
active (Definition 4.1.5) in at least one of the two derivations. -/
def Active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index) : Prop :=
  cd.leftDerivation.Active i ∨ cd.rightDerivation.Active (cd.rightIndex i)

/-- Definition 4.3.1(4)(c): an index of a circuit-derivation is doubly active when it
is active in both derivations. -/
def DoublyActive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index) : Prop :=
  cd.leftDerivation.Active i ∧ cd.rightDerivation.Active (cd.rightIndex i)

/-- Definition 4.3.1(4)(d): an index of a circuit-derivation is inactive when it is
inactive in both derivations. -/
def Inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index) : Prop :=
  cd.leftDerivation.Inactive i ∧ cd.rightDerivation.Inactive (cd.rightIndex i)

/-- Definition 4.3.1(4)(b): circuit activity is activity on at least one side. -/
theorem active_iff_left_or_right_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) :
    cd.Active i ↔
      cd.leftDerivation.Active i ∨ cd.rightDerivation.Active (cd.rightIndex i) :=
  Iff.rfl

/-- Definition 4.3.1(4)(c): doubly active means active on both sides. -/
theorem doublyActive_iff_left_and_right_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index) :
    cd.DoublyActive i ↔
      cd.leftDerivation.Active i ∧ cd.rightDerivation.Active (cd.rightIndex i) :=
  Iff.rfl

/-- Definition 4.3.1(4)(d): inactive means inactive on both sides. -/
theorem inactive_iff_left_and_right_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index) :
    cd.Inactive i ↔
      cd.leftDerivation.Inactive i ∧ cd.rightDerivation.Inactive (cd.rightIndex i) :=
  Iff.rfl

/-- Definition 4.3.1(4)(b): left-path activity makes the circuit index active. -/
theorem active_of_left_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.leftDerivation.Active i) : cd.Active i := by
  exact Or.inl h

/-- Definition 4.3.1(4)(b): right-path activity makes the circuit index active. -/
theorem active_of_right_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.rightDerivation.Active (cd.rightIndex i)) : cd.Active i := by
  exact Or.inr h

/-- Definition 4.3.1(4)(c): a doubly active index is active on the left path. -/
theorem doublyActive_left_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.DoublyActive i) : cd.leftDerivation.Active i := by
  exact h.1

/-- Definition 4.3.1(4)(c): a doubly active index is active on the right path. -/
theorem doublyActive_right_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.DoublyActive i) :
    cd.rightDerivation.Active (cd.rightIndex i) := by
  exact h.2

/-- Definition 4.3.1(4)(d): circuit inactivity includes left-path inactivity. -/
theorem inactive_left_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.Inactive i) : cd.leftDerivation.Inactive i := by
  exact h.1

/-- Definition 4.3.1(4)(d): circuit inactivity includes right-path inactivity. -/
theorem inactive_right_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.Inactive i) :
    cd.rightDerivation.Inactive (cd.rightIndex i) := by
  exact h.2

theorem doublyActive_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) : cd.DoublyActive i → cd.Active i := by
  intro h
  exact cd.active_of_left_active h.1

/-- Definition 4.3.1(4)(c): a doubly active index is active. -/
theorem active_of_doublyActive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.DoublyActive i) : cd.Active i := by
  exact cd.doublyActive_active i h

/-- Definition 4.3.1(4)(b) with Definition 4.1.5: the first circuit index is active. -/
theorem active_of_first_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (hfirst : i.val = 0) :
    cd.Active i := by
  exact cd.active_of_left_active (cd.leftDerivation.active_of_first_index hfirst)

/-- Definition 4.3.1(4)(b) with Definition 4.1.5: the final circuit index is active. -/
theorem active_of_last_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (hlast : cd.circuit.left.1.paperIndex i = cd.circuit.length) :
    cd.Active i := by
  have hleftLast : cd.circuit.left.1.paperIndex i = cd.circuit.left.1.length := by
    simpa [Circuit.length] using hlast
  exact cd.active_of_left_active (cd.leftDerivation.active_of_last_index hleftLast)

theorem inactive_iff_not_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) : cd.Inactive i ↔ ¬ cd.Active i := by
  classical
  constructor
  · intro h hactive
    cases hactive with
    | inl hleft => exact hleft h.1
    | inr hright => exact hright h.2
  · intro h
    constructor
    · by_cases hleft : cd.leftDerivation.Inactive i
      · exact hleft
      · exact False.elim (h (Or.inl hleft))
    · by_cases hright : cd.rightDerivation.Inactive (cd.rightIndex i)
      · exact hright
      · exact False.elim (h (Or.inr hright))

/-- Definition 4.3.1(4)(d): active is equivalent to not inactive. -/
theorem active_iff_not_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) : cd.Active i ↔ ¬ cd.Inactive i := by
  classical
  constructor
  · intro hactive hinactive
    exact (cd.inactive_iff_not_active i).mp hinactive hactive
  · intro hnotInactive
    by_cases hactive : cd.Active i
    · exact hactive
    · exact False.elim (hnotInactive ((cd.inactive_iff_not_active i).mpr hactive))

/-- Definition 4.3.1(4)(d): an inactive index is not active. -/
theorem inactive_not_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.Inactive i) : ¬ cd.Active i := by
  exact (cd.inactive_iff_not_active i).mp h

/-- Definition 4.3.1(4)(d): a non-active index is inactive. -/
theorem not_active_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : ¬ cd.Active i) : cd.Inactive i := by
  exact (cd.inactive_iff_not_active i).mpr h

/--
Extend the left side of a circuit derivation by one final `Inc` step at index
`j`, raising its time under an unchanged cutting flag while leaving the right
side fixed.
-/
def incLeft {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (j : cd.Index) {t' : Time}
    (hlt : lt (cd.leftTime j) t')
    (hflag :
      flagOf cuttingFlagSet (cd.leftTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    CircuitDerivation Time :=
  let leftInc := Derivation.inc cd.leftDerivation j hlt hflag hconsistent
  { circuit :=
      { left := ⟨Derivation.root leftInc, ⟨leftInc⟩⟩
        right := cd.circuit.right
        length_eq := cd.circuit.length_eq
        controller_eq_before_last := by
          intro i hi
          have hleftController :
              controller
                  ((cd.circuit.left.1.replace j t' hlt.1.1.symm hconsistent).get i) =
                controller (cd.circuit.left.1.get i) := by
            by_cases hidx : i = j
            · subst i
              exact Prepath.replace_get_same_controller cd.circuit.left.1 j t'
                hlt.1.1.symm hconsistent
            · exact Prepath.replace_get_ne_controller cd.circuit.left.1 hidx t'
                hlt.1.1.symm hconsistent
          have hi_base :
              cd.circuit.left.1.paperIndex i < cd.circuit.left.1.length := by
            simpa [Prepath.replace_paperIndex] using hi
          exact hleftController.trans
            (cd.circuit.controller_eq_before_last i hi_base) }
    leftDerivation := leftInc
    rightDerivation := cd.rightDerivation }

/--
Extend the right side of a circuit derivation by one final `Inc` step at the
index matching a left circuit index.
-/
def incRight {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (j : cd.Index) {t' : Time}
    (hlt : lt (cd.rightTime j) t')
    (hflag :
      flagOf cuttingFlagSet (cd.rightTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    CircuitDerivation Time :=
  let rightIdx := cd.rightIndex j
  let rightInc := Derivation.inc cd.rightDerivation rightIdx hlt hflag hconsistent
  { circuit :=
      { left := cd.circuit.left
        right := ⟨Derivation.root rightInc, ⟨rightInc⟩⟩
        length_eq := cd.circuit.length_eq
        controller_eq_before_last := by
          intro i hi
          have hrightController :
              controller
                  ((cd.circuit.right.1.replace rightIdx t' hlt.1.1.symm
                    hconsistent).get (Fin.cast cd.circuit.length_eq i)) =
                controller
                  (cd.circuit.right.1.get (Fin.cast cd.circuit.length_eq i)) := by
            by_cases hidx : Fin.cast cd.circuit.length_eq i = rightIdx
            · rw [hidx]
              exact Prepath.replace_get_same_controller cd.circuit.right.1 rightIdx t'
                hlt.1.1.symm hconsistent
            · exact Prepath.replace_get_ne_controller cd.circuit.right.1 hidx t'
                hlt.1.1.symm hconsistent
          exact (cd.circuit.controller_eq_before_last i hi).trans
            hrightController.symm }
    leftDerivation := cd.leftDerivation
    rightDerivation := rightInc }

/--
Extend the right side of a circuit derivation by one final `⋉Intro` step at the
index matching a left circuit index.
-/
def cutYouIntroRight {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (j : cd.Index) (target : Nat) {t : Time}
    (hshape : cd.rightTime j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    CircuitDerivation Time :=
  let rightIdx := cd.rightIndex j
  let hctrl :
      controller (⋉ target t) =
        controller (cd.rightTime j) := by
    calc
      controller (⋉ target t) =
          controller t :=
        (⋉ target).controller_preserving t
      _ = controller (↱ target t) :=
        ((↱ target).controller_preserving t).symm
      _ = controller (cd.rightTime j) := by rw [hshape]
  let rightIntro := Derivation.cutYouIntro cd.rightDerivation rightIdx target
    hshape hconsistent
  { circuit :=
      { left := cd.circuit.left
        right := ⟨Derivation.root rightIntro, ⟨rightIntro⟩⟩
        length_eq := cd.circuit.length_eq
        controller_eq_before_last := by
          intro i hi
          have hrightController :
              controller
                  ((cd.circuit.right.1.replace rightIdx (⋉ target t) hctrl
                    hconsistent).get (Fin.cast cd.circuit.length_eq i)) =
                controller
                  (cd.circuit.right.1.get (Fin.cast cd.circuit.length_eq i)) := by
            by_cases hidx : Fin.cast cd.circuit.length_eq i = rightIdx
            · rw [hidx]
              exact Prepath.replace_get_same_controller cd.circuit.right.1
                rightIdx (⋉ target t) hctrl hconsistent
            · exact Prepath.replace_get_ne_controller cd.circuit.right.1 hidx
                (⋉ target t) hctrl hconsistent
          exact (cd.circuit.controller_eq_before_last i hi).trans
            hrightController.symm }
    leftDerivation := cd.leftDerivation
    rightDerivation := rightIntro }

@[simp] theorem incLeft_leftTime_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) {t' : Time}
    (hlt : (cd.leftTime j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (cd.leftTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (cd.incLeft j hlt hflag hconsistent).leftTime j = t' := by
  exact Prepath.replace_get_same cd.circuit.left.1 j t' hlt.1.1.symm
    hconsistent

@[simp] theorem incRight_rightTime_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) {t' : Time}
    (hlt : (cd.rightTime j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (cd.rightTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (cd.incRight j hlt hflag hconsistent).rightTime j = t' := by
  exact Prepath.replace_get_same cd.circuit.right.1 (cd.rightIndex j) t'
    hlt.1.1.symm hconsistent

@[simp] theorem cutYouIntroRight_rightTime_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) (target : Nat) {t : Time}
    (hshape : cd.rightTime j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (cd.cutYouIntroRight j target hshape hconsistent).rightTime j =
      ⋉ target t := by
  let hctrl :
      controller (⋉ target t) =
        controller (cd.rightTime j) := by
    calc
      controller (⋉ target t) =
          controller t :=
        (⋉ target).controller_preserving t
      _ = controller (↱ target t) :=
        ((↱ target).controller_preserving t).symm
      _ = controller (cd.rightTime j) := by rw [hshape]
  exact Prepath.replace_get_same cd.circuit.right.1 (cd.rightIndex j)
    (⋉ target t) hctrl hconsistent

@[simp] theorem cutYouIntroRight_leftTime_unchanged {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) (target : Nat) {t : Time}
    (hshape : cd.rightTime j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (cd.cutYouIntroRight j target hshape hconsistent).leftTime j =
      cd.leftTime j := by
  rfl

theorem incLeft_inactive_of_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) {t' : Time}
    (hlt : (cd.leftTime j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (cd.leftTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t')
    (hinactive : cd.Inactive j) :
    (cd.incLeft j hlt hflag hconsistent).Inactive j := by
  constructor
  · exact cd.leftDerivation.inc_inactive_of_inactive hinactive.1 hlt hflag
      hconsistent
  · simpa [incLeft, Inactive, rightIndex] using hinactive.2

theorem incRight_inactive_of_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) {t' : Time}
    (hlt : (cd.rightTime j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (cd.rightTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t')
    (hinactive : cd.Inactive j) :
    (cd.incRight j hlt hflag hconsistent).Inactive j := by
  constructor
  · simpa [incRight, Inactive] using hinactive.1
  · exact cd.rightDerivation.inc_inactive_of_inactive hinactive.2 hlt hflag
      hconsistent

/-- Definition 4.2.1(2): a pair initial prefix, specialized to circuit
derivations — each side is an initial prefix of the corresponding derivation. -/
def IsInitialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (pref cd : CircuitDerivation Time) : Prop :=
  InitialPrefix pref.leftDerivation cd.leftDerivation ∧
    InitialPrefix pref.rightDerivation cd.rightDerivation

theorem isInitialPrefix_refl {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    cd.IsInitialPrefix cd := by
  exact ⟨InitialPrefix.refl cd.leftDerivation, InitialPrefix.refl cd.rightDerivation⟩

theorem incLeft_isInitialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) {t' : Time}
    (hlt : (cd.leftTime j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (cd.leftTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    cd.IsInitialPrefix (cd.incLeft j hlt hflag hconsistent) := by
  constructor
  · simpa [incLeft] using
      InitialPrefix.inc cd.leftDerivation
        (InitialPrefix.refl cd.leftDerivation) j hlt hflag hconsistent
  · simpa [incLeft] using InitialPrefix.refl cd.rightDerivation

theorem incRight_isInitialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) {t' : Time}
    (hlt : (cd.rightTime j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (cd.rightTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    cd.IsInitialPrefix (cd.incRight j hlt hflag hconsistent) := by
  constructor
  · simpa [incRight] using InitialPrefix.refl cd.leftDerivation
  · simpa [incRight] using
      InitialPrefix.inc cd.rightDerivation
        (InitialPrefix.refl cd.rightDerivation) (cd.rightIndex j) hlt hflag
        hconsistent

/--
Circuit-prefix support for the one-sided `Inc` route: a prefix of
`cd.incLeft` is either already a prefix of `cd`, or its left side reaches the
whole final left derivation while its right side remains a prefix of `cd`.
-/
theorem incLeft_prefix_cases {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) {t' : Time}
    (hlt : (cd.leftTime j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (cd.leftTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t')
    {pref : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix (cd.incLeft j hlt hflag hconsistent)) :
    pref.IsInitialPrefix cd ∨
      (InitialPrefix (cd.incLeft j hlt hflag hconsistent).leftDerivation
          pref.leftDerivation ∧
        InitialPrefix pref.rightDerivation cd.rightDerivation) := by
  rcases
      InitialPrefix.inc_cases j hlt hflag hconsistent hprefix.1 with
    hbefore | hafter
  · exact Or.inl
      ⟨hbefore, by simpa [incLeft] using hprefix.2⟩
  · exact Or.inr
      ⟨hafter, by simpa [incLeft] using hprefix.2⟩

/--
Circuit-prefix support for the one-sided `Inc` route: a prefix of
`cd.incRight` is either already a prefix of `cd`, or its right side reaches the
whole final right derivation while its left side remains a prefix of `cd`.
-/
theorem incRight_prefix_cases {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) {t' : Time}
    (hlt : (cd.rightTime j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (cd.rightTime j) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t')
    {pref : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix (cd.incRight j hlt hflag hconsistent)) :
    pref.IsInitialPrefix cd ∨
      (InitialPrefix pref.leftDerivation cd.leftDerivation ∧
        InitialPrefix (cd.incRight j hlt hflag hconsistent).rightDerivation
          pref.rightDerivation) := by
  rcases
      InitialPrefix.inc_cases (cd.rightIndex j) hlt hflag hconsistent hprefix.2 with
    hbefore | hafter
  · exact Or.inl
      ⟨by simpa [incRight] using hprefix.1, hbefore⟩
  · exact Or.inr
      ⟨by simpa [incRight] using hprefix.1, hafter⟩

/--
Circuit-prefix support for the one-sided final Cut route: a prefix of
`cd.cutLeft` is either already a prefix of `cd`, or its left side reaches the
whole final left Cut derivation while its right side remains a prefix of `cd`.
-/
theorem cutLeft_prefix_cases {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    {i j k : cd.circuit.left.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : cd.circuit.left.1.get k = ⋉ (cd.circuit.left.1.paperIndex j) tk)
    (hj : cd.circuit.left.1.get j =
      ⋊ (cd.circuit.left.1.paperIndex i)
        (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk)))
    (hi : cd.circuit.left.1.get i =
      ti # (⋊ (cd.circuit.left.1.paperIndex i)
          (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk))))
    (hconsistent :
      ConsistentTime
        (↱ (cd.circuit.left.1.paperIndex i) tk))
    {pref : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix (cd.cutLeft hij hjk hk hj hi hconsistent)) :
    pref.IsInitialPrefix cd ∨
      (InitialPrefix
          (cd.cutLeft hij hjk hk hj hi hconsistent).leftDerivation
          pref.leftDerivation ∧
        InitialPrefix pref.rightDerivation cd.rightDerivation) := by
  let leftCut :=
    Derivation.cut cd.leftDerivation hij hjk hk hj hi hconsistent
  have hleftStep :
      InitialPrefix cd.leftDerivation leftCut := by
    exact InitialPrefix.cut cd.leftDerivation (InitialPrefix.refl cd.leftDerivation)
      hij hjk hk hj hi hconsistent
  rcases
      InitialPrefix.immediate_extension_cases hleftStep
        (by simpa [cutLeft, leftCut] using hprefix.1) rfl with
    hbefore | hafter
  · exact Or.inl
      ⟨hbefore, by simpa [cutLeft] using hprefix.2⟩
  · exact Or.inr
      ⟨by simpa [cutLeft, leftCut] using hafter,
        by simpa [cutLeft] using hprefix.2⟩

/--
Circuit-prefix support for the one-sided final-`⋉Intro` route: a prefix
of `cd.cutYouIntroRight` is either already a prefix of `cd`, or its right side
reaches the whole final right derivation while its left side remains a prefix
of `cd`.
-/
theorem cutYouIntroRight_prefix_cases {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) (target : Nat) {t : Time}
    (hshape : cd.rightTime j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t))
    {pref : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix
      (cd.cutYouIntroRight j target hshape hconsistent)) :
    pref.IsInitialPrefix cd ∨
      (InitialPrefix pref.leftDerivation cd.leftDerivation ∧
        InitialPrefix
          (cd.cutYouIntroRight j target hshape hconsistent).rightDerivation
          pref.rightDerivation) := by
  let rightIdx := cd.rightIndex j
  let rightIntro :=
    Derivation.cutYouIntro cd.rightDerivation rightIdx target hshape hconsistent
  have hrightStep :
      InitialPrefix cd.rightDerivation rightIntro := by
    exact InitialPrefix.cutYouIntro cd.rightDerivation
      (InitialPrefix.refl cd.rightDerivation) rightIdx target hshape hconsistent
  rcases
      InitialPrefix.immediate_extension_cases hrightStep
        (by simpa [cutYouIntroRight, rightIntro, rightIdx] using hprefix.2) rfl with
    hbefore | hafter
  · exact Or.inl
      ⟨by simpa [cutYouIntroRight] using hprefix.1, hbefore⟩
  · exact Or.inr
      ⟨by simpa [cutYouIntroRight] using hprefix.1,
        by simpa [cutYouIntroRight, rightIntro, rightIdx] using hafter⟩

theorem IsInitialPrefix.trans {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {pref mid cd : CircuitDerivation Time}
    (hpm : pref.IsInitialPrefix mid) (hmc : mid.IsInitialPrefix cd) :
    pref.IsInitialPrefix cd := by
  exact ⟨InitialPrefix.trans hpm.1 hmc.1, InitialPrefix.trans hpm.2 hmc.2⟩

/--
Paired initial prefixes of a circuit derivation preserve the circuit
controller-equality condition before the last index.
-/
theorem initialPrefix_controller_eq_before_last {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    {TL TR : Prepath Time}
    {leftPref : Derivation Time TL} {rightPref : Derivation Time TR}
    (hleft : InitialPrefix leftPref cd.leftDerivation)
    (hright : InitialPrefix rightPref cd.rightDerivation) :
    let hlen : TL.length = TR.length :=
      (InitialPrefix.length_eq hleft).trans
        (cd.circuit.length_eq.trans (InitialPrefix.length_eq hright).symm)
    ∀ i : TL.Index, TL.paperIndex i < TL.length →
      controller (TL.get i) =
        controller (TR.get (Fin.cast hlen i)) := by
  intro hlen i hi
  let iLeftFinal : cd.circuit.left.1.Index :=
    Fin.cast (InitialPrefix.length_eq hleft) i
  let iRightPref : TR.Index := Fin.cast hlen i
  let iRightFinal : cd.circuit.right.1.Index :=
    Fin.cast (InitialPrefix.length_eq hright) iRightPref
  have hleftCtrl :
      controller (TL.get i) =
        controller (cd.circuit.left.1.get iLeftFinal) := by
    have hle := InitialPrefix.times_increase hleft i
    simpa [iLeftFinal] using hle.1
  have hiFinal : cd.circuit.left.1.paperIndex iLeftFinal < cd.circuit.length := by
    have hlenLeft : TL.length = cd.circuit.left.1.length :=
      InitialPrefix.length_eq hleft
    change i.val + 1 < cd.circuit.left.1.length
    simpa [Prepath.paperIndex, Circuit.length, hlenLeft] using hi
  have hrightFinal_eq :
      iRightFinal = Fin.cast cd.circuit.length_eq iLeftFinal := by
    apply Fin.ext
    rfl
  have hcircuit :
      controller (cd.circuit.left.1.get iLeftFinal) =
        controller (cd.circuit.right.1.get iRightFinal) := by
    simpa [hrightFinal_eq] using
      cd.circuit.controller_eq_before_last iLeftFinal hiFinal
  have hrightCtrl :
      controller (TR.get iRightPref) =
        controller (cd.circuit.right.1.get iRightFinal) := by
    have hle := InitialPrefix.times_increase hright iRightPref
    simpa [iRightFinal] using hle.1
  exact hleftCtrl.trans (hcircuit.trans hrightCtrl.symm)

/--
Circuit derivation formed from paired initial prefixes of a circuit derivation.
-/
def initialPrefixDerivation {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {TL TR : Prepath Time}
    (leftPref : Derivation Time TL) (rightPref : Derivation Time TR)
    (hleft : InitialPrefix leftPref cd.leftDerivation)
    (hright : InitialPrefix rightPref cd.rightDerivation) : CircuitDerivation Time :=
  let hlen : TL.length = TR.length :=
    (InitialPrefix.length_eq hleft).trans
      (cd.circuit.length_eq.trans (InitialPrefix.length_eq hright).symm)
  { circuit :=
      { left := ⟨TL, ⟨leftPref⟩⟩
        right := ⟨TR, ⟨rightPref⟩⟩
        length_eq := hlen
        controller_eq_before_last := by
          intro i hi
          exact cd.initialPrefix_controller_eq_before_last hleft hright i hi }
    leftDerivation := leftPref
    rightDerivation := rightPref }

theorem initialPrefixDerivation_isInitialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {TL TR : Prepath Time}
    (leftPref : Derivation Time TL) (rightPref : Derivation Time TR)
    (hleft : InitialPrefix leftPref cd.leftDerivation)
    (hright : InitialPrefix rightPref cd.rightDerivation) :
    (cd.initialPrefixDerivation leftPref rightPref hleft hright).IsInitialPrefix cd := by
  exact ⟨hleft, hright⟩

/-- Cast a final circuit index back to an initial-prefix circuit index. -/
def prefixIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {pref cd : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix cd) (i : cd.Index) : pref.Index :=
  Fin.cast (InitialPrefix.length_eq hprefix.1).symm i

theorem prefixIndex_val {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {pref cd : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix cd) (i : cd.Index) :
    (pref.prefixIndex hprefix i).val = i.val := by
  rfl

theorem prefixIndex_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {pref cd : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix cd) (i : cd.Index) :
    pref.circuit.left.1.paperIndex (pref.prefixIndex hprefix i) =
      cd.circuit.left.1.paperIndex i := by
  simp [Prepath.paperIndex, prefixIndex]

/-- Lemma 4.2.2 (Times increase) on the left path: the left time at an index in
an initial prefix is `≼` the left time at that index in the whole circuit
derivation. -/
theorem leftTime_increases_from_prefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {pref cd : CircuitDerivation Time} (hprefix : pref.IsInitialPrefix cd)
    (i : cd.Index) :
    (pref.leftTime (pref.prefixIndex hprefix i)) ≼ (cd.leftTime i) := by
  have hleft_raw := InitialPrefix.times_increase hprefix.1 (pref.prefixIndex hprefix i)
  simpa [leftTime, prefixIndex] using hleft_raw

/-- Lemma 4.2.2 (Times increase) on the right path: the right time at an index in
an initial prefix is `≼` the right time at that index in the whole circuit
derivation. -/
theorem rightTime_increases_from_prefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {pref cd : CircuitDerivation Time} (hprefix : pref.IsInitialPrefix cd)
    (i : cd.Index) :
    (pref.rightTime (pref.prefixIndex hprefix i)) ≼ (cd.rightTime i) := by
  have hright_raw := InitialPrefix.times_increase hprefix.2
    (pref.rightIndex (pref.prefixIndex hprefix i))
  simpa [rightTime, rightIndex, prefixIndex] using hright_raw

/--
Definition 4.3.2(1): index `j` is inconsistent in a circuit-derivation `(Π, Π')`
when there are initial prefixes `Π₁` of `Π` and `Π₁'` of `Π'` such that `j` is
doubly active in `(Π₁, Π₁')` and `Π₁[j] 🗲 Π₁'[j]`.
-/
def InconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) : Prop :=
  ∃ pref : CircuitDerivation Time, ∃ hprefix : pref.IsInitialPrefix cd,
    let iprefix := pref.prefixIndex hprefix i
    pref.DoublyActive iprefix ∧ (pref.leftTime iprefix) 🗲 (pref.rightTime iprefix)

/--
Definition 4.3.2(1): the defining condition of an inconsistent index, named
explicitly — the existence of an initial-prefix witness that is doubly active at
the index and contradictory there.
-/
def DoublyActiveContradictoryPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index) : Prop :=
  ∃ pref : CircuitDerivation Time, ∃ hprefix : pref.IsInitialPrefix cd,
    let iprefix := pref.prefixIndex hprefix i
    pref.DoublyActive iprefix ∧ (pref.leftTime iprefix) 🗲 (pref.rightTime iprefix)

/--
Definition 4.3.2(1) (see Remark 4.3.3(2)): being inconsistent is exactly the
existence of a doubly-active contradictory initial-prefix witness, a strictly
stronger condition than a final contradiction at the index.
-/
theorem inconsistentIndex_iff_doublyActiveContradictoryPrefix
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index) :
    cd.InconsistentIndex i ↔ cd.DoublyActiveContradictoryPrefix i :=
  Iff.rfl

theorem final_contradiction_not_inconsistent_of_left_inactive_in_every_prefix
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hleftInactive :
      ∀ pref : CircuitDerivation Time, ∀ hprefix : pref.IsInitialPrefix cd,
        pref.leftDerivation.Inactive (pref.prefixIndex hprefix i)) :
    (cd.leftTime i) 🗲 (cd.rightTime i) →
      ¬ cd.InconsistentIndex i := by
  intro _hfinal hinconsistent
  rcases hinconsistent with ⟨pref, hprefix, hactive, _hcontr⟩
  exact hactive.1 (hleftInactive pref hprefix)

/--
Remark 4.3.3(2): a final contradiction at an index need not make it inconsistent.
Here, if the right side is inactive at the index in every initial prefix, then no
doubly-active contradictory prefix exists, so the index is not inconsistent.
-/
theorem final_contradiction_not_inconsistent_of_right_inactive_in_every_prefix
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hrightInactive :
      ∀ pref : CircuitDerivation Time, ∀ hprefix : pref.IsInitialPrefix cd,
        pref.rightDerivation.Inactive
          (pref.rightIndex (pref.prefixIndex hprefix i))) :
    (cd.leftTime i) 🗲 (cd.rightTime i) →
      ¬ cd.InconsistentIndex i := by
  intro _hfinal hinconsistent
  rcases hinconsistent with ⟨pref, hprefix, hactive, _hcontr⟩
  exact hactive.2 (hrightInactive pref hprefix)

/--
Remark 4.3.3(2): to show a final-contradictory index is not inconsistent, it
suffices that no contradictory initial prefix is doubly active at that index.
-/
theorem not_inconsistentIndex_of_prefix_contradictions_not_doublyActive
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hprefixContr :
      ∀ pref : CircuitDerivation Time, ∀ hprefix : pref.IsInitialPrefix cd,
        (pref.leftTime (pref.prefixIndex hprefix i)) 🗲 (pref.rightTime (pref.prefixIndex hprefix i)) →
          ¬ pref.DoublyActive (pref.prefixIndex hprefix i)) :
    ¬ cd.InconsistentIndex i := by
  intro hinconsistent
  rcases hinconsistent with ⟨pref, hprefix, hactive, hcontr⟩
  exact hprefixContr pref hprefix hcontr hactive

/--
Remark 4.3.3(2): a more concrete sufficient condition — if every contradictory
initial prefix is already inactive on at least one side at the index, then the
index is not inconsistent.
-/
theorem not_inconsistentIndex_of_prefix_contradictions_left_or_right_inactive
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {i : cd.Index}
    (hprefixContr :
      ∀ pref : CircuitDerivation Time, ∀ hprefix : pref.IsInitialPrefix cd,
        (pref.leftTime (pref.prefixIndex hprefix i)) 🗲 (pref.rightTime (pref.prefixIndex hprefix i)) →
          pref.leftDerivation.Inactive (pref.prefixIndex hprefix i) ∨
            pref.rightDerivation.Inactive
              (pref.rightIndex (pref.prefixIndex hprefix i))) :
    ¬ cd.InconsistentIndex i := by
  refine cd.not_inconsistentIndex_of_prefix_contradictions_not_doublyActive ?_
  intro pref hprefix hcontr hactive
  rcases hprefixContr pref hprefix hcontr with hleft | hright
  · exact hactive.1 hleft
  · exact hactive.2 hright

theorem not_inconsistentIndex_of_incRight_left_prefix_contradictions_inactive
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index)
    {t' : Time}
    (hlt : (cd.rightTime i) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (cd.rightTime i) =
        flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t')
    (hleftPrefixContr :
      ∀ {Tpref : Prepath Time} (leftPref : Derivation Time Tpref),
        ∀ hleft : InitialPrefix leftPref cd.leftDerivation,
          (leftPref.get (Fin.cast (InitialPrefix.length_eq hleft).symm i)) 🗲 t' →
            leftPref.Inactive
              (Fin.cast (InitialPrefix.length_eq hleft).symm i)) :
    let finalCd := cd.incRight i hlt hflag hconsistent
    (finalCd.leftTime i) 🗲 (finalCd.rightTime i) →
      ¬ finalCd.InconsistentIndex i := by
  intro finalCd hfinal
  refine
    finalCd.not_inconsistentIndex_of_prefix_contradictions_left_or_right_inactive
      ?_
  intro pref hprefix hcontr
  have hright_le_final :
      (pref.rightTime (pref.prefixIndex hprefix i)) ≼ (finalCd.rightTime i) :=
    CircuitDerivation.rightTime_increases_from_prefix hprefix i
  have hcontr_final :
      (pref.leftTime (pref.prefixIndex hprefix i)) 🗲 t' := by
    have hmono := contradicts_of_le_right hright_le_final hcontr
    simpa [finalCd] using hmono
  have hleft_prefix :
      InitialPrefix pref.leftDerivation cd.leftDerivation := by
    rcases
        cd.incRight_prefix_cases i hlt hflag hconsistent hprefix with
      hbefore | hafter
    · exact hbefore.1
    · exact hafter.1
  have hidx :
      Fin.cast (InitialPrefix.length_eq hleft_prefix).symm i =
        pref.prefixIndex hprefix i := by
    apply Fin.ext
    rfl
  have hleftInactive :=
    hleftPrefixContr pref.leftDerivation hleft_prefix (by
      simpa [leftTime, hidx] using hcontr_final)
  exact Or.inl (by simpa [hidx] using hleftInactive)

theorem not_inconsistentIndex_of_cutYouIntroRight_left_prefix_contradictions_inactive
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index)
    (target : Nat) {t : Time}
    (hshape : cd.rightTime i = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t))
    (hleftPrefixContr :
      ∀ {Tpref : Prepath Time} (leftPref : Derivation Time Tpref),
        ∀ hleft : InitialPrefix leftPref cd.leftDerivation,
          (leftPref.get (Fin.cast (InitialPrefix.length_eq hleft).symm i)) 🗲 (⋉ target t) →
            leftPref.Inactive
              (Fin.cast (InitialPrefix.length_eq hleft).symm i)) :
    let finalCd := cd.cutYouIntroRight i target hshape hconsistent
    (finalCd.leftTime i) 🗲 (finalCd.rightTime i) →
      ¬ finalCd.InconsistentIndex i := by
  intro finalCd hfinal
  refine
    finalCd.not_inconsistentIndex_of_prefix_contradictions_left_or_right_inactive
      ?_
  intro pref hprefix hcontr
  have hright_le_final :
      (pref.rightTime (pref.prefixIndex hprefix i)) ≼ (finalCd.rightTime i) :=
    CircuitDerivation.rightTime_increases_from_prefix hprefix i
  have hcontr_final :
      (pref.leftTime (pref.prefixIndex hprefix i)) 🗲 (⋉ target t) := by
    have hmono := contradicts_of_le_right hright_le_final hcontr
    simpa [finalCd] using hmono
  have hleft_prefix :
      InitialPrefix pref.leftDerivation cd.leftDerivation := by
    rcases
        cd.cutYouIntroRight_prefix_cases i target hshape hconsistent hprefix with
      hbefore | hafter
    · exact hbefore.1
    · exact hafter.1
  have hidx :
      Fin.cast (InitialPrefix.length_eq hleft_prefix).symm i =
        pref.prefixIndex hprefix i := by
    apply Fin.ext
    rfl
  have hleftInactive :=
    hleftPrefixContr pref.leftDerivation hleft_prefix (by
      simpa [leftTime, hidx] using hcontr_final)
  exact Or.inl (by simpa [hidx] using hleftInactive)

theorem preCut_center_contradicts_same_target_cutYou_of_cutMe
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (i : cd.Index)
    (target : Nat) {base rightBase : Time}
    (hcenter : cd.leftTime i = ⋊ target base)
    (hctrl : controller base = controller rightBase) :
    (cd.leftTime i) 🗲 (⋉ target rightBase) := by
  rw [hcenter]
  exact cutMe_contradicts_cutYou target hctrl

/--
If the pre-Cut left time at an index does not contradict `right'`, then no
initial-prefix left time at that index contradicts `right'` either: initial-prefix
times only increase (Lemma 4.2.2) and contradiction is monotone upward on the
left.
-/
theorem left_prefix_no_contradiction_of_center_no_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) (j : cd.Index)
    {right' : Time}
    (hcenter :
      ¬ (cd.leftTime j) 🗲 right') :
    ∀ {Tpref : Prepath Time} (leftPref : Derivation Time Tpref),
      ∀ hleft : InitialPrefix leftPref cd.leftDerivation,
        (leftPref.get (Fin.cast (InitialPrefix.length_eq hleft).symm j)) 🗲 right' →
          False := by
  intro _Tpref leftPref hleft hcontr
  let prefIndex : leftPref.Index :=
    Fin.cast (InitialPrefix.length_eq hleft).symm j
  have hcast :
      Fin.cast (InitialPrefix.length_eq hleft) prefIndex = j := by
    apply Fin.ext
    rfl
  have hle :
      (leftPref.get prefIndex) ≼ (cd.leftDerivation.get j) := by
    have hraw := InitialPrefix.derivation_times_increase hleft prefIndex
    simpa [prefIndex, hcast] using hraw
  exact hcenter
    (contradicts_of_le_left hle (by
      simpa [prefIndex] using hcontr))

theorem cutLeft_cutYouIntroRight_center_no_contradiction_final_impossible
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j k : cd.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : cd.circuit.left.1.get k =
      ⋉ (cd.circuit.left.1.paperIndex j) tk)
    (hj : cd.circuit.left.1.get j =
      ⋊ (cd.circuit.left.1.paperIndex i)
        (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk)))
    (hi : cd.circuit.left.1.get i =
      ti # (⋊ (cd.circuit.left.1.paperIndex i)
          (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk))))
    (hcutCons :
      ConsistentTime
        (↱ (cd.circuit.left.1.paperIndex i) tk))
    (target : Nat) {t : Time}
    (hshape :
      (cd.cutLeft hij hjk hk hj hi hcutCons).rightTime j =
        ↱ target t)
    (hrightCons : ConsistentTime (⋉ target t))
    (hpreCutCenterNoContr :
      ¬ (cd.leftTime j) 🗲 (⋉ target t))
    (hfinal :
      let cutCd := cd.cutLeft hij hjk hk hj hi hcutCons
      let finalCd := cutCd.cutYouIntroRight j target hshape hrightCons
      (finalCd.leftTime j) 🗲 (finalCd.rightTime j)) :
    False := by
  exact hpreCutCenterNoContr (by simpa using hfinal)

theorem three_index_cut_data_infinite_interval_of_center_consistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {tj tk : Time}
    (hcenterCons :
      ConsistentTime
        (⋊ 1
          (tj # (⋉ 2 tk)))) :
    ∃ f : Nat → Time,
      Function.Injective f ∧
        ∀ offset : Nat,
          ConsistentTime (f offset) ∧
            (tj # (⋉ 2 tk)) ≼ (f offset) ∧
              (f offset) ≼ (↱ 1
                  (tj # (⋉ 2 tk))) := by
  exact
    cutYou_successor_infinite_consistent_interval_of_cutMe_consistent
      hcenterCons

/--
Finite-carrier obstruction for the three-index Cut route: the consistent
pre-Cut center already supplies an injective `Nat`-indexed family of Cut times.
Thus any explicit witness cannot be built on a carrier that admits no injective
`Nat` sequence.
-/
theorem three_index_cut_data_center_consistent_not_dedekind_finite
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {tj tk : Time}
    (hnoNatInjection : ∀ f : Nat → Time, ¬ Function.Injective f)
    (hcenterCons :
      ConsistentTime
        (⋊ 1
          (tj # (⋉ 2 tk)))) :
    False := by
  rcases
      three_index_cut_data_infinite_interval_of_center_consistent
        hcenterCons with
    ⟨f, hinj, _hinterval⟩
  exact hnoNatInjection f hinj

/--
Flag-form bridge for the three-index Cut route: the pre-Cut
center has exactly the `⋊ 1` cutting flag.
-/
theorem three_index_center_flagOf_cutMe_one
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {tj tk : Time}
    (hcenterCons :
      ConsistentTime
        (⋊ 1
          (tj # (⋉ 2 tk)))) :
    flagOf cuttingFlagSet
        (⋊ 1
          (tj # (⋉ 2 tk))) =
      some ⟨⋊ 1, cutMe_mem 1⟩ := by
  exact
    flagOf_eq_some_of_hasForm cuttingFlagSet
      (cutMe_mem 1)
      ⟨hcenterCons,
        ⟨tj # (⋉ 2 tk), rfl⟩⟩

/--
Flag-form bridge for the three-index Cut route: any successor
whose `flagOf` agrees with the pre-Cut center is an actual output of the same
`⋊ 1` cutting flag.
-/
theorem three_index_same_flag_successor_has_cutMe_one_form
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {tj tk successor : Time}
    (hcenterCons :
      ConsistentTime
        (⋊ 1
          (tj # (⋉ 2 tk))))
    (hflag :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet successor) :
    HasForm (⋊ 1) successor := by
  have hcenterFlag :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        some ⟨⋊ 1, cutMe_mem 1⟩ :=
    three_index_center_flagOf_cutMe_one hcenterCons
  have hsuccessorFlag :
      flagOf cuttingFlagSet successor =
        some ⟨⋊ 1, cutMe_mem 1⟩ := by
    rw [← hflag]
    exact hcenterFlag
  exact flagOf_eq_some_hasForm cuttingFlagSet hsuccessorFlag

/--
Model-obligation bridge for the three-index Cut route: the two
same-flag final successors required by the route are two concrete outputs of
the same `⋊ 1` cutting flag.
-/
theorem three_index_same_flag_successors_are_cutMe_one_outputs
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {tj tk left' right' : Time}
    (hcenterCons :
      ConsistentTime
        (⋊ 1
          (tj # (⋉ 2 tk))))
    (hflagLeft :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet left')
    (hflagRight :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet right') :
    (∃ leftBase : Time, left' = ⋊ 1 leftBase) ∧
      ∃ rightBase : Time, right' = ⋊ 1 rightBase := by
  constructor
  · exact
      hasForm_exists_eq
        (three_index_same_flag_successor_has_cutMe_one_form
          hcenterCons hflagLeft)
  · exact
      hasForm_exists_eq
        (three_index_same_flag_successor_has_cutMe_one_form
          hcenterCons hflagRight)

/--
Model-obligation bridge for the three-index Cut route: its final
contradiction, if supplied by same-flag successors, is a contradiction between
two outputs of the same `⋊ 1` cutting flag.
-/
theorem three_index_same_flag_final_contradiction_cutMe_one_outputs
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {tj tk left' right' : Time}
    (hcenterCons :
      ConsistentTime
        (⋊ 1
          (tj # (⋉ 2 tk))))
    (hflagLeft :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet left')
    (hflagRight :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet right')
    (hfinal : left' 🗲 right') :
    ∃ leftBase rightBase : Time,
      left' = ⋊ 1 leftBase ∧
        right' = ⋊ 1 rightBase ∧
          (⋊ 1 leftBase) 🗲 (⋊ 1 rightBase) := by
  rcases
      three_index_same_flag_successors_are_cutMe_one_outputs
        hcenterCons hflagLeft hflagRight with
    ⟨⟨leftBase, hleft⟩, ⟨rightBase, hright⟩⟩
  refine ⟨leftBase, rightBase, hleft, hright, ?_⟩
  simpa [hleft, hright] using hfinal

/--
Model-obligation bridge for the three-index Cut route: under an explicit
sequentiality hypothesis, the contradictory same-flag final successors required
by the route are incomparable consistent outputs of the same `⋊ 1` flag.
-/
theorem three_index_same_flag_final_contradiction_cutMe_one_outputs_incomparable
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {tj tk left' right' : Time}
    (hseq : Sequential (Time := Time))
    (hcenterCons :
      ConsistentTime
        (⋊ 1
          (tj # (⋉ 2 tk))))
    (hflagLeft :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet left')
    (hflagRight :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet right')
    (hleftCons : ConsistentTime left')
    (hrightCons : ConsistentTime right')
    (hfinal : left' 🗲 right') :
    ∃ leftBase rightBase : Time,
      left' = ⋊ 1 leftBase ∧
        right' = ⋊ 1 rightBase ∧
          (¬ (⋊ 1 leftBase) ≼ (⋊ 1 rightBase)) ∧
            (¬ (⋊ 1 rightBase) ≼ (⋊ 1 leftBase)) ∧
              (⋊ 1 leftBase) 🗲 (⋊ 1 rightBase) := by
  rcases
      three_index_same_flag_final_contradiction_cutMe_one_outputs
        hcenterCons hflagLeft hflagRight hfinal with
    ⟨leftBase, rightBase, hleft, hright, hcontr⟩
  have hinc :
      ¬ left' ≼ right' ∧ ¬ right' ≼ left' := by
    exact
      incomparable_of_same_controller_contradicts_consistentTime
        hseq (p := controller left') rfl hfinal.1.symm
        hleftCons hrightCons hfinal
  refine ⟨leftBase, rightBase, hleft, hright, ?_, ?_, hcontr⟩
  · intro hle
    exact hinc.1 (by simpa [hleft, hright] using hle)
  · intro hle
    exact hinc.2 (by simpa [hleft, hright] using hle)

/--
Exact local model shape still needed by the three-index Cut
route: the route's hypotheses force a `⋊ 1` branching pattern, with the
center below both same-flag branches, the right branch noncontradictory with
the center, and the two branch endpoints contradictory and incomparable.
-/
theorem three_index_same_flag_route_forces_cutMe_one_branching
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {tj tk left' right' : Time}
    (hseq : Sequential (Time := Time))
    (hcenterCons :
      ConsistentTime
        (⋊ 1
          (tj # (⋉ 2 tk))))
    (hltLeft :
      (⋊ 1
          (tj # (⋉ 2 tk))) ≺ left')
    (hflagLeft :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet left')
    (hleftCons : ConsistentTime left')
    (hltRight :
      (⋊ 1
          (tj # (⋉ 2 tk))) ≺ right')
    (hflagRight :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet right')
    (hrightCons : ConsistentTime right')
    (hpreCutCenterNoContr :
      ¬ (⋊ 1
            (tj # (⋉ 2 tk))) 🗲 right')
    (hfinal : left' 🗲 right') :
    ∃ centerBase leftBase rightBase : Time,
      ⋊ 1
          (tj # (⋉ 2 tk)) =
        ⋊ 1 centerBase ∧
        left' = ⋊ 1 leftBase ∧
          right' = ⋊ 1 rightBase ∧
            (⋊ 1 centerBase) ≺ (⋊ 1 leftBase) ∧
              (⋊ 1 centerBase) ≺ (⋊ 1 rightBase) ∧
                (¬ (⋊ 1 centerBase) 🗲 (⋊ 1 rightBase)) ∧
                  (¬ (⋊ 1 leftBase) ≼ (⋊ 1 rightBase)) ∧
                    (¬ (⋊ 1 rightBase) ≼ (⋊ 1 leftBase)) ∧
                      (⋊ 1 leftBase) 🗲 (⋊ 1 rightBase) := by
  let centerBase : Time :=
    tj # (⋉ 2 tk)
  rcases
      three_index_same_flag_final_contradiction_cutMe_one_outputs_incomparable
        hseq hcenterCons hflagLeft hflagRight hleftCons hrightCons hfinal with
    ⟨leftBase, rightBase, hleft, hright, hincLeftRight,
      hincRightLeft, hcontr⟩
  refine
    ⟨centerBase, leftBase, rightBase, rfl, hleft, hright, ?_, ?_, ?_,
      hincLeftRight, hincRightLeft, hcontr⟩
  · simpa [centerBase, hleft] using hltLeft
  · simpa [centerBase, hright] using hltRight
  · simpa [centerBase, hright] using hpreCutCenterNoContr

/--
Model-obligation bridge for the three-index Cut route: if either
same-flag branch base lies below the center base, then the `⋊ 1` cutting
operator cannot be monotone on all bases. This records a structural constraint
on any model realising the three-index Cut route.
-/
theorem three_index_same_flag_route_forces_cutMe_one_nonmonotone_if_branch_base_le
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {tj tk left' right' : Time}
    (hseq : Sequential (Time := Time))
    (hcenterCons :
      ConsistentTime
        (⋊ 1
          (tj # (⋉ 2 tk))))
    (hltLeft :
      (⋊ 1
          (tj # (⋉ 2 tk))) ≺ left')
    (hflagLeft :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet left')
    (hleftCons : ConsistentTime left')
    (hltRight :
      (⋊ 1
          (tj # (⋉ 2 tk))) ≺ right')
    (hflagRight :
      flagOf cuttingFlagSet
          (⋊ 1
            (tj # (⋉ 2 tk))) =
        flagOf cuttingFlagSet right')
    (hrightCons : ConsistentTime right')
    (hpreCutCenterNoContr :
      ¬ (⋊ 1
            (tj # (⋉ 2 tk))) 🗲 right')
    (hfinal : left' 🗲 right') :
    ∃ centerBase leftBase rightBase : Time,
      ⋊ 1
          (tj # (⋉ 2 tk)) =
        ⋊ 1 centerBase ∧
        left' = ⋊ 1 leftBase ∧
          right' = ⋊ 1 rightBase ∧
            (leftBase ≼ centerBase →
              ¬ ∀ {a b : Time}, a ≼ b →
                (⋊ 1 a) ≼ (⋊ 1 b)) ∧
              (rightBase ≼ centerBase →
                ¬ ∀ {a b : Time}, a ≼ b →
                  (⋊ 1 a) ≼ (⋊ 1 b)) := by
  rcases
      three_index_same_flag_route_forces_cutMe_one_branching
        hseq hcenterCons hltLeft hflagLeft hleftCons hltRight hflagRight
        hrightCons hpreCutCenterNoContr hfinal with
    ⟨centerBase, leftBase, rightBase, hcenter, hleft, hright, hltCenterLeft,
      hltCenterRight, _hnoCenterRight, _hincLeftRight, _hincRightLeft,
      _hcontr⟩
  refine ⟨centerBase, leftBase, rightBase, hcenter, hleft, hright, ?_, ?_⟩
  · intro hbaseLe hmono
    have hleftCenter :
        (⋊ 1 leftBase) ≼ (⋊ 1 centerBase) :=
      hmono hbaseLe
    have heq :
        ⋊ 1 centerBase = ⋊ 1 leftBase :=
      le_antisymm hltCenterLeft.1 hleftCenter
    exact hltCenterLeft.2 heq
  · intro hbaseLe hmono
    have hrightCenter :
        (⋊ 1 rightBase) ≼ (⋊ 1 centerBase) :=
      hmono hbaseLe
    have heq :
        ⋊ 1 centerBase = ⋊ 1 rightBase :=
      le_antisymm hltCenterRight.1 hrightCenter
    exact hltCenterRight.2 heq

/--
Remark 4.3.3(1): an inconsistent index need not be active. A synchronized pair
of final Cut steps centered at a doubly-active contradictory index makes that
center inconsistent by its pre-Cut prefix witness (Definition 4.3.2(1)), yet
inactive in the final circuit derivation.
-/
theorem cutPair_center_inconsistent_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    {i j k : cd.Index} {i' j' k' : cd.circuit.right.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    (hij' : i'.val < j'.val) (hjk' : j'.val < k'.val)
    {ti tj tk ti' tj' tk' : Time}
    (hk : cd.circuit.left.1.get k = ⋉ (cd.circuit.left.1.paperIndex j) tk)
    (hj : cd.circuit.left.1.get j =
      ⋊ (cd.circuit.left.1.paperIndex i)
        (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk)))
    (hi : cd.circuit.left.1.get i =
      ti # (⋊ (cd.circuit.left.1.paperIndex i)
          (tj # (⋉ (cd.circuit.left.1.paperIndex j) tk))))
    (hconsistent :
      ConsistentTime
        (↱ (cd.circuit.left.1.paperIndex i) tk))
    (hk' : cd.circuit.right.1.get k' =
      ⋉ (cd.circuit.right.1.paperIndex j') tk')
    (hj' : cd.circuit.right.1.get j' =
      ⋊ (cd.circuit.right.1.paperIndex i')
        (tj' # (⋉ (cd.circuit.right.1.paperIndex j') tk')))
    (hi' : cd.circuit.right.1.get i' =
      ti' # (⋊ (cd.circuit.right.1.paperIndex i')
          (tj' # (⋉ (cd.circuit.right.1.paperIndex j') tk'))))
    (hconsistent' :
      ConsistentTime
        (↱ (cd.circuit.right.1.paperIndex i') tk'))
    (hcenterRight : j' = cd.rightIndex j)
    (hactiveCenter : cd.DoublyActive j)
    (hcontrCenter : (cd.leftTime j) 🗲 (cd.rightTime j)) :
    let cutCd :=
      cd.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
        hconsistent'
    cutCd.InconsistentIndex j ∧ cutCd.Inactive j ∧ ¬ cutCd.Active j := by
  let cutCd :=
    cd.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
      hconsistent'
  have hprefix : cd.IsInitialPrefix cutCd := by
    constructor
    · simpa [cutCd, CircuitDerivation.cutPair] using
        (InitialPrefix.cut cd.leftDerivation
          (InitialPrefix.refl cd.leftDerivation) hij hjk hk hj hi hconsistent)
    · simpa [cutCd, CircuitDerivation.cutPair] using
        (InitialPrefix.cut cd.rightDerivation
          (InitialPrefix.refl cd.rightDerivation) hij' hjk' hk' hj' hi'
          hconsistent')
  have hinconsistent : cutCd.InconsistentIndex j := by
    refine ⟨cd, hprefix, ?_⟩
    simpa [CircuitDerivation.prefixIndex] using And.intro hactiveCenter hcontrCenter
  have hleftInactive : cutCd.leftDerivation.Inactive j := by
    refine ⟨k, i, ?_⟩
    refine ⟨hij, hjk, ?_⟩
    simpa [cutCd, CircuitDerivation.cutPair, Derivation.root,
      Prepath.replace_get_same, Prepath.replace_paperIndex] using
      (hasCutLabelAt_nextIndex (Time := Time) (cd.circuit.left.1.paperIndex i) tk)
  have hrightIndex_center : cutCd.rightIndex j = j' := by
    rw [hcenterRight]
    rfl
  have hrightInactive : cutCd.rightDerivation.Inactive j' := by
    refine ⟨k', i', ?_⟩
    refine ⟨hij', hjk', ?_⟩
    simpa [cutCd, CircuitDerivation.cutPair, Derivation.root,
      Prepath.replace_get_same, Prepath.replace_paperIndex] using
      (hasCutLabelAt_nextIndex (Time := Time) (cd.circuit.right.1.paperIndex i') tk')
  have hinactive : cutCd.Inactive j := by
    constructor
    · exact hleftInactive
    · rw [hrightIndex_center]
      exact hrightInactive
  exact ⟨hinconsistent, hinactive, cutCd.inactive_not_active hinactive⟩

/-- `Least` is the least inconsistent index no greater than `bound`. -/
def LeastInconsistentAtOrBelow {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (bound least : cd.Index) : Prop :=
  least.val ≤ bound.val ∧
    cd.InconsistentIndex least ∧
    ∀ l : cd.Index, l.val < least.val → ¬ cd.InconsistentIndex l

theorem leastInconsistentAtOrBelow_le_bound {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastInconsistentAtOrBelow bound least) :
    least.val ≤ bound.val :=
  h.1

theorem leastInconsistentAtOrBelow_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastInconsistentAtOrBelow bound least) :
    cd.InconsistentIndex least :=
  h.2.1

theorem leastInconsistentAtOrBelow_no_smaller {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastInconsistentAtOrBelow bound least) :
    ∀ l : cd.Index, l.val < least.val → ¬ cd.InconsistentIndex l :=
  h.2.2

/--
Definition 4.3.2 least-index component: the least inconsistent index no greater
than a bound is also no greater in paper index notation.
-/
theorem leastInconsistentAtOrBelow_paperIndex_le_bound {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastInconsistentAtOrBelow bound least) :
    cd.circuit.left.1.paperIndex least <= cd.circuit.left.1.paperIndex bound := by
  exact Nat.succ_le_succ (cd.leastInconsistentAtOrBelow_le_bound h)

/--
Definition 4.3.2 least-index component: no strictly smaller paper index is
inconsistent.
-/
theorem leastInconsistentAtOrBelow_no_smaller_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastInconsistentAtOrBelow bound least) :
    ∀ l : cd.Index,
      cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex least →
        ¬ cd.InconsistentIndex l := by
  intro l hlt
  exact cd.leastInconsistentAtOrBelow_no_smaller h l
    (Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hlt))

theorem exists_leastInconsistentAtOrBelow {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound : cd.Index}
    (hbound : cd.InconsistentIndex bound) :
    ∃ least : cd.Index, cd.LeastInconsistentAtOrBelow bound least := by
  classical
  by_cases hsmaller : ∃ l : cd.Index, l.val < bound.val ∧ cd.InconsistentIndex l
  · rcases hsmaller with ⟨smaller, hlt, hinc⟩
    rcases exists_leastInconsistentAtOrBelow cd hinc with ⟨least, hleast⟩
    rcases hleast with ⟨hle_smaller, hleast_inc, hleast_min⟩
    exact
      ⟨least,
        ⟨Nat.le_trans hle_smaller (Nat.le_of_lt hlt), hleast_inc, hleast_min⟩⟩
  · exact
      ⟨bound,
        ⟨Nat.le_refl bound.val, hbound, by
          intro l hlt hlinc
          exact hsmaller ⟨l, hlt, hlinc⟩⟩⟩
termination_by bound.val
decreasing_by exact hlt

/-- Definition 4.3.2(2): a circuit-derivation is inconsistent when it contains an
inconsistent index (Definition 4.3.2(1)). -/
def Inconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) : Prop :=
  ∃ i : cd.Index, cd.InconsistentIndex i

/-- Definition 4.3.2(2): a circuit-derivation is consistent (not inconsistent)
when it contains no inconsistent index. -/
def Consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) : Prop :=
  ¬ cd.Inconsistent

/-- Definition 4.3.2: consistency is non-inconsistency. -/
theorem consistent_iff_not_inconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    cd.Consistent ↔ ¬ cd.Inconsistent :=
  Iff.rfl

/-- Definition 4.3.2: inconsistency is existence of an inconsistent index. -/
theorem inconsistent_iff_exists_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    cd.Inconsistent ↔ ∃ i : cd.Index, cd.InconsistentIndex i :=
  Iff.rfl

/-- Definition 4.3.2: consistency is absence of inconsistent indexes. -/
theorem consistent_iff_no_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    cd.Consistent ↔ ∀ i : cd.Index, ¬ cd.InconsistentIndex i := by
  constructor
  · intro hconsistent i hinconsistent
    exact hconsistent ⟨i, hinconsistent⟩
  · intro hno hinconsistent
    rcases hinconsistent with ⟨i, hi⟩
    exact hno i hi

/-- Definition 4.3.2: an inconsistent index makes the circuit derivation inconsistent. -/
theorem inconsistent_of_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index} (h : cd.InconsistentIndex i) :
    cd.Inconsistent := by
  exact ⟨i, h⟩

/-- Definition 4.3.2: an inconsistent index rules out consistency. -/
theorem inconsistentIndex_not_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index} (h : cd.InconsistentIndex i) :
    ¬ cd.Consistent := by
  intro hconsistent
  exact hconsistent (cd.inconsistent_of_inconsistentIndex h)

/-- Definition 4.3.2: a consistent circuit derivation has no inconsistent index. -/
theorem consistent_no_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (h : cd.Consistent) (i : cd.Index) :
    ¬ cd.InconsistentIndex i := by
  intro hinc
  exact h (cd.inconsistent_of_inconsistentIndex hinc)

/-- Definition 4.3.2: consistency is non-inconsistency. -/
theorem not_inconsistent_of_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (h : cd.Consistent) : ¬ cd.Inconsistent := by
  exact h

/-- Definition 4.3.2: an inconsistent circuit derivation is not consistent. -/
theorem inconsistent_not_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (h : cd.Inconsistent) :
    ¬ cd.Consistent := by
  intro hconsistent
  exact hconsistent h

/-- Definition 4.3.2(3): an index is active inconsistent when it is active
(Definition 4.3.1(4)(b)) and inconsistent (Definition 4.3.2(1)). -/
def ActiveInconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (i : cd.Index) : Prop :=
  cd.Active i ∧ cd.InconsistentIndex i

/-- Definition 4.3.2(4): a circuit-derivation is active inconsistent when it
contains an active-inconsistent index (Definition 4.3.2(3)). -/
def ActiveInconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) : Prop :=
  ∃ i : cd.Index, cd.ActiveInconsistentIndex i

/-- Definition 4.3.2: active-inconsistent indexes are active and inconsistent. -/
theorem activeInconsistentIndex_iff_active_and_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (i : cd.Index) :
    cd.ActiveInconsistentIndex i ↔ cd.Active i ∧ cd.InconsistentIndex i :=
  Iff.rfl

/-- Definition 4.3.2: active inconsistency is existence of an active-inconsistent index. -/
theorem activeInconsistent_iff_exists_activeInconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    cd.ActiveInconsistent ↔ ∃ i : cd.Index, cd.ActiveInconsistentIndex i :=
  Iff.rfl

/-- Definition 4.3.2: active plus inconsistent is active inconsistent. -/
theorem activeInconsistentIndex_of_active_and_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hactive : cd.Active i) (hinc : cd.InconsistentIndex i) :
    cd.ActiveInconsistentIndex i := by
  exact ⟨hactive, hinc⟩

theorem activeInconsistentIndex_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (h : cd.ActiveInconsistentIndex i) :
    cd.Active i := by
  exact h.1

theorem activeInconsistentIndex_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (h : cd.ActiveInconsistentIndex i) :
    cd.InconsistentIndex i := by
  exact h.2

/-- Definition 4.3.2: an active-inconsistent index makes the circuit inconsistent. -/
theorem activeInconsistentIndex_inconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (h : cd.ActiveInconsistentIndex i) :
    cd.Inconsistent := by
  exact cd.inconsistent_of_inconsistentIndex h.2

/-- Definition 4.3.2: an active-inconsistent index rules out consistency. -/
theorem activeInconsistentIndex_not_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (h : cd.ActiveInconsistentIndex i) :
    ¬ cd.Consistent := by
  exact cd.inconsistent_not_consistent (cd.activeInconsistentIndex_inconsistent h)

/--
If an initial-prefix circuit derivation has the corresponding index active
inconsistent, then the final circuit derivation has that index inconsistent.
-/
theorem inconsistentIndex_of_initialPrefix_activeInconsistentIndex
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {pref cd : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix cd) (i : cd.Index)
    (hactiveInconsistent :
      pref.ActiveInconsistentIndex (pref.prefixIndex hprefix i)) :
    cd.InconsistentIndex i := by
  rcases hactiveInconsistent with ⟨_hactivePref, hinconsistentPref⟩
  rcases hinconsistentPref with ⟨subpref, hsubprefix, hactiveSub, hcontrSub⟩
  refine ⟨subpref, hsubprefix.trans hprefix, ?_⟩
  simpa [CircuitDerivation.prefixIndex] using And.intro hactiveSub hcontrSub

/--
Casted-index form of
`inconsistentIndex_of_initialPrefix_activeInconsistentIndex`, for data that is
naturally indexed in the initial-prefix circuit.
-/
theorem inconsistentIndex_of_initialPrefix_activeInconsistentIndex_cast
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {pref cd : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix cd) (i : pref.Index)
    (hactiveInconsistent : pref.ActiveInconsistentIndex i) :
    cd.InconsistentIndex (Fin.cast (InitialPrefix.length_eq hprefix.1) i) := by
  exact
    inconsistentIndex_of_initialPrefix_activeInconsistentIndex hprefix
      (Fin.cast (InitialPrefix.length_eq hprefix.1) i)
      (by
        simpa [CircuitDerivation.prefixIndex] using hactiveInconsistent)

/-- Definition 4.3.2: an active inconsistent index makes the circuit active inconsistent. -/
theorem activeInconsistent_of_activeInconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index} (h : cd.ActiveInconsistentIndex i) :
    cd.ActiveInconsistent := by
  exact ⟨i, h⟩

theorem activeInconsistent_inconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    cd.ActiveInconsistent → cd.Inconsistent := by
  rintro ⟨i, hactiveInconsistent⟩
  exact ⟨i, activeInconsistentIndex_inconsistentIndex cd hactiveInconsistent⟩

/-- Definition 4.3.2: an active-inconsistent circuit has an active index. -/
theorem activeInconsistent_has_active_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    cd.ActiveInconsistent → ∃ i : cd.Index, cd.Active i := by
  rintro ⟨i, hactiveInconsistent⟩
  exact ⟨i, activeInconsistentIndex_active cd hactiveInconsistent⟩

/-- Definition 4.3.2: an active-inconsistent circuit has an inconsistent index. -/
theorem activeInconsistent_has_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    cd.ActiveInconsistent → ∃ i : cd.Index, cd.InconsistentIndex i := by
  rintro ⟨i, hactiveInconsistent⟩
  exact ⟨i, activeInconsistentIndex_inconsistentIndex cd hactiveInconsistent⟩

theorem activeInconsistent_not_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    cd.ActiveInconsistent → ¬ cd.Consistent := by
  intro hactive hconsistent
  exact hconsistent (activeInconsistent_inconsistent cd hactive)

theorem inconsistentIndex_of_doublyActive_contradicts_final {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hactive : cd.DoublyActive i)
    (hcontr : (cd.leftTime i) 🗲 (cd.rightTime i)) :
    cd.InconsistentIndex i := by
  exact
    ⟨cd, ⟨InitialPrefix.refl cd.leftDerivation,
      InitialPrefix.refl cd.rightDerivation⟩, hactive, hcontr⟩

theorem activeInconsistentIndex_of_doublyActive_contradicts_final {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hactive : cd.DoublyActive i)
    (hcontr : (cd.leftTime i) 🗲 (cd.rightTime i)) :
    cd.ActiveInconsistentIndex i := by
  exact ⟨cd.doublyActive_active i hactive,
    cd.inconsistentIndex_of_doublyActive_contradicts_final hactive hcontr⟩

/-- Definition 4.3.2: a final contradiction at a doubly active index is active inconsistency. -/
theorem activeInconsistent_of_doublyActive_contradicts_final {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hactive : cd.DoublyActive i)
    (hcontr : (cd.leftTime i) 🗲 (cd.rightTime i)) :
    cd.ActiveInconsistent := by
  exact cd.activeInconsistent_of_activeInconsistentIndex
    (cd.activeInconsistentIndex_of_doublyActive_contradicts_final hactive hcontr)

/-- Activity is preserved when the two sides of a circuit derivation are exchanged. -/
theorem swap_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.Active i) :
    cd.swap.Active (cd.rightIndex i) := by
  rcases h with hleft | hright
  · exact Or.inr (by
      simpa [CircuitDerivation.swap, cd.swap_rightIndex (cd.rightIndex i),
        CircuitDerivation.rightIndex] using hleft)
  · exact Or.inl (by
      simpa [CircuitDerivation.swap] using hright)

/--
Doubly-active indexes are preserved when the two sides of a circuit derivation
are exchanged.
-/
theorem swap_doublyActive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.DoublyActive i) :
    cd.swap.DoublyActive (cd.rightIndex i) := by
  exact
    ⟨by simpa [CircuitDerivation.swap] using h.2,
      by
        simpa [CircuitDerivation.swap, cd.swap_rightIndex (cd.rightIndex i),
          CircuitDerivation.rightIndex] using h.1⟩

/--
Paired initial-prefix evidence is preserved when the two sides of both circuit
derivations are exchanged.
-/
theorem swap_isInitialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {pref cd : CircuitDerivation Time} (h : pref.IsInitialPrefix cd) :
    pref.swap.IsInitialPrefix cd.swap := by
  exact ⟨h.2, h.1⟩

/--
Inconsistent-index witnesses are preserved when the two sides of a circuit
derivation are exchanged.
-/
theorem swap_inconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i : cd.Index} (h : cd.InconsistentIndex i) :
    cd.swap.InconsistentIndex (cd.rightIndex i) := by
  rcases h with ⟨pref, hpref, hactive, hcontr⟩
  let iprefix : pref.Index := pref.prefixIndex hpref i
  have hprefSwap : pref.swap.IsInitialPrefix cd.swap := swap_isInitialPrefix hpref
  have hidx :
      pref.swap.prefixIndex hprefSwap (cd.rightIndex i) =
        pref.rightIndex iprefix := by
    ext
    rfl
  have hactiveSwap : pref.swap.DoublyActive (pref.rightIndex iprefix) := by
    exact swap_doublyActive pref (by simpa [iprefix] using hactive)
  have hcontrSwap :
      (pref.swap.leftTime (pref.rightIndex iprefix)) 🗲 (pref.swap.rightTime (pref.rightIndex iprefix)) := by
    simpa [CircuitDerivation.swap, CircuitDerivation.leftTime,
      CircuitDerivation.rightTime, pref.swap_rightIndex (pref.rightIndex iprefix),
      CircuitDerivation.rightIndex, iprefix] using contradicts_symm hcontr
  exact ⟨pref.swap, hprefSwap, by
    simpa [hidx] using And.intro hactiveSwap hcontrSwap⟩

/--
Active-inconsistent-index witnesses are preserved when the two sides of a
circuit derivation are exchanged.
-/
theorem swap_activeInconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (h : cd.ActiveInconsistentIndex i) :
    cd.swap.ActiveInconsistentIndex (cd.rightIndex i) := by
  exact ⟨swap_active cd h.1, swap_inconsistentIndex cd h.2⟩

/--
Transport an inconsistent-index witness from the swapped circuit derivation
back to the original side-indexing.
-/
theorem inconsistentIndex_of_swap {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.circuit.right.1.Index}
    (h : cd.swap.InconsistentIndex i) :
    cd.InconsistentIndex (Fin.cast cd.circuit.length_eq.symm i) := by
  have hswap :
      cd.swap.swap.InconsistentIndex
        (cd.swap.rightIndex i) :=
    swap_inconsistentIndex cd.swap h
  simpa [CircuitDerivation.swap, Circuit.swap, cd.swap_rightIndex i] using hswap

/--
Transport an active-inconsistent witness from the swapped circuit derivation
back to the original side-indexing.
-/
theorem activeInconsistentIndex_of_swap {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.circuit.right.1.Index}
    (h : cd.swap.ActiveInconsistentIndex i) :
    cd.ActiveInconsistentIndex (Fin.cast cd.circuit.length_eq.symm i) := by
  have hswap :
      cd.swap.swap.ActiveInconsistentIndex
        (cd.swap.rightIndex i) :=
    swap_activeInconsistentIndex cd.swap h
  simpa [CircuitDerivation.swap, Circuit.swap, cd.swap_rightIndex i] using hswap

/--
Least inconsistent indexes are preserved when the two sides of a circuit
derivation are exchanged.
-/
theorem swap_leastInconsistentAtOrBelow {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastInconsistentAtOrBelow bound least) :
    cd.swap.LeastInconsistentAtOrBelow (cd.rightIndex bound) (cd.rightIndex least) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [CircuitDerivation.rightIndex] using h.1
  · exact cd.swap_inconsistentIndex h.2.1
  · intro l hlt hinconsistent
    exact h.2.2 (Fin.cast cd.circuit.length_eq.symm l)
      (by simpa [CircuitDerivation.rightIndex] using hlt)
      (cd.inconsistentIndex_of_swap hinconsistent)

/-- Proposition 4.3.4, first clause. -/
theorem contradiction_persists_from_prefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {pref cd : CircuitDerivation Time} (hprefix : pref.IsInitialPrefix cd)
    (i : cd.Index) :
    let iprefix := pref.prefixIndex hprefix i
    (pref.leftTime iprefix) 🗲 (pref.rightTime iprefix) →
      (cd.leftTime i) 🗲 (cd.rightTime i) := by
  intro iprefix hcontr
  have hleft_raw := InitialPrefix.times_increase hprefix.1 iprefix
  have hleft : (pref.leftTime iprefix) ≼ (cd.leftTime i) := by
    simpa [leftTime, prefixIndex] using hleft_raw
  have hright_raw := InitialPrefix.times_increase hprefix.2 (pref.rightIndex iprefix)
  have hright : (pref.rightTime iprefix) ≼ (cd.rightTime i) := by
    simpa [rightTime, rightIndex, prefixIndex] using hright_raw
  exact contradicts_of_le_both hleft hright hcontr

/--
Proposition 4.3.4, first clause, stated with the
index belonging to the initial-prefix circuit derivation.
-/
theorem contradiction_persists_from_prefixIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {pref cd : CircuitDerivation Time} (hprefix : pref.IsInitialPrefix cd)
    (i : pref.Index) :
    (pref.leftTime i) 🗲 (pref.rightTime i) →
      (cd.leftTime (Fin.cast (InitialPrefix.length_eq hprefix.1) i)) 🗲 (cd.rightTime (Fin.cast (InitialPrefix.length_eq hprefix.1) i)) := by
  intro hcontr
  let ifinal : cd.Index := Fin.cast (InitialPrefix.length_eq hprefix.1) i
  have hprefixIndex : pref.prefixIndex hprefix ifinal = i := by
    ext
    rfl
  simpa [ifinal, hprefixIndex] using
    contradiction_persists_from_prefix hprefix ifinal hcontr

/-- Proposition 4.3.4, second clause. -/
theorem inconsistentIndex_contradicts_final {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index} (h : cd.InconsistentIndex i) :
    (cd.leftTime i) 🗲 (cd.rightTime i) := by
  rcases h with ⟨pref, hprefix, _hactive, hcontr⟩
  exact contradiction_persists_from_prefix hprefix i hcontr

/-- Packed form of Proposition 4.3.4. -/
theorem circuit_times_increase
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {pref cd : CircuitDerivation Time}
    (hprefix : pref.IsInitialPrefix cd) :
    (∀ i : pref.Index,
      (pref.leftTime i) 🗲 (pref.rightTime i) →
        (cd.leftTime (Fin.cast (InitialPrefix.length_eq hprefix.1) i)) 🗲 (cd.rightTime (Fin.cast (InitialPrefix.length_eq hprefix.1) i))) ∧
      (∀ i : cd.Index, cd.InconsistentIndex i →
        (cd.leftTime i) 🗲 (cd.rightTime i)) := by
  constructor
  · intro i hcontr
    exact contradiction_persists_from_prefixIndex hprefix i hcontr
  · intro i hinconsistent
    exact cd.inconsistentIndex_contradicts_final hinconsistent

/--
Proposition 4.3.4, per-index contrapositive: if the final times at an index do
not contradict, that index is not inconsistent.
-/
theorem not_inconsistentIndex_of_no_final_contradiction {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hno : ¬ (cd.leftTime i) 🗲 (cd.rightTime i)) :
    ¬ cd.InconsistentIndex i := by
  intro hinconsistent
  exact hno (cd.inconsistentIndex_contradicts_final hinconsistent)

/--
Definition 4.3.1 and Notation 2.2.4, notation-level component: final circuit times with
different controllers cannot contradict.
-/
theorem not_final_contradiction_of_controller_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hctrl : controller (cd.leftTime i) ≠
      controller (cd.rightTime i)) :
    ¬ (cd.leftTime i) 🗲 (cd.rightTime i) := by
  exact not_contradicts_of_controller_ne hctrl

/--
Notation 2.2.4 and Definition 4.3.2, contrapositive component: an index whose final
circuit times have different controllers is not inconsistent.
-/
theorem not_inconsistentIndex_of_final_controller_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index}
    (hctrl : controller (cd.leftTime i) ≠
      controller (cd.rightTime i)) :
    ¬ cd.InconsistentIndex i := by
  exact cd.not_inconsistentIndex_of_no_final_contradiction
    (cd.not_final_contradiction_of_controller_ne hctrl)

/--
Definition 4.3.1 and Definition 4.3.2: an inconsistent index has matching final
controllers because its final times contradict.
-/
theorem inconsistentIndex_controller_eq_final {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i : cd.Index} (h : cd.InconsistentIndex i) :
    controller (cd.leftTime i) = controller (cd.rightTime i) :=
  (cd.inconsistentIndex_contradicts_final h).1

/--
Proposition 4.3.4, second clause combined with: an inconsistent circuit derivation has a final contradictory
index.
-/
theorem inconsistent_has_final_contradiction {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (h : cd.Inconsistent) :
    ∃ i : cd.Index, (cd.leftTime i) 🗲 (cd.rightTime i) := by
  rcases h with ⟨i, hinconsistent⟩
  exact ⟨i, cd.inconsistentIndex_contradicts_final hinconsistent⟩

/--
Proposition 4.3.4, contrapositive form: if no final circuit index contradicts,
the circuit derivation is consistent.
-/
theorem consistent_of_no_final_contradiction {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    (hno : ∀ i : cd.Index,
      ¬ (cd.leftTime i) 🗲 (cd.rightTime i)) :
    cd.Consistent := by
  intro hinconsistent
  rcases cd.inconsistent_has_final_contradiction hinconsistent with ⟨i, hcontr⟩
  exact hno i hcontr

/--
Proposition 4.3.4 plus Proposition 4.3.4: an active-inconsistent
circuit derivation has an active final contradictory index.
-/
theorem activeInconsistent_has_active_final_contradiction {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (h : cd.ActiveInconsistent) :
    ∃ i : cd.Index,
      cd.Active i ∧ (cd.leftTime i) 🗲 (cd.rightTime i) := by
  rcases h with ⟨i, hactive, hinconsistent⟩
  exact ⟨i, hactive, cd.inconsistentIndex_contradicts_final hinconsistent⟩

/--
Proposition 4.3.4 plus Proposition 4.3.4, contrapositive form: if
no active final index contradicts, the circuit derivation is not active
inconsistent.
-/
theorem not_activeInconsistent_of_no_active_final_contradiction {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    (hno : ∀ i : cd.Index, cd.Active i →
      ¬ (cd.leftTime i) 🗲 (cd.rightTime i)) :
    ¬ cd.ActiveInconsistent := by
  intro hactiveInconsistent
  rcases cd.activeInconsistent_has_active_final_contradiction hactiveInconsistent with
    ⟨i, hactive, hcontr⟩
  exact hno i hactive hcontr

/-- Definition 4.3.6(3): the circuit-derivation contains a right-incompatible
pair of cuts at `j`, i.e. `(Cut_{k,j,i}) ∈ Π` and `(Cut_{k',j,i'}) ∈ Π'` with
`i ≠ i'`. -/
def RightIncompatibleAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (j : cd.Index) : Prop :=
  ∃ k i k' i', ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex j) i ∧
    ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex j) i' ∧ i ≠ i'

/-- Definition 4.3.6: a right-incompatible index has two unequal lower cut endpoints. -/
theorem rightIncompatibleAt_has_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index} (h : cd.RightIncompatibleAt j) :
    ∃ k i k' i',
      ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex j) i ∧
        ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex j) i' ∧
          i ≠ i' :=
  h

/-- Definition 4.3.6: right incompatibility is exactly unequal paired cut endpoints. -/
theorem rightIncompatibleAt_iff_exists_containsCut_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) :
    cd.RightIncompatibleAt j ↔
      ∃ k i k' i',
        ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex j) i ∧
          ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex j) i' ∧
            i ≠ i' :=
  Iff.rfl

/-- Definition 4.3.6: unequal lower endpoints give right-incompatible cuts at `j`. -/
theorem rightIncompatibleAt_of_containsCut_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index} {k i k' i' : Nat}
    (hleft : ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex j) i)
    (hright : ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex j) i')
    (hne : i ≠ i') :
    cd.RightIncompatibleAt j := by
  exact ⟨k, i, k', i', hleft, hright, hne⟩

/--
Definition 4.3.6, indexed witness form: a right-incompatible center has actual
left and right Cut endpoints around that center, with unequal lower endpoints.
-/
theorem rightIncompatibleAt_indexed_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {center : cd.Index}
    (h : cd.RightIncompatibleAt center) :
    ∃ leftUpper leftLower : cd.circuit.left.1.Index,
      ∃ rightUpper rightLower : cd.circuit.right.1.Index,
        leftLower.val < center.val ∧ center.val < leftUpper.val ∧
          rightLower.val < (cd.rightIndex center).val ∧
          (cd.rightIndex center).val < rightUpper.val ∧
          ContainsCut cd.leftDerivation
            (cd.circuit.left.1.paperIndex leftUpper)
            (cd.circuit.left.1.paperIndex center)
            (cd.circuit.left.1.paperIndex leftLower) ∧
          ContainsCut cd.rightDerivation
            (cd.circuit.right.1.paperIndex rightUpper)
            (cd.circuit.right.1.paperIndex (cd.rightIndex center))
            (cd.circuit.right.1.paperIndex rightLower) ∧
          cd.circuit.left.1.paperIndex leftLower ≠
            cd.circuit.right.1.paperIndex rightLower := by
  rcases h with ⟨leftK, leftI, rightK, rightI, hleft, hright, hne⟩
  rcases containsCut_indices hleft with
    ⟨leftUpper, leftCenter, leftLower, hleftUpper, hleftCenter, hleftLower,
      hleftLower_center, hleftCenter_upper⟩
  rcases containsCut_indices hright with
    ⟨rightUpper, rightCenter, rightLower, hrightUpper, hrightCenter, hrightLower,
      hrightLower_center, hrightCenter_upper⟩
  have hleftCenter_eq : leftCenter = center := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hleftCenter)
  have hrightCenter_eq : rightCenter = cd.rightIndex center := by
    apply Fin.ext
    have hpaper :
        cd.circuit.right.1.paperIndex rightCenter =
          cd.circuit.right.1.paperIndex (cd.rightIndex center) := by
      calc
        cd.circuit.right.1.paperIndex rightCenter = cd.circuit.left.1.paperIndex center :=
          hrightCenter
        _ = cd.circuit.right.1.paperIndex (cd.rightIndex center) :=
          (cd.rightIndex_paperIndex center).symm
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hpaper)
  refine
    ⟨leftUpper, leftLower, rightUpper, rightLower, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hleftCenter_eq] using hleftLower_center
  · simpa [hleftCenter_eq] using hleftCenter_upper
  · simpa [hrightCenter_eq] using hrightLower_center
  · simpa [hrightCenter_eq] using hrightCenter_upper
  · simpa [hleftUpper, hleftCenter, hleftLower] using hleft
  · simpa [hrightUpper, hrightCenter, hrightLower,
      cd.rightIndex_paperIndex center] using hright
  · intro hlower_eq
    exact hne (by
      calc
        leftI = cd.circuit.left.1.paperIndex leftLower := hleftLower.symm
        _ = cd.circuit.right.1.paperIndex rightLower := hlower_eq
        _ = rightI := hrightLower)

/-- Definition 4.3.6: a right-incompatible center has a lower endpoint. -/
theorem rightIncompatibleAt_center_val_pos {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {center : cd.Index}
    (h : cd.RightIncompatibleAt center) :
    0 < center.val := by
  rcases cd.rightIncompatibleAt_indexed_witness h with
    ⟨_leftUpper, leftLower, _rightUpper, _rightLower, hleftLower_center,
      _hcenter_leftUpper, _hrightLower_center, _hcenter_rightUpper, _hleft,
      _hright, _hne⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le leftLower.val) hleftLower_center

/--
Definition 4.3.6: a right-incompatible center is not the final circuit index.
-/
theorem rightIncompatibleAt_center_paperIndex_lt_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {center : cd.Index}
    (h : cd.RightIncompatibleAt center) :
    cd.circuit.left.1.paperIndex center < cd.circuit.length := by
  rcases cd.rightIncompatibleAt_indexed_witness h with
    ⟨leftUpper, _leftLower, _rightUpper, _rightLower, _hleftLower_center,
      hcenter_leftUpper, _hrightLower_center, _hcenter_rightUpper, _hleft,
      _hright, _hne⟩
  change center.val + 1 < cd.circuit.left.1.length
  exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hcenter_leftUpper) leftUpper.isLt

theorem rightIncompatibleAt_controller_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {center : cd.Index}
    (h : cd.RightIncompatibleAt center) :
    controller (cd.leftTime center) =
      controller (cd.rightTime center) := by
  exact cd.controller_eq_before_last center
    (cd.rightIncompatibleAt_center_paperIndex_lt_length h)

/--
`Least` is the least right-incompatible index (Definition 4.3.6(3)) no greater
than `bound`.
-/
def LeastRightIncompatibleAtOrBelow {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (bound least : cd.Index) : Prop :=
  least.val ≤ bound.val ∧
    cd.RightIncompatibleAt least ∧
    ∀ l : cd.Index, l.val < least.val → ¬ cd.RightIncompatibleAt l

theorem leastRightIncompatibleAtOrBelow_le_bound {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastRightIncompatibleAtOrBelow bound least) :
    least.val ≤ bound.val :=
  h.1

theorem leastRightIncompatibleAtOrBelow_rightIncompatibleAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastRightIncompatibleAtOrBelow bound least) :
    cd.RightIncompatibleAt least :=
  h.2.1

theorem leastRightIncompatibleAtOrBelow_no_smaller {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastRightIncompatibleAtOrBelow bound least) :
    ∀ l : cd.Index, l.val < least.val → ¬ cd.RightIncompatibleAt l :=
  h.2.2

/--
Definition 4.3.6 least-index setup, index-translated projection: the chosen least
right-incompatible index is no greater than the original witness.
-/
theorem leastRightIncompatibleAtOrBelow_paperIndex_le_bound {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastRightIncompatibleAtOrBelow bound least) :
    cd.circuit.left.1.paperIndex least <= cd.circuit.left.1.paperIndex bound := by
  exact Nat.succ_le_succ h.1

/--
Definition 4.3.6 least-index setup, index-translated projection: no smaller
paper index is right-incompatible.
-/
theorem leastRightIncompatibleAtOrBelow_no_smaller_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (h : cd.LeastRightIncompatibleAtOrBelow bound least) :
    ∀ l : cd.Index,
      cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex least →
        ¬ cd.RightIncompatibleAt l := by
  intro l hl
  exact h.2.2 l (Nat.succ_lt_succ_iff.mp (by
    simpa [Prepath.paperIndex] using hl))

theorem exists_leastRightIncompatibleAtOrBelow {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound : cd.Index}
    (hbound : cd.RightIncompatibleAt bound) :
    ∃ least : cd.Index, cd.LeastRightIncompatibleAtOrBelow bound least := by
  classical
  by_cases hsmaller : ∃ l : cd.Index, l.val < bound.val ∧ cd.RightIncompatibleAt l
  · rcases hsmaller with ⟨smaller, hlt, hincompat⟩
    rcases cd.exists_leastRightIncompatibleAtOrBelow hincompat with
      ⟨least, hleast⟩
    rcases hleast with ⟨hle_smaller, hleast_incompat, hleast_min⟩
    exact
      ⟨least,
        ⟨Nat.le_trans hle_smaller (Nat.le_of_lt hlt), hleast_incompat,
          hleast_min⟩⟩
  · exact
      ⟨bound,
        ⟨Nat.le_refl bound.val, hbound, by
          intro l hlt hlincompat
          exact hsmaller ⟨l, hlt, hlincompat⟩⟩⟩
termination_by bound.val
decreasing_by exact hlt

/-- Definition 4.3.6(4): the circuit-derivation contains right-compatible cuts
at `j`, i.e. whenever `(Cut_{k,j,i}) ∈ Π` and `(Cut_{k',j,i'}) ∈ Π'` then
`i = i'`. -/
def RightCompatibleAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (j : cd.Index) : Prop :=
  ∀ {k i k' i'}, ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex j) i →
    ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex j) i' → i = i'

/--
Definition 4.3.6 note: right compatibility holds vacuously if the left
derivation has no cut centered at `j`.
-/
theorem rightCompatibleAt_of_no_left_containsCut {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index}
    (hleft :
      ∀ k i, ¬ ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex j) i) :
    cd.RightCompatibleAt j := by
  intro k i _k' _i' hcut _hright
  exact False.elim (hleft k i hcut)

/--
Definition 4.3.6 note: right compatibility holds vacuously if the right
derivation has no cut centered at `j`.
-/
theorem rightCompatibleAt_of_no_right_containsCut {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index}
    (hright :
      ∀ k i, ¬ ContainsCut cd.rightDerivation k (cd.circuit.left.1.paperIndex j) i) :
    cd.RightCompatibleAt j := by
  intro _k _i k' i' _hleft hcut
  exact False.elim (hright k' i' hcut)

/-- Definition 4.3.6: right-compatible cuts at `j` have the same lower endpoint. -/
theorem rightCompatibleAt_cutLower_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index}
    (hcompat : cd.RightCompatibleAt j) {k i k' i' : Nat}
    (hleft : ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex j) i)
    (hright : ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex j) i') :
    i = i' := by
  exact hcompat hleft hright

/-- Right-compatible cuts at every index no greater than `j`. -/
def RightCompatibleUpTo {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (j : cd.Index) : Prop :=
  ∀ l : cd.Index, l.val ≤ j.val → cd.RightCompatibleAt l

/-- Right-compatible cuts at every index strictly less than `j`. -/
def RightCompatibleBefore {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (j : cd.Index) : Prop :=
  ∀ l : cd.Index, l.val < j.val → cd.RightCompatibleAt l

theorem rightCompatibleAt_of_upTo {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j : cd.Index} (h : cd.RightCompatibleUpTo j) (hij : i.val ≤ j.val) :
    cd.RightCompatibleAt i := by
  exact h i hij

/--
Definition 4.3.6 interval form: right compatibility up to `j` gives
compatibility at every paper index no greater than `j`.
-/
theorem rightCompatibleAt_of_upTo_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i j : cd.Index}
    (h : cd.RightCompatibleUpTo j)
    (hij : cd.circuit.left.1.paperIndex i <= cd.circuit.left.1.paperIndex j) :
    cd.RightCompatibleAt i := by
  exact cd.rightCompatibleAt_of_upTo h (Nat.succ_le_succ_iff.mp (by
    simpa [Prepath.paperIndex] using hij))

/-- Right compatibility at an index is the negation of right incompatibility there. -/
theorem rightCompatibleAt_iff_not_rightIncompatibleAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) :
    cd.RightCompatibleAt j ↔ ¬ cd.RightIncompatibleAt j := by
  constructor
  · intro hcompat hincompat
    rcases hincompat with ⟨k, i, k', i', hleft, hright, hne⟩
    exact hne (hcompat hleft hright)
  · intro hnot k i k' i' hleft hright
    by_cases heq : i = i'
    · exact heq
    · exact False.elim (hnot ⟨k, i, k', i', hleft, hright, heq⟩)

/-- Right compatibility up to `j` excludes right-incompatible cuts up to `j`. -/
theorem rightCompatibleUpTo_iff_no_rightIncompatibleAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) :
    cd.RightCompatibleUpTo j ↔
      ∀ l : cd.Index, l.val ≤ j.val → ¬ cd.RightIncompatibleAt l := by
  constructor
  · intro hcompat l hle
    exact (cd.rightCompatibleAt_iff_not_rightIncompatibleAt l).mp (hcompat l hle)
  · intro hno l hle
    exact (cd.rightCompatibleAt_iff_not_rightIncompatibleAt l).mpr (hno l hle)

/-- Right incompatibility at an index is the negation of right compatibility there. -/
theorem rightIncompatibleAt_iff_not_rightCompatibleAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) :
    cd.RightIncompatibleAt j ↔ ¬ cd.RightCompatibleAt j := by
  constructor
  · intro hincompat hcompat
    exact (cd.rightCompatibleAt_iff_not_rightIncompatibleAt j).mp hcompat hincompat
  · intro hnotCompat
    by_cases hincompat : cd.RightIncompatibleAt j
    · exact hincompat
    · exact False.elim
        (hnotCompat ((cd.rightCompatibleAt_iff_not_rightIncompatibleAt j).mpr hincompat))

/-- Right compatibility before `j` excludes right-incompatible cuts before `j`. -/
theorem rightCompatibleBefore_iff_no_rightIncompatibleAt_before {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) (j : cd.Index) :
    cd.RightCompatibleBefore j ↔
      ∀ l : cd.Index, l.val < j.val → ¬ cd.RightIncompatibleAt l := by
  constructor
  · intro hcompat l hlt
    exact (cd.rightCompatibleAt_iff_not_rightIncompatibleAt l).mp (hcompat l hlt)
  · intro hno l hlt
    exact (cd.rightCompatibleAt_iff_not_rightIncompatibleAt l).mpr (hno l hlt)

theorem rightCompatibleBefore_of_leastRightIncompatibleAtOrBelow
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound least : cd.Index}
    (hleast : cd.LeastRightIncompatibleAtOrBelow bound least) :
    cd.RightCompatibleBefore least := by
  exact (cd.rightCompatibleBefore_iff_no_rightIncompatibleAt_before least).mpr
    hleast.2.2

theorem rightCompatibleBefore_of_upTo {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j : cd.Index} (h : cd.RightCompatibleUpTo j) (hij : i.val < j.val) :
    cd.RightCompatibleAt i := by
  exact cd.rightCompatibleAt_of_upTo h (Nat.le_of_lt hij)

/--
Definition 4.3.6 proof setup: right compatibility up to `j` gives compatibility
at every strictly smaller paper index.
-/
theorem rightCompatibleBefore_of_upTo_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i j : cd.Index}
    (h : cd.RightCompatibleUpTo j)
    (hij : cd.circuit.left.1.paperIndex i < cd.circuit.left.1.paperIndex j) :
    cd.RightCompatibleAt i := by
  exact cd.rightCompatibleBefore_of_upTo h (Nat.succ_lt_succ_iff.mp (by
    simpa [Prepath.paperIndex] using hij))

theorem rightCompatibleBefore_from_upTo {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index}
    (h : cd.RightCompatibleUpTo j) :
    cd.RightCompatibleBefore j := by
  intro i hij
  exact cd.rightCompatibleBefore_of_upTo h hij

theorem rightCompatibleUpTo_of_before_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i j : cd.Index}
    (h : cd.RightCompatibleBefore j) (hij : i.val < j.val) :
    cd.RightCompatibleUpTo i := by
  intro l hli
  exact h l (Nat.lt_of_le_of_lt hli hij)

/--
Definition 4.3.6 proof setup: compatibility before `j` gives compatibility up
to every strictly smaller paper index.
-/
theorem rightCompatibleUpTo_of_before_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {i j : cd.Index}
    (h : cd.RightCompatibleBefore j)
    (hij : cd.circuit.left.1.paperIndex i < cd.circuit.left.1.paperIndex j) :
    cd.RightCompatibleUpTo i := by
  exact cd.rightCompatibleUpTo_of_before_lt h
    (Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hij))

theorem rightCompatibleUpTo_cutLower_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index} (hcompat : cd.RightCompatibleUpTo j)
    {center : cd.Index} (hcenter : center.val ≤ j.val)
    {k i k' i' : Nat}
    (hleft : ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex center) i)
    (hright : ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex center) i') :
    i = i' := by
  exact (cd.rightCompatibleAt_of_upTo hcompat hcenter) hleft hright

/--
Definition 4.3.6 interval form: right compatibility up to `j` makes
right-compatible cuts at every paper index no greater than `j` share the same
lower endpoint.
-/
theorem rightCompatibleUpTo_cutLower_eq_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index} (hcompat : cd.RightCompatibleUpTo j)
    {center : cd.Index}
    (hcenter : cd.circuit.left.1.paperIndex center <= cd.circuit.left.1.paperIndex j)
    {k i k' i' : Nat}
    (hleft : ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex center) i)
    (hright : ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex center) i') :
    i = i' := by
  exact cd.rightCompatibleUpTo_cutLower_eq hcompat
    (Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hcenter))
    hleft hright

theorem rightCompatibleBefore_cutLower_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j center : cd.Index}
    (hcompat : cd.RightCompatibleBefore j) (hcenter : center.val < j.val)
    {k i k' i' : Nat}
    (hleft : ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex center) i)
    (hright : ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex center) i') :
    i = i' := by
  exact (hcompat center hcenter) hleft hright

/--
Definition 4.3.6 proof setup: compatibility before `j` makes right-compatible
cuts at every strictly smaller paper index share the same lower endpoint.
-/
theorem rightCompatibleBefore_cutLower_eq_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j center : cd.Index}
    (hcompat : cd.RightCompatibleBefore j)
    (hcenter : cd.circuit.left.1.paperIndex center < cd.circuit.left.1.paperIndex j)
    {k i k' i' : Nat}
    (hleft : ContainsCut cd.leftDerivation k (cd.circuit.left.1.paperIndex center) i)
    (hright : ContainsCut cd.rightDerivation k' (cd.circuit.left.1.paperIndex center) i') :
    i = i' := by
  exact cd.rightCompatibleBefore_cutLower_eq hcompat
    (Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hcenter))
    hleft hright

theorem rightCompatibleUpTo_mono {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j : cd.Index} (h : cd.RightCompatibleUpTo j) (hij : i.val ≤ j.val) :
    cd.RightCompatibleUpTo i := by
  intro l hli
  exact h l (Nat.le_trans hli hij)

theorem rightCompatibleUpTo_of_before_and_at {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index}
    (hbefore : cd.RightCompatibleBefore j) (hat : cd.RightCompatibleAt j) :
    cd.RightCompatibleUpTo j := by
  intro i hi
  rcases Nat.lt_or_eq_of_le hi with hlt | heq
  · exact hbefore i hlt
  · have hidx : i = j := Fin.ext heq
    subst i
    exact fun {k} {lower} {k'} {lower'} hleft hright => hat hleft hright

/--
Right-compatible cuts at one index are preserved when the two sides of a
circuit derivation are exchanged.
-/
theorem swap_rightCompatibleAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center : cd.circuit.right.1.Index}
    (hcompat : cd.RightCompatibleAt (Fin.cast cd.circuit.length_eq.symm center)) :
    cd.swap.RightCompatibleAt center := by
  intro k lower k' lower' hswapLeft hswapRight
  let centerLeft : cd.Index := Fin.cast cd.circuit.length_eq.symm center
  have hcenterPaper :
      cd.circuit.left.1.paperIndex centerLeft =
        cd.circuit.right.1.paperIndex center := by
    simp [centerLeft, Prepath.paperIndex]
  have hrightOrig :
      ContainsCut cd.rightDerivation k
        (cd.circuit.left.1.paperIndex centerLeft) lower := by
    simpa [CircuitDerivation.swap, Circuit.swap, hcenterPaper] using hswapLeft
  have hleftOrig :
      ContainsCut cd.leftDerivation k'
        (cd.circuit.left.1.paperIndex centerLeft) lower' := by
    simpa [CircuitDerivation.swap, Circuit.swap, hcenterPaper] using hswapRight
  exact (hcompat hleftOrig hrightOrig).symm

/--
Right-compatible cuts are preserved when the two sides of a circuit derivation
are exchanged.
-/
theorem swap_rightCompatibleUpTo {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (hcompat : cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm start)) :
    cd.swap.RightCompatibleUpTo start := by
  intro center hcenter_le
  intro k lower k' lower' hswapLeft hswapRight
  let centerLeft : cd.Index := Fin.cast cd.circuit.length_eq.symm center
  have hcenter_left_le :
      centerLeft.val ≤ (Fin.cast cd.circuit.length_eq.symm start).val := by
    simpa [centerLeft] using hcenter_le
  have hcompatAt :
      ∀ {k i k' i'}, ContainsCut cd.leftDerivation k
          (cd.circuit.left.1.paperIndex centerLeft) i →
        ContainsCut cd.rightDerivation k'
          (cd.circuit.left.1.paperIndex centerLeft) i' → i = i' :=
    hcompat centerLeft hcenter_left_le
  have hcenterPaper :
      cd.circuit.left.1.paperIndex centerLeft =
        cd.circuit.right.1.paperIndex center := by
    simp [centerLeft, Prepath.paperIndex]
  have hrightOrig :
      ContainsCut cd.rightDerivation k
        (cd.circuit.left.1.paperIndex centerLeft) lower := by
    simpa [CircuitDerivation.swap, Circuit.swap, hcenterPaper] using hswapLeft
  have hleftOrig :
      ContainsCut cd.leftDerivation k'
        (cd.circuit.left.1.paperIndex centerLeft) lower' := by
    simpa [CircuitDerivation.swap, Circuit.swap, hcenterPaper] using hswapRight
  exact (hcompatAt hleftOrig hrightOrig).symm

/--
Right-compatible-before cuts are preserved when the two sides of a circuit
derivation are exchanged.
-/
theorem swap_rightCompatibleBefore {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (hcompat : cd.RightCompatibleBefore (Fin.cast cd.circuit.length_eq.symm start)) :
    cd.swap.RightCompatibleBefore start := by
  intro center hcenter_lt
  intro k lower k' lower' hswapLeft hswapRight
  let centerLeft : cd.Index := Fin.cast cd.circuit.length_eq.symm center
  have hcenter_left_lt :
      centerLeft.val < (Fin.cast cd.circuit.length_eq.symm start).val := by
    simpa [centerLeft] using hcenter_lt
  have hcompatAt :
      ∀ {k i k' i'}, ContainsCut cd.leftDerivation k
          (cd.circuit.left.1.paperIndex centerLeft) i →
        ContainsCut cd.rightDerivation k'
          (cd.circuit.left.1.paperIndex centerLeft) i' → i = i' :=
    hcompat centerLeft hcenter_left_lt
  have hcenterPaper :
      cd.circuit.left.1.paperIndex centerLeft =
        cd.circuit.right.1.paperIndex center := by
    simp [centerLeft, Prepath.paperIndex]
  have hrightOrig :
      ContainsCut cd.rightDerivation k
        (cd.circuit.left.1.paperIndex centerLeft) lower := by
    simpa [CircuitDerivation.swap, Circuit.swap, hcenterPaper] using hswapLeft
  have hleftOrig :
      ContainsCut cd.leftDerivation k'
        (cd.circuit.left.1.paperIndex centerLeft) lower' := by
    simpa [CircuitDerivation.swap, Circuit.swap, hcenterPaper] using hswapRight
  exact (hcompatAt hleftOrig hrightOrig).symm

/--
Right-incompatible cut witnesses are preserved when the two sides of a circuit
derivation are exchanged.
-/
theorem swap_rightIncompatibleAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center : cd.circuit.right.1.Index}
    (hincompat :
      cd.RightIncompatibleAt (Fin.cast cd.circuit.length_eq.symm center)) :
    cd.swap.RightIncompatibleAt center := by
  rcases hincompat with
    ⟨leftK, leftLower, rightK, rightLower, hleft, hright, hne⟩
  let centerLeft : cd.Index := Fin.cast cd.circuit.length_eq.symm center
  have hcenterPaper :
      cd.circuit.left.1.paperIndex centerLeft =
        cd.circuit.right.1.paperIndex center := by
    simp [centerLeft, Prepath.paperIndex]
  have hswapLeft :
      ContainsCut cd.swap.leftDerivation rightK
        (cd.swap.circuit.left.1.paperIndex center) rightLower := by
    simpa [CircuitDerivation.swap, Circuit.swap, hcenterPaper] using hright
  have hswapRight :
      ContainsCut cd.swap.rightDerivation leftK
        (cd.swap.circuit.left.1.paperIndex center) leftLower := by
    simpa [CircuitDerivation.swap, Circuit.swap, hcenterPaper] using hleft
  exact
    ⟨rightK, rightLower, leftK, leftLower, hswapLeft, hswapRight, hne.symm⟩

end CircuitDerivation

end ConsistentHistories.Routes.Paths.Circuits
