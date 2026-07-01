import ContForm.Foundation.Cut.Structure

/-!
Paper section 4.1: Paths.

-/

namespace ContForm.Foundation.Paths.Basic

open ContForm.Foundation.LocatedSemilattices.Basic
open ContForm.Foundation.Cut.Flags
open ContForm.Foundation.Cut.Structure
open ContForm.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ContForm.Foundation.Cut.Structure.LocatedSemilatticeWithCut

universe u v

/--
Definition 4.1.1(1): an `L`-prepath is an `n`-tuple (`n ≥ 1`) of consistent
times.

Lean represents the paper's finite nonempty tuples as functions out of `Fin
length`. By Definition 4.1.1(2) the paper displays its tuples right-to-left, but
the indexing notation `T[i]` is represented directly by `Fin`.
-/
structure Prepath (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] where
  length : Nat
  length_pos : 0 < length
  time : Fin length → Time
  consistent : ∀ i, ConsistentTime (time i)

namespace Prepath

/-- Definition 4.1.1(3)(b), `index(T)`: the set of indexes of a prepath. -/
abbrev Index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) : Type :=
  Fin T.length

/-- Definition 4.1.1(3)(d), `T[i]`: the time at the `i`-th index of a prepath. -/
def get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) (i : T.Index) : Time :=
  T.time i

/-- Definition 4.1.1: prepaths are extensional finite tuples of times. -/
theorem ext_by_get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T U : Prepath Time}
    (hlen : T.length = U.length)
    (hget : ∀ i : T.Index, T.get i = U.get (Fin.cast hlen i)) :
    T = U := by
  cases T with
  | mk lenT posT timeT consT =>
    cases U with
    | mk lenU posU timeU consU =>
      cases hlen
      simp [get] at hget
      have htime : timeT = timeU := funext hget
      subst htime
      rfl

/-- The paper's one-based numeric index corresponding to a Lean `Fin` index. -/
def paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) (i : T.Index) : Nat :=
  i.val + 1

/-- Definition 4.1.1: a paper index is at least one. -/
theorem paperIndex_pos {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) (i : T.Index) :
    0 < T.paperIndex i :=
  Nat.succ_pos i.val

/-- Definition 4.1.1: a paper index is at most the prepath length. -/
theorem paperIndex_le_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) (i : T.Index) :
    T.paperIndex i <= T.length :=
  Nat.succ_le_of_lt i.isLt

/-- Definition 4.1.1: Lean index order agrees with the paper's one-based order. -/
theorem paperIndex_lt_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) {i j : T.Index} :
    T.paperIndex i < T.paperIndex j ↔ i.val < j.val := by
  simp [paperIndex]

/-- Definition 4.1.1: Lean non-strict index order agrees with the paper's one-based order. -/
theorem paperIndex_le_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) {i j : T.Index} :
    T.paperIndex i <= T.paperIndex j ↔ i.val <= j.val := by
  simp [paperIndex]

/-- Definition 4.1.1: equal paper indexes identify the same Lean index. -/
theorem paperIndex_eq_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) {i j : T.Index} :
    T.paperIndex i = T.paperIndex j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    exact Nat.succ.inj (by simpa [paperIndex] using h)
  · intro h
    rw [h]

/-- Definition 4.1.1(3)(c), `length(T)`: the number of indexes in a prepath. -/
def lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) : Nat :=
  T.length

/-- Definition 4.1.1: a nonempty prepath has a first paper index. -/
def firstIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) : T.Index :=
  ⟨0, T.length_pos⟩

/-- Definition 4.1.1: a nonempty prepath has a last paper index. -/
def lastIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) : T.Index :=
  ⟨T.length - 1, by
    have hpos : 0 < T.length := T.length_pos
    omega⟩

/-- Definition 4.1.1: the first Lean endpoint has paper index `1`. -/
theorem paperIndex_firstIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) :
    T.paperIndex T.firstIndex = 1 := by
  rfl

/-- Definition 4.1.1: the last Lean endpoint has paper index `length(T)`. -/
theorem paperIndex_lastIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) :
    T.paperIndex T.lastIndex = T.lengthValue := by
  have hpos : 0 < T.length := T.length_pos
  simp [paperIndex, lastIndex, lengthValue]
  omega

/-- Definition 4.1.1: the first entry of a prepath is consistent. -/
theorem firstIndex_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) :
    ConsistentTime (T.get T.firstIndex) := by
  exact T.consistent T.firstIndex

/-- Definition 4.1.1: the last entry of a prepath is consistent. -/
theorem lastIndex_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) :
    ConsistentTime (T.get T.lastIndex) := by
  exact T.consistent T.lastIndex

/--
Notation 4.1.2, the path index update `T{j:=t}`: the tuple that agrees with `T`
except that index `j` is set to `t`. Lean carries explicit controller-equality
and consistency side conditions so the result is again a prepath.
-/
def replace {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) (j : T.Index) (t : Time)
    (_hctrl : controller t = controller (T.get j))
    (hconsistent : ConsistentTime t) : Prepath Time where
  length := T.length
  length_pos := T.length_pos
  time i := if h : i = j then t else T.time i
  consistent i := by
    by_cases h : i = j
    · subst h
      simpa
    · simpa [h] using T.consistent i

@[simp] theorem replace_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) (t : Time) (hctrl hconsistent) :
    (T.replace j t hctrl hconsistent).length = T.length :=
  rfl

@[simp] theorem replace_get_same {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) (t : Time) (hctrl hconsistent) :
    (T.replace j t hctrl hconsistent).get j = t := by
  simp [replace, get]

theorem replace_get_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {i j : T.Index} (hij : i ≠ j) (t : Time) (hctrl hconsistent) :
    (T.replace j t hctrl hconsistent).get i = T.get i := by
  simp [replace, get, hij]

/--
Notation 4.1.2: `T{j:=t}` is pointwise the stated update, with index `j` set to
`t` and every other index left unchanged.
-/
theorem replace_get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) (t : Time) (hctrl hconsistent)
    (i : (T.replace j t hctrl hconsistent).Index) :
    (T.replace j t hctrl hconsistent).get i =
      if _ : i = j then t else T.get i := by
  by_cases h : i = j
  · simp [h, replace_get_same]
  · simp [h, replace_get_ne T h t hctrl hconsistent]

/--
Notation 4.1.2: in `T{j:=t}`, an index with the same paper index as `j`
receives the replacement time `t`.
-/
theorem replace_get_of_paperIndex_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {i j : T.Index} (hij : T.paperIndex i = T.paperIndex j)
    (t : Time) (hctrl hconsistent) :
    (T.replace j t hctrl hconsistent).get i = t := by
  have hidx : i = j := (T.paperIndex_eq_iff.mp hij)
  rw [hidx]
  exact replace_get_same T j t hctrl hconsistent

/--
Notation 4.1.2: in `T{j:=t}`, an index with a different paper index from `j`
keeps its original value.
-/
theorem replace_get_of_paperIndex_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {i j : T.Index} (hij : T.paperIndex i ≠ T.paperIndex j)
    (t : Time) (hctrl hconsistent) :
    (T.replace j t hctrl hconsistent).get i = T.get i := by
  have hidx : i ≠ j := by
    intro h
    exact hij (by rw [h])
  exact replace_get_ne T hidx t hctrl hconsistent

/-- Replacement keeps the same length notation. -/
theorem replace_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) (t : Time) (hctrl hconsistent) :
    (T.replace j t hctrl hconsistent).lengthValue = T.lengthValue :=
  rfl

/-- Replacement keeps the same paper index numbers. -/
theorem replace_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) (t : Time) (hctrl hconsistent)
    (i : (T.replace j t hctrl hconsistent).Index) :
    (T.replace j t hctrl hconsistent).paperIndex i = T.paperIndex i :=
  rfl

/-- Replacement remains a tuple of consistent times. -/
theorem replace_get_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) (t : Time) (hctrl hconsistent)
    (i : (T.replace j t hctrl hconsistent).Index) :
    ConsistentTime ((T.replace j t hctrl hconsistent).get i) :=
  (T.replace j t hctrl hconsistent).consistent i

/--
The replacement side condition
preserves the changed controller.
-/
theorem replace_get_same_controller {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) (t : Time) (hctrl hconsistent) :
    controller ((T.replace j t hctrl hconsistent).get j) =
      controller (T.get j) := by
  simpa [replace_get_same] using hctrl

/-- Unchanged indexes keep their controllers under replacement. -/
theorem replace_get_ne_controller {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {i j : T.Index} (hij : i ≠ j) (t : Time) (hctrl hconsistent) :
    controller ((T.replace j t hctrl hconsistent).get i) =
      controller (T.get i) := by
  rw [replace_get_ne T hij t hctrl hconsistent]

/--
Every replacement index has the
same controller as it had before replacement, using the explicit
controller-equality hypothesis carried by `Prepath.replace`.
-/
theorem replace_get_controller {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (j : T.Index) (t : Time) (hctrl hconsistent)
    (i : (T.replace j t hctrl hconsistent).Index) :
    controller ((T.replace j t hctrl hconsistent).get i) =
      controller (T.get i) := by
  by_cases hij : i = j
  · subst i
    exact replace_get_same_controller T j t hctrl hconsistent
  · exact replace_get_ne_controller T hij t hctrl hconsistent

end Prepath

/-- The initial-rule time at one index. -/
def initTime (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat} (base : Fin n → Time) :
    Fin n → Time :=
  fun i => if i.val = 0 then base i else ↱ i.val (base i)

/-- The prepath produced by the Init rule from its underlying raw times. -/
def initPrepath (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat} (hpos : 0 < n)
    (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i)) :
    Prepath Time where
  length := n
  length_pos := hpos
  time := initTime Time base
  consistent := hconsistent

/-- Remark 4.1.3, Init rule: the first pushed time is unchanged. -/
theorem initTime_zero {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (base : Fin n → Time) (i : Fin n) (h : i.val = 0) :
    initTime Time base i = base i := by
  simp [initTime, h]

/-- Remark 4.1.3, Init rule: non-first indexes are wrapped by `nextIndex`. -/
theorem initTime_nonzero {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (base : Fin n → Time) (i : Fin n) (h : i.val ≠ 0) :
    initTime Time base i = ↱ i.val (base i) := by
  simp [initTime, h]

/-- Remark 4.1.3, Init rule: the produced prepath has the requested length. -/
theorem initPrepath_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i)) :
    (initPrepath Time hpos base hconsistent).lengthValue = n :=
  rfl

/-- Remark 4.1.3, Init rule: the produced prepath is pointwise `initTime`. -/
theorem initPrepath_get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (initPrepath Time hpos base hconsistent).Index) :
    (initPrepath Time hpos base hconsistent).get i = initTime Time base i :=
  rfl

/-- Remark 4.1.3, Init rule: the rightmost/first index contains its base time. -/
theorem initPrepath_get_first {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (initPrepath Time hpos base hconsistent).Index) (h : i.val = 0) :
    (initPrepath Time hpos base hconsistent).get i = base i := by
  rw [initPrepath_get]
  exact initTime_zero base i h

/-- Remark 4.1.3, Init rule: every later index contains its `nextIndex` time. -/
theorem initPrepath_get_nonzero {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (initPrepath Time hpos base hconsistent).Index) (h : i.val ≠ 0) :
    (initPrepath Time hpos base hconsistent).get i =
      ↱ i.val (base i) := by
  rw [initPrepath_get]
  exact initTime_nonzero base i h

/-- Remark 4.1.3, Init rule: paper index `1` contains its base time. -/
theorem initPrepath_get_paperIndex_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (initPrepath Time hpos base hconsistent).Index)
    (h : (initPrepath Time hpos base hconsistent).paperIndex i = 1) :
    (initPrepath Time hpos base hconsistent).get i = base i := by
  apply initPrepath_get_first
  unfold Prepath.paperIndex at h
  omega

/--
Remark 4.1.3, Init rule: every paper index after `1` is wrapped by
`nextIndex` with the previous paper index.
-/
theorem initPrepath_get_paperIndex_gt_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (initPrepath Time hpos base hconsistent).Index)
    (h : 1 < (initPrepath Time hpos base hconsistent).paperIndex i) :
    (initPrepath Time hpos base hconsistent).get i =
      ↱ ((initPrepath Time hpos base hconsistent).paperIndex i - 1) (base i) := by
  have hnonzero : i.val ≠ 0 := by
    unfold Prepath.paperIndex at h
    omega
  rw [initPrepath_get_nonzero hpos base hconsistent i hnonzero]
  simp [Prepath.paperIndex]

/--
Definition 4.1.1(4): derivations (derivation-trees), defined inductively by the
rules of Figure 9 — (Init), (Inc_j), (⋈Intro_j), (⋉Intro_j), and (Cut_{k,j,i}).
As Figure 9 notes, since by Definition 4.1.1(1) prepaths are tuples of consistent
times, a rule instance is only well-formed when the times above and below the
line are consistent.
-/
inductive Derivation (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    Prepath Time → Type (max (u + 1) (v + 1)) where
  | init {n : Nat} (hpos : 0 < n) (base : Fin n → Time)
      (hconsistent : ∀ i, ConsistentTime (initTime Time base i)) :
      Derivation Time (initPrepath Time hpos base hconsistent)
  | inc {T : Prepath Time} (deriv : Derivation Time T) (j : T.Index) {t' : Time}
      (hlt : (T.get j) ≺ t')
      (hflag :
        flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
      (hconsistent : ConsistentTime t') :
      Derivation Time (T.replace j t' hlt.1.1.symm hconsistent)
  | cutMeIntro {T : Prepath Time} (deriv : Derivation Time T) (j : T.Index)
      (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋊ target t)) :
      Derivation Time (T.replace j (⋊ target t) (by
        calc
          controller (⋊ target t) = controller t :=
            (⋊ target).controller_preserving t
          _ = controller (↱ target t) :=
            ((↱ target).controller_preserving t).symm
          _ = controller (T.get j) := by rw [hshape])
        hconsistent)
  | cutYouIntro {T : Prepath Time} (deriv : Derivation Time T) (j : T.Index)
      (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋉ target t)) :
      Derivation Time (T.replace j (⋉ target t) (by
        calc
          controller (⋉ target t) = controller t :=
            (⋉ target).controller_preserving t
          _ = controller (↱ target t) :=
            ((↱ target).controller_preserving t).symm
          _ = controller (T.get j) := by rw [hshape])
        hconsistent)
  | cut {T : Prepath Time} (deriv : Derivation Time T) {i j k : T.Index}
      (hij : i.val < j.val) (hjk : j.val < k.val)
      {ti tj tk : Time}
      (hk : T.get k = ⋉ (T.paperIndex j) tk)
      (hj : T.get j =
        ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
      (hi : T.get i =
        ti # (⋊ (T.paperIndex i)
          (tj # (⋉ (T.paperIndex j) tk))))
      (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
      Derivation Time (T.replace k (↱ (T.paperIndex i) tk) (by
        calc
          controller (↱ (T.paperIndex i) tk) =
              controller tk :=
            (↱ (T.paperIndex i)).controller_preserving tk
          _ = controller (⋉ (T.paperIndex j) tk) :=
            ((⋉ (T.paperIndex j)).controller_preserving tk).symm
          _ = controller (T.get k) := by rw [hk])
        hconsistent)

namespace Derivation

/-- Definition 4.1.1(4)(a), `root(Π)`: the prepath at the root of `Π`. -/
def root {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} (_deriv : Derivation Time T) :
    Prepath Time :=
  T

/-- Structural height of a derivation, used to reason about initial prefixes. -/
def height {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] : {T : Prepath Time} → Derivation Time T → Nat
  | _, Derivation.init _ _ _ => 0
  | _, Derivation.inc deriv _ _ _ _ => height deriv + 1
  | _, Derivation.cutMeIntro deriv _ _ _ _ => height deriv + 1
  | _, Derivation.cutYouIntro deriv _ _ _ _ => height deriv + 1
  | _, Derivation.cut deriv _ _ _ _ _ _ => height deriv + 1

/-- A derivation packaged with the prepath it derives. -/
abbrev Packed (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :=
  Σ T : Prepath Time, Derivation Time T

/-- Package a derivation with its root prepath. -/
def pack {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) : Packed Time :=
  ⟨T, deriv⟩

/--
The derivation ancestor chain, starting with the derivation itself and then
moving backward through immediate premises.
-/
def ancestors {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    {T : Prepath Time} → Derivation Time T → List (Packed Time)
  | _, deriv@(Derivation.init _ _ _) => [pack deriv]
  | _, deriv@(Derivation.inc prev _ _ _ _) => pack deriv :: ancestors prev
  | _, deriv@(Derivation.cutMeIntro prev _ _ _ _) => pack deriv :: ancestors prev
  | _, deriv@(Derivation.cutYouIntro prev _ _ _ _) => pack deriv :: ancestors prev
  | _, deriv@(Derivation.cut prev _ _ _ _ _ _) => pack deriv :: ancestors prev

/-- Definition 4.1.1(4)(b), `index(Π)`: the set of indexes of the prepath `Π` derives. -/
abbrev Index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} (_deriv : Derivation Time T) : Type :=
  T.Index

/-- Definition 4.1.1(4)(c), `Π[i]`: the `i`-index value `root(Π)[i]` of the prepath `Π` derives. -/
def get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} (_deriv : Derivation Time T)
    (i : T.Index) : Time :=
  T.get i

/-- Definition 4.1.1: the root notation of a derivation is its derived prepath. -/
theorem root_eq_prepath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) :
    deriv.root = T :=
  rfl

/-- Definition 4.1.1: `Π[i]` is the value of `root(Π)` at `i`. -/
theorem get_eq_root_get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (i : deriv.root.Index) :
    deriv.get i = deriv.root.get i :=
  rfl

/-- Definition 4.1.1: every `Π[i]` is a consistent time. -/
theorem get_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (i : T.Index) :
    ConsistentTime (deriv.get i) :=
  T.consistent i

/-- Remark 4.1.3, Init rule: the root has the requested length. -/
theorem init_root_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i)) :
    (Derivation.init (Time := Time) hpos base hconsistent).root.lengthValue = n := by
  rfl

/-- Remark 4.1.3, Init rule: the root is pointwise `initTime`. -/
theorem init_root_get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (Derivation.init (Time := Time) hpos base hconsistent).root.Index) :
    (Derivation.init (Time := Time) hpos base hconsistent).root.get i =
      initTime Time base i := by
  rfl

/--
Remark 4.1.3, programmatic derivation-rules remark: every Init output
entry is structurally consistent.
-/
theorem init_root_get_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (Derivation.init (Time := Time) hpos base hconsistent).root.Index) :
    ConsistentTime
      ((Derivation.init (Time := Time) hpos base hconsistent).root.get i) :=
  (Derivation.init (Time := Time) hpos base hconsistent).root.consistent i

/-- Remark 4.1.3, Init rule: root paper index `1` contains its base time. -/
theorem init_root_get_paperIndex_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (Derivation.init (Time := Time) hpos base hconsistent).root.Index)
    (h : (Derivation.init (Time := Time) hpos base hconsistent).root.paperIndex i = 1) :
    (Derivation.init (Time := Time) hpos base hconsistent).root.get i = base i := by
  exact initPrepath_get_paperIndex_one hpos base hconsistent i h

/--
Remark 4.1.3, Init rule: every root paper index after `1` is wrapped by
`nextIndex` with the previous paper index.
-/
theorem init_root_get_paperIndex_gt_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (Derivation.init (Time := Time) hpos base hconsistent).root.Index)
    (h : 1 < (Derivation.init (Time := Time) hpos base hconsistent).root.paperIndex i) :
    (Derivation.init (Time := Time) hpos base hconsistent).root.get i =
      nextIndex
        ((Derivation.init (Time := Time) hpos base hconsistent).root.paperIndex i - 1)
        (base i) := by
  exact initPrepath_get_paperIndex_gt_one hpos base hconsistent i h

/-- Remark 4.1.3, Inc rule: the root length is unchanged. -/
theorem inc_root_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (Derivation.inc deriv j hlt hflag hconsistent).root.lengthValue = T.lengthValue := by
  rfl

/-- Remark 4.1.3, Inc rule: the indicated index is changed to the new time. -/
theorem inc_root_get_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (Derivation.inc deriv j hlt hflag hconsistent).root.get j = t' := by
  simp [Derivation.root]

/--
Remark 4.1.3, programmatic derivation-rules remark: the Inc output at the
changed index is structurally consistent.
-/
theorem inc_root_get_changed_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    ConsistentTime
      ((Derivation.inc deriv j hlt hflag hconsistent).root.get j) := by
  rw [inc_root_get_changed deriv j hlt hflag hconsistent]
  exact hconsistent

/-- Remark 4.1.3, Inc rule: the changed root time is strictly later. -/
theorem inc_root_get_changed_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (T.get j) ≺ ((Derivation.inc deriv j hlt hflag hconsistent).root.get j) := by
  rw [inc_root_get_changed deriv j hlt hflag hconsistent]
  exact hlt

/-- Remark 4.1.3, Inc rule: the changed root time has the same flag lookup. -/
theorem inc_root_get_changed_flag_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    flagOf cuttingFlagSet (T.get j) =
      flagOf cuttingFlagSet
        ((Derivation.inc deriv j hlt hflag hconsistent).root.get j) := by
  rw [inc_root_get_changed deriv j hlt hflag hconsistent]
  exact hflag

/--
Remark 4.1.3, programmatic derivation-rules remark: `Inc` really changes
the indicated index.
-/
theorem inc_root_get_changed_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (Derivation.inc deriv j hlt hflag hconsistent).root.get j ≠ T.get j := by
  rw [inc_root_get_changed deriv j hlt hflag hconsistent]
  exact hlt.2.symm

/-- Remark 4.1.3, Inc rule: every non-indicated index is unchanged. -/
theorem inc_root_get_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') {idx : T.Index}
    (hidx : idx ≠ j) :
    (Derivation.inc deriv j hlt hflag hconsistent).root.get idx = T.get idx := by
  simp [Derivation.root, Prepath.replace_get_ne T hidx]

/--
Remark 4.1.4(1): `Inc` changes precisely the indicated index.
-/
theorem inc_root_changes_precisely_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag :
      flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (Derivation.inc deriv j hlt hflag hconsistent).root.get j = t' ∧
      (Derivation.inc deriv j hlt hflag hconsistent).root.get j ≠ T.get j ∧
      ∀ idx : T.Index, idx ≠ j →
        (Derivation.inc deriv j hlt hflag hconsistent).root.get idx = T.get idx := by
  exact
    ⟨inc_root_get_changed deriv j hlt hflag hconsistent,
      inc_root_get_changed_ne deriv j hlt hflag hconsistent,
      fun _ hidx => inc_root_get_ne deriv j hlt hflag hconsistent hidx⟩

/-- Remark 4.1.3, `cutme Intro`: the root length is unchanged. -/
theorem cutMeIntro_root_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (Derivation.cutMeIntro deriv j target hshape hconsistent).root.lengthValue =
      T.lengthValue := by
  rfl

/-- Remark 4.1.4, `cutme Intro`: the source index is a `nextIndex` state. -/
theorem cutMeIntro_source_get_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (_hconsistent : ConsistentTime (⋊ target t)) :
    deriv.root.get j = ↱ target t := by
  exact hshape

/-- Remark 4.1.3, `cutme Intro`: the indicated index receives `cutMe`. -/
theorem cutMeIntro_root_get_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (Derivation.cutMeIntro deriv j target hshape hconsistent).root.get j =
      ⋊ target t := by
  simp [Derivation.root]

/--
Remark 4.1.3, programmatic derivation-rules remark: the `cutme Intro`
output at the changed index is structurally consistent.
-/
theorem cutMeIntro_root_get_changed_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    ConsistentTime
      ((Derivation.cutMeIntro deriv j target hshape hconsistent).root.get j) := by
  rw [cutMeIntro_root_get_changed deriv j target hshape hconsistent]
  exact hconsistent

/--
Remark 4.1.4(5), (⋈Intro_j) rule: the `cutme Intro` changed root time is later
than the source.
-/
theorem cutMeIntro_root_get_changed_le {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (T.get j) ≼ ((Derivation.cutMeIntro deriv j target hshape hconsistent).root.get j) := by
  rw [cutMeIntro_root_get_changed deriv j target hshape hconsistent, hshape]
  exact nextIndex_le_cutMe target t

/--
Remark 4.1.4(5), (⋈Intro_j) rule: the `cutme Intro` changed root time is
strictly later than the source.
-/
theorem cutMeIntro_root_get_changed_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (T.get j) ≺ ((Derivation.cutMeIntro deriv j target hshape hconsistent).root.get j) := by
  rw [cutMeIntro_root_get_changed deriv j target hshape hconsistent, hshape]
  have hnext : ConsistentTime (↱ target t) := by
    rw [← hshape]
    exact T.consistent j
  exact
    ⟨nextIndex_le_cutMe target t,
      (cutMe_ne_nextIndex_of_consistent hconsistent hnext).symm⟩

/--
Remark 4.1.3, programmatic derivation-rules remark: `cutme Intro` really
changes the indicated index.
-/
theorem cutMeIntro_root_get_changed_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (Derivation.cutMeIntro deriv j target hshape hconsistent).root.get j ≠ T.get j := by
  rw [cutMeIntro_root_get_changed deriv j target hshape hconsistent, hshape]
  have hnext : ConsistentTime (↱ target t) := by
    rw [← hshape]
    exact T.consistent j
  exact cutMe_ne_nextIndex_of_consistent hconsistent hnext

/-- Remark 4.1.3, `cutme Intro`: every non-indicated index is unchanged. -/
theorem cutMeIntro_root_get_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j idx : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t))
    (hidx : idx ≠ j) :
    (Derivation.cutMeIntro deriv j target hshape hconsistent).root.get idx = T.get idx := by
  simp [Derivation.root, Prepath.replace_get_ne T hidx]

/--
Remark 4.1.4(1): `cutme Intro` changes precisely the indicated index.
-/
theorem cutMeIntro_root_changes_precisely_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (Derivation.cutMeIntro deriv j target hshape hconsistent).root.get j =
        ⋊ target t ∧
      (Derivation.cutMeIntro deriv j target hshape hconsistent).root.get j ≠ T.get j ∧
      ∀ idx : T.Index, idx ≠ j →
        (Derivation.cutMeIntro deriv j target hshape hconsistent).root.get idx =
          T.get idx := by
  exact
    ⟨cutMeIntro_root_get_changed deriv j target hshape hconsistent,
      cutMeIntro_root_get_changed_ne deriv j target hshape hconsistent,
      fun idx hidx =>
        cutMeIntro_root_get_ne deriv j idx target hshape hconsistent hidx⟩

/-- Remark 4.1.3, `cutyou Intro`: the root length is unchanged. -/
theorem cutYouIntro_root_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (Derivation.cutYouIntro deriv j target hshape hconsistent).root.lengthValue =
      T.lengthValue := by
  rfl

/-- Remark 4.1.4, `cutyou Intro`: the source index is a `nextIndex` state. -/
theorem cutYouIntro_source_get_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (_hconsistent : ConsistentTime (⋉ target t)) :
    deriv.root.get j = ↱ target t := by
  exact hshape

/-- Remark 4.1.3, `cutyou Intro`: the indicated index receives `cutYou`. -/
theorem cutYouIntro_root_get_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (Derivation.cutYouIntro deriv j target hshape hconsistent).root.get j =
      ⋉ target t := by
  simp [Derivation.root]

/--
Remark 4.1.3, programmatic derivation-rules remark: the `cutyou Intro`
output at the changed index is structurally consistent.
-/
theorem cutYouIntro_root_get_changed_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    ConsistentTime
      ((Derivation.cutYouIntro deriv j target hshape hconsistent).root.get j) := by
  rw [cutYouIntro_root_get_changed deriv j target hshape hconsistent]
  exact hconsistent

/--
Remark 4.1.4(6), (⋉Intro_j) rule: the `cutyou Intro` changed root time is later
than the source.
-/
theorem cutYouIntro_root_get_changed_le {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (T.get j) ≼ ((Derivation.cutYouIntro deriv j target hshape hconsistent).root.get j) := by
  rw [cutYouIntro_root_get_changed deriv j target hshape hconsistent, hshape]
  exact nextIndex_le_cutYou target t

/--
Remark 4.1.4(6), (⋉Intro_j) rule: the `cutyou Intro` changed root time is
strictly later than the source.
-/
theorem cutYouIntro_root_get_changed_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (T.get j) ≺ ((Derivation.cutYouIntro deriv j target hshape hconsistent).root.get j) := by
  rw [cutYouIntro_root_get_changed deriv j target hshape hconsistent, hshape]
  have hnext : ConsistentTime (↱ target t) := by
    rw [← hshape]
    exact T.consistent j
  exact
    ⟨nextIndex_le_cutYou target t,
      (cutYou_ne_nextIndex_of_consistent hconsistent hnext).symm⟩

/--
Remark 4.1.3, programmatic derivation-rules remark: `cutyou Intro` really
changes the indicated index.
-/
theorem cutYouIntro_root_get_changed_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (Derivation.cutYouIntro deriv j target hshape hconsistent).root.get j ≠ T.get j := by
  rw [cutYouIntro_root_get_changed deriv j target hshape hconsistent, hshape]
  have hnext : ConsistentTime (↱ target t) := by
    rw [← hshape]
    exact T.consistent j
  exact cutYou_ne_nextIndex_of_consistent hconsistent hnext

/-- Remark 4.1.3, `cutyou Intro`: every non-indicated index is unchanged. -/
theorem cutYouIntro_root_get_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j idx : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t))
    (hidx : idx ≠ j) :
    (Derivation.cutYouIntro deriv j target hshape hconsistent).root.get idx = T.get idx := by
  simp [Derivation.root, Prepath.replace_get_ne T hidx]

/--
Remark 4.1.4(1): `cutyou Intro` changes precisely the indicated index.
-/
theorem cutYouIntro_root_changes_precisely_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (Derivation.cutYouIntro deriv j target hshape hconsistent).root.get j =
        ⋉ target t ∧
      (Derivation.cutYouIntro deriv j target hshape hconsistent).root.get j ≠ T.get j ∧
      ∀ idx : T.Index, idx ≠ j →
        (Derivation.cutYouIntro deriv j target hshape hconsistent).root.get idx =
          T.get idx := by
  exact
    ⟨cutYouIntro_root_get_changed deriv j target hshape hconsistent,
      cutYouIntro_root_get_changed_ne deriv j target hshape hconsistent,
      fun idx hidx =>
        cutYouIntro_root_get_ne deriv j idx target hshape hconsistent hidx⟩

/-- Remark 4.1.3, Cut rule: the root length is unchanged. -/
theorem cut_root_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.lengthValue =
      T.lengthValue := by
  rfl

/-- Remark 4.1.4, Cut rule: the source indexes satisfy `i < j < k`. -/
theorem cut_source_index_order {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {i j k : T.Index} (hij : i.val < j.val) (hjk : j.val < k.val) :
    i.val < j.val ∧ j.val < k.val := by
  exact ⟨hij, hjk⟩

/-- Remark 4.1.4, Cut rule: the source upper index has the `cutYou` shape. -/
theorem cut_source_get_upper_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j k : T.Index} {tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk) :
    deriv.root.get k = ⋉ (T.paperIndex j) tk := by
  exact hk

/-- Remark 4.1.4, Cut rule: the source center index has the `cutMe` shape. -/
theorem cut_source_get_center_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j : T.Index} {tj tk : Time}
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk))) :
    deriv.root.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)) := by
  exact hj

/--
Remark 4.1.4, Cut rule: the source lower index has the displayed
attestation-to-`cutMe` shape.
-/
theorem cut_source_get_lower_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j : T.Index} {ti tj tk : Time}
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk)))) :
    deriv.root.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))) := by
  exact hi

/-- Definition 4.1.1, Cut rule: the indicated upper index receives `nextIndex`. -/
theorem cut_root_get_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get k =
      ↱ (T.paperIndex i) tk := by
  simp [Derivation.root]

/--
Remark 4.1.3, programmatic derivation-rules remark: the Cut output at the
changed upper index is structurally consistent.
-/
theorem cut_root_get_changed_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    ConsistentTime
      ((Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get k) := by
  rw [cut_root_get_changed deriv hij hjk hk hj hi hconsistent]
  exact hconsistent

/--
Remark 4.1.4(7), Cut rule: the `Cut` changed upper root time is later than the
source.
-/
theorem cut_root_get_changed_le {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (T.get k) ≼ ((Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get k) := by
  rw [cut_root_get_changed deriv hij hjk hk hj hi hconsistent, hk]
  have hpaper : T.paperIndex i < T.paperIndex j := by
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ hij
  exact cutYou_le_nextIndex_of_lt hpaper tk

/--
Remark 4.1.4(7), Cut rule: the `Cut` changed upper root time is strictly later
than the source.
-/
theorem cut_root_get_changed_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (T.get k) ≺ ((Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get k) := by
  rw [cut_root_get_changed deriv hij hjk hk hj hi hconsistent, hk]
  have hpaper : T.paperIndex i < T.paperIndex j := by
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ hij
  have hcutYou : ConsistentTime (⋉ (T.paperIndex j) tk) := by
    rw [← hk]
    exact T.consistent k
  exact
    ⟨cutYou_le_nextIndex_of_lt hpaper tk,
      cutYou_ne_nextIndex_of_consistent hcutYou hconsistent⟩

/--
Remark 4.1.3, programmatic derivation-rules remark: `Cut` really changes
the indicated upper index.
-/
theorem cut_root_get_changed_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get k ≠ T.get k := by
  rw [cut_root_get_changed deriv hij hjk hk hj hi hconsistent, hk]
  have hcutYou : ConsistentTime (⋉ (T.paperIndex j) tk) := by
    rw [← hk]
    exact T.consistent k
  exact (cutYou_ne_nextIndex_of_consistent hcutYou hconsistent).symm

/-- Definition 4.1.1, Cut rule: every non-upper index is unchanged. -/
theorem cut_root_get_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk))
    {idx : T.Index} (hidx : idx ≠ k) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get idx = T.get idx := by
  simp [Derivation.root, Prepath.replace_get_ne T hidx]

/--
Remark 4.1.4(1): `Cut` changes precisely the indicated upper index.
-/
theorem cut_root_changes_precisely_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get k =
        ↱ (T.paperIndex i) tk ∧
      (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get k ≠ T.get k ∧
      ∀ idx : T.Index, idx ≠ k →
        (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get idx = T.get idx := by
  exact
    ⟨cut_root_get_changed deriv hij hjk hk hj hi hconsistent,
      cut_root_get_changed_ne deriv hij hjk hk hj hi hconsistent,
      fun _ hidx => cut_root_get_ne deriv hij hjk hk hj hi hconsistent hidx⟩

/-- Definition 4.1.1, Cut rule: the lower index `i` is unchanged. -/
theorem cut_root_get_lower_unchanged {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get i = T.get i := by
  apply cut_root_get_ne deriv hij hjk hk hj hi hconsistent
  intro hik
  have hval : i.val = k.val := congrArg Fin.val hik
  omega

/-- Definition 4.1.1, Cut rule: the center index `j` is unchanged. -/
theorem cut_root_get_center_unchanged {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get j = T.get j := by
  apply cut_root_get_ne deriv hij hjk hk hj hi hconsistent
  intro hjk_eq
  have hval : j.val = k.val := congrArg Fin.val hjk_eq
  omega

/--
Definition 4.1.1, Cut rule: after the rule, the center index still has the
displayed `cutMe` attestation shape.
-/
theorem cut_root_get_center_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)) := by
  rw [cut_root_get_center_unchanged deriv hij hjk hk hj hi hconsistent, hj]

/--
Definition 4.1.1, Cut rule: after the rule, the lower index still has the
displayed attestation-to-`cutMe` shape.
-/
theorem cut_root_get_lower_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    (Derivation.cut deriv hij hjk hk hj hi hconsistent).root.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))) := by
  rw [cut_root_get_lower_unchanged deriv hij hjk hk hj hi hconsistent, hi]

end Derivation

/-- Definition 4.1.1(5), `Path(L)`: a prepath is a path when it equals `root(Π)` for some derivation `Π`. -/
def IsPath (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) : Prop :=
  Nonempty (Derivation Time T)

/-- Definition 4.1.1(5), `Path(L)`: the type of paths, i.e. prepaths equal to `root(Π)` for some derivation `Π`. -/
def Path (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :=
  {T : Prepath Time // IsPath Time T}

/-- Definition 4.1.1: a `Path` carries its path proof. -/
theorem path_isPath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time) :
    IsPath Time P.1 :=
  P.2

/-- Definition 4.1.1: a `Path` carries a derivation of its underlying prepath. -/
theorem path_exists_derivation {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time) :
    Nonempty (Derivation Time P.1) :=
  P.2

/-- Definition 4.1.1: a `Path` is nonempty because its underlying prepath is nonempty. -/
theorem path_length_pos {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time) :
    0 < P.1.length :=
  P.1.length_pos

/-- Definition 4.1.1: every entry of a `Path` is a consistent time. -/
theorem path_get_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (i : P.1.Index) :
    ConsistentTime (P.1.get i) :=
  P.1.consistent i

/-- Remark 4.1.3, Init rule: an initial prepath is a path. -/
theorem isPath_init {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat} (hpos : 0 < n)
    (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i)) :
    IsPath Time (initPrepath Time hpos base hconsistent) :=
  ⟨Derivation.init (Time := Time) hpos base hconsistent⟩

/-- Remark 4.1.3, Inc rule: paths are closed under valid increments. -/
theorem isPath_inc {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (hpath : IsPath Time T) (j : T.Index) {t' : Time}
    (hlt : (T.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (T.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    IsPath Time (T.replace j t' hlt.1.1.symm hconsistent) := by
  rcases hpath with ⟨deriv⟩
  exact ⟨Derivation.inc deriv j hlt hflag hconsistent⟩

/--
Lemma 3.2.8, path-rule corollary: a scope-extruding
cutting flag gives an `Inc` step once the strictness and consistency side
conditions of the path rule are supplied.
-/
theorem isPath_scopeFlagInc {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (hpath : IsPath Time T) (j : T.Index)
    (Q : Flag Time) (hmem : cuttingFlagSet.member Q)
    {t s : Time}
    (hshape : T.get j = Q t)
    (hscope : ScopeExtruding Q)
    (hneq : Q (t # s) ≠ Q t)
    (hconsistent : ConsistentTime (Q (t # s))) :
    ∃ hlt : (T.get j) ≺ (Q (t # s)),
      flagOf cuttingFlagSet (T.get j) =
        flagOf cuttingFlagSet (Q (t # s)) ∧
      IsPath Time (T.replace j (Q (t # s)) hlt.1.1.symm hconsistent) := by
  have hleQ :
      (Q t) ≼ (Q (t # s)) :=
    scope_flag Q hscope t s
  have hltQ :
      (Q t) ≺ (Q (t # s)) := by
    refine ⟨hleQ, ?_⟩
    intro heq
    exact hneq heq.symm
  have hlt :
      (T.get j) ≺ (Q (t # s)) := by
    rw [hshape]
    exact hltQ
  have hsourceCons : ConsistentTime (Q t) := by
    rw [← hshape]
    exact T.consistent j
  have hsameFlag :
      flagOf cuttingFlagSet (Q t) =
        flagOf cuttingFlagSet (Q (t # s)) :=
    same_cutting_flag_flagOf_eq Q hmem
      hsourceCons hconsistent
  have hflag :
      flagOf cuttingFlagSet (T.get j) =
        flagOf cuttingFlagSet (Q (t # s)) := by
    calc
      flagOf cuttingFlagSet (T.get j) =
          flagOf cuttingFlagSet (Q t) := by rw [hshape]
      _ = flagOf cuttingFlagSet (Q (t # s)) := hsameFlag
  exact ⟨hlt, hflag, isPath_inc hpath j hlt hflag hconsistent⟩

/-- Remark 4.1.3, cut-me introduction rule: paths are closed under cut-me intro. -/
theorem isPath_cutMeIntro {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (hpath : IsPath Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    IsPath Time (T.replace j (⋊ target t) (by
      calc
        controller (⋊ target t) = controller t :=
          (⋊ target).controller_preserving t
        _ = controller (↱ target t) :=
          ((↱ target).controller_preserving t).symm
        _ = controller (T.get j) := by rw [hshape])
      hconsistent) := by
  rcases hpath with ⟨deriv⟩
  exact ⟨Derivation.cutMeIntro deriv j target hshape hconsistent⟩

/-- Remark 4.1.3, cut-you introduction rule: paths are closed under cut-you intro. -/
theorem isPath_cutYouIntro {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (hpath : IsPath Time T) (j : T.Index) (target : Nat) {t : Time}
    (hshape : T.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    IsPath Time (T.replace j (⋉ target t) (by
      calc
        controller (⋉ target t) = controller t :=
          (⋉ target).controller_preserving t
        _ = controller (↱ target t) :=
          ((↱ target).controller_preserving t).symm
        _ = controller (T.get j) := by rw [hshape])
      hconsistent) := by
  rcases hpath with ⟨deriv⟩
  exact ⟨Derivation.cutYouIntro deriv j target hshape hconsistent⟩

/-- Remark 4.1.3, Cut rule: paths are closed under valid cuts. -/
theorem isPath_cut {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (hpath : IsPath Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    IsPath Time (T.replace k (↱ (T.paperIndex i) tk) (by
      calc
        controller (↱ (T.paperIndex i) tk) =
            controller tk :=
          (↱ (T.paperIndex i)).controller_preserving tk
        _ = controller (⋉ (T.paperIndex j) tk) :=
          ((⋉ (T.paperIndex j)).controller_preserving tk).symm
        _ = controller (T.get k) := by rw [hk])
      hconsistent) := by
  rcases hpath with ⟨deriv⟩
  exact ⟨Derivation.cut deriv hij hjk hk hj hi hconsistent⟩

/-- Remark 4.1.3, Init rule, bundled `Path` form. -/
def path_init {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat} (hpos : 0 < n)
    (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i)) :
    Path Time :=
  ⟨initPrepath Time hpos base hconsistent, isPath_init hpos base hconsistent⟩

/-- Remark 4.1.3, Init bundled `Path` form: the output length is `n`. -/
theorem path_init_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat} (hpos : 0 < n)
    (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i)) :
    (path_init hpos base hconsistent).1.lengthValue = n := by
  rfl

/-- Remark 4.1.3, Init bundled `Path` form: the output is pointwise `initTime`. -/
theorem path_init_get {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat} (hpos : 0 < n)
    (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (path_init hpos base hconsistent).1.Index) :
    (path_init hpos base hconsistent).1.get i = initTime Time base i := by
  rfl

/--
Remark 4.1.3, bundled `Path` form: every Init output entry is consistent.
-/
theorem path_init_get_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat} (hpos : 0 < n)
    (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (i : (path_init hpos base hconsistent).1.Index) :
    ConsistentTime ((path_init hpos base hconsistent).1.get i) := by
  rw [path_init_get hpos base hconsistent i]
  exact hconsistent i

/-- Remark 4.1.3, Inc rule, bundled `Path` form. -/
def path_inc {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time) (j : P.1.Index)
    {t' : Time}
    (hlt : lt (P.1.get j) t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    Path Time :=
  ⟨P.1.replace j t' hlt.1.1.symm hconsistent,
    isPath_inc P.2 j hlt hflag hconsistent⟩

/-- Remark 4.1.3, Inc bundled `Path` form: the output length is unchanged. -/
theorem path_inc_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time) (j : P.1.Index)
    {t' : Time}
    (hlt : (P.1.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (path_inc P j hlt hflag hconsistent).1.lengthValue = P.1.lengthValue := by
  rfl

/-- Remark 4.1.3, Inc bundled `Path` form: the indicated index is changed. -/
theorem path_inc_get_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time) (j : P.1.Index)
    {t' : Time}
    (hlt : (P.1.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (path_inc P j hlt hflag hconsistent).1.get j = t' := by
  simp [path_inc]

/--
Remark 4.1.3, bundled `Path` form: the Inc replacement keeps the changed
entry at the same controller.
-/
theorem path_inc_get_changed_controller {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) {t' : Time}
    (hlt : (P.1.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    controller ((path_inc P j hlt hflag hconsistent).1.get j) =
      controller (P.1.get j) := by
  rw [path_inc_get_changed P j hlt hflag hconsistent]
  exact hlt.1.1.symm

/--
Remark 4.1.3, bundled `Path` form: the Inc output at the changed index is
strictly later than the source entry.
-/
theorem path_inc_get_changed_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) {t' : Time}
    (hlt : (P.1.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (P.1.get j) ≺ ((path_inc P j hlt hflag hconsistent).1.get j) := by
  rw [path_inc_get_changed P j hlt hflag hconsistent]
  exact hlt

/--
Remark 4.1.3, bundled `Path` form: the Inc output at the changed index has
the same cutting-flag lookup as the source entry.
-/
theorem path_inc_get_changed_flag_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) {t' : Time}
    (hlt : (P.1.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet
        ((path_inc P j hlt hflag hconsistent).1.get j) := by
  rw [path_inc_get_changed P j hlt hflag hconsistent]
  exact hflag

/--
Remark 4.1.3, bundled `Path` form: the Inc output at the changed index is
consistent.
-/
theorem path_inc_get_changed_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) {t' : Time}
    (hlt : (P.1.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    ConsistentTime ((path_inc P j hlt hflag hconsistent).1.get j) := by
  rw [path_inc_get_changed P j hlt hflag hconsistent]
  exact hconsistent

/--
Remark 4.1.3, bundled `Path` form: Inc really changes the indicated index.
-/
theorem path_inc_get_changed_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) {t' : Time}
    (hlt : (P.1.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (path_inc P j hlt hflag hconsistent).1.get j ≠ P.1.get j := by
  rw [path_inc_get_changed P j hlt hflag hconsistent]
  exact hlt.2.symm

/-- Remark 4.1.3, Inc bundled `Path` form: every non-indicated index is unchanged. -/
theorem path_inc_get_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time) (j : P.1.Index)
    {t' : Time}
    (hlt : (P.1.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') {idx : P.1.Index}
    (hidx : idx ≠ j) :
    (path_inc P j hlt hflag hconsistent).1.get idx = P.1.get idx := by
  simp [path_inc, Prepath.replace_get_ne P.1 hidx]

/--
Remark 4.1.4(1), bundled `Path` form: `Inc` changes precisely the indicated
index.
-/
theorem path_inc_changes_precisely_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) {t' : Time}
    (hlt : (P.1.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (P.1.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (path_inc P j hlt hflag hconsistent).1.get j = t' ∧
      (path_inc P j hlt hflag hconsistent).1.get j ≠ P.1.get j ∧
      ∀ idx : P.1.Index, idx ≠ j →
        (path_inc P j hlt hflag hconsistent).1.get idx = P.1.get idx := by
  exact
    ⟨path_inc_get_changed P j hlt hflag hconsistent,
      path_inc_get_changed_ne P j hlt hflag hconsistent,
      fun idx hidx => path_inc_get_ne P j hlt hflag hconsistent hidx⟩

/--
Lemma 3.2.8, bundled `Path` form: a scope-extruding cutting flag gives an
`Inc` step once the strictness and consistency side conditions of the path rule
are supplied.
-/
def path_scopeFlagInc {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time) (j : P.1.Index)
    (Q : Flag Time) (hmem : cuttingFlagSet.member Q)
    {t s : Time}
    (hshape : P.1.get j = Q t)
    (hscope : ScopeExtruding Q)
    (hneq : Q (t # s) ≠ Q t)
    (hconsistent : ConsistentTime (Q (t # s))) :
    {P' : Path Time //
      ∃ hlt : lt (P.1.get j) (Q (t # s)),
        flagOf cuttingFlagSet (P.1.get j) =
          flagOf cuttingFlagSet (Q (t # s)) ∧
        P'.1 = P.1.replace j (Q (t # s)) hlt.1.1.symm hconsistent} := by
  have hleQ :
      le (Q t) (Q (t # s)) :=
    scope_flag Q hscope t s
  have hltQ :
      lt (Q t) (Q (t # s)) := by
    refine ⟨hleQ, ?_⟩
    intro heq
    exact hneq heq.symm
  have hlt :
      lt (P.1.get j) (Q (t # s)) := by
    rw [hshape]
    exact hltQ
  have hsourceCons : ConsistentTime (Q t) := by
    rw [← hshape]
    exact P.1.consistent j
  have hsameFlag :
      flagOf cuttingFlagSet (Q t) =
        flagOf cuttingFlagSet (Q (t # s)) :=
    same_cutting_flag_flagOf_eq Q hmem
      hsourceCons hconsistent
  have hflag :
      flagOf cuttingFlagSet (P.1.get j) =
        flagOf cuttingFlagSet (Q (t # s)) := by
    calc
      flagOf cuttingFlagSet (P.1.get j) =
          flagOf cuttingFlagSet (Q t) := by rw [hshape]
      _ = flagOf cuttingFlagSet (Q (t # s)) := hsameFlag
  have hpath :
      IsPath Time (P.1.replace j (Q (t # s)) hlt.1.1.symm hconsistent) :=
    isPath_inc P.2 j hlt hflag hconsistent
  exact ⟨⟨P.1.replace j (Q (t # s)) hlt.1.1.symm hconsistent, hpath⟩,
    ⟨hlt, hflag, rfl⟩⟩

/-- Remark 4.1.3, cut-me introduction rule, bundled `Path` form. -/
def path_cutMeIntro {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    Path Time := by
  exact ⟨P.1.replace j (⋊ target t) (by
      calc
        controller (⋊ target t) = controller t :=
          (⋊ target).controller_preserving t
        _ = controller (↱ target t) :=
          ((↱ target).controller_preserving t).symm
        _ = controller (P.1.get j) := by rw [hshape])
      hconsistent,
    isPath_cutMeIntro P.2 j target hshape hconsistent⟩

/-- Remark 4.1.3, `cutme Intro` bundled `Path` form: the output length is unchanged. -/
theorem path_cutMeIntro_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (path_cutMeIntro P j target hshape hconsistent).1.lengthValue = P.1.lengthValue := by
  rfl

/--
Definition 4.1.1, bundled `Path` form: the `cutme Intro` source index has the
displayed `nextIndex` shape.
-/
theorem path_cutMeIntro_source_get_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (_hconsistent : ConsistentTime (⋊ target t)) :
    P.1.get j = ↱ target t := by
  exact hshape

/-- Remark 4.1.3, `cutme Intro` bundled `Path` form: the indicated index receives `cutMe`. -/
theorem path_cutMeIntro_get_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (path_cutMeIntro P j target hshape hconsistent).1.get j =
      ⋊ target t := by
  simp [path_cutMeIntro]

/--
Remark 4.1.3, bundled `Path` form: the `cutme Intro` replacement keeps the
changed entry at the same controller.
-/
theorem path_cutMeIntro_get_changed_controller {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    controller ((path_cutMeIntro P j target hshape hconsistent).1.get j) =
      controller (P.1.get j) := by
  rw [path_cutMeIntro_get_changed P j target hshape hconsistent]
  calc
    controller (⋊ target t) = controller t :=
      (⋊ target).controller_preserving t
    _ = controller (↱ target t) :=
      ((↱ target).controller_preserving t).symm
    _ = controller (P.1.get j) := by rw [hshape]

/--
Remark 4.1.3, bundled `Path` form: the `cutme Intro` output at the changed
index is consistent.
-/
theorem path_cutMeIntro_get_changed_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    ConsistentTime
      ((path_cutMeIntro P j target hshape hconsistent).1.get j) := by
  rw [path_cutMeIntro_get_changed P j target hshape hconsistent]
  exact hconsistent

/--
Definition 4.1.1, bundled `Path` form: the `cutme Intro` output at the changed
index is later than the source.
-/
theorem path_cutMeIntro_get_changed_le {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (P.1.get j) ≼ ((path_cutMeIntro P j target hshape hconsistent).1.get j) := by
  rw [path_cutMeIntro_get_changed P j target hshape hconsistent, hshape]
  exact nextIndex_le_cutMe target t

/--
Definition 4.1.1, bundled `Path` form: the `cutme Intro` output at the changed
index is strictly later than the source.
-/
theorem path_cutMeIntro_get_changed_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (P.1.get j) ≺ ((path_cutMeIntro P j target hshape hconsistent).1.get j) := by
  rw [path_cutMeIntro_get_changed P j target hshape hconsistent, hshape]
  have hnext :
      ConsistentTime (↱ target t) := by
    rw [← hshape]
    exact P.1.consistent j
  exact
    ⟨nextIndex_le_cutMe target t,
      (cutMe_ne_nextIndex_of_consistent hconsistent hnext).symm⟩

/--
Remark 4.1.3, bundled `Path` form: `cutme Intro` really changes the
indicated index.
-/
theorem path_cutMeIntro_get_changed_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (path_cutMeIntro P j target hshape hconsistent).1.get j ≠ P.1.get j := by
  rw [path_cutMeIntro_get_changed P j target hshape hconsistent, hshape]
  have hnext :
      ConsistentTime (↱ target t) := by
    rw [← hshape]
    exact P.1.consistent j
  exact cutMe_ne_nextIndex_of_consistent hconsistent hnext

/-- Remark 4.1.3, `cutme Intro` bundled `Path` form: every non-indicated index is unchanged. -/
theorem path_cutMeIntro_get_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j idx : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t))
    (hidx : idx ≠ j) :
    (path_cutMeIntro P j target hshape hconsistent).1.get idx = P.1.get idx := by
  simp [path_cutMeIntro, Prepath.replace_get_ne P.1 hidx]

/--
Remark 4.1.4(1), bundled `Path` form: `cutme Intro` changes precisely the
indicated index.
-/
theorem path_cutMeIntro_changes_precisely_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋊ target t)) :
    (path_cutMeIntro P j target hshape hconsistent).1.get j =
        ⋊ target t ∧
      (path_cutMeIntro P j target hshape hconsistent).1.get j ≠ P.1.get j ∧
      ∀ idx : P.1.Index, idx ≠ j →
        (path_cutMeIntro P j target hshape hconsistent).1.get idx =
          P.1.get idx := by
  exact
    ⟨path_cutMeIntro_get_changed P j target hshape hconsistent,
      path_cutMeIntro_get_changed_ne P j target hshape hconsistent,
      fun idx hidx =>
        path_cutMeIntro_get_ne P j idx target hshape hconsistent hidx⟩

/-- Remark 4.1.3, cut-you introduction rule, bundled `Path` form. -/
def path_cutYouIntro {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    Path Time := by
  exact ⟨P.1.replace j (⋉ target t) (by
      calc
        controller (⋉ target t) = controller t :=
          (⋉ target).controller_preserving t
        _ = controller (↱ target t) :=
          ((↱ target).controller_preserving t).symm
        _ = controller (P.1.get j) := by rw [hshape])
      hconsistent,
    isPath_cutYouIntro P.2 j target hshape hconsistent⟩

/-- Remark 4.1.3, `cutyou Intro` bundled `Path` form: the output length is unchanged. -/
theorem path_cutYouIntro_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (path_cutYouIntro P j target hshape hconsistent).1.lengthValue = P.1.lengthValue := by
  rfl

/--
Definition 4.1.1, bundled `Path` form: the `cutyou Intro` source index has the
displayed `nextIndex` shape.
-/
theorem path_cutYouIntro_source_get_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (_hconsistent : ConsistentTime (⋉ target t)) :
    P.1.get j = ↱ target t := by
  exact hshape

/-- Remark 4.1.3, `cutyou Intro` bundled `Path` form: the indicated index receives `cutYou`. -/
theorem path_cutYouIntro_get_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (path_cutYouIntro P j target hshape hconsistent).1.get j =
      ⋉ target t := by
  simp [path_cutYouIntro]

/--
Remark 4.1.3, bundled `Path` form: the `cutyou Intro` replacement keeps the
changed entry at the same controller.
-/
theorem path_cutYouIntro_get_changed_controller {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    controller ((path_cutYouIntro P j target hshape hconsistent).1.get j) =
      controller (P.1.get j) := by
  rw [path_cutYouIntro_get_changed P j target hshape hconsistent]
  calc
    controller (⋉ target t) = controller t :=
      (⋉ target).controller_preserving t
    _ = controller (↱ target t) :=
      ((↱ target).controller_preserving t).symm
    _ = controller (P.1.get j) := by rw [hshape]

/--
Remark 4.1.3, bundled `Path` form: the `cutyou Intro` output at the changed
index is consistent.
-/
theorem path_cutYouIntro_get_changed_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    ConsistentTime
      ((path_cutYouIntro P j target hshape hconsistent).1.get j) := by
  rw [path_cutYouIntro_get_changed P j target hshape hconsistent]
  exact hconsistent

/--
Definition 4.1.1, bundled `Path` form: the `cutyou Intro` output at the changed
index is later than the source.
-/
theorem path_cutYouIntro_get_changed_le {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (P.1.get j) ≼ ((path_cutYouIntro P j target hshape hconsistent).1.get j) := by
  rw [path_cutYouIntro_get_changed P j target hshape hconsistent, hshape]
  exact nextIndex_le_cutYou target t

/--
Definition 4.1.1, bundled `Path` form: the `cutyou Intro` output at the changed
index is strictly later than the source.
-/
theorem path_cutYouIntro_get_changed_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (P.1.get j) ≺ ((path_cutYouIntro P j target hshape hconsistent).1.get j) := by
  rw [path_cutYouIntro_get_changed P j target hshape hconsistent, hshape]
  have hnext :
      ConsistentTime (↱ target t) := by
    rw [← hshape]
    exact P.1.consistent j
  exact
    ⟨nextIndex_le_cutYou target t,
      (cutYou_ne_nextIndex_of_consistent hconsistent hnext).symm⟩

/--
Remark 4.1.3, bundled `Path` form: `cutyou Intro` really changes the
indicated index.
-/
theorem path_cutYouIntro_get_changed_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (path_cutYouIntro P j target hshape hconsistent).1.get j ≠ P.1.get j := by
  rw [path_cutYouIntro_get_changed P j target hshape hconsistent, hshape]
  have hnext :
      ConsistentTime (↱ target t) := by
    rw [← hshape]
    exact P.1.consistent j
  exact cutYou_ne_nextIndex_of_consistent hconsistent hnext

/-- Remark 4.1.3, `cutyou Intro` bundled `Path` form: every non-indicated index is unchanged. -/
theorem path_cutYouIntro_get_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j idx : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t))
    (hidx : idx ≠ j) :
    (path_cutYouIntro P j target hshape hconsistent).1.get idx = P.1.get idx := by
  simp [path_cutYouIntro, Prepath.replace_get_ne P.1 hidx]

/--
Remark 4.1.4(1), bundled `Path` form: `cutyou Intro` changes precisely the
indicated index.
-/
theorem path_cutYouIntro_changes_precisely_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    (j : P.1.Index) (target : Nat) {t : Time}
    (hshape : P.1.get j = ↱ target t)
    (hconsistent : ConsistentTime (⋉ target t)) :
    (path_cutYouIntro P j target hshape hconsistent).1.get j =
        ⋉ target t ∧
      (path_cutYouIntro P j target hshape hconsistent).1.get j ≠ P.1.get j ∧
      ∀ idx : P.1.Index, idx ≠ j →
        (path_cutYouIntro P j target hshape hconsistent).1.get idx =
          P.1.get idx := by
  exact
    ⟨path_cutYouIntro_get_changed P j target hshape hconsistent,
      path_cutYouIntro_get_changed_ne P j target hshape hconsistent,
      fun idx hidx =>
        path_cutYouIntro_get_ne P j idx target hshape hconsistent hidx⟩

/-- Remark 4.1.3, Cut rule, bundled `Path` form. -/
def path_cut {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    Path Time := by
  exact ⟨P.1.replace k (↱ (P.1.paperIndex i) tk) (by
      calc
        controller (↱ (P.1.paperIndex i) tk) =
            controller tk :=
          (↱ (P.1.paperIndex i)).controller_preserving tk
        _ = controller (⋉ (P.1.paperIndex j) tk) :=
          ((⋉ (P.1.paperIndex j)).controller_preserving tk).symm
        _ = controller (P.1.get k) := by rw [hk])
      hconsistent,
    isPath_cut P.2 hij hjk hk hj hi hconsistent⟩

/--
Definition 4.1.1, bundled `Path` form: the `Cut` rule source indexes satisfy
the displayed lower/center/upper order.
-/
theorem path_cut_source_index_order {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (_hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (_hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (_hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (_hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    i.val < j.val ∧ j.val < k.val := by
  exact ⟨hij, hjk⟩

/--
Definition 4.1.1, bundled `Path` form: the `Cut` source upper index has the
displayed `cutYou` shape.
-/
theorem path_cut_source_get_upper_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (_hij : i.val < j.val) (_hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (_hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (_hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (_hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    P.1.get k = ⋉ (P.1.paperIndex j) tk := by
  exact hk

/--
Definition 4.1.1, bundled `Path` form: the `Cut` source center index has the
displayed `cutMe`-attestation shape.
-/
theorem path_cut_source_get_center_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (_hij : i.val < j.val) (_hjk : j.val < k.val)
    {ti tj tk : Time}
    (_hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (_hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (_hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)) := by
  exact hj

/--
Definition 4.1.1, bundled `Path` form: the `Cut` source lower index has the
displayed attestation-to-`cutMe` shape.
-/
theorem path_cut_source_get_lower_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (_hij : i.val < j.val) (_hjk : j.val < k.val)
    {ti tj tk : Time}
    (_hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (_hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (_hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))) := by
  exact hi

/-- Remark 4.1.3, Cut bundled `Path` form: the output length is unchanged. -/
theorem path_cut_lengthValue {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (path_cut P hij hjk hk hj hi hconsistent).1.lengthValue = P.1.lengthValue := by
  rfl

/-- Remark 4.1.3, Cut bundled `Path` form: the upper index receives `nextIndex`. -/
theorem path_cut_get_changed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (path_cut P hij hjk hk hj hi hconsistent).1.get k =
      ↱ (P.1.paperIndex i) tk := by
  simp [path_cut]

/--
Remark 4.1.3, bundled `Path` form: the Cut replacement keeps the changed
upper entry at the same controller.
-/
theorem path_cut_get_changed_controller {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    controller ((path_cut P hij hjk hk hj hi hconsistent).1.get k) =
      controller (P.1.get k) := by
  rw [path_cut_get_changed P hij hjk hk hj hi hconsistent]
  calc
    controller (↱ (P.1.paperIndex i) tk) =
        controller tk :=
      (↱ (P.1.paperIndex i)).controller_preserving tk
    _ = controller (⋉ (P.1.paperIndex j) tk) :=
      ((⋉ (P.1.paperIndex j)).controller_preserving tk).symm
    _ = controller (P.1.get k) := by rw [hk]

/--
Remark 4.1.3, bundled `Path` form: the Cut output at the changed upper
index is consistent.
-/
theorem path_cut_get_changed_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    ConsistentTime
      ((path_cut P hij hjk hk hj hi hconsistent).1.get k) := by
  rw [path_cut_get_changed P hij hjk hk hj hi hconsistent]
  exact hconsistent

/--
Definition 4.1.1, bundled `Path` form: the `Cut` output at the changed upper
index is later than the source.
-/
theorem path_cut_get_changed_le {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (P.1.get k) ≼ ((path_cut P hij hjk hk hj hi hconsistent).1.get k) := by
  rw [path_cut_get_changed P hij hjk hk hj hi hconsistent, hk]
  have hpaper : P.1.paperIndex i < P.1.paperIndex j := by
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ hij
  exact cutYou_le_nextIndex_of_lt hpaper tk

/--
Definition 4.1.1, bundled `Path` form: the `Cut` output at the changed upper
index is strictly later than the source.
-/
theorem path_cut_get_changed_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (P.1.get k) ≺ ((path_cut P hij hjk hk hj hi hconsistent).1.get k) := by
  rw [path_cut_get_changed P hij hjk hk hj hi hconsistent, hk]
  have hpaper : P.1.paperIndex i < P.1.paperIndex j := by
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ hij
  have hcutYou :
      ConsistentTime (⋉ (P.1.paperIndex j) tk) := by
    rw [← hk]
    exact P.1.consistent k
  exact
    ⟨cutYou_le_nextIndex_of_lt hpaper tk,
      cutYou_ne_nextIndex_of_consistent hcutYou hconsistent⟩

/--
Remark 4.1.3, bundled `Path` form: Cut really changes the upper index.
-/
theorem path_cut_get_changed_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (path_cut P hij hjk hk hj hi hconsistent).1.get k ≠ P.1.get k := by
  rw [path_cut_get_changed P hij hjk hk hj hi hconsistent, hk]
  have hcutYou :
      ConsistentTime (⋉ (P.1.paperIndex j) tk) := by
    rw [← hk]
    exact P.1.consistent k
  exact (cutYou_ne_nextIndex_of_consistent hcutYou hconsistent).symm

/-- Remark 4.1.3, Cut bundled `Path` form: every non-upper index is unchanged. -/
theorem path_cut_get_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk))
    {idx : P.1.Index} (hidx : idx ≠ k) :
    (path_cut P hij hjk hk hj hi hconsistent).1.get idx = P.1.get idx := by
  simp [path_cut, Prepath.replace_get_ne P.1 hidx]

/-- Remark 4.1.3, Cut bundled `Path` form: the lower index is unchanged. -/
theorem path_cut_get_lower_unchanged {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (path_cut P hij hjk hk hj hi hconsistent).1.get i = P.1.get i := by
  exact path_cut_get_ne P hij hjk hk hj hi hconsistent (by
    intro hik
    have hval : i.val = k.val := congrArg Fin.val hik
    omega)

/-- Remark 4.1.3, Cut bundled `Path` form: the center index is unchanged. -/
theorem path_cut_get_center_unchanged {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (path_cut P hij hjk hk hj hi hconsistent).1.get j = P.1.get j := by
  exact path_cut_get_ne P hij hjk hk hj hi hconsistent (by
    intro hjk_eq
    have hval : j.val = k.val := congrArg Fin.val hjk_eq
    omega)

/--
Definition 4.1.1, bundled `Path` form: after `Cut`, the center index still has
the displayed `cutMe` attestation shape.
-/
theorem path_cut_get_center_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (path_cut P hij hjk hk hj hi hconsistent).1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)) := by
  rw [path_cut_get_center_unchanged P hij hjk hk hj hi hconsistent, hj]

/--
Definition 4.1.1, bundled `Path` form: after `Cut`, the lower index still has
the displayed attestation-to-`cutMe` shape.
-/
theorem path_cut_get_lower_shape {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (path_cut P hij hjk hk hj hi hconsistent).1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))) := by
  rw [path_cut_get_lower_unchanged P hij hjk hk hj hi hconsistent, hi]

/--
Remark 4.1.4(1), bundled `Path` form: `Cut` changes precisely the upper index.
-/
theorem path_cut_changes_precisely_one {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (P : Path Time)
    {i j k : P.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : P.1.get k = ⋉ (P.1.paperIndex j) tk)
    (hj : P.1.get j =
      ⋊ (P.1.paperIndex i) (tj # (⋉ (P.1.paperIndex j) tk)))
    (hi : P.1.get i =
      ti # (⋊ (P.1.paperIndex i)
        (tj # (⋉ (P.1.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (P.1.paperIndex i) tk)) :
    (path_cut P hij hjk hk hj hi hconsistent).1.get k =
        ↱ (P.1.paperIndex i) tk ∧
      (path_cut P hij hjk hk hj hi hconsistent).1.get k ≠ P.1.get k ∧
      ∀ idx : P.1.Index, idx ≠ k →
        (path_cut P hij hjk hk hj hi hconsistent).1.get idx = P.1.get idx := by
  exact
    ⟨path_cut_get_changed P hij hjk hk hj hi hconsistent,
      path_cut_get_changed_ne P hij hjk hk hj hi hconsistent,
      fun idx hidx => path_cut_get_ne P hij hjk hk hj hi hconsistent hidx⟩

/-- Definition 4.1.5(1): the condition `T[k] = Q_i⊖` — the time carries one of the
cutting labels `Q ∈ {↱, ⋊, ⋉}` with the given target index. -/
def HasCutLabelAt (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (target : Nat) (t : Time) : Prop :=
  ∃ kind base, t = cutting kind target base

/-- Definition 4.1.5: a time equal to a cutting-label time has that label target. -/
theorem hasCutLabelAt_of_eq_cutting {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {target : Nat}
    {t : Time} {kind} {base : Time}
    (h : t = cutting kind target base) :
    HasCutLabelAt Time target t :=
  ⟨kind, base, h⟩

/--
Definition 4.1.5 bridge: any time with the form of a member of the cutting
flag-set has some paper label target.
-/
theorem exists_hasCutLabelAt_of_hasForm_member {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {Q : Flag Time} (hmem : cuttingFlagSet.member Q)
    {t : Time} (hform : HasForm Q t) :
    ∃ target : Nat, HasCutLabelAt Time target t := by
  rcases cutting_mem_complete hmem with ⟨kind, target, hQ⟩
  rcases hform with ⟨_hconsistent, ⟨base, hbase⟩⟩
  refine ⟨target, kind, base, ?_⟩
  rw [hbase, hQ]

/--
Definition 4.1.5 bridge: a defined cutting-flag lookup gives some paper label
target for the inactive-index definition.
-/
theorem exists_hasCutLabelAt_of_flagOf_eq_some {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {t : Time} {Q : {Q : Flag Time // cuttingFlagSet.member Q}}
    (hflag : flagOf cuttingFlagSet t = some Q) :
    ∃ target : Nat, HasCutLabelAt Time target t :=
  exists_hasCutLabelAt_of_hasForm_member Q.2
    (flagOf_eq_some_hasForm cuttingFlagSet hflag)

/--
Definition 4.1.5 bridge: a consistent time with a paper Cut label target has a
defined cutting-flag lookup.
-/
theorem exists_flagOf_eq_some_of_hasCutLabelAt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {target : Nat} {t : Time}
    (hconsistent : ConsistentTime t)
    (hlabel : HasCutLabelAt Time target t) :
    ∃ Q : {Q : Flag Time // cuttingFlagSet.member Q},
      flagOf cuttingFlagSet t = some Q := by
  rcases hlabel with ⟨kind, base, hshape⟩
  let Q : {Q : Flag Time // cuttingFlagSet.member Q} :=
    ⟨cutting kind target, cutting_mem kind target⟩
  refine ⟨Q, ?_⟩
  exact flagOf_eq_some_of_hasForm cuttingFlagSet Q.2
    ⟨hconsistent, ⟨base, hshape⟩⟩

/--
Definition 4.1.5 bridge: for consistent times, having some cutting-flag lookup
is equivalent to having some paper Cut label target.
-/
theorem flagOf_ne_none_iff_exists_hasCutLabelAt_of_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {t : Time} (hconsistent : ConsistentTime t) :
    flagOf cuttingFlagSet t ≠ none ↔
      ∃ target : Nat, HasCutLabelAt Time target t := by
  constructor
  · intro hne
    rcases Option.ne_none_iff_exists'.mp hne with ⟨Q, hsome⟩
    exact exists_hasCutLabelAt_of_flagOf_eq_some hsome
  · rintro ⟨target, hlabel⟩ hnone
    rcases exists_flagOf_eq_some_of_hasCutLabelAt hconsistent hlabel with
      ⟨Q, hsome⟩
    rw [hnone] at hsome
    cases hsome

/-- Definition 4.1.5: `nextIndex` is one of the cutting labels at its target. -/
theorem hasCutLabelAt_nextIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (target : Nat)
    (base : Time) :
    HasCutLabelAt Time target (↱ target base) :=
  ⟨CutFlagKind.nextIndex, base, rfl⟩

/-- Definition 4.1.5: `cutMe` is one of the cutting labels at its target. -/
theorem hasCutLabelAt_cutMe {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (target : Nat)
    (base : Time) :
    HasCutLabelAt Time target (⋊ target base) :=
  ⟨CutFlagKind.cutMe, base, rfl⟩

/-- Definition 4.1.5: `cutYou` is one of the cutting labels at its target. -/
theorem hasCutLabelAt_cutYou {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (target : Nat)
    (base : Time) :
    HasCutLabelAt Time target (⋉ target base) :=
  ⟨CutFlagKind.cutYou, base, rfl⟩

namespace Prepath

/-- Definition 4.1.5(1): index `j` is `k,i`-inactive in a prepath `T` when
`i < j < k` and `T[k] = Q_i⊖`. -/
def InactiveBetween {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    (k j i : T.Index) : Prop :=
  i.val < j.val ∧ j.val < k.val ∧ HasCutLabelAt Time (T.paperIndex i) (T.get k)

/-- Definition 4.1.5(3): index `j` is inactive in a prepath when it is `k,i`-inactive
for some `k, i`. -/
def Inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) (j : T.Index) : Prop :=
  ∃ k i : T.Index, T.InactiveBetween k j i

/-- Definition 4.1.5(4): index `j` is active in a prepath when it is not inactive. -/
def Active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time) (j : T.Index) : Prop :=
  ¬ T.Inactive j

/-- Definition 4.1.5: a `$k,i$`-inactive witness makes the center inactive. -/
theorem inactive_of_inactiveBetween {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {k j i : T.Index} (h : T.InactiveBetween k j i) :
    T.Inactive j :=
  ⟨k, i, h⟩

/-- Definition 4.1.5: inactive indexes are exactly indexes with `$k,i$` witnesses. -/
theorem inactive_iff_exists_inactiveBetween {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {j : T.Index} :
    T.Inactive j ↔ ∃ k i : T.Index, T.InactiveBetween k j i :=
  Iff.rfl

theorem inactiveBetween_lower_lt_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {k j i : T.Index} (h : T.InactiveBetween k j i) :
    i.val < j.val := by
  exact h.1

theorem inactiveBetween_center_lt_upper {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {k j i : T.Index} (h : T.InactiveBetween k j i) :
    j.val < k.val := by
  exact h.2.1

/-- Definition 4.1.5: an inactive witness has lower paper index below the center. -/
theorem inactiveBetween_lower_paperIndex_lt_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (T : Prepath Time) {k j i : T.Index} (h : T.InactiveBetween k j i) :
    T.paperIndex i < T.paperIndex j := by
  exact (T.paperIndex_lt_iff).mpr h.1

/-- Definition 4.1.5: an inactive witness has center paper index below the upper index. -/
theorem inactiveBetween_center_paperIndex_lt_upper {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (T : Prepath Time) {k j i : T.Index} (h : T.InactiveBetween k j i) :
    T.paperIndex j < T.paperIndex k := by
  exact (T.paperIndex_lt_iff).mpr h.2.1

theorem inactiveBetween_hasCutLabel {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {k j i : T.Index} (h : T.InactiveBetween k j i) :
    HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  exact h.2.2

/--
Notation 4.1.2 and Definition 4.1.5: replacing a different index preserves a
particular inactive witness.
-/
theorem replace_inactiveBetween_iff_of_upper_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {upper center lower changed : T.Index} (hupper_ne_changed : upper ≠ changed)
    (t : Time) (hctrl hconsistent) :
    (T.replace changed t hctrl hconsistent).InactiveBetween upper center lower ↔
      T.InactiveBetween upper center lower := by
  constructor
  · intro hinactive
    exact ⟨hinactive.1, hinactive.2.1, by
      simpa [Prepath.replace_paperIndex,
        Prepath.replace_get_ne T hupper_ne_changed t hctrl hconsistent] using hinactive.2.2⟩
  · intro hinactive
    exact ⟨hinactive.1, hinactive.2.1, by
      simpa [Prepath.replace_paperIndex,
        Prepath.replace_get_ne T hupper_ne_changed t hctrl hconsistent] using hinactive.2.2⟩

/--
Notation 4.1.2 and Definition 4.1.5: replacing an inactive center preserves the same
inactive witness, because the witness is read at the upper index.
-/
theorem replace_inactiveBetween_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {upper center lower : T.Index} (hinactive : T.InactiveBetween upper center lower)
    (t : Time)
    (hctrl : controller t = controller (T.get center))
    (hconsistent : ConsistentTime t) :
    (T.replace center t hctrl hconsistent).InactiveBetween upper center lower := by
  have hupper_ne_center : upper ≠ center := by
    intro h
    have hcenter_upper : center.val < upper.val := hinactive.2.1
    rw [h] at hcenter_upper
    exact (Nat.lt_irrefl center.val) hcenter_upper
  exact
    (T.replace_inactiveBetween_iff_of_upper_ne hupper_ne_center t hctrl hconsistent).mpr
      hinactive

/--
Notation 4.1.2 and Definition 4.1.5: replacing an inactive center by a consistent
same-controller time preserves inactivity of that center.
-/
theorem replace_inactive_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {center : T.Index} (hinactive : T.Inactive center) (t : Time)
    (hctrl : controller t = controller (T.get center))
    (hconsistent : ConsistentTime t) :
    (T.replace center t hctrl hconsistent).Inactive center := by
  rcases hinactive with ⟨upper, lower, hinactiveBetween⟩
  exact
    ⟨upper, lower,
      T.replace_inactiveBetween_center hinactiveBetween t hctrl hconsistent⟩

theorem inactive_has_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {j : T.Index} (h : T.Inactive j) :
    ∃ k i : T.Index, i.val < j.val ∧ j.val < k.val ∧
      HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  rcases h with ⟨k, i, hinactive⟩
  exact ⟨k, i, hinactive.1, hinactive.2.1, hinactive.2.2⟩

/-- Definition 4.1.5: inactive indexes have paper-shaped `$k>j>i` witnesses. -/
theorem inactive_has_paperIndex_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {j : T.Index} (h : T.Inactive j) :
    ∃ k i : T.Index, T.paperIndex i < T.paperIndex j ∧
      T.paperIndex j < T.paperIndex k ∧
      HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  rcases h with ⟨k, i, hinactive⟩
  exact ⟨k, i, T.inactiveBetween_lower_paperIndex_lt_center hinactive,
    T.inactiveBetween_center_paperIndex_lt_upper hinactive,
    T.inactiveBetween_hasCutLabel hinactive⟩

/-- Definition 4.1.5: active means there are no inactive witnesses. -/
theorem active_iff_no_inactive_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {j : T.Index} :
    T.Active j ↔
      ¬ ∃ k i : T.Index, i.val < j.val ∧ j.val < k.val ∧
        HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  constructor
  · intro hactive hwitness
    rcases hwitness with ⟨k, i, hik, hjk, hlabel⟩
    exact hactive ⟨k, i, hik, hjk, hlabel⟩
  · intro hno hinactive
    rcases T.inactive_has_witness hinactive with ⟨k, i, hik, hjk, hlabel⟩
    exact hno ⟨k, i, hik, hjk, hlabel⟩

/-- Definition 4.1.5: active means there are no paper-shaped inactive witnesses. -/
theorem active_iff_no_paperIndex_inactive_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (T : Prepath Time) {j : T.Index} :
    T.Active j ↔
      ¬ ∃ k i : T.Index, T.paperIndex i < T.paperIndex j ∧
        T.paperIndex j < T.paperIndex k ∧
        HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  constructor
  · intro hactive hwitness
    rcases hwitness with ⟨k, i, hik, hjk, hlabel⟩
    exact hactive ⟨k, i, (T.paperIndex_lt_iff).mp hik,
      (T.paperIndex_lt_iff).mp hjk, hlabel⟩
  · intro hno hinactive
    exact hno (T.inactive_has_paperIndex_witness hinactive)

/-- Definition 4.1.5: active is the negation of inactive. -/
theorem active_iff_not_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {j : T.Index} :
    T.Active j ↔ ¬ T.Inactive j :=
  Iff.rfl

theorem active_not_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {j : T.Index} (h : T.Active j) :
    ¬ T.Inactive j := by
  exact h

/-- Definition 4.1.5: an inactive index is not active. -/
theorem inactive_not_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {j : T.Index} (h : T.Inactive j) :
    ¬ T.Active j := by
  intro hactive
  exact hactive h

/-- Definition 4.1.5: the first index cannot be inactive. -/
theorem active_of_first_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {j : T.Index} (hfirst : j.val = 0) :
    T.Active j := by
  intro hinactive
  rcases T.inactive_has_witness hinactive with
    ⟨_k, i, hi_lt_j, _hj_lt_k, _hlabel⟩
  have hi_lt_zero : i.val < 0 := by
    simp [hfirst] at hi_lt_j
  exact Nat.not_lt_zero i.val hi_lt_zero

/-- Definition 4.1.5: the final index cannot be inactive. -/
theorem active_of_last_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (T : Prepath Time)
    {j : T.Index} (hlast : T.paperIndex j = T.length) :
    T.Active j := by
  intro hinactive
  rcases T.inactive_has_witness hinactive with
    ⟨k, _i, _hi_lt_j, hj_lt_k, _hlabel⟩
  have hlength_le_k : T.length <= k.val := by
    have hsucc_le_k : j.val + 1 <= k.val := Nat.succ_le_of_lt hj_lt_k
    have hpaper_le_k : T.paperIndex j <= k.val := by
      simpa [Prepath.paperIndex] using hsucc_le_k
    calc
      T.length = T.paperIndex j := hlast.symm
      _ <= k.val := hpaper_le_k
  exact (Nat.not_lt_of_ge hlength_le_k) k.isLt

/--
Remark 4.1.3 structural consequence: Init labels alone do
not make any index inactive. Every non-first Init entry has cutting target
equal to its Lean index, while an inactive witness through a lower index would
need the upper label target to be the lower paper index.
-/
theorem initPrepath_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (j : (initPrepath Time hpos base hconsistent).Index) :
    (initPrepath Time hpos base hconsistent).Active j := by
  intro hinactive
  rcases (initPrepath Time hpos base hconsistent).inactive_has_witness hinactive with
    ⟨k, i, hi_lt_j, hj_lt_k, hlabel⟩
  have hk_ne_zero : k.val ≠ 0 := by omega
  have hk_get :
      (initPrepath Time hpos base hconsistent).get k =
        ↱ k.val (base k) :=
    initPrepath_get_nonzero hpos base hconsistent k hk_ne_zero
  rcases hlabel with ⟨kind, labelBase, hlabelShape⟩
  have hnextCons :
      ConsistentTime (↱ k.val (base k)) := by
    rw [← hk_get]
    exact hconsistent k
  have heq :
      ↱ k.val (base k) =
        cutting kind ((initPrepath Time hpos base hconsistent).paperIndex i)
          labelBase :=
    hk_get.symm.trans hlabelShape
  have hlabelCons :
      ConsistentTime
        (cutting kind ((initPrepath Time hpos base hconsistent).paperIndex i)
          labelBase) := by
    rw [← heq]
    exact hnextCons
  have htarget :
      k.val = (initPrepath Time hpos base hconsistent).paperIndex i :=
    (flags_are_equal hnextCons hlabelCons heq).2
  have hk_eq_i_succ : k.val = i.val + 1 := by
    simpa [Prepath.paperIndex] using htarget
  omega

end Prepath

namespace Derivation

/-- Definition 4.1.5(2): index `j` is `k,i`-inactive in a derivation `Π` when it is
`k,i`-inactive in `root(Π)`. -/
def InactiveBetween {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (_deriv : Derivation Time T) (k j i : T.Index) : Prop :=
  T.InactiveBetween k j i

/-- Definition 4.1.5(2),(3): index `j` is inactive in a derivation `Π` when it is
inactive in `root(Π)`. -/
def Inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} (_deriv : Derivation Time T)
    (j : T.Index) : Prop :=
  T.Inactive j

/-- Definition 4.1.5(4): index `j` is active in a derivation when it is not inactive. -/
def Active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} (deriv : Derivation Time T)
    (j : T.Index) : Prop :=
  ¬ deriv.Inactive j

/-- Definition 4.1.5: derivation inactivity is root-prepath inactivity. -/
theorem inactive_iff_root_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} :
    deriv.Inactive j ↔ T.Inactive j :=
  Iff.rfl

/-- Definition 4.1.5: derivation activity is root-prepath activity. -/
theorem active_iff_root_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} :
    deriv.Active j ↔ T.Active j :=
  Iff.rfl

/-- Definition 4.1.5: derivation `$k,i$`-inactivity is root-prepath `$k,i$`-inactivity. -/
theorem inactiveBetween_iff_root_inactiveBetween {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {k j i : T.Index} :
    deriv.InactiveBetween k j i ↔ T.InactiveBetween k j i :=
  Iff.rfl

/-- Definition 4.1.5: a root inactive witness makes the derivation index inactive. -/
theorem inactive_of_inactiveBetween {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {k j i : T.Index}
    (h : deriv.InactiveBetween k j i) :
    deriv.Inactive j :=
  T.inactive_of_inactiveBetween h

/-- Definition 4.1.5: derivation inactive indexes are exactly indexes with `$k,i$` witnesses. -/
theorem inactive_iff_exists_inactiveBetween {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} :
    deriv.Inactive j ↔ ∃ k i : T.Index, deriv.InactiveBetween k j i :=
  Iff.rfl

/--
Notation 4.1.2 and Definition 4.1.5: an `Inc` step at an already-inactive center keeps
that center inactive, since the inactive witness is determined by an upper
index whose value is unchanged.
-/
theorem inc_inactive_of_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} (hinactive : deriv.Inactive j)
    {t' : Time} (hlt : (T.get j) ≺ t')
    (hflag : flagOf cuttingFlagSet (T.get j) =
      flagOf cuttingFlagSet t')
    (hconsistent : ConsistentTime t') :
    (Derivation.inc deriv j hlt hflag hconsistent).Inactive j := by
  exact T.replace_inactive_center hinactive t' hlt.1.1.symm hconsistent

theorem inactiveBetween_lower_lt_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {k j i : T.Index}
    (h : deriv.InactiveBetween k j i) :
    i.val < j.val := by
  exact T.inactiveBetween_lower_lt_center h

theorem inactiveBetween_center_lt_upper {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {k j i : T.Index}
    (h : deriv.InactiveBetween k j i) :
    j.val < k.val := by
  exact T.inactiveBetween_center_lt_upper h

/-- Definition 4.1.5: a derivation inactive witness has lower paper index below the center. -/
theorem inactiveBetween_lower_paperIndex_lt_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {k j i : T.Index}
    (h : deriv.InactiveBetween k j i) :
    T.paperIndex i < T.paperIndex j := by
  exact T.inactiveBetween_lower_paperIndex_lt_center h

/-- Definition 4.1.5: a derivation inactive witness has center paper index below the upper index. -/
theorem inactiveBetween_center_paperIndex_lt_upper {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {k j i : T.Index}
    (h : deriv.InactiveBetween k j i) :
    T.paperIndex j < T.paperIndex k := by
  exact T.inactiveBetween_center_paperIndex_lt_upper h

theorem inactiveBetween_hasCutLabel {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {k j i : T.Index}
    (h : deriv.InactiveBetween k j i) :
    HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  exact T.inactiveBetween_hasCutLabel h

theorem inactive_has_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} (h : deriv.Inactive j) :
    ∃ k i : T.Index, i.val < j.val ∧ j.val < k.val ∧
      HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  exact Prepath.inactive_has_witness T h

/-- Definition 4.1.5: derivation inactive indexes have paper-shaped witnesses. -/
theorem inactive_has_paperIndex_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} (h : deriv.Inactive j) :
    ∃ k i : T.Index, T.paperIndex i < T.paperIndex j ∧
      T.paperIndex j < T.paperIndex k ∧
      HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  exact Prepath.inactive_has_paperIndex_witness T h

/-- Definition 4.1.5: derivation activity is the negation of derivation inactivity. -/
theorem active_iff_not_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} :
    deriv.Active j ↔ ¬ deriv.Inactive j :=
  Iff.rfl

/-- Definition 4.1.5: derivation activity means there are no root inactive witnesses. -/
theorem active_iff_no_inactive_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} :
    deriv.Active j ↔
      ¬ ∃ k i : T.Index, i.val < j.val ∧ j.val < k.val ∧
        HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  exact Prepath.active_iff_no_inactive_witness T

/-- Definition 4.1.5: derivation activity excludes paper-shaped inactive witnesses. -/
theorem active_iff_no_paperIndex_inactive_witness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {j : T.Index} :
    deriv.Active j ↔
      ¬ ∃ k i : T.Index, T.paperIndex i < T.paperIndex j ∧
        T.paperIndex j < T.paperIndex k ∧
        HasCutLabelAt Time (T.paperIndex i) (T.get k) := by
  exact Prepath.active_iff_no_paperIndex_inactive_witness T

theorem active_not_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} (h : deriv.Active j) :
    ¬ deriv.Inactive j := by
  exact h

/-- Definition 4.1.5: an inactive derivation index is not active. -/
theorem inactive_not_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} (h : deriv.Inactive j) :
    ¬ deriv.Active j := by
  intro hactive
  exact hactive h

/-- Definition 4.1.5: the first derivation index cannot be inactive. -/
theorem active_of_first_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} (hfirst : j.val = 0) :
    deriv.Active j := by
  exact T.active_of_first_index hfirst

/-- Definition 4.1.5: the final derivation index cannot be inactive. -/
theorem active_of_last_index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {j : T.Index} (hlast : T.paperIndex j = T.length) :
    deriv.Active j := by
  exact T.active_of_last_index hlast

/-- Remark 4.1.3 structural consequence: every Init index is active. -/
theorem init_active {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {n : Nat}
    (hpos : 0 < n) (base : Fin n → Time)
    (hconsistent : ∀ i, ConsistentTime (initTime Time base i))
    (j : (Derivation.init (Time := Time) hpos base hconsistent).root.Index) :
    (Derivation.init (Time := Time) hpos base hconsistent).Active j := by
  exact Prepath.initPrepath_active hpos base hconsistent j

end Derivation

end ContForm.Foundation.Paths.Basic
