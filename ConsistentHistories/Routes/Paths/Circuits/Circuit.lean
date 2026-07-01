import ConsistentHistories.Foundation.Paths.InitialPrefixes

namespace ConsistentHistories.Routes.Paths.Circuits

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.Cut.Flags
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Foundation.Paths.InitialPrefixes

universe u v

/-- Definition 4.3.1(1): a circuit `(T, T')` is a pair of paths of equal length `n`
with `ctrl(T[i]) = ctrl(T'[i])` for every `1 ≤ i < n`; the controllers at the
final index `n` need not be equal. -/
structure Circuit (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] where
  left : Path Time
  right : Path Time
  length_eq : left.1.length = right.1.length
  controller_eq_before_last :
    ∀ i : left.1.Index, left.1.paperIndex i < left.1.length →
      controller (left.1.get i) =
        controller (right.1.get (Fin.cast length_eq i))

namespace Circuit

/-- Definition 4.3.1(1): the left member of a circuit is a path. -/
theorem left_isPath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) :
    IsPath Time c.left.1 := by
  exact c.left.2

/-- Definition 4.3.1(1): the right member of a circuit is a path. -/
theorem right_isPath {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) :
    IsPath Time c.right.1 := by
  exact c.right.2

/-- Definition 4.3.1(2), `length(T, T')`: the common length of the two paths of a
circuit. -/
def length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) : Nat :=
  c.left.1.length

/-- Definition 4.3.1(2): the left path has the circuit length. -/
theorem left_length_eq_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) :
    c.left.1.length = c.length :=
  rfl

/-- Definition 4.3.1(2): the right path has the circuit length. -/
theorem right_length_eq_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) :
    c.right.1.length = c.length :=
  c.length_eq.symm

/-- Definition 4.3.1(2): the circuit length is positive, since each side is a
nonempty path. -/
theorem length_pos {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) :
    0 < c.length :=
  c.left.1.length_pos

/-- Definition 4.3.1(4)(a), `index(T, T')`: the common index set of a circuit,
represented on the left path. -/
abbrev Index {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) : Type :=
  c.left.1.Index

/-- Definition 4.3.1(4)(a): the matching right-path index for a common circuit index. -/
def rightIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) (i : c.Index) :
    c.right.1.Index :=
  Fin.cast c.length_eq i

/-- Definition 4.3.1(4)(a): common circuit indexes have the same numeric value on the right path. -/
theorem rightIndex_val {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) (i : c.Index) :
    (c.rightIndex i).val = i.val := by
  rfl

/-- Definition 4.3.1(4)(a): common circuit indexes have the same strict order on the right path. -/
theorem rightIndex_lt_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) {i j : c.Index} :
    (c.rightIndex i).val < (c.rightIndex j).val ↔ i.val < j.val := by
  simp [rightIndex]

/-- Definition 4.3.1(4)(a): common circuit indexes have the same weak order on the right path. -/
theorem rightIndex_le_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) {i j : c.Index} :
    (c.rightIndex i).val ≤ (c.rightIndex j).val ↔ i.val ≤ j.val := by
  simp [rightIndex]

/-- Definition 4.3.1(4)(a): every right-path index is represented by a common circuit index. -/
theorem rightIndex_castLeft {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time)
    (i : c.right.1.Index) :
    c.rightIndex (Fin.cast c.length_eq.symm i) = i := by
  ext
  rfl

/-- Definition 4.3.1(4)(a): casting a common circuit index to the right and back is identity. -/
theorem rightIndex_castRight {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) (i : c.Index) :
    Fin.cast c.length_eq.symm (c.rightIndex i) = i := by
  ext
  rfl

/-- Definition 4.3.1(4)(a): the common-to-right index transport is injective. -/
theorem rightIndex_injective {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) :
    Function.Injective c.rightIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : c.right.1.Index => x.val) h

/-- Definition 4.3.1(4)(a): the common-to-right index transport is surjective. -/
theorem rightIndex_surjective {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) :
    Function.Surjective c.rightIndex := by
  intro i
  exact ⟨Fin.cast c.length_eq.symm i, c.rightIndex_castLeft i⟩

/-- Definition 4.3.1(4)(a): equality of right indexes is equality of common circuit indexes. -/
theorem rightIndex_eq_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) {i j : c.Index} :
    c.rightIndex i = c.rightIndex j ↔ i = j := by
  constructor
  · intro h
    exact Circuit.rightIndex_injective c h
  · intro h
    cases h
    rfl

/-- Definition 4.3.1(4)(a): right-path and left-path paper indexes agree for common indexes. -/
theorem rightIndex_paperIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) (i : c.Index) :
    c.right.1.paperIndex (c.rightIndex i) = c.left.1.paperIndex i := by
  simp [Prepath.paperIndex, rightIndex]

/-- Definition 4.3.1(4)(a): strict paper-index order is preserved on the right path. -/
theorem rightIndex_paperIndex_lt_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time)
    {i j : c.Index} :
    c.right.1.paperIndex (c.rightIndex i) <
        c.right.1.paperIndex (c.rightIndex j) ↔
      c.left.1.paperIndex i < c.left.1.paperIndex j := by
  simp [Prepath.paperIndex, rightIndex]

/-- Definition 4.3.1(4)(a): weak paper-index order is preserved on the right path. -/
theorem rightIndex_paperIndex_le_iff {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time)
    {i j : c.Index} :
    c.right.1.paperIndex (c.rightIndex i) ≤
        c.right.1.paperIndex (c.rightIndex j) ↔
      c.left.1.paperIndex i ≤ c.left.1.paperIndex j := by
  simp [Prepath.paperIndex, rightIndex]

/-- Definition 4.3.1: non-final matching circuit indexes have the same controller. -/
theorem controller_eq_before_last_of_lt_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (c : Circuit Time) (i : c.left.1.Index) (hi : c.left.1.paperIndex i < c.length) :
    controller (c.left.1.get i) =
      controller (c.right.1.get (Fin.cast c.length_eq i)) :=
  c.controller_eq_before_last i hi

/--
Definition 4.3.1(1): since the two sides share controllers at every non-final
index, differing controllers at an index force that index to be the final
circuit index.
-/
theorem final_index_of_controller_ne {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (c : Circuit Time) {i : c.left.1.Index}
    (hctrl :
      controller (c.left.1.get i) ≠
        controller (c.right.1.get (Fin.cast c.length_eq i))) :
    c.left.1.paperIndex i = c.length := by
  have hle : c.left.1.paperIndex i <= c.length :=
    c.left.1.paperIndex_le_length i
  have hnotlt : ¬ c.left.1.paperIndex i < c.length := by
    intro hi
    exact hctrl (c.controller_eq_before_last i hi)
  omega

/--
Replacing one time on each side by controller-preserving times preserves the
circuit controller-equality condition before the last index.
-/
theorem replaceBoth_controller_eq_before_last
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time)
    (leftIdx : c.left.1.Index) (leftTime : Time)
    (hleftCtrl :
      controller leftTime = controller (c.left.1.get leftIdx))
    (hleftCons : ConsistentTime leftTime)
    (rightIdx : c.right.1.Index) (rightTime : Time)
    (hrightCtrl :
      controller rightTime = controller (c.right.1.get rightIdx))
    (hrightCons : ConsistentTime rightTime) :
    let leftPath := c.left.1.replace leftIdx leftTime hleftCtrl hleftCons
    let rightPath := c.right.1.replace rightIdx rightTime hrightCtrl hrightCons
    let hlen : leftPath.length = rightPath.length := c.length_eq
    ∀ i : leftPath.Index, leftPath.paperIndex i < leftPath.length →
      controller (leftPath.get i) =
        controller (rightPath.get (Fin.cast hlen i)) := by
  dsimp
  intro i hi
  have hleftController :
      controller
          ((c.left.1.replace leftIdx leftTime hleftCtrl hleftCons).get i) =
        controller (c.left.1.get i) := by
    by_cases hidx : i = leftIdx
    · subst i
      exact Prepath.replace_get_same_controller c.left.1 leftIdx leftTime
        hleftCtrl hleftCons
    · exact Prepath.replace_get_ne_controller c.left.1 hidx leftTime hleftCtrl
        hleftCons
  have hrightController :
      controller
          ((c.right.1.replace rightIdx rightTime hrightCtrl hrightCons).get
            (Fin.cast c.length_eq i)) =
        controller (c.right.1.get (Fin.cast c.length_eq i)) := by
    by_cases hidx : Fin.cast c.length_eq i = rightIdx
    · rw [hidx]
      exact Prepath.replace_get_same_controller c.right.1 rightIdx rightTime
        hrightCtrl hrightCons
    · exact Prepath.replace_get_ne_controller c.right.1 hidx rightTime hrightCtrl
        hrightCons
  have hi_base : c.left.1.paperIndex i < c.left.1.length := by
    simpa [Prepath.replace_paperIndex] using hi
  exact hleftController.trans
    ((c.controller_eq_before_last i hi_base).trans hrightController.symm)

/-- The same circuit with its two paths exchanged. -/
def swap {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) : Circuit Time where
  left := c.right
  right := c.left
  length_eq := c.length_eq.symm
  controller_eq_before_last := by
    intro i hi
    let j : c.left.1.Index := Fin.cast c.length_eq.symm i
    have hj : c.left.1.paperIndex j < c.left.1.length := by
      simpa [j, Prepath.paperIndex, c.length_eq] using hi
    have hcast : Fin.cast c.length_eq j = i := by
      ext
      rfl
    have hctrl := c.controller_eq_before_last j hj
    simpa [j, hcast] using hctrl.symm

/-- Swapping a circuit preserves its length. -/
theorem swap_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (c : Circuit Time) :
    c.swap.length = c.length :=
  c.length_eq.symm

end Circuit

/-- Definition 4.3.1(3): a circuit-derivation `(Π, Π')` of a circuit `(T, T')` is a
pair of derivations deriving `T` and `T'` respectively. -/
structure CircuitDerivation (Time : Type v) {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] where
  circuit : Circuit Time
  leftDerivation : Derivation Time circuit.left.1
  rightDerivation : Derivation Time circuit.right.1

/-- Definition 4.3.6(1), `(Cut_{k,j,i}) ∈ Π`: an instance of the Cut rule
`(Cut_{k,j,i})` appears in `Π`, so `Π` contains a cut centred on `j`. -/
inductive ContainsCut {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    {T : Prepath Time} → Derivation Time T → Nat → Nat → Nat → Prop where
  | here {T : Prepath Time} (deriv : Derivation Time T) {i j k : T.Index}
      (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
      (hk : T.get k = ⋉ (T.paperIndex j) tk)
      (hj : T.get j =
        ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
      (hi : T.get i =
        ti # (⋊ (T.paperIndex i)
          (tj # (⋉ (T.paperIndex j) tk))))
      (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
      ContainsCut (Derivation.cut deriv hij hjk hk hj hi hconsistent)
        (T.paperIndex k) (T.paperIndex j) (T.paperIndex i)
  | inc {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
      (h : ContainsCut deriv cutK cutJ cutI) (j : T.Index) {t' : Time}
      (hlt : (T.get j) ≺ t')
      (hflag : flagOf cuttingFlagSet (T.get j) = flagOf cuttingFlagSet t')
      (hconsistent : ConsistentTime t') :
      ContainsCut (Derivation.inc deriv j hlt hflag hconsistent) cutK cutJ cutI
  | cutMeIntro {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
      (h : ContainsCut deriv cutK cutJ cutI) (j : T.Index) (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋊ target t)) :
      ContainsCut (Derivation.cutMeIntro deriv j target hshape hconsistent) cutK cutJ cutI
  | cutYouIntro {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
      (h : ContainsCut deriv cutK cutJ cutI) (j : T.Index) (target : Nat) {t : Time}
      (hshape : T.get j = ↱ target t)
      (hconsistent : ConsistentTime (⋉ target t)) :
      ContainsCut (Derivation.cutYouIntro deriv j target hshape hconsistent) cutK cutJ cutI
  | cutStep {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
      (h : ContainsCut deriv cutK cutJ cutI) {i j k : T.Index}
      (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
      (hk : T.get k = ⋉ (T.paperIndex j) tk)
      (hj : T.get j =
        ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
      (hi : T.get i =
        ti # (⋊ (T.paperIndex i)
          (tj # (⋉ (T.paperIndex j) tk))))
      (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
      ContainsCut (Derivation.cut deriv hij hjk hk hj hi hconsistent) cutK cutJ cutI

theorem final_cut_contains_cut {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {i j k : T.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val) {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk)) :
    ContainsCut (Derivation.cut deriv hij hjk hk hj hi hconsistent)
      (T.paperIndex k) (T.paperIndex j) (T.paperIndex i) := by
  exact ContainsCut.here deriv hij hjk hk hj hi hconsistent

theorem containsCut_order {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (h : ContainsCut deriv cutK cutJ cutI) :
    cutI < cutJ ∧ cutJ < cutK := by
  induction h with
  | here _deriv hij hjk _hk _hj _hi _hconsistent =>
      exact ⟨Nat.succ_lt_succ hij, Nat.succ_lt_succ hjk⟩
  | inc h _j _hlt _hflag _hconsistent ih =>
      exact ih
  | cutMeIntro h _j _target _hshape _hconsistent ih =>
      exact ih
  | cutYouIntro h _j _target _hshape _hconsistent ih =>
      exact ih
  | cutStep h _hij _hjk _hk _hj _hi _hconsistent ih =>
      exact ih

theorem containsCut_indices {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (h : ContainsCut deriv cutK cutJ cutI) :
    ∃ k j i : T.Index,
      T.paperIndex k = cutK ∧ T.paperIndex j = cutJ ∧ T.paperIndex i = cutI ∧
      i.val < j.val ∧ j.val < k.val := by
  induction h with
  | here _deriv hij hjk _hk _hj _hi _hconsistent =>
      rename_i i j k ti tj tk
      exact ⟨k, j, i, rfl, rfl, rfl, hij, hjk⟩
  | inc _h _changed _hlt _hflag _hconsistent ih =>
      rcases ih with ⟨k, j, i, hk, hj, hi, hij, hjk⟩
      exact ⟨k, j, i, hk, hj, hi, hij, hjk⟩
  | cutMeIntro _h _changed _target _hshape _hconsistent ih =>
      rcases ih with ⟨k, j, i, hk, hj, hi, hij, hjk⟩
      exact ⟨k, j, i, hk, hj, hi, hij, hjk⟩
  | cutYouIntro _h _changed _target _hshape _hconsistent ih =>
      rcases ih with ⟨k, j, i, hk, hj, hi, hij, hjk⟩
      exact ⟨k, j, i, hk, hj, hi, hij, hjk⟩
  | cutStep _h _hij _hjk _hk _hj _hi _hconsistent ih =>
      rcases ih with ⟨k, j, i, hk, hj, hi, hij, hjk⟩
      exact ⟨k, j, i, hk, hj, hi, hij, hjk⟩

/--
Proof-support list of the Cut triples introduced by a derivation, in derivation
order. This is an internal representation used to reason about Cut occurrence
uniqueness; it is not a separate paper definition.
-/
def cutTriples {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    {T : Prepath Time} → Derivation Time T → List (Nat × Nat × Nat)
  | _, Derivation.init _ _ _ => []
  | _, Derivation.inc deriv _ _ _ _ => cutTriples deriv
  | _, Derivation.cutMeIntro deriv _ _ _ _ => cutTriples deriv
  | _, Derivation.cutYouIntro deriv _ _ _ _ => cutTriples deriv
  | _, Derivation.cut deriv _hij _hjk _hk _hj _hi _hconsistent =>
      by
        rename_i T i j k _ti _tj _tk
        exact (T.paperIndex k, T.paperIndex j, T.paperIndex i) :: cutTriples deriv

theorem mem_cutTriples_of_containsCut {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) :
    (cutK, cutJ, cutI) ∈ cutTriples deriv := by
  induction hcut with
  | here _deriv _hij _hjk _hk _hj _hi _hconsistent =>
      simp [cutTriples]
  | inc _h _changed _hlt _hflag _hconsistent ih =>
      simpa [cutTriples] using ih
  | cutMeIntro _h _changed _target _hshape _hconsistent ih =>
      simpa [cutTriples] using ih
  | cutYouIntro _h _changed _target _hshape _hconsistent ih =>
      simpa [cutTriples] using ih
  | cutStep _h _hij _hjk _hk _hj _hi _hconsistent ih =>
      simp [cutTriples, ih]

theorem containsCut_of_mem_cutTriples {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} (deriv : Derivation Time T) {cutK cutJ cutI : Nat},
      (cutK, cutJ, cutI) ∈ cutTriples deriv →
        ContainsCut deriv cutK cutJ cutI := by
  intro T deriv
  induction deriv with
  | init _hpos _base _hconsistent =>
      intro _cutK _cutJ _cutI hmem
      simp [cutTriples] at hmem
  | inc deriv changed hlt hflag hconsistent ih =>
      intro _cutK _cutJ _cutI hmem
      exact ContainsCut.inc (ih hmem) changed hlt hflag hconsistent
  | cutMeIntro deriv changed target hshape hconsistent ih =>
      intro _cutK _cutJ _cutI hmem
      exact ContainsCut.cutMeIntro (ih hmem) changed target hshape hconsistent
  | cutYouIntro deriv changed target hshape hconsistent ih =>
      intro _cutK _cutJ _cutI hmem
      exact ContainsCut.cutYouIntro (ih hmem) changed target hshape hconsistent
  | cut deriv hij hjk hk hj hi hconsistent ih =>
      intro cutK cutJ cutI hmem
      rename_i T i j k _ti _tj _tk
      simp [cutTriples] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl, rfl⟩
        exact ContainsCut.here deriv hij hjk hk hj hi hconsistent
      · exact ContainsCut.cutStep (ih htail) hij hjk hk hj hi hconsistent

theorem containsCut_iff_mem_cutTriples {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) {cutK cutJ cutI : Nat} :
    ContainsCut deriv cutK cutJ cutI ↔ (cutK, cutJ, cutI) ∈ cutTriples deriv := by
  constructor
  · exact mem_cutTriples_of_containsCut
  · exact containsCut_of_mem_cutTriples deriv

/-- A `ContainsCut` occurrence can be exposed as an initial prefix whose final
rule is exactly that Cut. -/
def CutPrefixWitness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (cutK cutJ cutI : Nat) : Prop :=
  ∃ (base : Prepath Time) (baseDeriv : Derivation Time base)
    (idxI idxJ idxK : base.Index) (ti tj tk : Time)
    (hij : idxI.val < idxJ.val) (hjk : idxJ.val < idxK.val)
    (hk : base.get idxK = ⋉ (base.paperIndex idxJ) tk)
    (hj : base.get idxJ =
      ⋊ (base.paperIndex idxI) (tj # (⋉ (base.paperIndex idxJ) tk)))
    (hi : base.get idxI =
      ti # (⋊ (base.paperIndex idxI)
        (tj # (⋉ (base.paperIndex idxJ) tk))))
    (hconsistent : ConsistentTime (↱ (base.paperIndex idxI) tk)),
      cutK = base.paperIndex idxK ∧
        cutJ = base.paperIndex idxJ ∧
        cutI = base.paperIndex idxI ∧
        InitialPrefix
          (Derivation.cut baseDeriv hij hjk hk hj hi hconsistent)
          deriv

/--
Decomposable form of `CutPrefixWitness`.

This is the first-class proof object used when later arguments need to compose
the post-Cut prefix with another derivation prefix, rather than only consume a
terminal existential fact.
-/
structure CutPrefixData {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (cutK cutJ cutI : Nat) where
  base : Prepath Time
  baseDeriv : Derivation Time base
  idxI : base.Index
  idxJ : base.Index
  idxK : base.Index
  ti : Time
  tj : Time
  tk : Time
  hij : idxI.val < idxJ.val
  hjk : idxJ.val < idxK.val
  hk : base.get idxK = ⋉ (base.paperIndex idxJ) tk
  hj : base.get idxJ =
    ⋊ (base.paperIndex idxI) (tj # (⋉ (base.paperIndex idxJ) tk))
  hi : base.get idxI =
    ti # (⋊ (base.paperIndex idxI)
      (tj # (⋉ (base.paperIndex idxJ) tk)))
  hconsistent :
    ConsistentTime (↱ (base.paperIndex idxI) tk)
  cutK_eq : cutK = base.paperIndex idxK
  cutJ_eq : cutJ = base.paperIndex idxJ
  cutI_eq : cutI = base.paperIndex idxI
  hprefix :
    InitialPrefix
      (Derivation.cut baseDeriv hij hjk hk hj hi hconsistent)
      deriv

end ConsistentHistories.Routes.Paths.Circuits
