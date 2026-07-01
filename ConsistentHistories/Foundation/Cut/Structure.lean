import ConsistentHistories.Foundation.Cut.Flags

/-!
Paper section 3.2: Located semilattices with Cut.

-/

namespace ConsistentHistories.Foundation.Cut.Structure

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Flags

universe u v

/-- The three flag labels in the cutting flag-set. -/
inductive CutFlagKind where
  | nextIndex
  | cutMe
  | cutYou
  deriving DecidableEq

/-- Definition 3.2.1: a located semilattice with Cut — a located semilattice equipped with
the cutting flag-set `⋃ᵢ {↱ i, ⋊ i, ⋉ i}` and its five properties. -/
class LocatedSemilatticeWithCut (Time : Type v) (Ctrl : outParam (Type u))
    extends LocatedSemilattice Time Ctrl where
  cuttingFlagSet : FlagSet Time
  cutting : CutFlagKind → Nat → Flag Time
  cutting_mem : ∀ kind i, cuttingFlagSet.member (cutting kind i)
  cutting_mem_complete :
    ∀ {Q : Flag Time}, cuttingFlagSet.member Q → ∃ kind i, Q = cutting kind i
  next_le_cutme : ∀ j (t : Time), le ((cutting CutFlagKind.nextIndex j) t)
    ((cutting CutFlagKind.cutMe j) t)
  next_le_cutyou : ∀ j (t : Time), le ((cutting CutFlagKind.nextIndex j) t)
    ((cutting CutFlagKind.cutYou j) t)
  cutyou_le_next : ∀ {i j : Nat}, i < j → ∀ t : Time,
    le ((cutting CutFlagKind.cutYou j) t) ((cutting CutFlagKind.nextIndex i) t)
  cutme_contradicts_cutyou :
    ∀ j {t t' : Time}, controller t = controller t' →
      Contradicts ((cutting CutFlagKind.cutMe j) t) ((cutting CutFlagKind.cutYou j) t')
  cutting_injective :
    ∀ {kind kind' : CutFlagKind} {i i' : Nat},
      cutting kind i = cutting kind' i' → kind = kind' ∧ i = i'

namespace LocatedSemilatticeWithCut

section CutMethods
variable {Time : Type v} {Ctrl : Type u} [inst : LocatedSemilatticeWithCut Time Ctrl]
include inst

def nextIndex (i : Nat) : Flag Time :=
  cutting CutFlagKind.nextIndex i

def cutMe (i : Nat) : Flag Time :=
  cutting CutFlagKind.cutMe i

def cutYou (i : Nat) : Flag Time :=
  cutting CutFlagKind.cutYou i

/-!
Notation for the three cut flags, indexed by the applied argument: `⋊ i` is `cutme-i`,
`⋉ i` is `cutyou-i`, and `↱ i` is `nextindex-i`. The paper subscripts the index (`⋊ᵢ`);
here the index is the flag's argument. Each resolves through the ambient
`LocatedSemilatticeWithCut` instance.
-/
notation:max "⋊" i:max => LocatedSemilatticeWithCut.cutMe i
notation:max "⋉" i:max => LocatedSemilatticeWithCut.cutYou i
notation:max "↱" i:max => LocatedSemilatticeWithCut.nextIndex i

/-- Definition 3.2.1: `nextindex-i` is in the cutting flag-set. -/
theorem nextIndex_mem (i : Nat) :
    cuttingFlagSet.member (nextIndex (Time := Time) i) :=
  cutting_mem CutFlagKind.nextIndex i

/-- Definition 3.2.1: `cutme-i` is in the cutting flag-set. -/
theorem cutMe_mem (i : Nat) :
    cuttingFlagSet.member (cutMe (Time := Time) i) :=
  cutting_mem CutFlagKind.cutMe i

/-- Definition 3.2.1: `cutyou-i` is in the cutting flag-set. -/
theorem cutYou_mem (i : Nat) :
    cuttingFlagSet.member (cutYou (Time := Time) i) :=
  cutting_mem CutFlagKind.cutYou i

/-- Definition 3.2.1: the cutting flag-set is exactly the displayed union. -/
theorem cuttingFlagSet_member_iff
    {Q : Flag Time} :
    cuttingFlagSet.member Q ↔ ∃ kind i, Q = cutting kind i := by
  constructor
  · exact cutting_mem_complete
  · intro h
    rcases h with ⟨kind, i, rfl⟩
    exact cutting_mem kind i

/--
Inherited from Definition 3.1.1: `nextindex-i` preserves
controllers.
-/
theorem nextIndex_controller
    (i : Nat) (t : Time) :
    controller (↱ i t) = controller t := by
  exact (↱ i).apply_controller t

/-- Inherited from Definition 3.1.1: `cutme-i` preserves controllers. -/
theorem cutMe_controller
    (i : Nat) (t : Time) :
    controller (⋊ i t) = controller t := by
  exact (⋊ i).apply_controller t

/-- Inherited from Definition 3.1.1: `cutyou-i` preserves controllers. -/
theorem cutYou_controller
    (i : Nat) (t : Time) :
    controller (⋉ i t) = controller t := by
  exact (⋉ i).apply_controller t

/-- Inherited from Definition 3.1.1: `nextindex-i` is expansive. -/
theorem nextIndex_expansive
    (i : Nat) (t : Time) :
    t ≼ (↱ i t) := by
  exact (↱ i).apply_le t

/-- Inherited from Definition 3.1.1: `cutme-i` is expansive. -/
theorem cutMe_expansive
    (i : Nat) (t : Time) :
    t ≼ (⋊ i t) := by
  exact (⋊ i).apply_le t

/-- Inherited from Definition 3.1.1: `cutyou-i` is expansive. -/
theorem cutYou_expansive
    (i : Nat) (t : Time) :
    t ≼ (⋉ i t) := by
  exact (⋉ i).apply_le t

/-- Definition 3.2.1(1): `↱ j t ≼ ⋊ j t`. -/
theorem nextIndex_le_cutMe
    (j : Nat) (t : Time) :
    (↱ j t) ≼ (⋊ j t) :=
  next_le_cutme j t

/-- Definition 3.2.1(2): `↱ j t ≼ ⋉ j t`. -/
theorem nextIndex_le_cutYou
    (j : Nat) (t : Time) :
    (↱ j t) ≼ (⋉ j t) :=
  next_le_cutyou j t

/-- Definition 3.2.1(3): if `i < j` then `⋉ j t ≼ ↱ i t`. -/
theorem cutYou_le_nextIndex_of_lt
    {i j : Nat} (hij : i < j) (t : Time) :
    (⋉ j t) ≼ (↱ i t) :=
  cutyou_le_next hij t

/-- Definition 3.2.1(4): `⋊ j t 🗲 ⋉ j t'` for same-controller `t`, `t'`. -/
theorem cutMe_contradicts_cutYou
    (j : Nat) {t t' : Time}
    (hctrl : controller t = controller t') :
    (⋊ j t) 🗲 (⋉ j t') :=
  cutme_contradicts_cutyou j hctrl

/-- Definition 3.2.1(4), symmetric form. -/
theorem cutYou_contradicts_cutMe
    (j : Nat) {t t' : Time}
    (hctrl : controller t = controller t') :
    (⋉ j t') 🗲 (⋊ j t) :=
  contradicts_symm (cutMe_contradicts_cutYou j hctrl)

/-- Definition 3.2.1(5): equal cutting flags have equal symbol and index. -/
theorem cutting_eq_iff
    {kind kind' : CutFlagKind} {i i' : Nat} :
    cutting (Time := Time) kind i = cutting kind' i' ↔ kind = kind' ∧ i = i' := by
  constructor
  · intro h
    exact cutting_injective h
  · intro h
    rcases h with ⟨hkind, hi⟩
    rw [hkind, hi]

/-- Definition 3.2.1(5): distinct symbol-index pairs give distinct flags. -/
theorem cutting_ne_of_pair_ne
    {kind kind' : CutFlagKind} {i i' : Nat}
    (hne : kind ≠ kind' ∨ i ≠ i') :
    cutting (Time := Time) kind i ≠ cutting kind' i' := by
  intro h
  rcases (cutting_eq_iff.mp h) with ⟨hkind, hi⟩
  cases hne with
  | inl hkind_ne => exact hkind_ne hkind
  | inr hi_ne => exact hi_ne hi

end CutMethods

/--
Support package for constructing the paper's `LocatedSemilatticeWithCut`
record from an explicit cutting-flag family.

This is not a replacement definition: every field below is one of the paper
Cut obligations, or the exact consistent-output injectivity condition needed
to build the paper `FlagSet`.
-/
structure PackageSpec (Time : Type v) {Ctrl : Type u} [LocatedSemilattice Time Ctrl] where
  cutting : CutFlagKind → Nat → Flag Time
  consistent_output_injective :
    ∀ {kind kind' : CutFlagKind} {i i' : Nat} {t t' : Time},
      ConsistentTime (cutting kind i t) →
        cutting kind i t = cutting kind' i' t' → kind = kind' ∧ i = i'
  next_le_cutme : ∀ j (t : Time), le ((cutting CutFlagKind.nextIndex j) t)
    ((cutting CutFlagKind.cutMe j) t)
  next_le_cutyou : ∀ j (t : Time), le ((cutting CutFlagKind.nextIndex j) t)
    ((cutting CutFlagKind.cutYou j) t)
  cutyou_le_next : ∀ {i j : Nat}, i < j → ∀ t : Time,
    le ((cutting CutFlagKind.cutYou j) t) ((cutting CutFlagKind.nextIndex i) t)
  cutme_contradicts_cutyou :
    ∀ j {t t' : Time}, controller t = controller t' →
      Contradicts ((cutting CutFlagKind.cutMe j) t) ((cutting CutFlagKind.cutYou j) t')
  cutting_injective :
    ∀ {kind kind' : CutFlagKind} {i i' : Nat},
      cutting kind i = cutting kind' i' → kind = kind' ∧ i = i'

namespace PackageSpec

/-- The paper `FlagSet` generated by an explicit cutting-flag family. -/
def cuttingFlagSet {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (S : PackageSpec Time) : FlagSet Time where
  member Q := ∃ kind i, Q = S.cutting kind i
  injective_where_consistent := by
    intro Q Q' t t' hmem hmem' hcons heq
    rcases hmem with ⟨kind, i, rfl⟩
    rcases hmem' with ⟨kind', i', rfl⟩
    rcases S.consistent_output_injective hcons heq with ⟨hkind, hi⟩
    subst hkind
    subst hi
    rfl

theorem cuttingFlagSet_member {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (S : PackageSpec Time) (kind : CutFlagKind) (i : Nat) :
    S.cuttingFlagSet.member (S.cutting kind i) :=
  ⟨kind, i, rfl⟩

theorem cuttingFlagSet_member_complete {Time : Type v} {Ctrl : Type u}
    [LocatedSemilattice Time Ctrl]
    (S : PackageSpec Time) {Q : Flag Time} :
    S.cuttingFlagSet.member Q → ∃ kind i, Q = S.cutting kind i := by
  intro hmem
  exact hmem

/-- Package the explicit obligations as the paper's `LocatedSemilatticeWithCut`. -/
def toLocatedSemilatticeWithCut {Time : Type v} {Ctrl : Type u}
    [LocatedSemilattice Time Ctrl] (S : PackageSpec Time) :
    LocatedSemilatticeWithCut Time Ctrl where
  toLocatedSemilattice := inferInstance
  cuttingFlagSet := S.cuttingFlagSet
  cutting := S.cutting
  cutting_mem := by
    intro kind i
    exact S.cuttingFlagSet_member kind i
  cutting_mem_complete := by
    intro Q hmem
    exact S.cuttingFlagSet_member_complete hmem
  next_le_cutme := S.next_le_cutme
  next_le_cutyou := S.next_le_cutyou
  cutyou_le_next := S.cutyou_le_next
  cutme_contradicts_cutyou := S.cutme_contradicts_cutyou
  cutting_injective := S.cutting_injective

end PackageSpec

section CutTheorems
variable {Time : Type v} {Ctrl : Type u} [inst : LocatedSemilatticeWithCut Time Ctrl]
include inst

/-- Lemma 3.2.4: `⋊ j t 🗲 ↱ i t'` when `i < j`. -/
theorem cutMe_contradicts_nextIndex_of_lt
    {t t' : Time} {i j : Nat}
    (hctrl : controller t = controller t') (hij : i < j) :
    (⋊ j t) 🗲 (↱ i t') := by
  exact contradicts_of_le_right
    (cutyou_le_next hij t')
    (cutme_contradicts_cutyou j hctrl)

/-- Definition 3.2.1(1,3): the derived flag-order edge `⋉ j t ≼ ⋊ i t` for `i < j`. -/
theorem cutYou_le_cutMe_of_lt
    {i j : Nat} (hij : i < j) (t : Time) :
    (⋉ j t) ≼ (⋊ i t) :=
  le_trans (cutyou_le_next hij t) (next_le_cutme i t)

/-- Definition 3.2.1(2,3): the derived flag-order edge `⋉ j t ≼ ⋉ i t` for `i < j`. -/
theorem cutYou_le_cutYou_of_lt
    {i j : Nat} (hij : i < j) (t : Time) :
    (⋉ j t) ≼ (⋉ i t) :=
  le_trans (cutyou_le_next hij t) (next_le_cutyou i t)

/-- Lemma 3.2.5: a consistent flag value determines its symbol and index. -/
theorem flags_are_equal
    
    {kind kind' : CutFlagKind} {i i' : Nat} {t t' : Time}
    (hleft : ConsistentTime ((cutting kind i) t))
    (_hright : ConsistentTime ((cutting kind' i') t'))
    (heq : (cutting kind i) t = (cutting kind' i') t') :
    kind = kind' ∧ i = i' := by
  have hflag :
      cutting kind i = cutting kind' i' :=
    cuttingFlagSet.injective_where_consistent
      (cutting_mem kind i) (cutting_mem kind' i') hleft heq
  exact cutting_injective hflag

/-- Lemma 3.2.5: a consistent flag value determines its symbol. -/
theorem flag_kind_eq_of_eq_consistent
    {kind kind' : CutFlagKind} {i i' : Nat} {t t' : Time}
    (hleft : ConsistentTime ((cutting kind i) t))
    (hright : ConsistentTime ((cutting kind' i') t'))
    (heq : (cutting kind i) t = (cutting kind' i') t') :
    kind = kind' := by
  exact (flags_are_equal hleft hright heq).1

/-- Lemma 3.2.5: a consistent flag value determines its index. -/
theorem flag_target_eq_of_eq_consistent
    {kind kind' : CutFlagKind} {i i' : Nat} {t t' : Time}
    (hleft : ConsistentTime ((cutting kind i) t))
    (hright : ConsistentTime ((cutting kind' i') t'))
    (heq : (cutting kind i) t = (cutting kind' i') t') :
    i = i' := by
  exact (flags_are_equal hleft hright heq).2

/-- Lemma 3.2.5: a consistent time has at most one cutting flag. `HasForm` carries the
consistency side-condition. -/
theorem cuttingFlagSet_hasForm_unique
    
    {Q Q' : Flag Time} (hQ : cuttingFlagSet.member Q)
    (hQ' : cuttingFlagSet.member Q') {t : Time}
    (hform : HasForm Q t) (hform' : HasForm Q' t) :
    Q = Q' :=
  flag_unique_of_hasForm cuttingFlagSet hQ hQ' hform hform'

/-- Lemma 3.2.5: consistent `cutme` and `nextindex` values differ. -/
theorem cutMe_ne_nextIndex_of_consistent
    {cutTarget nextTarget : Nat}
    {cutBase nextBase : Time}
    (hcut : ConsistentTime (⋊ cutTarget cutBase))
    (hnext : ConsistentTime (↱ nextTarget nextBase)) :
    ⋊ cutTarget cutBase ≠ ↱ nextTarget nextBase := by
  intro heq
  have hkind := (flags_are_equal hcut hnext heq).1
  cases hkind

/-- Lemma 3.2.5: consistent `cutme` and `cutyou` values differ. -/
theorem cutMe_ne_cutYou_of_consistent
    {cutTarget youTarget : Nat}
    {cutBase youBase : Time}
    (hcut : ConsistentTime (⋊ cutTarget cutBase))
    (hyou : ConsistentTime (⋉ youTarget youBase)) :
    ⋊ cutTarget cutBase ≠ ⋉ youTarget youBase := by
  intro heq
  have hkind := (flags_are_equal hcut hyou heq).1
  cases hkind

/-- Remark 3.2.3(5): same-index `cutme` and `cutyou` outputs are equal only at the
controller top. -/
theorem cutMe_eq_cutYou_eq_topTime
    {j : Nat} {t t' : Time}
    (hctrl : controller t = controller t')
    (heq : ⋊ j t = ⋉ j t') :
    ⋊ j t = topTime (controller (⋊ j t)) := by
  have hcontr : (⋊ j t) 🗲 (⋉ j t') :=
    cutMe_contradicts_cutYou j hctrl
  have hself : (⋊ j t) 🗲 (⋊ j t) := by
    simpa [heq] using hcontr
  have hnotCons : ¬ ConsistentTime (⋊ j t) :=
    (contradicts_self_iff_not_consistentTime (⋊ j t)).mp hself
  simpa [LocatedSemilattice.topTime] using Classical.not_not.mp hnotCons

/-- Remark 3.2.3(5): same-index `cutme` and `cutyou` outputs are equal only at the
controller top, stated on the `cutyou` side. -/
theorem cutMe_eq_cutYou_cutYou_eq_topTime
    {j : Nat} {t t' : Time}
    (hctrl : controller t = controller t')
    (heq : ⋊ j t = ⋉ j t') :
    ⋉ j t' = topTime (controller (⋉ j t')) := by
  calc
    ⋉ j t' = ⋊ j t := heq.symm
    _ = topTime (controller (⋊ j t)) :=
      cutMe_eq_cutYou_eq_topTime hctrl heq
    _ = topTime (controller (⋉ j t')) := by rw [heq]

/-- Remark 3.2.3(5): same-index `cutme` and `cutyou` outputs cannot be equal when the
`cutme` output is not top. -/
theorem cutMe_ne_cutYou_of_not_top
    {j : Nat} {t t' : Time}
    (hctrl : controller t = controller t')
    (hnotTop :
      ⋊ j t ≠ topTime (controller (⋊ j t))) :
    ⋊ j t ≠ ⋉ j t' := by
  intro heq
  exact hnotTop (cutMe_eq_cutYou_eq_topTime hctrl heq)

/-- Remark 3.2.3(5): same-index `cutme` and `cutyou` outputs cannot be equal when the
`cutyou` output is not top. -/
theorem cutMe_ne_cutYou_of_cutYou_not_top
    {j : Nat} {t t' : Time}
    (hctrl : controller t = controller t')
    (hnotTop :
      ⋉ j t' ≠ topTime (controller (⋉ j t'))) :
    ⋊ j t ≠ ⋉ j t' := by
  intro heq
  exact hnotTop (cutMe_eq_cutYou_cutYou_eq_topTime hctrl heq)

/-- Lemma 3.2.5: consistent `nextindex` and `cutyou` values differ (`⋉_i = ↱_i` is
impossible). -/
theorem nextIndex_ne_cutYou_of_consistent
    {nextTarget youTarget : Nat}
    {nextBase youBase : Time}
    (hnext : ConsistentTime (↱ nextTarget nextBase))
    (hyou : ConsistentTime (⋉ youTarget youBase)) :
    ↱ nextTarget nextBase ≠ ⋉ youTarget youBase := by
  intro heq
  have hkind := (flags_are_equal hnext hyou heq).1
  cases hkind

/-- Lemma 3.2.5: consistent `cutyou` and `nextindex` values differ. -/
theorem cutYou_ne_nextIndex_of_consistent
    {youTarget nextTarget : Nat}
    {youBase nextBase : Time}
    (hyou : ConsistentTime (⋉ youTarget youBase))
    (hnext : ConsistentTime (↱ nextTarget nextBase)) :
    ⋉ youTarget youBase ≠ ↱ nextTarget nextBase := by
  intro heq
  exact nextIndex_ne_cutYou_of_consistent hnext hyou heq.symm

/-- Remark 3.2.3(5): a consistent `cutyou` cannot lie above same-index `cutme`. -/
theorem not_cutMe_le_cutYou_of_consistent
    {j : Nat} {t t' : Time}
    (hctrl : controller t = controller t')
    (hyou : ConsistentTime (⋉ j t')) :
    ¬ (⋊ j t) ≼ (⋉ j t') := by
  intro hle
  have hcontr : (⋊ j t) 🗲 (⋉ j t') :=
    cutme_contradicts_cutyou j hctrl
  exact not_contradicts_right_of_le_of_consistentTime hle hyou hcontr

/-- Remark 3.2.3(5): a consistent `cutme` cannot lie above same-index `cutyou`. -/
theorem not_cutYou_le_cutMe_of_consistent
    {j : Nat} {t t' : Time}
    (hctrl : controller t = controller t')
    (hcut : ConsistentTime (⋊ j t)) :
    ¬ (⋉ j t') ≼ (⋊ j t) := by
  intro hle
  have hcontr : (⋉ j t') 🗲 (⋊ j t) :=
    contradicts_symm (cutme_contradicts_cutyou j hctrl)
  exact not_contradicts_right_of_le_of_consistentTime hle hcut hcontr

/-- Remark 3.2.3(5): consistent same-index `cutme` and `cutyou` states are incomparable —
once a process enters a cut-me or cut-you state it is committed. -/
theorem cutMe_cutYou_incomparable_of_consistent
    {j : Nat} {t t' : Time}
    (hctrl : controller t = controller t')
    (hcut : ConsistentTime (⋊ j t))
    (hyou : ConsistentTime (⋉ j t')) :
    ¬ (⋊ j t) ≼ (⋉ j t') ∧
      ¬ (⋉ j t') ≼ (⋊ j t) :=
  ⟨not_cutMe_le_cutYou_of_consistent hctrl hyou,
    not_cutYou_le_cutMe_of_consistent hctrl hcut⟩

/-- Definition 3.2.1(1): a consistent `cutme-i` forces `nextindex-i` consistent (it lies
below). -/
theorem nextIndex_consistent_of_cutMe_consistent
    {i : Nat} {t : Time}
    (hcut : ConsistentTime (⋊ i t)) :
    ConsistentTime (↱ i t) := by
  exact consistentTime_of_le (next_le_cutme i t) hcut

/-- Definition 3.2.1(2): a consistent `cutyou-i` forces `nextindex-i` consistent (it lies
below). -/
theorem nextIndex_consistent_of_cutYou_consistent
    {i : Nat} {t : Time}
    (hyou : ConsistentTime (⋉ i t)) :
    ConsistentTime (↱ i t) := by
  exact consistentTime_of_le (next_le_cutyou i t) hyou

/--
A consistent `cutMe_i` state forces every later `cutYou_j` state on the same
base to be consistent.
-/
theorem cutYou_consistent_of_cutMe_consistent_of_lt
    {i j : Nat} (hij : i < j) {t : Time}
    (hcut : ConsistentTime (⋊ i t)) :
    ConsistentTime (⋉ j t) := by
  exact consistentTime_of_le (cutYou_le_cutMe_of_lt hij t) hcut

/--
Below a consistent `cutMe_i` state, later `cutYou` outputs at different Cut
targets cannot collapse.
-/
theorem cutYou_outputs_distinct_of_cutMe_consistent_of_lt
    {i j k : Nat}
    (hij : i < j) (hik : i < k) (hjk : j ≠ k) {t : Time}
    (hcut : ConsistentTime (⋊ i t)) :
    ⋉ j t ≠ ⋉ k t := by
  intro heq
  have hjCons : ConsistentTime (⋉ j t) :=
    cutYou_consistent_of_cutMe_consistent_of_lt hij hcut
  have hkCons : ConsistentTime (⋉ k t) :=
    cutYou_consistent_of_cutMe_consistent_of_lt hik hcut
  have htarget : j = k :=
    flag_target_eq_of_eq_consistent hjCons hkCons heq
  exact hjk htarget

/--
A consistent `cutMe_i` state forces every successor-indexed later `cutYou`
output on the same base to be consistent.
-/
theorem cutYou_successor_consistent_of_cutMe_consistent
    {i : Nat} {t : Time}
    (hcut : ConsistentTime (⋊ i t)) (offset : Nat) :
    ConsistentTime (⋉ (i + offset + 1) t) := by
  exact cutYou_consistent_of_cutMe_consistent_of_lt (by omega) hcut

/--
Below a consistent `cutMe_i` state, the later `cutYou` outputs indexed by
successors of `i` form an injective family. Thus any explicit model witness
with a consistent `cutMe_i` source must provide infinitely many distinct
same-base `cutYou` outputs below that source.
-/
theorem cutYou_successor_outputs_injective_of_cutMe_consistent
    {i : Nat} {t : Time}
    (hcut : ConsistentTime (⋊ i t)) :
    Function.Injective (fun offset : Nat => ⋉ (i + offset + 1) t) := by
  intro left right heq
  by_cases h : left = right
  · exact h
  · exact False.elim
      (cutYou_outputs_distinct_of_cutMe_consistent_of_lt
        (i := i) (j := i + left + 1) (k := i + right + 1)
        (by omega) (by omega) (by omega) hcut heq)

/--
A consistent `cutMe_i` source forces an injectively indexed infinite family of
consistent later `cutYou` outputs in the interval from the original base `t` up
to `nextIndex_i t`. Thus a collision-free model for the same-flag route must
populate that whole interval, not merely add finitely many successors above the
center.
-/
theorem cutYou_successor_infinite_consistent_interval_of_cutMe_consistent
    {i : Nat} {t : Time}
    (hcut : ConsistentTime (⋊ i t)) :
    ∃ f : Nat → Time,
      Function.Injective f ∧
        ∀ offset : Nat,
          ConsistentTime (f offset) ∧
            t ≼ (f offset) ∧
              (f offset) ≼ (↱ i t) := by
  refine
    ⟨fun offset => ⋉ (i + offset + 1) t,
      cutYou_successor_outputs_injective_of_cutMe_consistent hcut, ?_⟩
  intro offset
  exact
    ⟨cutYou_successor_consistent_of_cutMe_consistent hcut offset,
      (⋉ (i + offset + 1)).expansive t,
      cutYou_le_nextIndex_of_lt (by omega) t⟩

/-- Remark 3.2.3(5): a consistent `cutme` state cannot backtrack to `nextindex`. -/
theorem not_cutMe_le_nextIndex_of_consistent
    {j : Nat} {t : Time}
    (hcut : ConsistentTime (⋊ j t))
    (hnext : ConsistentTime (↱ j t)) :
    ¬ (⋊ j t) ≼ (↱ j t) := by
  intro hle
  have heq : ⋊ j t = ↱ j t :=
    le_antisymm hle (next_le_cutme j t)
  exact cutMe_ne_nextIndex_of_consistent hcut hnext heq

/-- Remark 3.2.3(5): a consistent `cutme` state cannot backtrack to the matching
`nextindex` state. -/
theorem not_cutMe_le_nextIndex_of_cutMe_consistent
    {j : Nat} {t : Time}
    (hcut : ConsistentTime (⋊ j t)) :
    ¬ (⋊ j t) ≼ (↱ j t) := by
  exact not_cutMe_le_nextIndex_of_consistent hcut
    (nextIndex_consistent_of_cutMe_consistent hcut)

/-- Remark 3.2.3(5): a consistent `cutme` state cannot strictly backtrack to `nextindex`
(`⋊_j < ↱_j` is impossible). -/
theorem not_cutMe_lt_nextIndex_of_consistent
    {j : Nat} {t : Time}
    (hcut : ConsistentTime (⋊ j t))
    (hnext : ConsistentTime (↱ j t)) :
    ¬ (⋊ j t) ≺ (↱ j t) := by
  intro hlt
  exact not_cutMe_le_nextIndex_of_consistent hcut hnext hlt.1

/-- Remark 3.2.3(5): a consistent `cutme` state cannot strictly backtrack to the matching
`nextindex` state. -/
theorem not_cutMe_lt_nextIndex_of_cutMe_consistent
    {j : Nat} {t : Time}
    (hcut : ConsistentTime (⋊ j t)) :
    ¬ (⋊ j t) ≺ (↱ j t) := by
  exact not_cutMe_lt_nextIndex_of_consistent hcut
    (nextIndex_consistent_of_cutMe_consistent hcut)

/-- Remark 3.2.3: a consistent `cutYou` state cannot backtrack to `nextIndex`. -/
theorem not_cutYou_le_nextIndex_of_consistent
    {j : Nat} {t : Time}
    (hyou : ConsistentTime (⋉ j t))
    (hnext : ConsistentTime (↱ j t)) :
    ¬ (⋉ j t) ≼ (↱ j t) := by
  intro hle
  have heq : ⋉ j t = ↱ j t :=
    le_antisymm hle (next_le_cutyou j t)
  exact cutYou_ne_nextIndex_of_consistent hyou hnext heq

/-- Remark 3.2.3(5): a consistent `cutyou` state cannot backtrack to the matching
`nextindex` state. -/
theorem not_cutYou_le_nextIndex_of_cutYou_consistent
    {j : Nat} {t : Time}
    (hyou : ConsistentTime (⋉ j t)) :
    ¬ (⋉ j t) ≼ (↱ j t) := by
  exact not_cutYou_le_nextIndex_of_consistent hyou
    (nextIndex_consistent_of_cutYou_consistent hyou)

/-- Remark 3.2.3(5): a consistent `cutyou` state cannot strictly backtrack to `nextindex`
(`⋉_j < ↱_j` is impossible). -/
theorem not_cutYou_lt_nextIndex_of_consistent
    {j : Nat} {t : Time}
    (hyou : ConsistentTime (⋉ j t))
    (hnext : ConsistentTime (↱ j t)) :
    ¬ (⋉ j t) ≺ (↱ j t) := by
  intro hlt
  exact not_cutYou_le_nextIndex_of_consistent hyou hnext hlt.1

/-- Remark 3.2.3(5): a consistent `cutyou` state cannot strictly backtrack to the matching
`nextindex` state. -/
theorem not_cutYou_lt_nextIndex_of_cutYou_consistent
    {j : Nat} {t : Time}
    (hyou : ConsistentTime (⋉ j t)) :
    ¬ (⋉ j t) ≺ (↱ j t) := by
  exact not_cutYou_lt_nextIndex_of_consistent hyou
    (nextIndex_consistent_of_cutYou_consistent hyou)

/-- Remark 3.2.3(5): under the consistency hypotheses for the states involved, entering
`cutme-j` or `cutyou-j` is committed and cannot backtrack to `nextindex-j`. -/
theorem cut_commitment_of_consistent
    {j : Nat} {t t' : Time}
    (hctrl : controller t = controller t')
    (hcut : ConsistentTime (⋊ j t))
    (hyou : ConsistentTime (⋉ j t'))
    (hnext : ConsistentTime (↱ j t))
    (hnext' : ConsistentTime (↱ j t')) :
    ¬ (⋊ j t) ≼ (⋉ j t') ∧
      ¬ (⋉ j t') ≼ (⋊ j t) ∧
      ¬ (⋊ j t) ≺ (↱ j t) ∧
      ¬ (⋉ j t') ≺ (↱ j t') :=
  ⟨not_cutMe_le_cutYou_of_consistent hctrl hyou,
    not_cutYou_le_cutMe_of_consistent hctrl hcut,
    not_cutMe_lt_nextIndex_of_consistent hcut hnext,
    not_cutYou_lt_nextIndex_of_consistent hyou hnext'⟩

/-- Remark 3.2.3(5): entering consistent same-index `cutme` and `cutyou` states is
committed, without separately assuming consistency of the matching `nextindex` states. -/
theorem cut_commitment_of_cut_states_consistent
    {j : Nat} {t t' : Time}
    (hctrl : controller t = controller t')
    (hcut : ConsistentTime (⋊ j t))
    (hyou : ConsistentTime (⋉ j t')) :
    ¬ (⋊ j t) ≼ (⋉ j t') ∧
      ¬ (⋉ j t') ≼ (⋊ j t) ∧
      ¬ (⋊ j t) ≺ (↱ j t) ∧
      ¬ (⋉ j t') ≺ (↱ j t') := by
  exact
    ⟨not_cutMe_le_cutYou_of_consistent hctrl hyou,
      not_cutYou_le_cutMe_of_consistent hctrl hcut,
      not_cutMe_lt_nextIndex_of_cutMe_consistent hcut,
      not_cutYou_lt_nextIndex_of_cutYou_consistent hyou⟩

end CutTheorems

/--
Support package for the paper's standing sequential Cut-system context.
-/
class SequentialLocatedSemilatticeWithCut (Time : Type v) (Ctrl : outParam (Type u))
    extends LocatedSemilatticeWithCut Time Ctrl where
  sequential : Sequential (Time := Time)

/--
Package an explicit cutting-flag family as the paper's standing fixed
sequential Cut system once the underlying located semilattice is sequential.
-/
def PackageSpec.toSequentialLocatedSemilatticeWithCut
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] (S : PackageSpec Time)
    (hseq : Sequential (Time := Time)) :
    SequentialLocatedSemilatticeWithCut Time Ctrl where
  toLocatedSemilatticeWithCut := S.toLocatedSemilatticeWithCut
  sequential := hseq

/-- Definition 3.2.7: a flag `Q` is scope-extruding when `(Q t) # s ≼ Q (t # s)` for all
`s, t`. -/
def ScopeExtruding {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (Q : Flag Time) : Prop :=
  ∀ t s : Time, le (attest (Q t) s) (Q (attest t s))

/-- Lemma 3.2.8: the scoped flag step preserves the controller side-condition. -/
theorem scope_flag_controller_eq
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (Q : Flag Time) (t s : Time) :
    controller (Q t) = controller (Q (attest t s)) := by
  calc
    controller (Q t) = controller t := Q.controller_preserving t
    _ = controller (attest t s) := (controller_preserving t s).symm
    _ = controller (Q (attest t s)) :=
      (Q.controller_preserving (attest t s)).symm

/-- Lemma 3.2.8: `Q t ≼ Q (t # s)` for a scope-extruding flag `Q`. -/
theorem scope_flag
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (Q : Flag Time)
    (hscope : ScopeExtruding Q) (t s : Time) :
    le (Q t) (Q (attest t s)) :=
  le_trans (le_attest (Q t) s) (hscope t s)

/--
Lemma 3.2.8: the scoped flag step provides both the
controller side-condition and the local order needed for `Inc`.
-/
theorem scope_flag_step_data
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (Q : Flag Time)
    (hscope : ScopeExtruding Q) (t s : Time) :
    controller (Q t) = controller (Q (attest t s)) ∧
      le (Q t) (Q (attest t s)) :=
  ⟨scope_flag_controller_eq Q t s, scope_flag Q hscope t s⟩

section CutScopeConsequences
variable {Time : Type v} {Ctrl : Type u} [inst : LocatedSemilatticeWithCut Time Ctrl]
include inst

/--
Remark 4.1.4, operational explanation of the `Cut` rule, conditional local
component: if `cutMe_i` is scope-extruding, the center update factors through
the displayed expansivity step and the displayed scope-extrusion step.
-/
theorem cutMe_scope_extrusion_center_update_chain
    (i : Nat) (t s : Time)
    (hscope : ScopeExtruding (cutMe (Time := Time) i)) :
    (⋊ i t) ≼ ((⋊ i t) # s) ∧
      ((⋊ i t) # s) ≼ (⋊ i (t # s)) ∧
        (⋊ i t) ≼ (⋊ i (t # s)) := by
  have hExpansive :
      (⋊ i t) ≼ ((⋊ i t) # s) :=
    le_attest (⋊ i t) s
  have hScope :
      ((⋊ i t) # s) ≼ (⋊ i (t # s)) :=
    hscope t s
  exact ⟨hExpansive, hScope, le_trans hExpansive hScope⟩

/--
Remark 4.1.4, operational explanation of the `Cut` rule, lower-index
attestation order component. This specializes attestation expansiveness to the
displayed Cut center time; it does not supply the same-flag or consistency
side-conditions needed for a full `Inc` step.
-/
theorem cut_lower_attestation_update_le
    (i j : Nat) (ti tj tk : Time) :
    ti ≼ (ti # (⋊ i (tj # (⋉ j tk)))) :=
  le_attest ti (⋊ i (tj # (⋉ j tk)))

/--
Remark 4.1.4, operational explanation of the `Cut` rule, upper-index
transition order component. This is the displayed final `cutYou_j` to
`nextIndex_i` order step; it does not by itself package a full path-rule
transition.
-/
theorem cut_upper_transition_le
    {i j : Nat} (hij : i < j) (tk : Time) :
    (⋉ j tk) ≼ (↱ i tk) :=
  cutYou_le_nextIndex_of_lt hij tk

/--
Lemma 3.2.8, Inc side-condition: consistent source and
target times under the same cutting flag have the same flag lookup.
-/
theorem same_cutting_flag_flagOf_eq
    (Q : Flag Time)
    (hmem : cuttingFlagSet.member Q) {t s : Time}
    (hsource : ConsistentTime (Q t))
    (htarget : ConsistentTime (Q (t # s))) :
    flagOf cuttingFlagSet (Q t) =
      flagOf cuttingFlagSet (Q (t # s)) := by
  have hsourceForm : HasForm Q (Q t) :=
    ⟨hsource, ⟨t, rfl⟩⟩
  have htargetForm :
      HasForm Q (Q (t # s)) :=
    ⟨htarget, ⟨t # s, rfl⟩⟩
  calc
    flagOf cuttingFlagSet (Q t) = some ⟨Q, hmem⟩ :=
      flagOf_eq_some_of_hasForm cuttingFlagSet hmem hsourceForm
    _ = flagOf cuttingFlagSet (Q (t # s)) :=
      (flagOf_eq_some_of_hasForm cuttingFlagSet hmem htargetForm).symm

/--
Remark 3.2.9(2): under the strict (equality) form of scope-extrusion for `nextindex j`
and `cutme j`, the two nested flag applications are equal (both reduce to `⋊ j t`). The
remark's subsequent flag-set step is guarded by `⋊ j t ∈ CTime`; see
`strict_scope_extrusion_cutMe_eq_nextIndex_of_consistent`.
-/
theorem strict_scope_extrusion_nested_cutMe_nextIndex_eq
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s)) :
    ⋊ j (↱ j t) = ↱ j (⋊ j t) := by
  have hnext_cut : (↱ j t) ≼ (⋊ j t) :=
    next_le_cutme j t
  have hnext_ctrl :
      controller (↱ j t) = controller (⋊ j t) :=
    hnext_cut.1
  have ht_le_cut : t ≼ (⋊ j t) :=
    (⋊ j).expansive t
  have ht_le_next : t ≼ (↱ j t) :=
    (↱ j).expansive t
  have hcut_eq_next_nested :
      ⋊ j t = ↱ j (⋊ j t) := by
    calc
      ⋊ j t = (↱ j t) # (⋊ j t) :=
        hnext_cut.2.symm
      _ = ↱ j (t # (⋊ j t)) :=
        hnextStrict t (⋊ j t)
      _ = ↱ j (⋊ j t) := by rw [ht_le_cut.2]
  have hcut_eq_cut_nested :
      ⋊ j t = ⋊ j (↱ j t) := by
    calc
      ⋊ j t = (↱ j t) # (⋊ j t) :=
        hnext_cut.2.symm
      _ = (⋊ j t) # (↱ j t) :=
        self_join_comm hnext_ctrl
      _ = ⋊ j (t # (↱ j t)) :=
        hcutStrict t (↱ j t)
      _ = ⋊ j (↱ j t) := by rw [ht_le_next.2]
  have hnested :
      ⋊ j (↱ j t) = ↱ j (⋊ j t) :=
    hcut_eq_cut_nested.symm.trans hcut_eq_next_nested
  exact hnested

/-- Remark 3.2.9(2): under the consistency guard `⋊ j t ∈ CTime`, the common nested value
has both flag forms, enabling the flag-set step. -/
theorem strict_scope_extrusion_nested_hasForms_of_consistent
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s))
    (hcommon : ConsistentTime (⋊ j (↱ j t))) :
    HasForm (⋊ j) (⋊ j (↱ j t)) ∧
      HasForm (↱ j) (⋊ j (↱ j t)) := by
  have hnested :
      ⋊ j (↱ j t) = ↱ j (⋊ j t) :=
    strict_scope_extrusion_nested_cutMe_nextIndex_eq
      j t hnextStrict hcutStrict
  exact
    ⟨⟨hcommon, ⟨↱ j t, rfl⟩⟩,
      ⟨hcommon, ⟨⋊ j t, hnested⟩⟩⟩

/-- Remark 3.2.9(2): under strict scope-extrusion and the guard `⋊ j t ∈ CTime`, flag-set
injectivity forces `⋊ j = ↱ j` — the equation the remark derives before invoking flag
distinctness. -/
theorem strict_scope_extrusion_cutMe_eq_nextIndex_of_consistent
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s))
    (hcommon : ConsistentTime (⋊ j (↱ j t))) :
    cutMe (Time := Time) j = ↱ j := by
  rcases strict_scope_extrusion_nested_hasForms_of_consistent
      j t hnextStrict hcutStrict hcommon with
    ⟨hcutForm, hnextForm⟩
  exact flag_unique_of_hasForm cuttingFlagSet
    (cutMe_mem j) (nextIndex_mem j) hcutForm hnextForm

/-- Remark 3.2.9(2): the reductio — under strict scope-extrusion and the guard
`⋊ j t ∈ CTime`, the forced collapse `⋊ j = ↱ j` contradicts cutting-flag distinctness. -/
theorem strict_scope_extrusion_contradicts_cutting_distinctness_of_consistent
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s))
    (hcommon : ConsistentTime (⋊ j (↱ j t))) :
    False := by
  have hflag : ⋊ j = ↱ j :=
    strict_scope_extrusion_cutMe_eq_nextIndex_of_consistent
      j t hnextStrict hcutStrict hcommon
  have hkind : CutFlagKind.cutMe = CutFlagKind.nextIndex :=
    (cutting_eq_iff.mp hflag).1
  cases hkind

/-- Remark 3.2.9(2): contrapositive of the reductio — since consistency of the common
nested `cutme`/`nextindex` value would force the collapse above, strict scope-extrusion
makes that value inconsistent. -/
theorem strict_scope_extrusion_nested_not_consistent
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s)) :
    ¬ ConsistentTime (⋊ j (↱ j t)) := by
  intro hcommon
  exact strict_scope_extrusion_contradicts_cutting_distinctness_of_consistent
    j t hnextStrict hcutStrict hcommon

/--
Remark 3.2.9(2) consequence: under strict scope-extrusion the
common nested `cutMe`/`nextIndex` value equals the top time at its controller.
-/
theorem strict_scope_extrusion_nested_eq_topTime
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s)) :
    ⋊ j (↱ j t) =
      topTime (controller (⋊ j (↱ j t))) := by
  have hnot :
      ¬ ConsistentTime (⋊ j (↱ j t)) :=
    strict_scope_extrusion_nested_not_consistent j t hnextStrict hcutStrict
  simpa [LocatedSemilattice.ConsistentTime, LocatedSemilattice.topTime]
    using Classical.not_not.mp hnot

/--
Remark 3.2.9(2) consequence: under strict scope-extrusion the
common nested value has no defined cutting flag.
-/
theorem strict_scope_extrusion_nested_flagOf_none
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s)) :
    flagOf cuttingFlagSet (⋊ j (↱ j t)) = none := by
  exact flagOf_eq_none_of_not_consistent cuttingFlagSet
    (strict_scope_extrusion_nested_not_consistent j t hnextStrict hcutStrict)

/--
Remark 3.2.9(2) consequence: the other syntactic side of the
displayed nested equality is also inconsistent under strict scope-extrusion.
-/
theorem strict_scope_extrusion_nested_nextIndex_cutMe_not_consistent
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s)) :
    ¬ ConsistentTime (↱ j (⋊ j t)) := by
  intro hconsistent
  have hnested :
      ⋊ j (↱ j t) = ↱ j (⋊ j t) :=
    strict_scope_extrusion_nested_cutMe_nextIndex_eq j t hnextStrict hcutStrict
  have hleft :
      ConsistentTime (⋊ j (↱ j t)) := by
    simpa [hnested] using hconsistent
  exact strict_scope_extrusion_nested_not_consistent j t hnextStrict hcutStrict hleft

/--
Remark 3.2.9(2) consequence: the other syntactic side of the
displayed nested equality is top at its controller.
-/
theorem strict_scope_extrusion_nested_nextIndex_cutMe_eq_topTime
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s)) :
    ↱ j (⋊ j t) =
      topTime (controller (↱ j (⋊ j t))) := by
  have hnot :
      ¬ ConsistentTime (↱ j (⋊ j t)) :=
    strict_scope_extrusion_nested_nextIndex_cutMe_not_consistent
      j t hnextStrict hcutStrict
  simpa [LocatedSemilattice.ConsistentTime, LocatedSemilattice.topTime]
    using Classical.not_not.mp hnot

/--
Remark 3.2.9(2) consequence: the other syntactic side of the
displayed nested equality has no defined cutting flag.
-/
theorem strict_scope_extrusion_nested_nextIndex_cutMe_flagOf_none
    (j : Nat) (t : Time)
    (hnextStrict : ∀ t s : Time,
      (↱ j t) # s =
        ↱ j (t # s))
    (hcutStrict : ∀ t s : Time,
      (⋊ j t) # s =
        ⋊ j (t # s)) :
    flagOf cuttingFlagSet (↱ j (⋊ j t)) = none := by
  exact flagOf_eq_none_of_not_consistent cuttingFlagSet
    (strict_scope_extrusion_nested_nextIndex_cutMe_not_consistent
      j t hnextStrict hcutStrict)

end CutScopeConsequences

end LocatedSemilatticeWithCut

end ConsistentHistories.Foundation.Cut.Structure
