import ConsistentHistories.AlternativePresentation.AlternativeLocatedSemilattice

namespace ConsistentHistories.AlternativePresentation

open ConsistentHistories.Models.Cut.Consistency
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.Cut.Flags
open ConsistentHistories.Foundation.LocatedSemilattices.TopTrees
open ConsistentHistories.Foundation.LocatedSemilattices.TopTrees.BoundedSemilattice

universe u v

namespace DegenerateAlternativeCutExample

/-!
A degenerate located semilattice with Cut (Definition 7.7) over a single
controller (`PUnit`) whose one component is the two-element bounded semilattice
`Bool`. The cutting attestation sends the bottom cutting flag to the identity and
every non-bottom flag to top. It satisfies the Definition 7.7(2)(c) separating
condition vacuously — the only consistent (non-top) output comes from the bottom
flag — yet distinct non-bottom flags such as `cutMe`/`cutYou` collapse to the same
global function, so the function-level flag injectivity
(`CuttingFlagFunctionInjective`) that would recover the original Cut interface
fails. The example thereby separates the alternative presentation's separating
condition from that stronger injectivity requirement.
-/

abbrev BoolSemilattice : Type := Bool

/-- Underlying located semilattice (Definition 7.6): one controller (`PUnit`)
whose single component is the two-element bounded semilattice `Bool`, carrying the
required join self-attestation (Definition 7.6(4), Example 7.4(3)). -/
def located : AlternativeLocatedSemilattice where
  Ctrl := PUnit
  timeAt _ := BoolSemilattice
  timeInst _ := inferInstance
  attest _ _ := joinSelfAttestation BoolSemilattice
  self_attest_join := by
    intro _p _y _x
    rfl

/-- Raw cutting map: the bottom cutting flag acts as the identity, every other
flag maps to top. Underlies `degenerateCuttingAttestation`. -/
def degenerateCuttingToFun
    (flag : ConcreteTime) (x : BoolSemilattice) :
    BoolSemilattice :=
  match flag with
  | ConcreteTime.bot => x
  | _ => (⊤ : BoolSemilattice)

/-- Cutting attestation (Definition 7.2) built from `degenerateCuttingToFun`:
expansive and strongly contradiction-preserving over `ConcreteTime`. -/
def degenerateCuttingAttestation :
    Attestation ConcreteTime BoolSemilattice where
  toFun := degenerateCuttingToFun
  expansive := by
    intro flag x
    cases flag <;> cases x <;> rfl
  strongly_contradiction_preserving := by
    intro flag flag' hcontr x x'
    cases flag <;> cases flag' <;> cases x <;> cases x' <;> try rfl
    all_goals cases hcontr

/-- Definition 7.7(2)(c) separating condition for the degenerate cutting
attestation, holding vacuously: every non-bottom flag outputs top, so no two
consistent (non-top) outputs can coincide. -/
theorem degenerateCuttingAttestation_separating :
    degenerateCuttingAttestation.Separating := by
  intro flag _flag' x _x' hflag _hflag' _heq hnotTop
  cases flag
  · exact False.elim (hflag rfl)
  all_goals cases x <;> exact False.elim (hnotTop rfl)

/-- The degenerate cutting attestation is monotone (Definition 7.5(2)). -/
theorem degenerateCuttingAttestation_monotone :
    degenerateCuttingAttestation.Monotone := by
  intro flag flag' hle x
  cases flag <;> cases flag' <;> cases x <;> try rfl
  all_goals
    have hbot :=
      (cuttingFlagBoundedSemilattice.le_bot_iff_eq_bot _).mp hle
    cases hbot

/--
The assembled located semilattice with Cut: every Definition 7.7 clause holds
(bottom/top, item 3 separating, monotone), yet non-bottom cutting flags collapse
as global functions on time.
-/
def system : AlternativeLocatedSemilatticeWithCut where
  toLocated := located
  cutting _p := degenerateCuttingAttestation
  cutting_bot := by
    intro _p x
    cases x <;> rfl
  cutting_top := by
    intro _p x
    cases x <;> rfl
  cutting_separating := by
    intro _p
    exact degenerateCuttingAttestation_separating
  cutting_attestation_monotone := by
    intro _p
    exact degenerateCuttingAttestation_monotone

/--
The Definition 7.7(2)(c) separating clause does not imply the extra
function-level flag injectivity needed by
`toOriginalPackageSpec_of_cuttingFlagFunctionInjective`: here `cutMe`/`cutYou`
have the same global cutting function.
-/
theorem not_cuttingFlagFunctionInjective :
    ¬ system.CuttingFlagFunctionInjective := by
  intro hinj
  have hcollapse :
      system.cuttingFlag CutFlagKind.cutMe 0 =
        system.cuttingFlag CutFlagKind.cutYou 0 := by
    change
      ({ toFun := system.cuttingTime (ConcreteTime.ofFlagKind CutFlagKind.cutMe 0),
          controller_preserving := _,
          expansive := _ } :
          Flag system.toLocated.FlatTime) =
        { toFun := system.cuttingTime (ConcreteTime.ofFlagKind CutFlagKind.cutYou 0),
          controller_preserving := _,
          expansive := _ }
    rw [Flag.mk.injEq]
    funext t
    rcases t with ⟨p, x⟩
    cases p
    cases x <;> rfl
  have hkind : CutFlagKind.cutMe = CutFlagKind.cutYou :=
    (hinj hcollapse).1
  cases hkind

/--
The Definition 7.7(2)(c) consistent-output separating condition holds for the
degenerate alternative Cut system, while the extra function-level flag
injectivity needed for the original Cut interface fails.
-/
theorem cuttingTimeSeparating_not_cuttingFlagFunctionInjective :
    system.CuttingTimeSeparating ∧ ¬ system.CuttingFlagFunctionInjective := by
  exact ⟨system.cuttingTime_separating, not_cuttingFlagFunctionInjective⟩

/--
Existence witness: Definition 7.7(2)(c) separating data does not imply the extra
global flag-function injectivity obligation.
-/
theorem exists_cuttingTimeSeparating_not_cuttingFlagFunctionInjective :
    ∃ L : AlternativeLocatedSemilatticeWithCut.{0},
      L.CuttingTimeSeparating ∧ ¬ L.CuttingFlagFunctionInjective := by
  exact ⟨system, cuttingTimeSeparating_not_cuttingFlagFunctionInjective⟩

end DegenerateAlternativeCutExample

/--
Definition 7.7(2)(c) separating condition, bottom-excluded form: for non-bottom
flags, equal consistent (non-top) cutting outputs force equal flags.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_flag_eq_of_eq_not_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    {flag flag' : ConcreteTime}
    {x x' : L.toLocated.timeAt p}
    (hflag : flag ≠ cuttingFlagBoundedSemilattice.bot)
    (hflag' : flag' ≠ cuttingFlagBoundedSemilattice.bot)
    (heq : (L.cutting p).toFun flag x = (L.cutting p).toFun flag' x')
    (hnotTop : (L.cutting p).toFun flag x ≠ (⊤ : L.toLocated.timeAt p)) :
    flag = flag' := by
  exact L.cutting_separating p flag flag' x x' hflag hflag' heq hnotTop

/--
Definition 7.7(2)(c): restricted to
`CuttingPoset \ {top,bottom}`, same-component equal consistent cutting outputs
have equal cutting-poset parameters.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_flag_eq_of_eq_consistent_nontrivial
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    {flag flag' : ConcreteTime}
    {x x' : L.toLocated.timeAt p}
    (hflag_bot : flag ≠ cuttingFlagBoundedSemilattice.bot)
    (_hflag_top : flag ≠ cuttingFlagBoundedSemilattice.top)
    (hflag'_bot : flag' ≠ cuttingFlagBoundedSemilattice.bot)
    (_hflag'_top : flag' ≠ cuttingFlagBoundedSemilattice.top)
    (heq : (L.cutting p).toFun flag x = (L.cutting p).toFun flag' x')
    (hnotTop : (L.cutting p).toFun flag x ≠ (⊤ : L.toLocated.timeAt p)) :
    flag = flag' := by
  exact L.cutting_flag_eq_of_eq_not_top p hflag_bot hflag'_bot heq hnotTop

/--
Definition 7.7(2)(c), postfix form (Definition 7.2(7)): for non-bottom flags,
equal consistent postfix cutting outputs over `CuttingPoset` force equal flags.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_postfix_flag_eq_of_eq_not_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    {flag flag' : ConcreteTime}
    {x x' : L.toLocated.timeAt p}
    (hflag : flag ≠ cuttingFlagBoundedSemilattice.bot)
    (hflag' : flag' ≠ cuttingFlagBoundedSemilattice.bot)
    (heq : (L.cutting p).postfixApply x flag =
      (L.cutting p).postfixApply x' flag')
    (hnotTop :
      (L.cutting p).postfixApply x flag ≠ (⊤ : L.toLocated.timeAt p)) :
    flag = flag' := by
  exact Attestation.separating_postfix_eq_of_not_top
    (L.cutting_separating p) hflag hflag' heq hnotTop

/--
Remark 7.8(2): `cutMe j` and `cutYou j` lie on distinct branches of
`CuttingPoset` (Figure 6), and the cutting attestation is strongly
contradiction-preserving (Definition 7.2(3)); hence their outputs contradict
(`🗲`) in the component time semilattice — the characteristic contradiction
axiom `⋊ j t 🗲 ⋉ j t'` of Definition 3.2.1(4).
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_cutMe_contradicts_cutYou
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p) :
    ((L.cutting p).toFun (ConcreteTime.cutMe j) x) 🗲 ((L.cutting p).toFun (ConcreteTime.cutYou j) x') := by
  exact (L.cutting p).strongly_contradiction_preserving
    (cuttingFlag_cutMe_contradicts_cutYou j) x x'

/--
Remark 7.8(2), via the Definition 7.7(2)(c) global cutting operation: the
same-index `cutMe`/`cutYou` contradiction expressed on the flattened
located-semilattice time `FlatTime`.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutMe_contradicts_cutYou
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p) :
    (L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩) 🗲 (L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩) := by
  constructor
  · rfl
  · have hcontr := L.cutting_cutMe_contradicts_cutYou p j x x'
    change L.toLocated.flatAttest
        ⟨p, (L.cutting p).toFun (ConcreteTime.cutMe j) x⟩
        ⟨p, (L.cutting p).toFun (ConcreteTime.cutYou j) x'⟩ =
      L.toLocated.toLocatedSemilattice.top p
    rw [AlternativeLocatedSemilattice.flatAttest_self_join]
    apply Sigma.ext
    · rfl
    · exact heq_of_eq hcontr

/--
Remark 7.8(2) consequence: if same-index `cutMe` and `cutYou` cutting outputs
are equal, that output contradicts itself and so equals top (is inconsistent).
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_cutMe_eq_cutYou_eq_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (heq : (L.cutting p).toFun (ConcreteTime.cutMe j) x =
      (L.cutting p).toFun (ConcreteTime.cutYou j) x') :
    (L.cutting p).toFun (ConcreteTime.cutMe j) x =
      (⊤ : L.toLocated.timeAt p) := by
  have hcontr := L.cutting_cutMe_contradicts_cutYou p j x x'
  have hself :
      ((L.cutting p).toFun (ConcreteTime.cutMe j) x) 🗲 ((L.cutting p).toFun (ConcreteTime.cutMe j) x) := by
    simpa [heq] using hcontr
  exact (BoundedSemilattice.contradicts_self_iff_eq_top _).mp hself

/--
Remark 7.8(2) consequence: if same-index `cutMe` and `cutYou` cutting outputs
are equal, the `cutYou` output equals top (is inconsistent).
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_cutMe_eq_cutYou_cutYou_eq_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (heq : (L.cutting p).toFun (ConcreteTime.cutMe j) x =
      (L.cutting p).toFun (ConcreteTime.cutYou j) x') :
    (L.cutting p).toFun (ConcreteTime.cutYou j) x' =
      (⊤ : L.toLocated.timeAt p) := by
  calc
    (L.cutting p).toFun (ConcreteTime.cutYou j) x' =
        (L.cutting p).toFun (ConcreteTime.cutMe j) x := heq.symm
    _ = (⊤ : L.toLocated.timeAt p) :=
      L.cutting_cutMe_eq_cutYou_eq_top p j x x' heq

/--
Remark 7.8(2) consequence: same-index `cutMe` and `cutYou` cutting outputs
cannot be equal when the `cutMe` output is consistent.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_cutMe_ne_cutYou_of_consistent_output
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hconsistent :
      BoundedSemilattice.Consistent
        ((L.cutting p).toFun (ConcreteTime.cutMe j) x)) :
    (L.cutting p).toFun (ConcreteTime.cutMe j) x ≠
      (L.cutting p).toFun (ConcreteTime.cutYou j) x' := by
  intro heq
  exact hconsistent (L.cutting_cutMe_eq_cutYou_eq_top p j x x' heq)

/--
Remark 7.8(2) consequence: same-index `cutMe` and `cutYou` cutting outputs
cannot be equal when the `cutYou` output is consistent.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_cutMe_ne_cutYou_of_cutYou_consistent_output
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hconsistent :
      BoundedSemilattice.Consistent
        ((L.cutting p).toFun (ConcreteTime.cutYou j) x')) :
    (L.cutting p).toFun (ConcreteTime.cutMe j) x ≠
      (L.cutting p).toFun (ConcreteTime.cutYou j) x' := by
  intro heq
  exact hconsistent (L.cutting_cutMe_eq_cutYou_cutYou_eq_top p j x x' heq)

/--
Remark 7.8(2) consequence, via the Definition 7.7(2)(c) global cutting
operation: if same-index global `cutMe` and `cutYou` outputs agree, the `cutMe`
output is the controller top time.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutMe_eq_cutYou_eq_topTime
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (heq :
      L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ =
        L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩) :
    L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ =
      L.toLocated.toLocatedSemilattice.topTime p := by
  have hsigma :
      (⟨p, (L.cutting p).toFun (ConcreteTime.cutMe j) x⟩ :
          L.toLocated.FlatTime) =
        ⟨p, (L.cutting p).toFun (ConcreteTime.cutYou j) x'⟩ := by
    simpa [AlternativeLocatedSemilatticeWithCut.cuttingTime] using heq
  have hlocalEq :
      (L.cutting p).toFun (ConcreteTime.cutMe j) x =
        (L.cutting p).toFun (ConcreteTime.cutYou j) x' := by
    exact eq_of_heq (by
      simpa only [Sigma.mk.injEq, true_and] using hsigma)
  change L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ =
    L.toLocated.toLocatedSemilattice.top p
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (L.cutting_cutMe_eq_cutYou_eq_top p j x x' hlocalEq)

/--
Remark 7.8(2) consequence, via the Definition 7.7(2)(c) global cutting
operation: if same-index global `cutMe` and `cutYou` outputs agree, the `cutYou`
output is the controller top time.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutMe_eq_cutYou_cutYou_eq_topTime
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (heq :
      L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ =
        L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩) :
    L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩ =
      L.toLocated.toLocatedSemilattice.topTime p := by
  calc
    L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩ =
        L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ := heq.symm
    _ = L.toLocated.toLocatedSemilattice.topTime p :=
      L.cuttingTime_cutMe_eq_cutYou_eq_topTime p j x x' heq

/--
Remark 7.8(2) consequence, via the Definition 7.7(2)(c) global cutting
operation: same-index global `cutMe` and `cutYou` outputs cannot agree when the
`cutMe` output is consistent.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutMe_ne_cutYou_of_consistent_output
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hconsistent :
      L.toLocated.toLocatedSemilattice.ConsistentTime
        (L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩)) :
    L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ ≠
      L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩ := by
  intro heq
  exact
    ((L.toLocated.toLocatedSemilattice.consistentTime_iff_ne_topTime
      (L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩)).mp hconsistent p)
        (L.cuttingTime_cutMe_eq_cutYou_eq_topTime p j x x' heq)

/--
Remark 7.8(2) consequence, via the Definition 7.7(2)(c) global cutting
operation: same-index global `cutMe` and `cutYou` outputs cannot agree when the
`cutYou` output is consistent.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutMe_ne_cutYou_of_cutYou_consistent_output
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hconsistent :
      L.toLocated.toLocatedSemilattice.ConsistentTime
        (L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩)) :
    L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ ≠
      L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩ := by
  intro heq
  exact
    ((L.toLocated.toLocatedSemilattice.consistentTime_iff_ne_topTime
      (L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩)).mp hconsistent p)
        (L.cuttingTime_cutMe_eq_cutYou_cutYou_eq_topTime p j x x' heq)

/--
Remark 7.8(2) consequence, via the Definition 7.7(2)(c) global cutting
operation: same-index global `cutMe` and `cutYou` outputs cannot agree when the
`cutMe` output is not top.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutMe_ne_cutYou_of_not_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hnotTop :
      L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ ≠
        L.toLocated.toLocatedSemilattice.topTime p) :
    L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ ≠
      L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩ := by
  intro heq
  exact hnotTop (L.cuttingTime_cutMe_eq_cutYou_eq_topTime p j x x' heq)

/--
Remark 7.8(2) consequence, via the Definition 7.7(2)(c) global cutting
operation: same-index global `cutMe` and `cutYou` outputs cannot agree when the
`cutYou` output is not top.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutMe_ne_cutYou_of_cutYou_not_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hnotTop :
      L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩ ≠
        L.toLocated.toLocatedSemilattice.topTime p) :
    L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ ≠
      L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩ := by
  intro heq
  exact hnotTop
    (L.cuttingTime_cutMe_eq_cutYou_cutYou_eq_topTime p j x x' heq)

/--
Remark 7.8(2) order consequence, via the Definition 7.7(2)(c) global cutting
operation: a consistent same-index global `cutYou` output cannot lie above the
contradictory `cutMe` output.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_not_cutMe_le_cutYou_of_consistent_output
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hconsistent :
      L.toLocated.toLocatedSemilattice.ConsistentTime
        (L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩)) :
    ¬ (L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩) ≼ (L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩) := by
  exact
    L.toLocated.toLocatedSemilattice.not_le_right_of_contradicts_consistentTime
      (L.cuttingTime_cutMe_contradicts_cutYou p j x x') hconsistent

/--
Remark 7.8(2) order consequence, via the Definition 7.7(2)(c) global cutting
operation: a consistent same-index global `cutMe` output cannot lie above the
contradictory `cutYou` output.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_not_cutYou_le_cutMe_of_consistent_output
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hconsistent :
      L.toLocated.toLocatedSemilattice.ConsistentTime
        (L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩)) :
    ¬ (L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩) ≼ (L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩) := by
  exact
    L.toLocated.toLocatedSemilattice.not_le_left_of_contradicts_consistentTime
      (L.cuttingTime_cutMe_contradicts_cutYou p j x x') hconsistent

/--
Remark 7.8(2) order consequence, via the Definition 7.7(2)(c) global cutting
operation: consistent same-index global `cutMe` and `cutYou` outputs are
incomparable.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutMe_cutYou_incomparable_of_consistent_outputs
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hcut :
      L.toLocated.toLocatedSemilattice.ConsistentTime
        (L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩))
    (hyou :
      L.toLocated.toLocatedSemilattice.ConsistentTime
        (L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩)) :
    ¬ (L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩) ≼ (L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩) ∧
      ¬ (L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x'⟩) ≼ (L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩) := by
  exact
    ⟨L.cuttingTime_not_cutMe_le_cutYou_of_consistent_output p j x x' hyou,
      L.cuttingTime_not_cutYou_le_cutMe_of_consistent_output p j x x' hcut⟩

/--
Remark 7.8(2) consequence: same-index `cutMe` and `cutYou` cannot produce the
same cutting-attestation output when the `cutMe` output is not top.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_cutMe_ne_cutYou_of_not_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hnotTop :
      (L.cutting p).toFun (ConcreteTime.cutMe j) x ≠
        (⊤ : L.toLocated.timeAt p)) :
    (L.cutting p).toFun (ConcreteTime.cutMe j) x ≠
      (L.cutting p).toFun (ConcreteTime.cutYou j) x' := by
  intro heq
  exact hnotTop (L.cutting_cutMe_eq_cutYou_eq_top p j x x' heq)

/--
Remark 7.8(2) consequence: same-index `cutMe` and `cutYou` cannot produce the
same cutting-attestation output when the `cutYou` output is not top.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_cutMe_ne_cutYou_of_cutYou_not_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hnotTop :
      (L.cutting p).toFun (ConcreteTime.cutYou j) x' ≠
        (⊤ : L.toLocated.timeAt p)) :
    (L.cutting p).toFun (ConcreteTime.cutMe j) x ≠
      (L.cutting p).toFun (ConcreteTime.cutYou j) x' := by
  intro heq
  exact hnotTop (L.cutting_cutMe_eq_cutYou_cutYou_eq_top p j x x' heq)

/--
Remark 7.8(2) order consequence: a consistent same-index `cutYou` cutting
output cannot lie above the contradictory `cutMe` output.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_not_cutMe_le_cutYou_of_consistent_output
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hconsistent :
      BoundedSemilattice.Consistent
        ((L.cutting p).toFun (ConcreteTime.cutYou j) x')) :
    ¬ ((L.cutting p).toFun (ConcreteTime.cutMe j) x) ≤ ((L.cutting p).toFun (ConcreteTime.cutYou j) x') := by
  intro hle
  have hcontr := L.cutting_cutMe_contradicts_cutYou p j x x'
  exact hconsistent (hle.symm.trans hcontr)

/--
Remark 7.8(2) order consequence: a consistent same-index `cutMe` cutting
output cannot lie above the contradictory `cutYou` output.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_not_cutYou_le_cutMe_of_consistent_output
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hconsistent :
      BoundedSemilattice.Consistent
        ((L.cutting p).toFun (ConcreteTime.cutMe j) x)) :
    ¬ ((L.cutting p).toFun (ConcreteTime.cutYou j) x') ≤ ((L.cutting p).toFun (ConcreteTime.cutMe j) x) := by
  intro hle
  have hcontr :=
    BoundedSemilattice.contradicts_comm
      (L.cutting_cutMe_contradicts_cutYou p j x x')
  exact hconsistent (hle.symm.trans hcontr)

/--
Remark 7.8(2) order consequence: consistent same-index `cutMe` and `cutYou`
cutting outputs are incomparable in the component semilattice.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_cutMe_cutYou_incomparable_of_consistent_outputs
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x x' : L.toLocated.timeAt p)
    (hcut :
      BoundedSemilattice.Consistent
        ((L.cutting p).toFun (ConcreteTime.cutMe j) x))
    (hyou :
      BoundedSemilattice.Consistent
        ((L.cutting p).toFun (ConcreteTime.cutYou j) x')) :
    BoundedSemilattice.Incomparable
      ((L.cutting p).toFun (ConcreteTime.cutMe j) x)
      ((L.cutting p).toFun (ConcreteTime.cutYou j) x') := by
  exact
    ⟨L.cutting_not_cutMe_le_cutYou_of_consistent_output p j x x' hyou,
      L.cutting_not_cutYou_le_cutMe_of_consistent_output p j x x' hcut⟩

/-- Definition 7.7(2)(a): every component of a located semilattice with Cut
carries a separating, monotone cutting attestation `CuttingPoset ⇸ Time_p`. -/
theorem alternativeWithCut_has_paper_cutting_attestation
    (L : AlternativeLocatedSemilatticeWithCut) (p : L.toLocated.Ctrl) :
    ∃ A : Attestation ConcreteTime (L.toLocated.timeAt p),
      A.Separating ∧ A.Monotone := by
  exact ⟨L.cutting p, L.cutting_separating p, L.cutting_attestation_monotone p⟩

end ConsistentHistories.AlternativePresentation
