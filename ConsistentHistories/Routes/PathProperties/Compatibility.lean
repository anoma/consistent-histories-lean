import ConsistentHistories.Routes.PathProperties.Matryoshka

/-!
Paper section 5.5: Compatible and incompatible cuts.

-/

namespace ConsistentHistories.Routes.PathProperties.Compatibility

open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Routes.Paths.Circuits
open ConsistentHistories.Foundation.Paths.InitialPrefixes
open ConsistentHistories.Routes.PathProperties.InactiveCuts

universe u v

/--
Derivation-level core of Lemma 5.5.1: after the two right-compatible final Cut
steps, each center `j`, `j'` is inactive (clause 1), each lower endpoint `i`,
`i'` is active (clause 2, cut endpoints active), and the center contradiction
`Π₁[j] 🗲 Π'₁[j]` propagates to the lower endpoints (clause 4).
-/
theorem final_cut_pair {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T T' : Prepath Time}
    (leftDeriv : Derivation Time T) (rightDeriv : Derivation Time T')
    {i j k : T.Index} {i' j' k' : T'.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    (hij' : i'.val < j'.val) (hjk' : j'.val < k'.val)
    {ti tj tk ti' tj' tk' : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk))
    (hk' : T'.get k' = ⋉ (T'.paperIndex j') tk')
    (hj' : T'.get j' =
      ⋊ (T'.paperIndex i') (tj' # (⋉ (T'.paperIndex j') tk')))
    (hi' : T'.get i' =
      ti' # (⋊ (T'.paperIndex i')
        (tj' # (⋉ (T'.paperIndex j') tk'))))
    (hconsistent' : ConsistentTime (↱ (T'.paperIndex i') tk'))
    (hctrlLower :
      controller (T.get i) = controller (T'.get i'))
    (hcontrCenter : (T.get j) 🗲 (T'.get j')) :
    (Derivation.cut leftDeriv hij hjk hk hj hi hconsistent).Inactive j ∧
    (Derivation.cut rightDeriv hij' hjk' hk' hj' hi' hconsistent').Inactive j' ∧
    (Derivation.cut leftDeriv hij hjk hk hj hi hconsistent).Active i ∧
    (Derivation.cut rightDeriv hij' hjk' hk' hj' hi' hconsistent').Active i' ∧
    ((Derivation.root (Derivation.cut leftDeriv hij hjk hk hj hi hconsistent)).get i) 🗲 ((Derivation.root
        (Derivation.cut rightDeriv hij' hjk' hk' hj' hi' hconsistent')).get i') := by
  let leftCut := Derivation.cut leftDeriv hij hjk hk hj hi hconsistent
  let rightCut := Derivation.cut rightDeriv hij' hjk' hk' hj' hi' hconsistent'
  have hleftCenterInactive : leftCut.Inactive j :=
    final_cut_implies_inactive leftDeriv hij hjk hk hj hi hconsistent
  have hrightCenterInactive : rightCut.Inactive j' :=
    final_cut_implies_inactive rightDeriv hij' hjk' hk' hj' hi' hconsistent'
  have hleftLowerActive : leftCut.Active i :=
    (final_cut_endpoints_active leftDeriv hij hjk hk hj hi hconsistent).2
  have hrightLowerActive : rightCut.Active i' :=
    (final_cut_endpoints_active rightDeriv hij' hjk' hk' hj' hi' hconsistent').2
  have hi_ne_k : i ≠ k := by
    intro h
    cases h
    exact Nat.lt_irrefl i.val (Nat.lt_trans hij hjk)
  have hi'_ne_k' : i' ≠ k' := by
    intro h
    cases h
    exact Nat.lt_irrefl i'.val (Nat.lt_trans hij' hjk')
  have hleftLowerShape :
      (Derivation.root leftCut).get i = ti # (T.get j) := by
    simp [leftCut, Derivation.root, Prepath.replace_get_ne T hi_ne_k, hi, hj]
  have hrightLowerShape :
      (Derivation.root rightCut).get i' = ti' # (T'.get j') := by
    simp [rightCut, Derivation.root, Prepath.replace_get_ne T' hi'_ne_k', hi', hj']
  have hleftCtrlTi :
      controller (T.get i) = controller ti := by
    calc
      controller (T.get i) =
          controller
            (ti # (⋊ (T.paperIndex i)
              (tj # (⋉ (T.paperIndex j) tk)))) := by
            rw [hi]
      _ = controller ti :=
            controller_preserving ti
              (⋊ (T.paperIndex i)
                (tj # (⋉ (T.paperIndex j) tk)))
  have hrightCtrlTi :
      controller (T'.get i') = controller ti' := by
    calc
      controller (T'.get i') =
          controller
            (ti' # (⋊ (T'.paperIndex i')
              (tj' # (⋉ (T'.paperIndex j') tk')))) := by
            rw [hi']
      _ = controller ti' :=
            controller_preserving ti'
              (⋊ (T'.paperIndex i')
                (tj' # (⋉ (T'.paperIndex j') tk')))
  have hctrlTi : controller ti = controller ti' :=
    hleftCtrlTi.symm.trans (hctrlLower.trans hrightCtrlTi)
  have hcontrLower :
      (ti # (T.get j)) 🗲 (ti' # (T'.get j')) :=
    contradiction_preserving hctrlTi hcontrCenter.1 hcontrCenter
  exact
    ⟨hleftCenterInactive, hrightCenterInactive, hleftLowerActive,
      hrightLowerActive, by
        simpa [leftCut, rightCut, hleftLowerShape, hrightLowerShape] using hcontrLower⟩

/--
Lemma 5.5.1(3): if the pre-Cut circuit has indexes `i < j < k`, then `i` and
`j` lie strictly before the last index (`i, j < length`), so by Definition
4.3.1(1) the left and right controllers agree at both `i` and `j`.
-/
theorem cutPair_pre_cut_indices_before_last_and_controller_eq
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {i j k : cd.Index} (hij : i.val < j.val) (hjk : j.val < k.val) :
    cd.circuit.left.1.paperIndex i < cd.circuit.length ∧
      cd.circuit.left.1.paperIndex j < cd.circuit.length ∧
      controller (cd.leftTime j) = controller (cd.rightTime j) ∧
      controller (cd.leftTime i) = controller (cd.rightTime i) := by
  have hi_before : cd.circuit.left.1.paperIndex i < cd.circuit.length := by
    exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hij) j.isLt
  have hj_before : cd.circuit.left.1.paperIndex j < cd.circuit.length := by
    exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hjk) k.isLt
  exact
    ⟨hi_before, hj_before, cd.controller_eq_before_last j hj_before,
      cd.controller_eq_before_last i hi_before⟩

/--
Lemma 5.5.1(3) after the Cut pair: following the synchronized right-compatible
Cut step, the center `j` and lower endpoint `i` still lie strictly before the
last index, so by Definition 4.3.1(1) the left and right controllers agree at
both, because `cutPair` preserves the circuit's controller equalities below the
final index.
-/
theorem cutPair_post_cut_indices_before_last_and_controller_eq
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
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
        (↱ (cd.circuit.right.1.paperIndex i') tk')) :
    let cutCd :=
      cd.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
        hconsistent'
    cutCd.circuit.left.1.paperIndex i < cutCd.circuit.length ∧
      cutCd.circuit.left.1.paperIndex j < cutCd.circuit.length ∧
      controller (cutCd.leftTime j) =
        controller (cutCd.rightTime j) ∧
      controller (cutCd.leftTime i) =
        controller (cutCd.rightTime i) := by
  let cutCd :=
    cd.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
      hconsistent'
  have hpre :
      cd.circuit.left.1.paperIndex i < cd.circuit.length ∧
        cd.circuit.left.1.paperIndex j < cd.circuit.length ∧
        controller (cd.leftTime j) =
          controller (cd.rightTime j) ∧
        controller (cd.leftTime i) =
          controller (cd.rightTime i) :=
    cutPair_pre_cut_indices_before_last_and_controller_eq cd hij hjk
  have hi_before : cutCd.circuit.left.1.paperIndex i < cutCd.circuit.length := by
    simpa [cutCd, CircuitDerivation.cutPair, Prepath.replace_paperIndex] using hpre.1
  have hj_before : cutCd.circuit.left.1.paperIndex j < cutCd.circuit.length := by
    simpa [cutCd, CircuitDerivation.cutPair, Prepath.replace_paperIndex] using hpre.2.1
  exact
    ⟨hi_before, hj_before, cutCd.controller_eq_before_last j hj_before,
      cutCd.controller_eq_before_last i hi_before⟩

/--
Circuit-level inactive, doubly-active, and lower-inconsistent component of
Lemma 5.5.1: a right-compatible pair
of final Cut steps propagates a center contradiction to an active-inconsistent
lower index in the circuit derivation after the two Cut steps.
-/
theorem cutPair_lower_activeInconsistentIndex
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
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
    (hlowerRight : i' = cd.rightIndex i)
    (hcontrCenter : (cd.leftTime j) 🗲 (cd.rightTime j)) :
    let cutCd :=
      cd.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
        hconsistent'
    cutCd.Inactive j ∧ cutCd.DoublyActive i ∧
      cutCd.ActiveInconsistentIndex i := by
  let cutCd :=
    cd.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
      hconsistent'
  have hctrlLower :
      controller (cd.circuit.left.1.get i) =
        controller (cd.circuit.right.1.get i') := by
    have hi_before : cd.circuit.left.1.paperIndex i < cd.circuit.length := by
      exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hij) j.isLt
    have hctrl := cd.circuit.controller_eq_before_last i hi_before
    rw [hlowerRight]
    simpa [CircuitDerivation.rightIndex] using hctrl
  have hcontrCenter' :
      (cd.circuit.left.1.get j) 🗲 (cd.circuit.right.1.get j') := by
    rw [hcenterRight]
    simpa [CircuitDerivation.leftTime, CircuitDerivation.rightTime]
      using hcontrCenter
  have hcore :=
    final_cut_pair cd.leftDerivation cd.rightDerivation hij hjk hij' hjk'
      hk hj hi hconsistent hk' hj' hi' hconsistent' hctrlLower hcontrCenter'
  have hrightIndex_center : cutCd.rightIndex j = j' := by
    rw [hcenterRight]
    rfl
  have hrightIndex_lower : cutCd.rightIndex i = i' := by
    rw [hlowerRight]
    rfl
  have hinactive : cutCd.Inactive j := by
    constructor
    · simpa [cutCd, CircuitDerivation.cutPair] using hcore.1
    · rw [hrightIndex_center]
      simpa [cutCd, CircuitDerivation.cutPair] using hcore.2.1
  have hdoublyActive : cutCd.DoublyActive i := by
    constructor
    · simpa [cutCd, CircuitDerivation.cutPair] using hcore.2.2.1
    · rw [hrightIndex_lower]
      simpa [cutCd, CircuitDerivation.cutPair] using hcore.2.2.2.1
  have hcontrLower :
      (cutCd.leftTime i) 🗲 (cutCd.rightTime i) := by
    rw [CircuitDerivation.rightTime, hrightIndex_lower]
    simpa [cutCd, CircuitDerivation.cutPair, CircuitDerivation.leftTime]
      using hcore.2.2.2.2
  exact
    ⟨hinactive, hdoublyActive,
      cutCd.activeInconsistentIndex_of_doublyActive_contradicts_final
        hdoublyActive hcontrLower⟩

/--
Full conclusion of Lemma 5.5.1 at the circuit level: a synchronized
right-compatible final Cut pair centered at a doubly-active index `j` whose two
sides contradict makes `j` inactive (clause 1), makes the common lower endpoint
`i` doubly active (clause 2), places `i` and `j` before the last index so their
controllers agree across the circuit (clause 3), and makes `i` active
inconsistent (clauses 2 and 4).
-/
theorem cutPair_doublyActive_cut_from_center_to_lower
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
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
    (hlowerRight : i' = cd.rightIndex i)
    (hcontrCenter : (cd.leftTime j) 🗲 (cd.rightTime j)) :
    let cutCd :=
      cd.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
        hconsistent'
    cutCd.Inactive j ∧ cutCd.DoublyActive i ∧
      cd.circuit.left.1.paperIndex i < cd.circuit.length ∧
      cd.circuit.left.1.paperIndex j < cd.circuit.length ∧
      controller (cd.leftTime j) = controller (cd.rightTime j) ∧
      controller (cd.leftTime i) = controller (cd.rightTime i) ∧
      cutCd.ActiveInconsistentIndex i := by
  let cutCd :=
    cd.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
      hconsistent'
  have hstatus :
      cutCd.Inactive j ∧ cutCd.DoublyActive i ∧
        cutCd.ActiveInconsistentIndex i := by
    exact
      cutPair_lower_activeInconsistentIndex cd hij hjk hij' hjk' hk hj hi
        hconsistent hk' hj' hi' hconsistent' hcenterRight hlowerRight
        hcontrCenter
  have hcontrollers :
      cd.circuit.left.1.paperIndex i < cd.circuit.length ∧
        cd.circuit.left.1.paperIndex j < cd.circuit.length ∧
        controller (cd.leftTime j) = controller (cd.rightTime j) ∧
        controller (cd.leftTime i) = controller (cd.rightTime i) :=
    cutPair_pre_cut_indices_before_last_and_controller_eq cd hij hjk
  exact
    ⟨hstatus.1, hstatus.2.1, hcontrollers.1, hcontrollers.2.1,
      hcontrollers.2.2.1, hcontrollers.2.2.2, hstatus.2.2⟩

/--
Initial-prefix transport form of `cutPair_lower_activeInconsistentIndex`: if
the synchronized Cut-pair derivation is an initial prefix of a final circuit
derivation, then its lower endpoint is inconsistent in the final derivation.
-/
theorem cutPair_lower_inconsistentIndex_of_initialPrefix
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {pref cd : CircuitDerivation Time}
    {i j k : pref.Index} {i' j' k' : pref.circuit.right.1.Index}
    (hij : i.val < j.val) (hjk : j.val < k.val)
    (hij' : i'.val < j'.val) (hjk' : j'.val < k'.val)
    {ti tj tk ti' tj' tk' : Time}
    (hk : pref.circuit.left.1.get k = ⋉ (pref.circuit.left.1.paperIndex j) tk)
    (hj : pref.circuit.left.1.get j =
      ⋊ (pref.circuit.left.1.paperIndex i)
        (tj # (⋉ (pref.circuit.left.1.paperIndex j) tk)))
    (hi : pref.circuit.left.1.get i =
      ti # (⋊ (pref.circuit.left.1.paperIndex i)
          (tj # (⋉ (pref.circuit.left.1.paperIndex j) tk))))
    (hconsistent :
      ConsistentTime
        (↱ (pref.circuit.left.1.paperIndex i) tk))
    (hk' : pref.circuit.right.1.get k' =
      ⋉ (pref.circuit.right.1.paperIndex j') tk')
    (hj' : pref.circuit.right.1.get j' =
      ⋊ (pref.circuit.right.1.paperIndex i')
        (tj' # (⋉ (pref.circuit.right.1.paperIndex j') tk')))
    (hi' : pref.circuit.right.1.get i' =
      ti' # (⋊ (pref.circuit.right.1.paperIndex i')
          (tj' # (⋉ (pref.circuit.right.1.paperIndex j') tk'))))
    (hconsistent' :
      ConsistentTime
        (↱ (pref.circuit.right.1.paperIndex i') tk'))
    (hcutPrefix :
      (pref.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
        hconsistent').IsInitialPrefix cd)
    (hcenterRight : j' = pref.rightIndex j)
    (hlowerRight : i' = pref.rightIndex i)
    (hcontrCenter : (pref.leftTime j) 🗲 (pref.rightTime j)) :
    cd.InconsistentIndex (Fin.cast (InitialPrefix.length_eq hcutPrefix.1) i) := by
  let cutPref :=
    pref.cutPair hij hjk hij' hjk' hk hj hi hconsistent hk' hj' hi'
      hconsistent'
  have hactiveInconsistent :
      cutPref.ActiveInconsistentIndex i := by
    exact
      (cutPair_lower_activeInconsistentIndex pref hij hjk hij' hjk' hk hj hi
        hconsistent hk' hj' hi' hconsistent' hcenterRight hlowerRight
        hcontrCenter).2.2
  exact
    CircuitDerivation.inconsistentIndex_of_initialPrefix_activeInconsistentIndex_cast
      hcutPrefix i hactiveInconsistent

/--
Cut-prefix form: synchronized Cut-prefix data with a center
contradiction gives a strictly lower inconsistent index in the final circuit.
-/
theorem cutPrefix_pair_lower_inconsistent_of_center_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    {leftCutK rightCutK cutI : Nat}
    (leftData :
      CutPrefixData cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center) cutI)
    (rightData :
      CutPrefixData cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center) cutI)
    (hcontrCenter :
      (leftData.base.get leftData.idxJ) 🗲 (rightData.base.get rightData.idxJ)) :
    ∃ lower : cd.Index, lower.val < center.val ∧ cd.InconsistentIndex lower := by
  let leftCutDeriv :=
    Derivation.cut leftData.baseDeriv leftData.hij leftData.hjk leftData.hk
      leftData.hj leftData.hi leftData.hconsistent
  let rightCutDeriv :=
    Derivation.cut rightData.baseDeriv rightData.hij rightData.hjk rightData.hk
      rightData.hj rightData.hi rightData.hconsistent
  have hleftBaseToCut : InitialPrefix leftData.baseDeriv leftCutDeriv := by
    exact
      InitialPrefix.cut leftData.baseDeriv
        (InitialPrefix.refl leftData.baseDeriv) leftData.hij leftData.hjk
        leftData.hk leftData.hj leftData.hi leftData.hconsistent
  have hrightBaseToCut : InitialPrefix rightData.baseDeriv rightCutDeriv := by
    exact
      InitialPrefix.cut rightData.baseDeriv
        (InitialPrefix.refl rightData.baseDeriv) rightData.hij rightData.hjk
        rightData.hk rightData.hj rightData.hi rightData.hconsistent
  have hleftBaseToFinal : InitialPrefix leftData.baseDeriv cd.leftDerivation :=
    InitialPrefix.trans hleftBaseToCut leftData.hprefix
  have hrightBaseToFinal : InitialPrefix rightData.baseDeriv cd.rightDerivation :=
    InitialPrefix.trans hrightBaseToCut rightData.hprefix
  let preCd :=
    cd.initialPrefixDerivation leftData.baseDeriv rightData.baseDeriv
      hleftBaseToFinal hrightBaseToFinal
  have hcenterPaper :
      leftData.base.paperIndex leftData.idxJ =
        rightData.base.paperIndex rightData.idxJ := by
    exact leftData.cutJ_eq.symm.trans rightData.cutJ_eq
  have hlowerPaper :
      leftData.base.paperIndex leftData.idxI =
        rightData.base.paperIndex rightData.idxI := by
    exact leftData.cutI_eq.symm.trans rightData.cutI_eq
  have hcenterRight : rightData.idxJ = preCd.rightIndex leftData.idxJ := by
    apply Fin.ext
    exact Nat.succ.inj (by
      simpa [preCd, CircuitDerivation.rightIndex, Prepath.paperIndex] using
        hcenterPaper.symm)
  have hlowerRight : rightData.idxI = preCd.rightIndex leftData.idxI := by
    apply Fin.ext
    exact Nat.succ.inj (by
      simpa [preCd, CircuitDerivation.rightIndex, Prepath.paperIndex] using
        hlowerPaper.symm)
  have hcutPrefix :
      (preCd.cutPair leftData.hij leftData.hjk rightData.hij rightData.hjk
        leftData.hk leftData.hj leftData.hi leftData.hconsistent
        rightData.hk rightData.hj rightData.hi rightData.hconsistent).IsInitialPrefix cd := by
    exact ⟨leftData.hprefix, rightData.hprefix⟩
  have hcontrCenterPre :
      (preCd.leftTime leftData.idxJ) 🗲 (preCd.rightTime leftData.idxJ) := by
    rw [CircuitDerivation.rightTime, ← hcenterRight]
    simpa [preCd, CircuitDerivation.leftTime, CircuitDerivation.rightTime]
      using hcontrCenter
  let lower : cd.Index :=
    Fin.cast (InitialPrefix.length_eq leftData.hprefix) leftData.idxI
  have hlower_center : lower.val < center.val := by
    have hcenter_val : center.val = leftData.idxJ.val := by
      exact Nat.succ.inj (by
        simpa [Prepath.paperIndex] using leftData.cutJ_eq)
    simpa [lower, hcenter_val] using leftData.hij
  have hinconsistent_lower : cd.InconsistentIndex lower := by
    simpa [lower] using
      cutPair_lower_inconsistentIndex_of_initialPrefix (pref := preCd) (cd := cd)
        leftData.hij leftData.hjk rightData.hij rightData.hjk leftData.hk
        leftData.hj leftData.hi leftData.hconsistent rightData.hk
        rightData.hj rightData.hi rightData.hconsistent hcutPrefix
        hcenterRight hlowerRight hcontrCenterPre
  exact ⟨lower, hlower_center, hinconsistent_lower⟩

/--
If an inconsistent-prefix witness for the Cut center lies before both pre-Cut
bases, monotonicity of the times along an initial prefix transports its center
contradiction to those bases. This is the formal version of the step in the
inactive case of Proposition 5.5.2's proof where the greatest active initial
prefixes `Π*`, `Π'*` (which precede the two Cuts) inherit the inconsistency
contradiction `Π*[j] 🗲 Π'*[j]`.
-/
theorem cutPrefix_center_contradiction_of_witness_prefixes
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    {leftCutK rightCutK cutI : Nat}
    (leftData :
      CutPrefixData cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center) cutI)
    (rightData :
      CutPrefixData cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center) cutI)
    {pref : CircuitDerivation Time} (hpref : pref.IsInitialPrefix cd)
    (hleftToBase : InitialPrefix pref.leftDerivation leftData.baseDeriv)
    (hrightToBase : InitialPrefix pref.rightDerivation rightData.baseDeriv)
    (hcontr :
      (pref.leftTime (pref.prefixIndex hpref center)) 🗲 (pref.rightTime (pref.prefixIndex hpref center))) :
    (leftData.base.get leftData.idxJ) 🗲 (rightData.base.get rightData.idxJ) := by
  let prefCenter : pref.Index := pref.prefixIndex hpref center
  have hleftPaper :
      pref.circuit.left.1.paperIndex prefCenter =
        leftData.base.paperIndex leftData.idxJ := by
    calc
      pref.circuit.left.1.paperIndex prefCenter =
          cd.circuit.left.1.paperIndex center := by
            simpa [prefCenter] using pref.prefixIndex_paperIndex hpref center
      _ = leftData.base.paperIndex leftData.idxJ := leftData.cutJ_eq
  have hleftCast :
      Fin.cast (InitialPrefix.length_eq hleftToBase) prefCenter =
        leftData.idxJ := by
    apply Fin.ext
    exact Nat.succ.inj (by
      simpa [Prepath.paperIndex] using hleftPaper)
  have hrightPaper :
      pref.circuit.right.1.paperIndex (pref.rightIndex prefCenter) =
        rightData.base.paperIndex rightData.idxJ := by
    calc
      pref.circuit.right.1.paperIndex (pref.rightIndex prefCenter) =
          pref.circuit.left.1.paperIndex prefCenter := by
            exact pref.rightIndex_paperIndex prefCenter
      _ = cd.circuit.left.1.paperIndex center := by
            simpa [prefCenter] using pref.prefixIndex_paperIndex hpref center
      _ = rightData.base.paperIndex rightData.idxJ := rightData.cutJ_eq
  have hrightCast :
      Fin.cast (InitialPrefix.length_eq hrightToBase) (pref.rightIndex prefCenter) =
        rightData.idxJ := by
    apply Fin.ext
    exact Nat.succ.inj (by
      simpa [Prepath.paperIndex] using hrightPaper)
  have hleftLe :
      (pref.leftTime prefCenter) ≼ (leftData.base.get leftData.idxJ) := by
    have hle := InitialPrefix.times_increase hleftToBase prefCenter
    simpa [CircuitDerivation.leftTime, hleftCast] using hle
  have hrightLe :
      (pref.rightTime prefCenter) ≼ (rightData.base.get rightData.idxJ) := by
    have hle := InitialPrefix.times_increase hrightToBase (pref.rightIndex prefCenter)
    simpa [CircuitDerivation.rightTime, hrightCast] using hle
  exact contradicts_of_le_both hleftLe hrightLe (by
    simpa [prefCenter] using hcontr)

/--
Once a Cut centered at `j` occurs in an initial prefix, `j` is inactive in
every later derivation extending that prefix (Lemma 5.3.1, cut centers become
inactive). This is the single-side inactivity fact underlying the inactive case
of Proposition 5.5.2.
-/
theorem final_cut_center_inactive_of_initialPrefix
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T U : Prepath Time}
    {baseDeriv : Derivation Time T} {laterDeriv : Derivation Time U}
    {i j k : T.Index} (hij : i.val < j.val) (hjk : j.val < k.val)
    {ti tj tk : Time}
    (hk : T.get k = ⋉ (T.paperIndex j) tk)
    (hj : T.get j =
      ⋊ (T.paperIndex i) (tj # (⋉ (T.paperIndex j) tk)))
    (hi : T.get i =
      ti # (⋊ (T.paperIndex i)
        (tj # (⋉ (T.paperIndex j) tk))))
    (hconsistent : ConsistentTime (↱ (T.paperIndex i) tk))
    (hprefix :
      InitialPrefix (Derivation.cut baseDeriv hij hjk hk hj hi hconsistent)
        laterDeriv) :
    laterDeriv.Inactive (Fin.cast hprefix.length_eq j) := by
  exact inactive_of_initialPrefix hprefix
    (final_cut_implies_inactive baseDeriv hij hjk hk hj hi hconsistent)

/--
If the left and right derivations each end an initial prefix with a Cut centered
at the same circuit index `center`, then `center` is inactive on both sides, so
it is inactive in the final circuit derivation (Definition 4.3.1(4d), via Lemma
5.3.1 on each side).
-/
theorem cutPrefixData_pair_center_inactive
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    {leftCutK rightCutK cutI : Nat}
    (leftData :
      CutPrefixData cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center) cutI)
    (rightData :
      CutPrefixData cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center) cutI) :
    cd.Inactive center := by
  constructor
  · exact cutPrefixData_center_inactive leftData rfl
  · exact cutPrefixData_center_inactive rightData
      (by rw [cd.rightIndex_paperIndex center])

/--
Inactive case of Proposition 5.5.2: an initial prefix at which the synchronized
Cut center is doubly active lies before both selected pre-Cut bases (the greatest
active initial prefixes precede the Cuts that inactivated the center).
-/
theorem cutPrefixData_pair_active_prefixes_before_bases
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    {leftCutK rightCutK cutI : Nat}
    (leftData :
      CutPrefixData cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center) cutI)
    (rightData :
      CutPrefixData cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center) cutI)
    {pref : CircuitDerivation Time} (hpref : pref.IsInitialPrefix cd)
    (hactive : pref.DoublyActive (pref.prefixIndex hpref center)) :
    InitialPrefix pref.leftDerivation leftData.baseDeriv ∧
      InitialPrefix pref.rightDerivation rightData.baseDeriv := by
  constructor
  · exact cutPrefixData_active_prefix_before_base leftData hpref.1
      (center := center) rfl hactive.1
  · have hrightIdx :
        pref.rightIndex (pref.prefixIndex hpref center) =
          Fin.cast (InitialPrefix.length_eq hpref.2).symm (cd.rightIndex center) := by
      ext
      rfl
    exact cutPrefixData_active_prefix_before_base rightData hpref.2
      (center := cd.rightIndex center)
      (by exact (cd.rightIndex_paperIndex center).symm)
      (by simpa [hrightIdx] using hactive.2)

/--
Active-index case of Proposition 5.5.2.
-/
theorem right_consistent_inconsistent_active_case {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index}
    (hcompat : cd.RightCompatibleUpTo j)
    (hactive : cd.Active j)
    (hinconsistent : cd.InconsistentIndex j) :
    ∃ l : cd.Index,
      l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact ⟨j, Nat.le_refl j.val, hcompat, ⟨hactive, hinconsistent⟩⟩

/-- Lean-indexed active case. -/
theorem right_consistent_inconsistent_active_case_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index}
    (hcompat : cd.RightCompatibleUpTo j)
    (hactive : cd.Active j)
    (hinconsistent : cd.InconsistentIndex j) :
    ∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  rcases right_consistent_inconsistent_active_case cd hcompat hactive hinconsistent with
    ⟨l, hle, hcompat_l, hactiveInconsistent⟩
  exact ⟨l, Nat.succ_le_succ hle, hcompat_l, hactiveInconsistent⟩

/--
Least-index active case of Proposition 5.5.2.
-/
theorem right_consistent_inconsistent_least_active_case {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hleast : cd.LeastInconsistentAtOrBelow bound least)
    (hactive : cd.Active least) :
    ∃ l : cd.Index,
      l.val ≤ bound.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  rcases hleast with ⟨hle_bound, hinconsistent, _hminimal⟩
  exact
    ⟨least, hle_bound, cd.rightCompatibleUpTo_mono hcompat hle_bound,
      ⟨hactive, hinconsistent⟩⟩

/-- Lean-indexed least-index active case. -/
theorem right_consistent_inconsistent_least_active_case_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound least : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hleast : cd.LeastInconsistentAtOrBelow bound least)
    (hactive : cd.Active least) :
    ∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex bound ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  rcases right_consistent_inconsistent_least_active_case cd hcompat hleast hactive with
    ⟨l, hle, hcompat_l, hactiveInconsistent⟩
  exact ⟨l, Nat.succ_le_succ hle, hcompat_l, hactiveInconsistent⟩

/--
Case split after choosing the least inconsistent index in Proposition 5.5.2.
-/
theorem right_consistent_inconsistent_least_case_split {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound) :
    (∃ l : cd.Index,
      l.val ≤ bound.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) ∨
    (∃ least : cd.Index,
      cd.LeastInconsistentAtOrBelow bound least ∧ cd.Inactive least) := by
  rcases cd.exists_leastInconsistentAtOrBelow hinconsistent with ⟨least, hleast⟩
  by_cases hactive : cd.Active least
  · exact Or.inl
      (right_consistent_inconsistent_least_active_case cd hcompat hleast hactive)
  · exact Or.inr ⟨least, hleast, (cd.inactive_iff_not_active least).mpr hactive⟩

/-- Lean-indexed case split after choosing the least inconsistent index. -/
theorem right_consistent_inconsistent_least_case_split_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound) :
    (∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex bound ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) ∨
    (∃ least : cd.Index,
      cd.LeastInconsistentAtOrBelow bound least ∧ cd.Inactive least) := by
  rcases right_consistent_inconsistent_least_case_split cd hcompat hinconsistent with
    hdone | hinactiveBranch
  · rcases hdone with ⟨l, hle, hcompat_l, hactiveInconsistent⟩
    exact Or.inl ⟨l, Nat.succ_le_succ hle, hcompat_l, hactiveInconsistent⟩
  · exact Or.inr hinactiveBranch

/--
Inactive branch setup: an inactive center in a
right-compatible range has Cut instances on both sides with the same lower
paper index.
-/
theorem inactive_rightCompatible_contains_cut_pair {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center) :
    ∃ cutI : Nat,
      (∃ cutUpper cutLower : cd.circuit.left.1.Index,
        cutLower.val < center.val ∧ center.val < cutUpper.val ∧
        ContainsCut cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
          (cd.circuit.left.1.paperIndex center) cutI) ∧
      (∃ cutUpper cutLower : cd.circuit.right.1.Index,
        cutLower.val < (cd.rightIndex center).val ∧
        (cd.rightIndex center).val < cutUpper.val ∧
        ContainsCut cd.rightDerivation (cd.circuit.right.1.paperIndex cutUpper)
          (cd.circuit.right.1.paperIndex (cd.rightIndex center)) cutI) := by
  rcases hinactive with ⟨hleftInactive, hrightInactive⟩
  rcases inactive_implies_containsCut_center cd.leftDerivation hleftInactive with
    ⟨leftUpper, leftLower, hleftLower_center, hcenter_leftUpper, hleftCut⟩
  rcases inactive_implies_containsCut_center cd.rightDerivation hrightInactive with
    ⟨rightUpper, rightLower, hrightLower_center, hcenter_rightUpper, hrightCut⟩
  have hrightCutCompat :
      ContainsCut cd.rightDerivation (cd.circuit.right.1.paperIndex rightUpper)
        (cd.circuit.left.1.paperIndex center) (cd.circuit.right.1.paperIndex rightLower) := by
    simpa [cd.rightIndex_paperIndex center] using hrightCut
  have hlower_eq :
      cd.circuit.left.1.paperIndex leftLower =
        cd.circuit.right.1.paperIndex rightLower :=
    cd.rightCompatibleUpTo_cutLower_eq hcompat (Nat.le_refl center.val)
      hleftCut hrightCutCompat
  exact
    ⟨cd.circuit.left.1.paperIndex leftLower,
      ⟨leftUpper, leftLower, hleftLower_center, hcenter_leftUpper, hleftCut⟩,
      ⟨rightUpper, rightLower, hrightLower_center, hcenter_rightUpper, by
        simpa [hlower_eq] using hrightCut⟩⟩

/-- Lean-indexed inactive right-compatible Cut occurrence data. -/
theorem inactive_rightCompatible_contains_cut_pair_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center) :
    ∃ cutI : Nat,
      (∃ cutUpper cutLower : cd.circuit.left.1.Index,
        cd.circuit.left.1.paperIndex cutLower <
          cd.circuit.left.1.paperIndex center ∧
        cd.circuit.left.1.paperIndex center <
          cd.circuit.left.1.paperIndex cutUpper ∧
        ContainsCut cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
          (cd.circuit.left.1.paperIndex center) cutI) ∧
      (∃ cutUpper cutLower : cd.circuit.right.1.Index,
        cd.circuit.right.1.paperIndex cutLower <
          cd.circuit.right.1.paperIndex (cd.rightIndex center) ∧
        cd.circuit.right.1.paperIndex (cd.rightIndex center) <
          cd.circuit.right.1.paperIndex cutUpper ∧
        ContainsCut cd.rightDerivation (cd.circuit.right.1.paperIndex cutUpper)
          (cd.circuit.right.1.paperIndex (cd.rightIndex center)) cutI) := by
  rcases inactive_rightCompatible_contains_cut_pair cd hcompat hinactive with
    ⟨cutI, hleft, hright⟩
  rcases hleft with
    ⟨leftUpper, leftLower, hleftLower_center, hcenter_leftUpper, hleftCut⟩
  rcases hright with
    ⟨rightUpper, rightLower, hrightLower_center, hcenter_rightUpper, hrightCut⟩
  exact
    ⟨cutI,
      ⟨leftUpper, leftLower, Nat.succ_lt_succ hleftLower_center,
        Nat.succ_lt_succ hcenter_leftUpper, hleftCut⟩,
      ⟨rightUpper, rightLower, Nat.succ_lt_succ hrightLower_center,
        Nat.succ_lt_succ hcenter_rightUpper, hrightCut⟩⟩

/--
Inactive right-compatible branch data with both Cut occurrence and
prefix-ending-Cut witnesses.
-/
theorem inactive_rightCompatible_cutPrefix_pair {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center) :
    ∃ cutI : Nat,
      (∃ cutUpper cutLower : cd.circuit.left.1.Index,
        cutLower.val < center.val ∧ center.val < cutUpper.val ∧
        ContainsCut cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
          (cd.circuit.left.1.paperIndex center) cutI ∧
        CutPrefixWitness cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
          (cd.circuit.left.1.paperIndex center) cutI) ∧
      (∃ cutUpper cutLower : cd.circuit.right.1.Index,
        cutLower.val < (cd.rightIndex center).val ∧
        (cd.rightIndex center).val < cutUpper.val ∧
        ContainsCut cd.rightDerivation (cd.circuit.right.1.paperIndex cutUpper)
          (cd.circuit.right.1.paperIndex (cd.rightIndex center)) cutI ∧
        CutPrefixWitness cd.rightDerivation (cd.circuit.right.1.paperIndex cutUpper)
          (cd.circuit.right.1.paperIndex (cd.rightIndex center)) cutI) := by
  rcases inactive_rightCompatible_contains_cut_pair cd hcompat hinactive with
    ⟨cutI, hleft, hright⟩
  rcases hleft with
    ⟨leftUpper, leftLower, hleftLower_center, hcenter_leftUpper, hleftCut⟩
  rcases hright with
    ⟨rightUpper, rightLower, hrightLower_center, hcenter_rightUpper, hrightCut⟩
  exact
    ⟨cutI,
      ⟨leftUpper, leftLower, hleftLower_center, hcenter_leftUpper, hleftCut,
        containsCut_prefixWitness hleftCut⟩,
      ⟨rightUpper, rightLower, hrightLower_center, hcenter_rightUpper, hrightCut,
        containsCut_prefixWitness hrightCut⟩⟩

/-- Lean-indexed inactive right-compatible Cut-prefix data. -/
theorem inactive_rightCompatible_cutPrefix_pair_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center) :
    ∃ cutI : Nat,
      (∃ cutUpper cutLower : cd.circuit.left.1.Index,
        cd.circuit.left.1.paperIndex cutLower <
          cd.circuit.left.1.paperIndex center ∧
        cd.circuit.left.1.paperIndex center <
          cd.circuit.left.1.paperIndex cutUpper ∧
        ContainsCut cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
          (cd.circuit.left.1.paperIndex center) cutI ∧
        CutPrefixWitness cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
          (cd.circuit.left.1.paperIndex center) cutI) ∧
      (∃ cutUpper cutLower : cd.circuit.right.1.Index,
        cd.circuit.right.1.paperIndex cutLower <
          cd.circuit.right.1.paperIndex (cd.rightIndex center) ∧
        cd.circuit.right.1.paperIndex (cd.rightIndex center) <
          cd.circuit.right.1.paperIndex cutUpper ∧
        ContainsCut cd.rightDerivation (cd.circuit.right.1.paperIndex cutUpper)
          (cd.circuit.right.1.paperIndex (cd.rightIndex center)) cutI ∧
        CutPrefixWitness cd.rightDerivation (cd.circuit.right.1.paperIndex cutUpper)
          (cd.circuit.right.1.paperIndex (cd.rightIndex center)) cutI) := by
  rcases inactive_rightCompatible_cutPrefix_pair cd hcompat hinactive with
    ⟨cutI, hleft, hright⟩
  rcases hleft with
    ⟨leftUpper, leftLower, hleftLower_center, hcenter_leftUpper, hleftCut,
      hleftPrefix⟩
  rcases hright with
    ⟨rightUpper, rightLower, hrightLower_center, hcenter_rightUpper, hrightCut,
      hrightPrefix⟩
  exact
    ⟨cutI,
      ⟨leftUpper, leftLower, Nat.succ_lt_succ hleftLower_center,
        Nat.succ_lt_succ hcenter_leftUpper, hleftCut, hleftPrefix⟩,
      ⟨rightUpper, rightLower, Nat.succ_lt_succ hrightLower_center,
        Nat.succ_lt_succ hcenter_rightUpper, hrightCut, hrightPrefix⟩⟩

/--
Decomposable Cut-prefix data for the inactive branch: an
inactive right-compatible center supplies synchronized left and right
prefix-ending Cut data with the same lower paper index.
-/
theorem inactive_rightCompatible_cutPrefixData_pair
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center) :
    ∃ cutI leftCutK rightCutK : Nat,
      Nonempty
        (CutPrefixData cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center) cutI) ∧
      Nonempty
        (CutPrefixData cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center) cutI) := by
  rcases inactive_rightCompatible_contains_cut_pair cd hcompat hinactive with
    ⟨cutI, hleft, hright⟩
  rcases hleft with
    ⟨leftUpper, _leftLower, _hleftLower_center, _hcenter_leftUpper,
      hleftCut⟩
  rcases hright with
    ⟨rightUpper, _rightLower, _hrightLower_center, _hcenter_rightUpper,
      hrightCut⟩
  have hrightCut' :
      ContainsCut cd.rightDerivation
        (cd.circuit.right.1.paperIndex rightUpper)
        (cd.circuit.left.1.paperIndex center) cutI := by
    simpa [cd.rightIndex_paperIndex center] using hrightCut
  rcases containsCut_prefixData hleftCut with ⟨leftData⟩
  rcases containsCut_prefixData hrightCut' with ⟨rightData⟩
  exact
    ⟨cutI, cd.circuit.left.1.paperIndex leftUpper,
      cd.circuit.right.1.paperIndex rightUpper, ⟨leftData⟩, ⟨rightData⟩⟩

/--
Inactive case of Proposition 5.5.2: an inactive right-compatible center supplies
synchronized left and right Cut-prefix data (same lower paper index) whose two
pre-Cut centers are each active in their base derivation.
-/
theorem inactive_rightCompatible_cutPrefixData_pair_refined
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center) :
    ∃ cutI leftCutK rightCutK : Nat,
      ∃ leftData :
        CutPrefixData cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center) cutI,
      ∃ rightData :
        CutPrefixData cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center) cutI,
        leftData.baseDeriv.Active leftData.idxJ ∧
          rightData.baseDeriv.Active rightData.idxJ ∧
          cd.Inactive center := by
  rcases inactive_rightCompatible_cutPrefixData_pair cd hcompat hinactive with
    ⟨cutI, leftCutK, rightCutK, ⟨leftData⟩, ⟨rightData⟩⟩
  exact
    ⟨cutI, leftCutK, rightCutK, leftData, rightData,
      cutPrefixData_pre_cut_center_active leftData,
      cutPrefixData_pre_cut_center_active rightData, hinactive⟩

/--
Inactive case of Proposition 5.5.2: the synchronized pre-Cut prefix data form an
initial-prefix circuit derivation in which the Cut center is doubly active. This
is the pre-Cut circuit prefix whose contradiction the surrounding argument later
inherits.
-/
theorem cutPrefixData_pair_preCircuit_doublyActive
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    {leftCutK rightCutK cutI : Nat}
    (leftData :
      CutPrefixData cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center) cutI)
    (rightData :
      CutPrefixData cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center) cutI) :
    ∃ preCd : CircuitDerivation Time, ∃ hprefix : preCd.IsInitialPrefix cd,
      preCd.DoublyActive (preCd.prefixIndex hprefix center) := by
  have hleftToFinal : InitialPrefix leftData.baseDeriv cd.leftDerivation := by
    exact leftData.base_initialPrefix_final
  have hrightToFinal : InitialPrefix rightData.baseDeriv cd.rightDerivation := by
    exact rightData.base_initialPrefix_final
  let preCd :=
    cd.initialPrefixDerivation leftData.baseDeriv rightData.baseDeriv
      hleftToFinal hrightToFinal
  let hprefix : preCd.IsInitialPrefix cd :=
    cd.initialPrefixDerivation_isInitialPrefix leftData.baseDeriv
      rightData.baseDeriv hleftToFinal hrightToFinal
  let preCenter : preCd.Index := preCd.prefixIndex hprefix center
  have hleftCenter : preCenter = leftData.idxJ := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.left.1.paperIndex preCenter =
          leftData.base.paperIndex leftData.idxJ := by
      calc
        preCd.circuit.left.1.paperIndex preCenter =
            cd.circuit.left.1.paperIndex center := by
              simpa [preCenter] using preCd.prefixIndex_paperIndex hprefix center
        _ = leftData.base.paperIndex leftData.idxJ := leftData.cutJ_eq
    exact Nat.succ.inj (by simpa [preCd, preCenter, Prepath.paperIndex] using hpaper)
  have hrightCenter : preCd.rightIndex preCenter = rightData.idxJ := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preCenter) =
          rightData.base.paperIndex rightData.idxJ := by
      calc
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preCenter) =
            preCd.circuit.left.1.paperIndex preCenter := by
              exact preCd.rightIndex_paperIndex preCenter
        _ = cd.circuit.left.1.paperIndex center := by
              simpa [preCenter] using preCd.prefixIndex_paperIndex hprefix center
        _ = rightData.base.paperIndex rightData.idxJ := rightData.cutJ_eq
    exact Nat.succ.inj (by simpa [preCd, preCenter, Prepath.paperIndex] using hpaper)
  refine ⟨preCd, hprefix, ?_⟩
  constructor
  · simpa [preCd, preCenter, hleftCenter] using
      cutPrefixData_pre_cut_center_active leftData
  · simpa [preCd, preCenter, hrightCenter] using
      cutPrefixData_pre_cut_center_active rightData

/--
Inactive case of Proposition 5.5.2: synchronized pre-Cut prefix data form a
pre-Cut circuit prefix whose center is doubly active, and if that pre-Cut center
is contradictory (`Π*[j] 🗲 Π'*[j]`) then applying Lemma 5.5.1 across the two
Cuts makes the common lower endpoint inconsistent, giving the final circuit a
strictly lower inconsistent index. The center contradiction is taken as a
hypothesis here.
-/
theorem cutPrefixData_pair_lower_inconsistent_of_preCircuit_center_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    {leftCutK rightCutK cutI : Nat}
    (leftData :
      CutPrefixData cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center) cutI)
    (rightData :
      CutPrefixData cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center) cutI) :
    ∃ preCd : CircuitDerivation Time, ∃ hprefix : preCd.IsInitialPrefix cd,
      let preCenter := preCd.prefixIndex hprefix center
      preCd.DoublyActive preCenter ∧
        ((preCd.leftTime preCenter) 🗲 (preCd.rightTime preCenter) →
          ∃ lower : cd.Index, lower.val < center.val ∧ cd.InconsistentIndex lower) := by
  have hleftToFinal : InitialPrefix leftData.baseDeriv cd.leftDerivation := by
    exact leftData.base_initialPrefix_final
  have hrightToFinal : InitialPrefix rightData.baseDeriv cd.rightDerivation := by
    exact rightData.base_initialPrefix_final
  let preCd :=
    cd.initialPrefixDerivation leftData.baseDeriv rightData.baseDeriv
      hleftToFinal hrightToFinal
  let hprefix : preCd.IsInitialPrefix cd :=
    cd.initialPrefixDerivation_isInitialPrefix leftData.baseDeriv
      rightData.baseDeriv hleftToFinal hrightToFinal
  let preCenter : preCd.Index := preCd.prefixIndex hprefix center
  have hleftCenter : preCenter = leftData.idxJ := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.left.1.paperIndex preCenter =
          leftData.base.paperIndex leftData.idxJ := by
      calc
        preCd.circuit.left.1.paperIndex preCenter =
            cd.circuit.left.1.paperIndex center := by
              simpa [preCenter] using preCd.prefixIndex_paperIndex hprefix center
        _ = leftData.base.paperIndex leftData.idxJ := leftData.cutJ_eq
    exact Nat.succ.inj (by simpa [preCd, preCenter, Prepath.paperIndex] using hpaper)
  have hrightCenter : preCd.rightIndex preCenter = rightData.idxJ := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preCenter) =
          rightData.base.paperIndex rightData.idxJ := by
      calc
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preCenter) =
            preCd.circuit.left.1.paperIndex preCenter := by
              exact preCd.rightIndex_paperIndex preCenter
        _ = cd.circuit.left.1.paperIndex center := by
              simpa [preCenter] using preCd.prefixIndex_paperIndex hprefix center
        _ = rightData.base.paperIndex rightData.idxJ := rightData.cutJ_eq
    exact Nat.succ.inj (by simpa [preCd, preCenter, Prepath.paperIndex] using hpaper)
  have hrightCenterLeft : preCd.rightIndex leftData.idxJ = rightData.idxJ := by
    simpa [hleftCenter] using hrightCenter
  have hdoublyActive : preCd.DoublyActive preCenter := by
    constructor
    · simpa [preCd, preCenter, hleftCenter] using
        cutPrefixData_pre_cut_center_active leftData
    · simpa [preCd, preCenter, hrightCenter] using
        cutPrefixData_pre_cut_center_active rightData
  refine ⟨preCd, hprefix, ?_⟩
  dsimp only
  refine ⟨hdoublyActive, ?_⟩
  intro hcontrPre
  have hcontrBase :
      (leftData.base.get leftData.idxJ) 🗲 (rightData.base.get rightData.idxJ) := by
    simpa [preCd, preCenter, hleftCenter, hrightCenterLeft,
      CircuitDerivation.leftTime, CircuitDerivation.rightTime] using hcontrPre
  exact cutPrefix_pair_lower_inconsistent_of_center_contradiction cd leftData
    rightData hcontrBase

/--
Inactive case of Proposition 5.5.2: from an inactive right-compatible center,
this returns the synchronized Cut-prefix data (with active pre-Cut centers) and
a pre-Cut circuit prefix in which the center is doubly active.
-/
theorem inactive_rightCompatible_preCircuit_doublyActive
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center) :
    ∃ cutI leftCutK rightCutK : Nat,
      ∃ leftData :
        CutPrefixData cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex center) cutI,
      ∃ rightData :
        CutPrefixData cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex center) cutI,
      ∃ preCd : CircuitDerivation Time, ∃ hprefix : preCd.IsInitialPrefix cd,
        leftData.baseDeriv.Active leftData.idxJ ∧
          rightData.baseDeriv.Active rightData.idxJ ∧
          preCd.DoublyActive (preCd.prefixIndex hprefix center) ∧
          cd.Inactive center := by
  rcases inactive_rightCompatible_cutPrefixData_pair_refined cd hcompat hinactive with
    ⟨cutI, leftCutK, rightCutK, leftData, rightData, hleftActive,
      hrightActive, hinactiveFinal⟩
  rcases cutPrefixData_pair_preCircuit_doublyActive cd leftData rightData with
    ⟨preCd, hprefix, hdoublyActive⟩
  exact
    ⟨cutI, leftCutK, rightCutK, leftData, rightData, preCd, hprefix,
      hleftActive, hrightActive, hdoublyActive, hinactiveFinal⟩

/--
Inactive case of Proposition 5.5.2: for an inactive right-compatible center,
this returns a pre-Cut circuit prefix whose center is doubly active together
with the implication that, if that pre-Cut center is contradictory, the final
circuit has a strictly lower inconsistent index (the index that contradicts
leastness in the proof). The center contradiction is the hypothesis of that
implication.
-/
theorem inactive_rightCompatible_lower_inconsistent_of_preCircuit_center_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center) :
    ∃ preCd : CircuitDerivation Time, ∃ hprefix : preCd.IsInitialPrefix cd,
      let preCenter := preCd.prefixIndex hprefix center
      preCd.DoublyActive preCenter ∧
        ((preCd.leftTime preCenter) 🗲 (preCd.rightTime preCenter) →
          ∃ lower : cd.Index, lower.val < center.val ∧ cd.InconsistentIndex lower) := by
  rcases inactive_rightCompatible_cutPrefixData_pair_refined cd hcompat hinactive with
    ⟨_cutI, _leftCutK, _rightCutK, leftData, rightData, _hleftActive,
      _hrightActive, _hinactiveFinal⟩
  rcases cutPrefixData_pair_lower_inconsistent_of_preCircuit_center_contradiction
      cd leftData rightData with
    ⟨preCd, hprefix, hpre⟩
  exact ⟨preCd, hprefix, hpre⟩

/--
Inactive case of Proposition 5.5.2: given that the pre-Cut center times of the
synchronized right-compatible Cut prefixes contradict, this produces the
strictly lower inconsistent index that contradicts leastness of the least
inconsistent index.
-/
theorem inactive_rightCompatible_lower_inconsistent_of_cutPrefix_center_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center)
    (hcontrCutPrefixes :
      ∀ {leftCutK rightCutK cutI : Nat},
        (leftData :
          CutPrefixData cd.leftDerivation leftCutK
            (cd.circuit.left.1.paperIndex center) cutI) →
        (rightData :
          CutPrefixData cd.rightDerivation rightCutK
            (cd.circuit.left.1.paperIndex center) cutI) →
        (leftData.base.get leftData.idxJ) 🗲 (rightData.base.get rightData.idxJ)) :
    ∃ lower : cd.Index, lower.val < center.val ∧ cd.InconsistentIndex lower := by
  rcases inactive_rightCompatible_cutPrefixData_pair cd hcompat hinactive with
    ⟨_cutI, _leftCutK, _rightCutK, ⟨leftData⟩, ⟨rightData⟩⟩
  exact
    cutPrefix_pair_lower_inconsistent_of_center_contradiction cd leftData
      rightData (hcontrCutPrefixes leftData rightData)

/-- Lean-indexed inactive-branch Cut-prefix contradiction bridge. -/
theorem inactive_rightCompatible_lower_inconsistent_of_cutPrefix_center_contradiction_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {center : cd.Index}
    (hcompat : cd.RightCompatibleUpTo center)
    (hinactive : cd.Inactive center)
    (hcontrCutPrefixes :
      ∀ {leftCutK rightCutK cutI : Nat},
        (leftData :
          CutPrefixData cd.leftDerivation leftCutK
            (cd.circuit.left.1.paperIndex center) cutI) →
        (rightData :
          CutPrefixData cd.rightDerivation rightCutK
            (cd.circuit.left.1.paperIndex center) cutI) →
        (leftData.base.get leftData.idxJ) 🗲 (rightData.base.get rightData.idxJ)) :
    ∃ lower : cd.Index,
      cd.circuit.left.1.paperIndex lower <
        cd.circuit.left.1.paperIndex center ∧
      cd.InconsistentIndex lower := by
  rcases
      inactive_rightCompatible_lower_inconsistent_of_cutPrefix_center_contradiction
        cd hcompat hinactive hcontrCutPrefixes with
    ⟨lower, hlower_center, hinconsistent_lower⟩
  exact
    ⟨lower, by simpa [Prepath.paperIndex] using Nat.succ_lt_succ hlower_center,
      hinconsistent_lower⟩

/--
Proposition 5.5.2 given that the inactive case is vacuous: if no least
inconsistent index at or below the bound is inactive, then the least
inconsistent index is active, and the active case supplies an active
inconsistent index no greater than the bound.
-/
theorem right_consistent_inconsistent_of_no_inactive_least {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound)
    (hnoInactiveLeast :
      ∀ least : cd.Index,
        cd.LeastInconsistentAtOrBelow bound least → cd.Inactive least → False) :
    ∃ l : cd.Index,
      l.val ≤ bound.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  rcases right_consistent_inconsistent_least_case_split cd hcompat hinconsistent with
    hdone | hinactiveBranch
  · exact hdone
  · rcases hinactiveBranch with ⟨least, hleast, hinactive⟩
    exact False.elim (hnoInactiveLeast least hleast hinactive)

/--
Proposition 5.5.2, reducing the inactive case to its defining contradiction:
given that every inactive least inconsistent index yields a strictly smaller
inconsistent index (the contradiction of the inactive case), leastness is
contradicted, so the least inconsistent index is active and the active case
applies.
-/
theorem right_consistent_inconsistent_of_inactive_least_lower_inconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound)
    (hlower :
      ∀ least : cd.Index,
        cd.LeastInconsistentAtOrBelow bound least → cd.Inactive least →
          ∃ lower : cd.Index, lower.val < least.val ∧
            cd.InconsistentIndex lower) :
    ∃ l : cd.Index,
      l.val ≤ bound.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  exact
    right_consistent_inconsistent_of_no_inactive_least cd hcompat hinconsistent
      (by
        intro least hleast hinactive
        rcases hlower least hleast hinactive with
          ⟨lower, hlower_least, hinconsistent_lower⟩
        exact hleast.2.2 lower hlower_least hinconsistent_lower)

/--
Proposition 5.5.2, inactive case via the pre-Cut circuit prefix: given that the
selected pre-Cut doubly-active center of every inactive least inconsistent index
is contradictory, the inactive case produces a strictly smaller inconsistent
index, contradicting leastness, so an active inconsistent index results.
-/
theorem right_consistent_inconsistent_of_inactive_least_preCircuit_center_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound)
    (hcontrPreCircuit :
      ∀ (least : cd.Index),
        cd.LeastInconsistentAtOrBelow bound least →
        cd.Inactive least →
          ∀ (preCd : CircuitDerivation Time) (hprefix : preCd.IsInitialPrefix cd),
            preCd.DoublyActive (preCd.prefixIndex hprefix least) →
              (preCd.leftTime (preCd.prefixIndex hprefix least)) 🗲 (preCd.rightTime (preCd.prefixIndex hprefix least))) :
    ∃ l : cd.Index,
      l.val ≤ bound.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  exact
    right_consistent_inconsistent_of_inactive_least_lower_inconsistent cd
      hcompat hinconsistent
      (by
        intro least hleast hinactive
        rcases
            inactive_rightCompatible_lower_inconsistent_of_preCircuit_center_contradiction
              cd (cd.rightCompatibleUpTo_mono hcompat hleast.1) hinactive with
          ⟨preCd, hprefix, hpre⟩
        dsimp only at hpre
        rcases hpre with ⟨hdoublyActive, hlowerOfContr⟩
        exact
          hlowerOfContr
            (hcontrPreCircuit least hleast hinactive preCd hprefix hdoublyActive))

/--
Proposition 5.5.2, inactive case with the Cut-prefix contradiction as the
hypothesis: given that, for every inactive least inconsistent index, the two
chosen pre-Cut base centers contradict, the inactive case closes and an active
inconsistent index results.
-/
theorem right_consistent_inconsistent_of_inactive_least_cutPrefix_center_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound)
    (hcontrCutPrefixes :
      ∀ (least : cd.Index),
        cd.LeastInconsistentAtOrBelow bound least →
        cd.Inactive least →
          ∀ {leftCutK rightCutK cutI : Nat},
            (leftData :
              CutPrefixData cd.leftDerivation leftCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            (rightData :
              CutPrefixData cd.rightDerivation rightCutK
                (cd.circuit.left.1.paperIndex least) cutI) →
            (leftData.base.get leftData.idxJ) 🗲 (rightData.base.get rightData.idxJ)) :
    ∃ l : cd.Index,
      l.val ≤ bound.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  exact
    right_consistent_inconsistent_of_inactive_least_lower_inconsistent cd
      hcompat hinconsistent
      (by
        intro least hleast hinactive
        exact
          inactive_rightCompatible_lower_inconsistent_of_cutPrefix_center_contradiction
            cd (cd.rightCompatibleUpTo_mono hcompat hleast.1) hinactive
            (hcontrCutPrefixes least hleast hinactive))

/--
Every inconsistent-prefix witness
for an inactive least index must precede the two selected pre-Cut bases. Under
that condition, the pre-Cut center contradiction follows by times-increase and
the inactive branch closes.
-/
theorem right_consistent_inconsistent_of_inactive_least_witnesses_before_cut_bases
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound)
    (hwitnessBefore :
      ∀ (least : cd.Index),
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
                InitialPrefix pref.rightDerivation rightData.baseDeriv) :
    ∃ l : cd.Index,
      l.val ≤ bound.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  exact
    right_consistent_inconsistent_of_inactive_least_cutPrefix_center_contradiction
      cd hcompat hinconsistent
      (by
        intro least hleast hinactive leftCutK rightCutK cutI leftData rightData
        rcases hleast.2.1 with ⟨pref, hpref, hactivePref, hcontrPref⟩
        rcases hwitnessBefore least hleast hinactive (leftData := leftData)
            (rightData := rightData) hpref hactivePref hcontrPref with
          ⟨hleftToBase, hrightToBase⟩
        exact
          cutPrefix_center_contradiction_of_witness_prefixes cd leftData rightData
            hpref hleftToBase hrightToBase hcontrPref)

/--
Proposition 5.5.2, inactive case discharged: the greatest active initial
prefixes precede the two pre-Cut bases (by linearity of initial prefixes), which
supplies the witness-before-base premise, closes the inactive case, and leaves
no remaining hypotheses.
-/
theorem right_consistent_inconsistent_of_inactive_least_prefix_comparable
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound) :
    ∃ l : cd.Index,
      l.val ≤ bound.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  exact
    right_consistent_inconsistent_of_inactive_least_witnesses_before_cut_bases
      cd hcompat hinconsistent
      (by
        intro least _hleast _hinactive _leftCutK _rightCutK _cutI leftData
          rightData pref hpref hactivePref _hcontrPref
        exact
          cutPrefixData_pair_active_prefixes_before_bases cd leftData rightData
            hpref hactivePref)

/--
Indexed form of
`right_consistent_inconsistent_of_inactive_least_prefix_comparable`.
-/
theorem right_consistent_inconsistent_of_inactive_least_prefix_comparable_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound) :
    ∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex bound ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  rcases
      right_consistent_inconsistent_of_inactive_least_prefix_comparable
        cd hcompat hinconsistent with
    ⟨l, hle_bound, hcompat_l, hactiveInconsistent_l⟩
  exact
    ⟨l, by simpa [Prepath.paperIndex] using Nat.succ_le_succ hle_bound,
      hcompat_l, hactiveInconsistent_l⟩

/--
Proposition 5.5.2: if a circuit derivation has right-compatible cuts at all
indexes up to and including an inconsistent index (Definition 4.3.2(1)), then it
has an active inconsistent index (Definition 4.3.2(3)) no greater than it (whose
cuts are also right-compatible up to it).
-/
theorem right_consistent_inconsistent_implies_active_inconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound) :
    ∃ l : cd.Index,
      l.val ≤ bound.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  exact
    right_consistent_inconsistent_of_inactive_least_prefix_comparable
      cd hcompat hinconsistent

/--
Paper-index form of Proposition 5.5.2
(`right_consistent_inconsistent_implies_active_inconsistent`), stated with
`paperIndex` comparisons.
-/
theorem right_consistent_inconsistent_implies_active_inconsistent_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound : cd.Index}
    (hcompat : cd.RightCompatibleUpTo bound)
    (hinconsistent : cd.InconsistentIndex bound) :
    ∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex bound ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact
    right_consistent_inconsistent_of_inactive_least_prefix_comparable_indexed
      cd hcompat hinconsistent

/--
Least-index setup for Proposition 5.5.4: from any right-incompatible cut pair,
choose a no-greater least right-incompatible index; all lesser cuts are then
right-compatible.
-/
theorem rightIncompatible_least_setup {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index}
    (hincompat : cd.RightIncompatibleAt j) :
    ∃ least : cd.Index,
      least.val ≤ j.val ∧ cd.RightIncompatibleAt least ∧
        cd.RightCompatibleBefore least := by
  rcases cd.exists_leastRightIncompatibleAtOrBelow hincompat with
    ⟨least, hleast⟩
  exact
    ⟨least, hleast.1, hleast.2.1,
      cd.rightCompatibleBefore_of_leastRightIncompatibleAtOrBelow hleast⟩

/-- Lean-indexed least-index setup. -/
theorem rightIncompatible_least_setup_indexed {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {j : cd.Index}
    (hincompat : cd.RightIncompatibleAt j) :
    ∃ least : cd.Index,
      cd.circuit.left.1.paperIndex least ≤ cd.circuit.left.1.paperIndex j ∧
        cd.RightIncompatibleAt least ∧ cd.RightCompatibleBefore least := by
  rcases rightIncompatible_least_setup cd hincompat with
    ⟨least, hle, hincompat_least, hcompat_before⟩
  exact ⟨least, Nat.succ_le_succ hle, hincompat_least, hcompat_before⟩

/--
The global right-incompatible
proposition reduces to the local analysis of a least right-incompatible witness.
-/
theorem rightIncompatible_exists_activeInconsistent_of_least_witness
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {j : cd.Index}
    (hincompat : cd.RightIncompatibleAt j)
    (hlocal :
      ∀ {least : cd.Index} {leftCutK leftLower rightCutK rightLower : Nat},
        least.val ≤ j.val →
        cd.RightCompatibleBefore least →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex least) leftLower →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex least) rightLower →
        leftLower ≠ rightLower →
        ∃ l : cd.Index,
          l.val < least.val ∧ cd.RightCompatibleUpTo l ∧
            cd.ActiveInconsistentIndex l) :
    ∃ l : cd.Index,
      l.val < j.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  rcases rightIncompatible_least_setup cd hincompat with
    ⟨least, hleast_j, hincompat_least, hcompat_before⟩
  rcases hincompat_least with
    ⟨leftCutK, leftLower, rightCutK, rightLower, hleftCut, hrightCut,
      hne_lower⟩
  rcases hlocal hleast_j hcompat_before hleftCut hrightCut hne_lower with
    ⟨l, hl_least, hcompat_l, hactiveInconsistent_l⟩
  exact
    ⟨l, Nat.lt_of_lt_of_le hl_least hleast_j, hcompat_l,
      hactiveInconsistent_l⟩

/--
Proposition 5.5.4, splitting the least right-incompatible witness: since the two
lower endpoints are unequal (`i ≠ i'`), they order one way or the other,
matching the paper's "without loss of generality suppose `i' > i`" reduction.
Each ordered case is supplied as a local-analysis hypothesis.
-/
theorem rightIncompatible_exists_activeInconsistent_of_ordered_local_analysis
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {j : cd.Index}
    (hincompat : cd.RightIncompatibleAt j)
    (hleftRight :
      ∀ {least leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        least.val ≤ j.val →
        cd.RightCompatibleBefore least →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex least)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex least)
          (cd.circuit.left.1.paperIndex rightLower) →
        leftLower.val < rightLower.val →
        ∃ l : cd.Index,
          l.val < least.val ∧ cd.RightCompatibleUpTo l ∧
            cd.ActiveInconsistentIndex l)
    (hrightLeft :
      ∀ {least leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        least.val ≤ j.val →
        cd.RightCompatibleBefore least →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex least)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex least)
          (cd.circuit.left.1.paperIndex rightLower) →
        rightLower.val < leftLower.val →
        ∃ l : cd.Index,
          l.val < least.val ∧ cd.RightCompatibleUpTo l ∧
            cd.ActiveInconsistentIndex l) :
    ∃ l : cd.Index,
      l.val < j.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  exact
    rightIncompatible_exists_activeInconsistent_of_least_witness cd
      hincompat
      (by
        intro least leftCutK leftLowerNat rightCutK rightLowerNat hleast_j
          hcompatBefore hleftCut hrightCut hlower_ne
        rcases containsCut_indices hleftCut with
          ⟨_leftUpper, _leftCenter, leftLower, _hleftUpper, _hleftCenter,
            hleftLower, _hleftLower_center, _hleftCenter_upper⟩
        rcases containsCut_indices hrightCut with
          ⟨_rightUpper, _rightCenter, rightLowerRaw, _hrightUpper,
            _hrightCenter, hrightLowerRaw, _hrightLower_center,
            _hrightCenter_upper⟩
        let rightLower : cd.Index := Fin.cast cd.circuit.length_eq.symm rightLowerRaw
        have hrightLower :
            cd.circuit.left.1.paperIndex rightLower = rightLowerNat := by
          calc
            cd.circuit.left.1.paperIndex rightLower =
                cd.circuit.right.1.paperIndex (cd.rightIndex rightLower) :=
                  (cd.rightIndex_paperIndex rightLower).symm
            _ = cd.circuit.right.1.paperIndex rightLowerRaw := by
                  rw [cd.rightIndex_castLeft rightLowerRaw]
            _ = rightLowerNat := hrightLowerRaw
        have hleftCut' :
            ContainsCut cd.leftDerivation leftCutK
              (cd.circuit.left.1.paperIndex least)
              (cd.circuit.left.1.paperIndex leftLower) := by
          simpa [hleftLower] using hleftCut
        have hrightCut' :
            ContainsCut cd.rightDerivation rightCutK
              (cd.circuit.left.1.paperIndex least)
              (cd.circuit.left.1.paperIndex rightLower) := by
          simpa [hrightLower] using hrightCut
        rcases Nat.lt_or_gt_of_ne hlower_ne with hlt | hgt
        · have hlt_index : leftLower.val < rightLower.val := by
            have hpaper :
                cd.circuit.left.1.paperIndex leftLower <
                  cd.circuit.left.1.paperIndex rightLower := by
              simpa [hleftLower, hrightLower] using hlt
            exact Nat.succ_lt_succ_iff.mp (by
              simpa [Prepath.paperIndex] using hpaper)
          exact hleftRight hleast_j hcompatBefore hleftCut' hrightCut' hlt_index
        · have hgt_index : rightLower.val < leftLower.val := by
            have hpaper :
                cd.circuit.left.1.paperIndex rightLower <
                  cd.circuit.left.1.paperIndex leftLower := by
              simpa [hleftLower, hrightLower] using hgt
            exact Nat.succ_lt_succ_iff.mp (by
              simpa [Prepath.paperIndex] using hpaper)
          exact hrightLeft hleast_j hcompatBefore hleftCut' hrightCut' hgt_index)

/--
Paper-index form of
`rightIncompatible_exists_activeInconsistent_of_ordered_local_analysis`; the
`leftLower < rightLower` and `rightLower < leftLower` local-analysis branches are
supplied as hypotheses.
-/
theorem rightIncompatible_exists_activeInconsistent_of_ordered_local_analysis_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {j : cd.Index}
    (hincompat : cd.RightIncompatibleAt j)
    (hleftRight :
      ∀ {least leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        cd.circuit.left.1.paperIndex least ≤ cd.circuit.left.1.paperIndex j →
        cd.RightCompatibleBefore least →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex least)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex least)
          (cd.circuit.left.1.paperIndex rightLower) →
        cd.circuit.left.1.paperIndex leftLower <
          cd.circuit.left.1.paperIndex rightLower →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l <
            cd.circuit.left.1.paperIndex least ∧
          cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hrightLeft :
      ∀ {least leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat},
        cd.circuit.left.1.paperIndex least ≤ cd.circuit.left.1.paperIndex j →
        cd.RightCompatibleBefore least →
        ContainsCut cd.leftDerivation leftCutK
          (cd.circuit.left.1.paperIndex least)
          (cd.circuit.left.1.paperIndex leftLower) →
        ContainsCut cd.rightDerivation rightCutK
          (cd.circuit.left.1.paperIndex least)
          (cd.circuit.left.1.paperIndex rightLower) →
        cd.circuit.left.1.paperIndex rightLower <
          cd.circuit.left.1.paperIndex leftLower →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l <
            cd.circuit.left.1.paperIndex least ∧
          cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    ∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  rcases
      rightIncompatible_exists_activeInconsistent_of_ordered_local_analysis cd
        hincompat
        (by
          intro least leftLower rightLower leftCutK rightCutK hleast_j
            hcompatBefore hleftCut hrightCut hleft_right
          rcases hleftRight (Nat.succ_le_succ hleast_j) hcompatBefore
              hleftCut hrightCut (Nat.succ_lt_succ hleft_right) with
            ⟨l, hl_least, hcompat_l, hactiveInconsistent_l⟩
          exact
            ⟨l,
              Nat.succ_lt_succ_iff.mp (by
                simpa [Prepath.paperIndex] using hl_least),
              hcompat_l, hactiveInconsistent_l⟩)
        (by
          intro least leftLower rightLower leftCutK rightCutK hleast_j
            hcompatBefore hleftCut hrightCut hright_left
          rcases hrightLeft (Nat.succ_le_succ hleast_j) hcompatBefore
              hleftCut hrightCut (Nat.succ_lt_succ hright_left) with
            ⟨l, hl_least, hcompat_l, hactiveInconsistent_l⟩
          exact
            ⟨l,
              Nat.succ_lt_succ_iff.mp (by
                simpa [Prepath.paperIndex] using hl_least),
              hcompat_l, hactiveInconsistent_l⟩) with
    ⟨l, hl_j, hcompat_l, hactiveInconsistent_l⟩
  exact
    ⟨l, by simpa [Prepath.paperIndex] using Nat.succ_lt_succ hl_j,
      hcompat_l, hactiveInconsistent_l⟩

/--
Left-path structural case split for Corollary 5.5.3: if a Cut centered at `cutJ` points to `cutI`, then
any intermediate index is centered by a nested Cut. Either that nested Cut's
upper endpoint is exactly `cutJ`, or its upper endpoint is strictly below
`cutJ`.
-/
theorem incompatible_left_nested_cut_or_lower_upper {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) {inner : T.Index}
    (hlower_inner : cutI < T.paperIndex inner)
    (hinner_center : T.paperIndex inner < cutJ) :
    (∃ cutLower : T.Index,
      cutI ≤ T.paperIndex cutLower ∧
        T.paperIndex cutLower < T.paperIndex inner ∧
          ContainsCut deriv cutJ (T.paperIndex inner) (T.paperIndex cutLower)) ∨
    (∃ cutUpper cutLower : T.Index,
      T.paperIndex cutUpper < cutJ ∧
        T.paperIndex inner < T.paperIndex cutUpper ∧
          cutI ≤ T.paperIndex cutLower ∧
            T.paperIndex cutLower < T.paperIndex inner ∧
              ContainsCut deriv (T.paperIndex cutUpper) (T.paperIndex inner)
                (T.paperIndex cutLower)) := by
  rcases
      ConsistentHistories.Routes.PathProperties.Matryoshka.matryoshka_cuts_lower_side_indexed
        deriv hcut hlower_inner hinner_center with
    ⟨cutUpper, cutLower, hupper_le, hlower_le, hcutLower_inner,
      hinner_cutUpper, hnested⟩
  rcases Nat.lt_or_eq_of_le hupper_le with hupper_lt | hupper_eq
  · exact Or.inr
      ⟨cutUpper, cutLower, hupper_lt, hinner_cutUpper, hlower_le,
        hcutLower_inner, hnested⟩
  · exact Or.inl
      ⟨cutLower, hlower_le, hcutLower_inner, by
        simpa [hupper_eq] using hnested⟩

/--
Right-path `cutMe` extraction for Corollary 5.5.3: if a Cut centered at `cutJ` points to `cutI`, then
any intermediate index has a `cutMe` label whose target is no smaller than
`cutI`.
-/
theorem incompatible_intermediate_hasCutMe_ge_lower {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} (deriv : Derivation Time T) {cutK cutJ cutI : Nat}
    (hcut : ContainsCut deriv cutK cutJ cutI) {inner : T.Index}
    (hlower_inner : cutI < T.paperIndex inner)
    (hinner_center : T.paperIndex inner < cutJ) :
    ∃ cutLower : T.Index,
      cutI ≤ T.paperIndex cutLower ∧
        T.paperIndex cutLower < T.paperIndex inner ∧
          ConsistentHistories.Routes.PathProperties.CutmePersistence.HasCutMe
            (T.paperIndex cutLower) (T.get inner) := by
  rcases
      ConsistentHistories.Routes.PathProperties.Matryoshka.matryoshka_cuts_lower_side_indexed
        deriv hcut hlower_inner hinner_center with
    ⟨_cutUpper, cutLower, _hupper_le, hlower_le, hcutLower_inner,
      _hinner_cutUpper, hnested⟩
  exact
    ⟨cutLower, hlower_le, hcutLower_inner,
      ConsistentHistories.Routes.PathProperties.CutmePersistence.containsCut_center_hasCutMe
        hnested inner rfl⟩

/--
Algebraic contradiction step: a time above
`↱ nextTarget` contradicts a same-controller time of the form
`⋊ cutTarget` whenever `nextTarget < cutTarget`.
-/
theorem contradicts_of_nextIndex_le_and_cutMe_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {nextTarget cutTarget : Nat} {nextBase cutBase leftTime rightTime : Time}
    (htarget : nextTarget < cutTarget)
    (hnext : (↱ nextTarget nextBase) ≼ leftTime)
    (hcutMe : rightTime = ⋊ cutTarget cutBase)
    (hctrl : controller leftTime = controller rightTime) :
    leftTime 🗲 rightTime := by
  have hcutMeCtrl :
      controller rightTime = controller cutBase := by
    rw [hcutMe]
    exact (⋊ cutTarget).controller_preserving cutBase
  have hbaseCtrl : controller cutBase = controller nextBase := by
    calc
      controller cutBase = controller rightTime := hcutMeCtrl.symm
      _ = controller leftTime := hctrl.symm
      _ = controller (↱ nextTarget nextBase) := hnext.1.symm
      _ = controller nextBase :=
        (↱ nextTarget).controller_preserving nextBase
  have hdirect :
      (↱ nextTarget nextBase) 🗲 (⋊ cutTarget cutBase) := by
    exact contradicts_symm
      (cutMe_contradicts_nextIndex_of_lt hbaseCtrl htarget)
  have hright : (⋊ cutTarget cutBase) ≼ rightTime := by
    rw [hcutMe]
    exact le_refl _
  exact contradicts_of_le_both hnext hright hdirect

/--
Final-time contradiction in the nontrivial branch of Corollary 5.5.3: when the left nested Cut has upper endpoint strictly
below the original center, the final circuit times at that upper endpoint
contradict.
-/
theorem incompatible_lower_upper_branch_final_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center inner cutUpper cutLower : cd.Index} {rightCutK : Nat}
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex inner))
    (hleftNested :
      ContainsCut cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
        (cd.circuit.left.1.paperIndex inner)
        (cd.circuit.left.1.paperIndex cutLower))
    (hcutLower_inner : cutLower.val < inner.val)
    (hinner_cutUpper : inner.val < cutUpper.val)
    (hcutUpper_center : cutUpper.val < center.val) :
    (cd.leftTime cutUpper) 🗲 (cd.rightTime cutUpper) := by
  have hrightLower_inner :
      cd.circuit.left.1.paperIndex inner <
        cd.circuit.right.1.paperIndex (cd.rightIndex cutUpper) := by
    rw [cd.rightIndex_paperIndex cutUpper]
    exact Nat.succ_lt_succ hinner_cutUpper
  have hrightUpper_center :
      cd.circuit.right.1.paperIndex (cd.rightIndex cutUpper) <
        cd.circuit.left.1.paperIndex center := by
    rw [cd.rightIndex_paperIndex cutUpper]
    exact Nat.succ_lt_succ hcutUpper_center
  rcases incompatible_intermediate_hasCutMe_ge_lower cd.rightDerivation hrightCut
      hrightLower_inner hrightUpper_center with
    ⟨rightLower, hinner_le_rightLower, _hrightLower_lt_cutUpper, hrightCutMe⟩
  rcases hrightCutMe with ⟨rightBase, hrightShape⟩
  rcases containsCut_prefixData hleftNested with ⟨leftData⟩
  have hleftNext :
      (↱ (cd.circuit.left.1.paperIndex cutLower)
        leftData.tk) ≼ (cd.leftTime cutUpper) := by
    simpa [CircuitDerivation.leftTime]
      using leftData.nextIndex_upper_bound_to_prefix leftData.hprefix
        (upper := cutUpper) rfl
  have htarget :
      cd.circuit.left.1.paperIndex cutLower <
        cd.circuit.right.1.paperIndex rightLower := by
    have hleftLower_inner :
        cd.circuit.left.1.paperIndex cutLower <
          cd.circuit.left.1.paperIndex inner :=
      Nat.succ_lt_succ hcutLower_inner
    exact Nat.lt_of_lt_of_le hleftLower_inner hinner_le_rightLower
  have hrightShape' :
      cd.rightTime cutUpper =
        ⋊ (cd.circuit.right.1.paperIndex rightLower) rightBase := by
    simpa [CircuitDerivation.rightTime] using hrightShape
  have hbeforeLast : cd.circuit.left.1.paperIndex cutUpper < cd.circuit.length := by
    have hcutUpper_center_paper :
        cd.circuit.left.1.paperIndex cutUpper <
          cd.circuit.left.1.paperIndex center :=
      Nat.succ_lt_succ hcutUpper_center
    have hcenter_le_length : cd.circuit.left.1.paperIndex center ≤ cd.circuit.length := by
      exact Nat.succ_le_of_lt center.isLt
    exact Nat.lt_of_lt_of_le hcutUpper_center_paper hcenter_le_length
  exact
    contradicts_of_nextIndex_le_and_cutMe_eq (Time := Time) htarget hleftNext
      hrightShape' (cd.controller_eq_before_last cutUpper hbeforeLast)

/--
Prefix-witness form of the nontrivial branch of Corollary 5.5.3: the left nested Cut and the right nested Cut supplied
by Matryoshka form an initial-prefix circuit in which `cutUpper` is doubly
active and contradictory. Therefore `cutUpper` is an inconsistent index of the
final circuit, even though the final right side is inactive there.
-/
theorem incompatible_lower_upper_branch_inconsistent_of_prefix_witness
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center inner cutUpper cutLower : cd.Index} {rightCutK : Nat}
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex inner))
    (hleftNested :
      ContainsCut cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
        (cd.circuit.left.1.paperIndex inner)
        (cd.circuit.left.1.paperIndex cutLower))
    (hcutLower_inner : cutLower.val < inner.val)
    (hinner_cutUpper : inner.val < cutUpper.val)
    (hcutUpper_center : cutUpper.val < center.val) :
    cd.InconsistentIndex cutUpper := by
  have hrightLower_cutUpper :
      cd.circuit.left.1.paperIndex inner <
        cd.circuit.right.1.paperIndex (cd.rightIndex cutUpper) := by
    rw [cd.rightIndex_paperIndex cutUpper]
    exact Nat.succ_lt_succ hinner_cutUpper
  have hcutUpper_center_right :
      cd.circuit.right.1.paperIndex (cd.rightIndex cutUpper) <
        cd.circuit.left.1.paperIndex center := by
    rw [cd.rightIndex_paperIndex cutUpper]
    exact Nat.succ_lt_succ hcutUpper_center
  rcases
      ConsistentHistories.Routes.PathProperties.Matryoshka.matryoshka_cuts_lower_side_indexed
        cd.rightDerivation hrightCut hrightLower_cutUpper hcutUpper_center_right with
    ⟨rightUpper, rightLower, _hrightUpper_center, hinner_le_rightLower,
      _hrightLower_cutUpper, _hcutUpper_rightUpper, hrightNested⟩
  rcases containsCut_prefixData hleftNested with ⟨leftData⟩
  rcases containsCut_prefixData hrightNested with ⟨rightData⟩
  let leftCutDeriv :=
    Derivation.cut leftData.baseDeriv leftData.hij leftData.hjk leftData.hk
      leftData.hj leftData.hi leftData.hconsistent
  have hleftCutToFinal : InitialPrefix leftCutDeriv cd.leftDerivation := by
    simpa [leftCutDeriv] using leftData.hprefix
  have hrightBaseToFinal : InitialPrefix rightData.baseDeriv cd.rightDerivation := by
    exact rightData.base_initialPrefix_final
  let preCd :=
    cd.initialPrefixDerivation leftCutDeriv rightData.baseDeriv
      hleftCutToFinal hrightBaseToFinal
  let hprefix : preCd.IsInitialPrefix cd :=
    cd.initialPrefixDerivation_isInitialPrefix leftCutDeriv rightData.baseDeriv
      hleftCutToFinal hrightBaseToFinal
  let preUpper : preCd.Index := preCd.prefixIndex hprefix cutUpper
  have hleftUpper : preUpper = leftData.idxK := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.left.1.paperIndex preUpper =
          leftData.base.paperIndex leftData.idxK := by
      calc
        preCd.circuit.left.1.paperIndex preUpper =
            cd.circuit.left.1.paperIndex cutUpper := by
              simpa [preUpper] using preCd.prefixIndex_paperIndex hprefix cutUpper
        _ = leftData.base.paperIndex leftData.idxK := leftData.cutK_eq
    exact Nat.succ.inj (by
      simpa [preCd, preUpper, leftCutDeriv, Prepath.paperIndex] using hpaper)
  have hrightUpper : preCd.rightIndex preUpper = rightData.idxJ := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preUpper) =
          rightData.base.paperIndex rightData.idxJ := by
      calc
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preUpper) =
            preCd.circuit.left.1.paperIndex preUpper := by
              exact preCd.rightIndex_paperIndex preUpper
        _ = cd.circuit.left.1.paperIndex cutUpper := by
              simpa [preUpper] using preCd.prefixIndex_paperIndex hprefix cutUpper
        _ = rightData.base.paperIndex rightData.idxJ := by
              exact rightData.cutJ_eq
    exact Nat.succ.inj (by
      simpa [preCd, preUpper, Prepath.paperIndex] using hpaper)
  have hrightUpper_left : preCd.rightIndex leftData.idxK = rightData.idxJ := by
    simpa [hleftUpper] using hrightUpper
  have hactive : preCd.DoublyActive preUpper := by
    constructor
    · simpa [preCd, preUpper, hleftUpper, leftCutDeriv] using
        cutPrefixData_final_cut_upper_active leftData
    · simpa [preCd, preUpper, hrightUpper] using
        cutPrefixData_pre_cut_center_active rightData
  have htarget :
      leftData.base.paperIndex leftData.idxI <
        rightData.base.paperIndex rightData.idxI := by
    have hleftLower_inner :
        cd.circuit.left.1.paperIndex cutLower <
          cd.circuit.left.1.paperIndex inner :=
      Nat.succ_lt_succ hcutLower_inner
    have htargetFinal :
        cd.circuit.left.1.paperIndex cutLower <
          cd.circuit.right.1.paperIndex rightLower :=
      Nat.lt_of_lt_of_le hleftLower_inner hinner_le_rightLower
    have hleftLower :
        leftData.base.paperIndex leftData.idxI =
          cd.circuit.left.1.paperIndex cutLower := by
      exact leftData.cutI_eq.symm
    have hrightLower :
        rightData.base.paperIndex rightData.idxI =
          cd.circuit.right.1.paperIndex rightLower := by
      exact rightData.cutI_eq.symm
    simpa [hleftLower, hrightLower] using htargetFinal
  have hleftNext :
      (↱ (leftData.base.paperIndex leftData.idxI)
        leftData.tk) ≼ (preCd.leftTime preUpper) := by
    have hshape :
        (Derivation.root leftCutDeriv).get leftData.idxK =
          ↱ (leftData.base.paperIndex leftData.idxI) leftData.tk := by
      simp [leftCutDeriv, Derivation.root, Prepath.replace_get_same]
    have hle :
        ((Derivation.root leftCutDeriv).get leftData.idxK) ≼ (preCd.leftTime preUpper) := by
      rw [CircuitDerivation.leftTime, hleftUpper]
      exact le_refl _
    simpa [hshape] using hle
  have hrightShape :
      preCd.rightTime preUpper =
        ⋊ (rightData.base.paperIndex rightData.idxI)
          (rightData.tj # (⋉ (rightData.base.paperIndex rightData.idxJ)
              rightData.tk)) := by
    rw [CircuitDerivation.rightTime, hrightUpper]
    simpa [preCd] using rightData.hj
  have hbeforeLast : preCd.circuit.left.1.paperIndex preUpper < preCd.length := by
    have hidx :
        rightData.idxJ.val + 1 < rightData.base.length := by
      have hjk : rightData.idxJ.val < rightData.idxK.val := rightData.hjk
      have hk_lt : rightData.idxK.val < rightData.base.length := rightData.idxK.isLt
      omega
    have hpreUpper_val : preUpper.val = rightData.idxJ.val := by
      have hval := congrArg Fin.val hrightUpper
      simpa [CircuitDerivation.rightIndex] using hval
    have hlen : rightData.base.length = preCd.length := by
      simpa [preCd, CircuitDerivation.length] using
        preCd.circuit.right_length_eq_length
    change preUpper.val + 1 < preCd.length
    rw [hpreUpper_val]
    rw [← hlen]
    exact hidx
  have hcontr :
      (preCd.leftTime preUpper) 🗲 (preCd.rightTime preUpper) := by
    exact
      contradicts_of_nextIndex_le_and_cutMe_eq (Time := Time) htarget hleftNext
        hrightShape (preCd.controller_eq_before_last preUpper hbeforeLast)
  exact ⟨preCd, hprefix, hactive, hcontr⟩

/--
Lower-upper branch of Corollary 5.5.3: the prefix witness makes the nested upper endpoint
inconsistent; right-consistency before the outer center then yields the active
inconsistent index required by the later argument.
-/
theorem incompatible_lower_upper_branch_exists_rightCompatible_activeInconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center inner cutUpper cutLower : cd.Index} {rightCutK : Nat}
    (hcompatBefore : cd.RightCompatibleBefore center)
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex inner))
    (hleftNested :
      ContainsCut cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
        (cd.circuit.left.1.paperIndex inner)
        (cd.circuit.left.1.paperIndex cutLower))
    (hcutLower_inner : cutLower.val < inner.val)
    (hinner_cutUpper : inner.val < cutUpper.val)
    (hcutUpper_center : cutUpper.val < center.val) :
    ∃ l : cd.Index,
      l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  have hinconsistent :
      cd.InconsistentIndex cutUpper :=
    incompatible_lower_upper_branch_inconsistent_of_prefix_witness cd hrightCut
      hleftNested hcutLower_inner hinner_cutUpper hcutUpper_center
  have hcompatCutUpper : cd.RightCompatibleUpTo cutUpper :=
    cd.rightCompatibleUpTo_of_before_lt hcompatBefore hcutUpper_center
  rcases
      right_consistent_inconsistent_implies_active_inconsistent cd
        hcompatCutUpper hinconsistent with
    ⟨l, hl_cutUpper, hcompat_l, hactive_l⟩
  exact ⟨l, Nat.lt_of_le_of_lt hl_cutUpper hcutUpper_center, hcompat_l,
    hactive_l⟩

/-- Lean-indexed form of
`incompatible_lower_upper_branch_exists_rightCompatible_activeInconsistent`. -/
theorem incompatible_lower_upper_branch_exists_rightCompatible_activeInconsistent_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center inner cutUpper cutLower : cd.Index} {rightCutK : Nat}
    (hcompatBefore : cd.RightCompatibleBefore center)
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex inner))
    (hleftNested :
      ContainsCut cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
        (cd.circuit.left.1.paperIndex inner)
        (cd.circuit.left.1.paperIndex cutLower))
    (hcutLower_inner :
      cd.circuit.left.1.paperIndex cutLower < cd.circuit.left.1.paperIndex inner)
    (hinner_cutUpper :
      cd.circuit.left.1.paperIndex inner < cd.circuit.left.1.paperIndex cutUpper)
    (hcutUpper_center :
      cd.circuit.left.1.paperIndex cutUpper < cd.circuit.left.1.paperIndex center) :
    ∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex center ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  have hcutLower_inner_val : cutLower.val < inner.val :=
    Nat.succ_lt_succ_iff.mp (by
      simpa [Prepath.paperIndex] using hcutLower_inner)
  have hinner_cutUpper_val : inner.val < cutUpper.val :=
    Nat.succ_lt_succ_iff.mp (by
      simpa [Prepath.paperIndex] using hinner_cutUpper)
  have hcutUpper_center_val : cutUpper.val < center.val :=
    Nat.succ_lt_succ_iff.mp (by
      simpa [Prepath.paperIndex] using hcutUpper_center)
  rcases
      incompatible_lower_upper_branch_exists_rightCompatible_activeInconsistent
        cd hcompatBefore hrightCut hleftNested hcutLower_inner_val
        hinner_cutUpper_val hcutUpper_center_val with
    ⟨l, hl_center, hcompat_l, hactive_l⟩
  exact
    ⟨l, by simpa [Prepath.paperIndex] using Nat.succ_lt_succ hl_center,
      hcompat_l, hactive_l⟩

/--
Internal-index form of Corollary 5.5.3: Matryoshka either returns the same-upper nested Cut or
the lower-upper branch produces a smaller right-compatible active-inconsistent
index via the prefix witness.
-/
theorem incompatible_lemma_of_prefix_witness
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center inner leftLower : cd.Index} {leftCutK rightCutK : Nat}
    (hcompatBefore : cd.RightCompatibleBefore center)
    (hleftCut :
      ContainsCut cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex leftLower))
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex inner))
    (hleftLower_inner : leftLower.val < inner.val)
    (hinner_center : inner.val < center.val) :
    (∃ cutLower : cd.Index,
      leftLower.val ≤ cutLower.val ∧ cutLower.val < inner.val ∧
        ContainsCut cd.leftDerivation
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex inner)
          (cd.circuit.left.1.paperIndex cutLower)) ∨
    (∃ l : cd.Index,
      l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l) := by
  have hleftLower_inner_paper :
      cd.circuit.left.1.paperIndex leftLower <
        cd.circuit.left.1.paperIndex inner := by
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ hleftLower_inner
  have hinner_center_paper :
      cd.circuit.left.1.paperIndex inner <
        cd.circuit.left.1.paperIndex center := by
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ hinner_center
  rcases incompatible_left_nested_cut_or_lower_upper cd.leftDerivation hleftCut
      hleftLower_inner_paper hinner_center_paper with hsameUpper | hlowerUpper
  · rcases hsameUpper with
      ⟨cutLower, hleftLower_cutLower, hcutLower_inner, hleftNested⟩
    exact Or.inl
      ⟨cutLower,
        Nat.succ_le_succ_iff.mp (by
          simpa [Prepath.paperIndex] using hleftLower_cutLower),
        Nat.succ_lt_succ_iff.mp (by
          simpa [Prepath.paperIndex] using hcutLower_inner),
        hleftNested⟩
  · rcases hlowerUpper with
      ⟨cutUpper, cutLower, hcutUpper_center, hinner_cutUpper,
        _hleftLower_cutLower, hcutLower_inner, hleftNested⟩
    have hcutLower_inner_val : cutLower.val < inner.val :=
      Nat.succ_lt_succ_iff.mp (by
        simpa [Prepath.paperIndex] using hcutLower_inner)
    have hinner_cutUpper_val : inner.val < cutUpper.val :=
      Nat.succ_lt_succ_iff.mp (by
        simpa [Prepath.paperIndex] using hinner_cutUpper)
    have hcutUpper_center_val : cutUpper.val < center.val :=
      Nat.succ_lt_succ_iff.mp (by
        simpa [Prepath.paperIndex] using hcutUpper_center)
    exact Or.inr
      (incompatible_lower_upper_branch_exists_rightCompatible_activeInconsistent
        cd hcompatBefore hrightCut hleftNested hcutLower_inner_val
        hinner_cutUpper_val hcutUpper_center_val)

/-- Lean-indexed form of `incompatible_lemma_of_prefix_witness`. -/
theorem incompatible_lemma_of_prefix_witness_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center inner leftLower : cd.Index} {leftCutK rightCutK : Nat}
    (hcompatBefore : cd.RightCompatibleBefore center)
    (hleftCut :
      ContainsCut cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex leftLower))
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex inner))
    (hleftLower_inner :
      cd.circuit.left.1.paperIndex leftLower < cd.circuit.left.1.paperIndex inner)
    (hinner_center :
      cd.circuit.left.1.paperIndex inner < cd.circuit.left.1.paperIndex center) :
    (∃ cutLower : cd.Index,
      cd.circuit.left.1.paperIndex leftLower ≤
          cd.circuit.left.1.paperIndex cutLower ∧
        cd.circuit.left.1.paperIndex cutLower <
          cd.circuit.left.1.paperIndex inner ∧
        ContainsCut cd.leftDerivation
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex inner)
          (cd.circuit.left.1.paperIndex cutLower)) ∨
    (∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex center ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) := by
  rcases incompatible_left_nested_cut_or_lower_upper cd.leftDerivation hleftCut
      hleftLower_inner hinner_center with hsameUpper | hlowerUpper
  · exact Or.inl hsameUpper
  · rcases hlowerUpper with
      ⟨cutUpper, cutLower, hcutUpper_center, hinner_cutUpper,
        _hleftLower_cutLower, hcutLower_inner, hleftNested⟩
    exact Or.inr
      (incompatible_lower_upper_branch_exists_rightCompatible_activeInconsistent_indexed
        cd hcompatBefore hrightCut hleftNested hcutLower_inner hinner_cutUpper
        hcutUpper_center)

/--
Ordered local analysis for Proposition 5.5.4 via Corollary 5.5.3: when the right
lower endpoint is above the left lower endpoint, Corollary 5.5.3's lower-upper
case is closed here by the prefix witness, leaving only its same-upper (same
center) case, which is supplied as a hypothesis.
-/
theorem ordered_witness_of_incompatible_and_same_center
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat}
    (hcompatBefore : cd.RightCompatibleBefore center)
    (hleftCut :
      ContainsCut cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex leftLower))
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex rightLower))
    (hleftLower_rightLower : leftLower.val < rightLower.val)
    (hsameCenterBranch :
      ∀ {cutLower : cd.Index},
        leftLower.val ≤ cutLower.val →
        cutLower.val < rightLower.val →
        ContainsCut cd.leftDerivation
          (cd.circuit.left.1.paperIndex center)
          (cd.circuit.left.1.paperIndex rightLower)
          (cd.circuit.left.1.paperIndex cutLower) →
        ∃ l : cd.Index,
          l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
            cd.ActiveInconsistentIndex l) :
    ∃ l : cd.Index,
      l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  have hrightLower_center : rightLower.val < center.val :=
    Nat.succ_lt_succ_iff.mp (by
      simpa [Prepath.paperIndex] using (containsCut_order hrightCut).1)
  rcases incompatible_lemma_of_prefix_witness cd hcompatBefore
      hleftCut hrightCut hleftLower_rightLower hrightLower_center with
      hsameCenter | hdone
  · rcases hsameCenter with
      ⟨cutLower, hleftLower_cutLower, hcutLower_rightLower, hleftNested⟩
    exact hsameCenterBranch hleftLower_cutLower hcutLower_rightLower hleftNested
  · exact hdone

/--
Paper-index form of `ordered_witness_of_incompatible_and_same_center`:
Corollary 5.5.3's lower-upper case is closed by the prefix witness, and its
same-upper (same center) case is supplied as a hypothesis.
-/
theorem ordered_witness_of_incompatible_and_same_center_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat}
    (hcompatBefore : cd.RightCompatibleBefore center)
    (hleftCut :
      ContainsCut cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex leftLower))
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex rightLower))
    (hleftLower_rightLower :
      cd.circuit.left.1.paperIndex leftLower <
        cd.circuit.left.1.paperIndex rightLower)
    (hsameCenterBranch :
      ∀ {cutLower : cd.Index},
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
          cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    ∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex center ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  have hrightLower_center :
      cd.circuit.left.1.paperIndex rightLower <
        cd.circuit.left.1.paperIndex center :=
    (containsCut_order hrightCut).1
  rcases incompatible_lemma_of_prefix_witness_indexed cd hcompatBefore hleftCut
      hrightCut hleftLower_rightLower hrightLower_center with
      hsameCenter | hdone
  · rcases hsameCenter with
      ⟨cutLower, hleftLower_cutLower, hcutLower_rightLower, hleftNested⟩
    exact hsameCenterBranch hleftLower_cutLower hcutLower_rightLower hleftNested
  · exact hdone

/--
Reverse ordered local branch: when the right lower
endpoint is below the left lower endpoint, apply the ordered
technical analysis to the swapped circuit derivation and transport the
resulting active-inconsistent witness back. Only the swapped same-center
branch remains explicit.
-/
theorem reverse_ordered_witness_of_swapped_incompatible_and_same_center
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat}
    (hcompatBefore : cd.RightCompatibleBefore center)
    (hleftCut :
      ContainsCut cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex leftLower))
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex rightLower))
    (hrightLower_leftLower : rightLower.val < leftLower.val)
    (hswapSameCenterBranch :
      ∀ {cutLower : cd.swap.Index},
        (cd.rightIndex rightLower).val ≤ cutLower.val →
        cutLower.val < (cd.rightIndex leftLower).val →
        ContainsCut cd.swap.leftDerivation
          (cd.swap.circuit.left.1.paperIndex (cd.rightIndex center))
          (cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower))
          (cd.swap.circuit.left.1.paperIndex cutLower) →
        ∃ l : cd.swap.Index,
          l.val < (cd.rightIndex center).val ∧
            cd.swap.RightCompatibleUpTo l ∧ cd.swap.ActiveInconsistentIndex l) :
    ∃ l : cd.Index,
      l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  let centerS : cd.swap.Index := cd.rightIndex center
  let leftLowerS : cd.swap.Index := cd.rightIndex rightLower
  let rightLowerS : cd.swap.Index := cd.rightIndex leftLower
  have hcompatBeforeS : cd.swap.RightCompatibleBefore centerS := by
    exact cd.swap_rightCompatibleBefore hcompatBefore
  have hleftCutS :
      ContainsCut cd.swap.leftDerivation rightCutK
        (cd.swap.circuit.left.1.paperIndex centerS)
        (cd.swap.circuit.left.1.paperIndex leftLowerS) := by
    simpa [centerS, leftLowerS, CircuitDerivation.swap, Circuit.swap,
      cd.rightIndex_paperIndex center, cd.rightIndex_paperIndex rightLower]
      using hrightCut
  have hrightCutS :
      ContainsCut cd.swap.rightDerivation leftCutK
        (cd.swap.circuit.left.1.paperIndex centerS)
        (cd.swap.circuit.left.1.paperIndex rightLowerS) := by
    simpa [centerS, rightLowerS, CircuitDerivation.swap, Circuit.swap,
      cd.rightIndex_paperIndex center, cd.rightIndex_paperIndex leftLower]
      using hleftCut
  have horderS : leftLowerS.val < rightLowerS.val := by
    simpa [leftLowerS, rightLowerS, CircuitDerivation.rightIndex]
      using hrightLower_leftLower
  rcases
      ordered_witness_of_incompatible_and_same_center cd.swap
        hcompatBeforeS hleftCutS hrightCutS horderS
        (by
          intro cutLower hleftLower_cutLower hcutLower_right hleftNested
          exact
            hswapSameCenterBranch hleftLower_cutLower hcutLower_right
              hleftNested) with
    ⟨lS, hlS_center, hcompatS, hactiveS⟩
  let l : cd.Index := Fin.cast cd.circuit.length_eq.symm lS
  have hcompatBack : cd.RightCompatibleUpTo l := by
    have hcompatBackSwap : cd.swap.swap.RightCompatibleUpTo l :=
      cd.swap.swap_rightCompatibleUpTo (start := l) (by
        simpa [l, CircuitDerivation.swap, Circuit.swap,
          CircuitDerivation.rightIndex] using hcompatS)
    simpa [CircuitDerivation.swap, Circuit.swap] using hcompatBackSwap
  have hactiveBack : cd.ActiveInconsistentIndex l := by
    simpa [l] using cd.activeInconsistentIndex_of_swap hactiveS
  exact
    ⟨l,
      by
        simpa [l, centerS, CircuitDerivation.rightIndex] using hlS_center,
      hcompatBack, hactiveBack⟩

/--
Paper-index form of
`reverse_ordered_witness_of_swapped_incompatible_and_same_center`; the swapped
same-center branch is supplied as a hypothesis.
-/
theorem reverse_ordered_witness_of_swapped_incompatible_and_same_center_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center leftLower rightLower : cd.Index} {leftCutK rightCutK : Nat}
    (hcompatBefore : cd.RightCompatibleBefore center)
    (hleftCut :
      ContainsCut cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex leftLower))
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex rightLower))
    (hrightLower_leftLower :
      cd.circuit.left.1.paperIndex rightLower <
        cd.circuit.left.1.paperIndex leftLower)
    (hswapSameCenterBranch :
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
            cd.swap.RightCompatibleUpTo l ∧ cd.swap.ActiveInconsistentIndex l) :
    ∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex center ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  have hrightLower_leftLower_val : rightLower.val < leftLower.val :=
    Nat.succ_lt_succ_iff.mp (by
      simpa [Prepath.paperIndex] using hrightLower_leftLower)
  rcases
      reverse_ordered_witness_of_swapped_incompatible_and_same_center
        cd hcompatBefore hleftCut hrightCut hrightLower_leftLower_val
        (by
          intro cutLower hrightLower_cutLower hcutLower_left hleftNested
          rcases hswapSameCenterBranch
              (by
                simpa [Prepath.paperIndex] using
                  Nat.succ_le_succ hrightLower_cutLower)
              (by
                simpa [Prepath.paperIndex] using
                  Nat.succ_lt_succ hcutLower_left)
              hleftNested with
            ⟨l, hl_center, hcompat_l, hactive_l⟩
          exact
            ⟨l,
              Nat.succ_lt_succ_iff.mp (by
                simpa [Prepath.paperIndex] using hl_center),
              hcompat_l, hactive_l⟩) with
    ⟨l, hl_center, hcompat_l, hactive_l⟩
  exact
    ⟨l, by simpa [Prepath.paperIndex] using Nat.succ_lt_succ hl_center,
      hcompat_l, hactive_l⟩

/--
Proposition 5.5.4, both ordered branches of the least right-incompatible witness:
the `leftLower < rightLower` branch is handled on `cd` and the reverse branch on
`cd.swap`. The lower-upper (prefix-witness) case is closed here; the two
same-center branches are supplied as hypotheses (discharged in
`rightIncompatiblePair_implies_activeInconsistent` by
`same_upper_branch_exists_activeInconsistent`).
-/
theorem rightIncompatible_exists_activeInconsistent_of_ordered_incompatible_branches
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {j : cd.Index}
    (hincompat : cd.RightIncompatibleAt j)
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
                  cd.swap.ActiveInconsistentIndex l) :
    ∃ l : cd.Index,
      l.val < j.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  exact
    rightIncompatible_exists_activeInconsistent_of_ordered_local_analysis cd
      hincompat
      (by
        intro least leftLower rightLower leftCutK rightCutK _hleast_j
          hcompatBefore hleftCut hrightCut hleft_right
        exact
          ordered_witness_of_incompatible_and_same_center cd
            hcompatBefore hleftCut hrightCut hleft_right
            (by
              intro cutLower hleftLower_cutLower hcutLower_right hleftNested
              exact
                hdirectSameCenterBranch hcompatBefore hleftCut hrightCut
                  hleft_right hleftLower_cutLower hcutLower_right hleftNested))
      (by
        intro least leftLower rightLower leftCutK rightCutK _hleast_j
          hcompatBefore hleftCut hrightCut hright_left
        exact
          reverse_ordered_witness_of_swapped_incompatible_and_same_center
            cd hcompatBefore hleftCut hrightCut hright_left
            (by
              intro cutLower hrightLower_cutLower hcutLower_left hleftNested
              exact
                hswapSameCenterBranch hcompatBefore hleftCut hrightCut
                  hright_left hrightLower_cutLower hcutLower_left hleftNested))

/--
Paper-index form of
`rightIncompatible_exists_activeInconsistent_of_ordered_incompatible_branches`;
the direct and swapped same-center branches are supplied as hypotheses.
-/
theorem rightIncompatible_exists_activeInconsistent_of_ordered_incompatible_branches_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {j : cd.Index}
    (hincompat : cd.RightIncompatibleAt j)
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
                  cd.swap.ActiveInconsistentIndex l) :
    ∃ l : cd.Index,
      cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
        cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact
    rightIncompatible_exists_activeInconsistent_of_ordered_local_analysis_indexed
      cd hincompat
      (by
        intro least leftLower rightLower leftCutK rightCutK _hleast_j
          hcompatBefore hleftCut hrightCut hleft_right
        exact
          ordered_witness_of_incompatible_and_same_center_indexed cd
            hcompatBefore hleftCut hrightCut hleft_right
            (by
              intro cutLower hleftLower_cutLower hcutLower_right hleftNested
              exact
                hdirectSameCenterBranch hcompatBefore hleftCut hrightCut
                  hleft_right hleftLower_cutLower hcutLower_right hleftNested))
      (by
        intro least leftLower rightLower leftCutK rightCutK _hleast_j
          hcompatBefore hleftCut hrightCut hright_left
        exact
          reverse_ordered_witness_of_swapped_incompatible_and_same_center_indexed
            cd hcompatBefore hleftCut hrightCut hright_left
            (by
              intro cutLower hrightLower_cutLower hcutLower_left hleftNested
              exact
                hswapSameCenterBranch hcompatBefore hleftCut hrightCut
                  hright_left hrightLower_cutLower hcutLower_left hleftNested))

/--
Same-upper branch: if the technical lemma returns a left
Cut `Cut[center,rightLower,cutLower]` while the right derivation has the outer
Cut to `rightLower`, then `rightLower` is an inconsistent index.
-/
theorem same_upper_branch_inconsistentIndex
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center rightLower cutLower : cd.Index} {rightCutK : Nat}
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex rightLower))
    (hleftNested :
      ContainsCut cd.leftDerivation
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex rightLower)
        (cd.circuit.left.1.paperIndex cutLower))
    (_hcutLower_right : cutLower.val < rightLower.val) :
    cd.InconsistentIndex rightLower := by
  rcases containsCut_prefixData hleftNested with ⟨leftData⟩
  rcases containsCut_prefixData hrightCut with ⟨rightData⟩
  let rightCutDeriv :=
    Derivation.cut rightData.baseDeriv rightData.hij rightData.hjk
      rightData.hk rightData.hj rightData.hi rightData.hconsistent
  have hleftBaseToFinal :
      InitialPrefix leftData.baseDeriv cd.leftDerivation :=
    leftData.base_initialPrefix_final
  have hrightCutToFinal :
      InitialPrefix rightCutDeriv cd.rightDerivation := by
    simpa [rightCutDeriv] using rightData.hprefix
  let preCd :=
    cd.initialPrefixDerivation leftData.baseDeriv rightCutDeriv
      hleftBaseToFinal hrightCutToFinal
  let hprefix : preCd.IsInitialPrefix cd :=
    cd.initialPrefixDerivation_isInitialPrefix leftData.baseDeriv
      rightCutDeriv hleftBaseToFinal hrightCutToFinal
  let preLower : preCd.Index := preCd.prefixIndex hprefix rightLower
  let preCenter : preCd.Index := preCd.prefixIndex hprefix center
  have hleftLower : preLower = leftData.idxJ := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.left.1.paperIndex preLower =
          leftData.base.paperIndex leftData.idxJ := by
      calc
        preCd.circuit.left.1.paperIndex preLower =
            cd.circuit.left.1.paperIndex rightLower := by
              simpa [preLower] using preCd.prefixIndex_paperIndex hprefix rightLower
        _ = leftData.base.paperIndex leftData.idxJ := leftData.cutJ_eq
    exact Nat.succ.inj (by
      simpa [preCd, preLower, Prepath.paperIndex] using hpaper)
  have hleftCenter : preCenter = leftData.idxK := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.left.1.paperIndex preCenter =
          leftData.base.paperIndex leftData.idxK := by
      calc
        preCd.circuit.left.1.paperIndex preCenter =
            cd.circuit.left.1.paperIndex center := by
              simpa [preCenter] using preCd.prefixIndex_paperIndex hprefix center
        _ = leftData.base.paperIndex leftData.idxK := leftData.cutK_eq
    exact Nat.succ.inj (by
      simpa [preCd, preCenter, Prepath.paperIndex] using hpaper)
  have hrightLower : preCd.rightIndex preLower = rightData.idxI := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preLower) =
          rightData.base.paperIndex rightData.idxI := by
      calc
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preLower) =
            preCd.circuit.left.1.paperIndex preLower :=
              preCd.rightIndex_paperIndex preLower
        _ = cd.circuit.left.1.paperIndex rightLower := by
              simpa [preLower] using preCd.prefixIndex_paperIndex hprefix rightLower
        _ = rightData.base.paperIndex rightData.idxI := rightData.cutI_eq
    exact Nat.succ.inj (by
      simpa [preCd, rightCutDeriv, CircuitDerivation.rightIndex,
        Prepath.paperIndex] using hpaper)
  have hrightCenter : preCd.rightIndex preCenter = rightData.idxJ := by
    apply Fin.ext
    have hpaper :
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preCenter) =
          rightData.base.paperIndex rightData.idxJ := by
      calc
        preCd.circuit.right.1.paperIndex (preCd.rightIndex preCenter) =
            preCd.circuit.left.1.paperIndex preCenter :=
              preCd.rightIndex_paperIndex preCenter
        _ = cd.circuit.left.1.paperIndex center := by
              simpa [preCenter] using preCd.prefixIndex_paperIndex hprefix center
        _ = rightData.base.paperIndex rightData.idxJ := rightData.cutJ_eq
    exact Nat.succ.inj (by
      simpa [preCd, rightCutDeriv, CircuitDerivation.rightIndex,
        Prepath.paperIndex] using hpaper)
  have hactive : preCd.DoublyActive preLower := by
    constructor
    · simpa [preCd, preLower, hleftLower, CircuitDerivation.leftTime] using
        cutPrefixData_pre_cut_center_active leftData
    · simpa [preCd, preLower, hrightLower, rightCutDeriv,
        CircuitDerivation.rightTime] using
        cutPrefixData_final_cut_lower_active rightData
  have hpreLower_beforeLast :
      preCd.circuit.left.1.paperIndex preLower < preCd.length := by
    have hidx :
        rightData.idxI.val + 1 < rightData.base.length := by
      have hij : rightData.idxI.val < rightData.idxJ.val := rightData.hij
      have hjk : rightData.idxJ.val < rightData.idxK.val := rightData.hjk
      have hk_lt : rightData.idxK.val < rightData.base.length := rightData.idxK.isLt
      omega
    have hpreLower_val : preLower.val = rightData.idxI.val := by
      have hval := congrArg Fin.val hrightLower
      simpa [CircuitDerivation.rightIndex] using hval
    have hlen : rightData.base.length = preCd.length := by
      have hlenRight :
          (Derivation.root rightCutDeriv).length = rightData.base.length := by
        rfl
      exact hlenRight.symm.trans preCd.right_root_length_eq_length
    change preLower.val + 1 < preCd.length
    rw [hpreLower_val]
    rw [← hlen]
    exact hidx
  have hpreCenter_beforeLast :
      preCd.circuit.left.1.paperIndex preCenter < preCd.length := by
    have hidx :
        rightData.idxJ.val + 1 < rightData.base.length := by
      have hjk : rightData.idxJ.val < rightData.idxK.val := rightData.hjk
      have hk_lt : rightData.idxK.val < rightData.base.length := rightData.idxK.isLt
      omega
    have hpreCenter_val : preCenter.val = rightData.idxJ.val := by
      have hval := congrArg Fin.val hrightCenter
      simpa [CircuitDerivation.rightIndex] using hval
    have hlen : rightData.base.length = preCd.length := by
      have hlenRight :
          (Derivation.root rightCutDeriv).length = rightData.base.length := by
        rfl
      exact hlenRight.symm.trans preCd.right_root_length_eq_length
    change preCenter.val + 1 < preCd.length
    rw [hpreCenter_val]
    rw [← hlen]
    exact hidx
  have hrightLowerShape :
      (Derivation.root rightCutDeriv).get rightData.idxI =
        rightData.ti # (⋊ (rightData.base.paperIndex rightData.idxI)
            (rightData.tj # (⋉ (rightData.base.paperIndex rightData.idxJ)
                rightData.tk))) := by
    have hunchanged :=
      Derivation.cut_root_get_lower_unchanged rightData.baseDeriv
        rightData.hij rightData.hjk rightData.hk rightData.hj rightData.hi
        rightData.hconsistent
    rw [hunchanged, rightData.hi]
  let rightBase : Time :=
    rightData.tj # (⋉ (rightData.base.paperIndex rightData.idxJ) rightData.tk)
  have htarget :
      rightData.base.paperIndex rightData.idxI =
        leftData.base.paperIndex leftData.idxJ := by
    calc
      rightData.base.paperIndex rightData.idxI =
          cd.circuit.left.1.paperIndex rightLower := rightData.cutI_eq.symm
      _ = leftData.base.paperIndex leftData.idxJ := leftData.cutJ_eq
  have hcenterCtrl :
      controller (leftData.base.get leftData.idxK) =
        controller (rightData.base.get rightData.idxJ) := by
    have hctrl := preCd.controller_eq_before_last preCenter hpreCenter_beforeLast
    have hrightCenterLeft : preCd.rightIndex leftData.idxK = rightData.idxJ := by
      simpa [hleftCenter] using hrightCenter
    have hrightUnchanged :
        (Derivation.root rightCutDeriv).get rightData.idxJ =
          rightData.base.get rightData.idxJ := by
      exact
        Derivation.cut_root_get_center_unchanged rightData.baseDeriv
          rightData.hij rightData.hjk rightData.hk rightData.hj rightData.hi
          rightData.hconsistent
    have hctrl' :
        controller (leftData.base.get leftData.idxK) =
          controller
            ((Derivation.root rightCutDeriv).get (preCd.rightIndex leftData.idxK)) := by
      simpa [preCd, CircuitDerivation.initialPrefixDerivation, preCenter,
        hleftCenter,
        CircuitDerivation.leftTime, CircuitDerivation.rightTime] using hctrl
    have hctrl'' :
        controller (leftData.base.get leftData.idxK) =
          controller ((Derivation.root rightCutDeriv).get rightData.idxJ) := by
      simpa [hrightCenterLeft] using hctrl'
    simpa [hrightUnchanged] using hctrl''
  have hleftUpperCtrl :
      controller (leftData.base.get leftData.idxK) =
        controller leftData.tk := by
    rw [leftData.hk]
    exact cutYou_controller (leftData.base.paperIndex leftData.idxJ)
      leftData.tk
  have hrightCenterCtrl :
      controller (rightData.base.get rightData.idxJ) =
        controller rightBase := by
    rw [rightData.hj]
    exact cutMe_controller (rightData.base.paperIndex rightData.idxI)
      rightBase
  have hinnerCtrl :
      controller rightBase =
        controller leftData.tk :=
    hrightCenterCtrl.symm.trans (hcenterCtrl.symm.trans hleftUpperCtrl)
  have hinnerContr :
      (⋉ (leftData.base.paperIndex leftData.idxJ) leftData.tk) 🗲 (⋊ (leftData.base.paperIndex leftData.idxJ) rightBase) := by
    exact cutYou_contradicts_cutMe
      (leftData.base.paperIndex leftData.idxJ) hinnerCtrl
  have hlowerCtrl :
      controller leftData.tj =
        controller rightData.ti := by
    have hctrl := preCd.controller_eq_before_last preLower hpreLower_beforeLast
    have hleftCtrl :
        controller (preCd.leftTime preLower) =
          controller leftData.tj := by
      have hcalc :
          controller
              (⋊ (leftData.base.paperIndex leftData.idxI)
                (leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ)
                    leftData.tk))) =
            controller leftData.tj := by
        calc
          controller
              (⋊ (leftData.base.paperIndex leftData.idxI)
                (leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ)
                    leftData.tk))) =
              controller
                (leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ)
                    leftData.tk)) :=
                cutMe_controller (leftData.base.paperIndex leftData.idxI)
                  (leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ)
                      leftData.tk))
          _ = controller leftData.tj :=
                controller_preserving leftData.tj
                  (⋉ (leftData.base.paperIndex leftData.idxJ)
                    leftData.tk)
      have hcalc' :
          controller (leftData.base.get leftData.idxJ) =
            controller leftData.tj := by
        rw [leftData.hj]
        exact hcalc
      simpa [preCd, CircuitDerivation.initialPrefixDerivation, preLower,
        hleftLower, CircuitDerivation.leftTime] using hcalc'
    have hrightCtrl :
        controller (preCd.rightTime preLower) =
          controller rightData.ti := by
      rw [CircuitDerivation.rightTime, hrightLower]
      change
        controller ((Derivation.root rightCutDeriv).get rightData.idxI) =
          controller rightData.ti
      rw [hrightLowerShape]
      exact
        controller_preserving rightData.ti
          (⋊ (rightData.base.paperIndex rightData.idxI) rightBase)
    exact hleftCtrl.symm.trans (hctrl.trans hrightCtrl)
  have hattestContr :
      (leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ)
            leftData.tk)) 🗲 (rightData.ti # (⋊ (leftData.base.paperIndex leftData.idxJ)
            rightBase)) := by
    exact attest_transports_contradiction hlowerCtrl hinnerContr
  have hleftLe :
      (leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ)
            leftData.tk)) ≼ (preCd.leftTime preLower) := by
    have hle :=
      cutMe_expansive (leftData.base.paperIndex leftData.idxI)
        (leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ)
            leftData.tk))
    have hle' :
        (leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ)
              leftData.tk)) ≼ (leftData.base.get leftData.idxJ) := by
      rw [leftData.hj]
      exact hle
    simpa [preCd, CircuitDerivation.initialPrefixDerivation, preLower,
      hleftLower, CircuitDerivation.leftTime] using hle'
  have hrightLe :
      (rightData.ti # (⋊ (leftData.base.paperIndex leftData.idxJ)
            rightBase)) ≼ (preCd.rightTime preLower) := by
    have hrightEq :
        preCd.rightTime preLower =
          rightData.ti # (⋊ (leftData.base.paperIndex leftData.idxJ)
              rightBase) := by
      rw [CircuitDerivation.rightTime, hrightLower]
      simpa [preCd, rightCutDeriv, rightBase, htarget] using
        hrightLowerShape
    rw [hrightEq]
    exact le_refl _
  have hcontr :
      (preCd.leftTime preLower) 🗲 (preCd.rightTime preLower) :=
    contradicts_of_le_both hleftLe hrightLe hattestContr
  exact ⟨preCd, hprefix, by simpa [preLower] using And.intro hactive hcontr⟩

/--
Same-upper branch: the inconsistent `rightLower` index
from `same_upper_branch_inconsistentIndex` is strictly below the outer center,
so right compatibility before the center yields the desired active-inconsistent
witness.
-/
theorem same_upper_branch_exists_activeInconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {center leftLower rightLower cutLower : cd.Index}
    {leftCutK rightCutK : Nat}
    (hcompatBefore : cd.RightCompatibleBefore center)
    (_hleftCut :
      ContainsCut cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex leftLower))
    (hrightCut :
      ContainsCut cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex rightLower))
    (_hleftLower_rightLower : leftLower.val < rightLower.val)
    (_hleftLower_cutLower : leftLower.val ≤ cutLower.val)
    (hcutLower_right : cutLower.val < rightLower.val)
    (hleftNested :
      ContainsCut cd.leftDerivation
        (cd.circuit.left.1.paperIndex center)
        (cd.circuit.left.1.paperIndex rightLower)
        (cd.circuit.left.1.paperIndex cutLower)) :
    ∃ l : cd.Index,
      l.val < center.val ∧ cd.RightCompatibleUpTo l ∧
        cd.ActiveInconsistentIndex l := by
  have hrightLower_center : rightLower.val < center.val :=
    Nat.succ_lt_succ_iff.mp (by
      simpa [Prepath.paperIndex] using (containsCut_order hrightCut).1)
  have hinconsistent :
      cd.InconsistentIndex rightLower :=
    same_upper_branch_inconsistentIndex cd hrightCut hleftNested
      hcutLower_right
  have hcompatRightLower : cd.RightCompatibleUpTo rightLower :=
    cd.rightCompatibleUpTo_of_before_lt hcompatBefore hrightLower_center
  rcases
      right_consistent_inconsistent_implies_active_inconsistent cd
        hcompatRightLower hinconsistent with
    ⟨l, hl_rightLower, hcompat_l, hactive_l⟩
  exact
    ⟨l, Nat.lt_of_le_of_lt hl_rightLower hrightLower_center, hcompat_l,
      hactive_l⟩

/--
Proposition 5.5.4: if a circuit derivation contains a right-incompatible pair of
cuts at some index `j` (Definition 4.3.6(3)), then it has an active inconsistent
index (Definition 4.3.2(3)) strictly below `j` whose cuts are right-compatible at
all indexes up to it.
-/
theorem rightIncompatiblePair_implies_activeInconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    ∀ j : cd.Index, cd.RightIncompatibleAt j →
      ∃ l : cd.Index,
        l.val < j.val ∧ cd.RightCompatibleUpTo l ∧
          cd.ActiveInconsistentIndex l := by
  intro j hincompat
  exact
    rightIncompatible_exists_activeInconsistent_of_ordered_incompatible_branches
      cd hincompat
      (by
        intro center leftLower rightLower cutLower leftCutK rightCutK
          hcompatBefore hleftCut hrightCut hleft_right hleft_cut
          hcut_right hleftNested
        exact
          same_upper_branch_exists_activeInconsistent cd hcompatBefore hleftCut
            hrightCut hleft_right hleft_cut hcut_right hleftNested)
      (by
        intro center leftLower rightLower leftCutK rightCutK hcompatBefore
          hleftCut hrightCut hright_left cutLower hright_cut hcut_left
          hleftNested
        have hcompatBeforeSwap :
            cd.swap.RightCompatibleBefore (cd.rightIndex center) :=
          cd.swap_rightCompatibleBefore hcompatBefore
        have hleftCutSwap :
            ContainsCut cd.swap.leftDerivation rightCutK
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex center))
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex rightLower)) := by
          simpa [CircuitDerivation.swap, Circuit.swap,
            cd.rightIndex_paperIndex center,
            cd.rightIndex_paperIndex rightLower] using hrightCut
        have hrightCutSwap :
            ContainsCut cd.swap.rightDerivation leftCutK
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex center))
              (cd.swap.circuit.left.1.paperIndex (cd.rightIndex leftLower)) := by
          simpa [CircuitDerivation.swap, Circuit.swap,
            cd.rightIndex_paperIndex center,
            cd.rightIndex_paperIndex leftLower] using hleftCut
        have horderSwap :
            (cd.rightIndex rightLower).val < (cd.rightIndex leftLower).val := by
          simpa [CircuitDerivation.rightIndex] using hright_left
        exact
          same_upper_branch_exists_activeInconsistent cd.swap hcompatBeforeSwap
            hleftCutSwap hrightCutSwap horderSwap hright_cut hcut_left
            hleftNested)

end ConsistentHistories.Routes.PathProperties.Compatibility
