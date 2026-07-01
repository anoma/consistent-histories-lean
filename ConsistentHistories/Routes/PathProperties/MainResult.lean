import ConsistentHistories.Routes.PathProperties.Compatibility

/-!
Paper §5.6 "Main result: inconsistent index implies active inconsistent index".
This module assembles Theorem 5.6.2 (an inconsistent index has a no-greater
active inconsistent index reached through right-compatible cuts) together with
its two circuit-level consequences, Corollary 5.6.3 (an inconsistent circuit
derivation is active inconsistent) and Corollary 5.6.4 (the least inconsistent
index is itself active inconsistent).
-/

namespace ConsistentHistories.Routes.PathProperties.MainResult

open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Routes.Paths.Circuits
open ConsistentHistories.Foundation.Paths.InitialPrefixes

universe u v

/--
Case split underlying Theorem 5.6.2. The first hypothesis is the
right-incompatible branch (Proposition 5.5.4): a right-incompatible index has a
strictly lesser active inconsistent index reached through right-compatible cuts.
The second is the right-compatible branch (Proposition 5.5.2): a right-compatible
inconsistent index has a no-greater active inconsistent index. Applied to the
least inconsistent index at or below any inconsistent `j`, they give a no-greater
active inconsistent index `l` (`l.val ≤ j.val`) with right-compatible cuts at all
indexes no greater than `l`.
-/
theorem index_result_of_right_incompatible_and_right_consistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hrightConsistent :
      ∀ j : cd.Index, cd.RightCompatibleUpTo j → cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  intro j hinconsistent
  rcases cd.exists_leastInconsistentAtOrBelow hinconsistent with
    ⟨least, hleast_bound, hinconsistentLeast, hminimal⟩
  have hcompatLeast : cd.RightCompatibleUpTo least := by
    exact (cd.rightCompatibleUpTo_iff_no_rightIncompatibleAt least).mpr (by
      intro r hr_least hincompat
      rcases hrightIncompatible r hincompat with
        ⟨lower, hlower_r, _hcompat_lower, hactiveInconsistent_lower⟩
      exact hminimal lower (Nat.lt_of_lt_of_le hlower_r hr_least)
        hactiveInconsistent_lower.2)
  rcases hrightConsistent least hcompatLeast hinconsistentLeast with
    ⟨l, hle_l_least, hcompat_l, hactiveInconsistent_l⟩
  exact
    ⟨l, Nat.le_trans hle_l_least hleast_bound, hcompat_l,
      hactiveInconsistent_l⟩

/--
Paper-index form of `index_result_of_right_incompatible_and_right_consistent`:
the same case split for Theorem 5.6.2 with both branches left as hypotheses,
stated with `paperIndex` comparisons in place of the underlying `Fin` values.
-/
theorem index_result_of_right_incompatible_and_right_consistent_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l)
    (hrightConsistent :
      ∀ j : cd.Index, cd.RightCompatibleUpTo j → cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
          cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  intro j hinconsistent
  have hrightIncompatibleInternal :
      ∀ r : cd.Index, cd.RightIncompatibleAt r →
        ∃ l : cd.Index,
          l.val < r.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
    intro r hincompat
    rcases hrightIncompatible r hincompat with
      ⟨l, hlt, hcompat_l, hactiveInconsistent_l⟩
    exact
      ⟨l, Nat.succ_lt_succ_iff.mp (by simpa [Prepath.paperIndex] using hlt),
        hcompat_l, hactiveInconsistent_l⟩
  have hrightConsistentInternal :
      ∀ r : cd.Index, cd.RightCompatibleUpTo r → cd.InconsistentIndex r →
        ∃ l : cd.Index,
          l.val ≤ r.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
    intro r hcompat hinconsistent_r
    rcases hrightConsistent r hcompat hinconsistent_r with
      ⟨l, hle, hcompat_l, hactiveInconsistent_l⟩
    exact
      ⟨l, Nat.succ_le_succ_iff.mp (by simpa [Prepath.paperIndex] using hle),
        hcompat_l, hactiveInconsistent_l⟩
  rcases index_result_of_right_incompatible_and_right_consistent cd
      hrightIncompatibleInternal hrightConsistentInternal j hinconsistent with
    ⟨l, hle, hcompat_l, hactiveInconsistent_l⟩
  exact ⟨l, Nat.succ_le_succ hle, hcompat_l, hactiveInconsistent_l⟩

/--
Theorem 5.6.2 with the right-compatible branch (Proposition 5.5.2) discharged by
`right_consistent_inconsistent_implies_active_inconsistent`, leaving the
right-incompatible branch (Proposition 5.5.4) as the only hypothesis.
-/
theorem index_result_of_right_incompatible {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          l.val < j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_right_incompatible_and_right_consistent cd
      hrightIncompatible
      (by
        intro j hcompat hinconsistent
        exact
          ConsistentHistories.Routes.PathProperties.Compatibility.right_consistent_inconsistent_implies_active_inconsistent
            cd hcompat hinconsistent)

/--
Paper-index form of `index_result_of_right_incompatible`, stated with
`paperIndex` comparisons.
-/
theorem index_result_of_right_incompatible_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    (hrightIncompatible :
      ∀ j : cd.Index, cd.RightIncompatibleAt j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l < cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
          cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_right_incompatible_and_right_consistent_indexed cd
      hrightIncompatible
      (by
        intro j hcompat hinconsistent
        exact
          ConsistentHistories.Routes.PathProperties.Compatibility.right_consistent_inconsistent_implies_active_inconsistent_indexed
            cd hcompat hinconsistent)

/--
Theorem 5.6.2 with the right-incompatible branch (Proposition 5.5.4) obtained
from the ordered same-center reduction of Section 5.5, and the right-compatible
branch (Proposition 5.5.2) left explicit. The remaining hypotheses are the two
same-center cut obligations, one for each order of the lower left and right
endpoints.
-/
theorem index_result_of_ordered_incompatible_branches_and_right_consistent
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
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧
          cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_right_incompatible_and_right_consistent cd
      (by
        intro j hincompat
        exact
          ConsistentHistories.Routes.PathProperties.Compatibility.rightIncompatible_exists_activeInconsistent_of_ordered_incompatible_branches
            cd hincompat hdirectSameCenterBranch hswapSameCenterBranch)
      hrightConsistent

/--
Theorem 5.6.2 with the right-incompatible branch obtained from the ordered
same-center reduction of Section 5.5, and the right-compatible branch
(Proposition 5.5.2) discharged by
`right_consistent_inconsistent_implies_active_inconsistent`. The remaining
hypotheses are the two same-center cut obligations.
-/
theorem index_result_of_ordered_incompatible_branches
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
                  cd.swap.ActiveInconsistentIndex l) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧
          cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_ordered_incompatible_branches_and_right_consistent cd hdirectSameCenterBranch hswapSameCenterBranch
      (by
        intro j hcompat hinconsistent
        exact
          ConsistentHistories.Routes.PathProperties.Compatibility.right_consistent_inconsistent_implies_active_inconsistent
            cd hcompat hinconsistent)

/--
Paper-index form of
`index_result_of_ordered_incompatible_branches_and_right_consistent`, stated with
`paperIndex` comparisons; the two same-center cut obligations and the
right-compatible branch remain explicit hypotheses.
-/
theorem index_result_of_ordered_incompatible_branches_and_right_consistent_indexed
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
    (hrightConsistent :
      ∀ j : cd.Index, cd.RightCompatibleUpTo j → cd.InconsistentIndex j →
        ∃ l : cd.Index,
          cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
            cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
          cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_right_incompatible_and_right_consistent_indexed cd
      (by
        intro j hincompat
        exact
          ConsistentHistories.Routes.PathProperties.Compatibility.rightIncompatible_exists_activeInconsistent_of_ordered_incompatible_branches_indexed
            cd hincompat hdirectSameCenterBranch hswapSameCenterBranch)
      hrightConsistent

/--
Paper-index form of `index_result_of_ordered_incompatible_branches`, stated with
`paperIndex` comparisons; the two same-center cut obligations remain the only
explicit hypotheses.
-/
theorem index_result_of_ordered_incompatible_branches_indexed
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
                  cd.swap.ActiveInconsistentIndex l) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        cd.circuit.left.1.paperIndex l ≤ cd.circuit.left.1.paperIndex j ∧
          cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_ordered_incompatible_branches_and_right_consistent_indexed cd hdirectSameCenterBranch hswapSameCenterBranch
      (by
        intro j hcompat hinconsistent
        exact
          ConsistentHistories.Routes.PathProperties.Compatibility.right_consistent_inconsistent_implies_active_inconsistent_indexed
            cd hcompat hinconsistent)

/--
Theorem 5.6.2 with the right-incompatible branch (Proposition 5.5.4) left as an
explicit premise, and the right-compatible branch (Proposition 5.5.2) reduced,
for an inactive least inconsistent index, to the center contradiction over
initial prefixes: on every initial prefix that is doubly active at the least
index, its left and right times there are contradictory.
-/
theorem index_result_of_right_incompatible_and_preCircuit_center_contradiction
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
              (preCd.leftTime (preCd.prefixIndex hprefix least)) 🗲 (preCd.rightTime (preCd.prefixIndex hprefix least))) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_right_incompatible_and_right_consistent cd hrightIncompatible
      (by
        intro bound hcompat hinconsistent
        exact
          ConsistentHistories.Routes.PathProperties.Compatibility.right_consistent_inconsistent_of_inactive_least_preCircuit_center_contradiction
            cd hcompat hinconsistent
            (by
              intro least hleast hinactive
              exact hcontrPreCircuit (bound := bound) (least := least)
                hcompat hleast hinactive))

/--
Theorem 5.6.2 with the right-incompatible branch (Proposition 5.5.4) left as an
explicit premise, and the right-compatible branch (Proposition 5.5.2) reduced,
for an inactive least inconsistent index, to the Cut-prefix center contradiction:
for matching left and right Cut-prefix data at the least index, the two base
times at the shared cut witness are contradictory.
-/
theorem index_result_of_right_incompatible_and_cutPrefix_center_contradiction
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
            (leftData.base.get leftData.idxJ) 🗲 (rightData.base.get rightData.idxJ)) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_right_incompatible_and_right_consistent cd hrightIncompatible
      (by
        intro bound hcompat hinconsistent
        exact
          ConsistentHistories.Routes.PathProperties.Compatibility.right_consistent_inconsistent_of_inactive_least_cutPrefix_center_contradiction
            cd hcompat hinconsistent
            (by
              intro least hleast hinactive
              exact hcontrCutPrefixes (bound := bound) (least := least)
                hcompat hleast hinactive))

/--
Theorem 5.6.2 with the right-incompatible branch (Proposition 5.5.4) left as an
explicit premise, and the right-compatible branch (Proposition 5.5.2) supplied
through the paper's chosen active pre-Cut prefixes step. The explicit premise
orders the doubly-active witness prefixes before the Cut base derivations, which
is what yields the Cut-prefix center contradiction.
-/
theorem index_result_of_right_incompatible_and_witnesses_before_cut_bases
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
                InitialPrefix pref.rightDerivation rightData.baseDeriv) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_right_incompatible_and_right_consistent cd hrightIncompatible
      (by
        intro bound hcompat hinconsistent
        exact
          ConsistentHistories.Routes.PathProperties.Compatibility.right_consistent_inconsistent_of_inactive_least_witnesses_before_cut_bases
            cd hcompat hinconsistent
            (by
              intro least hleast hinactive
              exact hwitnessBefore (bound := bound) (least := least)
                hcompat hleast hinactive))

/--
Circuit-level form of Corollary 5.6.3 derived from the index-level statement of
Theorem 5.6.2: unfolding `Inconsistent` to an inconsistent index and applying
`hindex` produces an active inconsistent index, hence `ActiveInconsistent`.
-/
theorem inconsistent_activeInconsistent_of_index_result {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    cd.Inconsistent → cd.ActiveInconsistent := by
  rintro ⟨j, hinconsistent⟩
  rcases hindex j hinconsistent with ⟨l, _hle, _hcompat, hactiveInconsistent⟩
  exact ⟨l, hactiveInconsistent⟩

/--
Corollary 5.6.3 obtained from
`index_result_of_ordered_incompatible_branches_and_right_consistent`: the
right-incompatible branch comes from the ordered same-center reduction of
Section 5.5 and the right-compatible branch is left explicit, with the two
same-center cut obligations remaining as hypotheses.
-/
theorem inconsistent_activeInconsistent_of_ordered_incompatible_branches_and_right_consistent
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
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    cd.Inconsistent → cd.ActiveInconsistent := by
  exact
    inconsistent_activeInconsistent_of_index_result cd
      (index_result_of_ordered_incompatible_branches_and_right_consistent cd hdirectSameCenterBranch hswapSameCenterBranch hrightConsistent)

/--
Corollary 5.6.4 derived from the index-level statement of Theorem 5.6.2: the
least inconsistent index has some no-greater active inconsistent index `l`, and
leastness forces `l` to equal it, so the least inconsistent index is itself
active inconsistent with right-compatible cuts through it.
-/
theorem least_inconsistent_activeInconsistent_of_index_result {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) {bound least : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound least)
    (hindex :
      ∀ j : cd.Index, cd.InconsistentIndex j →
        ∃ l : cd.Index,
          l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧ cd.ActiveInconsistentIndex l) :
    cd.RightCompatibleUpTo least ∧ cd.ActiveInconsistentIndex least := by
  rcases hleast with ⟨_hle_bound, hinconsistentLeast, hminimal⟩
  rcases hindex least hinconsistentLeast with
    ⟨l, hle_l_least, hcompat_l, hactiveInconsistent_l⟩
  have hnot_lt : ¬ l.val < least.val := by
    intro hlt
    exact hminimal l hlt hactiveInconsistent_l.2
  have hval : l.val = least.val :=
    Nat.le_antisymm hle_l_least (Nat.le_of_not_gt hnot_lt)
  have hl_eq_least : l = least := Fin.ext hval
  subst l
  exact ⟨hcompat_l, hactiveInconsistent_l⟩

/--
Theorem 5.6.2: for a circuit derivation, any inconsistent index `j`
(Definition 4.3.2(1)) has an index `l` with `l ≤ j` that is active inconsistent
(Definition 4.3.2(3)) and through which the derivation has right-compatible cuts
at all indexes no greater than `l` (Definition 4.3.6(4)).
-/
theorem inconsistentIndex_implies_activeInconsistentIndex {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    (cd : CircuitDerivation Time) :
    ∀ j : cd.Index, cd.InconsistentIndex j →
      ∃ l : cd.Index,
        l.val ≤ j.val ∧ cd.RightCompatibleUpTo l ∧
          cd.ActiveInconsistentIndex l := by
  exact
    index_result_of_right_incompatible cd
      (ConsistentHistories.Routes.PathProperties.Compatibility.rightIncompatiblePair_implies_activeInconsistent
        cd)

/--
Corollary 5.6.3: an inconsistent circuit derivation (Definition 4.3.2(2)) is
active inconsistent (Definition 4.3.2(4)).
-/
theorem inconsistentCircuit_implies_activeInconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) :
    cd.Inconsistent → cd.ActiveInconsistent := by
  exact
    inconsistent_activeInconsistent_of_index_result cd
      (inconsistentIndex_implies_activeInconsistentIndex cd)

/--
Corollary 5.6.4: for an inconsistent circuit derivation, the least inconsistent
index is active inconsistent (Definition 4.3.2(3)) and has right-compatible cuts
at all indexes no greater than it (Definition 4.3.6(4), i.e. up to and including
it).
-/
theorem leastInconsistentIndex_is_activeInconsistent {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {bound least : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound least) :
    cd.RightCompatibleUpTo least ∧ cd.ActiveInconsistentIndex least := by
  exact
    least_inconsistent_activeInconsistent_of_index_result cd hleast
      (inconsistentIndex_implies_activeInconsistentIndex cd)

end ConsistentHistories.Routes.PathProperties.MainResult
