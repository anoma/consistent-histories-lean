# Formalization Map

A reference map from the published paper to this Lean development: each numbered
paper item is linked to the declaration(s) that formalize it.

## Source Authority

The formalization target is the published paper *Consistent histories:
enforcing linearity and excluding double-spending amongst collaborating
controllers* by Murdoch J. Gabbay and Isaac Sheff.

Each row below is keyed by the paper's published item number (Definition,
Lemma, Proposition, Theorem, Corollary, Notation, Example, or Remark) and by
the margin line at which that item's statement begins. Only numbered items with
a faithful Lean formalization are listed; conclusions/future-work material and
purely expository remarks with nothing to formalize are not targets.

## Module Tree

```text
ConsistentHistories.lean
ConsistentHistories/Basic.lean
ConsistentHistories/Foundation.lean
ConsistentHistories/Foundation/...
ConsistentHistories/AlternativePresentation.lean
ConsistentHistories/AlternativePresentation/...
ConsistentHistories/Models.lean
ConsistentHistories/Models/...
ConsistentHistories/Routes.lean
ConsistentHistories/Routes/...
```

## Role Map

| Role | Lean root | Responsibility |
| --- | --- | --- |
| Foundation | `ConsistentHistories.Foundation` | Reusable definitions, structures, APIs, and general laws. |
| Alternative presentation | `ConsistentHistories.AlternativePresentation` | Alternative-presentation models, counterexamples, and comparison-bridge declarations. |
| Models | `ConsistentHistories.Models` | Concrete examples, candidate models, witnesses, and construction packages. |
| Routes | `ConsistentHistories.Routes` | Downstream conditional composition routes and dependent adapters. |

## Formal Inventory

Each row maps one numbered paper item to the Lean declaration(s) that state it.
The **PDF line** is the paper's margin line where the item's statement begins;
the **Paper item** is the published number and a short human name; the
**Lean statement** links to the declaration(s) that formalize it, at their exact
file and line.

| PDF line | Paper item | Lean statement |
| ---: | --- | --- |
| 68 | Example 1.2.1 - the exponential cake (narrative) | [`cakeEventSequence`](ConsistentHistories/Models/Introduction.lean#L40), [`CakeEvent.IllegalCopy`](ConsistentHistories/Models/Introduction.lean#L130) |
| 261 | Definition 2.1.1 - bounded semilattice | [`BoundedSemilattice`](ConsistentHistories/Foundation/LocatedSemilattices/TopTrees.lean#L32) |
| 271 | Lemma 2.1.2 - incomparable elements have an inconsistent join | [`BoundedSemilattice.sequential_iff_incomparable_join_top`](ConsistentHistories/Foundation/LocatedSemilattices/TopTrees.lean#L232) |
| 279 | Definition 2.1.3 - contradiction | [`BoundedSemilattice.Contradicts`](ConsistentHistories/Foundation/LocatedSemilattices/TopTrees.lean#L365) |
| 280 | Example 2.1.4 - worked top-tree and its joins | [`ConcreteTopTreeExample.semilattice`](ConsistentHistories/Foundation/LocatedSemilattices/TopTrees.lean#L714) |
| 286 | Remark 2.1.5 - top is the inconsistent element | [`not_consistent_top`](ConsistentHistories/Foundation/LocatedSemilattices/TopTrees.lean#L81), [`top_contradicts_top`](ConsistentHistories/Foundation/LocatedSemilattices/TopTrees.lean#L390) |
| 307 | Lemma 2.1.6 - monotonicity of contradiction | [`BoundedSemilattice.contradiction_monotone`](ConsistentHistories/Foundation/LocatedSemilattices/TopTrees.lean#L458) |
| 310 | Lemma 2.1.7 - consistent times are incomparable iff they contradict | [`BoundedSemilattice.incomparable_iff_contradicts_of_consistent`](ConsistentHistories/Foundation/LocatedSemilattices/TopTrees.lean#L859) |
| 313 | Remark 2.1.8 - design alternatives: preorders vs posets | [`BoundedSemilattice`](ConsistentHistories/Foundation/LocatedSemilattices/TopTrees.lean#L32) |
| 345 | Definition 2.2.2 - located semilattice | [`LocatedSemilattice`](ConsistentHistories/Foundation/LocatedSemilattices/Basic.lean#L28) |
| 379 | Remark 2.2.3 - a located semilattice is a forest of top-trees | [`LocatedSemilattice.fiber`](ConsistentHistories/Foundation/LocatedSemilattices/Basic.lean#L123) |
| 398 | Notation 2.2.4 - consistent times CTime | [`LocatedSemilattice.ConsistentTime`](ConsistentHistories/Foundation/LocatedSemilattices/Basic.lean#L379) |
| 410 | Lemma 2.2.5 - contradiction implies equal controllers | [`LocatedSemilattice.contradicts_iff`](ConsistentHistories/Foundation/LocatedSemilattices/Basic.lean#L603) |
| 414 | Remark 2.2.6 - attestation is an expansive operator | [`LocatedSemilattice.attestation_expansive_operator`](ConsistentHistories/Foundation/LocatedSemilattices/Basic.lean#L259) |
| 455 | Example 2.3.2 - a simple located semilattice | [`threeLocatedSemilattice`](ConsistentHistories/Models/LocatedSemilattices/Examples/ThreeValued.lean#L116) |
| 468 | Example 2.3.3 - an even simpler example | [`simplerThreeLocatedSemilattice`](ConsistentHistories/Models/LocatedSemilattices/Examples/ThreeValued.lean#L178) |
| 471 | Example 2.3.4 - the cake as a located semilattice | [`cakeFigure_realizable_as_located_semilattice`](ConsistentHistories/Models/LocatedSemilattices/Examples/CakeFigure.lean#L842) |
| 482 | Example 2.3.5 - paper-scissors-stone | [`simpleGameLocatedSemilattice`](ConsistentHistories/Models/LocatedSemilattices/Examples/GamePlay.lean#L153) |
| 503 | Example 2.3.6 - the bureaucracy | [`bureaucracyLocatedSemilattice`](ConsistentHistories/Models/LocatedSemilattices/Examples/Bureaucracy.lean#L401) |
| 520 | Example 2.3.7 - closure operators | [`ClosureSystemExample.ClosureSystem`](ConsistentHistories/Models/LocatedSemilattices/Examples/ClosureSystem.lean#L89) |
| 553 | Definition 3.1.1 - flag | [`Flag`](ConsistentHistories/Foundation/Cut/Flags.lean#L16) |
| 558 | Definition 3.1.2 - having the form of a flag | [`HasForm`](ConsistentHistories/Foundation/Cut/Flags.lean#L46) |
| 562 | Definition 3.1.3 - flag-set | [`FlagSet`](ConsistentHistories/Foundation/Cut/Flags.lean#L26) |
| 565 | Definition 3.1.4 - flag of a time | [`flagOf`](ConsistentHistories/Foundation/Cut/Flags.lean#L101) |
| 573 | Lemma 3.1.5 - top time has no flag | [`apply_top`](ConsistentHistories/Foundation/Cut/Flags.lean#L259), [`flagOf_top_none`](ConsistentHistories/Foundation/Cut/Flags.lean#L306) |
| 581 | Remark 3.1.6 - top is a flag image yet has no form | [`top_eq_apply_top_and_not_hasForm`](ConsistentHistories/Foundation/Cut/Flags.lean#L293) |
| 586 | Lemma 3.1.7 - a time may lack a flag; a flag may lack a time | [`exists_time_flagOf_none_of_controller`](ConsistentHistories/Foundation/Cut/Flags.lean#L320), [`topFlag`](ConsistentHistories/Foundation/Cut/Flags.lean#L327) |
| 599 | Definition 3.2.1 - located semilattice with Cut | [`LocatedSemilatticeWithCut`](ConsistentHistories/Foundation/Cut/Structure.lean#L25) |
| 627 | Remark 3.2.3 - what the cutting flag-set means | [`LocatedSemilatticeWithCut.cutMe_cutYou_incomparable_of_consistent`](ConsistentHistories/Foundation/Cut/Structure.lean#L450) |
| 644 | Lemma 3.2.4 - cutMe_j contradicts nextIndex_i for i<j | [`cutMe_contradicts_nextIndex_of_lt`](ConsistentHistories/Foundation/Cut/Structure.lean#L270) |
| 650 | Lemma 3.2.5 - flag symbol and index are determined by a consistent value | [`LocatedSemilatticeWithCut.flags_are_equal`](ConsistentHistories/Foundation/Cut/Structure.lean#L291) |
| 664 | Definition 3.2.7 - scope-extrusion | [`LocatedSemilatticeWithCut.ScopeExtruding`](ConsistentHistories/Foundation/Cut/Structure.lean#L692) |
| 665 | Lemma 3.2.8 - scope-extruding flag gives a valid derivation-step | [`LocatedSemilatticeWithCut.scope_flag`](ConsistentHistories/Foundation/Cut/Structure.lean#L708) |
| 670 | Remark 3.2.9 - why scope-extrusion is lax | [`LocatedSemilatticeWithCut.strict_scope_extrusion_nested_cutMe_nextIndex_eq`](ConsistentHistories/Foundation/Cut/Structure.lean#L800) |
| 716 | Proposition 3.3.1 - a located semilattice with Cut exists | [`locatedSemilatticeWithCut_exists`](ConsistentHistories/Models/Cut/Consistency.lean#L578) |
| 739 | Definition 3.3.2 - many-controller product model | [`manyLocatedSemilattice`](ConsistentHistories/Models/Cut/Consistency.lean#L619) |
| 765 | Notation 3.4.1 - list update | [`listUpdate`](ConsistentHistories/Models/Cut/InductiveConstruction.lean#L19) |
| 766 | Definition 3.4.2 - the fixed data for the concrete construction | [`NonemptyLocalStateData`](ConsistentHistories/Models/Cut/InductiveConstruction.lean#L61) |
| 769 | Definition 3.4.3 - the concrete inductive located semilattice | [`Time`](ConsistentHistories/Models/Cut/InductiveConstruction.lean#L92), [`attest`](ConsistentHistories/Models/Cut/InductiveConstruction.lean#L433) |
| 780 | Lemma 3.4.4 - t # t = t | [`LocalStateData.attest_self_time`](ConsistentHistories/Models/Cut/InductiveConstruction.lean#L464) |
| 786 | Proposition 3.4.5 - the concrete construction is a located semilattice | [`LocalStateData.locatedSemilattice`](ConsistentHistories/Models/Cut/InductiveConstructionLaws.lean#L640) |
| 815 | Definition 4.1.1 - prepath, path, derivation | [`Prepath`](ConsistentHistories/Foundation/Paths/Basic.lean#L26), [`Derivation`](ConsistentHistories/Foundation/Paths/Basic.lean#L347) |
| 839 | Notation 4.1.2 - path index update | [`Prepath.replace`](ConsistentHistories/Foundation/Paths/Basic.lean#L132) |
| 843 | Remark 4.1.3 - programmatic rephrasing of the derivation rules | [`initPrepath`](ConsistentHistories/Foundation/Paths/Basic.lean#L257) |
| 863 | Remark 4.1.4 - discussion of the derivation rules | [`Derivation.inc_root_changes_precisely_one`](ConsistentHistories/Foundation/Paths/Basic.lean#L604) |
| 907 | Definition 4.1.5 - inactive index | [`Prepath.InactiveBetween`](ConsistentHistories/Foundation/Paths/Basic.lean#L2222) |
| 918 | Definition 4.2.1 - initial prefix | [`InitialPrefix`](ConsistentHistories/Foundation/Paths/InitialPrefixes.lean#L21) |
| 924 | Lemma 4.2.2 - times increase | [`InitialPrefix.times_increase`](ConsistentHistories/Foundation/Paths/InitialPrefixes.lean#L388) |
| 934 | Definition 4.3.1 - circuits and circuit-derivations | [`Circuit`](ConsistentHistories/Routes/Paths/Circuits/Circuit.lean#L18) |
| 950 | Definition 4.3.2 - (in)consistency of circuit-derivations | [`CircuitDerivation.Inconsistent`](ConsistentHistories/Routes/Paths/Circuits/CircuitDerivation.lean#L1849), [`CircuitDerivation.Consistent`](ConsistentHistories/Routes/Paths/Circuits/CircuitDerivation.lean#L1854) |
| 975 | Proposition 4.3.4 - contradiction persists along a circuit-derivation | [`CircuitDerivation.contradiction_persists_from_prefix`](ConsistentHistories/Routes/Paths/Circuits/CircuitDerivation.lean#L2170), [`CircuitDerivation.inconsistentIndex_contradicts_final`](ConsistentHistories/Routes/Paths/Circuits/CircuitDerivation.lean#L2203) |
| 997 | Definition 4.3.6 - contains a cut centred on j; right-(in)compatible | [`ContainsCut`](ConsistentHistories/Routes/Paths/Circuits/Circuit.lean#L247) |
| 1043 | Lemma 5.1.1 - cutMe persists | [`cutme_forever`](ConsistentHistories/Routes/PathProperties/CutmePersistence.lean#L179) |
| 1057 | Corollary 5.1.2 - inactive implies cutMe | [`inactiveBetween_implies_hasCutMe`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L665) |
| 1065 | Corollary 5.1.3 - cut implies cutMe | [`containsCut_bracketed_hasCutMe`](ConsistentHistories/Routes/PathProperties/Matryoshka.lean#L1416) |
| 1071 | Remark 5.1.4 - the reverse implication fails (counterexample) | [`cutMeIntro_after_init_has_cutMe_active_uncut`](ConsistentHistories/Routes/PathProperties/CutmePersistence.lean#L445) |
| 1079 | Lemma 5.2.1 - flag of a non-initial index | [`time_flag`](ConsistentHistories/Routes/PathProperties/FlagNesting.lean#L111) |
| 1088 | Lemma 5.2.2 - flags nest | [`derivation_skip_cuts_initialPrefix`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L1120) |
| 1118 | Proposition 5.2.3 - affine cuts | [`containsCut_same_center_endpoints_eq`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L1704), [`no_containsCut_before_final_same_center`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L1455) |
| 1144 | Corollary 5.2.4 - active points to active | [`active_points_to_active`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L786) |
| 1157 | Lemma 5.2.5 - cut endpoints are active | [`final_cut_endpoints_active`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L1779) |
| 1170 | Lemma 5.3.1 - cut implies inactive | [`containsCut_brackets_inactive`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L129) |
| 1178 | Lemma 5.3.2 - a jump implies a cut exists | [`jump_implies_cut_exists`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L293) |
| 1197 | Proposition 5.3.3 - inactive implies a cut | [`inactiveBetween_implies_containsCut_center`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L465) |
| 1220 | Corollary 5.3.4 - inactive implies a cut (refined) | [`inactive_implies_cutPrefixData_refined`](ConsistentHistories/Routes/PathProperties/InactiveCuts.lean#L1610) |
| 1236 | Proposition 5.4.1 - matryoshka cuts | [`matryoshka_cuts_lower_side`](ConsistentHistories/Routes/PathProperties/Matryoshka.lean#L31), [`matryoshka_cuts_upper_side`](ConsistentHistories/Routes/PathProperties/Matryoshka.lean#L55) |
| 1261 | Corollary 5.4.3 - cuts are ordered by derivation | [`cuts_ordered_by_derivation`](ConsistentHistories/Routes/PathProperties/Matryoshka.lean#L1191) |
| 1280 | Corollary 5.4.4 - cuts nest | [`cuts_ordered_nesting_precisely_one_component`](ConsistentHistories/Routes/PathProperties/Matryoshka.lean#L1716) |
| 1288 | Lemma 5.5.1 - a final cut pair makes its endpoint doubly-active inconsistent | [`final_cut_pair`](ConsistentHistories/Routes/PathProperties/Compatibility.lean#L26) |
| 1311 | Proposition 5.5.2 - right-compatible inconsistent implies active inconsistent | [`right_consistent_inconsistent_implies_active_inconsistent`](ConsistentHistories/Routes/PathProperties/Compatibility.lean#L1368) |
| 1343 | Corollary 5.5.3 - incompatible cuts | [`incompatible_left_nested_cut_or_lower_upper`](ConsistentHistories/Routes/PathProperties/Compatibility.lean#L1627) |
| 1369 | Proposition 5.5.4 - a right-incompatible pair implies active inconsistent | [`rightIncompatiblePair_implies_activeInconsistent`](ConsistentHistories/Routes/PathProperties/Compatibility.lean#L2850) |
| 1416 | Theorem 5.6.2 - inconsistent index implies active inconsistent index | [`inconsistentIndex_implies_activeInconsistentIndex`](ConsistentHistories/Routes/PathProperties/MainResult.lean#L657) |
| 1435 | Corollary 5.6.3 - inconsistent implies active inconsistent | [`inconsistentCircuit_implies_activeInconsistent`](ConsistentHistories/Routes/PathProperties/MainResult.lean#L672) |
| 1442 | Corollary 5.6.4 - the least inconsistent index is active inconsistent | [`leastInconsistentIndex_is_activeInconsistent`](ConsistentHistories/Routes/PathProperties/MainResult.lean#L684) |
| 1473 | Definition 6.2.1 - C-closure of T | [`CClosure`](ConsistentHistories/Routes/StrongerSafety/Closure.lean#L26) |
| 1480 | Lemma 6.2.2 - properties of the C-closure | [`cClosure_is_C_closure`](ConsistentHistories/Routes/StrongerSafety/Closure.lean#L149) |
| 1497 | Definition 6.3.1 - chain of cuts | [`ChainOfCuts`](ConsistentHistories/Routes/StrongerSafety/Chains.lean#L40) |
| 1503 | Lemma 6.3.2 - the chain of cuts is well-defined | [`exists_unique_nodes_of_inactive`](ConsistentHistories/Routes/StrongerSafety/Chains.lean#L2077) |
| 1512 | Lemma 6.3.3 - the non-final chain nodes are active in the other derivation | [`left_chain_right_active_of_least_inconsistent_active`](ConsistentHistories/Routes/StrongerSafety/Chains.lean#L1392), [`right_chain_left_active_of_least_inconsistent`](ConsistentHistories/Routes/StrongerSafety/Chains.lean#L1414) |
| 1557 | Definition 6.4.1 - active indices, times and controllers | [`ActiveIndexPath`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L27), [`ActiveIndexCircuit`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L132) |
| 1562 | Definition 6.4.2 - (in)consistent set of times | [`TimesInconsistent`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L492) |
| 1572 | Theorem 6.4.3 - inconsistent circuit implies inconsistent C-closure | [`inconsistentCircuit_implies_cClosure_inconsistent`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L5769) |
| 1611 | Notation 6.4.4 - upper-bounded by R | [`UpperBoundedBy`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L4504) |
| 1614 | Definition 6.4.5 - consistent C-attestation-closed set of upper bounds | [`ConsistentCAttestationClosedUpperBounds`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L4649) |
| 1622 | Corollary 6.4.6 - an upper-bound set implies consistency | [`consistent_upperBounds_imply_circuit_consistent`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L5801) |
| 1642 | Definition 6.4.8 - most recent attested time | [`MostRecentAttested`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L4762) |
| 1645 | Example 6.4.9 - algorithm computing a set of upper bounds | [`algorithm_computes_consistent_upperBounds`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L5831) |
| 1680 | Remark 6.4.10 - the most-recent proof obligation | [`mostRecentAttested_tuple_check`](ConsistentHistories/Routes/StrongerSafety/Absolute.lean#L5871) |
| 1703 | Definition 7.2 - attestation | [`Attestation`](ConsistentHistories/AlternativePresentation/Attestation.lean#L200) |
| 1718 | Remark 7.3 - attestation is not necessarily monotone | [`exists_attestation_not_inputMonotone`](ConsistentHistories/AlternativePresentation/Attestation.lean#L800), [`exists_attestation_not_parameterMonotone`](ConsistentHistories/AlternativePresentation/Attestation.lean#L844) |
| 1721 | Example 7.4 - examples of attestations | [`principalAttestation`](ConsistentHistories/AlternativePresentation/Attestation.lean#L1177) |
| 1747 | Definition 7.5 - separating / monotone attestation | [`Attestation.Separating`](ConsistentHistories/AlternativePresentation/Attestation.lean#L467) |
| 1753 | Definition 7.6 - located semilattice (alternative presentation) | [`AlternativeLocatedSemilattice`](ConsistentHistories/AlternativePresentation/AlternativeLocatedSemilattice.lean#L24) |
| 1767 | Definition 7.7 - cutting-flag bounded semilattice; located semilattice with Cut | [`AlternativeLocatedSemilatticeWithCut`](ConsistentHistories/AlternativePresentation/AlternativeLocatedSemilattice.lean#L853) |
| 1777 | Remark 7.8 - geometric observation on the cutting poset | [`AlternativeLocatedSemilatticeWithCut.cutting_cutMe_contradicts_cutYou`](ConsistentHistories/AlternativePresentation/DegenerateAlternativeCutExample.lean#L212) |
