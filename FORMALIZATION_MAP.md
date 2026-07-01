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
ContForm.lean
ContForm/Basic.lean
ContForm/Foundation.lean
ContForm/Foundation/...
ContForm/AlternativePresentation.lean
ContForm/AlternativePresentation/...
ContForm/Models.lean
ContForm/Models/...
ContForm/Routes.lean
ContForm/Routes/...
```

## Role Map

| Role | Lean root | Responsibility |
| --- | --- | --- |
| Foundation | `ContForm.Foundation` | Reusable definitions, structures, APIs, and general laws. |
| Alternative presentation | `ContForm.AlternativePresentation` | Alternative-presentation models, counterexamples, and comparison-bridge declarations. |
| Models | `ContForm.Models` | Concrete examples, candidate models, witnesses, and construction packages. |
| Routes | `ContForm.Routes` | Downstream conditional composition routes and dependent adapters. |

## Formal Inventory

Each row maps one numbered paper item to the Lean declaration(s) that state it.
The **PDF line** is the paper's margin line where the item's statement begins;
the **Paper item** is the published number and a short human name; the
**Lean statement** links to the declaration(s) that formalize it, at their exact
file and line.

| PDF line | Paper item | Lean statement |
| ---: | --- | --- |
| 71 | Example 1.2.1 - the exponential cake (narrative) | [`cakeEventSequence`](ContForm/Models/Introduction.lean#L40), [`CakeEvent.IllegalCopy`](ContForm/Models/Introduction.lean#L130) |
| 248 | Definition 2.1.1 - bounded semilattice | [`BoundedSemilattice`](ContForm/Foundation/LocatedSemilattices/TopTrees.lean#L32) |
| 256 | Lemma 2.1.2 - incomparable elements have an inconsistent join | [`BoundedSemilattice.sequential_iff_incomparable_join_top`](ContForm/Foundation/LocatedSemilattices/TopTrees.lean#L232) |
| 264 | Remark 2.1.3 - top is the inconsistent element | [`not_consistent_top`](ContForm/Foundation/LocatedSemilattices/TopTrees.lean#L81), [`top_contradicts_top`](ContForm/Foundation/LocatedSemilattices/TopTrees.lean#L390) |
| 284 | Definition 2.1.4 - contradiction | [`BoundedSemilattice.Contradicts`](ContForm/Foundation/LocatedSemilattices/TopTrees.lean#L365) |
| 285 | Lemma 2.1.5 - monotonicity of contradiction | [`BoundedSemilattice.contradiction_monotone`](ContForm/Foundation/LocatedSemilattices/TopTrees.lean#L458) |
| 287 | Example 2.1.6 - worked top-tree and its joins | [`ConcreteTopTreeExample.semilattice`](ContForm/Foundation/LocatedSemilattices/TopTrees.lean#L714) |
| 294 | Lemma 2.1.7 - consistent times are incomparable iff they contradict | [`BoundedSemilattice.incomparable_iff_contradicts_of_consistent`](ContForm/Foundation/LocatedSemilattices/TopTrees.lean#L859) |
| 297 | Remark 2.1.8 - design alternatives: preorders vs posets | [`BoundedSemilattice`](ContForm/Foundation/LocatedSemilattices/TopTrees.lean#L32) |
| 328 | Definition 2.2.2 - located semilattice | [`LocatedSemilattice`](ContForm/Foundation/LocatedSemilattices/Basic.lean#L28) |
| 359 | Remark 2.2.3 - a located semilattice is a forest of top-trees | [`LocatedSemilattice.fiber`](ContForm/Foundation/LocatedSemilattices/Basic.lean#L123) |
| 378 | Notation 2.2.4 - consistent times CTime | [`LocatedSemilattice.ConsistentTime`](ContForm/Foundation/LocatedSemilattices/Basic.lean#L379) |
| 390 | Lemma 2.2.5 - contradiction implies equal controllers | [`LocatedSemilattice.contradicts_iff`](ContForm/Foundation/LocatedSemilattices/Basic.lean#L603) |
| 394 | Remark 2.2.6 - attestation is an expansive operator | [`LocatedSemilattice.attestation_expansive_operator`](ContForm/Foundation/LocatedSemilattices/Basic.lean#L259) |
| 435 | Example 2.3.2 - a simple located semilattice | [`threeLocatedSemilattice`](ContForm/Models/LocatedSemilattices/Examples/ThreeValued.lean#L116) |
| 448 | Example 2.3.3 - an even simpler example | [`simplerThreeLocatedSemilattice`](ContForm/Models/LocatedSemilattices/Examples/ThreeValued.lean#L178) |
| 451 | Example 2.3.4 - the cake as a located semilattice | [`cakeFigure_realizable_as_located_semilattice`](ContForm/Models/LocatedSemilattices/Examples/CakeFigure.lean#L842) |
| 462 | Example 2.3.5 - paper-scissors-stone | [`simpleGameLocatedSemilattice`](ContForm/Models/LocatedSemilattices/Examples/GamePlay.lean#L153) |
| 483 | Example 2.3.6 - the bureaucracy | [`bureaucracyLocatedSemilattice`](ContForm/Models/LocatedSemilattices/Examples/Bureaucracy.lean#L401) |
| 500 | Example 2.3.7 - closure operators | [`ClosureSystemExample.ClosureSystem`](ContForm/Models/LocatedSemilattices/Examples/ClosureSystem.lean#L89) |
| 534 | Definition 3.1.1 - flag | [`Flag`](ContForm/Foundation/Cut/Flags.lean#L16) |
| 539 | Definition 3.1.2 - having the form of a flag | [`HasForm`](ContForm/Foundation/Cut/Flags.lean#L46) |
| 543 | Definition 3.1.3 - flag-set | [`FlagSet`](ContForm/Foundation/Cut/Flags.lean#L26) |
| 545 | Definition 3.1.4 - flag of a time | [`flagOf`](ContForm/Foundation/Cut/Flags.lean#L101) |
| 553 | Lemma 3.1.5 - top time has no flag | [`apply_top`](ContForm/Foundation/Cut/Flags.lean#L259), [`flagOf_top_none`](ContForm/Foundation/Cut/Flags.lean#L306) |
| 561 | Remark 3.1.6 - top is a flag image yet has no form | [`top_eq_apply_top_and_not_hasForm`](ContForm/Foundation/Cut/Flags.lean#L293) |
| 566 | Lemma 3.1.7 - a time may lack a flag; a flag may lack a time | [`exists_time_flagOf_none_of_controller`](ContForm/Foundation/Cut/Flags.lean#L320), [`topFlag`](ContForm/Foundation/Cut/Flags.lean#L327) |
| 580 | Definition 3.2.1 - located semilattice with Cut | [`LocatedSemilatticeWithCut`](ContForm/Foundation/Cut/Structure.lean#L25) |
| 607 | Remark 3.2.3 - what the cutting flag-set means | [`LocatedSemilatticeWithCut.cutMe_cutYou_incomparable_of_consistent`](ContForm/Foundation/Cut/Structure.lean#L450) |
| 624 | Lemma 3.2.4 - cutMe_j contradicts nextIndex_i for i<j | [`cutMe_contradicts_nextIndex_of_lt`](ContForm/Foundation/Cut/Structure.lean#L270) |
| 630 | Lemma 3.2.5 - flag symbol and index are determined by a consistent value | [`LocatedSemilatticeWithCut.flags_are_equal`](ContForm/Foundation/Cut/Structure.lean#L291) |
| 644 | Definition 3.2.7 - scope-extrusion | [`LocatedSemilatticeWithCut.ScopeExtruding`](ContForm/Foundation/Cut/Structure.lean#L692) |
| 645 | Lemma 3.2.8 - scope-extruding flag gives a valid derivation-step | [`LocatedSemilatticeWithCut.scope_flag`](ContForm/Foundation/Cut/Structure.lean#L708) |
| 650 | Remark 3.2.9 - why scope-extrusion is lax | [`LocatedSemilatticeWithCut.strict_scope_extrusion_nested_cutMe_nextIndex_eq`](ContForm/Foundation/Cut/Structure.lean#L800) |
| 696 | Proposition 3.3.1 - a located semilattice with Cut exists | [`locatedSemilatticeWithCut_exists`](ContForm/Models/Cut/Consistency.lean#L578) |
| 719 | Definition 3.3.2 - many-controller product model | [`manyLocatedSemilattice`](ContForm/Models/Cut/Consistency.lean#L619) |
| 745 | Notation 3.4.1 - list update | [`listUpdate`](ContForm/Models/Cut/InductiveConstruction.lean#L19) |
| 746 | Definition 3.4.2 - the fixed data for the concrete construction | [`NonemptyLocalStateData`](ContForm/Models/Cut/InductiveConstruction.lean#L61) |
| 749 | Definition 3.4.3 - the concrete inductive located semilattice | [`Time`](ContForm/Models/Cut/InductiveConstruction.lean#L92), [`attest`](ContForm/Models/Cut/InductiveConstruction.lean#L433) |
| 760 | Lemma 3.4.4 - t # t = t | [`LocalStateData.attest_self_time`](ContForm/Models/Cut/InductiveConstruction.lean#L464) |
| 766 | Proposition 3.4.5 - the concrete construction is a located semilattice | [`LocalStateData.locatedSemilattice`](ContForm/Models/Cut/InductiveConstructionLaws.lean#L640) |
| 795 | Definition 4.1.1 - prepath, path, derivation | [`Prepath`](ContForm/Foundation/Paths/Basic.lean#L26), [`Derivation`](ContForm/Foundation/Paths/Basic.lean#L347) |
| 819 | Notation 4.1.2 - path index update | [`Prepath.replace`](ContForm/Foundation/Paths/Basic.lean#L132) |
| 823 | Remark 4.1.3 - programmatic rephrasing of the derivation rules | [`initPrepath`](ContForm/Foundation/Paths/Basic.lean#L257) |
| 843 | Remark 4.1.4 - discussion of the derivation rules | [`Derivation.inc_root_changes_precisely_one`](ContForm/Foundation/Paths/Basic.lean#L604) |
| 887 | Definition 4.1.5 - inactive index | [`Prepath.InactiveBetween`](ContForm/Foundation/Paths/Basic.lean#L2222) |
| 898 | Definition 4.2.1 - initial prefix | [`InitialPrefix`](ContForm/Foundation/Paths/InitialPrefixes.lean#L21) |
| 904 | Lemma 4.2.2 - times increase | [`InitialPrefix.times_increase`](ContForm/Foundation/Paths/InitialPrefixes.lean#L388) |
| 914 | Definition 4.3.1 - circuits and circuit-derivations | [`Circuit`](ContForm/Routes/Paths/Circuits/Circuit.lean#L18) |
| 930 | Definition 4.3.2 - (in)consistency of circuit-derivations | [`CircuitDerivation.Inconsistent`](ContForm/Routes/Paths/Circuits/CircuitDerivation.lean#L1849), [`CircuitDerivation.Consistent`](ContForm/Routes/Paths/Circuits/CircuitDerivation.lean#L1854) |
| 954 | Proposition 4.3.4 - contradiction persists along a circuit-derivation | [`CircuitDerivation.contradiction_persists_from_prefix`](ContForm/Routes/Paths/Circuits/CircuitDerivation.lean#L2170), [`CircuitDerivation.inconsistentIndex_contradicts_final`](ContForm/Routes/Paths/Circuits/CircuitDerivation.lean#L2203) |
| 977 | Definition 4.3.6 - contains a cut centred on j; right-(in)compatible | [`ContainsCut`](ContForm/Routes/Paths/Circuits/Circuit.lean#L247) |
| 1023 | Lemma 5.1.1 - cutMe persists | [`cutme_forever`](ContForm/Routes/PathProperties/CutmePersistence.lean#L179) |
| 1037 | Corollary 5.1.2 - inactive implies cutMe | [`inactiveBetween_implies_hasCutMe`](ContForm/Routes/PathProperties/InactiveCuts.lean#L665) |
| 1045 | Corollary 5.1.3 - cut implies cutMe | [`containsCut_bracketed_hasCutMe`](ContForm/Routes/PathProperties/Matryoshka.lean#L1416) |
| 1051 | Remark 5.1.4 - the reverse implication fails (counterexample) | [`cutMeIntro_after_init_has_cutMe_active_uncut`](ContForm/Routes/PathProperties/CutmePersistence.lean#L445) |
| 1059 | Lemma 5.2.1 - flag of a non-initial index | [`time_flag`](ContForm/Routes/PathProperties/FlagNesting.lean#L111) |
| 1068 | Lemma 5.2.2 - flags nest | [`derivation_skip_cuts_initialPrefix`](ContForm/Routes/PathProperties/InactiveCuts.lean#L1120) |
| 1098 | Proposition 5.2.3 - affine cuts | [`containsCut_same_center_endpoints_eq`](ContForm/Routes/PathProperties/InactiveCuts.lean#L1704), [`no_containsCut_before_final_same_center`](ContForm/Routes/PathProperties/InactiveCuts.lean#L1455) |
| 1124 | Corollary 5.2.4 - active points to active | [`active_points_to_active`](ContForm/Routes/PathProperties/InactiveCuts.lean#L786) |
| 1137 | Lemma 5.2.5 - cut endpoints are active | [`final_cut_endpoints_active`](ContForm/Routes/PathProperties/InactiveCuts.lean#L1779) |
| 1150 | Lemma 5.3.1 - cut implies inactive | [`containsCut_brackets_inactive`](ContForm/Routes/PathProperties/InactiveCuts.lean#L129) |
| 1158 | Lemma 5.3.2 - a jump implies a cut exists | [`jump_implies_cut_exists`](ContForm/Routes/PathProperties/InactiveCuts.lean#L293) |
| 1177 | Proposition 5.3.3 - inactive implies a cut | [`inactiveBetween_implies_containsCut_center`](ContForm/Routes/PathProperties/InactiveCuts.lean#L465) |
| 1200 | Corollary 5.3.4 - inactive implies a cut (refined) | [`inactive_implies_cutPrefixData_refined`](ContForm/Routes/PathProperties/InactiveCuts.lean#L1610) |
| 1216 | Proposition 5.4.1 - matryoshka cuts | [`matryoshka_cuts_lower_side`](ContForm/Routes/PathProperties/Matryoshka.lean#L31), [`matryoshka_cuts_upper_side`](ContForm/Routes/PathProperties/Matryoshka.lean#L55) |
| 1241 | Corollary 5.4.3 - cuts are ordered by derivation | [`cuts_ordered_by_derivation`](ContForm/Routes/PathProperties/Matryoshka.lean#L1191) |
| 1260 | Corollary 5.4.4 - cuts nest | [`cuts_ordered_nesting_precisely_one_component`](ContForm/Routes/PathProperties/Matryoshka.lean#L1716) |
| 1268 | Lemma 5.5.1 - a final cut pair makes its endpoint doubly-active inconsistent | [`final_cut_pair`](ContForm/Routes/PathProperties/Compatibility.lean#L26) |
| 1291 | Proposition 5.5.2 - right-compatible inconsistent implies active inconsistent | [`right_consistent_inconsistent_implies_active_inconsistent`](ContForm/Routes/PathProperties/Compatibility.lean#L1368) |
| 1323 | Corollary 5.5.3 - incompatible cuts | [`incompatible_left_nested_cut_or_lower_upper`](ContForm/Routes/PathProperties/Compatibility.lean#L1627) |
| 1349 | Proposition 5.5.4 - a right-incompatible pair implies active inconsistent | [`rightIncompatiblePair_implies_activeInconsistent`](ContForm/Routes/PathProperties/Compatibility.lean#L2850) |
| 1396 | Theorem 5.6.2 - inconsistent index implies active inconsistent index | [`inconsistentIndex_implies_activeInconsistentIndex`](ContForm/Routes/PathProperties/MainResult.lean#L657) |
| 1415 | Corollary 5.6.3 - inconsistent implies active inconsistent | [`inconsistentCircuit_implies_activeInconsistent`](ContForm/Routes/PathProperties/MainResult.lean#L672) |
| 1421 | Corollary 5.6.4 - the least inconsistent index is active inconsistent | [`leastInconsistentIndex_is_activeInconsistent`](ContForm/Routes/PathProperties/MainResult.lean#L684) |
| 1452 | Definition 6.2.1 - C-closure of T | [`CClosure`](ContForm/Routes/StrongerSafety/Closure.lean#L26) |
| 1459 | Lemma 6.2.2 - properties of the C-closure | [`cClosure_is_C_closure`](ContForm/Routes/StrongerSafety/Closure.lean#L149) |
| 1476 | Definition 6.3.1 - chain of cuts | [`ChainOfCuts`](ContForm/Routes/StrongerSafety/Chains.lean#L40) |
| 1482 | Lemma 6.3.2 - the chain of cuts is well-defined | [`exists_unique_nodes_of_inactive`](ContForm/Routes/StrongerSafety/Chains.lean#L2077) |
| 1491 | Lemma 6.3.3 - the non-final chain nodes are active in the other derivation | [`left_chain_right_active_of_least_inconsistent_active`](ContForm/Routes/StrongerSafety/Chains.lean#L1392), [`right_chain_left_active_of_least_inconsistent`](ContForm/Routes/StrongerSafety/Chains.lean#L1414) |
| 1536 | Definition 6.4.1 - active indices, times and controllers | [`ActiveIndexPath`](ContForm/Routes/StrongerSafety/Absolute.lean#L27), [`ActiveIndexCircuit`](ContForm/Routes/StrongerSafety/Absolute.lean#L132) |
| 1541 | Definition 6.4.2 - (in)consistent set of times | [`TimesInconsistent`](ContForm/Routes/StrongerSafety/Absolute.lean#L492) |
| 1551 | Theorem 6.4.3 - inconsistent circuit implies inconsistent C-closure | [`inconsistentCircuit_implies_cClosure_inconsistent`](ContForm/Routes/StrongerSafety/Absolute.lean#L5769) |
| 1590 | Notation 6.4.4 - upper-bounded by R | [`UpperBoundedBy`](ContForm/Routes/StrongerSafety/Absolute.lean#L4504) |
| 1593 | Definition 6.4.5 - consistent C-attestation-closed set of upper bounds | [`ConsistentCAttestationClosedUpperBounds`](ContForm/Routes/StrongerSafety/Absolute.lean#L4649) |
| 1601 | Corollary 6.4.6 - an upper-bound set implies consistency | [`consistent_upperBounds_imply_circuit_consistent`](ContForm/Routes/StrongerSafety/Absolute.lean#L5801) |
| 1622 | Definition 6.4.8 - most recent attested time | [`MostRecentAttested`](ContForm/Routes/StrongerSafety/Absolute.lean#L4762) |
| 1624 | Example 6.4.9 - algorithm computing a set of upper bounds | [`algorithm_computes_consistent_upperBounds`](ContForm/Routes/StrongerSafety/Absolute.lean#L5831) |
| 1659 | Remark 6.4.10 - the most-recent proof obligation | [`mostRecentAttested_tuple_check`](ContForm/Routes/StrongerSafety/Absolute.lean#L5871) |
| 1682 | Definition 7.2 - attestation | [`Attestation`](ContForm/AlternativePresentation/Attestation.lean#L200) |
| 1697 | Remark 7.3 - attestation is not necessarily monotone | [`exists_attestation_not_inputMonotone`](ContForm/AlternativePresentation/Attestation.lean#L800), [`exists_attestation_not_parameterMonotone`](ContForm/AlternativePresentation/Attestation.lean#L844) |
| 1700 | Example 7.4 - examples of attestations | [`principalAttestation`](ContForm/AlternativePresentation/Attestation.lean#L1177) |
| 1726 | Definition 7.5 - separating / monotone attestation | [`Attestation.Separating`](ContForm/AlternativePresentation/Attestation.lean#L467) |
| 1732 | Definition 7.6 - located semilattice (alternative presentation) | [`AlternativeLocatedSemilattice`](ContForm/AlternativePresentation/AlternativeLocatedSemilattice.lean#L24) |
| 1746 | Definition 7.7 - cutting-flag bounded semilattice; located semilattice with Cut | [`AlternativeLocatedSemilatticeWithCut`](ContForm/AlternativePresentation/AlternativeLocatedSemilattice.lean#L853) |
| 1756 | Remark 7.8 - geometric observation on the cutting poset | [`AlternativeLocatedSemilatticeWithCut.cutting_cutMe_contradicts_cutYou`](ContForm/AlternativePresentation/DegenerateAlternativeCutExample.lean#L212) |

