import ContForm.Basic

/-!
Paper section: Introduction.

This module is reserved for introductory examples and global paper metadata.
The first formal mathematical definitions start in
`ContForm.Foundation.LocatedSemilattices`.
-/

namespace ContForm.Models.Introduction

/--
Example 1.2.1: the three controllers appearing in the
introductory cake narrative.

This records only the narrative's actors; the mathematical
cake-as-located-semilattice construction is Example 2.3.4, in
`ContForm.Models.LocatedSemilattices.Examples`.
-/
inductive CakeController where
  | controller1
  | controller2
  | controller3
  deriving DecidableEq

/--
Example 1.2.1: the explicit sequence of events listed in the
introductory cake narrative.
-/
inductive CakeEvent where
  | sendSliceToController2
  | controller2CopiesCake
  | controller2ReturnsFirstCopy
  | controller2SendsSecondCopyToController3
  | controller3PassesSliceBackToController1
  deriving DecidableEq

/-- Example 1.2.1: the five listed cake events in order. -/
def cakeEventSequence : List CakeEvent :=
  [ CakeEvent.sendSliceToController2
  , CakeEvent.controller2CopiesCake
  , CakeEvent.controller2ReturnsFirstCopy
  , CakeEvent.controller2SendsSecondCopyToController3
  , CakeEvent.controller3PassesSliceBackToController1
  ]

/-- Example 1.2.1: the introductory cake sequence has five listed events. -/
theorem cakeEventSequence_length :
    cakeEventSequence.length = 5 := by
  rfl

/-- Example 1.2.1: the introductory cake sequence is exactly the listed order. -/
theorem cakeEventSequence_order :
    cakeEventSequence =
      [ CakeEvent.sendSliceToController2
      , CakeEvent.controller2CopiesCake
      , CakeEvent.controller2ReturnsFirstCopy
      , CakeEvent.controller2SendsSecondCopyToController3
      , CakeEvent.controller3PassesSliceBackToController1
      ] := by
  rfl

namespace CakeEvent

/--
Example 1.2.1: transfer events in the introductory narrative,
with their source and destination controllers.
-/
inductive Transfer : CakeEvent → CakeController → CakeController → Prop where
  | one_to_two :
      Transfer sendSliceToController2 CakeController.controller1 CakeController.controller2
  | two_to_one :
      Transfer controller2ReturnsFirstCopy CakeController.controller2 CakeController.controller1
  | two_to_three :
      Transfer controller2SendsSecondCopyToController3
        CakeController.controller2 CakeController.controller3
  | three_to_one :
      Transfer controller3PassesSliceBackToController1
        CakeController.controller3 CakeController.controller1

/-- Example 1.2.1: exact characterization of the transfer events. -/
theorem transfer_iff (event : CakeEvent) (source target : CakeController) :
    Transfer event source target ↔
      (event = sendSliceToController2 ∧
        source = CakeController.controller1 ∧ target = CakeController.controller2) ∨
      (event = controller2ReturnsFirstCopy ∧
        source = CakeController.controller2 ∧ target = CakeController.controller1) ∨
      (event = controller2SendsSecondCopyToController3 ∧
        source = CakeController.controller2 ∧ target = CakeController.controller3) ∨
      (event = controller3PassesSliceBackToController1 ∧
        source = CakeController.controller3 ∧ target = CakeController.controller1) := by
  constructor
  · intro h
    cases h <;> simp
  · intro h
    rcases h with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Transfer.one_to_two
    · exact Transfer.two_to_one
    · exact Transfer.two_to_three
    · exact Transfer.three_to_one

/-- Example 1.2.1: Controller 1 sends the slice to Controller 2. -/
theorem transfer_sendSliceToController2 :
    Transfer sendSliceToController2 CakeController.controller1 CakeController.controller2 := by
  exact Transfer.one_to_two

/-- Example 1.2.1: Controller 2 sends the first copied slice back to Controller 1. -/
theorem transfer_controller2ReturnsFirstCopy :
    Transfer controller2ReturnsFirstCopy CakeController.controller2 CakeController.controller1 := by
  exact Transfer.two_to_one

/-- Example 1.2.1: Controller 2 sends the second copied slice to Controller 3. -/
theorem transfer_controller2SendsSecondCopyToController3 :
    Transfer controller2SendsSecondCopyToController3
      CakeController.controller2 CakeController.controller3 := by
  exact Transfer.two_to_three

/-- Example 1.2.1: Controller 3 passes the slice back to Controller 1. -/
theorem transfer_controller3PassesSliceBackToController1 :
    Transfer controller3PassesSliceBackToController1
      CakeController.controller3 CakeController.controller1 := by
  exact Transfer.three_to_one

/--
Example 1.2.1: the non-linear/illegal copy event in the
introductory narrative.
-/
inductive IllegalCopy : CakeEvent → Prop where
  | controller2CopiesCake : IllegalCopy CakeEvent.controller2CopiesCake

/-- Example 1.2.1: exact characterization of the illegal copy event. -/
theorem illegalCopy_iff (event : CakeEvent) :
    IllegalCopy event ↔ event = controller2CopiesCake := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact IllegalCopy.controller2CopiesCake

/-- Example 1.2.1: Controller 2 illegally copies the cake. -/
theorem illegalCopy_controller2CopiesCake : IllegalCopy controller2CopiesCake := by
  exact IllegalCopy.controller2CopiesCake

end CakeEvent

end ContForm.Models.Introduction
