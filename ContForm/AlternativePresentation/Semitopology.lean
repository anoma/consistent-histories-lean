import ContForm.AlternativePresentation.Attestation

namespace ContForm.AlternativePresentation

open ContForm.Models.Cut.Consistency
open ContForm.Foundation.Cut.Structure
open ContForm.Foundation.Cut.Flags
open ContForm.Foundation.LocatedSemilattices.TopTrees
open ContForm.Foundation.LocatedSemilattices.TopTrees.BoundedSemilattice

universe u v

/-- The ambient object of Paper Example 7.4(5): a *semitopology* `X ⊆ pow(Pnt)`, i.e. a
join-subsemilattice of the powerset of a set `Pnt` that contains both `∅` and `Pnt`.
Elements are represented extensionally by their membership predicate
`asPred : Carrier → Pnt → Prop`; `bot`, `top`, and `union` interpret `∅`, `Pnt`, and `∪`,
and `ext` records that an element is determined by its predicate. -/
structure Semitopology (Pnt : Type u) where
  Carrier : Type u
  asPred : Carrier → Pnt → Prop
  bot : Carrier
  top : Carrier
  union : Carrier → Carrier → Carrier
  ext : ∀ {A B : Carrier}, asPred A = asPred B → A = B
  asPred_bot : asPred bot = fun _ => False
  asPred_top : asPred top = fun _ => True
  asPred_union : ∀ A B : Carrier, asPred (union A B) = predUnion (asPred A) (asPred B)

namespace Semitopology

/-- The bounded-semilattice structure on a semitopology from Paper Example 7.4(5):
join is set union, `⊥` is `∅` (`bot`), and `⊤` is `Pnt` (`top`). -/
instance toBoundedSemilattice {Pnt : Type u} (S : Semitopology Pnt) :
    BoundedSemilattice S.Carrier where
  join := S.union
  bot := S.bot
  top := S.top
  join_idem := by
    intro A
    apply S.ext
    rw [S.asPred_union]
    funext p
    apply propext
    constructor
    · intro h
      cases h with
      | inl hA => exact hA
      | inr hA => exact hA
    · intro hA
      exact Or.inl hA
  join_comm := by
    intro A B
    apply S.ext
    rw [S.asPred_union, S.asPred_union]
    funext p
    apply propext
    constructor
    · intro h
      cases h with
      | inl hA => exact Or.inr hA
      | inr hB => exact Or.inl hB
    · intro h
      cases h with
      | inl hB => exact Or.inr hB
      | inr hA => exact Or.inl hA
  join_assoc := by
    intro A B C
    apply S.ext
    rw [S.asPred_union, S.asPred_union, S.asPred_union, S.asPred_union]
    funext p
    apply propext
    constructor
    · intro h
      cases h with
      | inl hAB =>
          cases hAB with
          | inl hA => exact Or.inl hA
          | inr hB => exact Or.inr (Or.inl hB)
      | inr hC => exact Or.inr (Or.inr hC)
    · intro h
      cases h with
      | inl hA => exact Or.inl (Or.inl hA)
      | inr hBC =>
          cases hBC with
          | inl hB => exact Or.inl (Or.inr hB)
          | inr hC => exact Or.inr hC
  bot_le := by
    intro A
    apply S.ext
    rw [S.asPred_union, S.asPred_bot]
    funext p
    apply propext
    constructor
    · intro h
      cases h with
      | inl hFalse => exact False.elim hFalse
      | inr hA => exact hA
    · intro hA
      exact Or.inr hA
  le_top := by
    intro A
    apply S.ext
    rw [S.asPred_union, S.asPred_top]
    funext p
    apply propext
    constructor
    · intro _h
      exact True.intro
    · intro _h
      exact Or.inr True.intro

/-- In the semitopology of Paper Example 7.4(5), the inherited bounded-semilattice order
`A ≤ B` is pointwise implication of membership predicates, i.e. subset inclusion of the
underlying subsets of `Pnt`. -/
theorem le_iff
    {Pnt : Type u} (S : Semitopology Pnt)
    (A B : S.Carrier) :
    A ≤ B ↔
      ∀ p : Pnt, S.asPred A p → S.asPred B p := by
  constructor
  · intro h p hA
    have hpred :
        predUnion (S.asPred A) (S.asPred B) = S.asPred B := by
      rw [← S.asPred_union]
      exact congrArg S.asPred h
    have hp : (S.asPred A p ∨ S.asPred B p) = S.asPred B p :=
      by simpa [predUnion] using congrFun hpred p
    exact Eq.mp hp (Or.inl hA)
  · intro h
    apply S.ext
    change S.asPred (S.union A B) = S.asPred B
    rw [S.asPred_union]
    funext p
    apply propext
    constructor
    · intro hp
      cases hp with
      | inl hA => exact h p hA
      | inr hB => exact hB
    · intro hB
      exact Or.inr hB

/-- In the semitopology of Paper Example 7.4(5), `A` contradicts `B` in the sense of
Definition 7.2(1) (`A ∨ B = ⊤`) exactly when their union holds at every point, i.e.
`A ∪ B = Pnt`. -/
theorem contradicts_iff
    {Pnt : Type u} (S : Semitopology Pnt)
    (A B : S.Carrier) :
    S.toBoundedSemilattice.Contradicts A B ↔
      ∀ p : Pnt, S.asPred A p ∨ S.asPred B p := by
  constructor
  · intro h p
    have hpred :
        predUnion (S.asPred A) (S.asPred B) = S.asPred S.top := by
      rw [← S.asPred_union]
      exact congrArg S.asPred h
    have hp : (S.asPred A p ∨ S.asPred B p) = True := by
      calc
        (S.asPred A p ∨ S.asPred B p) = S.asPred S.top p := by
          change predUnion (S.asPred A) (S.asPred B) p = S.asPred S.top p
          exact congrFun hpred p
        _ = True := congrFun S.asPred_top p
    exact Eq.mp hp.symm True.intro
  · intro h
    apply S.ext
    change S.asPred (S.union A B) = S.asPred S.top
    rw [S.asPred_union, S.asPred_top]
    funext p
    apply propext
    constructor
    · intro _hp
      exact True.intro
    · intro _htrue
      exact h p

open Classical in
/-- Expansiveness bound for the attestation `#_R` of Paper Example 7.4(5): the input `O` is
below `#_R(O')(O)`, which is `O ∪ O'` when `(O,O') ∈ R` and `Pnt` otherwise. This discharges
the expansive condition of Definition 7.2(4) (`x ≤ f(x)`). -/
theorem relationUnionTopAttestation_input_le_output
    {Pnt : Type u} (S : Semitopology Pnt)
    (R : S.Carrier → S.Carrier → Prop) (input parameter : S.Carrier) :
    input ≤ (if R input parameter then S.union input parameter else S.top) := by
  by_cases hrel : R input parameter
  · simp [hrel]
    exact S.toBoundedSemilattice.le_join_left input parameter
  · simp [hrel]
    exact S.toBoundedSemilattice.le_top' input

open Classical in
/-- The parameter `O'` is below `#_R(O')(O)` in Paper Example 7.4(5): below `O ∪ O'` when
`(O,O') ∈ R` and below `Pnt` otherwise. This bound feeds the strong contradiction-preservation
proof (Definition 7.2(3)) for `#_R`. -/
theorem relationUnionTopAttestation_parameter_le_output
    {Pnt : Type u} (S : Semitopology Pnt)
    (R : S.Carrier → S.Carrier → Prop) (input parameter : S.Carrier) :
    parameter ≤ (if R input parameter then S.union input parameter else S.top) := by
  by_cases hrel : R input parameter
  · simp [hrel]
    exact S.toBoundedSemilattice.le_join_right input parameter
  · simp [hrel]
    exact S.toBoundedSemilattice.le_top' parameter

/-- The attestation `#_R` of Paper Example 7.4(5): for a relation `R ⊆ X × X`,
`#_R(O')(O) = O ∪ O'` when `(O,O') ∈ R` and `Pnt` otherwise. It is packaged as a
self-attestation (Definition 7.2(6)) on the semitopology `X`, being expansive
(Definition 7.2(4)) and strongly contradiction-preserving (Definition 7.2(3)). -/
noncomputable def relationUnionTopAttestation
    {Pnt : Type u} (S : Semitopology Pnt)
    (R : S.Carrier → S.Carrier → Prop) : SelfAttestation S.Carrier := by
  classical
  exact
    { toFun := fun parameter input =>
        if R input parameter then S.union input parameter else S.top
      expansive := by
        intro parameter input
        exact S.relationUnionTopAttestation_input_le_output R input parameter
      strongly_contradiction_preserving := by
        intro parameter parameter' hcontr input input'
        exact S.toBoundedSemilattice.contradiction_monotone
          (S.relationUnionTopAttestation_parameter_le_output R input parameter)
          (S.relationUnionTopAttestation_parameter_le_output R input' parameter')
          hcontr }

open Classical in
/-- Defining equation of `#_R` from Paper Example 7.4(5): `#_R(O')(O)` is `O ∪ O'` when
`(O,O') ∈ R` and `Pnt` otherwise. -/
theorem relationUnionTopAttestation_apply
    {Pnt : Type u} (S : Semitopology Pnt)
    (R : S.Carrier → S.Carrier → Prop) (parameter input : S.Carrier) :
    (S.relationUnionTopAttestation R).toFun parameter input =
      if R input parameter then S.union input parameter else S.top := by
  rfl

open Classical in
/-- The attestation `#_R` of Paper Example 7.4(5) viewed as its underlying map
`X → Expan(X)` (Definition 7.2(5)): `#_R(O')` is the expansive function whose value at `O`
is `O ∪ O'` when `(O,O') ∈ R` and `Pnt` otherwise. -/
theorem relationUnionTopAttestation_toExpansiveFunction_apply
    {Pnt : Type u} (S : Semitopology Pnt)
    (R : S.Carrier → S.Carrier → Prop) (parameter input : S.Carrier) :
    ((S.relationUnionTopAttestation R).toExpansiveFunction parameter).1 input =
      if R input parameter then S.union input parameter else S.top := by
  exact S.relationUnionTopAttestation_apply R parameter input

/-- On related arguments (`(O,O') ∈ R`), `#_R(O')(O) = O ∪ O'` (Paper Example 7.4(5)). -/
theorem relationUnionTopAttestation_apply_related
    {Pnt : Type u} (S : Semitopology Pnt)
    (R : S.Carrier → S.Carrier → Prop) (parameter input : S.Carrier)
    (hrel : R input parameter) :
    (S.relationUnionTopAttestation R).toFun parameter input =
      S.union input parameter := by
  rw [relationUnionTopAttestation_apply]
  simp [hrel]

/-- On unrelated arguments (`(O,O') ∉ R`), `#_R(O')(O) = Pnt` (Paper Example 7.4(5)). -/
theorem relationUnionTopAttestation_apply_unrelated
    {Pnt : Type u} (S : Semitopology Pnt)
    (R : S.Carrier → S.Carrier → Prop) (parameter input : S.Carrier)
    (hrel : ¬ R input parameter) :
    (S.relationUnionTopAttestation R).toFun parameter input = S.top := by
  rw [relationUnionTopAttestation_apply]
  simp [hrel]

open Classical in
/-- Postfix application of `#_R` from Paper Example 7.4(5) (Definition 7.2(7),
`x # y = #(y)(x)`): `O # O' = O ∪ O'` when `(O,O') ∈ R` and `Pnt` otherwise. -/
theorem relationUnionTopAttestation_postfixApply
    {Pnt : Type u} (S : Semitopology Pnt)
    (R : S.Carrier → S.Carrier → Prop) (input parameter : S.Carrier) :
    (S.relationUnionTopAttestation R).postfixApply input parameter =
      if R input parameter then S.union input parameter else S.top := by
  exact S.relationUnionTopAttestation_apply R parameter input

end Semitopology

end ContForm.AlternativePresentation
