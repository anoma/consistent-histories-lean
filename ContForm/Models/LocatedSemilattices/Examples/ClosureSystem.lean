import ContForm.Models.LocatedSemilattices.Examples.Bureaucracy

namespace ContForm.Models.LocatedSemilattices.Examples

open ContForm.Foundation.LocatedSemilattices.Basic
open ContForm.Foundation.LocatedSemilattices.TopTrees

/-!
Example 2.3.7 (closure operators).

Attestation `#` here is controller-preserving, expansive, and idempotent /
commutative / associative on each fiber, but the paper notes it is not in general
contradiction-preserving (Definition 2.2.2(7c)), so it is "not quite a located
semilattice (yet)". The paper then offers three conditions that recover
contradiction preservation — (1) a necessary and sufficient condition, (2)
identical inferences, and (3) well-pointedness — each formalized below, together
with a counterexample showing the bare construction fails.
-/

namespace ClosureSystemExample

universe u v

/-- Predicate inclusion for fact sets in the closure-operator example. -/
def subset {Fact : Type u} (A B : Fact → Prop) : Prop :=
  ∀ fact, A fact → B fact

/-- Predicate union for fact sets in the closure-operator example. -/
def setUnion {Fact : Type u} (A B : Fact → Prop) : Fact → Prop :=
  fun fact => A fact ∨ B fact

/-- Empty fact set in the closure-operator example. -/
def emptyFacts {Fact : Type u} : Fact → Prop :=
  fun _ => False

/-- Total fact set in the closure-operator example. -/
def topFacts {Fact : Type u} : Fact → Prop :=
  fun _ => True

/-- Two-fact witness set used by the well-pointed contradiction condition. -/
def pairFacts {Fact : Type u} (x y : Fact) : Fact → Prop :=
  fun fact => fact = x ∨ fact = y

theorem pred_ext {Fact : Type u} {A B : Fact → Prop}
    (hAB : subset A B) (hBA : subset B A) : A = B := by
  funext fact
  apply propext
  exact ⟨hAB fact, hBA fact⟩

theorem subset_refl {Fact : Type u} (A : Fact → Prop) : subset A A := by
  intro fact hfact
  exact hfact

theorem subset_trans {Fact : Type u} {A B C : Fact → Prop}
    (hAB : subset A B) (hBC : subset B C) : subset A C := by
  intro fact hfact
  exact hBC fact (hAB fact hfact)

theorem subset_setUnion_left {Fact : Type u} (A B : Fact → Prop) :
    subset A (setUnion A B) := by
  intro fact hfact
  exact Or.inl hfact

theorem subset_setUnion_right {Fact : Type u} (A B : Fact → Prop) :
    subset B (setUnion A B) := by
  intro fact hfact
  exact Or.inr hfact

/-- Set-union monotonicity used by the closure-example time order. -/
theorem setUnion_mono {Fact : Type u} {A A' B B' : Fact → Prop}
    (hA : subset A A') (hB : subset B B') :
    subset (setUnion A B) (setUnion A' B') := by
  intro fact hfact
  cases hfact with
  | inl hfact => exact Or.inl (hA fact hfact)
  | inr hfact => exact Or.inr (hB fact hfact)

theorem subset_topFacts {Fact : Type u} (A : Fact → Prop) :
    subset A topFacts := by
  intro _fact _hfact
  trivial

/--
Example 2.3.7: a Moore family of fact sets.

The paper assumes arbitrary intersection closure and explicitly includes both
the empty and total fact sets.
-/
structure ClosureSystem (Fact : Type u) where
  closed : (Fact → Prop) → Prop
  empty_closed : closed emptyFacts
  univ_closed : closed topFacts
  inter_closed :
    ∀ {ι : Type u} (family : ι → Fact → Prop),
      (∀ i, closed (family i)) → closed (fun fact => ∀ i, family i fact)

namespace ClosureSystem

/-- Example 2.3.7: closure is the intersection of closed supersets. -/
def closure {Fact : Type u} (M : ClosureSystem Fact) (X : Fact → Prop) :
    Fact → Prop :=
  fun fact =>
    ∀ C : {C : Fact → Prop // M.closed C ∧ subset X C}, C.1 fact

/-- Example 2.3.7: the closure of a fact set is closed. -/
theorem closure_closed {Fact : Type u} (M : ClosureSystem Fact) (X : Fact → Prop) :
    M.closed (M.closure X) := by
  exact M.inter_closed
    (fun C : {C : Fact → Prop // M.closed C ∧ subset X C} => C.1)
    (fun C => C.2.1)

/-- Example 2.3.7: every fact set is contained in its closure. -/
theorem subset_closure {Fact : Type u} (M : ClosureSystem Fact) (X : Fact → Prop) :
    subset X (M.closure X) := by
  intro fact hfact C
  exact C.2.2 fact hfact

/-- Closed supersets of `X` also contain `closure X`. -/
theorem closure_subset_closed {Fact : Type u} (M : ClosureSystem Fact)
    {X C : Fact → Prop} (hC : M.closed C) (hXC : subset X C) :
    subset (M.closure X) C := by
  intro fact hfact
  exact hfact ⟨C, hC, hXC⟩

/-- Example 2.3.7: for closed `D`, `X <= D` iff `closure X <= D`. -/
theorem closure_subset_closed_iff {Fact : Type u} (M : ClosureSystem Fact)
    {X D : Fact → Prop} (hD : M.closed D) :
    subset (M.closure X) D ↔ subset X D := by
  constructor
  · intro hclosure
    exact subset_trans (M.subset_closure X) hclosure
  · intro hX
    exact M.closure_subset_closed hD hX

theorem closure_eq_of_mutual_subset_closure {Fact : Type u} (M : ClosureSystem Fact)
    {X Y : Fact → Prop}
    (hXY : subset X (M.closure Y)) (hYX : subset Y (M.closure X)) :
    M.closure X = M.closure Y := by
  apply pred_ext
  · exact M.closure_subset_closed (M.closure_closed Y) hXY
  · exact M.closure_subset_closed (M.closure_closed X) hYX

theorem closure_mono {Fact : Type u} (M : ClosureSystem Fact)
    {X Y : Fact → Prop} (hXY : subset X Y) :
    subset (M.closure X) (M.closure Y) := by
  exact M.closure_subset_closed (M.closure_closed Y)
    (subset_trans hXY (M.subset_closure Y))

theorem closure_eq_topFacts_of_subset_closure_eq_topFacts {Fact : Type u}
    (M : ClosureSystem Fact) {X Y : Fact → Prop}
    (hXY : subset X Y) (hXtop : M.closure X = topFacts) :
    M.closure Y = topFacts := by
  apply pred_ext
  · exact subset_topFacts (M.closure Y)
  · intro fact _hfact
    have hmemX : M.closure X fact := by
      rw [hXtop]
      trivial
    exact M.closure_mono hXY fact hmemX

theorem setUnion_subset_iff {Fact : Type u} {X Y D : Fact → Prop} :
    subset (setUnion X Y) D ↔ subset X D ∧ subset Y D := by
  constructor
  · intro h
    constructor
    · intro fact hfact
      exact h fact (Or.inl hfact)
    · intro fact hfact
      exact h fact (Or.inr hfact)
  · intro h fact hfact
    cases hfact with
    | inl hx => exact h.1 fact hx
    | inr hy => exact h.2 fact hy

/-- Example 2.3.7: `closure (closure X union Y) = closure (X union Y)`. -/
theorem closure_setUnion_absorb_left {Fact : Type u} (M : ClosureSystem Fact)
    (X Y : Fact → Prop) :
    M.closure (setUnion (M.closure (setUnion X Y)) X) =
      M.closure (setUnion X Y) := by
  apply M.closure_eq_of_mutual_subset_closure
  · intro fact hfact
    cases hfact with
    | inl hclosed => exact hclosed
    | inr hx => exact M.subset_closure (setUnion X Y) fact (Or.inl hx)
  · intro fact hfact
    cases hfact with
    | inl hx =>
        exact M.subset_closure (setUnion (M.closure (setUnion X Y)) X) fact (Or.inr hx)
    | inr hy =>
        exact M.subset_closure (setUnion (M.closure (setUnion X Y)) X) fact
          (Or.inl (M.subset_closure (setUnion X Y) fact (Or.inr hy)))

/-- Example 2.3.7: closure-union associativity, left-associated form. -/
theorem closure_setUnion_assoc {Fact : Type u} (M : ClosureSystem Fact)
    (X Y Z : Fact → Prop) :
    M.closure (setUnion (M.closure (setUnion X Y)) Z) =
      M.closure (setUnion X (setUnion Y Z)) := by
  apply M.closure_eq_of_mutual_subset_closure
  · intro fact hfact
    cases hfact with
    | inl hclosed =>
        exact M.closure_subset_closed (M.closure_closed (setUnion X (setUnion Y Z)))
          (by
            intro fact hxy
            cases hxy with
            | inl hx => exact M.subset_closure _ fact (Or.inl hx)
            | inr hy => exact M.subset_closure _ fact (Or.inr (Or.inl hy)))
          fact hclosed
    | inr hz => exact M.subset_closure _ fact (Or.inr (Or.inr hz))
  · intro fact hfact
    cases hfact with
    | inl hx =>
        exact M.subset_closure (setUnion (M.closure (setUnion X Y)) Z) fact
          (Or.inl (M.subset_closure (setUnion X Y) fact (Or.inl hx)))
    | inr hyz =>
        cases hyz with
        | inl hy =>
            exact M.subset_closure (setUnion (M.closure (setUnion X Y)) Z) fact
              (Or.inl (M.subset_closure (setUnion X Y) fact (Or.inr hy)))
        | inr hz =>
            exact M.subset_closure (setUnion (M.closure (setUnion X Y)) Z) fact
              (Or.inr hz)

/-- Example 2.3.7: closure-union associativity, right-associated form. -/
theorem closure_setUnion_assoc_right {Fact : Type u} (M : ClosureSystem Fact)
    (X Y Z : Fact → Prop) :
    M.closure (setUnion X (M.closure (setUnion Y Z))) =
      M.closure (setUnion X (setUnion Y Z)) := by
  apply M.closure_eq_of_mutual_subset_closure
  · intro fact hfact
    cases hfact with
    | inl hx => exact M.subset_closure _ fact (Or.inl hx)
    | inr hclosed =>
        exact M.closure_subset_closed (M.closure_closed (setUnion X (setUnion Y Z)))
          (by
            intro fact hyz
            cases hyz with
            | inl hy => exact M.subset_closure _ fact (Or.inr (Or.inl hy))
            | inr hz => exact M.subset_closure _ fact (Or.inr (Or.inr hz)))
          fact hclosed
  · intro fact hfact
    cases hfact with
    | inl hx =>
        exact M.subset_closure (setUnion X (M.closure (setUnion Y Z))) fact (Or.inl hx)
    | inr hyz =>
        cases hyz with
        | inl hy =>
            exact M.subset_closure (setUnion X (M.closure (setUnion Y Z))) fact
              (Or.inr (M.subset_closure (setUnion Y Z) fact (Or.inl hy)))
        | inr hz =>
            exact M.subset_closure (setUnion X (M.closure (setUnion Y Z))) fact
              (Or.inr (M.subset_closure (setUnion Y Z) fact (Or.inr hz)))

/-- Example 2.3.7: `closure (X ∪ X) = X` for closed `X` (idempotence). -/
theorem closure_setUnion_self_of_closed {Fact : Type u} (M : ClosureSystem Fact)
    {X : Fact → Prop} (hX : M.closed X) :
    M.closure (setUnion X X) = X := by
  apply pred_ext
  · exact M.closure_subset_closed hX (by
      intro fact hfact
      cases hfact with
      | inl hx => exact hx
      | inr hx => exact hx)
  · intro fact hx
    exact M.subset_closure (setUnion X X) fact (Or.inl hx)

/-- Example 2.3.7: `closure (∅ ∪ X) = X` for closed `X` (bottom is a left identity). -/
theorem closure_setUnion_empty_left_of_closed {Fact : Type u} (M : ClosureSystem Fact)
    {X : Fact → Prop} (hX : M.closed X) :
    M.closure (setUnion emptyFacts X) = X := by
  apply pred_ext
  · exact M.closure_subset_closed hX (by
      intro fact hfact
      cases hfact with
      | inl hfalse => exact False.elim hfalse
      | inr hx => exact hx)
  · intro fact hx
    exact M.subset_closure (setUnion emptyFacts X) fact (Or.inr hx)

/-- Example 2.3.7: `closure (∅ ∪ X) = closure X`. -/
theorem closure_setUnion_empty_left {Fact : Type u} (M : ClosureSystem Fact)
    (X : Fact → Prop) :
    M.closure (setUnion emptyFacts X) = M.closure X := by
  apply M.closure_eq_of_mutual_subset_closure
  · intro fact hfact
    cases hfact with
    | inl hfalse => exact False.elim hfalse
    | inr hx => exact M.subset_closure X fact hx
  · intro fact hx
    exact M.subset_closure (setUnion emptyFacts X) fact (Or.inr hx)

/-- Example 2.3.7: pre-closing the inputs does not change the closure of a union. -/
theorem closure_setUnion_closed_inputs {Fact : Type u} (M : ClosureSystem Fact)
    (X Y : Fact → Prop) :
    M.closure (setUnion (M.closure X) (M.closure Y)) =
      M.closure (setUnion X Y) := by
  apply M.closure_eq_of_mutual_subset_closure
  · intro fact hfact
    cases hfact with
    | inl hx =>
        exact M.closure_mono (subset_setUnion_left X Y) fact hx
    | inr hy =>
        exact M.closure_mono (subset_setUnion_right X Y) fact hy
  · intro fact hfact
    cases hfact with
    | inl hx =>
        exact M.subset_closure (setUnion (M.closure X) (M.closure Y)) fact
          (Or.inl (M.subset_closure X fact hx))
    | inr hy =>
        exact M.subset_closure (setUnion (M.closure X) (M.closure Y)) fact
          (Or.inr (M.subset_closure Y fact hy))

/-- Example 2.3.7: `closure (X ∪ Y) = closure (Y ∪ X)` (commutativity). -/
theorem closure_setUnion_comm {Fact : Type u} (M : ClosureSystem Fact)
    (X Y : Fact → Prop) :
    M.closure (setUnion X Y) = M.closure (setUnion Y X) := by
  apply M.closure_eq_of_mutual_subset_closure
  · intro fact hfact
    cases hfact with
    | inl hx => exact M.subset_closure _ fact (Or.inr hx)
    | inr hy => exact M.subset_closure _ fact (Or.inl hy)
  · intro fact hfact
    cases hfact with
    | inl hy => exact M.subset_closure _ fact (Or.inr hy)
    | inr hx => exact M.subset_closure _ fact (Or.inl hx)

/-- Example 2.3.7: `closure (X ∪ Fact) = Fact` (top is a right zero). -/
theorem closure_setUnion_top_right {Fact : Type u} (M : ClosureSystem Fact)
    (X : Fact → Prop) :
    M.closure (setUnion X topFacts) = topFacts := by
  apply pred_ext
  · exact subset_topFacts _
  · intro fact _hfact
    exact M.subset_closure (setUnion X topFacts) fact (Or.inr trivial)

end ClosureSystem

/-- Example 2.3.7: times are controller-indexed closed fact sets. -/
structure Time (Ctrl : Type u) (Fact : Type v)
    (infer : Ctrl → ClosureSystem Fact) where
  controller : Ctrl
  facts : Fact → Prop
  closed : (infer controller).closed facts

namespace Time

/-- Example 2.3.7: same-controller subset order on closure-example times. -/
def le {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    (t s : Time Ctrl Fact infer) : Prop :=
  t.controller = s.controller ∧ subset t.facts s.facts

/-- Example 2.3.7: reflexivity of the closure-example time order. -/
theorem le_refl {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    (t : Time Ctrl Fact infer) : le t t := by
  exact ⟨rfl, subset_refl t.facts⟩

/-- Example 2.3.7: transitivity of the closure-example time order. -/
theorem le_trans {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    {t s r : Time Ctrl Fact infer} (hts : le t s) (hsr : le s r) : le t r := by
  exact ⟨hts.1.trans hsr.1, subset_trans hts.2 hsr.2⟩

/-- Example 2.3.7: antisymmetry of the closure-example time order. -/
theorem le_antisymm {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    {t s : Time Ctrl Fact infer} (hts : le t s) (hst : le s t) : t = s := by
  cases t with
  | mk tcontroller tfacts tclosed =>
    cases s with
    | mk scontroller sfacts sclosed =>
      simp only [le] at hts hst
      rcases hts with ⟨hcontroller, hfacts⟩
      rcases hst with ⟨_hcontroller', hfacts'⟩
      subst scontroller
      have hfacts : tfacts = sfacts := pred_ext hfacts hfacts'
      subst sfacts
      rfl

theorem ext {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    {t s : Time Ctrl Fact infer} (hcontroller : t.controller = s.controller)
    (hfacts : t.facts = s.facts) : t = s := by
  cases t with
  | mk tcontroller tfacts tclosed =>
    cases s with
    | mk scontroller sfacts sclosed =>
      simp only at hcontroller hfacts
      subst scontroller
      subst sfacts
      rfl

end Time

/-- Example 2.3.7: the closure-example times controlled by `p`. -/
def timeAt {Ctrl : Type u} {Fact : Type v} (infer : Ctrl → ClosureSystem Fact)
    (p : Ctrl) : Type (max u v) :=
  {t : Time Ctrl Fact infer // t.controller = p}

/-- Example 2.3.7: bottom time `(p, empty)`. -/
def botTime {Ctrl : Type u} {Fact : Type v} (infer : Ctrl → ClosureSystem Fact)
    (p : Ctrl) : Time Ctrl Fact infer where
  controller := p
  facts := emptyFacts
  closed := (infer p).empty_closed

/-- Example 2.3.7: top time `(p, Fact)`. -/
def topTime {Ctrl : Type u} {Fact : Type v} (infer : Ctrl → ClosureSystem Fact)
    (p : Ctrl) : Time Ctrl Fact infer where
  controller := p
  facts := topFacts
  closed := (infer p).univ_closed

/-- Example 2.3.7: bottom is least within its controller fiber. -/
theorem botTime_le {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} (p : Ctrl) {t : Time Ctrl Fact infer}
    (hcontroller : t.controller = p) : Time.le (botTime infer p) t := by
  exact ⟨hcontroller.symm, by
    intro fact hfact
    cases hfact⟩

/-- Example 2.3.7: top is greatest within its controller fiber. -/
theorem le_topTime {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} (p : Ctrl) {t : Time Ctrl Fact infer}
    (hcontroller : t.controller = p) : Time.le t (topTime infer p) := by
  exact ⟨hcontroller, subset_topFacts t.facts⟩

/--
Example 2.3.7: the example data before defining
the time carrier. The source fixes a nonempty controller set and a
controller-indexed closure system on facts.
-/
structure Data where
  Ctrl : Type u
  Fact : Type v
  nonemptyCtrl : Nonempty Ctrl
  infer : Ctrl → ClosureSystem Fact

namespace Data

/-- Example 2.3.7: the fixed nonempty controller set. -/
theorem controller_nonempty (D : Data.{u, v}) : Nonempty D.Ctrl := by
  exact D.nonemptyCtrl

/-- Example 2.3.7: the closure system assigned to a controller. -/
abbrev closureSystem (D : Data.{u, v}) (p : D.Ctrl) : ClosureSystem D.Fact :=
  D.infer p

/-- Example 2.3.7: the time carrier for paper closure-example data. -/
abbrev Time (D : Data.{u, v}) : Type (max u v) :=
  ClosureSystemExample.Time D.Ctrl D.Fact D.infer

/-- Example 2.3.7: bottom time at a controller in the paper data bundle. -/
def botTime (D : Data.{u, v}) (p : D.Ctrl) : D.Time :=
  ClosureSystemExample.botTime D.infer p

/-- Example 2.3.7: top time at a controller in the paper data bundle. -/
def topTime (D : Data.{u, v}) (p : D.Ctrl) : D.Time :=
  ClosureSystemExample.topTime D.infer p

/-- Example 2.3.7: the bundled bottom time has the requested controller. -/
theorem botTime_controller (D : Data.{u, v}) (p : D.Ctrl) :
    (D.botTime p).controller = p := by
  rfl

/-- Example 2.3.7: the bundled top time has the requested controller. -/
theorem topTime_controller (D : Data.{u, v}) (p : D.Ctrl) :
    (D.topTime p).controller = p := by
  rfl

/--
Consequence of the paper's nonempty-controller premise: the example time
carrier is inhabited.
-/
theorem time_nonempty (D : Data.{u, v}) : Nonempty D.Time := by
  rcases D.nonemptyCtrl with ⟨p⟩
  exact ⟨D.botTime p⟩

end Data

/-- Example 2.3.7: closure-operator attestation. -/
def attest {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    (t s : Time Ctrl Fact infer) : Time Ctrl Fact infer where
  controller := t.controller
  facts := (infer t.controller).closure (setUnion t.facts s.facts)
  closed := (infer t.controller).closure_closed (setUnion t.facts s.facts)

/-- Example 2.3.7: the closure-operator attestation preserves controllers. -/
theorem attest_controller {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} (t s : Time Ctrl Fact infer) :
    (attest t s).controller = t.controller := by
  rfl

/-- Example 2.3.7: the left input's facts are contained in the attested facts. -/
theorem left_facts_subset_attest {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} (t s : Time Ctrl Fact infer) :
    subset t.facts (attest t s).facts := by
  intro fact hfact
  exact (infer t.controller).subset_closure (setUnion t.facts s.facts) fact (Or.inl hfact)

/-- Example 2.3.7: the right input's facts are contained in the attested facts. -/
theorem right_facts_subset_attest {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} (t s : Time Ctrl Fact infer) :
    subset s.facts (attest t s).facts := by
  intro fact hfact
  exact (infer t.controller).subset_closure (setUnion t.facts s.facts) fact (Or.inr hfact)

/-- Example 2.3.7: closure attestation is monotone for the paper time order. -/
theorem attest_monotone {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} {t t' s s' : Time Ctrl Fact infer}
    (htt' : Time.le t t') (hss' : Time.le s s') :
    Time.le (attest t s) (attest t' s') := by
  rcases htt' with ⟨hcontroller, htfacts⟩
  rcases hss' with ⟨_hscontroller, hsfacts⟩
  constructor
  · exact hcontroller
  · dsimp [attest]
    rw [← hcontroller]
    exact (infer t.controller).closure_mono (setUnion_mono htfacts hsfacts)

/-- Example 2.3.7: closure attestation is monotone in the left input. -/
theorem attest_monotone_left {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} {t t' s : Time Ctrl Fact infer}
    (htt' : Time.le t t') : Time.le (attest t s) (attest t' s) := by
  exact attest_monotone htt' (Time.le_refl s)

/-- Example 2.3.7: closure attestation is monotone in the right input. -/
theorem attest_monotone_right {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} {t s s' : Time Ctrl Fact infer}
    (hss' : Time.le s s') : Time.le (attest t s) (attest t s') := by
  exact attest_monotone (Time.le_refl t) hss'

/-- Example 2.3.7: attestation is expansive in the located-semilattice sense. -/
theorem attest_expansive {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} (t s : Time Ctrl Fact infer) :
    attest (attest t s) t = attest t s := by
  refine Time.ext (t := attest (attest t s) t) (s := attest t s) rfl ?_
  dsimp [attest]
  exact (infer t.controller).closure_setUnion_absorb_left t.facts s.facts

/-- Example 2.3.7: bottom is a left identity on each closure-example fiber. -/
theorem attest_botTime_left_same_controller {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} (p : Ctrl) {t : Time Ctrl Fact infer}
    (hcontroller : t.controller = p) :
    attest (botTime infer p) t = t := by
  refine Time.ext (t := attest (botTime infer p) t) (s := t) hcontroller.symm ?_
  dsimp [attest, botTime]
  rw [← hcontroller]
  exact (infer t.controller).closure_setUnion_empty_left_of_closed t.closed

/-- Example 2.3.7: top is a right zero on each closure-example fiber. -/
theorem attest_topTime_right_same_controller {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} (p : Ctrl) {t : Time Ctrl Fact infer}
    (hcontroller : t.controller = p) :
    attest t (topTime infer p) = topTime infer p := by
  refine Time.ext (t := attest t (topTime infer p)) (s := topTime infer p) hcontroller ?_
  dsimp [attest, topTime]
  exact (infer t.controller).closure_setUnion_top_right t.facts

/-- Example 2.3.7: same-controller attestation is idempotent. -/
theorem attest_idem {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} (t : Time Ctrl Fact infer) :
    attest t t = t := by
  refine Time.ext (t := attest t t) (s := t) rfl ?_
  dsimp [attest]
  exact (infer t.controller).closure_setUnion_self_of_closed t.closed

/-- Example 2.3.7: same-controller attestation is commutative. -/
theorem attest_comm_same_controller {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} {t s : Time Ctrl Fact infer}
    (hcontroller : t.controller = s.controller) :
    attest t s = attest s t := by
  refine Time.ext (t := attest t s) (s := attest s t) hcontroller ?_
  dsimp [attest]
  rw [← hcontroller]
  exact (infer t.controller).closure_setUnion_comm t.facts s.facts

/-- Example 2.3.7: same-controller attestation is associative. -/
theorem attest_assoc_same_controller {Ctrl : Type u} {Fact : Type v}
    {infer : Ctrl → ClosureSystem Fact} {t s u : Time Ctrl Fact infer}
    (hts : t.controller = s.controller) (_hsu : s.controller = u.controller) :
    attest (attest t s) u = attest t (attest s u) := by
  refine Time.ext (t := attest (attest t s) u) (s := attest t (attest s u)) rfl ?_
  dsimp [attest]
  rw [← hts]
  exact (infer t.controller).closure_setUnion_assoc t.facts s.facts u.facts |>.trans
    ((infer t.controller).closure_setUnion_assoc_right t.facts s.facts u.facts).symm

/--
Example 2.3.7: each closure-example controller fiber is a bounded
semilattice under attestation.
-/
instance fiberSemilattice {Ctrl : Type u} {Fact : Type v}
    (infer : Ctrl → ClosureSystem Fact) (p : Ctrl) :
    BoundedSemilattice (timeAt infer p) where
  join t s :=
    ⟨attest t.1 s.1, by
      calc
        (attest t.1 s.1).controller = t.1.controller := attest_controller t.1 s.1
        _ = p := t.2⟩
  bot := ⟨botTime infer p, rfl⟩
  top := ⟨topTime infer p, rfl⟩
  join_idem := by
    intro t
    apply Subtype.ext
    exact attest_idem t.1
  join_comm := by
    intro t s
    apply Subtype.ext
    exact attest_comm_same_controller (t.2.trans s.2.symm)
  join_assoc := by
    intro t s r
    apply Subtype.ext
    exact attest_assoc_same_controller (t.2.trans s.2.symm) (s.2.trans r.2.symm)
  bot_le := by
    intro t
    apply Subtype.ext
    exact attest_botTime_left_same_controller p t.2
  le_top := by
    intro t
    apply Subtype.ext
    exact attest_topTime_right_same_controller p t.2

/-- Example 2.3.7: same-controller contradiction — the closure of the union is all of `Fact`. -/
def Contradicts {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    (t s : Time Ctrl Fact infer) : Prop :=
  t.controller = s.controller ∧
    (infer t.controller).closure (setUnion t.facts s.facts) = topFacts

/--
Example 2.3.7, option (1): the necessary and sufficient condition — whenever some
controller's closure of `C1 ∪ C2` is all of `Fact`, so is every controller's.
-/
def ContradictionPreservingCondition {Ctrl : Type u} {Fact : Type v}
    (infer : Ctrl → ClosureSystem Fact) : Prop :=
  ∀ {p' : Ctrl} {C1 C2 : Fact → Prop},
    (infer p').closed C1 →
    (infer p').closed C2 →
    (infer p').closure (setUnion C1 C2) = topFacts →
    ∀ p : Ctrl, (infer p).closure (setUnion C1 C2) = topFacts

/-- Contradiction preservation for the closure-operator attestation operation. -/
def AttestContradictionPreserving {Ctrl : Type u} {Fact : Type v}
    (infer : Ctrl → ClosureSystem Fact) : Prop :=
  ∀ {t t' s s' : Time Ctrl Fact infer},
    t.controller = t'.controller →
    s.controller = s'.controller →
    Contradicts s s' →
    Contradicts (attest t s) (attest t' s')

/--
Example 2.3.7: option (1) is necessary and sufficient for contradiction
preservation of the closure-operator attestation.
-/
theorem contradictionPreservingCondition_iff_attestContradictionPreserving
    {Ctrl : Type u} {Fact : Type v} (infer : Ctrl → ClosureSystem Fact) :
    ContradictionPreservingCondition infer ↔
      AttestContradictionPreserving infer := by
  constructor
  · intro hcondition t t' s s' htt' _hss' hcontr
    constructor
    · exact htt'
    · dsimp [attest]
      let p := t.controller
      let base := setUnion s.facts s'.facts
      let expanded :=
        setUnion ((infer t.controller).closure (setUnion t.facts s.facts))
          ((infer t'.controller).closure (setUnion t'.facts s'.facts))
      have hs'ClosedAtS :
          (infer s.controller).closed s'.facts := by
        rw [hcontr.1]
        exact s'.closed
      have hbaseTop : (infer p).closure base = topFacts := by
        exact hcondition (p' := s.controller) (C1 := s.facts) (C2 := s'.facts)
          s.closed hs'ClosedAtS hcontr.2 p
      have hbaseExpanded : subset base expanded := by
        intro fact hfact
        cases hfact with
        | inl hs =>
            exact Or.inl
              ((infer t.controller).subset_closure (setUnion t.facts s.facts) fact
                (Or.inr hs))
        | inr hs' =>
            exact Or.inr
              ((infer t'.controller).subset_closure (setUnion t'.facts s'.facts) fact
                (Or.inr hs'))
      exact (infer p).closure_eq_topFacts_of_subset_closure_eq_topFacts
        hbaseExpanded hbaseTop
  · intro hpreserve p' C1 C2 hC1 hC2 htop p
    let left : Time Ctrl Fact infer := botTime infer p
    let right : Time Ctrl Fact infer := botTime infer p
    let s : Time Ctrl Fact infer := ⟨p', C1, hC1⟩
    let s' : Time Ctrl Fact infer := ⟨p', C2, hC2⟩
    have hcontr : Contradicts s s' := by
      exact ⟨rfl, htop⟩
    have hout := hpreserve (t := left) (t' := right) (s := s) (s' := s') rfl rfl hcontr
    dsimp [Contradicts, attest, botTime] at hout
    have hleft :
        (infer p).closure (setUnion emptyFacts C1) = (infer p).closure C1 :=
      (infer p).closure_setUnion_empty_left C1
    have hright :
        (infer p).closure (setUnion emptyFacts C2) = (infer p).closure C2 :=
      (infer p).closure_setUnion_empty_left C2
    have hcollapse :
        (infer p).closure
            (setUnion ((infer p).closure C1) ((infer p).closure C2)) =
          (infer p).closure (setUnion C1 C2) :=
      (infer p).closure_setUnion_closed_inputs C1 C2
    simpa [left, right, s, s', Contradicts, attest, botTime, hleft, hright, hcollapse]
      using hout.2

/--
Contradiction in the closure-operator example is exactly the raw
same-controller contradiction used by `LocatedSemilattice`.
-/
theorem rawContradicts_iff_contradicts
    {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    (s t : Time Ctrl Fact infer) :
    RawContradicts Time.controller attest (topTime infer) s t ↔ Contradicts s t := by
  constructor
  · intro hraw
    constructor
    · exact hraw.1
    · have hfacts := congrArg Time.facts hraw.2
      simpa [attest, topTime] using hfacts
  · intro hcontr
    constructor
    · exact hcontr.1
    · refine Time.ext (t := attest s t) (s := topTime infer s.controller) rfl ?_
      dsimp [attest, topTime]
      exact hcontr.2

/--
Example 2.3.7: under option (1), the closure-operator construction is a located
semilattice.
-/
def locatedSemilatticeOfContradictionPreservingCondition
    {Ctrl : Type u} {Fact : Type v} (infer : Ctrl → ClosureSystem Fact)
    (hcondition : ContradictionPreservingCondition infer) :
    LocatedSemilattice (Time Ctrl Fact infer) Ctrl where
  attest := attest
  controller := Time.controller
  bot := botTime infer
  top := topTime infer
  bot_controller := by
    intro p
    rfl
  top_controller := by
    intro p
    rfl
  controller_preserving := by
    intro _t _s
    rfl
  self_join_idem := by
    intro t
    exact attest_idem t
  self_join_comm := by
    intro _t _t' hcontroller
    exact attest_comm_same_controller hcontroller
  self_join_assoc := by
    intro _t _t' _u hctrl hctrl'
    exact attest_assoc_same_controller hctrl hctrl'
  self_bot_le := by
    intro p t hctrl
    subst p
    refine Time.ext (t := attest (botTime infer t.controller) t) (s := t) rfl ?_
    dsimp [attest, botTime]
    exact (infer t.controller).closure_setUnion_empty_left_of_closed t.closed
  self_le_top := by
    intro p t hctrl
    subst p
    refine Time.ext (t := attest t (topTime infer t.controller))
      (s := topTime infer t.controller) rfl ?_
    dsimp [attest, topTime]
    exact (infer t.controller).closure_setUnion_top_right t.facts
  expansive := by
    intro t s
    exact attest_expansive t s
  contradiction_preserving := by
    intro t t' s s' htt' hss' hraw
    have hpreserve : AttestContradictionPreserving infer :=
      (contradictionPreservingCondition_iff_attestContradictionPreserving infer).mp
        hcondition
    have hcontr : Contradicts s s' :=
      (rawContradicts_iff_contradicts s s').mp hraw
    exact (rawContradicts_iff_contradicts (attest t s) (attest t' s')).mpr
      (hpreserve htt' hss' hcontr)

namespace NonPreservingCounterexample

/-- Two controllers for the closure-system non-preservation witness. -/
inductive Ctrl where
  | plain
  | explosive
  deriving DecidableEq

/-- Three facts for the closure-system non-preservation witness. -/
inductive Fact where
  | a
  | b
  | c
  deriving DecidableEq

def singletonA : Fact → Prop :=
  fun fact => fact = Fact.a

def singletonB : Fact → Prop :=
  fun fact => fact = Fact.b

/-- A closure system whose closure operator is the identity. -/
def identityClosureSystem : ClosureSystem Fact where
  closed _ := True
  empty_closed := trivial
  univ_closed := trivial
  inter_closed := by
    intro _ι _family _hclosed
    trivial

theorem identity_closure_eq (X : Fact → Prop) :
    identityClosureSystem.closure X = X := by
  apply pred_ext
  · exact identityClosureSystem.closure_subset_closed trivial (subset_refl X)
  · exact identityClosureSystem.subset_closure X

/-- Closed sets for a closure system where every two distinct facts close to top. -/
def subsingletonOrTopClosed (X : Fact → Prop) : Prop :=
  (∀ x y : Fact, X x → X y → x = y) ∨ X = topFacts

/-- A closure system that closes any two distinct facts to the total fact set. -/
def explosiveClosureSystem : ClosureSystem Fact where
  closed := subsingletonOrTopClosed
  empty_closed := by
    left
    intro x _y hx _hy
    cases hx
  univ_closed := Or.inr rfl
  inter_closed := by
    intro ι family hclosed
    by_cases hexists : ∃ i : ι, family i ≠ topFacts
    · rcases hexists with ⟨i0, hi0⟩
      rcases hclosed i0 with hsub | htop
      · left
        intro x y hx hy
        exact hsub x y (hx i0) (hy i0)
      · exact False.elim (hi0 htop)
    · right
      apply pred_ext
      · exact subset_topFacts _
      · intro fact _hfact i
        have htop : family i = topFacts := by
          by_cases h : family i = topFacts
          · exact h
          · exact False.elim (hexists ⟨i, h⟩)
        rw [htop]
        trivial

theorem explosive_singletonA_closed :
    explosiveClosureSystem.closed singletonA := by
  left
  intro x y hx hy
  exact hx.trans hy.symm

theorem explosive_singletonB_closed :
    explosiveClosureSystem.closed singletonB := by
  left
  intro x y hx hy
  exact hx.trans hy.symm

theorem explosive_closure_pair_top :
    explosiveClosureSystem.closure (setUnion singletonA singletonB) = topFacts := by
  apply pred_ext
  · exact subset_topFacts _
  · intro fact _hfact C
    rcases C with ⟨D, hDclosed, hsubset⟩
    rcases hDclosed with hsub | htop
    · have ha : D Fact.a := hsubset Fact.a (Or.inl rfl)
      have hb : D Fact.b := hsubset Fact.b (Or.inr rfl)
      have hab : Fact.a = Fact.b := hsub Fact.a Fact.b ha hb
      cases hab
    · change D fact
      rw [htop]
      trivial

theorem identity_closure_pair_ne_top :
    identityClosureSystem.closure (setUnion singletonA singletonB) ≠ topFacts := by
  intro htop
  have hcClosure : identityClosureSystem.closure (setUnion singletonA singletonB) Fact.c := by
    rw [htop]
    trivial
  have hc : setUnion singletonA singletonB Fact.c := by
    simpa [identity_closure_eq] using hcClosure
  cases hc with
  | inl hcA => cases hcA
  | inr hcB => cases hcB

def infer : Ctrl → ClosureSystem Fact
  | Ctrl.plain => identityClosureSystem
  | Ctrl.explosive => explosiveClosureSystem

/--
Example 2.3.7: closure attestation is not contradiction-preserving
for arbitrary controller-indexed closure systems.
-/
theorem not_contradictionPreservingCondition :
    ¬ ContradictionPreservingCondition infer := by
  intro hcondition
  have hplainTop :
      (infer Ctrl.plain).closure (setUnion singletonA singletonB) = topFacts :=
    hcondition (p' := Ctrl.explosive) (C1 := singletonA) (C2 := singletonB)
      explosive_singletonA_closed explosive_singletonB_closed explosive_closure_pair_top
      Ctrl.plain
  exact identity_closure_pair_ne_top hplainTop

/--
Example 2.3.7: the closure attestation operation is not
contradiction-preserving without an added global condition.
-/
theorem not_attestContradictionPreserving :
    ¬ AttestContradictionPreserving infer := by
  intro hpreserve
  exact not_contradictionPreservingCondition
    ((contradictionPreservingCondition_iff_attestContradictionPreserving infer).mpr hpreserve)

end NonPreservingCounterexample

/-- Example 2.3.7, option (2): all controllers have identical closure operators. -/
def IdenticalClosures {Ctrl : Type u} {Fact : Type v}
    (infer : Ctrl → ClosureSystem Fact) : Prop :=
  ∀ p q : Ctrl, ∀ X : Fact → Prop, (infer p).closure X = (infer q).closure X

/-- Example 2.3.7: identical closure operators imply the condition above. -/
theorem contradictionPreservingCondition_of_identicalClosures
    {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    (hidentical : IdenticalClosures infer) :
    ContradictionPreservingCondition infer := by
  intro p' C1 C2 _hC1 _hC2 htop p
  calc
    (infer p).closure (setUnion C1 C2) =
        (infer p').closure (setUnion C1 C2) := by
          exact (hidentical p p' (setUnion C1 C2))
    _ = topFacts := htop

/-- Example 2.3.7: identical closure operators give a located semilattice. -/
def locatedSemilatticeOfIdenticalClosures
    {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    (hidentical : IdenticalClosures infer) :
    LocatedSemilattice (Time Ctrl Fact infer) Ctrl :=
  locatedSemilatticeOfContradictionPreservingCondition infer
    (contradictionPreservingCondition_of_identicalClosures hidentical)

/--
Example 2.3.7, option (3): well-pointedness — every contradiction is witnessed by
two globally contradictory facts.
-/
def WellPointedContradictions {Ctrl : Type u} {Fact : Type v}
    (infer : Ctrl → ClosureSystem Fact) : Prop :=
  ∀ {p' : Ctrl} {C1 C2 : Fact → Prop},
    (infer p').closed C1 →
    (infer p').closed C2 →
    (infer p').closure (setUnion C1 C2) = topFacts →
    ∃ x1 x2 : Fact,
      subset (pairFacts x1 x2) (setUnion C1 C2) ∧
        ∀ p : Ctrl, (infer p).closure (pairFacts x1 x2) = topFacts

/-- Example 2.3.7: well-pointed contradictions imply the condition above. -/
theorem contradictionPreservingCondition_of_wellPointedContradictions
    {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    (hpointed : WellPointedContradictions infer) :
    ContradictionPreservingCondition infer := by
  intro p' C1 C2 hC1 hC2 htop p
  rcases hpointed hC1 hC2 htop with ⟨x1, x2, hpairSubset, hpairTop⟩
  exact (infer p).closure_eq_topFacts_of_subset_closure_eq_topFacts
    hpairSubset (hpairTop p)

/-- Example 2.3.7: well-pointed contradictions give a located semilattice. -/
def locatedSemilatticeOfWellPointedContradictions
    {Ctrl : Type u} {Fact : Type v} {infer : Ctrl → ClosureSystem Fact}
    (hpointed : WellPointedContradictions infer) :
    LocatedSemilattice (Time Ctrl Fact infer) Ctrl :=
  locatedSemilatticeOfContradictionPreservingCondition infer
    (contradictionPreservingCondition_of_wellPointedContradictions hpointed)

end ClosureSystemExample

end ContForm.Models.LocatedSemilattices.Examples
