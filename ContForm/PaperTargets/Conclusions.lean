import ContForm.AlternativePresentation

/-!
Section 8 (Conclusions), §8.2.3 (Transitive Attestation).

§8.2.3 observes that attestation is *not* transitive in general: the inequality
`t # u ≤ t # (s # u)` fails, so requiring it (a "transitive attestation") is a
genuine extra design choice rather than something the attestation axioms of
Definition 7.2 force. The paper argues transitivity is deliberately *not*
imposed here — it is more expensive and over-commits controllers — so "the lack
of structure of the not-necessarily-transitive attestations used in this paper
is a feature, not a bug".

This file substantiates that claim with an explicit witness: a self-attestation
`witnessAttestation : Attestation X X` on the four-element diamond `X` that
satisfies every clause of Definition 7.2 (expansive, strongly
contradiction-preserving) yet violates `t # u ≤ t # (s # u)`.
-/

namespace ContForm.PaperTargets.Conclusions

open ContForm.Foundation.LocatedSemilattices.TopTrees
open ContForm.AlternativePresentation
open ContForm.AlternativePresentation.NonMonotoneAttestationExample

namespace NonTransitiveAttestationCounterexample

abbrev X : Type := Diamond

/--
§8.2.3 (Transitive Attestation) witness: the underlying family `X → X → X` of
the self-attestation on the diamond `X`. By the postfix convention of
Definition 7.2(7), `x # y = witnessToFun y x`, so `witnessToFun y` is the
expansive endomap contributed by attesting parameter `y`. Parameter `bot` acts
by `nonmonotoneEndomap` (so base `bot ↦ left` and `right ↦ right`); parameter
`right` sends base `bot ↦ right`. These two choices are what make the
transitivity inequality `t # u ≤ t # (s # u)` fail (see `witness_not_transitive`).
-/
def witnessToFun : X → X → X
  | Diamond.bot, x => nonmonotoneEndomap x
  | Diamond.left, _ => Diamond.top
  | Diamond.right, Diamond.bot => Diamond.right
  | Diamond.right, Diamond.left => Diamond.top
  | Diamond.right, Diamond.right => Diamond.right
  | Diamond.right, Diamond.top => Diamond.top
  | Diamond.top, _ => Diamond.top

/-- §8.2.3 witness component: each parameter's endomap is expansive in the sense
of Definition 7.2(4), i.e. `x ≤ witnessToFun y x` for every base `x`. Required
for `witnessAttestation` to be an attestation. -/
theorem witness_expansive (y : X) :
    Expansive X (witnessToFun y) := by
  intro x
  cases y <;> cases x <;> rfl

/--
§8.2.3 witness component: the family is strongly contradiction-preserving in the
sense of Definition 7.2(3): contradictory attesting parameters `y 🗲 y'` produce
contradictory outputs `witnessToFun y x 🗲 witnessToFun y' x'` for all bases
`x, x'`. Required for `witnessAttestation` to be an attestation.
-/
theorem witness_strongly_contradiction_preserving :
    StronglyContradictionPreserving X X witnessToFun := by
  intro y y' hcontr x x'
  cases y <;> cases y' <;> cases x <;> cases x' <;> try cases hcontr <;> rfl

/-- §8.2.3 witness: the self-attestation `X ⫫ X` of Definition 7.2(5),(6),
assembled from the expansive (`witness_expansive`), strongly
contradiction-preserving (`witness_strongly_contradiction_preserving`) family
`witnessToFun`. It meets every attestation clause yet fails transitivity. -/
def witnessAttestation : Attestation X X where
  toFun := witnessToFun
  expansive := witness_expansive
  strongly_contradiction_preserving := witness_strongly_contradiction_preserving

/--
§8.2.3: the transitivity inequality `t # u ≤ t # (s # u)` fails for the valid
self-attestation `witnessAttestation` at `t = u = bot`, `s = right`. Concretely
`t # u = bot # bot = left` while `t # (s # u) = bot # right = right`, and
`left ⋠ right` in the diamond.
-/
theorem witness_not_transitive :
    ¬ (witnessAttestation.postfixApply Diamond.bot Diamond.bot) ≤ (witnessAttestation.postfixApply Diamond.bot
        (witnessAttestation.postfixApply Diamond.right Diamond.bot)) := by
  exact diamond_left_not_le_right

/--
§8.2.3: attestation is not transitive in general. There is a bounded
semilattice, a self-attestation on it (Definition 7.2(5),(6)), and elements
`t, s, u` for which `t # u ≤ t # (s # u)` fails — witnessed by
`witnessAttestation` on the diamond. This shows transitive attestation is a
genuine extra requirement, not a consequence of the attestation axioms.
-/
theorem exists_attestation_not_transitive :
    ∃ (X : Type) (iX : BoundedSemilattice X) (A : @Attestation X X iX iX) (t s u : X),
      ¬ @BoundedSemilattice.le X iX
        (A.postfixApply t u) (A.postfixApply t (A.postfixApply s u)) := by
  exact
    ⟨X, diamondSemilattice, witnessAttestation, Diamond.bot, Diamond.right, Diamond.bot,
      witness_not_transitive⟩

end NonTransitiveAttestationCounterexample

end ContForm.PaperTargets.Conclusions
