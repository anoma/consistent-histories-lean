import ConsistentHistories.Models.Cut.InductiveConstruction

namespace ConsistentHistories.AlternativePresentation

open ConsistentHistories.Models.Cut.Consistency
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.Cut.Flags
open ConsistentHistories.Foundation.LocatedSemilattices.TopTrees
open ConsistentHistories.Foundation.LocatedSemilattices.TopTrees.BoundedSemilattice

universe u v

/-- Definition 7.2 clause (2): the pointwise bounded semilattice on the set `Y → X`
of all functions, inheriting its structure from `X`. -/
instance functionSemilattice (Y : Type u) (X : Type v) [BoundedSemilattice X] :
    BoundedSemilattice (Y → X) where
  join F G := fun y => (F y) ⊔ (G y)
  bot := fun _ => (⊥ : X)
  top := fun _ => (⊤ : X)
  join_idem := by
    intro F
    funext y
    exact BoundedSemilattice.join_idem (F y)
  join_comm := by
    intro F G
    funext y
    exact BoundedSemilattice.join_comm (F y) (G y)
  join_assoc := by
    intro F G H
    funext y
    exact BoundedSemilattice.join_assoc (F y) (G y) (H y)
  bot_le := by
    intro F
    funext y
    exact BoundedSemilattice.bot_le (F y)
  le_top := by
    intro F
    funext y
    exact BoundedSemilattice.le_top (F y)

/-- Definition 7.2 clause (2)(b): bottom in the function semilattice is `λy.⊥_X`. -/
theorem functionSemilattice_bot_apply
    (Y : Type u) (X : Type v) [BoundedSemilattice X] (y : Y) :
    (functionSemilattice Y X).bot y = (⊥ : X) := by
  rfl

/-- Definition 7.2 clause (2)(c): top in the function semilattice is `λy.⊤_X`. -/
theorem functionSemilattice_top_apply
    (Y : Type u) (X : Type v) [BoundedSemilattice X] (y : Y) :
    (functionSemilattice Y X).top y = (⊤ : X) := by
  rfl

/-- Definition 7.2 clause (2)(d): join in the function semilattice is `λy.(F y ∨_X F' y)`. -/
theorem functionSemilattice_join_apply
    (Y : Type u) (X : Type v) [BoundedSemilattice X]
    (F G : Y → X) (y : Y) :
    (functionSemilattice Y X).join F G y = (F y) ⊔ (G y) := by
  rfl

/-- Definition 7.2 clause (2)(a): order in the function semilattice is `∀y. F y ≤_X F' y`. -/
theorem functionSemilattice_le_iff
    (Y : Type u) (X : Type v) [BoundedSemilattice X] (F G : Y → X) :
    (functionSemilattice Y X).le F G ↔ ∀ y : Y, (F y) ≤ (G y) := by
  constructor
  · intro h y
    exact congrFun h y
  · intro h
    funext y
    exact h y

/-- Definition 7.2 clauses (1),(2): contradiction (`F ∨ F' = ⊤`) in the function
semilattice holds exactly when `F y 🗲 F' y` pointwise for every `y`. -/
theorem functionSemilattice_contradicts_iff
    (Y : Type u) (X : Type v) [BoundedSemilattice X] (F G : Y → X) :
    (functionSemilattice Y X).Contradicts F G ↔
      ∀ y : Y, (F y) 🗲 (G y) := by
  constructor
  · intro h y
    exact congrFun h y
  · intro h
    funext y
    exact h y

/-- Definition 7.2 clause (3): a function `F : Y → X → X` is strongly
contradiction-preserving when `y 🗲 y' ⟹ ∀x,x'. F(y)(x) 🗲 F(y')(x')`. -/
def StronglyContradictionPreserving (Y : Type u) [BoundedSemilattice Y]
    (X : Type v) [BoundedSemilattice X] (F : Y → X → X) : Prop :=
  ∀ {y y' : Y}, y 🗲 y' →
    ∀ x x' : X, (F y x) 🗲 (F y' x')

/-- Definition 7.2 clause (4): `f : X → X` is expansive when `∀x. x ≤_X f(x)`. -/
def Expansive (X : Type u) [BoundedSemilattice X] (f : X → X) : Prop :=
  ∀ x : X, x ≤ (f x)

/-- Definition 7.2 clause (4): the identity endomap `λx.x` (the `⊥` of `Expan(X)`) is expansive. -/
theorem expansive_id (X : Type u) [BoundedSemilattice X] :
    Expansive X (fun x : X => x) := by
  intro x
  exact BoundedSemilattice.le_refl x

/-- Definition 7.2 clause (4): the constant-top endomap `λx.⊤_X` (the `⊤` of `Expan(X)`) is expansive. -/
theorem expansive_const_top (X : Type u) [BoundedSemilattice X] :
    Expansive X (fun _x : X => (⊤ : X)) := by
  intro x
  exact BoundedSemilattice.le_top' x

/-- Definition 7.2 clause (4): pointwise join preserves expansiveness, so `Expan(X)` is closed under join. -/
theorem expansive_join (X : Type u) [BoundedSemilattice X] {f g : X → X}
    (hf : Expansive X f) (_hg : Expansive X g) :
    Expansive X (fun x : X => (f x) ⊔ (g x)) := by
  intro x
  exact BoundedSemilattice.le_trans (hf x) (BoundedSemilattice.le_join_left (f x) (g x))

/-- Definition 7.2 clause (4): `Expan(X)`, the set of expansive self-maps of `X`. -/
abbrev expansiveFunctionSemilattice (X : Type u) [BoundedSemilattice X] : Type u :=
  {f : X → X // Expansive X f}

instance instExpansiveFunctionSemilattice (X : Type u) [BoundedSemilattice X] :
    BoundedSemilattice (expansiveFunctionSemilattice X) where
  join F G :=
    ⟨fun x => (F.1 x) ⊔ (G.1 x), expansive_join X F.2 G.2⟩
  bot := ⟨fun x => x, expansive_id X⟩
  top := ⟨fun _x => (⊤ : X), expansive_const_top X⟩
  join_idem := by
    intro F
    apply Subtype.ext
    funext x
    exact BoundedSemilattice.join_idem (F.1 x)
  join_comm := by
    intro F G
    apply Subtype.ext
    funext x
    exact BoundedSemilattice.join_comm (F.1 x) (G.1 x)
  join_assoc := by
    intro F G H
    apply Subtype.ext
    funext x
    exact BoundedSemilattice.join_assoc (F.1 x) (G.1 x) (H.1 x)
  bot_le := by
    intro F
    apply Subtype.ext
    funext x
    exact F.2 x
  le_top := by
    intro F
    apply Subtype.ext
    funext x
    exact BoundedSemilattice.le_top' (F.1 x)

/-- Definition 7.2 clause (4): `⊥_{Expan(X)} = λx.x`, the identity function. -/
theorem expansiveFunctionSemilattice_bot_apply
    (X : Type u) [BoundedSemilattice X] (x : X) :
    (⊥ : expansiveFunctionSemilattice X).1 x = x := by
  rfl

/-- Definition 7.2 clause (4): `⊤_{Expan(X)} = λx.⊤_X`, the constant-top function. -/
theorem expansiveFunctionSemilattice_top_apply
    (X : Type u) [BoundedSemilattice X] (x : X) :
    (⊤ : expansiveFunctionSemilattice X).1 x = (⊤ : X) := by
  rfl

/-- Definition 7.2 clause (4): join in `Expan(X)` is the pointwise join of clause (2)(d). -/
theorem expansiveFunctionSemilattice_join_apply
    (X : Type u) [BoundedSemilattice X]
    (F G : expansiveFunctionSemilattice X) (x : X) :
    (F ⊔ G).1 x =
      (F.1 x) ⊔ (G.1 x) := by
  rfl

/-- Definition 7.2 clause (4): `f ≤_{Expan(X)} g ⟺ ∀x. f(x) ≤_X g(x)`, the pointwise order. -/
theorem expansiveFunctionSemilattice_le_iff
    (X : Type u) [BoundedSemilattice X] (F G : expansiveFunctionSemilattice X) :
    BoundedSemilattice.le F G ↔
      ∀ x : X, BoundedSemilattice.le (F.1 x) (G.1 x) := by
  constructor
  · intro h x
    exact congrFun (congrArg Subtype.val h) x
  · intro h
    apply Subtype.ext
    funext x
    exact h x

/-- Definition 7.2 clauses (1),(4): contradiction in `Expan(X)` holds exactly when
`F.1 x 🗲 G.1 x` pointwise for every `x`. -/
theorem expansiveFunctionSemilattice_contradicts_iff
    (X : Type u) [BoundedSemilattice X] (F G : expansiveFunctionSemilattice X) :
    F 🗲 G ↔
      ∀ x : X, (F.1 x) 🗲 (G.1 x) := by
  constructor
  · intro h x
    exact congrFun (congrArg Subtype.val h) x
  · intro h
    apply Subtype.ext
    funext x
    exact h x

/-- Definition 7.2 clauses (4),(5): the attestation structure `Y ⇛ X`, bundling
the two conditions on `toFun : Y → X → X` — each `toFun y` is expansive (so the
family lands in `Expan(X)`) and the family is strongly contradiction-preserving. -/
structure Attestation (Y : Type u) (X : Type v) [BoundedSemilattice Y] [BoundedSemilattice X] where
  toFun : Y → X → X
  expansive : ∀ y : Y, Expansive X (toFun y)
  strongly_contradiction_preserving : StronglyContradictionPreserving Y X toFun

/--
Definition 7.2: the displayed view of an attestation
as a family `Y → Expan(X)`, with the paper's cross-input strong contradiction
condition kept explicit.
-/
def StronglyContradictionPreservingExpansiveFamily
    (Y : Type u) [BoundedSemilattice Y] (X : Type v) [BoundedSemilattice X]
    (F : Y → expansiveFunctionSemilattice X) : Prop :=
  ∀ {y y' : Y}, y 🗲 y' →
    ∀ x x' : X, ((F y).1 x) 🗲 ((F y').1 x')

namespace Attestation

/-- Definition 7.2 clause (7): postfix application convention `x # y = #(y)(x)`. -/
def postfixApply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) (x : X) (y : Y) : X :=
  A.toFun y x

/-- Definition 7.2 clause (7): postfix application unfolds to the stored attestation function. -/
theorem postfixApply_eq_toFun
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) (x : X) (y : Y) :
    A.postfixApply x y = A.toFun y x := by
  rfl

/-- Definition 7.2: the map from an attestation to its `Y → Expan(X)` family. -/
def toExpansiveFunction
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) (y : Y) : expansiveFunctionSemilattice X :=
  ⟨A.toFun y, A.expansive y⟩

theorem toExpansiveFunction_apply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) (y : Y) (x : X) :
    (A.toExpansiveFunction y).1 x = A.toFun y x := by
  rfl

theorem toExpansiveFunction_strongly_contradiction_preserving
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) :
    StronglyContradictionPreservingExpansiveFamily Y X A.toExpansiveFunction := by
  intro y y' hcontr x x'
  exact A.strongly_contradiction_preserving hcontr x x'

/--
Definition 7.2 consequence: the `Y → Expan(X)` family preserves ordinary
pointwise contradiction in `Expan(X)`. The definition still requires the
stronger cross-input condition above.
-/
theorem toExpansiveFunction_contradicts
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) {y y' : Y} (hcontr : y 🗲 y') :
    (A.toExpansiveFunction y) 🗲 (A.toExpansiveFunction y') := by
  exact (expansiveFunctionSemilattice_contradicts_iff X
    (A.toExpansiveFunction y) (A.toExpansiveFunction y')).mpr
    (fun x => A.strongly_contradiction_preserving hcontr x x)

/--
Definition 7.2: build an attestation from a family
`Y → Expan(X)` satisfying the paper's strong contradiction condition.
-/
def ofExpansiveFunction
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (F : Y → expansiveFunctionSemilattice X)
    (hstrong : StronglyContradictionPreservingExpansiveFamily Y X F) :
    Attestation Y X where
  toFun y x := (F y).1 x
  expansive := by
    intro y
    exact (F y).2
  strongly_contradiction_preserving := by
    intro y y' hcontr x x'
    exact hstrong hcontr x x'

/-- Definition 7.2: the inverse construction applies as the family. -/
theorem ofExpansiveFunction_apply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (F : Y → expansiveFunctionSemilattice X)
    (hstrong : StronglyContradictionPreservingExpansiveFamily Y X F)
    (y : Y) (x : X) :
    (ofExpansiveFunction F hstrong).toFun y x = (F y).1 x := by
  rfl

/--
Definition 7.2: converting the inverse construction back to `Y → Expan(X)`
returns the original family.
-/
theorem toExpansiveFunction_ofExpansiveFunction
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (F : Y → expansiveFunctionSemilattice X)
    (hstrong : StronglyContradictionPreservingExpansiveFamily Y X F) :
    (ofExpansiveFunction F hstrong).toExpansiveFunction = F := by
  funext y
  apply Subtype.ext
  rfl

end Attestation

/-- Definition 7.2, the bundled structure is exactly the paper's two conditions. -/
theorem exists_attestation_with_toFun_iff
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (F : Y → X → X) :
    (∃ A : Attestation Y X, A.toFun = F) ↔
      (∀ y : Y, Expansive X (F y)) ∧ StronglyContradictionPreserving Y X F := by
  constructor
  · intro h
    rcases h with ⟨A, hA⟩
    constructor
    · intro y
      simpa [hA] using A.expansive y
    · intro y y' hcontr x x'
      simpa [hA] using A.strongly_contradiction_preserving hcontr x x'
  · intro h
    let A : Attestation Y X :=
      { toFun := F
        expansive := h.1
        strongly_contradiction_preserving := by
          intro y y' hcontr x x'
          exact h.2 hcontr x x' }
    exact ⟨A, rfl⟩

/--
Definition 7.2: a family `Y → Expan(X)` is an
attestation exactly when it satisfies the paper's strong contradiction
condition.
-/
theorem exists_attestation_with_toExpansiveFunction_iff
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (F : Y → expansiveFunctionSemilattice X) :
    (∃ A : Attestation Y X, A.toExpansiveFunction = F) ↔
      StronglyContradictionPreservingExpansiveFamily Y X F := by
  constructor
  · intro h
    rcases h with ⟨A, hA⟩
    rw [← hA]
    exact A.toExpansiveFunction_strongly_contradiction_preserving
  · intro h
    let A : Attestation Y X :=
      { toFun := fun y x => (F y).1 x
        expansive := by
          intro y
          exact (F y).2
        strongly_contradiction_preserving := by
          intro y y' hcontr x x'
          exact h hcontr x x' }
    refine ⟨A, ?_⟩
    funext y
    apply Subtype.ext
    rfl

theorem attestation_ext
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A B : Attestation Y X} (h : A.toFun = B.toFun) : A = B := by
  cases A
  cases B
  cases h
  rfl

namespace Attestation

/--
Definition 7.2: the `Y → Expan(X)` representation determines the bundled
attestation.
-/
theorem toExpansiveFunction_injective
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X] :
    Function.Injective (fun A : Attestation Y X => A.toExpansiveFunction) := by
  intro A B h
  apply attestation_ext
  funext y x
  exact congrFun (congrArg Subtype.val (congrFun h y)) x

/--
Definition 7.2: rebuilding an attestation from its `Y → Expan(X)` family
returns the original bundled attestation.
-/
theorem ofExpansiveFunction_toExpansiveFunction
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) :
    ofExpansiveFunction A.toExpansiveFunction
      A.toExpansiveFunction_strongly_contradiction_preserving = A := by
  apply toExpansiveFunction_injective
  exact toExpansiveFunction_ofExpansiveFunction
    A.toExpansiveFunction A.toExpansiveFunction_strongly_contradiction_preserving

/-- Definition 7.2 clause (4): each `toFun y` is expansive, so the input `x` lies below the output. -/
theorem apply_le
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) (y : Y) (x : X) :
    x ≤ (A.toFun y x) := by
  exact A.expansive y x

/-- Definition 7.2 clauses (4),(7): postfix attestation application `x # y` is expansive in `x`. -/
theorem le_postfixApply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) (x : X) (y : Y) :
    x ≤ (A.postfixApply x y) := by
  exact A.apply_le y x

/--
Definition 7.2 clause (3): the strong contradiction-preservation carried by every
attestation — contradictory parameters `y 🗲 y'` force `F(y)(x) 🗲 F(y')(x')` for all
inputs `x`, `x'`.
-/
theorem apply_contradicts_apply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) {y y' : Y}
    (hcontr : y 🗲 y') (x x' : X) :
    (A.toFun y x) 🗲 (A.toFun y' x') := by
  exact A.strongly_contradiction_preserving hcontr x x'

/--
Definition 7.2 clauses (3),(7): postfix form of strong contradiction-preservation,
`y 🗲 y' ⟹ (x # y) 🗲 (x' # y')` for all inputs.
-/
theorem postfixApply_contradicts_postfixApply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) {y y' : Y}
    (hcontr : y 🗲 y') (x x' : X) :
    (A.postfixApply x y) 🗲 (A.postfixApply x' y') := by
  exact A.apply_contradicts_apply hcontr x x'

end Attestation

/-- Definition 7.2 clause (6): a self-attestation is an attestation `X ⇛ X`. -/
abbrev SelfAttestation (X : Type u) [BoundedSemilattice X] :=
  Attestation X X

/-- Bounded-semilattice morphisms `Y → X` (preserving join, `⊥`, `⊤`), the data for the
principal attestation of Example 7.4(2) and the bottom-or-top attestation of Example 7.4(4). -/
structure BoundedSemilatticeMorphism
    (Y : Type u) [BoundedSemilattice Y] (X : Type v) [BoundedSemilattice X] where
  toFun : Y → X
  map_join : ∀ y y' : Y, toFun (y ⊔ y') = (toFun y) ⊔ (toFun y')
  map_bot : toFun (⊥ : Y) = (⊥ : X)
  map_top : toFun (⊤ : Y) = (⊤ : X)

theorem BoundedSemilatticeMorphism.map_contradicts
    {Y : Type u} [BoundedSemilattice Y]
    {X : Type v} [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) {y y' : Y}
    (hcontr : y 🗲 y') :
    (f.toFun y) 🗲 (f.toFun y') := by
  have hmap := f.map_join y y'
  rw [hcontr, f.map_top] at hmap
  exact hmap.symm

theorem BoundedSemilatticeMorphism.map_le
    {Y : Type u} [BoundedSemilattice Y]
    {X : Type v} [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) {y y' : Y}
    (hle : y ≤ y') :
    (f.toFun y) ≤ (f.toFun y') := by
  have hmap := f.map_join y y'
  rw [hle] at hmap
  exact hmap.symm

namespace Attestation

/-- Definition 7.5 clause (1): an attestation is separating when, for non-`⊥` parameters
`y, y'`, any equal and consistent (non-`⊤`) outputs `x # y = x' # y'` force `y = y'`. -/
def Separating {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) : Prop :=
  ∀ y y' : Y, ∀ x x' : X,
    y ≠ (⊥ : Y) → y' ≠ (⊥ : Y) →
    A.toFun y x = A.toFun y' x' → A.toFun y x ≠ (⊤ : X) → y = y'

/-- Definition 7.5 clause (1), the displayed "equivalently" form: `(∃x,x'. x # y = x' # y'
∧ x # y ≠ ⊤) ⟹ y = y'` for non-`⊥` parameters. -/
def SeparatingExists {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) : Prop :=
  ∀ y y' : Y,
    y ≠ (⊥ : Y) → y' ≠ (⊥ : Y) →
    (∃ x x' : X, A.toFun y x = A.toFun y' x' ∧ A.toFun y x ≠ (⊤ : X)) → y = y'

/--
Injectivity of the two-input map `(y, x) ↦ x # y`. This is the ordinary injectivity
that the Definition 7.5(1) note warns is *not* the same as separating; it is comparison
vocabulary, not the paper's condition.
-/
def PairInjective {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) : Prop :=
  Function.Injective (fun p : Y × X => A.toFun p.1 p.2)

/--
Parameter-map injectivity for an attestation, i.e. injectivity of the paper's
family map `Y → Expan(X)`.
This is comparison vocabulary; it is not the paper's separating condition.
-/
def ParameterInjective {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) : Prop :=
  Function.Injective A.toFun

theorem parameterInjective_iff_toExpansiveFunction_injective
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) :
    A.ParameterInjective ↔ Function.Injective A.toExpansiveFunction := by
  constructor
  · intro hinj y y' heq
    apply hinj
    exact congrArg Subtype.val heq
  · intro hinj y y' heq
    apply hinj
    apply Subtype.ext
    exact heq

theorem separating_iff_exists {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) : A.Separating ↔ A.SeparatingExists := by
  constructor
  · intro hsep y y' hy hy' h
    rcases h with ⟨x, x', heq, hne_top⟩
    exact hsep y y' x x' hy hy' heq hne_top
  · intro hsep y y' x x' hy hy' heq hne_top
    exact hsep y y' hy hy' ⟨x, x', heq, hne_top⟩

/--
Definition 7.5 clause (1): if two attestation outputs are equal and that output is
consistent, non-`⊥` attesting parameters are equal.
-/
theorem separating_eq_of_consistent_output
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A : Attestation Y X} (hsep : A.Separating)
    {y y' : Y} {x x' : X}
    (hy : y ≠ (⊥ : Y)) (hy' : y' ≠ (⊥ : Y))
    (heq : A.toFun y x = A.toFun y' x')
    (hconsistent : BoundedSemilattice.Consistent (A.toFun y x)) :
    y = y' := by
  exact hsep y y' x x' hy hy' heq hconsistent

/--
Definition 7.5 clause (1): postfix form of separating, matching the displayed
`x # y = x' # y'` notation, on non-`⊥` parameters.
-/
theorem separating_postfix_eq_of_not_top
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A : Attestation Y X} (hsep : A.Separating)
    {y y' : Y} {x x' : X}
    (hy : y ≠ (⊥ : Y)) (hy' : y' ≠ (⊥ : Y))
    (heq : A.postfixApply x y = A.postfixApply x' y')
    (hnotTop : A.postfixApply x y ≠ (⊤ : X)) :
    y = y' := by
  exact hsep y y' x x' hy hy' heq hnotTop

theorem pairInjective_implies_separating
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A : Attestation Y X} (hinj : A.PairInjective) :
    A.Separating := by
  intro y y' x x' _hy _hy' heq _hne_top
  have hp : (y, x) = (y', x') := hinj heq
  exact congrArg Prod.fst hp

/-- Pair/output injectivity is stronger than ordinary injectivity of the family map. -/
theorem pairInjective_implies_parameterInjective
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A : Attestation Y X} (hinj : A.PairInjective) :
    A.ParameterInjective := by
  intro y y' hfun
  have hp : (y, (⊥ : X)) = (y', (⊥ : X)) := hinj (congrFun hfun (⊥ : X))
  exact congrArg Prod.fst hp

/-- Pair/output injectivity is stronger than injectivity of `Y → Expan(X)`. -/
theorem pairInjective_implies_toExpansiveFunction_injective
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A : Attestation Y X} (hinj : A.PairInjective) :
    Function.Injective A.toExpansiveFunction := by
  exact (parameterInjective_iff_toExpansiveFunction_injective A).mp
    (pairInjective_implies_parameterInjective hinj)

/-- Ordinary monotonicity for an endomap of a bounded semilattice. -/
def MonotoneEndomap (X : Type u) [BoundedSemilattice X] (f : X → X) : Prop :=
  ∀ x x' : X, x ≤ x' → (f x) ≤ (f x')

/--
Input-side monotonicity of an attestation family (`x ≤ x' ⟹ x # y ≤ x' # y`). This is
the first-component direction of Remark 7.3, distinct from the Definition 7.5(2)
parameter-side monotonicity.
-/
def InputMonotone {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) : Prop :=
  ∀ y : Y, ∀ x x' : X, x ≤ x' → (A.toFun y x) ≤ (A.toFun y x')

/--
Input-side monotonicity says exactly that each attesting parameter gives a
monotone endomap of `X`.
-/
theorem inputMonotone_iff_monotoneEndomap
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) :
    A.InputMonotone ↔ ∀ y : Y, MonotoneEndomap X (A.toFun y) := by
  rfl

/--
Postfix form of input-side monotonicity.
-/
theorem inputMonotone_postfixApply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A : Attestation Y X} (hmono : A.InputMonotone)
    (y : Y) {x x' : X} (hle : x ≤ x') :
    (A.postfixApply x y) ≤ (A.postfixApply x' y) := by
  exact hmono y x x' hle

/--
Definition 7.5 clause (2): an attestation is monotone when `y ≤ y' ⟹ ∀x. x # y ≤ x # y'`,
i.e. `# : Y → Expan(X)` is monotone for the pointwise order.
-/
def Monotone {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) : Prop :=
  ∀ {y y' : Y}, y ≤ y' → ∀ x : X, (A.toFun y x) ≤ (A.toFun y' x)

/--
Definition 7.5 clause (2): parameter monotonicity, stated as monotonicity of the
family `Y → Expan(X)`.
-/
theorem monotone_toExpansiveFunction
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A : Attestation Y X} (hmono : A.Monotone)
    {y y' : Y} (hle : y ≤ y') :
    BoundedSemilattice.le (A.toExpansiveFunction y) (A.toExpansiveFunction y') := by
  exact (expansiveFunctionSemilattice_le_iff X
    (A.toExpansiveFunction y) (A.toExpansiveFunction y')).mpr
    (fun x => hmono hle x)

/--
Definition 7.5 clause (2): the pointwise and `Y → Expan(X)` formulations of parameter
monotonicity are equivalent.
-/
theorem monotone_iff_toExpansiveFunction
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) :
    A.Monotone ↔
      ∀ {y y' : Y}, y ≤ y' →
        BoundedSemilattice.le (A.toExpansiveFunction y) (A.toExpansiveFunction y') := by
  constructor
  · intro hmono y y' hle
    exact monotone_toExpansiveFunction hmono hle
  · intro hfamily y y' hle x
    exact (expansiveFunctionSemilattice_le_iff X
      (A.toExpansiveFunction y) (A.toExpansiveFunction y')).mp
      (hfamily hle) x

/-- Alternative spelling for the paper's parameter-side `Monotone` predicate. -/
abbrev UniformlyMonotone {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (A : Attestation Y X) : Prop :=
  A.Monotone

/--
Definition 7.5 clause (2): postfix form of parameter-side monotonicity,
`y ≤ y' → x # y ≤ x # y'`.
-/
theorem monotone_postfixApply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A : Attestation Y X} (hmono : A.Monotone)
    {y y' : Y} (hle : y ≤ y') (x : X) :
    (A.postfixApply x y) ≤ (A.postfixApply x y') := by
  exact hmono hle x

theorem uniformlyMonotone_postfixApply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    {A : Attestation Y X} (hmono : A.UniformlyMonotone)
    {y y' : Y} (hle : y ≤ y') (x : X) :
    (A.postfixApply x y) ≤ (A.postfixApply x y') := by
  exact monotone_postfixApply hmono hle x

end Attestation

namespace NonMonotoneAttestationExample

/-!
Remark 7.3: an attestation need not be monotone in either component — `x ≤ x'` does
not imply `x # y ≤ x' # y`, and `y ≤ y'` does not imply `x # y ≤ x # y'`.
-/

def boolJoin : Bool → Bool → Bool
  | false, b => b
  | true, _ => true

theorem boolJoin_idem (b : Bool) : boolJoin b b = b := by
  cases b <;> rfl

theorem boolJoin_comm (b b' : Bool) : boolJoin b b' = boolJoin b' b := by
  cases b <;> cases b' <;> rfl

theorem boolJoin_assoc (b b' b'' : Bool) :
    boolJoin (boolJoin b b') b'' = boolJoin b (boolJoin b' b'') := by
  cases b <;> cases b' <;> cases b'' <;> rfl

theorem boolJoin_bot_le (b : Bool) : boolJoin false b = b := by
  cases b <;> rfl

theorem boolJoin_le_top (b : Bool) : boolJoin b true = true := by
  cases b <;> rfl

instance boolSemilattice : BoundedSemilattice Bool where
  join := boolJoin
  bot := false
  top := true
  join_idem := boolJoin_idem
  join_comm := boolJoin_comm
  join_assoc := boolJoin_assoc
  bot_le := boolJoin_bot_le
  le_top := boolJoin_le_top

theorem bool_contradicts_eq_true {y y' : Bool} :
    y 🗲 y' → y = true ∨ y' = true := by
  intro h
  change boolJoin y y' = true at h
  cases y <;> cases y' <;> simp [boolJoin] at h ⊢

inductive Diamond where
  | bot
  | left
  | right
  | top
  deriving DecidableEq

namespace Diamond

def join : Diamond → Diamond → Diamond
  | bot, x => x
  | x, bot => x
  | top, _ => top
  | _, top => top
  | left, left => left
  | right, right => right
  | left, right => top
  | right, left => top

theorem join_idem (x : Diamond) : join x x = x := by
  cases x <;> rfl

theorem join_comm (x y : Diamond) : join x y = join y x := by
  cases x <;> cases y <;> rfl

theorem join_assoc (x y z : Diamond) :
    join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem bot_le (x : Diamond) : join bot x = x := by
  cases x <;> rfl

theorem le_top (x : Diamond) : join x top = top := by
  cases x <;> rfl

end Diamond

instance diamondSemilattice : BoundedSemilattice Diamond where
  join := Diamond.join
  bot := Diamond.bot
  top := Diamond.top
  join_idem := Diamond.join_idem
  join_comm := Diamond.join_comm
  join_assoc := Diamond.join_assoc
  bot_le := Diamond.bot_le
  le_top := Diamond.le_top

def nonmonotoneEndomap : Diamond → Diamond
  | Diamond.bot => Diamond.left
  | Diamond.left => Diamond.left
  | Diamond.right => Diamond.right
  | Diamond.top => Diamond.top

def nonmonotoneAttestationToFun : Bool → Diamond → Diamond
  | true, _ => Diamond.top
  | false, x => nonmonotoneEndomap x

def nonmonotoneAttestation : Attestation Bool Diamond where
  toFun := nonmonotoneAttestationToFun
  expansive := by
    intro y x
    cases y <;> cases x <;> rfl
  strongly_contradiction_preserving := by
    intro y y' hcontr x x'
    rcases bool_contradicts_eq_true hcontr with hy | hy'
    · subst y
      cases y' <;> cases x <;> cases x' <;> rfl
    · subst y'
      cases y <;> cases x <;> cases x' <;> rfl

theorem diamond_bot_le_right : Diamond.bot ≤ Diamond.right := by
  rfl

theorem diamond_left_not_le_right :
    ¬ Diamond.left ≤ Diamond.right := by
  intro h
  change Diamond.top = Diamond.right at h
  cases h

theorem nonmonotoneAttestation_not_inputMonotone :
    ¬ nonmonotoneAttestation.InputMonotone := by
  intro hmono
  exact diamond_left_not_le_right
    (hmono false Diamond.bot Diamond.right diamond_bot_le_right)

/-- Remark 7.3, first component: attestations need not be input-monotone (`x ≤ x' ⇏ x # y ≤ x' # y`). -/
theorem exists_attestation_not_inputMonotone :
    ∃ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
      (A : @Attestation Y X iY iX),
      ¬ @Attestation.InputMonotone Y X iY iX A := by
  exact
    ⟨Bool, Diamond, boolSemilattice, diamondSemilattice, nonmonotoneAttestation,
      nonmonotoneAttestation_not_inputMonotone⟩

def nonmonotoneParameterAttestationToFun : Diamond → Bool → Bool
  | Diamond.bot, false => true
  | Diamond.bot, true => true
  | Diamond.left, x => x
  | Diamond.right, _ => true
  | Diamond.top, _ => true

def nonmonotoneParameterAttestation : Attestation Diamond Bool where
  toFun := nonmonotoneParameterAttestationToFun
  expansive := by
    intro y x
    cases y <;> cases x <;> rfl
  strongly_contradiction_preserving := by
    intro y y' hcontr x x'
    change Diamond.join y y' = Diamond.top at hcontr
    cases y <;> cases y' <;> try contradiction
    all_goals cases x <;> cases x' <;> rfl

theorem diamond_bot_le_left : Diamond.bot ≤ Diamond.left := by
  rfl

theorem bool_true_not_le_false :
    ¬ BoundedSemilattice.le (α := Bool) true false := by
  intro h
  change boolJoin true false = false at h
  cases h

theorem nonmonotoneParameterAttestation_not_monotone :
    ¬ nonmonotoneParameterAttestation.Monotone := by
  intro hmono
  exact bool_true_not_le_false
    (by
      simpa [nonmonotoneParameterAttestation, nonmonotoneParameterAttestationToFun] using
        hmono diamond_bot_le_left false)

/-- Remark 7.3, second component: attestations need not be parameter-monotone (`y ≤ y' ⇏ x # y ≤ x # y'`). -/
theorem exists_attestation_not_parameterMonotone :
    ∃ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
      (A : @Attestation Y X iY iX),
      ¬ @Attestation.Monotone Y X iY iX A := by
  exact
    ⟨Diamond, Bool, diamondSemilattice, boolSemilattice, nonmonotoneParameterAttestation,
      nonmonotoneParameterAttestation_not_monotone⟩

end NonMonotoneAttestationExample

namespace SeparatingNotInjectiveExample

/-!
Definition 7.5(1) note ("being separating is not just the condition of being
injective"): separating does not reduce to ordinary injectivity of the attestation as a
function of its two inputs. The constant-`⊤` attestation is separating yet not injective.
-/

abbrev parameterSemilattice : Type := Bool

abbrev outputSemilattice : Type := Bool

def constantTopAttestation :
    Attestation parameterSemilattice outputSemilattice where
  toFun _ _ := true
  expansive := by
    intro _y x
    cases x <;> rfl
  strongly_contradiction_preserving := by
    intro _y _y' _hcontr x x'
    cases x <;> cases x' <;> rfl

theorem constantTopAttestation_separating :
    constantTopAttestation.Separating := by
  intro _y _y' _x _x' _hy _hy' _heq hne_top
  exact False.elim (hne_top rfl)

theorem constantTopAttestation_not_pairInjective :
    ¬ constantTopAttestation.PairInjective := by
  intro hinj
  have hp :
      ((true : parameterSemilattice), (false : outputSemilattice)) =
        ((true : parameterSemilattice), (true : outputSemilattice)) :=
    hinj rfl
  have hbool : (false : Bool) = true := congrArg Prod.snd hp
  cases hbool

/--
Separating does not imply ordinary
injectivity of the attestation family map `Y → Expan(X)`.
-/
theorem constantTopAttestation_not_parameterInjective :
    ¬ constantTopAttestation.ParameterInjective := by
  intro hinj
  have hfun :
      constantTopAttestation.toFun (false : parameterSemilattice) =
        constantTopAttestation.toFun (true : parameterSemilattice) := by
    funext x
    cases x <;> rfl
  have hbool : (false : Bool) = true := hinj hfun
  cases hbool

theorem separating_not_pairInjective :
    ∃ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
      (A : @Attestation Y X iY iX),
      @Attestation.Separating Y X iY iX A ∧ ¬ @Attestation.PairInjective Y X iY iX A := by
  exact ⟨parameterSemilattice, outputSemilattice, inferInstance, inferInstance,
    constantTopAttestation,
    constantTopAttestation_separating, constantTopAttestation_not_pairInjective⟩

theorem separating_not_parameterInjective :
    ∃ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
      (A : @Attestation Y X iY iX),
      @Attestation.Separating Y X iY iX A ∧ ¬ @Attestation.ParameterInjective Y X iY iX A := by
  exact ⟨parameterSemilattice, outputSemilattice, inferInstance, inferInstance,
    constantTopAttestation,
    constantTopAttestation_separating, constantTopAttestation_not_parameterInjective⟩

end SeparatingNotInjectiveExample

namespace ParameterInjectiveNotSeparatingExample

/-!
Converse comparison boundary for the Definition 7.5(1) note: ordinary injectivity of the
attestation parameter map `Y → Expan(X)` does not imply the separating condition. Together
with `SeparatingNotInjectiveExample`, this shows separating and parameter injectivity are
independent.
-/

inductive Param where
  | bot
  | low
  | high
  | top
  deriving DecidableEq

namespace Param

def join : Param → Param → Param
  | bot, y => y
  | x, bot => x
  | top, _ => top
  | _, top => top
  | low, low => low
  | low, high => high
  | high, low => high
  | high, high => high

theorem join_idem (x : Param) : join x x = x := by
  cases x <;> rfl

theorem join_comm (x y : Param) : join x y = join y x := by
  cases x <;> cases y <;> rfl

theorem join_assoc (x y z : Param) :
    join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem bot_le (x : Param) : join bot x = x := by
  cases x <;> rfl

theorem le_top (x : Param) : join x top = top := by
  cases x <;> rfl

end Param

instance parameterSemilattice : BoundedSemilattice Param where
  join := Param.join
  bot := Param.bot
  top := Param.top
  join_idem := Param.join_idem
  join_comm := Param.join_comm
  join_assoc := Param.join_assoc
  bot_le := Param.bot_le
  le_top := Param.le_top

inductive Out where
  | bot
  | mid
  | top
  deriving DecidableEq

namespace Out

def join : Out → Out → Out
  | bot, y => y
  | x, bot => x
  | top, _ => top
  | _, top => top
  | mid, mid => mid

theorem join_idem (x : Out) : join x x = x := by
  cases x <;> rfl

theorem join_comm (x y : Out) : join x y = join y x := by
  cases x <;> cases y <;> rfl

theorem join_assoc (x y z : Out) :
    join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem bot_le (x : Out) : join bot x = x := by
  cases x <;> rfl

theorem le_top (x : Out) : join x top = top := by
  cases x <;> rfl

end Out

instance outputSemilattice : BoundedSemilattice Out where
  join := Out.join
  bot := Out.bot
  top := Out.top
  join_idem := Out.join_idem
  join_comm := Out.join_comm
  join_assoc := Out.join_assoc
  bot_le := Out.bot_le
  le_top := Out.le_top

def diagnosticToFun : Param → Out → Out
  | Param.bot, Out.bot => Out.bot
  | Param.bot, Out.mid => Out.top
  | Param.bot, Out.top => Out.top
  | Param.low, x => x
  | Param.high, Out.bot => Out.mid
  | Param.high, Out.mid => Out.mid
  | Param.high, Out.top => Out.top
  | Param.top, _ => Out.top

def diagnosticAttestation : Attestation Param Out where
  toFun := diagnosticToFun
  expansive := by
    intro y x
    cases y <;> cases x <;> rfl
  strongly_contradiction_preserving := by
    intro y y' hcontr x x'
    change Param.join y y' = Param.top at hcontr
    cases y <;> cases y' <;> try contradiction
    all_goals cases x <;> cases x' <;> rfl

theorem diagnostic_parameterInjective :
    diagnosticAttestation.ParameterInjective := by
  intro y y' hfun
  cases y <;> cases y'
  · rfl
  · have h := congrFun hfun Out.mid
    cases h
  · have h := congrFun hfun Out.bot
    cases h
  · have h := congrFun hfun Out.bot
    cases h
  · have h := congrFun hfun Out.mid
    cases h
  · rfl
  · have h := congrFun hfun Out.bot
    cases h
  · have h := congrFun hfun Out.mid
    cases h
  · have h := congrFun hfun Out.bot
    cases h
  · have h := congrFun hfun Out.bot
    cases h
  · rfl
  · have h := congrFun hfun Out.bot
    cases h
  · have h := congrFun hfun Out.bot
    cases h
  · have h := congrFun hfun Out.mid
    cases h
  · have h := congrFun hfun Out.bot
    cases h
  · rfl

/--
Ordinary parameter-map injectivity does not imply pair/output injectivity.
The distinct pairs `(low, mid)` and `(high, bot)` have the same output.
-/
theorem diagnostic_not_pairInjective :
    ¬ diagnosticAttestation.PairInjective := by
  intro hinj
  have hp :
      ((Param.low : Param), (Out.mid : Out)) =
        ((Param.high : Param), (Out.bot : Out)) :=
    hinj rfl
  have hparam : Param.low = Param.high := congrArg Prod.fst hp
  cases hparam

theorem diagnostic_not_separating :
    ¬ diagnosticAttestation.Separating := by
  intro hsep
  have hlow_ne_bot : Param.low ≠ parameterSemilattice.bot := by
    intro h
    cases h
  have hhigh_ne_bot : Param.high ≠ parameterSemilattice.bot := by
    intro h
    cases h
  have hnot_top :
      diagnosticAttestation.toFun Param.low Out.mid ≠ outputSemilattice.top := by
    intro h
    cases h
  have hflags :
      Param.low = Param.high :=
    hsep Param.low Param.high Out.mid Out.mid hlow_ne_bot hhigh_ne_bot rfl hnot_top
  cases hflags

theorem exists_parameterInjective_not_separating :
    ∃ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
      (A : @Attestation Y X iY iX),
      @Attestation.ParameterInjective Y X iY iX A ∧ ¬ @Attestation.Separating Y X iY iX A := by
  exact ⟨Param, Out, inferInstance, inferInstance, diagnosticAttestation,
    diagnostic_parameterInjective, diagnostic_not_separating⟩

theorem exists_parameterInjective_not_pairInjective :
    ∃ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
      (A : @Attestation Y X iY iX),
      @Attestation.ParameterInjective Y X iY iX A ∧ ¬ @Attestation.PairInjective Y X iY iX A := by
  exact ⟨Param, Out, inferInstance, inferInstance, diagnosticAttestation,
    diagnostic_parameterInjective, diagnostic_not_pairInjective⟩

/-- Ordinary parameter-map injectivity does not imply the paper's separating condition. -/
theorem not_parameterInjective_implies_separating :
    ¬ (∀ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
      (A : @Attestation Y X iY iX),
      @Attestation.ParameterInjective Y X iY iX A → @Attestation.Separating Y X iY iX A) := by
  intro h
  exact diagnostic_not_separating
    (h Param Out inferInstance inferInstance diagnosticAttestation
      diagnostic_parameterInjective)

/-- Injectivity of the represented family map does not imply separating. -/
theorem not_toExpansiveFunction_injective_implies_separating :
    ¬ (∀ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
      (A : @Attestation Y X iY iX),
      Function.Injective (@Attestation.toExpansiveFunction Y X iY iX A) →
        @Attestation.Separating Y X iY iX A) := by
  intro h
  exact diagnostic_not_separating
    (h Param Out inferInstance inferInstance diagnosticAttestation
      ((Attestation.parameterInjective_iff_toExpansiveFunction_injective
        diagnosticAttestation).mp diagnostic_parameterInjective))

/-- Injectivity of the represented family map does not imply pair/output injectivity. -/
theorem not_toExpansiveFunction_injective_implies_pairInjective :
    ¬ (∀ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
      (A : @Attestation Y X iY iX),
      Function.Injective (@Attestation.toExpansiveFunction Y X iY iX A) →
        @Attestation.PairInjective Y X iY iX A) := by
  intro h
  exact diagnostic_not_pairInjective
    (h Param Out inferInstance inferInstance diagnosticAttestation
      ((Attestation.parameterInjective_iff_toExpansiveFunction_injective
        diagnosticAttestation).mp diagnostic_parameterInjective))

end ParameterInjectiveNotSeparatingExample

/--
Under the ordinary parameter-map
reading of "injective", separating and injectivity of the attestation family
are independent.
-/
theorem separating_parameterInjective_independent :
    (∃ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
        (A : @Attestation Y X iY iX),
        @Attestation.Separating Y X iY iX A ∧ ¬ @Attestation.ParameterInjective Y X iY iX A) ∧
      (∃ (Y : Type) (X : Type) (iY : BoundedSemilattice Y) (iX : BoundedSemilattice X)
        (A : @Attestation Y X iY iX),
        @Attestation.ParameterInjective Y X iY iX A ∧ ¬ @Attestation.Separating Y X iY iX A) := by
  exact
    ⟨SeparatingNotInjectiveExample.separating_not_parameterInjective,
      ParameterInjectiveNotSeparatingExample.exists_parameterInjective_not_separating⟩

/-- Example 7.4(2), the principal attestation `λy.λx.(x ∨ f(y))` of a bounded-semilattice
morphism `f : Y → X`. -/
def principalAttestation
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) : Attestation Y X where
  toFun y x := x ⊔ (f.toFun y)
  expansive := by
    intro y x
    exact BoundedSemilattice.le_join_left x (f.toFun y)
  strongly_contradiction_preserving := by
    intro y y' hcontr x x'
    have hf_contr : (f.toFun y) 🗲 (f.toFun y') :=
      f.map_contradicts hcontr
    exact BoundedSemilattice.contradiction_monotone
      (BoundedSemilattice.le_join_right x (f.toFun y))
      (BoundedSemilattice.le_join_right x' (f.toFun y'))
      hf_contr

theorem principalAttestation_apply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) (x : X) :
    (principalAttestation f).toFun y x = x ⊔ (f.toFun y) := by
  rfl

/--
Example 7.4(2): the principal attestation as the displayed family `Y → Expan(X)`.
-/
theorem principalAttestation_toExpansiveFunction_apply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) (x : X) :
    ((principalAttestation f).toExpansiveFunction y).1 x =
      x ⊔ (f.toFun y) := by
  rfl

/-- Example 7.4(2): postfix form of the principal attestation, `x # y = x ∨ f(y)`. -/
theorem principalAttestation_postfixApply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (x : X) (y : Y) :
    (principalAttestation f).postfixApply x y = x ⊔ (f.toFun y) := by
  rfl

/-- Example 7.4(2): principal attestations are monotone (Definition 7.5(2)) in the attesting parameter. -/
theorem principalAttestation_monotone
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) :
    (principalAttestation f).Monotone := by
  intro y y' hyy' x
  exact BoundedSemilattice.join_le_join (BoundedSemilattice.le_refl x) (f.map_le hyy')

/--
Example 7.4(2): principal attestations are monotone as displayed families `Y → Expan(X)`.
-/
theorem principalAttestation_toExpansiveFunction_monotone
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) {y y' : Y} (hle : y ≤ y') :
    BoundedSemilattice.le ((principalAttestation f).toExpansiveFunction y) ((principalAttestation f).toExpansiveFunction y') := by
  exact Attestation.monotone_toExpansiveFunction
    (principalAttestation_monotone f) hle

/-- Alternative spelling for `principalAttestation_monotone`. -/
theorem principalAttestation_uniformlyMonotone
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) :
    (principalAttestation f).UniformlyMonotone := by
  exact principalAttestation_monotone f

/-- Example 7.4(3): the identity morphism `X → X`, exhibiting the join attestation as the
principal attestation of `f = id`. -/
def identityMorphism (X : Type u) [BoundedSemilattice X] :
    BoundedSemilatticeMorphism X X where
  toFun x := x
  map_join _ _ := rfl
  map_bot := rfl
  map_top := rfl

theorem principalAttestation_identity_apply
    (X : Type u) [BoundedSemilattice X] (y x : X) :
    (principalAttestation (identityMorphism X)).toFun y x = x ⊔ y := by
  rfl

/-- Example 7.4(3): the join self-attestation `λy.λx.(x ∨_X y)`, written `#_{∨_X}`. -/
def joinSelfAttestation (X : Type u) [BoundedSemilattice X] : SelfAttestation X where
  toFun y x := x ⊔ y
  expansive := by
    intro y x
    exact BoundedSemilattice.le_join_left x y
  strongly_contradiction_preserving := by
    intro y y' hcontr x x'
    exact BoundedSemilattice.contradiction_monotone (BoundedSemilattice.le_join_right x y) (BoundedSemilattice.le_join_right x' y') hcontr

theorem joinSelfAttestation_apply (X : Type u) [BoundedSemilattice X] (y x : X) :
    (joinSelfAttestation X).toFun y x = x ⊔ y := by
  rfl

/--
Example 7.4(3): the join self-attestation as the displayed family `X → Expan(X)`.
-/
theorem joinSelfAttestation_toExpansiveFunction_apply
    (X : Type u) [BoundedSemilattice X] (y x : X) :
    ((joinSelfAttestation X).toExpansiveFunction y).1 x = x ⊔ y := by
  rfl

/-- Example 7.4(3): postfix form of the join attestation, `x # y = x ∨_X y`. -/
theorem joinSelfAttestation_postfixApply (X : Type u) [BoundedSemilattice X] (x y : X) :
    (joinSelfAttestation X).postfixApply x y = x ⊔ y := by
  rfl

/-- Example 7.4(3): the join self-attestation is the principal attestation of the identity morphism. -/
theorem joinSelfAttestation_eq_principal_identity (X : Type u) [BoundedSemilattice X] :
    joinSelfAttestation X = principalAttestation (identityMorphism X) := by
  rfl

/-- Example 7.4(3): the join self-attestation is monotone (Definition 7.5(2)) in the attesting parameter. -/
theorem joinSelfAttestation_monotone (X : Type u) [BoundedSemilattice X] :
    (joinSelfAttestation X).Monotone := by
  intro y y' hyy' x
  exact BoundedSemilattice.join_le_join (BoundedSemilattice.le_refl x) hyy'

/--
Example 7.4(3): the join self-attestation is monotone as the displayed family `X → Expan(X)`.
-/
theorem joinSelfAttestation_toExpansiveFunction_monotone
    (X : Type u) [BoundedSemilattice X] {y y' : X} (hle : y ≤ y') :
    BoundedSemilattice.le ((joinSelfAttestation X).toExpansiveFunction y) ((joinSelfAttestation X).toExpansiveFunction y') := by
  exact Attestation.monotone_toExpansiveFunction
    (joinSelfAttestation_monotone X) hle

/-- Alternative spelling for `joinSelfAttestation_monotone`. -/
theorem joinSelfAttestation_uniformlyMonotone (X : Type u) [BoundedSemilattice X] :
    (joinSelfAttestation X).UniformlyMonotone := by
  exact joinSelfAttestation_monotone X

open Classical in
/-- Example 7.4(1), the linear attestation `λy.λx.(x if y ≤ x; y if x ≤ y; ⊤ otherwise)`,
where `y` is the paper's attesting parameter `x'`. -/
noncomputable def linearAttestationToFun (X : Type u) [BoundedSemilattice X]
    (y x : X) : X :=
  if y ≤ x then x else if x ≤ y then y else (⊤ : X)

open Classical in
theorem linearAttestationToFun_apply (X : Type u) [BoundedSemilattice X] (y x : X) :
    linearAttestationToFun X y x =
      if y ≤ x then x else if x ≤ y then y else (⊤ : X) := by
  rfl

/-- Example 7.4(1): the linear-attestation output is expansive (`x ≤` output). -/
theorem linearAttestationToFun_input_le_output
    (X : Type u) [BoundedSemilattice X] (y x : X) :
    x ≤ (linearAttestationToFun X y x) := by
  classical
  by_cases hyx : y ≤ x
  · simpa [linearAttestationToFun, hyx] using BoundedSemilattice.le_refl x
  · by_cases hxy : x ≤ y
    · simp [linearAttestationToFun, hyx, hxy]
    · simpa [linearAttestationToFun, hyx, hxy] using BoundedSemilattice.le_top' x

/--
Example 7.4(1): the linear-attestation output is above the attesting parameter `y`,
which is what yields strong contradiction preservation.
-/
theorem linearAttestationToFun_parameter_le_output
    (X : Type u) [BoundedSemilattice X] (y x : X) :
    y ≤ (linearAttestationToFun X y x) := by
  classical
  by_cases hyx : y ≤ x
  · simp [linearAttestationToFun, hyx]
  · by_cases hxy : x ≤ y
    · simpa [linearAttestationToFun, hyx, hxy] using BoundedSemilattice.le_refl y
    · simpa [linearAttestationToFun, hyx, hxy] using BoundedSemilattice.le_top' y

/-- Example 7.4(1): the linear example packaged as a self-attestation `X ⇛ X`. -/
noncomputable def linearSelfAttestation
    (X : Type u) [BoundedSemilattice X] : SelfAttestation X where
  toFun := linearAttestationToFun X
  expansive := by
    intro y x
    exact linearAttestationToFun_input_le_output X y x
  strongly_contradiction_preserving := by
    intro y y' hcontr x x'
    exact BoundedSemilattice.contradiction_monotone
      (linearAttestationToFun_parameter_le_output X y x)
      (linearAttestationToFun_parameter_le_output X y' x')
      hcontr

open Classical in
theorem linearSelfAttestation_apply
    (X : Type u) [BoundedSemilattice X] (y x : X) :
    (linearSelfAttestation X).toFun y x =
      if y ≤ x then x else if x ≤ y then y else (⊤ : X) := by
  rfl

/--
Example 7.4(1): the linear self-attestation as the displayed family `X → Expan(X)`.
-/
theorem linearSelfAttestation_toExpansiveFunction_apply
    (X : Type u) [BoundedSemilattice X] (y x : X) :
    ((linearSelfAttestation X).toExpansiveFunction y).1 x =
      linearAttestationToFun X y x := by
  rfl


namespace IdentityExpansiveNonAttestationExample

/-!
Example 7.4(6), the non-attestation: the identity map `λf.λx.f(x)` on `Expan(X)` is not an
attestation in `Expan(X) ⇛ X` in general, because it fails strong contradiction
preservation. This namespace supplies a concrete diamond-semilattice witness.
-/

open NonMonotoneAttestationExample

abbrev X : Type := Diamond

def leftExpansiveEndomapToFun : Diamond → Diamond
  | Diamond.bot => Diamond.right
  | Diamond.left => Diamond.left
  | Diamond.right => Diamond.top
  | Diamond.top => Diamond.top

def rightExpansiveEndomapToFun : Diamond → Diamond
  | Diamond.bot => Diamond.left
  | Diamond.left => Diamond.top
  | Diamond.right => Diamond.right
  | Diamond.top => Diamond.top

theorem leftExpansiveEndomap_expansive :
    Expansive X leftExpansiveEndomapToFun := by
  intro x
  cases x <;> rfl

theorem rightExpansiveEndomap_expansive :
    Expansive X rightExpansiveEndomapToFun := by
  intro x
  cases x <;> rfl

def leftExpansiveEndomap : expansiveFunctionSemilattice X :=
  ⟨leftExpansiveEndomapToFun, leftExpansiveEndomap_expansive⟩

def rightExpansiveEndomap : expansiveFunctionSemilattice X :=
  ⟨rightExpansiveEndomapToFun, rightExpansiveEndomap_expansive⟩

theorem identityExpansiveWitnesses_contradict :
    leftExpansiveEndomap 🗲 rightExpansiveEndomap := by
  exact (expansiveFunctionSemilattice_contradicts_iff X
    leftExpansiveEndomap rightExpansiveEndomap).mpr (by
      intro x
      cases x <;> rfl)

theorem identityExpansiveWitness_outputs_not_contradict :
    ¬ (leftExpansiveEndomap.1 Diamond.left) 🗲 (rightExpansiveEndomap.1 Diamond.bot) := by
  intro h
  change Diamond.left = Diamond.top at h
  cases h

theorem identityExpansiveFamily_not_strongly_contradiction_preserving :
    ¬ StronglyContradictionPreservingExpansiveFamily
      (expansiveFunctionSemilattice X) X
      (fun f : expansiveFunctionSemilattice X => f) := by
  intro hstrong
  exact identityExpansiveWitness_outputs_not_contradict
    (hstrong identityExpansiveWitnesses_contradict Diamond.left Diamond.bot)

/--
Example 7.4(6): the identity map on `Expan(X)` is not an attestation in
`Expan(X) ⇛ X` in general.
-/
theorem identityExpansiveFamily_not_attestation :
    ¬ ∃ A : Attestation (expansiveFunctionSemilattice X) X,
      A.toExpansiveFunction = (fun f : expansiveFunctionSemilattice X => f) := by
  intro hA
  have hstrong :
      StronglyContradictionPreservingExpansiveFamily
        (expansiveFunctionSemilattice X) X
        (fun f : expansiveFunctionSemilattice X => f) := by
    exact (exists_attestation_with_toExpansiveFunction_iff
      (Y := expansiveFunctionSemilattice X)
      (X := X)
      (fun f : expansiveFunctionSemilattice X => f)).mp hA
  exact identityExpansiveFamily_not_strongly_contradiction_preserving hstrong

/--
Example 7.4(6): identity on `Expan(X)` is not an attestation in general; the diamond
semilattice supplies a concrete witness.
-/
theorem exists_identityExpansiveFamily_not_attestation :
    ∃ (X : Type) (iX : BoundedSemilattice X),
      ¬ ∃ A : @Attestation (@expansiveFunctionSemilattice X iX) X
          (@instExpansiveFunctionSemilattice X iX) iX,
        @Attestation.toExpansiveFunction (@expansiveFunctionSemilattice X iX) X
            (@instExpansiveFunctionSemilattice X iX) iX A =
          (fun f : @expansiveFunctionSemilattice X iX => f) := by
  exact ⟨X, inferInstance, identityExpansiveFamily_not_attestation⟩

end IdentityExpansiveNonAttestationExample

/-- Example 7.4(4): the bottom-or-top attestation `λy.λx.(f(y) if x = ⊥_X; ⊤_X if x > ⊥_X)`
of a bounded-semilattice morphism `f`. -/
noncomputable def botTopAttestation
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) : Attestation Y X := by
  classical
  exact
    { toFun := fun y x => if x = (⊥ : X) then f.toFun y else (⊤ : X)
      expansive := by
        intro y x
        by_cases hx : x = (⊥ : X)
        · simp [hx]
          exact BoundedSemilattice.bot_le' (f.toFun y)
        · simp [hx]
          exact BoundedSemilattice.le_top' x
      strongly_contradiction_preserving := by
        intro y y' hcontr x x'
        have hf_contr : (f.toFun y) 🗲 (f.toFun y') :=
          f.map_contradicts hcontr
        by_cases hx : x = (⊥ : X)
        · by_cases hx' : x' = (⊥ : X)
          · simpa [hx, hx'] using hf_contr
          · simp [hx, hx']
            exact BoundedSemilattice.le_top' (f.toFun y)
        · by_cases hx' : x' = (⊥ : X)
          · simp [hx, hx']
            calc
              (⊤ : X) ⊔ (f.toFun y') = (f.toFun y') ⊔ (⊤ : X) :=
                BoundedSemilattice.join_comm (⊤ : X) (f.toFun y')
              _ = (⊤ : X) := BoundedSemilattice.le_top' (f.toFun y')
          · simp [hx, hx']
            exact BoundedSemilattice.join_idem (⊤ : X) }

open Classical in
theorem botTopAttestation_apply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) (x : X) :
    (botTopAttestation f).toFun y x =
      if x = (⊥ : X) then f.toFun y else (⊤ : X) := by
  rfl

open Classical in
/--
Example 7.4(4): the bottom-or-top example as the displayed family `Y → Expan(X)`.
-/
theorem botTopAttestation_toExpansiveFunction_apply
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) (x : X) :
    ((botTopAttestation f).toExpansiveFunction y).1 x =
      if x = (⊥ : X) then f.toFun y else (⊤ : X) := by
  exact botTopAttestation_apply f y x

theorem botTopAttestation_apply_bot
    {Y : Type u} [BoundedSemilattice Y]
    {X : Type v} [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) :
    (botTopAttestation f).toFun y (⊥ : X) = f.toFun y := by
  rw [botTopAttestation_apply]
  simp

open Classical in
/-- Example 7.4(4): postfix form of the bottom-or-top example. -/
theorem botTopAttestation_postfixApply
    {Y : Type u} [BoundedSemilattice Y]
    {X : Type v} [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (x : X) (y : Y) :
    (botTopAttestation f).postfixApply x y =
      if x = (⊥ : X) then f.toFun y else (⊤ : X) := by
  exact botTopAttestation_apply f y x

/-- Example 7.4(4): postfix bottom branch, `⊥ # y = f(y)`. -/
theorem botTopAttestation_postfixApply_bot
    {Y : Type u} [BoundedSemilattice Y]
    {X : Type v} [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) :
    (botTopAttestation f).postfixApply (⊥ : X) y = f.toFun y := by
  exact botTopAttestation_apply_bot f y

theorem botTopAttestation_apply_of_ne_bot
    {Y : Type u} [BoundedSemilattice Y]
    {X : Type v} [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) {x : X}
    (hx : x ≠ (⊥ : X)) :
    (botTopAttestation f).toFun y x = (⊤ : X) := by
  rw [botTopAttestation_apply]
  simp [hx]

/-- Example 7.4(4): postfix non-bottom branch, `x # y = ⊤` when `x ≠ ⊥`. -/
theorem botTopAttestation_postfixApply_of_ne_bot
    {Y : Type u} [BoundedSemilattice Y]
    {X : Type v} [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) {x : X}
    (hx : x ≠ (⊥ : X)) :
    (botTopAttestation f).postfixApply x y = (⊤ : X) := by
  exact botTopAttestation_apply_of_ne_bot f y hx

/-- Example 7.4(4): the `⊤` branch applies exactly when `x > ⊥_X`. -/
theorem botTopAttestation_apply_of_bot_lt
    {Y : Type u} [BoundedSemilattice Y]
    {X : Type v} [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) {x : X}
    (hx : (⊥ : X) < x) :
    (botTopAttestation f).toFun y x = (⊤ : X) := by
  exact botTopAttestation_apply_of_ne_bot f y ((BoundedSemilattice.bot_lt_iff_ne_bot x).mp hx)

/--
Example 7.4(4): postfix form of the strict non-bottom branch.
-/
theorem botTopAttestation_postfixApply_of_bot_lt
    {Y : Type u} [BoundedSemilattice Y]
    {X : Type v} [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) (y : Y) {x : X}
    (hx : (⊥ : X) < x) :
    (botTopAttestation f).postfixApply x y = (⊤ : X) := by
  exact botTopAttestation_apply_of_bot_lt f y hx

/-- Example 7.4(4): bottom-or-top attestations are monotone (Definition 7.5(2)) in the attesting parameter. -/
theorem botTopAttestation_monotone
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) :
    (botTopAttestation f).Monotone := by
  classical
  intro y y' hyy' x
  rw [botTopAttestation_apply, botTopAttestation_apply]
  by_cases hx : x = (⊥ : X)
  · simp [hx]
    exact f.map_le hyy'
  · simp [hx]
    exact BoundedSemilattice.le_refl (⊤ : X)

/--
Example 7.4(4): bottom-or-top attestations are monotone as displayed families `Y → Expan(X)`.
-/
theorem botTopAttestation_toExpansiveFunction_monotone
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) {y y' : Y} (hle : y ≤ y') :
    BoundedSemilattice.le ((botTopAttestation f).toExpansiveFunction y) ((botTopAttestation f).toExpansiveFunction y') := by
  exact Attestation.monotone_toExpansiveFunction
    (botTopAttestation_monotone f) hle

/-- Alternative spelling for `botTopAttestation_monotone`. -/
theorem botTopAttestation_uniformlyMonotone
    {Y : Type u} {X : Type v} [BoundedSemilattice Y] [BoundedSemilattice X]
    (f : BoundedSemilatticeMorphism Y X) :
    (botTopAttestation f).UniformlyMonotone := by
  exact botTopAttestation_monotone f

/-- Union of predicates, the join of the powerset semilattice underlying the semitopology
of Example 7.4(5). -/
def predUnion {Pnt : Type u} (A B : Pnt → Prop) : Pnt → Prop :=
  fun p => A p ∨ B p

/-- Example 7.4(5): the full powerset `pow(Pnt)` (predicates on `Pnt`) as a bounded
semilattice — join = union, `⊥` = ∅, `⊤` = `Pnt` — the ambient semilattice for a
semitopology `X ⊆ pow(Pnt)`. -/
instance powersetSemilattice (Pnt : Type u) : BoundedSemilattice (Pnt → Prop) where
  join := predUnion
  bot := fun _ => False
  top := fun _ => True
  join_idem := by
    intro A
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
    funext p
    apply propext
    constructor
    · intro _h
      exact True.intro
    · intro _h
      exact Or.inr True.intro

/-- Example 7.4(5): the powerset order is subset inclusion. -/
theorem powersetSemilattice_le_iff
    (Pnt : Type u) (A B : Pnt → Prop) :
    (powersetSemilattice Pnt).le A B ↔ ∀ p : Pnt, A p → B p := by
  constructor
  · intro h p hA
    have hp : (A p ∨ B p) = B p := congrFun h p
    exact Eq.mp hp (Or.inl hA)
  · intro h
    funext p
    apply propext
    constructor
    · intro hp
      cases hp with
      | inl hA => exact h p hA
      | inr hB => exact hB
    · intro hB
      exact Or.inr hB

/-- Example 7.4(5): contradiction (`A ∨ B = ⊤`) means the union `A ∪ B` is all of `Pnt`. -/
theorem powersetSemilattice_contradicts_iff
    (Pnt : Type u) (A B : Pnt → Prop) :
    (powersetSemilattice Pnt).Contradicts A B ↔ ∀ p : Pnt, A p ∨ B p := by
  constructor
  · intro h p
    have hp : (A p ∨ B p) = True := congrFun h p
    exact Eq.mp hp.symm True.intro
  · intro h
    funext p
    apply propext
    constructor
    · intro _hp
      exact True.intro
    · intro _htrue
      exact h p

end ConsistentHistories.AlternativePresentation
