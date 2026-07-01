import ContForm.AlternativePresentation.Cutting

namespace ContForm.AlternativePresentation

open ContForm.Models.Cut.Consistency
open ContForm.Foundation.Cut.Structure
open ContForm.Foundation.Cut.Flags
open ContForm.Foundation.LocatedSemilattices.TopTrees
open ContForm.Foundation.LocatedSemilattices.TopTrees.BoundedSemilattice
open ContForm.Foundation.LocatedSemilattices.Basic

universe u v

/--
Definition 7.6: a located semilattice in the alternative presentation. `Ctrl`
is the set of controllers (7.6(1)); `timeAt p` with `timeInst` is the
`Ctrl`-indexed family of pairwise disjoint bounded semilattices, the
`p`-components `Time_p` (7.6(2)); `attest q p` is the `(q,p)`-indexed family of
attestations `Time_q ⇛ Time_p` in the sense of Definition 7.2(5) (7.6(3)).
`self_attest_join` is the restriction 7.6(4): the diagonal `attest p p` is the
join self-attestation `∨_{Time_p}` of Example 7.4(3), i.e. `attest p p` applied
to attesting time `y` and input `x` is `x ⊔ y`.
-/
structure AlternativeLocatedSemilattice where
  Ctrl : Type u
  timeAt : Ctrl → Type u
  timeInst : ∀ p, BoundedSemilattice (timeAt p)
  attest : ∀ q p : Ctrl, @Attestation (timeAt q) (timeAt p) (timeInst q) (timeInst p)
  self_attest_join :
    ∀ p : Ctrl, ∀ y x : timeAt p,
      (attest p p).toFun y x = @BoundedSemilattice.join (timeAt p) (timeInst p) x y

namespace AlternativeLocatedSemilattice

attribute [instance] AlternativeLocatedSemilattice.timeInst

/--
Definition 7.6, flattened time type: the dependent sum of the indexed
components `Time_p` (7.6(2)), giving a single `Time` type for comparison with
the original located-semilattice interface of Definition 2.2.2.
-/
abbrev FlatTime (L : AlternativeLocatedSemilattice.{u}) : Type u :=
  Sigma fun p : L.Ctrl => L.timeAt p

/--
Definition 7.6: in the flattened Sigma representation, equality of times
from indexed components forces equality of the component controllers.
-/
theorem flatTime_controller_eq_of_eq
    (L : AlternativeLocatedSemilattice.{u}) {p q : L.Ctrl}
    {x : L.timeAt p} {y : L.timeAt q}
    (h : (⟨p, x⟩ : L.FlatTime) = ⟨q, y⟩) :
    p = q := by
  exact congrArg Sigma.fst h

/--
Definition 7.6: the flattened Sigma representation makes different indexed
components disjoint.
-/
theorem flatTime_ne_of_controller_ne
    (L : AlternativeLocatedSemilattice.{u}) {p q : L.Ctrl}
    {x : L.timeAt p} {y : L.timeAt q} (hpq : p ≠ q) :
    (⟨p, x⟩ : L.FlatTime) ≠ ⟨q, y⟩ := by
  intro h
  exact hpq (L.flatTime_controller_eq_of_eq h)

/--
Definition 7.6, flattened attestation operation `#` on `FlatTime`. The right
argument supplies the attesting time: for input `t` at `t.1` and attesting `s`
at `s.1` it applies the `(s.1, t.1)`-component attestation, matching the postfix
convention of Definition 7.2(7), `t # s = attest(s)(t)`.
-/
def flatAttest (L : AlternativeLocatedSemilattice.{u})
    (t s : L.FlatTime) : L.FlatTime :=
  ⟨t.1, (L.attest s.1 t.1).toFun s.2 t.2⟩

/--
Definition 7.6: flattened attestation applies the `(q,p)` indexed
attestation to an input time at `p` and an attesting time at `q`.
-/
theorem flatAttest_apply
    (L : AlternativeLocatedSemilattice.{u}) (p q : L.Ctrl)
    (x : L.timeAt p) (y : L.timeAt q) :
    L.flatAttest ⟨p, x⟩ ⟨q, y⟩ =
      ⟨p, (L.attest q p).toFun y x⟩ := by
  rfl

/--
Definition 7.6: component attestations viewed as `Y → Expan(X)` agree with
flattened attestation.
-/
theorem flatAttest_value_toExpansiveFunction_apply
    (L : AlternativeLocatedSemilattice.{u}) (p q : L.Ctrl)
    (x : L.timeAt p) (y : L.timeAt q) :
    (L.flatAttest ⟨p, x⟩ ⟨q, y⟩).2 =
      ((L.attest q p).toExpansiveFunction y).1 x := by
  rfl

/--
Definition 7.6: component attestations viewed with postfix application agree
with flattened attestation.
-/
theorem flatAttest_value_postfixApply
    (L : AlternativeLocatedSemilattice.{u}) (p q : L.Ctrl)
    (x : L.timeAt p) (y : L.timeAt q) :
    (L.flatAttest ⟨p, x⟩ ⟨q, y⟩).2 =
      (L.attest q p).postfixApply x y := by
  rfl

/-- Definition 7.6: flattened attestation preserves the input controller. -/
theorem flatAttest_controller
    (L : AlternativeLocatedSemilattice.{u}) (t s : L.FlatTime) :
    (L.flatAttest t s).1 = t.1 := by
  rfl

/-- Definition 7.6: flattened attestation is expansive in the input time. -/
theorem flatAttest_value_expansive
    (L : AlternativeLocatedSemilattice.{u}) (p q : L.Ctrl)
    (x : L.timeAt p) (y : L.timeAt q) :
    x ≤ (L.flatAttest ⟨p, x⟩ ⟨q, y⟩).2 := by
  exact (L.attest q p).expansive y x

/-- Definition 7.6: same-controller flattened attestation is semilattice join. -/
theorem flatAttest_self_join
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (x y : L.timeAt p) :
    L.flatAttest ⟨p, x⟩ ⟨p, y⟩ =
      ⟨p, x ⊔ y⟩ := by
  apply Sigma.ext
  · rfl
  · simpa [flatAttest] using L.self_attest_join p y x

/-- Definition 7.6: same-controller flattened attestation is idempotent. -/
theorem flatAttest_self_idem
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (x : L.timeAt p) :
    L.flatAttest ⟨p, x⟩ ⟨p, x⟩ = ⟨p, x⟩ := by
  rw [L.flatAttest_self_join p x x]
  apply Sigma.ext
  · rfl
  · simpa using BoundedSemilattice.join_idem x

/-- Definition 7.6: same-controller flattened attestation is commutative. -/
theorem flatAttest_self_comm
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (x y : L.timeAt p) :
    L.flatAttest ⟨p, x⟩ ⟨p, y⟩ =
      L.flatAttest ⟨p, y⟩ ⟨p, x⟩ := by
  calc
    L.flatAttest ⟨p, x⟩ ⟨p, y⟩ =
        ⟨p, x ⊔ y⟩ :=
      L.flatAttest_self_join p x y
    _ = ⟨p, y ⊔ x⟩ := by
      apply Sigma.ext
      · rfl
      · simpa using BoundedSemilattice.join_comm x y
    _ = L.flatAttest ⟨p, y⟩ ⟨p, x⟩ :=
      (L.flatAttest_self_join p y x).symm

/-- Definition 7.6: the flattened bottom time is below every same-controller time. -/
theorem flatAttest_self_bot
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (x : L.timeAt p) :
    L.flatAttest ⟨p, (⊥ : L.timeAt p)⟩ ⟨p, x⟩ = ⟨p, x⟩ := by
  rw [L.flatAttest_self_join p (⊥ : L.timeAt p) x]
  apply Sigma.ext
  · rfl
  · simpa using BoundedSemilattice.bot_le x

/-- Definition 7.6: the flattened top time is above every same-controller time. -/
theorem flatAttest_self_top
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (x : L.timeAt p) :
    L.flatAttest ⟨p, x⟩ ⟨p, (⊤ : L.timeAt p)⟩ =
      ⟨p, (⊤ : L.timeAt p)⟩ := by
  rw [L.flatAttest_self_join p x (⊤ : L.timeAt p)]
  apply Sigma.ext
  · rfl
  · simpa using BoundedSemilattice.le_top x

/--
Paper definitions Definition 7.6 and
Definition 2.2.2: the alternative indexed presentation flattens to
the original located-semilattice interface.
-/
instance toLocatedSemilattice (L : AlternativeLocatedSemilattice.{u}) :
    _root_.ContForm.Foundation.LocatedSemilattices.Basic.LocatedSemilattice L.FlatTime L.Ctrl where
  attest := L.flatAttest
  controller := Sigma.fst
  bot p := ⟨p, (⊥ : L.timeAt p)⟩
  top p := ⟨p, (⊤ : L.timeAt p)⟩
  bot_controller := by
    intro p
    rfl
  top_controller := by
    intro p
    rfl
  controller_preserving := by
    intro t s
    rfl
  self_join_idem := by
    intro t
    rcases t with ⟨p, x⟩
    apply Sigma.ext
    · rfl
    · simpa [flatAttest, L.self_attest_join p x x] using
        BoundedSemilattice.join_idem x
  self_join_comm := by
    intro t t' hctrl
    rcases t with ⟨p, x⟩
    rcases t' with ⟨p', y⟩
    cases hctrl
    apply Sigma.ext
    · rfl
    · simpa [flatAttest, L.self_attest_join p y x, L.self_attest_join p x y] using
        BoundedSemilattice.join_comm x y
  self_join_assoc := by
    intro t t' z hctrl hctrl'
    rcases t with ⟨p, x⟩
    rcases t' with ⟨p', y⟩
    rcases z with ⟨p'', z⟩
    cases hctrl
    cases hctrl'
    apply Sigma.ext
    · rfl
    · simp [flatAttest, L.self_attest_join,
        BoundedSemilattice.join_assoc x y z]
  self_bot_le := by
    intro p t hctrl
    rcases t with ⟨q, x⟩
    change q = p at hctrl
    subst q
    apply Sigma.ext
    · rfl
    · simpa [flatAttest, L.self_attest_join p x (⊥ : L.timeAt p)] using
        BoundedSemilattice.bot_le x
  self_le_top := by
    intro p t hctrl
    rcases t with ⟨q, x⟩
    change q = p at hctrl
    subst q
    apply Sigma.ext
    · rfl
    · simpa [flatAttest, L.self_attest_join p (⊤ : L.timeAt p) x] using
        BoundedSemilattice.le_top x
  expansive := by
    intro t s
    rcases t with ⟨p, x⟩
    rcases s with ⟨q, y⟩
    apply Sigma.ext
    · rfl
    · simp [flatAttest, L.self_attest_join]
      rw [BoundedSemilattice.join_comm]
      exact (L.attest q p).expansive y x
  contradiction_preserving := by
    intro t t' s s' ht ht' hcontr
    rcases t with ⟨p, x⟩
    rcases t' with ⟨p', x'⟩
    rcases s with ⟨q, y⟩
    rcases s' with ⟨q', y'⟩
    cases ht
    cases ht'
    have hyy' : y 🗲 y' := by
      have hraw := hcontr.2
      change L.flatAttest ⟨q, y⟩ ⟨q, y'⟩ =
        ⟨q, (⊤ : L.timeAt q)⟩ at hraw
      simpa [flatAttest, L.self_attest_join q y' y] using hraw
    constructor
    · rfl
    · apply Sigma.ext
      · rfl
      · simpa [flatAttest, L.self_attest_join] using
          (L.attest q p).strongly_contradiction_preserving hyy' x x'

/--
Paper definitions Definition 7.6 and
Definition 2.2.2: the flattened original controller is first projection.
-/
theorem toLocatedSemilattice_controller
    (L : AlternativeLocatedSemilattice.{u}) (t : L.FlatTime) :
    L.toLocatedSemilattice.controller t = t.1 := by
  rfl

/--
Definition 7.6: flattened attestation is the attestation operation of the
ordinary located-semilattice package.
-/
theorem toLocatedSemilattice_attest
    (L : AlternativeLocatedSemilattice.{u}) (t s : L.FlatTime) :
    t # s = L.flatAttest t s := by
  rfl

/-- Definition 7.6: the flattened bottom at `p` is the component bottom. -/
theorem toLocatedSemilattice_bot
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl) :
    L.toLocatedSemilattice.bot p = ⟨p, (⊥ : L.timeAt p)⟩ := by
  rfl

/-- Definition 7.6: the flattened top at `p` is the component top. -/
theorem toLocatedSemilattice_top
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl) :
    L.toLocatedSemilattice.top p = ⟨p, (⊤ : L.timeAt p)⟩ := by
  rfl

/--
Definition 7.6: order in the flattened located semilattice is the original
local-order definition over the flattened attestation operation.
-/
theorem toLocatedSemilattice_le_iff
    (L : AlternativeLocatedSemilattice.{u}) (t s : L.FlatTime) :
    t ≼ s ↔ t.1 = s.1 ∧ L.flatAttest t s = s := by
  rfl

theorem toLocatedSemilattice_self_join
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (x y : L.timeAt p) :
    L.toLocatedSemilattice.attest ⟨p, x⟩ ⟨p, y⟩ =
      ⟨p, x ⊔ y⟩ := by
  exact L.flatAttest_self_join p x y

/--
Definition 7.6: on a fixed controller component, flattened order is exactly
the bounded-semilattice order of that component.
-/
theorem toLocatedSemilattice_same_controller_le_iff
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (x y : L.timeAt p) :
    L.toLocatedSemilattice.le ⟨p, x⟩ ⟨p, y⟩ ↔
      x ≤ y := by
  constructor
  · intro hle
    have hval := hle.2
    change L.flatAttest ⟨p, x⟩ ⟨p, y⟩ = ⟨p, y⟩ at hval
    rw [L.flatAttest_self_join p x y] at hval
    exact eq_of_heq (by
      simpa only [Sigma.mk.injEq, true_and] using hval)
  · intro hle
    constructor
    · rfl
    · change L.flatAttest ⟨p, x⟩ ⟨p, y⟩ = ⟨p, y⟩
      rw [L.flatAttest_self_join p x y]
      apply Sigma.ext
      · rfl
      · exact heq_of_eq hle

/--
Definition 7.6: consistency after flattening is exactly non-topness in the
component bounded semilattice.
-/
theorem toLocatedSemilattice_consistentTime_iff
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (x : L.timeAt p) :
    L.toLocatedSemilattice.ConsistentTime ⟨p, x⟩ ↔
      x ≠ (⊤ : L.timeAt p) := by
  constructor
  · intro hconsistent htop
    exact hconsistent (by
      change (⟨p, x⟩ : L.FlatTime) = ⟨p, (⊤ : L.timeAt p)⟩
      rw [htop])
  · intro hnotTop htop
    change (⟨p, x⟩ : L.FlatTime) = ⟨p, (⊤ : L.timeAt p)⟩ at htop
    cases htop.symm
    exact hnotTop rfl

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: the original flat located-semilattice interface
supplies the indexed attestation family of the alternative presentation.
-/
def fiberAttestation
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (q p : Ctrl) : Attestation (@LocatedSemilattice.timeAt Time Ctrl inst q) (@LocatedSemilattice.timeAt Time Ctrl inst p) where
  toFun y x :=
    ⟨(@LocatedSemilattice.attest Time Ctrl inst) x.1 y.1, by
      calc
        (@LocatedSemilattice.controller Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) x.1 y.1) = (@LocatedSemilattice.controller Time Ctrl inst) x.1 :=
          (@LocatedSemilattice.controller_preserving Time Ctrl inst) x.1 y.1
        _ = p := x.2⟩
  expansive := by
    intro y x
    apply Subtype.ext
    exact ((@LocatedSemilattice.le_attest Time Ctrl inst) x.1 y.1).2
  strongly_contradiction_preserving := by
    intro y y' hcontr x x'
    have hraw : _root_.ContForm.Foundation.LocatedSemilattices.Basic.RawContradicts
        (@LocatedSemilattice.controller Time Ctrl inst) (@LocatedSemilattice.attest Time Ctrl inst) (@LocatedSemilattice.top Time Ctrl inst) y.1 y'.1 := by
      constructor
      · exact y.2.trans y'.2.symm
      · have hval : (@LocatedSemilattice.attest Time Ctrl inst) y.1 y'.1 = (@LocatedSemilattice.top Time Ctrl inst) q := congrArg Subtype.val hcontr
        rw [y.2]
        exact hval
    have hout : _root_.ContForm.Foundation.LocatedSemilattices.Basic.RawContradicts
        (@LocatedSemilattice.controller Time Ctrl inst) (@LocatedSemilattice.attest Time Ctrl inst) (@LocatedSemilattice.top Time Ctrl inst)
          ((@LocatedSemilattice.attest Time Ctrl inst) x.1 y.1) ((@LocatedSemilattice.attest Time Ctrl inst) x'.1 y'.1) :=
      (@LocatedSemilattice.contradiction_preserving Time Ctrl inst) (x.2.trans x'.2.symm) (y.2.trans y'.2.symm) hraw
    apply Subtype.ext
    change (@LocatedSemilattice.attest Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) x.1 y.1) ((@LocatedSemilattice.attest Time Ctrl inst) x'.1 y'.1) = (@LocatedSemilattice.top Time Ctrl inst) p
    simpa [(@LocatedSemilattice.controller_preserving Time Ctrl inst) x.1 y.1, x.2] using hout.2

theorem fiberAttestation_apply
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (q p : Ctrl) (y : @LocatedSemilattice.timeAt Time Ctrl inst q) (x : @LocatedSemilattice.timeAt Time Ctrl inst p) :
    ((@fiberAttestation Time Ctrl inst) q p).toFun y x =
      ⟨(@LocatedSemilattice.attest Time Ctrl inst) x.1 y.1, by
        calc
          (@LocatedSemilattice.controller Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) x.1 y.1) = (@LocatedSemilattice.controller Time Ctrl inst) x.1 :=
            (@LocatedSemilattice.controller_preserving Time Ctrl inst) x.1 y.1
          _ = p := x.2⟩ := by
  rfl

theorem fiberAttestation_self_join
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (p : Ctrl) (y x : @LocatedSemilattice.timeAt Time Ctrl inst p) :
    ((@fiberAttestation Time Ctrl inst) p p).toFun y x = x ⊔ y := by
  apply Subtype.ext
  rfl

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: every original flat located semilattice in the
same universe gives an alternative located semilattice by taking controller
fibers as the indexed bounded semilattices.
-/
def ofLocatedSemilattice
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl] :
    AlternativeLocatedSemilattice.{u} where
  Ctrl := Ctrl
  timeAt := @LocatedSemilattice.timeAt Time Ctrl inst
  timeInst := @LocatedSemilattice.fiber Time Ctrl inst
  attest := (@fiberAttestation Time Ctrl inst)
  self_attest_join := by
    intro p y x
    exact (@fiberAttestation_self_join Time Ctrl inst) p y x

theorem ofLocatedSemilattice_self_join
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (p : Ctrl) (y x : @LocatedSemilattice.timeAt Time Ctrl inst p) :
    ((@ofLocatedSemilattice Time Ctrl inst).attest p p).toFun y x = x ⊔ y := by
  exact (@fiberAttestation_self_join Time Ctrl inst) p y x

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: encode a raw original time into the flattened
time type of the alternative presentation built from the original located
semilattice.
-/
def encodeLocatedTime
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t : Time) : (@ofLocatedSemilattice Time Ctrl inst).FlatTime :=
  ⟨(@LocatedSemilattice.controller Time Ctrl inst) t, ⟨t, rfl⟩⟩

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: encoding preserves the original controller.
-/
theorem encodeLocatedTime_controller
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t : Time) :
    ((@encodeLocatedTime Time Ctrl inst) t).1 = (@LocatedSemilattice.controller Time Ctrl inst) t := by
  rfl

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: encoding stores the original time as its value.
-/
theorem encodeLocatedTime_value
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t : Time) :
    ((@encodeLocatedTime Time Ctrl inst) t).2.1 = t := by
  rfl

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: the original-to-indexed encoding is injective.
-/
theorem encodeLocatedTime_injective
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl] :
    Function.Injective (@encodeLocatedTime Time Ctrl inst) := by
  intro t s h
  exact congrArg (fun z => z.2.1) h

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: after converting an original located semilattice
to the alternative presentation and flattening it back, attestation on encoded
times has the same controller as the original attestation.
-/
theorem ofLocatedSemilattice_flatAttest_encode_controller
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t s : Time) :
    ((@ofLocatedSemilattice Time Ctrl inst).flatAttest
        ((@encodeLocatedTime Time Ctrl inst) t)
        ((@encodeLocatedTime Time Ctrl inst) s)).1 =
      (@LocatedSemilattice.controller Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) t s) := by
  exact ((@LocatedSemilattice.controller_preserving Time Ctrl inst) t s).symm

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: after converting an original located semilattice
to the alternative presentation and flattening it back, attestation on encoded
times has the original raw attestation as its time value.
-/
theorem ofLocatedSemilattice_flatAttest_encode_value
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t s : Time) :
    ((@ofLocatedSemilattice Time Ctrl inst).flatAttest
        ((@encodeLocatedTime Time Ctrl inst) t)
        ((@encodeLocatedTime Time Ctrl inst) s)).2.1 =
      (@LocatedSemilattice.attest Time Ctrl inst) t s := by
  rfl

private theorem fiber_heq_of_val_eq
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    {p q : Ctrl} {x : @LocatedSemilattice.timeAt Time Ctrl inst p} {y : @LocatedSemilattice.timeAt Time Ctrl inst q}
    (hval : x.1 = y.1) : x ≍ y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases hval
  have hpq : p = q := hx.symm.trans hy
  cases hpq
  exact heq_of_eq (Subtype.ext rfl)

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: every flattened time in the alternative
presentation built from an original located semilattice comes from an original
time.
-/
theorem encodeLocatedTime_surjective
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl] :
    Function.Surjective (@encodeLocatedTime Time Ctrl inst) := by
  intro z
  refine ⟨z.2.1, ?_⟩
  apply Sigma.ext
  · exact z.2.2
  · apply fiber_heq_of_val_eq
    rfl

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: the reverse conversion preserves attestation on
encoded times as a flattened Sigma value.
-/
theorem ofLocatedSemilattice_flatAttest_encode
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t s : Time) :
    (@ofLocatedSemilattice Time Ctrl inst).flatAttest
        ((@encodeLocatedTime Time Ctrl inst) t)
        ((@encodeLocatedTime Time Ctrl inst) s) =
      (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) t s) := by
  apply Sigma.ext
  · exact ((@LocatedSemilattice.controller_preserving Time Ctrl inst) t s).symm
  · apply fiber_heq_of_val_eq
    exact (@ofLocatedSemilattice_flatAttest_encode_value Time Ctrl inst) t s

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: after reverse conversion and flattening, located
order on encoded times is exactly the original located order.
-/
theorem ofLocatedSemilattice_toLocatedSemilattice_le_encode_iff
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t s : Time) :
    (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.le
        ((@encodeLocatedTime Time Ctrl inst) t)
        ((@encodeLocatedTime Time Ctrl inst) s) ↔
      (@LocatedSemilattice.le Time Ctrl inst) t s := by
  rw [toLocatedSemilattice_le_iff]
  constructor
  · intro hle
    constructor
    · exact hle.1
    · have henc : (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) t s) = (@encodeLocatedTime Time Ctrl inst) s := by
        calc
          (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) t s) =
              (@ofLocatedSemilattice Time Ctrl inst).flatAttest
                ((@encodeLocatedTime Time Ctrl inst) t) ((@encodeLocatedTime Time Ctrl inst) s) :=
            ((@ofLocatedSemilattice_flatAttest_encode Time Ctrl inst) t s).symm
          _ = (@encodeLocatedTime Time Ctrl inst) s := hle.2
      exact congrArg (fun z => z.2.1) henc
  · intro hle
    constructor
    · exact hle.1
    · rw [ofLocatedSemilattice_flatAttest_encode]
      apply Sigma.ext
      · exact ((@LocatedSemilattice.controller_preserving Time Ctrl inst) t s).trans hle.1
      · apply fiber_heq_of_val_eq
        exact hle.2

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: after reverse conversion and flattening,
located-semilattice attestation on encoded times is original attestation.
-/
theorem ofLocatedSemilattice_toLocatedSemilattice_attest_encode
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t s : Time) :
    (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.attest
        ((@encodeLocatedTime Time Ctrl inst) t)
        ((@encodeLocatedTime Time Ctrl inst) s) =
      (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) t s) := by
  exact (@ofLocatedSemilattice_flatAttest_encode Time Ctrl inst) t s

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: reverse conversion preserves bottom times.
-/
theorem ofLocatedSemilattice_toLocatedSemilattice_bot
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (p : Ctrl) :
    (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.bot p =
      (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.bot Time Ctrl inst) p) := by
  apply Sigma.ext
  · exact ((@LocatedSemilattice.bot_controller Time Ctrl inst) p).symm
  · apply fiber_heq_of_val_eq
    rfl

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: reverse conversion preserves top times.
-/
theorem ofLocatedSemilattice_toLocatedSemilattice_top
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (p : Ctrl) :
    (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.top p =
      (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.top Time Ctrl inst) p) := by
  apply Sigma.ext
  · exact ((@LocatedSemilattice.top_controller Time Ctrl inst) p).symm
  · apply fiber_heq_of_val_eq
    rfl

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: after reverse conversion and flattening,
consistency of encoded times is exactly original consistency.
-/
theorem ofLocatedSemilattice_toLocatedSemilattice_consistentTime_encode_iff
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t : Time) :
    (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.ConsistentTime
        ((@encodeLocatedTime Time Ctrl inst) t) ↔
      (@LocatedSemilattice.ConsistentTime Time Ctrl inst) t := by
  rw [toLocatedSemilattice_consistentTime_iff]
  change (⟨t, rfl⟩ : @LocatedSemilattice.timeAt Time Ctrl inst ((@LocatedSemilattice.controller Time Ctrl inst) t)) ≠
      (⊤ : @LocatedSemilattice.timeAt Time Ctrl inst ((@LocatedSemilattice.controller Time Ctrl inst) t)) ↔
    t ≠ (@LocatedSemilattice.top Time Ctrl inst) ((@LocatedSemilattice.controller Time Ctrl inst) t)
  constructor
  · intro hconsistent htop
    exact hconsistent (Subtype.ext htop)
  · intro hconsistent htop
    exact hconsistent (congrArg Subtype.val htop)

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: after reverse conversion and flattening,
contradiction of encoded times is exactly original contradiction.
-/
theorem ofLocatedSemilattice_toLocatedSemilattice_contradicts_encode_iff
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (t s : Time) :
    (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.Contradicts
        ((@encodeLocatedTime Time Ctrl inst) t)
        ((@encodeLocatedTime Time Ctrl inst) s) ↔
      (@LocatedSemilattice.Contradicts Time Ctrl inst) t s := by
  constructor
  · intro hcontr
    constructor
    · exact hcontr.1
    · have htop : (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) t s) =
          (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.top Time Ctrl inst) ((@LocatedSemilattice.controller Time Ctrl inst) t)) := by
        calc
          (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) t s) =
              (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.attest
                ((@encodeLocatedTime Time Ctrl inst) t) ((@encodeLocatedTime Time Ctrl inst) s) :=
            ((@ofLocatedSemilattice_toLocatedSemilattice_attest_encode Time Ctrl inst) t s).symm
          _ =
              (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.top
                ((@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.controller
                  ((@encodeLocatedTime Time Ctrl inst) t)) := hcontr.2
          _ = (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.top Time Ctrl inst) ((@LocatedSemilattice.controller Time Ctrl inst) t)) := by
            exact (@ofLocatedSemilattice_toLocatedSemilattice_top Time Ctrl inst) ((@LocatedSemilattice.controller Time Ctrl inst) t)
      exact congrArg (fun z => z.2.1) htop
  · intro hcontr
    constructor
    · exact hcontr.1
    · calc
        (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.attest
            ((@encodeLocatedTime Time Ctrl inst) t) ((@encodeLocatedTime Time Ctrl inst) s) =
          (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.attest Time Ctrl inst) t s) :=
            (@ofLocatedSemilattice_toLocatedSemilattice_attest_encode Time Ctrl inst) t s
        _ = (@encodeLocatedTime Time Ctrl inst) ((@LocatedSemilattice.top Time Ctrl inst) ((@LocatedSemilattice.controller Time Ctrl inst) t)) := by
          rw [hcontr.2]
        _ =
          (@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.top
            ((@ofLocatedSemilattice Time Ctrl inst).toLocatedSemilattice.controller
              ((@encodeLocatedTime Time Ctrl inst) t)) := by
          exact ((@ofLocatedSemilattice_toLocatedSemilattice_top Time Ctrl inst) ((@LocatedSemilattice.controller Time Ctrl inst) t)).symm

/-- Definition 7.6: the alternative located semilattice is sequential componentwise. -/
def Sequential (L : AlternativeLocatedSemilattice.{u}) : Prop :=
  ∀ p : L.Ctrl, BoundedSemilattice.Sequential (α := L.timeAt p)

/--
Definition 7.6: componentwise sequentiality gives sequentiality after
flattening to the original located-semilattice interface.
-/
theorem toLocatedSemilattice_sequential
    (L : AlternativeLocatedSemilattice.{u}) (hseq : L.Sequential) :
    L.toLocatedSemilattice.Sequential := by
  intro p t t'
  rcases t with ⟨⟨q, x⟩, hq⟩
  rcases t' with ⟨⟨q', y⟩, hq'⟩
  change q = p at hq
  change q' = p at hq'
  subst q
  subst q'
  rcases hseq p x y with hleft | hright | htop
  · left
    apply Subtype.ext
    change L.toLocatedSemilattice.attest ⟨p, x⟩ ⟨p, y⟩ = ⟨p, x⟩
    rw [toLocatedSemilattice_self_join, hleft]
  · right
    left
    apply Subtype.ext
    change L.toLocatedSemilattice.attest ⟨p, x⟩ ⟨p, y⟩ = ⟨p, y⟩
    rw [toLocatedSemilattice_self_join, hright]
  · right
    right
    apply Subtype.ext
    change L.toLocatedSemilattice.attest ⟨p, x⟩ ⟨p, y⟩ =
      L.toLocatedSemilattice.top p
    rw [toLocatedSemilattice_self_join, htop]
    rfl

/--
Paper definitions Definition 2.2.2 and
Definition 7.6: original located-semilattice sequentiality
transfers to the alternative indexed presentation built from its controller
fibers.
-/
theorem ofLocatedSemilattice_sequential
    {Time Ctrl : Type u} [inst : LocatedSemilattice Time Ctrl]
    (hseq : (@LocatedSemilattice.Sequential Time Ctrl inst)) :
    (@ofLocatedSemilattice Time Ctrl inst).Sequential := by
  exact hseq

end AlternativeLocatedSemilattice

/-- Definition 7.6: each indexed attestation component is expansive. -/
theorem AlternativeLocatedSemilattice.attest_expansive
    (L : AlternativeLocatedSemilattice.{u}) (q p : L.Ctrl)
    (y : L.timeAt q) (x : L.timeAt p) :
    x ≤ ((L.attest q p).toFun y x) := by
  exact (L.attest q p).expansive y x

/--
Definition 7.6: each indexed attestation component is strongly
contradiction-preserving.
-/
theorem AlternativeLocatedSemilattice.attest_strongly_contradiction_preserving
    (L : AlternativeLocatedSemilattice.{u}) {q p : L.Ctrl}
    {y y' : L.timeAt q} (hcontr : y 🗲 y')
    (x x' : L.timeAt p) :
    ((L.attest q p).toFun y x) 🗲 ((L.attest q p).toFun y' x') := by
  exact (L.attest q p).strongly_contradiction_preserving hcontr x x'

/-- Definition 7.6: applying a self component is semilattice join. -/
theorem AlternativeLocatedSemilattice.self_attest_apply
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (y x : L.timeAt p) :
    (L.attest p p).toFun y x = x ⊔ y := by
  exact L.self_attest_join p y x

/-- Definition 7.6: postfix application of a self component is semilattice join. -/
theorem AlternativeLocatedSemilattice.self_attest_postfixApply
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (x y : L.timeAt p) :
    (L.attest p p).postfixApply x y = x ⊔ y := by
  exact L.self_attest_join p y x

/-- Definition 7.6(4): the diagonal component `attest p p` is the join
self-attestation `∨_{Time_p}` of Example 7.4(3). -/
theorem AlternativeLocatedSemilattice.self_attest_eq_joinSelfAttestation
    (L : AlternativeLocatedSemilattice) (p : L.Ctrl) :
    L.attest p p = joinSelfAttestation (L.timeAt p) := by
  apply attestation_ext
  funext y x
  exact L.self_attest_join p y x

theorem AlternativeLocatedSemilattice.self_attest_parameter_le
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (y x : L.timeAt p) :
    y ≤ ((L.attest p p).toFun y x) := by
  rw [L.self_attest_join p y x]
  exact BoundedSemilattice.le_join_right x y

theorem AlternativeLocatedSemilattice.self_attest_comm
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    (y x : L.timeAt p) :
    (L.attest p p).toFun y x = (L.attest p p).toFun x y := by
  rw [L.self_attest_join p y x, L.self_attest_join p x y]
  exact BoundedSemilattice.join_comm x y

/-- Definition 7.6(4): the diagonal component `attest p p`, being the join
self-attestation (Example 7.4(3)), is the principal attestation of the identity
morphism, per the observation in Example 7.4(3) that join attestation is the
principal attestation with `Y = X` and `f = id`. -/
theorem AlternativeLocatedSemilattice.self_attest_eq_principal_identity
    (L : AlternativeLocatedSemilattice) (p : L.Ctrl) :
    L.attest p p = principalAttestation (identityMorphism (L.timeAt p)) := by
  calc
    L.attest p p = joinSelfAttestation (L.timeAt p) :=
      L.self_attest_eq_joinSelfAttestation p
    _ = principalAttestation (identityMorphism (L.timeAt p)) :=
      joinSelfAttestation_eq_principal_identity (L.timeAt p)

/-- Definition 7.6: self-attestations inherit join-attestation monotonicity. -/
theorem AlternativeLocatedSemilattice.self_attest_monotone
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl) :
    (L.attest p p).Monotone := by
  rw [L.self_attest_eq_joinSelfAttestation p]
  exact joinSelfAttestation_monotone (L.timeAt p)

/--
Definition 7.6: self-attestations are monotone as component families
`Time_p → Expan(Time_p)`.
-/
theorem AlternativeLocatedSemilattice.self_attest_toExpansiveFunction_monotone
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl)
    {y y' : L.timeAt p} (hle : y ≤ y') :
    BoundedSemilattice.le ((L.attest p p).toExpansiveFunction y) ((L.attest p p).toExpansiveFunction y') := by
  exact Attestation.monotone_toExpansiveFunction
    (L.self_attest_monotone p) hle

/-- Alternative spelling for `AlternativeLocatedSemilattice.self_attest_monotone`. -/
theorem AlternativeLocatedSemilattice.self_attest_uniformlyMonotone
    (L : AlternativeLocatedSemilattice.{u}) (p : L.Ctrl) :
    (L.attest p p).UniformlyMonotone := by
  exact L.self_attest_monotone p

/--
Definition 7.7(2): a located semilattice with Cut in the alternative
presentation. `toLocated` is the underlying Definition 7.6 located semilattice.
`cutting p` is the attestation `CuttingPoset ⇛ Time_p` equipping each
`p`-component (7.7(2)(a)), where `CuttingPoset` is the cutting-flag bounded
semilattice of Definition 7.7(1) (here `ConcreteTime` with
`cuttingFlagBoundedSemilattice`). `cutting_bot` and `cutting_top` are the
boundary conditions 7.7(2)(b): `t ⇛_p ⊥_CuttingPoset = t` and
`t ⇛_p ⊤_CuttingPoset = ⊤_p`. `cutting_separating` and
`cutting_attestation_monotone` are the separating (Definition 7.5(1)) and
monotone (Definition 7.5(2)) requirements of 7.7(2)(a).
-/
structure AlternativeLocatedSemilatticeWithCut where
  toLocated : AlternativeLocatedSemilattice.{u}
  cutting : ∀ p : toLocated.Ctrl,
    Attestation ConcreteTime (toLocated.timeAt p)
  cutting_bot :
    ∀ p : toLocated.Ctrl, ∀ x : toLocated.timeAt p,
      (cutting p).toFun cuttingFlagBoundedSemilattice.bot x = x
  cutting_top :
    ∀ p : toLocated.Ctrl, ∀ x : toLocated.timeAt p,
      (cutting p).toFun cuttingFlagBoundedSemilattice.top x = (⊤ : toLocated.timeAt p)
  cutting_separating : ∀ p : toLocated.Ctrl, (cutting p).Separating
  cutting_attestation_monotone : ∀ p : toLocated.Ctrl, (cutting p).Monotone

theorem cutting_attestation_bot
    (L : AlternativeLocatedSemilatticeWithCut) (p : L.toLocated.Ctrl)
    (x : L.toLocated.timeAt p) :
    (L.cutting p).toFun cuttingFlagBoundedSemilattice.bot x = x := by
  exact L.cutting_bot p x

theorem cutting_attestation_top
    (L : AlternativeLocatedSemilatticeWithCut) (p : L.toLocated.Ctrl)
    (x : L.toLocated.timeAt p) :
    (L.cutting p).toFun cuttingFlagBoundedSemilattice.top x =
      (⊤ : L.toLocated.timeAt p) := by
  exact L.cutting_top p x

theorem cutting_attestation_separating
    (L : AlternativeLocatedSemilatticeWithCut) (p : L.toLocated.Ctrl) :
    (L.cutting p).Separating := by
  exact L.cutting_separating p

theorem cutting_attestation_monotone
    (L : AlternativeLocatedSemilatticeWithCut) (p : L.toLocated.Ctrl) :
    (L.cutting p).Monotone := by
  exact L.cutting_attestation_monotone p

/--
Definition 7.7: each component cutting attestation is monotone
as a family `CuttingPoset → Expan(Time_p)`.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_attestation_toExpansiveFunction_monotone
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    {flag flag' : ConcreteTime}
    (hle : flag ≤ flag') :
    BoundedSemilattice.le ((L.cutting p).toExpansiveFunction flag) ((L.cutting p).toExpansiveFunction flag') := by
  exact Attestation.monotone_toExpansiveFunction
    (L.cutting_attestation_monotone p) hle

/--
Definition 7.7(2)(c): the global cutting operation
`⇛ : CuttingPoset → Time → Time` assembled from the component cutting
attestations by `t ⇛ Q = t ⇛_{ctrl(t)} Q`.
-/
def AlternativeLocatedSemilatticeWithCut.cuttingTime
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    (flag : ConcreteTime)
    (t : L.toLocated.FlatTime) : L.toLocated.FlatTime :=
  ⟨t.1, (L.cutting t.1).toFun flag t.2⟩

/-- Definition 7.7: component expansion of global cutting. -/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_apply
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (flag : ConcreteTime) (x : L.toLocated.timeAt p) :
    L.cuttingTime flag ⟨p, x⟩ = ⟨p, (L.cutting p).toFun flag x⟩ := by
  rfl

/--
Definition 7.7: component cutting attestations viewed as
`CuttingPoset → Expan(Time_p)` agree with global cutting.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_value_toExpansiveFunction_apply
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (flag : ConcreteTime) (x : L.toLocated.timeAt p) :
    (L.cuttingTime flag ⟨p, x⟩).2 =
      ((L.cutting p).toExpansiveFunction flag).1 x := by
  rfl

/--
Definition 7.7: component cutting postfix application agrees with the global
cutting operation.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_value_postfixApply
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (flag : ConcreteTime) (x : L.toLocated.timeAt p) :
    (L.cuttingTime flag ⟨p, x⟩).2 =
      (L.cutting p).postfixApply x flag := by
  rfl

/--
Definition 7.7: global cutting by `nextIndex_j` is the component cutting
attestation at `nextIndex_j`.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_nextIndex_apply
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x : L.toLocated.timeAt p) :
    L.cuttingTime (ConcreteTime.nextIndex j) ⟨p, x⟩ =
      ⟨p, (L.cutting p).postfixApply x (ConcreteTime.nextIndex j)⟩ := by
  rfl

/--
Definition 7.7: global cutting by `cutMe_j` is the component cutting
attestation at `cutMe_j`.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutMe_apply
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x : L.toLocated.timeAt p) :
    L.cuttingTime (ConcreteTime.cutMe j) ⟨p, x⟩ =
      ⟨p, (L.cutting p).postfixApply x (ConcreteTime.cutMe j)⟩ := by
  rfl

/--
Definition 7.7: global cutting by `cutYou_j` is the component cutting
attestation at `cutYou_j`.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_cutYou_apply
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (j : Nat) (x : L.toLocated.timeAt p) :
    L.cuttingTime (ConcreteTime.cutYou j) ⟨p, x⟩ =
      ⟨p, (L.cutting p).postfixApply x (ConcreteTime.cutYou j)⟩ := by
  rfl

/-- Definition 7.7: global cutting preserves the controller. -/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_controller
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    (flag : ConcreteTime) (t : L.toLocated.FlatTime) :
    (L.cuttingTime flag t).1 = t.1 := by
  rfl

/-- Definition 7.7: cutting by bottom is the identity. -/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_bot
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (t : L.toLocated.FlatTime) :
    L.cuttingTime cuttingFlagBoundedSemilattice.bot t = t := by
  rcases t with ⟨p, x⟩
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (L.cutting_bot p x)

/-- Definition 7.7: cutting by top gives top at the same controller. -/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (t : L.toLocated.FlatTime) :
    L.cuttingTime cuttingFlagBoundedSemilattice.top t =
      L.toLocated.toLocatedSemilattice.top t.1 := by
  rcases t with ⟨p, x⟩
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (L.cutting_top p x)

/-- Definition 7.7: global cutting is expansive in the input time. -/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_expansive
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    (flag : ConcreteTime) (t : L.toLocated.FlatTime) :
    t ≼ (L.cuttingTime flag t) := by
  rcases t with ⟨p, x⟩
  exact (AlternativeLocatedSemilattice.toLocatedSemilattice_same_controller_le_iff
    L.toLocated p x ((L.cutting p).toFun flag x)).mpr
      ((L.cutting p).expansive flag x)

/--
Definition 7.7: global cutting is monotone in the
`CuttingPoset` parameter.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_monotone
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    {flag flag' : ConcreteTime}
    (hle : flag ≤ flag')
    (t : L.toLocated.FlatTime) :
    (L.cuttingTime flag t) ≼ (L.cuttingTime flag' t) := by
  rcases t with ⟨p, x⟩
  exact (AlternativeLocatedSemilattice.toLocatedSemilattice_same_controller_le_iff
    L.toLocated p ((L.cutting p).toFun flag x)
      ((L.cutting p).toFun flag' x)).mpr
        (L.cutting_attestation_monotone p hle x)

/--
Definition 7.7(2)(c): the assembled global cutting operation
is separating on nontrivial cutting-poset parameters in the paper's
consistent-output sense: equal, consistent (non-`⊤`) outputs
`t ⇛ Q = t' ⇛ Q'` force `Q = Q'`.
-/
def AlternativeLocatedSemilatticeWithCut.CuttingTimeSeparating
    (L : AlternativeLocatedSemilatticeWithCut.{u}) : Prop :=
  ∀ {flag flag' : ConcreteTime}
    {t t' : L.toLocated.FlatTime},
    flag ≠ cuttingFlagBoundedSemilattice.bot →
    flag ≠ cuttingFlagBoundedSemilattice.top →
    flag' ≠ cuttingFlagBoundedSemilattice.bot →
    flag' ≠ cuttingFlagBoundedSemilattice.top →
    L.cuttingTime flag t = L.cuttingTime flag' t' →
    L.cuttingTime flag t ≠ L.toLocated.toLocatedSemilattice.top t.1 →
    flag = flag'

/--
Definition 7.7(2)(c): equal consistent global cutting outputs
have equal nontrivial cutting-poset parameters.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_flag_eq_of_eq_consistent_nontrivial
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    {flag flag' : ConcreteTime}
    {t t' : L.toLocated.FlatTime}
    (hflag_bot : flag ≠ cuttingFlagBoundedSemilattice.bot)
    (_hflag_top : flag ≠ cuttingFlagBoundedSemilattice.top)
    (hflag'_bot : flag' ≠ cuttingFlagBoundedSemilattice.bot)
    (_hflag'_top : flag' ≠ cuttingFlagBoundedSemilattice.top)
    (heq : L.cuttingTime flag t = L.cuttingTime flag' t')
    (hnotTop :
      L.cuttingTime flag t ≠ L.toLocated.toLocatedSemilattice.top t.1) :
    flag = flag' := by
  rcases t with ⟨p, x⟩
  rcases t' with ⟨p', x'⟩
  have hp : p = p' := congrArg Sigma.fst heq
  subst p'
  have hsigma :
      (⟨p, (L.cutting p).toFun flag x⟩ : L.toLocated.FlatTime) =
        ⟨p, (L.cutting p).toFun flag' x'⟩ := by
    simpa [AlternativeLocatedSemilatticeWithCut.cuttingTime] using heq
  have hlocalEq :
      (L.cutting p).toFun flag x = (L.cutting p).toFun flag' x' := by
    exact eq_of_heq (by
      simpa only [Sigma.mk.injEq, true_and] using hsigma)
  have hlocalNotTop :
      (L.cutting p).toFun flag x ≠ (⊤ : L.toLocated.timeAt p) := by
    intro htop
    apply hnotTop
    apply Sigma.ext
    · rfl
    · exact heq_of_eq htop
  exact L.cutting_separating p flag flag' x x'
    hflag_bot hflag'_bot hlocalEq hlocalNotTop

/--
Definition 7.7(2)(c): the alternative Cut structure supplies
the global consistent-output separation condition.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_separating
    (L : AlternativeLocatedSemilatticeWithCut.{u}) :
    L.CuttingTimeSeparating := by
  intro flag flag' t t' hflag_bot hflag_top hflag'_bot hflag'_top heq hnotTop
  exact L.cuttingTime_flag_eq_of_eq_consistent_nontrivial
    hflag_bot hflag_top hflag'_bot hflag'_top heq hnotTop

/-- Alternative spelling for `cutting_attestation_monotone`. -/
theorem cutting_attestation_uniformlyMonotone
    (L : AlternativeLocatedSemilatticeWithCut) (p : L.toLocated.Ctrl) :
    (L.cutting p).UniformlyMonotone := by
  exact L.cutting_attestation_monotone p

theorem AlternativeLocatedSemilatticeWithCut.cutting_expansive
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (flag : ConcreteTime) (x : L.toLocated.timeAt p) :
    x ≤ ((L.cutting p).toFun flag x) := by
  exact (L.cutting p).expansive flag x

theorem AlternativeLocatedSemilatticeWithCut.cutting_monotone
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    {flag flag' : ConcreteTime}
    (hle : flag ≤ flag')
    (x : L.toLocated.timeAt p) :
    ((L.cutting p).toFun flag x) ≤ ((L.cutting p).toFun flag' x) := by
  exact L.cutting_attestation_monotone p hle x

/-- Definition 7.7: postfix cutting attestation is expansive in the input time. -/
theorem AlternativeLocatedSemilatticeWithCut.cutting_postfix_expansive
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (flag : ConcreteTime) (x : L.toLocated.timeAt p) :
    x ≤ ((L.cutting p).postfixApply x flag) := by
  exact (L.cutting p).le_postfixApply x flag

/-- Definition 7.7: postfix cutting by bottom is the identity. -/
theorem AlternativeLocatedSemilatticeWithCut.cutting_postfix_bot
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (x : L.toLocated.timeAt p) :
    (L.cutting p).postfixApply x cuttingFlagBoundedSemilattice.bot = x := by
  exact L.cutting_bot p x

/-- Definition 7.7: postfix cutting by top gives the component top. -/
theorem AlternativeLocatedSemilatticeWithCut.cutting_postfix_top
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (x : L.toLocated.timeAt p) :
    (L.cutting p).postfixApply x cuttingFlagBoundedSemilattice.top =
      (⊤ : L.toLocated.timeAt p) := by
  exact L.cutting_top p x

/--
Definition 7.7: postfix cutting attestation is monotone in the
`CuttingPoset` parameter.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_postfix_monotone
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    {flag flag' : ConcreteTime}
    (hle : flag ≤ flag')
    (x : L.toLocated.timeAt p) :
    ((L.cutting p).postfixApply x flag) ≤ ((L.cutting p).postfixApply x flag') := by
  exact Attestation.monotone_postfixApply
    (L.cutting_attestation_monotone p) hle x

/--
Definition 7.7(1): the `CuttingPoset` order arrows of Figure 6
(`nextIndex j ≤ cutMe j`, `nextIndex j ≤ cutYou j`, and `cutYou j ≤ nextIndex i`
for `i < j`) transfer componentwise through the cutting attestation by its
monotonicity in the `CuttingPoset` parameter (Definition 7.7(2)(a)). These are
the geometric form, per Remark 7.8(2), of the Definition 3.2.1 order axioms.
-/
theorem AlternativeLocatedSemilatticeWithCut.cutting_original_order_axioms
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl) :
    (∀ j : Nat, ∀ x : L.toLocated.timeAt p,
      ((L.cutting p).toFun (ConcreteTime.nextIndex j) x) ≤ ((L.cutting p).toFun (ConcreteTime.cutMe j) x)) ∧
    (∀ j : Nat, ∀ x : L.toLocated.timeAt p,
      ((L.cutting p).toFun (ConcreteTime.nextIndex j) x) ≤ ((L.cutting p).toFun (ConcreteTime.cutYou j) x)) ∧
    (∀ {i j : Nat}, i < j → ∀ x : L.toLocated.timeAt p,
      ((L.cutting p).toFun (ConcreteTime.cutYou j) x) ≤ ((L.cutting p).toFun (ConcreteTime.nextIndex i) x)) := by
  constructor
  · intro j x
    exact L.cutting_monotone p (cuttingFlag_next_le_cutMe j) x
  · constructor
    · intro j x
      exact L.cutting_monotone p (cuttingFlag_next_le_cutYou j) x
    · intro i j hij x
      exact L.cutting_monotone p (cuttingFlag_cutYou_le_next hij) x

/--
Definition 7.7(1): the same `CuttingPoset` order arrows of Figure 6 also hold,
via `≼`, for the global cutting operation on flattened times, transported by
monotonicity of global cutting in the `CuttingPoset` parameter.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_original_order_axioms
    (L : AlternativeLocatedSemilatticeWithCut.{u}) :
    (∀ j : Nat, ∀ t : L.toLocated.FlatTime,
      (L.cuttingTime (ConcreteTime.nextIndex j) t) ≼ (L.cuttingTime (ConcreteTime.cutMe j) t)) ∧
    (∀ j : Nat, ∀ t : L.toLocated.FlatTime,
      (L.cuttingTime (ConcreteTime.nextIndex j) t) ≼ (L.cuttingTime (ConcreteTime.cutYou j) t)) ∧
    (∀ {i j : Nat}, i < j → ∀ t : L.toLocated.FlatTime,
      (L.cuttingTime (ConcreteTime.cutYou j) t) ≼ (L.cuttingTime (ConcreteTime.nextIndex i) t)) := by
  constructor
  · intro j t
    exact L.cuttingTime_monotone (cuttingFlag_next_le_cutMe j) t
  · constructor
    · intro j t
      exact L.cuttingTime_monotone (cuttingFlag_next_le_cutYou j) t
    · intro i j hij t
      exact L.cuttingTime_monotone (cuttingFlag_cutYou_le_next hij) t

/--
Definition 7.7(2)(c): the flag functions of the original Cut interface
(Definition 3.2.1) recovered from the alternative presentation, each given by
global cutting at the `CuttingPoset` element `ofFlagKind kind i` on flattened
times.
-/
def AlternativeLocatedSemilatticeWithCut.cuttingFlag
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    (kind : CutFlagKind) (i : Nat) :
    Flag L.toLocated.FlatTime where
  toFun := L.cuttingTime (ConcreteTime.ofFlagKind kind i)
  controller_preserving := by
    intro t
    exact L.cuttingTime_controller (ConcreteTime.ofFlagKind kind i) t
  expansive := by
    intro t
    exact L.cuttingTime_expansive (ConcreteTime.ofFlagKind kind i) t

/--
Extensional (functional) injectivity of the global cutting flags: the extra
obligation needed to turn the alternative presentation into the original
`LocatedSemilatticeWithCut` record of Definition 3.2.1. The separating clause
of Definition 7.7(2)(c) gives only consistent-output injectivity, which does
not by itself identify extensionally equal flag functions.
-/
def AlternativeLocatedSemilatticeWithCut.CuttingFlagFunctionInjective
    (L : AlternativeLocatedSemilatticeWithCut.{u}) : Prop :=
  ∀ {kind kind' : CutFlagKind} {i i' : Nat},
    L.cuttingFlag kind i = L.cuttingFlag kind' i' → kind = kind' ∧ i = i'

/--
Component pair/output injectivity comparison. This is stronger than the
source's separating field.
-/
def AlternativeLocatedSemilatticeWithCut.ComponentPairInjective
    (L : AlternativeLocatedSemilatticeWithCut.{u}) : Prop :=
  ∀ p : L.toLocated.Ctrl, (L.cutting p).PairInjective

/--
Ordinary component-map injectivity comparison, namely injectivity of each
component map `CuttingPoset → Expan(Time_p)`. This is not the source's
separating field and is not enough by itself to recover Definition 7.7(2)(c).
-/
def AlternativeLocatedSemilatticeWithCut.ComponentParameterInjective
    (L : AlternativeLocatedSemilatticeWithCut.{u}) : Prop :=
  ∀ p : L.toLocated.Ctrl, (L.cutting p).ParameterInjective

/--
Component parameter-map injectivity is exactly injectivity of each cutting
family `CuttingPoset → Expan(Time_p)`.
-/
theorem AlternativeLocatedSemilatticeWithCut.componentParameterInjective_iff_toExpansiveFunction_injective
    (L : AlternativeLocatedSemilatticeWithCut.{u}) :
    L.ComponentParameterInjective ↔
      ∀ p : L.toLocated.Ctrl, Function.Injective (L.cutting p).toExpansiveFunction := by
  constructor
  · intro hinj p
    exact (Attestation.parameterInjective_iff_toExpansiveFunction_injective
      (L.cutting p)).mp (hinj p)
  · intro hinj p
    exact (Attestation.parameterInjective_iff_toExpansiveFunction_injective
      (L.cutting p)).mpr (hinj p)

/--
Pair/output component injectivity is stronger than ordinary component
parameter-map injectivity.
-/
theorem AlternativeLocatedSemilatticeWithCut.componentPairInjective_implies_componentParameterInjective
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    (hinj : L.ComponentPairInjective) :
    L.ComponentParameterInjective := by
  intro p
  exact Attestation.pairInjective_implies_parameterInjective (hinj p)

/--
Component pair/output injectivity is stronger than injectivity of each
represented component family `CuttingPoset → Expan(Time_p)`.
-/
theorem AlternativeLocatedSemilatticeWithCut.componentPairInjective_implies_toExpansiveFunction_injective
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    (hinj : L.ComponentPairInjective) :
    ∀ p : L.toLocated.Ctrl, Function.Injective (L.cutting p).toExpansiveFunction := by
  exact (L.componentParameterInjective_iff_toExpansiveFunction_injective).mp
    (L.componentPairInjective_implies_componentParameterInjective hinj)

/--
Under explicit component pair/output injectivity, the global
consistent-output separating condition of Definition 7.7(2)(c) follows. This
does not by itself package the alternative presentation as the original Cut
interface of Definition 3.2.1.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingTime_separating_of_componentPairInjective
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    (hinj : L.ComponentPairInjective) :
    L.CuttingTimeSeparating := by
  intro flag flag' t t' _hflag_bot _hflag_top _hflag'_bot _hflag'_top heq _hnotTop
  rcases t with ⟨p, x⟩
  rcases t' with ⟨p', x'⟩
  have hp : p = p' := congrArg Sigma.fst heq
  subst p'
  have hsigma :
      (⟨p, (L.cutting p).toFun flag x⟩ : L.toLocated.FlatTime) =
        ⟨p, (L.cutting p).toFun flag' x'⟩ := by
    simpa [AlternativeLocatedSemilatticeWithCut.cuttingTime] using heq
  have hlocalEq :
      (L.cutting p).toFun flag x = (L.cutting p).toFun flag' x' := by
    exact eq_of_heq (by
      simpa only [Sigma.mk.injEq, true_and] using hsigma)
  have hpairOutput :
      (fun pair : ConcreteTime × L.toLocated.timeAt p =>
        (L.cutting p).toFun pair.1 pair.2) (flag, x) =
      (fun pair : ConcreteTime × L.toLocated.timeAt p =>
        (L.cutting p).toFun pair.1 pair.2) (flag', x') := by
    simpa using hlocalEq
  exact congrArg Prod.fst ((hinj p) hpairOutput)

/--
Component pair/output injectivity at one actual controller is enough to supply
the extra global flag-function injectivity obligation needed by the original
Cut package.
The explicit controller argument is essential; the paper does not
assume the controller type is inhabited.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingFlagFunctionInjective_of_pairInjective_at_controller
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (hinj : (L.cutting p).PairInjective) :
    L.CuttingFlagFunctionInjective := by
  intro kind kind' i i' hflag
  let base : L.toLocated.timeAt p := (⊥ : L.toLocated.timeAt p)
  have happly :
      L.cuttingTime (ConcreteTime.ofFlagKind kind i)
          (⟨p, base⟩ : L.toLocated.FlatTime) =
        L.cuttingTime (ConcreteTime.ofFlagKind kind' i')
          (⟨p, base⟩ : L.toLocated.FlatTime) := by
    simpa [AlternativeLocatedSemilatticeWithCut.cuttingFlag] using
      congrArg
        (fun Q : Flag L.toLocated.FlatTime =>
          Q (⟨p, base⟩ : L.toLocated.FlatTime))
        hflag
  have hlocal :
      (L.cutting p).toFun (ConcreteTime.ofFlagKind kind i) base =
        (L.cutting p).toFun (ConcreteTime.ofFlagKind kind' i') base := by
    simpa [AlternativeLocatedSemilatticeWithCut.cuttingTime] using happly
  have hpair :
      (fun pair : ConcreteTime × L.toLocated.timeAt p =>
        (L.cutting p).toFun pair.1 pair.2)
          (ConcreteTime.ofFlagKind kind i, base) =
      (fun pair : ConcreteTime × L.toLocated.timeAt p =>
        (L.cutting p).toFun pair.1 pair.2)
          (ConcreteTime.ofFlagKind kind' i', base) := by
    simpa using hlocal
  have hconcrete :
      ConcreteTime.ofFlagKind kind i = ConcreteTime.ofFlagKind kind' i' :=
    congrArg Prod.fst (hinj hpair)
  exact ConcreteTime.ofFlagKind_injective hconcrete

/--
Component pair/output injectivity supplies the extra global cutting-flag
function injectivity obligation once an actual component controller is
provided.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingFlagFunctionInjective_of_componentPairInjective
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (hinj : L.ComponentPairInjective) :
    L.CuttingFlagFunctionInjective := by
  exact L.cuttingFlagFunctionInjective_of_pairInjective_at_controller p (hinj p)

/--
If the controller type is inhabited, then component pair/output injectivity
supplies the extra global cutting-flag function injectivity obligation without
naming a particular component. The inhabitedness premise is explicit because
the paper does not assume it.
-/
theorem AlternativeLocatedSemilatticeWithCut.cuttingFlagFunctionInjective_of_componentPairInjective_inhabited
    (L : AlternativeLocatedSemilatticeWithCut.{u}) [Inhabited L.toLocated.Ctrl]
    (hinj : L.ComponentPairInjective) :
    L.CuttingFlagFunctionInjective := by
  exact L.cuttingFlagFunctionInjective_of_componentPairInjective default hinj

/--
Package the alternative Cut presentation as a `PackageSpec` for the original
`LocatedSemilatticeWithCut` interface (Definition 3.2.1), given extensional
flag-function injectivity. This extra hypothesis is required because the
separating clause of Definition 7.7(2)(c) is consistent-output injectivity, not
extensional injectivity of the flag functions.
-/
def AlternativeLocatedSemilatticeWithCut.toOriginalPackageSpec_of_cuttingFlagFunctionInjective
    (L : AlternativeLocatedSemilatticeWithCut.{u})
    (hinj : L.CuttingFlagFunctionInjective) :
    LocatedSemilatticeWithCut.PackageSpec L.toLocated.FlatTime where
  cutting := L.cuttingFlag
  consistent_output_injective := by
    intro kind kind' i i' t t' hconsistent heq
    have hflag :
        ConcreteTime.ofFlagKind kind i = ConcreteTime.ofFlagKind kind' i' := by
      apply L.cuttingTime_flag_eq_of_eq_consistent_nontrivial
      · cases kind <;> simp [ConcreteTime.ofFlagKind, cuttingFlagBoundedSemilattice]
      · cases kind <;> simp [ConcreteTime.ofFlagKind, cuttingFlagBoundedSemilattice]
      · cases kind' <;> simp [ConcreteTime.ofFlagKind, cuttingFlagBoundedSemilattice]
      · cases kind' <;> simp [ConcreteTime.ofFlagKind, cuttingFlagBoundedSemilattice]
      · simpa [AlternativeLocatedSemilatticeWithCut.cuttingFlag] using heq
      · intro htop
        apply hconsistent
        have hctrl :
            L.toLocated.toLocatedSemilattice.controller
              (L.cuttingTime (ConcreteTime.ofFlagKind kind i) t) = t.1 :=
          L.cuttingTime_controller (ConcreteTime.ofFlagKind kind i) t
        change
          L.cuttingTime (ConcreteTime.ofFlagKind kind i) t =
            L.toLocated.toLocatedSemilattice.top
              (L.toLocated.toLocatedSemilattice.controller
                (L.cuttingTime (ConcreteTime.ofFlagKind kind i) t))
        rw [hctrl]
        exact htop
    exact ConcreteTime.ofFlagKind_injective hflag
  next_le_cutme := by
    intro j t
    simpa [AlternativeLocatedSemilatticeWithCut.cuttingFlag, ConcreteTime.ofFlagKind]
      using (L.cuttingTime_original_order_axioms).1 j t
  next_le_cutyou := by
    intro j t
    simpa [AlternativeLocatedSemilatticeWithCut.cuttingFlag, ConcreteTime.ofFlagKind]
      using (L.cuttingTime_original_order_axioms).2.1 j t
  cutyou_le_next := by
    intro i j hij t
    simpa [AlternativeLocatedSemilatticeWithCut.cuttingFlag, ConcreteTime.ofFlagKind]
      using (L.cuttingTime_original_order_axioms).2.2 hij t
  cutme_contradicts_cutyou := by
    intro j t t' hctrl
    rcases t with ⟨p, x⟩
    rcases t' with ⟨p', x'⟩
    change p = p' at hctrl
    subst p'
    constructor
    · rfl
    · have hcontr :
          ((L.cutting p).toFun (ConcreteTime.cutMe j) x) 🗲 ((L.cutting p).toFun (ConcreteTime.cutYou j) x') :=
        (L.cutting p).strongly_contradiction_preserving
          (cuttingFlag_cutMe_contradicts_cutYou j) x x'
      change L.toLocated.flatAttest
          ⟨p, (L.cutting p).toFun (ConcreteTime.cutMe j) x⟩
          ⟨p, (L.cutting p).toFun (ConcreteTime.cutYou j) x'⟩ =
        L.toLocated.toLocatedSemilattice.top p
      rw [AlternativeLocatedSemilattice.flatAttest_self_join]
      apply Sigma.ext
      · rfl
      · exact heq_of_eq hcontr
  cutting_injective := by
    intro kind kind' i i' h
    exact hinj h

/--
Under component pair/output injectivity at one actual controller, the
alternative presentation packages as the original `LocatedSemilatticeWithCut`
interface.
-/
def AlternativeLocatedSemilatticeWithCut.toOriginalPackageSpec_of_pairInjective_at_controller
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (hinj : (L.cutting p).PairInjective) :
    LocatedSemilatticeWithCut.PackageSpec L.toLocated.FlatTime :=
  L.toOriginalPackageSpec_of_cuttingFlagFunctionInjective
    (L.cuttingFlagFunctionInjective_of_pairInjective_at_controller p hinj)

/--
Bridge from component pair/output injectivity and an explicit component
controller to the original `LocatedSemilatticeWithCut` package.
-/
def AlternativeLocatedSemilatticeWithCut.toOriginalPackageSpec_of_componentPairInjective
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (hinj : L.ComponentPairInjective) :
    LocatedSemilatticeWithCut.PackageSpec L.toLocated.FlatTime :=
  L.toOriginalPackageSpec_of_pairInjective_at_controller p (hinj p)

/--
Bridge from component pair/output injectivity and an inhabited controller type
to the original package specification.
-/
def AlternativeLocatedSemilatticeWithCut.toOriginalPackageSpec_of_componentPairInjective_inhabited
    (L : AlternativeLocatedSemilatticeWithCut.{u}) [Inhabited L.toLocated.Ctrl]
    (hinj : L.ComponentPairInjective) :
    LocatedSemilatticeWithCut.PackageSpec L.toLocated.FlatTime :=
  L.toOriginalPackageSpec_of_componentPairInjective default hinj

/--
Bridge from component pair/output injectivity and an explicit component
controller to the final original Cut record.
-/
def AlternativeLocatedSemilatticeWithCut.toOriginalLocatedSemilatticeWithCut_of_componentPairInjective
    (L : AlternativeLocatedSemilatticeWithCut.{u}) (p : L.toLocated.Ctrl)
    (hinj : L.ComponentPairInjective) :
    LocatedSemilatticeWithCut L.toLocated.FlatTime L.toLocated.Ctrl :=
  (L.toOriginalPackageSpec_of_componentPairInjective p hinj).toLocatedSemilatticeWithCut

/--
Bridge from component pair/output injectivity and an inhabited controller type
to the final original Cut record.
-/
def AlternativeLocatedSemilatticeWithCut.toOriginalLocatedSemilatticeWithCut_of_componentPairInjective_inhabited
    (L : AlternativeLocatedSemilatticeWithCut.{u}) [Inhabited L.toLocated.Ctrl]
    (hinj : L.ComponentPairInjective) :
    LocatedSemilatticeWithCut L.toLocated.FlatTime L.toLocated.Ctrl :=
  (L.toOriginalPackageSpec_of_componentPairInjective_inhabited hinj).toLocatedSemilatticeWithCut

end ContForm.AlternativePresentation
