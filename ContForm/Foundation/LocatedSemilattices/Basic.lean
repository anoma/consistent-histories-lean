import ContForm.Foundation.LocatedSemilattices.TopTrees

/-!
Paper section 2.2: Located semilattices.

-/

namespace ContForm.Foundation.LocatedSemilattices.Basic

open ContForm.Foundation.LocatedSemilattices.TopTrees

universe u v

/-- Raw same-controller contradiction data, used inside the class fields. -/
def RawContradicts {Ctrl : Type u} {Time : Type v}
    (controller : Time → Ctrl) (attest : Time → Time → Time)
    (top : Ctrl → Time) (s t : Time) : Prop :=
  controller s = controller t ∧ attest s t = top (controller s)

/--
Definition 2.2.2.

The paper uses one flat type of times with a controller map. The class below
keeps that representation as a typeclass on the time type `Time` (with the
controller type `Ctrl` an output of the instance), and states that each
controller fiber is a bounded semilattice under the restriction of `attest`.
-/
class LocatedSemilattice (Time : Type v) (Ctrl : outParam (Type u)) where
  attest : Time → Time → Time
  controller : Time → Ctrl
  bot : Ctrl → Time
  top : Ctrl → Time
  bot_controller : ∀ p : Ctrl, controller (bot p) = p
  top_controller : ∀ p : Ctrl, controller (top p) = p
  controller_preserving : ∀ t s : Time, controller (attest t s) = controller t
  self_join_idem : ∀ t : Time, attest t t = t
  self_join_comm :
    ∀ {t t' : Time}, controller t = controller t' → attest t t' = attest t' t
  self_join_assoc :
    ∀ {t t' u : Time}, controller t = controller t' → controller t' = controller u →
      attest (attest t t') u = attest t (attest t' u)
  self_bot_le : ∀ (p : Ctrl) (t : Time), controller t = p → attest (bot p) t = t
  self_le_top :
    ∀ (p : Ctrl) (t : Time), controller t = p → attest t (top p) = top p
  expansive : ∀ t s : Time, attest (attest t s) t = attest t s
  contradiction_preserving :
    ∀ {t t' s s' : Time}, controller t = controller t' → controller s = controller s' →
      RawContradicts controller attest top s s' →
        RawContradicts controller attest top (attest t s) (attest t' s')

namespace LocatedSemilattice

variable {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]

/-- Definition 2.2.2: local order on times at the same controller. -/
def le (t t' : Time) : Prop :=
  controller t = controller t' ∧ attest t t' = t'

/-- Definition 2.2.2: strict local order. -/
def lt (t t' : Time) : Prop :=
  le t t' ∧ t ≠ t'

/-!
Notation making formulas resemble the paper: `t ≼ t'` is the located order
(`le`), `t ≺ t'` the strict located order (`lt`), and `t # s` the paper's
attestation `#` (`attest`). Per-controller `bot`/`top` keep their named forms.
The located order uses dedicated notation rather than the `≤` typeclass, which
is reserved for the bounded-semilattice order. Each resolves from the time type
via the `LocatedSemilattice` instance wherever this module is imported.
-/
notation:50 lhs:51 " ≼ " rhs:51 => LocatedSemilattice.le lhs rhs
notation:50 lhs:51 " ≺ " rhs:51 => LocatedSemilattice.lt lhs rhs
notation:65 lhs:66 " # " rhs:66 => LocatedSemilattice.attest lhs rhs

/--
Generic one-controller located semilattice built from a bounded semilattice.

This is support infrastructure for model construction: it packages the paper's
located interface when all times have the same controller, but it supplies no
flags or Cut structure. It is a plain `def` (not a global instance) so that an
arbitrary bounded semilattice does not silently acquire a located structure and
a second contradiction (`🗲`) instance.
-/
def oneControllerOfBoundedSemilattice {α : Type v} [BoundedSemilattice α] :
    LocatedSemilattice α (PUnit : Type) where
  attest := BoundedSemilattice.join
  controller := fun _ => PUnit.unit
  bot := fun _ => BoundedSemilattice.bot
  top := fun _ => BoundedSemilattice.top
  bot_controller := by intro _p; rfl
  top_controller := by intro _p; rfl
  controller_preserving := by intro _t _s; rfl
  self_join_idem := by intro t; exact BoundedSemilattice.join_idem t
  self_join_comm := by intro _t _t' _h; exact BoundedSemilattice.join_comm _ _
  self_join_assoc := by intro _t _t' _u _h _h'; exact BoundedSemilattice.join_assoc _ _ _
  self_bot_le := by intro _p t _h; exact BoundedSemilattice.bot_le t
  self_le_top := by intro _p t _h; exact BoundedSemilattice.le_top t
  expansive := by
    intro t s
    calc
      (t ⊔ s) ⊔ t = t ⊔ (t ⊔ s) :=
        BoundedSemilattice.join_comm (t ⊔ s) t
      _ = (t ⊔ t) ⊔ s := (BoundedSemilattice.join_assoc t t s).symm
      _ = t ⊔ s := by rw [BoundedSemilattice.join_idem]
  contradiction_preserving := by
    intro t t' s s' _htt' _hss' hcontr
    constructor
    · rfl
    · exact BoundedSemilattice.contradiction_monotone
        (BoundedSemilattice.le_join_right t s)
        (BoundedSemilattice.le_join_right t' s') hcontr.2

/-- Definition 2.2.2, `timeat p`: the times controlled by `p`. -/
def timeAt (p : Ctrl) : Type v :=
  {t : Time // controller t = p}

/-- Definition 2.2.2: a member of `timeat p` is controlled by `p`. -/
theorem timeAt_controller (p : Ctrl) (t : timeAt (Time := Time) p) :
    controller t.1 = p := by
  exact t.2

/-- The bounded semilattice structure on a controller fiber. -/
instance fiber (p : Ctrl) : BoundedSemilattice (timeAt (Time := Time) p) where
  join t t' :=
    ⟨t.1 # t'.1, by
      calc
        controller (t.1 # t'.1) = controller t.1 :=
          controller_preserving t.1 t'.1
        _ = p := t.2⟩
  bot := ⟨bot p, bot_controller p⟩
  top := ⟨top p, top_controller p⟩
  join_idem := by
    intro t
    apply Subtype.ext
    exact self_join_idem t.1
  join_comm := by
    intro t t'
    apply Subtype.ext
    exact self_join_comm (t.2.trans t'.2.symm)
  join_assoc := by
    intro t t' u
    apply Subtype.ext
    exact self_join_assoc (t.2.trans t'.2.symm) (t'.2.trans u.2.symm)
  bot_le := by
    intro t
    apply Subtype.ext
    exact self_bot_le p t.1 t.2
  le_top := by
    intro t
    apply Subtype.ext
    exact self_le_top p t.1 t.2

/-- Definition 2.2.2: the fiber join is the restriction of attestation. -/
theorem fiber_join_apply
    (p : Ctrl) (t t' : timeAt (Time := Time) p) :
    ((fiber p).join t t').1 = t.1 # t'.1 := by
  rfl

/-- Definition 2.2.2: the fiber bottom is `bottime p`. -/
theorem fiber_bot_apply (p : Ctrl) :
    ((fiber (Time := Time) p).bot).1 = bot p := by
  rfl

/-- Definition 2.2.2: the fiber top is `toptime p`. -/
theorem fiber_top_apply (p : Ctrl) :
    ((fiber (Time := Time) p).top).1 = top p := by
  rfl


/--
Definition 2.2.2: on a fixed controller fiber, located order is exactly the
bounded-semilattice order of `timeat p`.
-/
theorem le_iff_fiber_le
    {p : Ctrl} {s t : Time}
    (hs : controller s = p) (ht : controller t = p) :
    s ≼ t ↔ (fiber p).le ⟨s, hs⟩ ⟨t, ht⟩ := by
  constructor
  · intro hle
    apply Subtype.ext
    exact hle.2
  · intro hle
    constructor
    · exact hs.trans ht.symm
    · exact congrArg Subtype.val hle

/--
Definition 2.2.2: on a fixed controller fiber, located strict order is exactly
the bounded-semilattice strict order of `timeat p`.
-/
theorem lt_iff_fiber_lt
    {p : Ctrl} {s t : Time}
    (hs : controller s = p) (ht : controller t = p) :
    s ≺ t ↔ (fiber p).lt ⟨s, hs⟩ ⟨t, ht⟩ := by
  constructor
  · intro hlt
    exact ⟨(le_iff_fiber_le hs ht).mp hlt.1, by
      intro hsub
      exact hlt.2 (congrArg Subtype.val hsub)⟩
  · intro hlt
    exact ⟨(le_iff_fiber_le hs ht).mpr hlt.1, by
      intro h
      exact hlt.2 (Subtype.ext h)⟩

theorem le_refl (t : Time) : t ≼ t :=
  ⟨rfl, self_join_idem t⟩

theorem le_antisymm {t u : Time}
    (htu : t ≼ u) (hut : u ≼ t) : t = u := by
  calc
    t = u # t := hut.2.symm
    _ = t # u := self_join_comm hut.1
    _ = u := htu.2

theorem le_trans {t u v : Time}
    (htu : t ≼ u) (huv : u ≼ v) : t ≼ v := by
  constructor
  · exact htu.1.trans huv.1
  · calc
      t # v = t # (u # v) := by rw [huv.2]
      _ = (t # u) # v := (self_join_assoc htu.1 huv.1).symm
      _ = u # v := by rw [htu.2]
      _ = v := huv.2

theorem le_attest (t s : Time) : t ≼ (t # s) := by
  constructor
  · exact (controller_preserving t s).symm
  · calc
      t # (t # s) = (t # s) # t :=
        self_join_comm (controller_preserving t s).symm
      _ = t # s := expansive t s

/-- Within one controller fiber, the right input precedes the attestation:
`s ≼ t # s` when `t` and `s` share a controller. -/
theorem le_right_attest_of_same_controller
    {t s : Time}
    (hctrl : controller t = controller s) :
    s ≼ (t # s) := by
  have hle : s ≼ (s # t) := le_attest s t
  have hcomm : s # t = t # s :=
    self_join_comm hctrl.symm
  constructor
  · calc
      controller s = controller t := hctrl.symm
      _ = controller (t # s) := (controller_preserving t s).symm
  · calc
      s # (t # s) = s # (s # t) := by rw [hcomm]
      _ = s # t := hle.2
      _ = t # s := hcomm

theorem le_of_attest_le_same_controller_right
    {t s u : Time}
    (hctrl : controller t = controller s)
    (hle : (t # s) ≼ u) :
    s ≼ u := by
  exact le_trans (le_right_attest_of_same_controller hctrl) hle

/-- Remark 2.2.6: attestation is an expansive operator — `t ≼ t # s`. -/
theorem attestation_expansive_operator
    (t s : Time) :
    t ≼ (t # s) := by
  exact le_attest t s

/-- Definition 2.2.2(7): `t # s` is controlled by `t`'s controller
(controller-preserving) and `t ≼ t # s` (expansive). -/
theorem attest_left_controller_and_expansive
    (t s : Time) :
    controller (t # s) = controller t ∧ t ≼ (t # s) := by
  exact ⟨controller_preserving t s, le_attest t s⟩

/--
Remark 2.2.3, same-controller order component:
if `t'` precedes `t`, then their local join is `t`.
-/
theorem attest_eq_left_of_right_le
    {t t' : Time}
    (hle : t' ≼ t) :
    t # t' = t := by
  calc
    t # t' = t' # t := self_join_comm hle.1.symm
    _ = t := hle.2

/-- If `t ≼ t'` then their attestation is `t'`: `t # t' = t'`. -/
theorem attest_eq_right_of_left_le
    {t t' : Time}
    (hle : t ≼ t') :
    t # t' = t' := by
  exact hle.2

/-- Definition 2.2.2: the top time at a controller. -/
def topTime (p : Ctrl) : Time :=
  top p

/-- Definition 2.2.2: `toptime p` is controlled by `p`. -/
theorem topTime_controller (p : Ctrl) :
    controller (topTime (Time := Time) p) = p :=
  top_controller p

/-- Definition 2.2.2: the bottom time at a controller. -/
def botTime (p : Ctrl) : Time :=
  bot p

/-- Definition 2.2.2: `bottime p` is controlled by `p`. -/
theorem botTime_controller (p : Ctrl) :
    controller (botTime (Time := Time) p) = p :=
  bot_controller p

/-- Definition 2.2.2: `bottime p` is the bottom of the fiber `timeat p`. -/
theorem botTime_le {p : Ctrl} {t : Time}
    (hctrl : controller t = p) : (botTime p) ≼ t := by
  constructor
  · rw [botTime, bot_controller p, hctrl]
  · exact self_bot_le p t hctrl

/-- Definition 2.2.2: `toptime p` is the top of the fiber `timeat p`. -/
theorem le_topTime {p : Ctrl} {t : Time}
    (hctrl : controller t = p) : t ≼ (topTime p) := by
  constructor
  · rw [topTime, top_controller p, hctrl]
  · exact self_le_top p t hctrl

/-- Definition 2.2.2(5): local attestation is idempotent — `t # t = t`. -/
theorem attest_idem (t : Time) :
    t # t = t := by
  exact self_join_idem t

/-- Definition 2.2.2(5): local attestation is commutative within a controller
fiber. -/
theorem attest_comm_of_same_controller
    {t t' : Time}
    (hctrl : controller t = controller t') :
    t # t' = t' # t := by
  exact self_join_comm hctrl

/-- Definition 2.2.2(5): local attestation is associative within a controller
fiber. -/
theorem attest_assoc_of_same_controller
    {t t' u : Time}
    (htt' : controller t = controller t')
    (ht'u : controller t' = controller u) :
    (t # t') # u = t # (t' # u) := by
  exact self_join_assoc htt' ht'u

/-- Definition 2.2.2(5): `⊥_p` is a left identity for local attestation. -/
theorem attest_botTime_left_of_controller
    {p : Ctrl} {t : Time}
    (hctrl : controller t = p) :
    (botTime p) # t = t := by
  exact self_bot_le p t hctrl

/-- Definition 2.2.2(5): `⊥_p` is a right identity for local attestation. -/
theorem attest_botTime_right_of_controller
    {p : Ctrl} {t : Time}
    (hctrl : controller t = p) :
    t # (botTime p) = t := by
  calc
    t # (botTime p) = (botTime p) # t :=
      self_join_comm (hctrl.trans (botTime_controller p).symm)
    _ = t := attest_botTime_left_of_controller hctrl

/-- Definition 2.2.2(5): `⊤_p` absorbs local attestation on the left. -/
theorem attest_topTime_left_of_controller
    {p : Ctrl} {t : Time}
    (hctrl : controller t = p) :
    (topTime p) # t = topTime p := by
  calc
    (topTime p) # t = t # (topTime p) :=
      self_join_comm ((topTime_controller p).trans hctrl.symm)
    _ = topTime p := self_le_top p t hctrl

/-- Definition 2.2.2(5): `⊤_p` absorbs local attestation on the right. -/
theorem attest_topTime_right_of_controller
    {p : Ctrl} {t : Time}
    (hctrl : controller t = p) :
    t # (topTime p) = topTime p := by
  exact self_le_top p t hctrl

/-- Definition 2.2.2: a time is consistent when it is not its controller's top. -/
def ConsistentTime (t : Time) : Prop :=
  t ≠ top (controller t)

/-- Notation 2.2.4, `CTime`: a controller's top time is not consistent. -/
theorem not_consistent_topTime (p : Ctrl) :
    ¬ ConsistentTime (topTime (Time := Time) p) := by
  intro h
  exact h (by rw [topTime, top_controller p])

/--
Notation 2.2.4, `CTime = Time \ {toptime p | p in Ctrl}`: being consistent
is equivalent to being distinct from every controller top time.
-/
theorem consistentTime_iff_ne_topTime
    (t : Time) :
    ConsistentTime t ↔ ∀ p : Ctrl, t ≠ topTime p := by
  constructor
  · intro ht p htop
    have hctrl : controller t = p := by
      rw [htop]
      exact topTime_controller p
    exact ht (by
      rw [hctrl, htop]
      rfl)
  · intro htop ht
    exact htop (controller t) (by
      simpa [topTime] using ht)

/--
Located-time bottom-consistency identity: `bottime p` is
consistent exactly when it is not `toptime p`.
-/
theorem botTime_consistent_iff_ne_topTime
    (p : Ctrl) :
    ConsistentTime (botTime (Time := Time) p) ↔
      botTime (Time := Time) p ≠ topTime p := by
  unfold ConsistentTime botTime topTime
  rw [bot_controller p]

/-- Consistency is downward closed for the local order. -/
theorem consistentTime_of_le
    {s t : Time}
    (hle : s ≼ t) (ht : ConsistentTime t) :
    ConsistentTime s := by
  intro hs_top
  have hjoin_top : s # t = top (controller s) := by
    calc
      s # t = (top (controller s)) # t :=
        congrArg (fun x => x # t) hs_top
      _ = t # (top (controller s)) :=
        self_join_comm ((top_controller (controller s)).trans hle.1)
      _ = top (controller s) :=
        self_le_top (controller s) t hle.1.symm
  exact ht (by
    calc
      t = s # t := hle.2.symm
      _ = top (controller s) := hjoin_top
      _ = top (controller t) := by rw [hle.1])

/-- `⊥_p` is consistent exactly when controller `p` has some consistent time. -/
theorem botTime_consistent_iff_exists_consistent_at_controller
    (p : Ctrl) :
    ConsistentTime (botTime (Time := Time) p) ↔
      ∃ t : Time, controller t = p ∧ ConsistentTime t := by
  constructor
  · intro hbot
    exact ⟨botTime p, botTime_controller p, hbot⟩
  · intro hex
    rcases hex with ⟨t, hctrl, ht⟩
    exact consistentTime_of_le (botTime_le hctrl) ht

/-- Controller `p` has a consistent time exactly when `⊥_p ≠ ⊤_p`. -/
theorem exists_consistent_at_controller_iff_botTime_ne_topTime
    (p : Ctrl) :
    (∃ t : Time, controller t = p ∧ ConsistentTime t) ↔
      botTime (Time := Time) p ≠ topTime p :=
  (botTime_consistent_iff_exists_consistent_at_controller p).symm.trans
    (botTime_consistent_iff_ne_topTime p)

/-- If a controller fiber contains a consistent time, its bottom time `⊥_p` is
consistent. -/
theorem botTime_consistent_of_exists_consistent_at_controller
    (p : Ctrl)
    (hex : ∃ t : Time, controller t = p ∧ ConsistentTime t) :
    ConsistentTime (botTime (Time := Time) p) :=
  (botTime_consistent_iff_exists_consistent_at_controller p).mpr hex

/-- Definition 2.2.2(8): a located semilattice is sequential when every
controller fiber is sequential. -/
def Sequential : Prop :=
  ∀ p : Ctrl, (fiber (Time := Time) p).Sequential

theorem oneControllerOfBoundedSemilattice_le_iff
    {α : Type v} [BoundedSemilattice α] {t t' : α} :
    (oneControllerOfBoundedSemilattice).le t t' ↔ t ≤ t' := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨rfl, h⟩

theorem oneControllerOfBoundedSemilattice_consistentTime_iff
    {α : Type v} [BoundedSemilattice α] {t : α} :
    (oneControllerOfBoundedSemilattice).ConsistentTime t ↔ BoundedSemilattice.Consistent t := by
  rfl

theorem oneControllerOfBoundedSemilattice_sequential
    {α : Type v} [BoundedSemilattice α] (hseq : BoundedSemilattice.Sequential (α := α)) :
    (oneControllerOfBoundedSemilattice (α := α)).Sequential := by
  intro p t t'
  cases p
  rcases t with ⟨t, _ht⟩
  rcases t' with ⟨t', _ht'⟩
  rcases hseq t t' with hleft | hright | htop
  · exact Or.inl (Subtype.ext hleft)
  · exact Or.inr (Or.inl (Subtype.ext hright))
  · exact Or.inr (Or.inr (Subtype.ext htop))

/--
One-controller located semilattice obtained directly from an order-level
top-tree specification. This is model-construction support only; it supplies no
flags or Cut structure.
-/
noncomputable def oneControllerOfOrderTopTreeSpec
    (S : OrderTopTreeSpec.{v}) : LocatedSemilattice S.Carrier PUnit :=
  @oneControllerOfBoundedSemilattice S.Carrier S.toBoundedSemilattice

theorem oneControllerOfOrderTopTreeSpec_le_iff
    (S : OrderTopTreeSpec.{v}) {t t' : S.Carrier} :
    (oneControllerOfOrderTopTreeSpec S).le t t' ↔ S.le t t' :=
  (@oneControllerOfBoundedSemilattice_le_iff S.Carrier S.toBoundedSemilattice t t').trans
    S.toBoundedSemilattice_le_iff

theorem oneControllerOfOrderTopTreeSpec_consistentTime_iff
    (S : OrderTopTreeSpec.{v}) {t : S.Carrier} :
    (oneControllerOfOrderTopTreeSpec S).ConsistentTime t ↔
      t ≠ S.top :=
  @oneControllerOfBoundedSemilattice_consistentTime_iff S.Carrier S.toBoundedSemilattice t

theorem oneControllerOfOrderTopTreeSpec_sequential
    (S : OrderTopTreeSpec.{v}) :
    (oneControllerOfOrderTopTreeSpec S).Sequential :=
  @oneControllerOfBoundedSemilattice_sequential S.Carrier S.toBoundedSemilattice
    S.toBoundedSemilattice_sequential

theorem attest_eq_left_or_right_or_topTime_of_same_controller
    (hseq : Sequential (Time := Time))
    {p : Ctrl} {t t' : Time}
    (ht : controller t = p) (ht' : controller t' = p) :
    t # t' = t ∨ t # t' = t' ∨ t # t' = topTime p := by
  rcases hseq p ⟨t, ht⟩ ⟨t', ht'⟩ with hleft | hright | htop
  · exact Or.inl (by
      have hval := congrArg Subtype.val hleft
      simpa [fiber] using hval)
  · exact Or.inr (Or.inl (by
      have hval := congrArg Subtype.val hright
      simpa [fiber] using hval))
  · exact Or.inr (Or.inr (by
      have hval := congrArg Subtype.val htop
      simpa [fiber, topTime] using hval))

/-- Notation 2.2.4, `CTime`: all consistent times. -/
def CTime : Type v :=
  {t : Time // ConsistentTime t}

/-- Notation 2.2.4: a member of `CTime` is consistent. -/
theorem CTime_consistent (t : CTime (Time := Time)) :
    ConsistentTime t.1 :=
  t.2

/-- Notation 2.2.4: a member of `CTime` is not any controller top time. -/
theorem CTime_ne_topTime (t : CTime (Time := Time)) (p : Ctrl) :
    t.1 ≠ topTime p := by
  exact (consistentTime_iff_ne_topTime t.1).mp t.2 p

/-- Notation 2.2.4, `ctimeat p`: consistent times controlled by `p`. -/
def ctimeAt (p : Ctrl) : Type v :=
  {t : Time // controller t = p ∧ ConsistentTime t}

/-- Notation 2.2.4: `ctimeat p` lies inside `CTime`. -/
def ctimeAt_toCTime (p : Ctrl) (t : ctimeAt (Time := Time) p) :
    CTime (Time := Time) :=
  ⟨t.1, t.2.2⟩

/-- Notation 2.2.4: `ctimeat p` lies inside `timeat p`. -/
def ctimeAt_toTimeAt (p : Ctrl) (t : ctimeAt (Time := Time) p) :
    timeAt (Time := Time) p :=
  ⟨t.1, t.2.1⟩

/-- Notation 2.2.4: a member of `ctimeat p` is controlled by `p`. -/
theorem ctimeAt_controller (p : Ctrl) (t : ctimeAt (Time := Time) p) :
    controller t.1 = p :=
  t.2.1

/-- Notation 2.2.4: a member of `ctimeat p` is consistent. -/
theorem ctimeAt_consistent (p : Ctrl) (t : ctimeAt (Time := Time) p) :
    ConsistentTime t.1 :=
  t.2.2

/-- Notation 2.2.4: a member of `ctimeat p` is not `toptime p`. -/
theorem ctimeAt_ne_topTime (p : Ctrl) (t : ctimeAt (Time := Time) p) :
    t.1 ≠ topTime p := by
  exact (consistentTime_iff_ne_topTime t.1).mp t.2.2 p

/--
Notation 2.2.4: same-controller contradiction, extended so that
times at distinct controllers do not contradict.
-/
def Contradicts (s t : Time) : Prop :=
  RawContradicts controller attest top s t

/-- The located-semilattice contradiction relation supplies the `🗲` notation
via the shared `Contradictory` class; `s 🗲 t` is definitionally `Contradicts`. -/
instance : Contradictory Time := ⟨Contradicts⟩

/-- Same-controller top join gives contradiction. -/
theorem contradicts_of_same_controller
    {s t : Time}
    (hctrl : controller s = controller t)
    (hjoin : s # t = top (controller s)) : s 🗲 t :=
  ⟨hctrl, hjoin⟩

/-- Lemma 2.2.5: `s 🗲 t` holds exactly when `controller s = controller t` and
`s # t = ⊤_{controller s}`. -/
theorem contradicts_iff
    {s t : Time} :
    s 🗲 t ↔
      controller s = controller t ∧ s # t = top (controller s) := by
  rfl

/-- Lemma 2.2.5: contradiction implies same controller. -/
theorem controller_eq_of_contradicts
    {s t : Time} (h : s 🗲 t) :
    controller s = controller t := by
  exact h.1

/--
Lemma 2.2.5: contradiction means the same-controller
join reaches that controller's top.
-/
theorem attest_eq_top_of_contradicts
    {s t : Time} (h : s 🗲 t) :
    s # t = top (controller s) := by
  exact h.2

/-- Under a same-controller hypothesis, `s 🗲 t` holds exactly when
`s # t = ⊤_{controller s}`. -/
theorem contradicts_iff_attest_eq_top_of_controller
    {s t : Time} (hctrl : controller s = controller t) :
    s 🗲 t ↔ s # t = top (controller s) := by
  constructor
  · intro h
    exact h.2
  · intro htop
    exact ⟨hctrl, htop⟩

/-- On a fixed controller fiber, located contradiction agrees with the fiber's
bounded-semilattice contradiction. -/
theorem contradicts_iff_fiber_contradicts
    {p : Ctrl} {s t : Time}
    (hs : controller s = p) (ht : controller t = p) :
    s 🗲 t ↔ (fiber p).Contradicts ⟨s, hs⟩ ⟨t, ht⟩ := by
  constructor
  · intro h
    apply Subtype.ext
    simpa [fiber] using h.2.trans (by rw [hs])
  · intro h
    constructor
    · exact hs.trans ht.symm
    · have hval := congrArg Subtype.val h
      simpa [fiber, hs] using hval

theorem same_controller_incomparable_iff_contradicts_of_consistentTime
    (hseq : Sequential (Time := Time)) {p : Ctrl} {s t : Time}
    (hs_ctrl : controller s = p) (ht_ctrl : controller t = p)
    (hs : ConsistentTime s) (ht : ConsistentTime t) :
    (¬ s ≼ t ∧ ¬ t ≼ s) ↔ s 🗲 t := by
  let sf : timeAt (Time := Time) p := ⟨s, hs_ctrl⟩
  let tf : timeAt (Time := Time) p := ⟨t, ht_ctrl⟩
  have hs_cons : (fiber p).Consistent sf := by
    intro htop
    apply hs
    have hval : s = top p := congrArg Subtype.val htop
    simpa [hs_ctrl] using hval
  have ht_cons : (fiber p).Consistent tf := by
    intro htop
    apply ht
    have hval : t = top p := congrArg Subtype.val htop
    simpa [ht_ctrl] using hval
  have hfiber :
      (fiber p).Incomparable sf tf ↔ (fiber p).Contradicts sf tf :=
    (fiber p).incomparable_iff_contradicts_of_consistent (hseq p) hs_cons ht_cons
  constructor
  · intro hinc
    have hfiber_inc : (fiber p).Incomparable sf tf := by
      constructor
      · intro hle
        exact hinc.1 ((le_iff_fiber_le hs_ctrl ht_ctrl).mpr hle)
      · intro hle
        exact hinc.2 ((le_iff_fiber_le ht_ctrl hs_ctrl).mpr hle)
    exact (contradicts_iff_fiber_contradicts hs_ctrl ht_ctrl).mpr
      (hfiber.mp hfiber_inc)
  · intro hcontr
    have hfiber_contr : (fiber p).Contradicts sf tf :=
      (contradicts_iff_fiber_contradicts hs_ctrl ht_ctrl).mp hcontr
    have hfiber_inc : (fiber p).Incomparable sf tf :=
      hfiber.mpr hfiber_contr
    constructor
    · intro hle
      exact hfiber_inc.1 ((le_iff_fiber_le hs_ctrl ht_ctrl).mp hle)
    · intro hle
      exact hfiber_inc.2 ((le_iff_fiber_le ht_ctrl hs_ctrl).mp hle)

/-- In a sequential located semilattice, same-controller consistent incomparable
times contradict (Lemma 2.1.7 within a fiber). -/
theorem contradicts_of_same_controller_incomparable_consistentTime
    (hseq : Sequential (Time := Time))
    {p : Ctrl} {s t : Time}
    (hs_ctrl : controller s = p) (ht_ctrl : controller t = p)
    (hs : ConsistentTime s) (ht : ConsistentTime t)
    (hinc : ¬ s ≼ t ∧ ¬ t ≼ s) :
    s 🗲 t := by
  exact
    (same_controller_incomparable_iff_contradicts_of_consistentTime
      hseq hs_ctrl ht_ctrl hs ht).mp hinc

/-- In a sequential controller fiber, consistent incomparable times join to
`⊤_p`. -/
theorem attest_eq_topTime_of_same_controller_incomparable_consistentTime
    (hseq : Sequential (Time := Time))
    {p : Ctrl} {s t : Time}
    (hs_ctrl : controller s = p) (ht_ctrl : controller t = p)
    (hs : ConsistentTime s) (ht : ConsistentTime t)
    (hinc : ¬ s ≼ t ∧ ¬ t ≼ s) :
    s # t = topTime p := by
  have hcontr :
      s 🗲 t :=
    contradicts_of_same_controller_incomparable_consistentTime
      hseq hs_ctrl ht_ctrl hs ht hinc
  simpa [topTime, hs_ctrl] using hcontr.2

/-- In a sequential located semilattice, same-controller consistent
contradictory times are incomparable (Lemma 2.1.7 within a fiber). -/
theorem incomparable_of_same_controller_contradicts_consistentTime
    (hseq : Sequential (Time := Time))
    {p : Ctrl} {s t : Time}
    (hs_ctrl : controller s = p) (ht_ctrl : controller t = p)
    (hs : ConsistentTime s) (ht : ConsistentTime t)
    (hcontr : s 🗲 t) :
    ¬ s ≼ t ∧ ¬ t ≼ s := by
  exact
    (same_controller_incomparable_iff_contradicts_of_consistentTime
      hseq hs_ctrl ht_ctrl hs ht).mpr hcontr

/-- Any time at `p` contradicts `⊤_p`. -/
theorem contradicts_topTime_right
    {p : Ctrl} {t : Time}
    (hctrl : controller t = p) : t 🗲 (topTime p) := by
  constructor
  · rw [topTime, top_controller p, hctrl]
  · calc
      t # (topTime p) = t # (top p) := rfl
      _ = top p := self_le_top p t hctrl
      _ = top (controller t) := by rw [hctrl]

/-- `⊤_p` contradicts any time at `p`. -/
theorem contradicts_topTime_left
    {p : Ctrl} {t : Time}
    (hctrl : controller t = p) : (topTime p) 🗲 t := by
  have hright := contradicts_topTime_right hctrl
  constructor
  · exact topTime_controller p |>.trans hctrl.symm
  · calc
      (topTime p) # t = t # (topTime p) :=
        self_join_comm ((topTime_controller p).trans hctrl.symm)
      _ = top (controller t) := hright.2
      _ = top (controller (topTime p)) := by
        rw [topTime_controller p, hctrl]

/-- A time self-contradicts exactly when it is not consistent. -/
theorem contradicts_self_iff_not_consistentTime
    (t : Time) :
    t 🗲 t ↔ ¬ ConsistentTime t := by
  constructor
  · intro h ht
    exact ht ((self_join_idem t).symm.trans h.2)
  · intro h
    have ht_top : t = top (controller t) := Classical.not_not.mp h
    constructor
    · rfl
    · calc
        t # t = t := self_join_idem t
        _ = top (controller t) := ht_top

/-- Consistent times do not self-contradict. -/
theorem not_contradicts_self_of_consistentTime
    {t : Time}
    (ht : ConsistentTime t) : ¬ t 🗲 t := by
  intro h
  exact (contradicts_self_iff_not_consistentTime t).mp h ht

/--
If comparable times at one controller contradict, the upper time is the
controller's top time.
-/
theorem eq_topTime_of_le_and_contradicts_right
    {s t : Time}
    (hle : s ≼ t) (hcontr : s 🗲 t) :
    t = topTime (controller t) := by
  rw [topTime]
  calc
    t = s # t := hle.2.symm
    _ = top (controller s) := hcontr.2
    _ = top (controller t) := by rw [hle.1]

/--
Lemma 2.2.5, order consequence: if the right time lies
below a contradictory left time, the left time is the controller top.
-/
theorem eq_topTime_of_le_and_contradicts_left
    {s t : Time}
    (hle : t ≼ s) (hcontr : s 🗲 t) :
    s = topTime (controller s) := by
  rw [topTime]
  calc
    s = t # s := hle.2.symm
    _ = s # t := self_join_comm hle.1
    _ = top (controller s) := hcontr.2

/--
Lemma 2.2.5, order consequence: a consistent right time
cannot lie above a contradictory left time.
-/
theorem not_le_right_of_contradicts_consistentTime
    {s t : Time}
    (hcontr : s 🗲 t) (ht : ConsistentTime t) :
    ¬ s ≼ t := by
  intro hle
  exact ht (by
    simpa [topTime] using eq_topTime_of_le_and_contradicts_right hle hcontr)

/--
Lemma 2.2.5, order consequence: a consistent left time
cannot lie above a contradictory right time.
-/
theorem not_le_left_of_contradicts_consistentTime
    {s t : Time}
    (hcontr : s 🗲 t) (hs : ConsistentTime s) :
    ¬ t ≼ s := by
  intro hle
  exact hs (by
    simpa [topTime] using eq_topTime_of_le_and_contradicts_left hle hcontr)

/--
Lemma 2.2.5, direct order consequence: a consistent
right time cannot contradict a lower left time.
-/
theorem not_contradicts_right_of_le_of_consistentTime
    {s t : Time}
    (hle : s ≼ t) (ht : ConsistentTime t) :
    ¬ s 🗲 t := by
  intro hcontr
  exact not_le_right_of_contradicts_consistentTime hcontr ht hle

/--
Lemma 2.2.5, direct order consequence: a consistent
left time cannot contradict a lower right time.
-/
theorem not_contradicts_left_of_le_of_consistentTime
    {s t : Time}
    (hle : t ≼ s) (hs : ConsistentTime s) :
    ¬ s 🗲 t := by
  intro hcontr
  exact not_le_left_of_contradicts_consistentTime hcontr hs hle

/-- Definition 2.2.2(7c): attestation is contradiction-preserving — if `s 🗲 s'`
then `t # s 🗲 t' # s'`. -/
theorem contradicts_attest
    {t t' s s' : Time}
    (htt' : controller t = controller t')
    (hss' : controller s = controller s')
    (hcontr : s 🗲 s') :
    (t # s) 🗲 (t' # s') :=
  contradiction_preserving htt' hss' hcontr

/-- Contradictory times stay contradictory after attestation by matching
left-controller times (a consequence of contradiction-preservation). -/
theorem attest_transports_contradiction
    {t t' s s' : Time}
    (htt' : controller t = controller t')
    (hcontr : s 🗲 s') :
    (t # s) 🗲 (t' # s') := by
  exact contradicts_attest htt' hcontr.1 hcontr

/-- Times at distinct controllers cannot contradict. -/
theorem not_contradicts_of_controller_ne
    {s t : Time}
    (hctrl : controller s ≠ controller t) : ¬ s 🗲 t := by
  intro h
  exact hctrl h.1

theorem contradicts_of_le_right
    {a b c : Time}
    (hbc : b ≼ c) (hab : a 🗲 b) : a 🗲 c := by
  constructor
  · exact hab.1.trans hbc.1
  · have hca : controller c = controller a := (hab.1.trans hbc.1).symm
    calc
      a # c = a # (b # c) := by rw [hbc.2]
      _ = (a # b) # c := (self_join_assoc hab.1 hbc.1).symm
      _ = (top (controller a)) # c := by rw [hab.2]
      _ = c # (top (controller a)) :=
        self_join_comm ((top_controller (controller a)).trans hca.symm)
      _ = top (controller a) := self_le_top (controller a) c hca

theorem contradicts_symm
    {s t : Time}
    (h : s 🗲 t) : t 🗲 s := by
  constructor
  · exact h.1.symm
  · calc
      t # s = s # t := self_join_comm h.1.symm
      _ = top (controller s) := h.2
      _ = top (controller t) := by rw [h.1]

theorem contradicts_of_le_left
    {a b c : Time}
    (hac : a ≼ c) (hab : a 🗲 b) : c 🗲 b := by
  exact contradicts_symm (contradicts_of_le_right hac (contradicts_symm hab))

theorem contradicts_of_le_both
    {a a' b b' : Time}
    (haa' : a ≼ a') (hbb' : b ≼ b') (hab : a 🗲 b) :
    a' 🗲 b' := by
  exact contradicts_of_le_right hbb' (contradicts_of_le_left haa' hab)

/-- Lemma 2.2.5: `s 🗲 t` gives `controller s = controller t` and
`s # t = ⊤_{controller s}`. -/
theorem repackages {s t : Time} (h : s 🗲 t) :
    controller s = controller t ∧ s # t = top (controller s) := by
  exact h

end LocatedSemilattice

end ContForm.Foundation.LocatedSemilattices.Basic
