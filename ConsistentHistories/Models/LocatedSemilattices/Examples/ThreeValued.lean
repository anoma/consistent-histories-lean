import ConsistentHistories.Models.LocatedSemilattices.Examples.CakeFigure

namespace ConsistentHistories.Models.LocatedSemilattices.Examples

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.LocatedSemilattices.TopTrees

/-- Example 2.3.2: the truth values `3 = {f, b, t}` under the order `f < b < t`. -/
inductive ThreeValue where
  | false
  | both
  | true
  deriving DecidableEq

namespace ThreeValue

/-- Example 2.3.2: the join `∨` on `3`, the least upper bound for `f < b < t`. -/
def join : ThreeValue → ThreeValue → ThreeValue
  | false, x => x
  | x, false => x
  | true, _ => true
  | _, true => true
  | both, both => both

/-- Example 2.3.2: truth-value negation `¬`, with `¬t = f`, `¬f = t`, `¬b = b`. -/
def neg : ThreeValue → ThreeValue
  | false => true
  | both => both
  | true => false

theorem join_idem (x : ThreeValue) : join x x = x := by
  cases x <;> rfl

theorem join_comm (x y : ThreeValue) : join x y = join y x := by
  cases x <;> cases y <;> rfl

theorem join_assoc (x y z : ThreeValue) :
    join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem bot_le (x : ThreeValue) : join false x = x := by
  cases x <;> rfl

theorem le_top (x : ThreeValue) : join x true = true := by
  cases x <;> rfl

end ThreeValue

/-- Example 2.3.2: the bounded semilattice `3 = {f, b, t}` with `f < b < t`. -/
instance threeValueSemilattice : BoundedSemilattice ThreeValue where
  join := ThreeValue.join
  bot := ThreeValue.false
  top := ThreeValue.true
  join_idem := ThreeValue.join_idem
  join_comm := ThreeValue.join_comm
  join_assoc := ThreeValue.join_assoc
  bot_le := ThreeValue.bot_le
  le_top := ThreeValue.le_top

/-- Example 2.3.2: the order on `3`, i.e. `x ≤ y` iff `x = f`, `y = t`, or `x = y`. -/
theorem threeValueSemilattice_le_iff (x y : ThreeValue) :
    x ≤ y ↔
      x = ThreeValue.false ∨ y = ThreeValue.true ∨ x = y := by
  constructor
  · intro h
    cases x <;> cases y <;>
      simp [threeValueSemilattice, BoundedSemilattice.le, LE.le, ThreeValue.join] at h ⊢
  · intro h
    cases x <;> cases y <;>
      simp [threeValueSemilattice, BoundedSemilattice.le, LE.le, ThreeValue.join] at h ⊢

/-- Example 2.3.2: the bounded semilattice `3` is sequential. -/
theorem threeValueSemilattice_sequential : threeValueSemilattice.Sequential := by
  intro x y
  cases x <;> cases y <;> simp [threeValueSemilattice, ThreeValue.join]

/-- Example 2.3.2: the two controllers `Ctrl = {P, Q}`. -/
inductive ThreeCtrl where
  | p
  | q
  deriving DecidableEq

/-- Example 2.3.2: times are controller/truth-value pairs, `Time = Ctrl × 3`. -/
abbrev ThreeTime := ThreeCtrl × ThreeValue

/-- Example 2.3.2: the cross-controller (`p ≠ p'`) truth value `tv ∨ ¬tv ∨ tv' ∨ ¬tv'`. -/
def threeCrossAttest (x y : ThreeValue) : ThreeValue :=
  ThreeValue.join (ThreeValue.join x (ThreeValue.neg x))
    (ThreeValue.join y (ThreeValue.neg y))

/-- Example 2.3.2: attestation `#`, `(p, tv) # (p', tv')` equal to `(p, tv ∨ tv')` when
`p = p'` and to `(p, tv ∨ ¬tv ∨ tv' ∨ ¬tv')` when `p ≠ p'`. -/
def threeAttest : ThreeTime → ThreeTime → ThreeTime
  | (ctrl, x), (ctrl', y) =>
      if ctrl = ctrl' then (ctrl, ThreeValue.join x y) else (ctrl, threeCrossAttest x y)

/--
Example 2.3.3: the times for the monotone variant, again `Time = Ctrl × 3`.

This is intentionally a separate carrier from `ThreeTime`: the two examples
have different attestation operations, so they must not share one global
`LocatedSemilattice` instance for the same time type.
-/
structure SimplerThreeTime where
  ctrl : ThreeCtrl
  value : ThreeValue
  deriving DecidableEq

/-- Example 2.3.3: the monotone attestation `(p, tv) # (p', tv') = (p, tv ∨ tv')`, taken
regardless of whether `p = p'`. -/
def simplerThreeAttest : SimplerThreeTime → SimplerThreeTime → SimplerThreeTime
  | ⟨ctrl, x⟩, ⟨_ctrl', y⟩ => ⟨ctrl, ThreeValue.join x y⟩

/-- Example 2.3.2: the simple located semilattice `L = (Ctrl, Time, #, ctrl)`. -/
instance threeLocatedSemilattice : LocatedSemilattice ThreeTime ThreeCtrl where
  attest := threeAttest
  controller := Prod.fst
  bot ctrl := (ctrl, ThreeValue.false)
  top ctrl := (ctrl, ThreeValue.true)
  bot_controller := by
    intro ctrl
    rfl
  top_controller := by
    intro ctrl
    rfl
  controller_preserving := by
    intro t s
    rcases t with ⟨ctrl, x⟩
    rcases s with ⟨ctrl', y⟩
    by_cases h : ctrl = ctrl' <;> simp [threeAttest, h]
  self_join_idem := by
    intro t
    rcases t with ⟨ctrl, x⟩
    simp [threeAttest, ThreeValue.join_idem]
  self_join_comm := by
    intro t t' hctrl
    rcases t with ⟨ctrl, x⟩
    rcases t' with ⟨ctrl', y⟩
    cases hctrl
    simp [threeAttest, ThreeValue.join_comm]
  self_join_assoc := by
    intro t t' u hctrl hctrl'
    rcases t with ⟨ctrl, x⟩
    rcases t' with ⟨ctrl', y⟩
    rcases u with ⟨ctrl'', z⟩
    cases hctrl
    cases hctrl'
    simp [threeAttest, ThreeValue.join_assoc]
  self_bot_le := by
    intro ctrl t hctrl
    rcases t with ⟨ctrl', x⟩
    cases hctrl
    simp [threeAttest, ThreeValue.bot_le]
  self_le_top := by
    intro ctrl t hctrl
    rcases t with ⟨ctrl', x⟩
    cases hctrl
    simp [threeAttest, ThreeValue.le_top]
  expansive := by
    intro t s
    rcases t with ⟨ctrl, x⟩
    rcases s with ⟨ctrl', y⟩
    cases ctrl <;> cases ctrl' <;> cases x <;> cases y <;> rfl
  contradiction_preserving := by
    intro t t' s s' hctrl hctrl' hcontr
    rcases t with ⟨ctrl, x⟩
    rcases t' with ⟨ctrl', x'⟩
    rcases s with ⟨param, y⟩
    rcases s' with ⟨param', y'⟩
    cases hctrl
    cases hctrl'
    cases ctrl <;> cases param <;> cases x <;> cases x' <;> cases y <;> cases y' <;>
      simp [RawContradicts, threeAttest, threeCrossAttest, ThreeValue.join, ThreeValue.neg]
        at hcontr ⊢

/-- Example 2.3.3: the monotone located semilattice `L = (Ctrl, Time, #, ctrl)`. -/
instance simplerThreeLocatedSemilattice : LocatedSemilattice SimplerThreeTime ThreeCtrl where
  attest := simplerThreeAttest
  controller := SimplerThreeTime.ctrl
  bot ctrl := ⟨ctrl, ThreeValue.false⟩
  top ctrl := ⟨ctrl, ThreeValue.true⟩
  bot_controller := by
    intro ctrl
    rfl
  top_controller := by
    intro ctrl
    rfl
  controller_preserving := by
    intro t s
    rcases t with ⟨ctrl, x⟩
    rcases s with ⟨ctrl', y⟩
    rfl
  self_join_idem := by
    intro t
    rcases t with ⟨ctrl, x⟩
    simp [simplerThreeAttest, ThreeValue.join_idem]
  self_join_comm := by
    intro t t' hctrl
    rcases t with ⟨ctrl, x⟩
    rcases t' with ⟨ctrl', y⟩
    cases hctrl
    simp [simplerThreeAttest, ThreeValue.join_comm]
  self_join_assoc := by
    intro t t' u hctrl hctrl'
    rcases t with ⟨ctrl, x⟩
    rcases t' with ⟨ctrl', y⟩
    rcases u with ⟨ctrl'', z⟩
    cases hctrl
    cases hctrl'
    simp [simplerThreeAttest, ThreeValue.join_assoc]
  self_bot_le := by
    intro ctrl t hctrl
    rcases t with ⟨ctrl', x⟩
    cases hctrl
    simp [simplerThreeAttest, ThreeValue.bot_le]
  self_le_top := by
    intro ctrl t hctrl
    rcases t with ⟨ctrl', x⟩
    cases hctrl
    simp [simplerThreeAttest, ThreeValue.le_top]
  expansive := by
    intro t s
    rcases t with ⟨ctrl, x⟩
    rcases s with ⟨ctrl', y⟩
    cases ctrl <;> cases ctrl' <;> cases x <;> cases y <;> rfl
  contradiction_preserving := by
    intro t t' s s' hctrl hctrl' hcontr
    rcases t with ⟨ctrl, x⟩
    rcases t' with ⟨ctrl', x'⟩
    rcases s with ⟨param, y⟩
    rcases s' with ⟨param', y'⟩
    cases hctrl
    cases hctrl'
    cases ctrl <;> cases param <;> cases x <;> cases x' <;> cases y <;> cases y' <;>
      simp [RawContradicts, simplerThreeAttest, ThreeValue.join] at hcontr ⊢

/-- Example 2.3.2: the cross-controller value of `b` and `f` is `t`. -/
theorem three_cross_false :
    threeCrossAttest ThreeValue.both ThreeValue.false = ThreeValue.true := by
  rfl

/-- Example 2.3.2: the cross-controller value of `b` and `b` is `b`. -/
theorem three_cross_both :
    threeCrossAttest ThreeValue.both ThreeValue.both = ThreeValue.both := by
  rfl

/-- Example 2.3.2: the cross-controller value of `f` and `b` is `t`. -/
theorem three_cross_input_false :
    threeCrossAttest ThreeValue.false ThreeValue.both = ThreeValue.true := by
  rfl

/-- Example 2.3.2: `#` is not monotone in its second argument — `(q, f) ≼ (q, b)` yet
`(p, b) # (q, f) = (p, t)` is not `≼ (p, b) = (p, b) # (q, b)`. -/
theorem threeAttest_not_monotone_second_component :
    (ThreeCtrl.q, ThreeValue.false) ≼ (ThreeCtrl.q, ThreeValue.both) ∧
      threeAttest (ThreeCtrl.p, ThreeValue.both) (ThreeCtrl.q, ThreeValue.false) =
        (ThreeCtrl.p, ThreeValue.true) ∧
      threeAttest (ThreeCtrl.p, ThreeValue.both) (ThreeCtrl.q, ThreeValue.both) =
        (ThreeCtrl.p, ThreeValue.both) ∧
      ¬ (threeAttest (ThreeCtrl.p, ThreeValue.both) (ThreeCtrl.q, ThreeValue.false)) ≼
        (threeAttest (ThreeCtrl.p, ThreeValue.both) (ThreeCtrl.q, ThreeValue.both)) := by
  constructor
  · constructor
    · rfl
    · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · intro hle
        change (ThreeCtrl.p, ThreeValue.true) ≼ (ThreeCtrl.p, ThreeValue.both) at hle
        exact (by
          cases hle.2)

/-- Example 2.3.2: `#` is not monotone in its first argument — `(p, f) ≼ (p, b)` yet
`(p, f) # (q, b) = (p, t)` is not `≼ (p, b) = (p, b) # (q, b)`. -/
theorem threeAttest_not_monotone_first_component :
    (ThreeCtrl.p, ThreeValue.false) ≼ (ThreeCtrl.p, ThreeValue.both) ∧
      threeAttest (ThreeCtrl.p, ThreeValue.false) (ThreeCtrl.q, ThreeValue.both) =
        (ThreeCtrl.p, ThreeValue.true) ∧
      threeAttest (ThreeCtrl.p, ThreeValue.both) (ThreeCtrl.q, ThreeValue.both) =
        (ThreeCtrl.p, ThreeValue.both) ∧
      ¬ (threeAttest (ThreeCtrl.p, ThreeValue.false) (ThreeCtrl.q, ThreeValue.both)) ≼
        (threeAttest (ThreeCtrl.p, ThreeValue.both) (ThreeCtrl.q, ThreeValue.both)) := by
  constructor
  · constructor
    · rfl
    · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · intro hle
        change (ThreeCtrl.p, ThreeValue.true) ≼ (ThreeCtrl.p, ThreeValue.both) at hle
        exact (by
          cases hle.2)

/-- Example 2.3.2: attestation `#` is monotone in neither of its two arguments. -/
theorem threeAttest_exists_not_monotone_either_component :
    (∃ t s s' : ThreeTime, s ≼ s' ∧ ¬ (threeAttest t s) ≼ (threeAttest t s')) ∧
      (∃ t t' s : ThreeTime, t ≼ t' ∧ ¬ (threeAttest t s) ≼ (threeAttest t' s)) := by
  constructor
  · exact
      ⟨(ThreeCtrl.p, ThreeValue.both),
        (ThreeCtrl.q, ThreeValue.false),
        (ThreeCtrl.q, ThreeValue.both),
        threeAttest_not_monotone_second_component.1,
        threeAttest_not_monotone_second_component.2.2.2⟩
  · exact
      ⟨(ThreeCtrl.p, ThreeValue.false),
        (ThreeCtrl.p, ThreeValue.both),
        (ThreeCtrl.q, ThreeValue.both),
        threeAttest_not_monotone_first_component.1,
        threeAttest_not_monotone_first_component.2.2.2⟩

/-- Example 2.3.3: the monotone attestation is monotone in its first argument. -/
theorem simplerThreeAttest_monotone_first_component
    {t t' s : SimplerThreeTime} (hle : t ≼ t') :
    simplerThreeAttest t s ≼ simplerThreeAttest t' s := by
  rcases t with ⟨ctrl, x⟩
  rcases t' with ⟨ctrl', x'⟩
  rcases s with ⟨param, y⟩
  cases hle.1
  cases ctrl <;> cases param <;> cases x <;> cases x' <;> cases y <;>
    simp [LocatedSemilattice.le, simplerThreeLocatedSemilattice, simplerThreeAttest,
      ThreeValue.join] at hle ⊢

/-- Example 2.3.3: the monotone attestation is monotone in its second argument. -/
theorem simplerThreeAttest_monotone_second_component
    {t s s' : SimplerThreeTime} (hle : s ≼ s') :
    simplerThreeAttest t s ≼ simplerThreeAttest t s' := by
  rcases t with ⟨ctrl, x⟩
  rcases s with ⟨param, y⟩
  rcases s' with ⟨param', y'⟩
  cases hle.1
  cases ctrl <;> cases param <;> cases x <;> cases y <;> cases y' <;>
    simp [LocatedSemilattice.le, simplerThreeLocatedSemilattice, simplerThreeAttest,
      ThreeValue.join] at hle ⊢

/-- Example 2.3.2: the simple located semilattice `L` is sequential. -/
theorem simpleLocatedSemilattice_sequential :
    threeLocatedSemilattice.Sequential := by
  intro ctrl
  intro t t'
  rcases t with ⟨⟨ctrl_t, x⟩, ht⟩
  rcases t' with ⟨⟨ctrl_t', y⟩, ht'⟩
  cases ctrl <;> cases ctrl_t <;> cases ctrl_t' <;>
    cases x <;> cases y <;>
      simp [LocatedSemilattice.fiber, threeLocatedSemilattice, threeAttest,
        ThreeValue.join] at ht ht' ⊢

/-- Example 2.3.3: the monotone located semilattice `L` is sequential. -/
theorem simplerLocatedSemilattice_sequential :
    simplerThreeLocatedSemilattice.Sequential := by
  intro ctrl
  intro t t'
  rcases t with ⟨⟨ctrl_t, x⟩, ht⟩
  rcases t' with ⟨⟨ctrl_t', y⟩, ht'⟩
  cases ctrl <;> cases ctrl_t <;> cases ctrl_t' <;>
    cases x <;> cases y <;>
      simp [LocatedSemilattice.fiber, simplerThreeLocatedSemilattice, simplerThreeAttest,
        ThreeValue.join] at ht ht' ⊢

end ConsistentHistories.Models.LocatedSemilattices.Examples
