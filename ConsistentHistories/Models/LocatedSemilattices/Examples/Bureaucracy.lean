import ConsistentHistories.Models.LocatedSemilattices.Examples.GamePlay

namespace ConsistentHistories.Models.LocatedSemilattices.Examples

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.LocatedSemilattices.TopTrees

/-- Example 2.3.6: states `State = ℕ ∪ {⊤}` — natural stages plus a failure top. -/
inductive BureaucracyState where
  | nat (n : Nat)
  | top
  deriving DecidableEq

namespace BureaucracyState

/-- Example 2.3.6: the state join is `max` on naturals with `⊤` absorbing. -/
def join : BureaucracyState → BureaucracyState → BureaucracyState
  | nat n, nat m => nat (Nat.max n m)
  | top, _ => top
  | _, top => top

theorem join_idem (x : BureaucracyState) : join x x = x := by
  cases x with
  | nat _n =>
      simp [join]
  | top =>
      rfl

theorem join_comm (x y : BureaucracyState) : join x y = join y x := by
  cases x with
  | nat n =>
      cases y with
      | nat m =>
          simp [join, Nat.max_comm]
      | top =>
          rfl
  | top =>
      cases y <;> rfl

theorem join_assoc (x y z : BureaucracyState) :
    join (join x y) z = join x (join y z) := by
  cases x with
  | nat n =>
      cases y with
      | nat m =>
          cases z with
          | nat k =>
              simp [join, Nat.max_assoc]
          | top =>
              rfl
      | top =>
          cases z <;> rfl
  | top =>
      cases y <;> cases z <;> rfl

theorem bot_le (x : BureaucracyState) : join (nat 0) x = x := by
  cases x with
  | nat _n =>
      simp [join]
  | top =>
      rfl

theorem le_top (x : BureaucracyState) : join x top = top := by
  cases x <;> rfl

end BureaucracyState

/-- Example 2.3.6: the bounded semilattice `State = ℕ ∪ {⊤}` ordered `0 < 1 < 2 < ⋯ < ⊤`. -/
instance bureaucracyStateSemilattice : BoundedSemilattice BureaucracyState where
  join := BureaucracyState.join
  bot := BureaucracyState.nat 0
  top := BureaucracyState.top
  join_idem := BureaucracyState.join_idem
  join_comm := BureaucracyState.join_comm
  join_assoc := BureaucracyState.join_assoc
  bot_le := BureaucracyState.bot_le
  le_top := BureaucracyState.le_top

/-- Example 2.3.6: the join of two natural states is their `max`. -/
theorem bureaucracyState_nat_join_nat (n m : Nat) :
    BureaucracyState.join (BureaucracyState.nat n) (BureaucracyState.nat m) =
      BureaucracyState.nat (Nat.max n m) := by
  rfl

/-- Example 2.3.6: joining any natural state with `⊤` gives `⊤`. -/
theorem bureaucracyState_nat_join_top (n : Nat) :
    BureaucracyState.join (BureaucracyState.nat n) BureaucracyState.top =
      BureaucracyState.top := by
  rfl

/-- Example 2.3.6: the bottom state `0` is a join identity on naturals. -/
theorem bureaucracyState_zero_join_nat (n : Nat) :
    BureaucracyState.join (BureaucracyState.nat 0) (BureaucracyState.nat n) =
      BureaucracyState.nat n := by
  simp [BureaucracyState.join]

/-- If `max n m = m` then `n ≤ m`. -/
private theorem nat_le_of_max_eq_right {n m : Nat} (h : Nat.max n m = m) : n <= m := by
  induction n generalizing m with
  | zero =>
      exact Nat.zero_le m
  | succ n ih =>
      cases m with
      | zero =>
          simp at h
      | succ m =>
          apply Nat.succ_le_succ
          apply ih
          simp at h
          exact h

/--
Example 2.3.6: the bureaucracy state order is the usual natural-number
order with `top` above every natural state.
-/
theorem bureaucracyStateSemilattice_le_iff
    (x y : BureaucracyState) :
    x ≤ y ↔
      match x, y with
      | BureaucracyState.nat n, BureaucracyState.nat m => n <= m
      | _, BureaucracyState.top => True
      | BureaucracyState.top, BureaucracyState.nat _ => False := by
  constructor
  · intro h
    cases x with
    | nat n =>
        cases y with
        | nat m =>
            simp [bureaucracyStateSemilattice, BoundedSemilattice.le, LE.le, -Nat.le_eq,
              BureaucracyState.join] at h
            exact nat_le_of_max_eq_right h
        | top =>
            exact True.intro
    | top =>
        cases y with
        | nat _m =>
            simp [bureaucracyStateSemilattice, BoundedSemilattice.le, LE.le, -Nat.le_eq,
              BureaucracyState.join] at h
        | top =>
            exact True.intro
  · intro h
    cases x with
    | nat n =>
        cases y with
        | nat m =>
            simp [bureaucracyStateSemilattice, BoundedSemilattice.le, LE.le, -Nat.le_eq,
              BureaucracyState.join, Nat.max_eq_right h]
        | top =>
            rfl
    | top =>
        cases y with
        | nat _m =>
            exact False.elim h
        | top =>
            rfl

/-- Example 2.3.6: consecutive natural bureaucracy states strictly increase. -/
theorem bureaucracyStateSemilattice_nat_lt_succ (n : Nat) :
    (BureaucracyState.nat n) < (BureaucracyState.nat (n + 1)) := by
  constructor
  · exact (bureaucracyStateSemilattice_le_iff
      (BureaucracyState.nat n) (BureaucracyState.nat (n + 1))).mpr
        (Nat.le_succ n)
  · intro h
    injection h with hn
    exact Nat.succ_ne_self n hn.symm

/-- Example 2.3.6: every natural bureaucracy state is strictly below `top`. -/
theorem bureaucracyStateSemilattice_nat_lt_top (n : Nat) :
    (BureaucracyState.nat n) < BureaucracyState.top := by
  constructor
  · exact (bureaucracyStateSemilattice_le_iff
      (BureaucracyState.nat n) BureaucracyState.top).mpr True.intro
  · intro h
    cases h

/-- Example 2.3.6: the state semilattice `State` is sequential. -/
theorem bureaucracyState_sequential : bureaucracyStateSemilattice.Sequential := by
  intro x y
  cases x with
  | top =>
      exact Or.inl rfl
  | nat n =>
      cases y with
      | top =>
          exact Or.inr (Or.inl rfl)
      | nat m =>
          by_cases hnm : n <= m
          · exact Or.inr (Or.inl (congrArg BureaucracyState.nat (Nat.max_eq_right hnm)))
          · have hmn : m <= n := Nat.le_of_not_ge hnm
            exact Or.inl (congrArg BureaucracyState.nat (Nat.max_eq_left hmn))

/--
Example 2.3.6: bureaucracy states contradict exactly when one side is
the failure top state.
-/
theorem bureaucracyState_contradicts_iff_top (x y : BureaucracyState) :
    x 🗲 y ↔
      x = BureaucracyState.top ∨ y = BureaucracyState.top := by
  constructor
  · intro h
    cases x with
    | nat n =>
        cases y with
        | nat m =>
            change BureaucracyState.nat (Nat.max n m) = BureaucracyState.top at h
            cases h
        | top =>
            exact Or.inr rfl
    | top =>
        exact Or.inl rfl
  · intro h
    rcases h with hx | hy
    · rw [hx]
      exact bureaucracyStateSemilattice.contradicts_top_left y
    · rw [hy]
      exact bureaucracyStateSemilattice.contradicts_top_right x

/-- Example 2.3.6: the two controllers `Ctrl = {JosefK, Prozess}`. -/
inductive BureaucracyCtrl where
  | josefK
  | prozess
  deriving DecidableEq

/-- Example 2.3.6: the bureaucracy example has exactly the two listed controllers. -/
theorem bureaucracyCtrl_eq_josefK_or_prozess (p : BureaucracyCtrl) :
    p = BureaucracyCtrl.josefK ∨ p = BureaucracyCtrl.prozess := by
  cases p
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Example 2.3.6: the two listed bureaucracy controllers are distinct. -/
theorem bureaucracyCtrl_josefK_ne_prozess :
    BureaucracyCtrl.josefK ≠ BureaucracyCtrl.prozess := by
  intro h
  cases h

/-- Example 2.3.6: bureaucracy times are controller/state pairs, `Time = Ctrl × State`. -/
abbrev BureaucracyTime := BureaucracyCtrl × BureaucracyState

/-- Example 2.3.6: the cross-controller transition — advance to `n'` when `n' = n + 1`,
else `⊤`. -/
def bureaucracyCrossState (n n' : Nat) : BureaucracyState :=
  if n' = n + 1 then BureaucracyState.nat n' else BureaucracyState.top

/-- Example 2.3.6: the bureaucracy attestation `#`. -/
def bureaucracyAttest : BureaucracyTime → BureaucracyTime → BureaucracyTime
  | (p, BureaucracyState.top), (_p', _x) => (p, BureaucracyState.top)
  | (p, BureaucracyState.nat _n), (_p', BureaucracyState.top) => (p, BureaucracyState.top)
  | (BureaucracyCtrl.josefK, BureaucracyState.nat n),
      (BureaucracyCtrl.josefK, BureaucracyState.nat n') =>
      (BureaucracyCtrl.josefK, BureaucracyState.nat (Nat.max n n'))
  | (BureaucracyCtrl.prozess, BureaucracyState.nat n),
      (BureaucracyCtrl.prozess, BureaucracyState.nat n') =>
      (BureaucracyCtrl.prozess, BureaucracyState.nat (Nat.max n n'))
  | (BureaucracyCtrl.josefK, BureaucracyState.nat n),
      (BureaucracyCtrl.prozess, BureaucracyState.nat n') =>
      (BureaucracyCtrl.josefK, bureaucracyCrossState n n')
  | (BureaucracyCtrl.prozess, BureaucracyState.nat n),
      (BureaucracyCtrl.josefK, BureaucracyState.nat n') =>
      (BureaucracyCtrl.prozess, bureaucracyCrossState n n')

/-- Example 2.3.6: attesting from a `⊤` state stays at `⊤`. -/
theorem bureaucracyAttest_left_top
    (p p' : BureaucracyCtrl) (x : BureaucracyState) :
    bureaucracyAttest (p, BureaucracyState.top) (p', x) =
      (p, BureaucracyState.top) := by
  cases p <;> cases p' <;> cases x <;> rfl

/-- Example 2.3.6: attesting to a `⊤` state goes to `⊤`. -/
theorem bureaucracyAttest_right_top
    (p p' : BureaucracyCtrl) (n : Nat) :
    bureaucracyAttest (p, BureaucracyState.nat n) (p', BureaucracyState.top) =
      (p, BureaucracyState.top) := by
  cases p <;> cases p' <;> rfl

/-- Example 2.3.6: same-controller attestation is the `max` of the two states. -/
theorem bureaucracyAttest_same_controller
    (p : BureaucracyCtrl) (n n' : Nat) :
    bureaucracyAttest (p, BureaucracyState.nat n) (p, BureaucracyState.nat n') =
      (p, BureaucracyState.nat (Nat.max n n')) := by
  cases p <;> rfl

/-- Example 2.3.6: cross-controller attestation applies the successive-form rule. -/
theorem bureaucracyAttest_cross_controller_apply
    {p p' : BureaucracyCtrl} (h : p ≠ p') (n n' : Nat) :
    bureaucracyAttest (p, BureaucracyState.nat n) (p', BureaucracyState.nat n') =
      (p, if n' = n + 1 then BureaucracyState.nat n' else BureaucracyState.top) := by
  cases p <;> cases p'
  · contradiction
  · rfl
  · rfl
  · contradiction

/-- Example 2.3.6: providing the next form (`n + 1`) advances the state to `n + 1`. -/
theorem bureaucracyAttest_cross_success
    {p p' : BureaucracyCtrl} (h : p ≠ p') (n : Nat) :
    bureaucracyAttest (p, BureaucracyState.nat n) (p', BureaucracyState.nat (n + 1)) =
      (p, BureaucracyState.nat (n + 1)) := by
  cases p <;> cases p'
  · contradiction
  · simp [bureaucracyAttest, bureaucracyCrossState]
  · simp [bureaucracyAttest, bureaucracyCrossState]
  · contradiction

/-- Example 2.3.6: an out-of-order form (`n' ≠ n + 1`) sends the attestation to `⊤`. -/
theorem bureaucracyAttest_cross_failure
    {p p' : BureaucracyCtrl} (h : p ≠ p') {n n' : Nat} (hstep : n' ≠ n + 1) :
    bureaucracyAttest (p, BureaucracyState.nat n) (p', BureaucracyState.nat n') =
      (p, BureaucracyState.top) := by
  cases p <;> cases p'
  · contradiction
  · simp [bureaucracyAttest, bureaucracyCrossState, hstep]
  · simp [bureaucracyAttest, bureaucracyCrossState, hstep]
  · contradiction

/-- Example 2.3.6: offering form 2 while holding form 0 is out of order, so it fails to `⊤`. -/
theorem bureaucracyAttest_cross_failure_zero_two :
    bureaucracyAttest
      (BureaucracyCtrl.prozess, BureaucracyState.nat 0)
      (BureaucracyCtrl.josefK, BureaucracyState.nat 2) =
        (BureaucracyCtrl.prozess, BureaucracyState.top) := by
  simp [bureaucracyAttest, bureaucracyCrossState]

/-- Example 2.3.6: "form 1, then form 2" succeeds, reaching state 2. -/
theorem bureaucracyAttest_forms_in_order :
    bureaucracyAttest
      (bureaucracyAttest
        (BureaucracyCtrl.prozess, BureaucracyState.nat 0)
        (BureaucracyCtrl.josefK, BureaucracyState.nat 1))
      (BureaucracyCtrl.josefK, BureaucracyState.nat 2) =
        (BureaucracyCtrl.prozess, BureaucracyState.nat 2) := by
  simp [bureaucracyAttest, bureaucracyCrossState]

/-- Example 2.3.6: "form 2, then form 1" fails, reaching `⊤`. -/
theorem bureaucracyAttest_forms_out_of_order :
    bureaucracyAttest
      (bureaucracyAttest
        (BureaucracyCtrl.prozess, BureaucracyState.nat 0)
        (BureaucracyCtrl.josefK, BureaucracyState.nat 2))
      (BureaucracyCtrl.josefK, BureaucracyState.nat 1) =
        (BureaucracyCtrl.prozess, BureaucracyState.top) := by
  simp [bureaucracyAttest, bureaucracyCrossState]

/-- Example 2.3.6: re-attesting a cross-controller result to its own prior state is stable. -/
theorem bureaucracyAttest_crossState_self
    (p : BureaucracyCtrl) (n n' : Nat) :
    bureaucracyAttest (p, bureaucracyCrossState n n') (p, BureaucracyState.nat n) =
      (p, bureaucracyCrossState n n') := by
  cases p <;> by_cases hstep : n' = n + 1 <;>
    simp [bureaucracyCrossState, hstep, bureaucracyAttest]

/-- Example 2.3.6: attesting to any `⊤` state goes to `⊤`. -/
theorem bureaucracyAttest_any_right_top
    (p p' : BureaucracyCtrl) (x : BureaucracyState) :
    bureaucracyAttest (p, x) (p', BureaucracyState.top) = (p, BureaucracyState.top) := by
  cases p <;> cases p' <;> cases x <;> rfl

/-- Example 2.3.6: attestation is controller-preserving. -/
theorem bureaucracyAttest_controller (t s : BureaucracyTime) :
    (bureaucracyAttest t s).fst = t.fst := by
  cases t with
  | mk p x =>
      cases s with
      | mk p' x' =>
          cases p <;> cases p' <;> cases x <;> cases x' <;>
            simp [bureaucracyAttest, bureaucracyCrossState]

/-- Example 2.3.6: a same-controller attestation reaches `⊤` only if an input state is `⊤`. -/
theorem bureaucracyAttest_same_controller_top_cases
    {p : BureaucracyCtrl} {x y : BureaucracyState}
    (h : bureaucracyAttest (p, x) (p, y) = (p, BureaucracyState.top)) :
    x = BureaucracyState.top ∨ y = BureaucracyState.top := by
  cases p <;> cases x <;> cases y <;> simp [bureaucracyAttest] at h ⊢

/-- Example 2.3.6: attestation is expansive. -/
theorem bureaucracyAttest_expansive (t s : BureaucracyTime) :
    bureaucracyAttest (bureaucracyAttest t s) t = bureaucracyAttest t s := by
  match t, s with
  | (p, BureaucracyState.top), (p', x') =>
      cases p <;> cases p' <;> cases x' <;> rfl
  | (p, BureaucracyState.nat _n), (p', BureaucracyState.top) =>
      cases p <;> cases p' <;> rfl
  | (BureaucracyCtrl.josefK, BureaucracyState.nat n),
      (BureaucracyCtrl.josefK, BureaucracyState.nat m) =>
      have hn : n <= Nat.max n m := Nat.le_max_left n m
      simp [bureaucracyAttest, Nat.max_eq_left hn]
  | (BureaucracyCtrl.prozess, BureaucracyState.nat n),
      (BureaucracyCtrl.prozess, BureaucracyState.nat m) =>
      have hn : n <= Nat.max n m := Nat.le_max_left n m
      simp [bureaucracyAttest, Nat.max_eq_left hn]
  | (BureaucracyCtrl.josefK, BureaucracyState.nat n),
      (BureaucracyCtrl.prozess, BureaucracyState.nat m) =>
      exact bureaucracyAttest_crossState_self BureaucracyCtrl.josefK n m
  | (BureaucracyCtrl.prozess, BureaucracyState.nat n),
      (BureaucracyCtrl.josefK, BureaucracyState.nat m) =>
      exact bureaucracyAttest_crossState_self BureaucracyCtrl.prozess n m

/-- Example 2.3.6: the bureaucracy located semilattice `L = (Ctrl, Time, #, ctrl)`. -/
instance bureaucracyLocatedSemilattice : LocatedSemilattice BureaucracyTime BureaucracyCtrl where
  attest := bureaucracyAttest
  controller := Prod.fst
  bot p := (p, BureaucracyState.nat 0)
  top p := (p, BureaucracyState.top)
  bot_controller := by
    intro p
    rfl
  top_controller := by
    intro p
    rfl
  controller_preserving := by
    intro t s
    exact bureaucracyAttest_controller t s
  self_join_idem := by
    intro t
    cases t with
    | mk p x =>
        cases p <;> cases x <;> simp [bureaucracyAttest]
  self_join_comm := by
    intro t t' hctrl
    cases t with
    | mk p x =>
        cases t' with
        | mk p' x' =>
            cases hctrl
            cases p <;> cases x <;> cases x' <;>
              simp [bureaucracyAttest, Nat.max_comm]
  self_join_assoc := by
    intro t t' u hctrl hctrl'
    cases t with
    | mk p x =>
        cases t' with
        | mk p' x' =>
            cases u with
            | mk p'' x'' =>
                cases hctrl
                cases hctrl'
                cases p <;> cases x <;> cases x' <;> cases x'' <;>
                  simp [bureaucracyAttest, Nat.max_assoc]
  self_bot_le := by
    intro p t hctrl
    cases t with
    | mk p' x =>
        cases hctrl
        cases p' <;> cases x <;> simp [bureaucracyAttest]
  self_le_top := by
    intro p t hctrl
    cases t with
    | mk p' x =>
        cases hctrl
        cases p' <;> cases x <;> rfl
  expansive := by
    intro t s
    exact bureaucracyAttest_expansive t s
  contradiction_preserving := by
    intro t t' s s' hctrl hctrl' hcontr
    rcases t with ⟨p, x⟩
    rcases t' with ⟨p', x'⟩
    rcases s with ⟨q, y⟩
    rcases s' with ⟨q', y'⟩
    rcases hcontr with ⟨hsctrl, hsjoin⟩
    cases hctrl
    cases hctrl'
    cases hsctrl
    constructor
    · rw [bureaucracyAttest_controller (p, x) (q, y),
        bureaucracyAttest_controller (p, x') (q, y')]
    · change
        bureaucracyAttest (bureaucracyAttest (p, x) (q, y))
            (bureaucracyAttest (p, x') (q, y')) =
          ((bureaucracyAttest (p, x) (q, y)).fst, BureaucracyState.top)
      rw [bureaucracyAttest_controller (p, x) (q, y)]
      rcases bureaucracyAttest_same_controller_top_cases hsjoin with hy | hy'
      · subst y
        have hleft :
            bureaucracyAttest (p, x) (q, BureaucracyState.top) =
              (p, BureaucracyState.top) :=
          bureaucracyAttest_any_right_top p q x
        rw [hleft]
        cases hres : bureaucracyAttest (p, x') (q, y') with
        | mk r z =>
            exact bureaucracyAttest_left_top p r z
      · subst y'
        have hright :
            bureaucracyAttest (p, x') (q, BureaucracyState.top) =
              (p, BureaucracyState.top) :=
          bureaucracyAttest_any_right_top p q x'
        rw [hright]
        have hfirstCtrl : (bureaucracyAttest (p, x) (q, y)).fst = p :=
          bureaucracyAttest_controller (p, x) (q, y)
        cases hres : bureaucracyAttest (p, x) (q, y) with
        | mk r z =>
            have hr : r = p := by
              simpa [hres] using hfirstCtrl
            subst r
            exact bureaucracyAttest_any_right_top p p z

/-- Example 2.3.6: bureaucracy attestation is strongly contradiction-preserving. -/
theorem bureaucracyLocatedSemilattice_strongly_contradiction_preserving
    {t t' s s' : BureaucracyTime} (htt' : t.fst = t'.fst) (hss' : s.fst = s'.fst)
    (hcontr : s 🗲 s') :
    (bureaucracyAttest t s) 🗲 (bureaucracyAttest t' s') :=
  bureaucracyLocatedSemilattice.contradicts_attest htt' hss' hcontr

/-- Example 2.3.6: on the natural states, the fiber order is the usual `≤` on `ℕ`. -/
theorem bureaucracyLocatedSemilattice_nat_le_nat
    (p : BureaucracyCtrl) (n m : Nat) :
    (p, BureaucracyState.nat n) ≼ (p, BureaucracyState.nat m) ↔ n <= m := by
  constructor
  · intro hle
    cases p <;> simp [LocatedSemilattice.le, bureaucracyLocatedSemilattice,
      bureaucracyAttest] at hle
    · exact nat_le_of_max_eq_right hle
    · exact nat_le_of_max_eq_right hle
  · intro hnm
    cases p <;> simp [LocatedSemilattice.le, bureaucracyLocatedSemilattice,
      bureaucracyAttest, Nat.max_eq_right hnm]

/--
Example 2.3.6: each bureaucracy controller fiber has exactly the state
order.
-/
theorem bureaucracyLocatedSemilattice_same_controller_le_iff_state_le
    (p : BureaucracyCtrl) (x y : BureaucracyState) :
    (p, x) ≼ (p, y) ↔
      x ≤ y := by
  cases p <;> cases x <;> cases y <;>
    simp [LocatedSemilattice.le, BoundedSemilattice.le, LE.le, -Nat.le_eq, bureaucracyLocatedSemilattice,
      bureaucracyStateSemilattice, bureaucracyAttest, BureaucracyState.join]

/-- Example 2.3.6: every natural state is below the controller's `⊤` state. -/
theorem bureaucracyLocatedSemilattice_nat_le_top
    (p : BureaucracyCtrl) (n : Nat) :
    (p, BureaucracyState.nat n) ≼ (p, BureaucracyState.top) := by
  cases p <;> simp [LocatedSemilattice.le, bureaucracyLocatedSemilattice,
    bureaucracyAttest]

/-- Example 2.3.6: the `⊤` state is not below any natural state. -/
theorem bureaucracyLocatedSemilattice_top_not_le_nat
    (p : BureaucracyCtrl) (n : Nat) :
    ¬ (p, BureaucracyState.top) ≼ (p, BureaucracyState.nat n) := by
  intro hle
  cases p <;> simp [LocatedSemilattice.le, bureaucracyLocatedSemilattice,
    bureaucracyAttest] at hle

/--
Example 2.3.6: successive natural bureaucracy times strictly increase
inside each controller fiber.
-/
theorem bureaucracyLocatedSemilattice_nat_lt_succ
    (p : BureaucracyCtrl) (n : Nat) :
    (p, BureaucracyState.nat n) ≺ (p, BureaucracyState.nat (n + 1)) := by
  constructor
  · exact (bureaucracyLocatedSemilattice_nat_le_nat p n (n + 1)).mpr (Nat.le_succ n)
  · intro h
    injection h with _ hstate
    injection hstate with hn
    exact Nat.succ_ne_self n hn.symm

/--
Example 2.3.6: every natural bureaucracy time is strictly below the
controller top time.
-/
theorem bureaucracyLocatedSemilattice_nat_lt_top
    (p : BureaucracyCtrl) (n : Nat) :
    (p, BureaucracyState.nat n) ≺ (p, BureaucracyState.top) := by
  constructor
  · exact bureaucracyLocatedSemilattice_nat_le_top p n
  · intro h
    injection h with _ hstate
    cases hstate

/--
Example 2.3.6: same-controller bureaucracy times contradict exactly
when one underlying state is the failure top state.
-/
theorem bureaucracyLocatedSemilattice_same_controller_contradicts_iff_top
    (p : BureaucracyCtrl) (x y : BureaucracyState) :
    (p, x) 🗲 (p, y) ↔
      x = BureaucracyState.top ∨ y = BureaucracyState.top := by
  constructor
  · intro h
    exact bureaucracyAttest_same_controller_top_cases h.2
  · intro h
    constructor
    · rfl
    · rcases h with hx | hy
      · rw [hx]
        exact bureaucracyAttest_left_top p p y
      · rw [hy]
        exact bureaucracyAttest_any_right_top p p x

/-- Example 2.3.6: the bureaucracy located semilattice is sequential. -/
theorem bureaucracyLocatedSemilattice_sequential :
    bureaucracyLocatedSemilattice.Sequential := by
  intro p t t'
  rcases t with ⟨⟨pt, x⟩, ht⟩
  rcases t' with ⟨⟨pt', x'⟩, ht'⟩
  cases ht
  cases ht'
  cases x with
  | top =>
      exact Or.inl rfl
  | nat n =>
      cases x' with
      | top =>
          exact Or.inr (Or.inl rfl)
      | nat m =>
          by_cases hnm : n <= m
          · exact Or.inr (Or.inl (by
              apply Subtype.ext
              cases pt <;> simp [LocatedSemilattice.fiber, bureaucracyLocatedSemilattice,
                bureaucracyAttest, Nat.max_eq_right hnm]))
          · have hmn : m <= n := Nat.le_of_not_ge hnm
            exact Or.inl (by
              apply Subtype.ext
              cases pt <;> simp [LocatedSemilattice.fiber, bureaucracyLocatedSemilattice,
                bureaucracyAttest, Nat.max_eq_left hmn])

/-- Example 2.3.6: the bureaucracy construction is a sequential located semilattice. -/
theorem bureaucracy_sequential :
    bureaucracyLocatedSemilattice.Sequential := by
  exact bureaucracyLocatedSemilattice_sequential

/-- Example 2.3.6: attestation is not monotone in its first argument — `(p, 0) ≼ (p, 1)`,
yet `(p, 0) # (p', 2) = (p, ⊤)` is not `≼ (p, 2) = (p, 1) # (p', 2)`. -/
theorem bureaucracyLocatedSemilattice_not_monotone_first_component
    {p p' : BureaucracyCtrl} (h : p ≠ p') :
    (p, BureaucracyState.nat 0) ≼ (p, BureaucracyState.nat 1) ∧
      (p, BureaucracyState.nat 0) # (p', BureaucracyState.nat 1) =
          (p, BureaucracyState.nat 1) ∧
      (p, BureaucracyState.nat 0) # (p', BureaucracyState.nat 2) =
          (p, BureaucracyState.top) ∧
      (p, BureaucracyState.nat 1) # (p', BureaucracyState.nat 2) =
          (p, BureaucracyState.nat 2) ∧
      ¬ ((p, BureaucracyState.nat 0) # (p', BureaucracyState.nat 2)) ≼ ((p, BureaucracyState.nat 1) # (p', BureaucracyState.nat 2)) := by
  constructor
  · exact (bureaucracyLocatedSemilattice_nat_le_nat p 0 1).mpr (Nat.zero_le 1)
  constructor
  · cases p <;> cases p'
    · contradiction
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · contradiction
  constructor
  · cases p <;> cases p'
    · contradiction
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · contradiction
  constructor
  · cases p <;> cases p'
    · contradiction
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · contradiction
  · cases p <;> cases p'
    · contradiction
    · simp [LocatedSemilattice.le, bureaucracyLocatedSemilattice, bureaucracyAttest,
        bureaucracyCrossState]
    · simp [LocatedSemilattice.le, bureaucracyLocatedSemilattice, bureaucracyAttest,
        bureaucracyCrossState]
    · contradiction

/--
Example 2.3.6: in the bureaucracy example, attestation is not monotone
in the first component.
-/
theorem bureaucracyLocatedSemilattice_exists_not_monotone_first_component :
    ∃ t t' s : BureaucracyTime,
      t ≼ t' ∧
        ¬ (t # s) ≼ (t' # s) := by
  refine
    ⟨(BureaucracyCtrl.prozess, BureaucracyState.nat 0),
      (BureaucracyCtrl.prozess, BureaucracyState.nat 1),
      (BureaucracyCtrl.josefK, BureaucracyState.nat 2), ?_⟩
  have hnonmono :=
    bureaucracyLocatedSemilattice_not_monotone_first_component
      (p := BureaucracyCtrl.prozess) (p' := BureaucracyCtrl.josefK) (by decide)
  exact ⟨hnonmono.1, hnonmono.2.2.2.2⟩

/-- Example 2.3.6: form order matters — "form 1 then 2" reaches state 2, "form 2 then 1"
reaches `⊤`. -/
theorem bureaucracyLocatedSemilattice_form_ordering
    {p p' : BureaucracyCtrl} (h : p ≠ p') :
    ((p, BureaucracyState.nat 0) # (p', BureaucracyState.nat 1)) # (p', BureaucracyState.nat 2) =
          (p, BureaucracyState.nat 2) ∧
      ((p, BureaucracyState.nat 0) # (p', BureaucracyState.nat 2)) # (p', BureaucracyState.nat 1) =
          (p, BureaucracyState.top) := by
  constructor
  · cases p <;> cases p'
    · contradiction
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · contradiction
  · cases p <;> cases p'
    · contradiction
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · simp [bureaucracyLocatedSemilattice, bureaucracyAttest, bureaucracyCrossState]
    · contradiction

/--
Example 2.3.6: the two bureaucracy form orders differ; the sequential
order stays consistent, while the swapped order reaches top.
-/
theorem bureaucracyLocatedSemilattice_form_ordering_outputs_differ
    {p p' : BureaucracyCtrl} (h : p ≠ p') :
    let ordered :=
      ((p, BureaucracyState.nat 0) # (p', BureaucracyState.nat 1)) # (p', BureaucracyState.nat 2)
    let swapped :=
      ((p, BureaucracyState.nat 0) # (p', BureaucracyState.nat 2)) # (p', BureaucracyState.nat 1)
    bureaucracyLocatedSemilattice.ConsistentTime ordered ∧
      ¬ bureaucracyLocatedSemilattice.ConsistentTime swapped ∧
        ordered ≠ swapped := by
  dsimp only
  rcases bureaucracyLocatedSemilattice_form_ordering h with ⟨hordered, hswapped⟩
  constructor
  · rw [hordered]
    intro htop
    cases p <;> cases htop
  constructor
  · rw [hswapped]
    intro hconsistent
    exact hconsistent rfl
  · intro heq
    rw [hordered, hswapped] at heq
    cases heq

end ConsistentHistories.Models.LocatedSemilattices.Examples
