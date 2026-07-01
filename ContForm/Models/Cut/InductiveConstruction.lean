import ContForm.Models.Cut.Consistency

/-!
Paper section 3.4: Consistency, inductive construction.

-/

namespace ContForm.Models.Cut.InductiveConstruction

open ContForm.Foundation.LocatedSemilattices.TopTrees

universe u

/-- Notation 3.4.1: Lean uses `Fin n` for `1..n`. -/
abbrev Upto (n : Nat) : Type :=
  Fin n

/-- Notation 3.4.1: list update `l[i := x]`, updating the `i`th entry of `l` to `x`. -/
def listUpdate {n : Nat} {X : Type u} (l : Upto n → X) (i : Upto n) (x : X) :
    Upto n → X :=
  fun j => if j = i then x else l j

@[simp] theorem listUpdate_same
    {n : Nat} {X : Type u} (l : Upto n → X) (i : Upto n) (x : X) :
    listUpdate l i x i = x := by
  simp [listUpdate]

theorem listUpdate_ne
    {n : Nat} {X : Type u} (l : Upto n → X) {i j : Upto n} (x : X)
    (hij : j ≠ i) : listUpdate l i x j = l j := by
  simp [listUpdate, hij]

/-- Notation 3.4.1: `(1,2,3)[2:= 0] = (1,0,3)`, using zero-based `Fin`. -/
theorem listUpdate_example_123 :
    listUpdate
        (fun i : Upto 3 => match i.val with | 0 => 1 | 1 => 2 | _ => 3)
        ⟨1, by decide⟩ 0 =
      (fun i : Upto 3 => match i.val with | 0 => 1 | 1 => 0 | _ => 3) := by
  funext i
  rcases i with ⟨n, hn⟩
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn_cases with rfl | rfl | rfl <;> simp [listUpdate]

/--
The data over which Section 3.4's inductive construction is parameterised: a
controller count `n` and a bounded semilattice `X` of local states that is
nondegenerate (`⊥_X ≠ ⊤_X`). Definition 3.4.2 additionally fixes `n ≥ 1`; see
`NonemptyLocalStateData`.
-/
structure LocalStateData where
  n : Nat
  X : Type u
  semilattice : BoundedSemilattice X
  bot_ne_top : semilattice.bot ≠ semilattice.top

/--
Definition 3.4.2: the fixed data of Section 3.4's construction — `n ≥ 1`
controllers `[1..n]` and a nondegenerate bounded semilattice `X` of local
states (`⊥_X ≠ ⊤_X`).
-/
structure NonemptyLocalStateData where
  n : Nat
  n_pos : 1 ≤ n
  X : Type u
  semilattice : BoundedSemilattice X
  bot_ne_top : semilattice.bot ≠ semilattice.top

namespace NonemptyLocalStateData

/-- Forget the `n ≥ 1` premise, viewing Definition 3.4.2's data as bare local-state data. -/
def toLocalStateData (D : NonemptyLocalStateData.{u}) : LocalStateData.{u} where
  n := D.n
  X := D.X
  semilattice := D.semilattice
  bot_ne_top := D.bot_ne_top

/-- Definition 3.4.2: `upto n` is inhabited under the paper premise `n >= 1`. -/
theorem ctrl_nonempty (D : NonemptyLocalStateData.{u}) :
    Nonempty (Upto D.n) :=
  ⟨⟨0, D.n_pos⟩⟩

end NonemptyLocalStateData

namespace LocalStateData

/-- Controllers for Definition 3.4.3, represented as `Fin n`. -/
abbrev Ctrl (D : LocalStateData.{u}) : Type :=
  Upto D.n

mutual
  /-- Definition 3.4.3: time formation, following Figure 7. -/
  inductive Time (D : LocalStateData.{u}) : Type u where
    | top (j : D.Ctrl) : Time D
    | consistent {j : D.Ctrl} (t : CTime D j) : Time D

  /--
 Definition 3.4.3, non-top time formation: each node stores a local state that
 is not `X.top`.
 -/
  inductive CTime (D : LocalStateData.{u}) : D.Ctrl → Type u where
    | bot (j : D.Ctrl) : CTime D j
    | node (j : D.Ctrl) (x : D.X) (hx : D.semilattice.Consistent x)
        (views : (i : D.Ctrl) → i ≠ j → CTime D i) : CTime D j
end

namespace CTime

/-- The explicit nontriviality proof needed by the cross-controller bot rule. -/
theorem botX_consistent (D : LocalStateData.{u}) : D.semilattice.Consistent D.semilattice.bot :=
  D.bot_ne_top

/-- Include a consistent time among all times. -/
def toTime {D : LocalStateData.{u}} {j : D.Ctrl} (t : CTime D j) : Time D :=
  Time.consistent t

/-- Controller of a consistent time. -/
def controller {D : LocalStateData.{u}} {j : D.Ctrl} (_t : CTime D j) : D.Ctrl :=
  j

@[simp] theorem controller_eq {D : LocalStateData.{u}} {j : D.Ctrl} (t : CTime D j) :
    CTime.controller t = j :=
  rfl

/-- The all-bottom view tuple for every controller except `j`. -/
def botViews (D : LocalStateData.{u}) (j : D.Ctrl) :
    (i : D.Ctrl) → i ≠ j → CTime D i :=
  fun i _hi => CTime.bot i

/--
The view tuple used by the cross-controller `bot_j # s` rule: every view is
bottom except the attested controller's view, which is set to `s`.
-/
def botViewsWith {D : LocalStateData.{u}} {j i : D.Ctrl} (_hij : i ≠ j)
    (s : CTime D i) : (k : D.Ctrl) → k ≠ j → CTime D k :=
  fun k _hk => if hki : k = i then hki ▸ s else CTime.bot k

@[simp] theorem botViewsWith_same {D : LocalStateData.{u}} {j i : D.Ctrl}
    (hij : i ≠ j) (s : CTime D i) : botViewsWith hij s i hij = s := by
  simp [botViewsWith]

theorem botViewsWith_ne {D : LocalStateData.{u}} {j i k : D.Ctrl}
    (hij : i ≠ j) (hk : k ≠ j) (s : CTime D i) (hki : k ≠ i) :
    botViewsWith hij s k hk = CTime.bot k := by
  simp [botViewsWith, hki]

/-- Definition 3.4.3: tuple for the cross-controller `bot_j # s` rule. -/
def crossBotNode {D : LocalStateData.{u}} (j i : D.Ctrl) (hij : i ≠ j) (s : CTime D i) :
    CTime D j :=
  CTime.node j D.semilattice.bot (botX_consistent D) (botViewsWith hij s)

/-- Replace the view at controller `i`, preserving every indexed controller type. -/
def viewsUpdate {D : LocalStateData.{u}} {j i : D.Ctrl}
    (views : (k : D.Ctrl) → k ≠ j → CTime D k) (_hij : i ≠ j) (s : CTime D i) :
    (k : D.Ctrl) → k ≠ j → CTime D k :=
  fun k hk => if hki : k = i then hki ▸ s else views k hk

@[simp] theorem viewsUpdate_same {D : LocalStateData.{u}} {j i : D.Ctrl}
    (views : (k : D.Ctrl) → k ≠ j → CTime D k) (hij : i ≠ j) (s : CTime D i) :
    viewsUpdate views hij s i hij = s := by
  simp [viewsUpdate]

theorem viewsUpdate_ne {D : LocalStateData.{u}} {j i k : D.Ctrl}
    (views : (k : D.Ctrl) → k ≠ j → CTime D k)
    (hij : i ≠ j) (hk : k ≠ j) (s : CTime D i) (hki : k ≠ i) :
    viewsUpdate views hij s k hk = views k hk := by
  simp [viewsUpdate, hki]

theorem node_views_eq_of_toTime_eq {D : LocalStateData.{u}} {j : D.Ctrl}
    {x : D.X} {hx hx' : D.semilattice.Consistent x}
    {views views' : (i : D.Ctrl) → i ≠ j → CTime D i}
    (h :
      CTime.toTime (CTime.node j x hx views) =
        CTime.toTime (CTime.node j x hx' views')) :
    ∀ i hij, views i hij = views' i hij := by
  cases h
  intro i hij
  rfl

theorem node_views_eq_of_toTime_eq_any {D : LocalStateData.{u}} {j : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {views views' : (i : D.Ctrl) → i ≠ j → CTime D i}
    (h :
      CTime.toTime (CTime.node j y hy views') =
        CTime.toTime (CTime.node j x hx views)) :
    ∀ i hij, views' i hij = views i hij := by
  cases h
  intro i hij
  rfl

end CTime

namespace Time

/-- Controller of a time. -/
def controller {D : LocalStateData.{u}} : Time D → D.Ctrl
  | top j => j
  | @consistent _ j _t => j

/-- Definition 2.2.2(6d): a time is consistent when it is not its controller's top time. -/
def Consistent {D : LocalStateData.{u}} (t : Time D) : Prop :=
  t ≠ Time.top (Time.controller t)

@[simp] theorem controller_top {D : LocalStateData.{u}} (j : D.Ctrl) :
    Time.controller (Time.top j) = j :=
  rfl

@[simp] theorem controller_consistent {D : LocalStateData.{u}} {j : D.Ctrl} (t : CTime D j) :
    Time.controller (CTime.toTime t) = j :=
  rfl

/-- Definition 3.4.3: `ctimeat j` embeds into non-top `timeat j`. -/
theorem consistent_toTime {D : LocalStateData.{u}} {j : D.Ctrl} (t : CTime D j) :
    Time.Consistent (CTime.toTime t) := by
  intro h
  cases h

/-- Top times are not consistent. -/
theorem not_consistent_top {D : LocalStateData.{u}} (j : D.Ctrl) :
    ¬ Time.Consistent (Time.top j) := by
  intro h
  exact h rfl

theorem toTime_ne_top {D : LocalStateData.{u}} {j k : D.Ctrl} (t : CTime D j) :
    CTime.toTime t ≠ Time.top k := by
  intro h
  cases h

end Time

/-- Definition 3.4.3: every non-top time is either `bot_j` or a tuple node. -/
theorem ctime_form_cases {D : LocalStateData.{u}} {j : D.Ctrl} (t : CTime D j) :
    t = CTime.bot j ∨
      ∃ (x : D.X) (hx : D.semilattice.Consistent x)
        (views : (i : D.Ctrl) → i ≠ j → CTime D i),
        t = CTime.node j x hx views := by
  cases t with
  | bot j =>
      exact Or.inl rfl
  | node j x hx views =>
      exact Or.inr ⟨x, hx, views, rfl⟩

/-- Bottom time at a controller. -/
def bot (D : LocalStateData.{u}) (j : D.Ctrl) : Time D :=
  Time.consistent (CTime.bot j)

/-- Top time at a controller. -/
def top (D : LocalStateData.{u}) (j : D.Ctrl) : Time D :=
  Time.top j

/-- Definition 3.4.3: the times controlled by `j` (`Time@j`). -/
def timeAt (D : LocalStateData.{u}) (j : D.Ctrl) : Type u :=
  {t : Time D // Time.controller t = j}

/-- Definition 3.4.3: the non-top (consistent) times controlled by `j` (`CTime@j`). -/
def ctimeAt (D : LocalStateData.{u}) (j : D.Ctrl) : Type u :=
  CTime D j

/-- Definition 3.4.3: `bot_j` is controlled by `j`. -/
theorem bot_controller (D : LocalStateData.{u}) (j : D.Ctrl) :
    Time.controller (bot D j) = j :=
  rfl

/-- Definition 3.4.3: `top_j` is controlled by `j`. -/
theorem top_controller (D : LocalStateData.{u}) (j : D.Ctrl) :
    Time.controller (top D j) = j :=
  rfl

/-- Definition 3.4.3: `bot_j` is non-top. -/
theorem bot_consistent (D : LocalStateData.{u}) (j : D.Ctrl) :
    Time.Consistent (bot D j) :=
  Time.consistent_toTime (CTime.bot j)

/-- Definition 3.4.3: `top_j` is top. -/
theorem top_not_consistent (D : LocalStateData.{u}) (j : D.Ctrl) :
    ¬ Time.Consistent (top D j) :=
  Time.not_consistent_top j

/-- Definition 3.4.3: every time is `bot_j`, `top_j`, or a non-top tuple node. -/
theorem time_form_cases (D : LocalStateData.{u}) (t : Time D) :
    (∃ j : D.Ctrl, t = bot D j) ∨
      (∃ j : D.Ctrl, t = top D j) ∨
        ∃ (j : D.Ctrl) (x : D.X) (hx : D.semilattice.Consistent x)
          (views : (i : D.Ctrl) → i ≠ j → CTime D i),
          t = CTime.toTime (CTime.node j x hx views) := by
  cases t with
  | top j =>
      exact Or.inr (Or.inl ⟨j, rfl⟩)
  | consistent t =>
      rcases ctime_form_cases t with hbot | hnode
      · cases hbot
        exact Or.inl ⟨_, rfl⟩
      · rcases hnode with ⟨x, hx, views, hnode⟩
        cases hnode
        exact Or.inr (Or.inr ⟨_, x, hx, views, rfl⟩)

/-- Definition 3.4.3: `bot_j` lies in `timeat j`. -/
theorem bot_mem_timeAt (D : LocalStateData.{u}) (j : D.Ctrl) :
    ∃ t : timeAt D j, t.1 = bot D j :=
  ⟨⟨bot D j, bot_controller D j⟩, rfl⟩

/-- Definition 3.4.3: `top_j` lies in `timeat j`. -/
theorem top_mem_timeAt (D : LocalStateData.{u}) (j : D.Ctrl) :
    ∃ t : timeAt D j, t.1 = top D j :=
  ⟨⟨top D j, top_controller D j⟩, rfl⟩

/-- Definition 3.4.3: every non-top time at `j` embeds into `timeAt j`. -/
theorem ctime_mem_timeAt (D : LocalStateData.{u}) {j : D.Ctrl} (t : CTime D j) :
    ∃ s : timeAt D j, s.1 = CTime.toTime t :=
  ⟨⟨CTime.toTime t, Time.controller_consistent t⟩, rfl⟩

/--
Definition 3.4.3: the cross-controller `bot_j # s` tuple embeds as a
consistent non-top time.
-/
theorem crossBotNode_consistent {D : LocalStateData.{u}} (j i : D.Ctrl)
    (hij : i ≠ j) (s : CTime D i) :
    Time.Consistent (CTime.toTime (CTime.crossBotNode j i hij s)) := by
  exact Time.consistent_toTime (CTime.crossBotNode j i hij s)

/-- Extract the indexed non-top time from a time-at-fiber proof and a non-top proof. -/
def Time.toCTimeOfNonTop {D : LocalStateData.{u}} {j : D.Ctrl}
    (t : timeAt D j) (htop : t.1 ≠ Time.top j) : CTime D j := by
  rcases t with ⟨t, hctrl⟩
  cases t with
  | top k =>
      simp [Time.controller] at hctrl
      cases hctrl
      exact False.elim (htop rfl)
  | consistent t =>
      simp [Time.controller] at hctrl
      cases hctrl
      exact t

/-- Re-embedding a non-top fiber extraction recovers the original time. -/
theorem Time.toCTimeOfNonTop_toTime {D : LocalStateData.{u}} {j : D.Ctrl}
    (t : timeAt D j) (htop : t.1 ≠ Time.top j) :
    CTime.toTime (Time.toCTimeOfNonTop t htop) = t.1 := by
  rcases t with ⟨t, hctrl⟩
  cases t with
  | top k =>
      simp [Time.controller] at hctrl
      cases hctrl
      exact False.elim (htop rfl)
  | consistent t =>
      simp [Time.controller] at hctrl
      cases hctrl
      rfl

/-- A non-top fiber extraction is unique when the fiber time is already embedded. -/
theorem Time.toCTimeOfNonTop_eq_of_toTime {D : LocalStateData.{u}} {j : D.Ctrl}
    (t : timeAt D j) (htop : t.1 ≠ Time.top j) (s : CTime D j)
    (hs : t.1 = CTime.toTime s) : Time.toCTimeOfNonTop t htop = s := by
  rcases t with ⟨t, hctrl⟩
  cases t with
  | top k =>
      cases hs
  | consistent t =>
      simp [Time.controller] at hctrl
      cases hctrl
      cases hs
      rfl

/-
Definition 3.4.3: the deterministic attestation function, read off Figure 8.

The value is returned with its controller-fiber proof, which makes the
controller-preserving clause definitional for downstream packaging.
-/
mutual
  /-- Definition 3.4.3: deterministic attestation result with its controller-fiber proof. -/
  noncomputable def attestAtTime {D : LocalStateData.{u}} (t s : Time D) :
      timeAt D (Time.controller t) := by
    classical
    exact
    match t with
    | Time.top j => ⟨Time.top j, rfl⟩
    | Time.consistent t => attestAtCTime t s

  /-- Definition 3.4.3: deterministic non-top first-argument attestation result. -/
  noncomputable def attestAtCTime {D : LocalStateData.{u}} {j : D.Ctrl}
      (t : CTime D j) (s : Time D) : timeAt D j := by
    classical
    exact
    match t with
    | CTime.bot j =>
        match s with
        | Time.top _i => ⟨Time.top j, rfl⟩
        | @Time.consistent _ i s =>
            if h : i = j then
              by
                subst i
                exact ⟨CTime.toTime s, rfl⟩
            else
              ⟨CTime.toTime (CTime.crossBotNode j i h s), rfl⟩
    | @CTime.node _ j x hx l =>
        match s with
        | Time.top _i => ⟨Time.top j, rfl⟩
        | @Time.consistent _ i s =>
            match s with
            | CTime.bot _i =>
                ⟨CTime.toTime (CTime.node j x hx l), rfl⟩
            | @CTime.node _ i y hy m =>
                if h : i = j then
                  by
                    subst i
                    if hxy : D.semilattice.join x y = D.semilattice.top then
                      exact ⟨Time.top j, rfl⟩
                    else
                      if hview :
                          ∃ (k : D.Ctrl) (hkj : k ≠ j),
                            (attestAtCTime (l k hkj) (CTime.toTime (m k hkj))).1 =
                              Time.top k then
                        exact ⟨Time.top j, rfl⟩
                      else
                        let r : (k : D.Ctrl) → k ≠ j → CTime D k :=
                          fun k hkj =>
                            Time.toCTimeOfNonTop
                              (attestAtCTime (l k hkj) (CTime.toTime (m k hkj)))
                              (by
                                intro htop
                                exact hview ⟨k, hkj, htop⟩)
                        exact ⟨CTime.toTime (CTime.node j (D.semilattice.join x y) hxy r), rfl⟩
                else
                  let out := attestAtCTime (l i h) (CTime.toTime s)
                  if htop : out.1 = Time.top i then
                    ⟨Time.top j, rfl⟩
                  else
                    let r := Time.toCTimeOfNonTop out htop
                    ⟨CTime.toTime (CTime.node j x hx (CTime.viewsUpdate l h r)), rfl⟩
end

/-- Definition 3.4.3: the attestation `#`, read off Figure 8. -/
noncomputable def attest {D : LocalStateData.{u}} (t s : Time D) : Time D :=
  (attestAtTime t s).1

theorem attest_controller {D : LocalStateData.{u}} (t s : Time D) :
    Time.controller (attest t s) = Time.controller t :=
  (attestAtTime t s).2

/--
Definition 3.4.3: the fiber-valued deterministic helper has the raw
deterministic attestation as its value.
-/
theorem attestAtTime_value {D : LocalStateData.{u}} (t s : Time D) :
    (attestAtTime t s).1 = attest t s := by
  rfl

/--
Definition 3.4.3: the fiber-valued deterministic helper is the raw deterministic
attestation with its controller proof.
-/
theorem attestAtTime_eq_mk {D : LocalStateData.{u}} (t s : Time D) :
    attestAtTime t s = ⟨attest t s, attest_controller t s⟩ := by
  apply Subtype.ext
  rfl

/-- Deterministic attestation with a non-top first argument unfolds to `attestAtCTime`. -/
theorem attest_ctime_eq {D : LocalStateData.{u}} {j : D.Ctrl}
    (t : CTime D j) (s : Time D) :
    attest (CTime.toTime t) s = (attestAtCTime t s).1 :=
  rfl

/-- Lemma 3.4.4: `t # t = t`. -/
theorem attest_self_time {D : LocalStateData.{u}} (t : Time D) : attest t t = t := by
  exact Time.rec (D := D)
    (motive_1 := fun t => attest t t = t)
    (motive_2 := fun _j t => attest (CTime.toTime t) (CTime.toTime t) = CTime.toTime t)
    (fun _j => rfl)
    (fun _t ht => ht)
    (fun j => by
      simp [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller])
    (fun j x hx views ih => by
      have hxy_not : ¬ D.semilattice.join x x = D.semilattice.top := by
        intro htop
        exact hx ((D.semilattice.join_idem x).symm.trans htop)
      have hview_eq :
          ∀ k hkj,
            (attestAtCTime (views k hkj) (Time.consistent (views k hkj))).1 =
              Time.consistent (views k hkj) := by
        intro k hkj
        have ihk := ih k hkj
        simpa [attest, attestAtTime, CTime.toTime] using ihk
      have hview_not :
          ¬ ∃ (k : D.Ctrl) (hkj : k ≠ j),
            (attestAtCTime (views k hkj) (Time.consistent (views k hkj))).1 = Time.top k := by
        rintro ⟨k, hkj, htop⟩
        rw [hview_eq k hkj] at htop
        cases htop
      by_cases hxy : D.semilattice.join x x = D.semilattice.top
      · exact False.elim (hxy_not hxy)
      · by_cases hview :
            ∃ (k : D.Ctrl) (hkj : k ≠ j),
              (attestAtCTime (views k hkj) (Time.consistent (views k hkj))).1 = Time.top k
        · exact False.elim (hview_not hview)
        · change
            attest (CTime.toTime (CTime.node j x hx views))
              (CTime.toTime (CTime.node j x hx views)) =
            CTime.toTime (CTime.node j x hx views)
          simp only [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller]
          rw [dif_neg hxy]
          rw [dif_pos trivial]
          rw [dif_neg hview]
          simp [D.semilattice.join_idem]
          funext k hkj
          exact Time.toCTimeOfNonTop_eq_of_toTime
            (attestAtCTime (views k hkj) (Time.consistent (views k hkj)))
            (by
              intro htop
              exact hview ⟨k, hkj, htop⟩)
            (views k hkj) (hview_eq k hkj))
    t

theorem attest_self_ctime {D : LocalStateData.{u}} {j : D.Ctrl} (t : CTime D j) :
    attest (CTime.toTime t) (CTime.toTime t) = CTime.toTime t :=
  attest_self_time (CTime.toTime t)

/-- Deterministic left-bottom fiber law for the attestation `#`. -/
theorem attest_bot_left_same_controller {D : LocalStateData.{u}} (j : D.Ctrl) (t : Time D)
    (hctrl : Time.controller t = j) : attest (bot D j) t = t := by
  cases t with
  | top k =>
      simp [Time.controller] at hctrl
      cases hctrl
      rfl
  | consistent t =>
      simp [Time.controller] at hctrl
      cases hctrl
      cases t with
      | bot =>
          simp [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, bot]
      | node j x hx views =>
          simp [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, bot]

/-- Deterministic right-bottom fiber law for the attestation `#`. -/
theorem attest_bot_right_same_controller {D : LocalStateData.{u}} (j : D.Ctrl) (t : Time D)
    (hctrl : Time.controller t = j) : attest t (bot D j) = t := by
  cases t with
  | top k =>
      simp [Time.controller] at hctrl
      cases hctrl
      rfl
  | consistent t =>
      simp [Time.controller] at hctrl
      cases hctrl
      cases t with
      | bot =>
          simp [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, bot]
      | node j x hx views =>
          simp [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, bot]

/-- Deterministic left-top fiber law for the attestation `#`. -/
theorem attest_top_left {D : LocalStateData.{u}} (j : D.Ctrl) (t : Time D) :
    attest (top D j) t = top D j :=
  rfl

/-- Deterministic right-top fiber law for the attestation `#`. -/
theorem attest_top_right_same_controller {D : LocalStateData.{u}} (j : D.Ctrl) (t : Time D)
    (hctrl : Time.controller t = j) : attest t (top D j) = top D j := by
  cases t with
  | top k =>
      simp [Time.controller] at hctrl
      cases hctrl
      rfl
  | consistent t =>
      simp [Time.controller] at hctrl
      cases hctrl
      cases t with
      | bot =>
          rfl
      | node j x hx views =>
          rfl

/--
Definition 3.4.3: the relational graph of the attestation clauses (Figure 8).

This graph follows the paper's disjoint right-bottom clause. The
deterministic function `LocalStateData.attest` is the primary formalization of
the paper definition. This relation is proof support for the recursive case
analysis, with `Attests.eq_attest` and `Attests.attest_graph` giving the exact
bridge to the deterministic function.
-/
inductive Attests (D : LocalStateData.{u}) : Time D → Time D → Time D → Prop where
  | right_top (t : Time D) (i : D.Ctrl) :
      Attests D t (Time.top i) (Time.top (Time.controller t))
  | right_bot (t : Time D) (i : D.Ctrl) (ht : t ≠ bot D (Time.controller t)) :
      Attests D t (CTime.toTime (CTime.bot i)) t
  | left_top (j : D.Ctrl) (s : Time D) :
      Attests D (Time.top j) s (Time.top j)
  | left_bot_same {j : D.Ctrl} (s : CTime D j) :
      Attests D (CTime.toTime (CTime.bot j)) (CTime.toTime s) (CTime.toTime s)
  | left_bot_ne {j i : D.Ctrl} (hij : i ≠ j) (s : CTime D i) :
      Attests D (CTime.toTime (CTime.bot j)) (CTime.toTime s)
        (CTime.toTime (CTime.crossBotNode j i hij s))
  | node_same_local_top {j : D.Ctrl} {x y : D.X}
      {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
      {l m : (i : D.Ctrl) → i ≠ j → CTime D i}
      (hxy : D.semilattice.join x y = D.semilattice.top) :
      Attests D (CTime.toTime (CTime.node j x hx l))
        (CTime.toTime (CTime.node j y hy m)) (Time.top j)
  | node_same_view_top {j k : D.Ctrl} {x y : D.X}
      {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
      {l m : (i : D.Ctrl) → i ≠ j → CTime D i}
      (hkj : k ≠ j)
      (hview : Attests D (CTime.toTime (l k hkj)) (CTime.toTime (m k hkj)) (Time.top k)) :
      Attests D (CTime.toTime (CTime.node j x hx l))
        (CTime.toTime (CTime.node j y hy m)) (Time.top j)
  | node_same_consistent {j : D.Ctrl} {x y : D.X}
      {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
      {l m r : (i : D.Ctrl) → i ≠ j → CTime D i}
      (hxy : D.semilattice.Consistent (D.semilattice.join x y))
      (hviews : ∀ i hij, Attests D (CTime.toTime (l i hij)) (CTime.toTime (m i hij))
        (CTime.toTime (r i hij))) :
      Attests D (CTime.toTime (CTime.node j x hx l))
        (CTime.toTime (CTime.node j y hy m))
        (CTime.toTime (CTime.node j (D.semilattice.join x y) hxy r))
  | node_cross_top {j i : D.Ctrl} {x y : D.X}
      {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
      {l : (k : D.Ctrl) → k ≠ j → CTime D k}
      {m : (k : D.Ctrl) → k ≠ i → CTime D k}
      (hij : i ≠ j)
      (hview : Attests D (CTime.toTime (l i hij))
        (CTime.toTime (CTime.node i y hy m)) (Time.top i)) :
      Attests D (CTime.toTime (CTime.node j x hx l))
        (CTime.toTime (CTime.node i y hy m)) (Time.top j)
  | node_cross_consistent {j i : D.Ctrl} {x y : D.X}
      {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
      {l : (k : D.Ctrl) → k ≠ j → CTime D k}
      {m : (k : D.Ctrl) → k ≠ i → CTime D k}
      (hij : i ≠ j) {r : CTime D i}
      (hview : Attests D (CTime.toTime (l i hij))
        (CTime.toTime (CTime.node i y hy m)) (CTime.toTime r)) :
      Attests D (CTime.toTime (CTime.node j x hx l))
        (CTime.toTime (CTime.node i y hy m))
        (CTime.toTime (CTime.node j x hx (CTime.viewsUpdate l hij r)))

namespace Attests

/-- Definition 3.4.3: `t # top_i = top_controller(t)`. -/
theorem right_top_clause {D : LocalStateData.{u}} (t : Time D) (i : D.Ctrl) :
    Attests D t (top D i) (top D (Time.controller t)) :=
  Attests.right_top t i

/-- Definition 3.4.3: `t # bot_i = t` when `t` is not its controller's bottom. -/
theorem right_bot_clause {D : LocalStateData.{u}} (t : Time D) (i : D.Ctrl)
    (ht : t ≠ bot D (Time.controller t)) :
    Attests D t (bot D i) t :=
  Attests.right_bot t i ht

/-- Definition 3.4.3: `top_j # s = top_j`. -/
theorem left_top_clause {D : LocalStateData.{u}} (j : D.Ctrl) (s : Time D) :
    Attests D (top D j) s (top D j) :=
  Attests.left_top j s

/-- Definition 3.4.3: `bot_j # s = s` for same-controller non-top `s`. -/
theorem left_bot_same_clause {D : LocalStateData.{u}} {j : D.Ctrl} (s : CTime D j) :
    Attests D (bot D j) (CTime.toTime s) (CTime.toTime s) :=
  Attests.left_bot_same s

/-- Definition 3.4.3: cross-controller `bot_j # s` produces the explicit non-top tuple. -/
theorem left_bot_cross_clause {D : LocalStateData.{u}} {j i : D.Ctrl}
    (hij : i ≠ j) (s : CTime D i) :
    Attests D (bot D j) (CTime.toTime s)
      (CTime.toTime (CTime.crossBotNode j i hij s)) :=
  Attests.left_bot_ne hij s

/-- Definition 3.4.3: same-controller node attestation goes top when local states join top. -/
theorem node_same_local_top_clause {D : LocalStateData.{u}} {j : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l m : (i : D.Ctrl) → i ≠ j → CTime D i}
    (hxy : D.semilattice.join x y = D.semilattice.top) :
    Attests D (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node j y hy m)) (top D j) :=
  Attests.node_same_local_top hxy

/-- Definition 3.4.3: same-controller node attestation goes top when one view joins top. -/
theorem node_same_view_top_clause {D : LocalStateData.{u}} {j k : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l m : (i : D.Ctrl) → i ≠ j → CTime D i}
    (hkj : k ≠ j)
    (hview : Attests D (CTime.toTime (l k hkj)) (CTime.toTime (m k hkj)) (top D k)) :
    Attests D (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node j y hy m)) (top D j) :=
  Attests.node_same_view_top hkj hview

/-- Definition 3.4.3: same-controller node attestation combines local state and views. -/
theorem node_same_consistent_clause {D : LocalStateData.{u}} {j : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l m r : (i : D.Ctrl) → i ≠ j → CTime D i}
    (hxy : D.semilattice.Consistent (D.semilattice.join x y))
    (hviews : ∀ i hij, Attests D (CTime.toTime (l i hij)) (CTime.toTime (m i hij))
      (CTime.toTime (r i hij))) :
    Attests D (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node j y hy m))
      (CTime.toTime (CTime.node j (D.semilattice.join x y) hxy r)) :=
  Attests.node_same_consistent hxy hviews

/-- Definition 3.4.3: cross-controller node attestation goes top when the stored view joins top. -/
theorem node_cross_top_clause {D : LocalStateData.{u}} {j i : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l : (k : D.Ctrl) → k ≠ j → CTime D k}
    {m : (k : D.Ctrl) → k ≠ i → CTime D k}
    (hij : i ≠ j)
    (hview : Attests D (CTime.toTime (l i hij))
      (CTime.toTime (CTime.node i y hy m)) (top D i)) :
    Attests D (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node i y hy m)) (top D j) :=
  Attests.node_cross_top hij hview

/-- Definition 3.4.3: cross-controller node attestation updates the stored view. -/
theorem node_cross_consistent_clause {D : LocalStateData.{u}} {j i : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l : (k : D.Ctrl) → k ≠ j → CTime D k}
    {m : (k : D.Ctrl) → k ≠ i → CTime D k}
    (hij : i ≠ j) {r : CTime D i}
    (hview : Attests D (CTime.toTime (l i hij))
      (CTime.toTime (CTime.node i y hy m)) (CTime.toTime r)) :
    Attests D (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node i y hy m))
      (CTime.toTime (CTime.node j x hx (CTime.viewsUpdate l hij r))) :=
  Attests.node_cross_consistent hij hview

/--
The relational graph is extensionally the deterministic attestation
function from Figure 3.4.
-/
theorem eq_attest {D : LocalStateData.{u}} {t s r : Time D}
    (h : Attests D t s r) : r = attest t s := by
  induction h with
  | right_top t i =>
      cases t with
      | top j => rfl
      | consistent t =>
          cases t <;> rfl
  | right_bot t i ht =>
      cases t with
      | top j => rfl
      | consistent t =>
          cases t with
          | bot j => exact False.elim (ht rfl)
          | node j x hx views => rfl
  | left_top j s =>
      rfl
  | left_bot_same s =>
      simp [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller]
  | left_bot_ne hij s =>
      simp [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, hij]
  | node_same_local_top hxy =>
      simp [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, hxy]
  | node_same_view_top hkj hview ih =>
      rename_i j k x y hx hy l m
      by_cases hxy : D.semilattice.join x y = D.semilattice.top
      · simp [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, hxy]
      · have hviewTop :
            ∃ (k' : D.Ctrl) (hk' : k' ≠ j),
              (attestAtCTime (l k' hk') (Time.consistent (m k' hk'))).1 = Time.top k' := by
          refine ⟨k, hkj, ?_⟩
          simpa [attest_ctime_eq] using ih.symm
        change
          Time.top j =
            attest (CTime.toTime (CTime.node j x hx l)) (CTime.toTime (CTime.node j y hy m))
        simp only [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller]
        rw [dif_neg hxy]
        rw [dif_pos trivial]
        rw [dif_pos hviewTop]
  | node_same_consistent hxy hviews ihviews =>
      rename_i j x y hx hy l m r
      have hxy_not : ¬ D.semilattice.join x y = D.semilattice.top := hxy
      have hview_not :
          ¬ ∃ (k' : D.Ctrl) (hk' : k' ≠ j),
            (attestAtCTime (l k' hk') (Time.consistent (m k' hk'))).1 = Time.top k' := by
        rintro ⟨k, hk, htop⟩
        have hkrel := ihviews k hk
        have hval :
            (attestAtCTime (l k hk) (Time.consistent (m k hk))).1 =
              CTime.toTime (r k hk) := by
          simpa [attest_ctime_eq] using hkrel.symm
        rw [hval] at htop
        cases htop
      change
        CTime.toTime (CTime.node j (D.semilattice.join x y) hxy r) =
          attest (CTime.toTime (CTime.node j x hx l)) (CTime.toTime (CTime.node j y hy m))
      simp only [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller]
      rw [dif_neg hxy_not]
      rw [dif_pos trivial]
      rw [dif_neg hview_not]
      simp
      funext k hkj
      have hkrel := ihviews k hkj
      have hval :
          (attestAtCTime (l k hkj) (Time.consistent (m k hkj))).1 =
            CTime.toTime (r k hkj) := by
        simpa [attest_ctime_eq] using hkrel.symm
      exact (Time.toCTimeOfNonTop_eq_of_toTime
        (attestAtCTime (l k hkj) (Time.consistent (m k hkj)))
        (by
          intro htop
          exact hview_not ⟨k, hkj, htop⟩)
        (r k hkj) hval).symm
  | node_cross_top hij hview ih =>
      rename_i j i x y hx hy l m
      have htop :
          (attestAtCTime (l i hij) (Time.consistent (CTime.node i y hy m))).1 =
            Time.top i := by
        simpa [attest_ctime_eq] using ih.symm
      change
        Time.top j =
          attest (CTime.toTime (CTime.node j x hx l)) (CTime.toTime (CTime.node i y hy m))
      simp only [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller]
      rw [dif_neg hij]
      rw [dif_pos htop]
  | node_cross_consistent hij hview ih =>
      rename_i j i x y hx hy l m r
      have hval :
          (attestAtCTime (l i hij) (Time.consistent (CTime.node i y hy m))).1 =
            CTime.toTime r := by
        simpa [attest_ctime_eq] using ih.symm
      have hnot :
          (attestAtCTime (l i hij) (Time.consistent (CTime.node i y hy m))).1 ≠ Time.top i := by
        intro htop
        rw [hval] at htop
        cases htop
      change
        CTime.toTime (CTime.node j x hx (CTime.viewsUpdate l hij r)) =
          attest (CTime.toTime (CTime.node j x hx l)) (CTime.toTime (CTime.node i y hy m))
      simp only [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller]
      rw [dif_neg hij]
      rw [dif_neg hnot]
      simp
      have hr : Time.toCTimeOfNonTop
          (attestAtCTime (l i hij) (Time.consistent (CTime.node i y hy m))) hnot = r :=
        Time.toCTimeOfNonTop_eq_of_toTime
          (attestAtCTime (l i hij) (Time.consistent (CTime.node i y hy m))) hnot r hval
      rw [hr]

/-- The deterministic attestation is generated by the graph. -/
theorem attest_graph {D : LocalStateData.{u}} (t s : Time D) :
    Attests D t s (attest t s) := by
  exact Time.rec (D := D)
    (motive_1 := fun t => ∀ s : Time D, Attests D t s (attest t s))
    (motive_2 := fun _j t => ∀ s : Time D,
      Attests D (CTime.toTime t) s (attest (CTime.toTime t) s))
    (fun j s => by
      simpa [attest] using Attests.left_top (D := D) j s)
    (fun _t ih s => ih s)
    (fun j s => by
      cases s with
      | top i =>
          simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller] using
            Attests.right_top (D := D) (bot D j) i
      | consistent s =>
          cases s with
          | bot =>
              rename_i i
              by_cases h : i = j
              · subst i
                simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, bot]
                  using Attests.left_bot_same (D := D) (CTime.bot j)
              · simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, h, bot]
                  using Attests.left_bot_ne (D := D) h (CTime.bot i)
          | node =>
              rename_i i y hy m
              by_cases h : i = j
              · subst i
                simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, bot]
                  using Attests.left_bot_same (D := D) (CTime.node j y hy m)
              · simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, h, bot]
                  using Attests.left_bot_ne (D := D) h (CTime.node i y hy m))
    (fun j x hx l ih s => by
      cases s with
      | top i =>
          simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller] using
            Attests.right_top (D := D) (CTime.toTime (CTime.node j x hx l)) i
      | consistent s =>
          cases s with
          | bot =>
              rename_i i
              simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller, bot] using
                Attests.right_bot (D := D) (CTime.toTime (CTime.node j x hx l)) i (by
                  intro h
                  cases h)
          | node =>
              rename_i i y hy m
              by_cases hij : i = j
              · subst i
                by_cases hxy : D.semilattice.join x y = D.semilattice.top
                · simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller,
                    hxy] using
                    Attests.node_same_local_top (D := D) (j := j) (x := x) (y := y)
                      (hx := hx) (hy := hy) (l := l) (m := m) hxy
                · by_cases hview :
                    ∃ (k : D.Ctrl) (hkj : k ≠ j),
                      (attestAtCTime (l k hkj) (Time.consistent (m k hkj))).1 =
                        Time.top k
                  · rcases hview with ⟨k, hkj, htop⟩
                    have hviewExists :
                        ∃ (k : D.Ctrl) (hkj : k ≠ j),
                          (attestAtCTime (l k hkj) (Time.consistent (m k hkj))).1 =
                            Time.top k :=
                      ⟨k, hkj, htop⟩
                    have hrel := ih k hkj (Time.consistent (m k hkj))
                    have hrelTop :
                        Attests D (CTime.toTime (l k hkj)) (CTime.toTime (m k hkj))
                          (Time.top k) := by
                      simpa [attest_ctime_eq, htop] using hrel
                    simpa [attest, attestAtTime, attestAtCTime, CTime.toTime,
                      Time.controller, hxy, hviewExists] using
                      Attests.node_same_view_top (D := D) (j := j) (k := k)
                        (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m)
                        hkj hrelTop
                  · let r : (k : D.Ctrl) → k ≠ j → CTime D k :=
                      fun k hkj =>
                        Time.toCTimeOfNonTop
                          (attestAtCTime (l k hkj) (Time.consistent (m k hkj)))
                          (by
                            intro htop
                            exact hview ⟨k, hkj, htop⟩)
                    have hviews :
                        ∀ k hkj, Attests D (CTime.toTime (l k hkj))
                          (CTime.toTime (m k hkj)) (CTime.toTime (r k hkj)) := by
                      intro k hkj
                      have hrel := ih k hkj (Time.consistent (m k hkj))
                      change Attests D (CTime.toTime (l k hkj)) (CTime.toTime (m k hkj))
                        (CTime.toTime
                          (Time.toCTimeOfNonTop
                            (attestAtCTime (l k hkj) (Time.consistent (m k hkj))) _))
                      rw [Time.toCTimeOfNonTop_toTime]
                      simpa [attest_ctime_eq] using hrel
                    simpa [attest, attestAtTime, attestAtCTime, CTime.toTime,
                      Time.controller, hxy, hview, r] using
                      Attests.node_same_consistent (D := D) (j := j)
                        (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m)
                        (r := r) hxy hviews
              · by_cases htop :
                    (attestAtCTime (l i hij) (Time.consistent (CTime.node i y hy m))).1 =
                      Time.top i
                · have hrel := ih i hij (Time.consistent (CTime.node i y hy m))
                  have hrelTop :
                      Attests D (CTime.toTime (l i hij))
                        (CTime.toTime (CTime.node i y hy m)) (Time.top i) := by
                    simpa [attest_ctime_eq, htop] using hrel
                  simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller,
                    hij, htop] using
                    Attests.node_cross_top (D := D) (j := j) (i := i)
                      (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m)
                      hij hrelTop
                · let r : CTime D i :=
                    Time.toCTimeOfNonTop
                      (attestAtCTime (l i hij) (Time.consistent (CTime.node i y hy m)))
                      htop
                  have hrel := ih i hij (Time.consistent (CTime.node i y hy m))
                  have hrelR :
                      Attests D (CTime.toTime (l i hij))
                        (CTime.toTime (CTime.node i y hy m)) (CTime.toTime r) := by
                    change Attests D (CTime.toTime (l i hij))
                      (CTime.toTime (CTime.node i y hy m))
                      (CTime.toTime
                        (Time.toCTimeOfNonTop
                          (attestAtCTime (l i hij) (Time.consistent (CTime.node i y hy m)))
                          htop))
                    rw [Time.toCTimeOfNonTop_toTime]
                    simpa [attest_ctime_eq] using hrel
                  simpa [attest, attestAtTime, attestAtCTime, CTime.toTime, Time.controller,
                    hij, htop, r] using
                    Attests.node_cross_consistent (D := D) (j := j) (i := i)
                      (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m)
                      hij hrelR)
    t s

/--
The relational graph is exactly the deterministic attestation
function from Figure 3.4.
-/
theorem iff_eq_attest {D : LocalStateData.{u}} {t s r : Time D} :
    Attests D t s r ↔ r = attest t s := by
  constructor
  · intro h
    exact eq_attest h
  · intro h
    rw [h]
    exact attest_graph t s

/--
The relational graph has a unique output, because it is exactly the
deterministic attestation function.
-/
theorem unique {D : LocalStateData.{u}} {t s r r' : Time D}
    (h : Attests D t s r) (h' : Attests D t s r') : r = r' := by
  exact (eq_attest h).trans (eq_attest h').symm

/--
Lemma 3.4.4, graph form: self-attestation follows from
the displayed clauses.
-/
theorem self_time {D : LocalStateData.{u}} (t : Time D) : Attests D t t t := by
  exact Time.rec (D := D)
    (motive_1 := fun t => Attests D t t t)
    (motive_2 := fun _j t => Attests D (CTime.toTime t) (CTime.toTime t) (CTime.toTime t))
    (fun j => Attests.left_top j (Time.top j))
    (fun t ht => ht)
    (fun j => Attests.left_bot_same (CTime.bot j))
    (fun j x hx views ih => by
      have hxy : D.semilattice.Consistent (D.semilattice.join x x) := by
        intro htop
        exact hx ((D.semilattice.join_idem x).symm.trans htop)
      have hnode : Attests D (CTime.toTime (CTime.node j x hx views))
          (CTime.toTime (CTime.node j x hx views))
          (CTime.toTime (CTime.node j (D.semilattice.join x x) hxy views)) := by
        apply Attests.node_same_consistent hxy
        intro i hij
        exact ih i hij
      simpa [CTime.toTime, D.semilattice.join_idem x] using hnode)
    t

theorem self_ctime {D : LocalStateData.{u}} {j : D.Ctrl} (t : CTime D j) :
    Attests D (CTime.toTime t) (CTime.toTime t) (CTime.toTime t) :=
  self_time (CTime.toTime t)

/-- Controller preservation clause for the relational attestation rules. -/
theorem controller_preserving {D : LocalStateData.{u}} {t s r : Time D}
    (h : Attests D t s r) : Time.controller r = Time.controller t := by
  cases h <;> simp [Time.controller, CTime.toTime, CTime.crossBotNode]

/-- Same-controller inputs produce an output in the shared controller fiber. -/
theorem controller_eq_right_of_same_controller {D : LocalStateData.{u}} {t s r : Time D}
    (hctrl : Time.controller t = Time.controller s)
    (h : Attests D t s r) : Time.controller r = Time.controller s :=
  (controller_preserving h).trans hctrl

/-- Left-bottom fiber law for the relational attestation rules. -/
theorem bot_left_same_controller {D : LocalStateData.{u}} (j : D.Ctrl) (t : Time D)
    (hctrl : Time.controller t = j) : Attests D (bot D j) t t := by
  cases t with
  | top k =>
      simp [Time.controller] at hctrl
      cases hctrl
      exact Attests.right_top (D := D) (bot D j) j
  | consistent t =>
      simp [Time.controller] at hctrl
      cases hctrl
      exact Attests.left_bot_same t

/-- Right-bottom fiber law for the relational attestation rules. -/
theorem bot_right_same_controller {D : LocalStateData.{u}} (j : D.Ctrl) (t : Time D)
    (hctrl : Time.controller t = j) : Attests D t (bot D j) t := by
  cases t with
  | top k =>
      simp [Time.controller] at hctrl
      cases hctrl
      exact Attests.left_top _ _
  | consistent t =>
      simp [Time.controller] at hctrl
      cases hctrl
      cases t with
      | bot =>
          exact Attests.left_bot_same _
      | node j x hx views =>
          apply Attests.right_bot
          intro h
          cases h

/-- Right-top fiber law for the relational attestation rules. -/
theorem top_right_same_controller {D : LocalStateData.{u}} (j : D.Ctrl) (t : Time D)
    (hctrl : Time.controller t = j) : Attests D t (top D j) (top D j) := by
  subst j
  exact Attests.right_top t (Time.controller t)

/-- Left-top fiber law for the relational attestation rules. -/
theorem top_left_same_controller {D : LocalStateData.{u}} (j : D.Ctrl) (t : Time D)
    (_hctrl : Time.controller t = j) : Attests D (top D j) t (top D j) :=
  Attests.left_top j t

/-- Same-controller commutativity clause for the relational attestation rules. -/
theorem comm_of_same_controller {D : LocalStateData.{u}} {t s r : Time D}
    (hctrl : Time.controller t = Time.controller s)
    (h : Attests D t s r) : Attests D s t r := by
  induction h with
  | right_top t i =>
      cases t with
      | top j =>
          simp [Time.controller] at hctrl
          cases hctrl
          exact Attests.left_top i (Time.top i)
      | consistent t =>
          simp [Time.controller] at hctrl
          cases hctrl
          exact Attests.left_top i (CTime.toTime t)
  | right_bot t i _ht =>
      cases t with
      | top j =>
          simp [Time.controller] at hctrl
          cases hctrl
          exact Attests.right_top (D := D) (CTime.toTime (CTime.bot i)) i
      | consistent t =>
          simp [Time.controller, CTime.toTime] at hctrl
          cases hctrl
          exact Attests.left_bot_same t
  | left_top j s =>
      cases s with
      | top i =>
          simp [Time.controller] at hctrl
          cases hctrl
          exact Attests.right_top (D := D) (Time.top j) j
      | consistent s =>
          simp [Time.controller] at hctrl
          cases hctrl
          exact Attests.right_top (D := D) (CTime.toTime s) j
  | left_bot_same s =>
      cases s with
      | bot => exact Attests.left_bot_same _
      | node j x hx views =>
          apply Attests.right_bot
          intro h
          cases h
  | left_bot_ne hij s =>
      simp [Time.controller, CTime.toTime] at hctrl
      exact False.elim (hij hctrl.symm)
  | node_same_local_top hxy =>
      rename_i _j x y _hx _hy _l _m
      have hyx : D.semilattice.join y x = D.semilattice.top := by
        calc
          D.semilattice.join y x = D.semilattice.join x y := D.semilattice.join_comm y x
          _ = D.semilattice.top := hxy
      exact Attests.node_same_local_top hyx
  | node_same_view_top hkj _hview ih =>
      apply Attests.node_same_view_top hkj
      exact ih rfl
  | node_same_consistent hxy _hviews ihviews =>
      rename_i j x y hx hy l m r
      have hyx : D.semilattice.Consistent (D.semilattice.join y x) := by
        intro htop
        exact hxy (by
          calc
            D.semilattice.join x y = D.semilattice.join y x := D.semilattice.join_comm x y
            _ = D.semilattice.top := htop)
      have hviews' :
          ∀ i hij, Attests D (CTime.toTime (m i hij)) (CTime.toTime (l i hij))
            (CTime.toTime (r i hij)) := by
        intro i hij
        exact ihviews i hij rfl
      have hnode := Attests.node_same_consistent (D := D) (j := j)
        (x := y) (y := x) (hx := hy) (hy := hx) (l := m) (m := l) (r := r)
        hyx hviews'
      simpa [CTime.toTime, D.semilattice.join_comm y x] using hnode
  | node_cross_top hij _hview _ih =>
      simp [Time.controller, CTime.toTime] at hctrl
      exact False.elim (hij hctrl.symm)
  | node_cross_consistent hij _hview _ih =>
      simp [Time.controller, CTime.toTime] at hctrl
      exact False.elim (hij hctrl.symm)

private theorem consistent_join_self {D : LocalStateData.{u}} {x : D.X} (hx : D.semilattice.Consistent x) :
    D.semilattice.Consistent (D.semilattice.join x x) := by
  intro htop
  exact hx ((D.semilattice.join_idem x).symm.trans htop)

private theorem join_join_left_eq {D : LocalStateData.{u}} (x y : D.X) :
    D.semilattice.join (D.semilattice.join x y) x = D.semilattice.join x y := by
  calc
    D.semilattice.join (D.semilattice.join x y) x = D.semilattice.join x (D.semilattice.join x y) :=
      D.semilattice.join_comm (D.semilattice.join x y) x
    _ = D.semilattice.join (D.semilattice.join x x) y := (D.semilattice.join_assoc x x y).symm
    _ = D.semilattice.join x y := by rw [D.semilattice.join_idem]

private theorem consistent_join_join_left {D : LocalStateData.{u}} {x y : D.X}
    (hxy : D.semilattice.Consistent (D.semilattice.join x y)) :
    D.semilattice.Consistent (D.semilattice.join (D.semilattice.join x y) x) := by
  intro htop
  exact hxy ((join_join_left_eq x y).symm.trans htop)

/-- Expansivity clause for the relational attestation rules. -/
theorem expansive {D : LocalStateData.{u}} {t s r : Time D} (h : Attests D t s r) :
    Attests D r t r := by
  induction h with
  | right_top t _i => exact Attests.left_top (Time.controller t) t
  | right_bot t _i _ht => exact self_time t
  | left_top j _s => exact Attests.left_top j (Time.top j)
  | left_bot_same s =>
      cases s with
      | bot => exact Attests.left_bot_same _
      | node j x hx views =>
          apply Attests.right_bot
          intro h
          cases h
  | left_bot_ne hij s =>
      apply Attests.right_bot
      intro h
      cases h
  | node_same_local_top _hxy => exact Attests.left_top _ _
  | node_same_view_top _hkj _hview _ih => exact Attests.left_top _ _
  | node_same_consistent hxy _hviews ihviews =>
    rename_i j x y hx _hy _l _m r
    have hxy' := consistent_join_join_left hxy
    have hnode := Attests.node_same_consistent (D := D) (j := j)
      (x := D.semilattice.join x y) (y := x) (hx := hxy) (hy := hx)
      (l := r) (m := _l) (r := r) hxy' ihviews
    simpa [CTime.toTime, join_join_left_eq] using hnode
  | node_cross_top _hij _hview _ih => exact Attests.left_top _ _
  | node_cross_consistent hij _hview ih =>
    rename_i j i x y hx hy l m r
    have hxx := consistent_join_self hx
    have hviews : ∀ k hk, Attests D
        (CTime.toTime (CTime.viewsUpdate l hij r k hk))
        (CTime.toTime (l k hk))
        (CTime.toTime (CTime.viewsUpdate l hij r k hk)) := by
      intro k hk
      by_cases hki : k = i
      · subst hki
        simpa [CTime.viewsUpdate] using ih
      · simpa [CTime.viewsUpdate, hki] using self_ctime (l k hk)
    have hnode := Attests.node_same_consistent (D := D) (j := j)
      (x := x) (y := x) (hx := hx) (hy := hx)
      (l := CTime.viewsUpdate l hij r) (m := l) (r := CTime.viewsUpdate l hij r)
      hxx hviews
    simpa [CTime.toTime, D.semilattice.join_idem] using hnode

end Attests

/-- Deterministic equation for the displayed `t # top_i` clause. -/
theorem attest_right_top_clause {D : LocalStateData.{u}} (t : Time D) (i : D.Ctrl) :
    attest t (top D i) = top D (Time.controller t) :=
  (Attests.eq_attest (Attests.right_top (D := D) t i)).symm

/-- Deterministic equation for the displayed non-bottom `t # bot_i` clause. -/
theorem attest_right_bot_clause {D : LocalStateData.{u}} (t : Time D) (i : D.Ctrl)
    (ht : t ≠ bot D (Time.controller t)) :
    attest t (bot D i) = t :=
  (Attests.eq_attest (Attests.right_bot (D := D) t i ht)).symm

/-- Deterministic equation for the displayed `top_j # s` clause. -/
theorem attest_left_top_clause {D : LocalStateData.{u}} (j : D.Ctrl) (s : Time D) :
    attest (top D j) s = top D j :=
  (Attests.eq_attest (Attests.left_top (D := D) j s)).symm

/-- Deterministic equation for same-controller `bot_j # s`. -/
theorem attest_left_bot_same_clause {D : LocalStateData.{u}} {j : D.Ctrl} (s : CTime D j) :
    attest (bot D j) (CTime.toTime s) = CTime.toTime s :=
  (Attests.eq_attest (Attests.left_bot_same (D := D) s)).symm

/-- Deterministic equation for same-controller `bot_j # s`, including the top case. -/
theorem attest_left_bot_same_time_clause {D : LocalStateData.{u}} (j : D.Ctrl) (s : Time D)
    (hctrl : Time.controller s = j) :
    attest (bot D j) s = s := by
  exact attest_bot_left_same_controller j s hctrl

/-- Deterministic equation for the cross-controller `bot_j # top_i` subcase. -/
theorem attest_left_bot_cross_top_clause {D : LocalStateData.{u}} {j i : D.Ctrl}
    (_hij : i ≠ j) :
    attest (bot D j) (top D i) = top D j := by
  simpa [bot, top, Time.controller] using attest_right_top_clause (D := D) (bot D j) i

/-- Deterministic equation for cross-controller `bot_j # s`. -/
theorem attest_left_bot_cross_clause {D : LocalStateData.{u}} {j i : D.Ctrl}
    (hij : i ≠ j) (s : CTime D i) :
    attest (bot D j) (CTime.toTime s) =
      CTime.toTime (CTime.crossBotNode j i hij s) :=
  (Attests.eq_attest (Attests.left_bot_ne (D := D) hij s)).symm

/-- Deterministic equation for same-controller node attestation reaching local top. -/
theorem attest_node_same_local_top_clause {D : LocalStateData.{u}} {j : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l m : (i : D.Ctrl) → i ≠ j → CTime D i}
    (hxy : D.semilattice.join x y = D.semilattice.top) :
    attest (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node j y hy m)) = top D j :=
  (Attests.eq_attest (Attests.node_same_local_top (D := D) (j := j)
    (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m) hxy)).symm

/-- Deterministic equation for same-controller node attestation reaching view top. -/
theorem attest_node_same_view_top_clause {D : LocalStateData.{u}} {j k : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l m : (i : D.Ctrl) → i ≠ j → CTime D i}
    (hkj : k ≠ j)
    (hview : Attests D (CTime.toTime (l k hkj)) (CTime.toTime (m k hkj)) (top D k)) :
    attest (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node j y hy m)) = top D j :=
  (Attests.eq_attest (Attests.node_same_view_top (D := D) (j := j) (k := k)
    (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m) hkj hview)).symm

/-- Deterministic equation for consistent same-controller node attestation. -/
theorem attest_node_same_consistent_clause {D : LocalStateData.{u}} {j : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l m r : (i : D.Ctrl) → i ≠ j → CTime D i}
    (hxy : D.semilattice.Consistent (D.semilattice.join x y))
    (hviews : ∀ i hij, Attests D (CTime.toTime (l i hij)) (CTime.toTime (m i hij))
      (CTime.toTime (r i hij))) :
    attest (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node j y hy m)) =
        CTime.toTime (CTime.node j (D.semilattice.join x y) hxy r) :=
  (Attests.eq_attest (Attests.node_same_consistent (D := D) (j := j)
    (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m) (r := r)
    hxy hviews)).symm

/-- Deterministic equation for cross-controller node attestation reaching top. -/
theorem attest_node_cross_top_clause {D : LocalStateData.{u}} {j i : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l : (k : D.Ctrl) → k ≠ j → CTime D k}
    {m : (k : D.Ctrl) → k ≠ i → CTime D k}
    (hij : i ≠ j)
    (hview : Attests D (CTime.toTime (l i hij))
      (CTime.toTime (CTime.node i y hy m)) (top D i)) :
    attest (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node i y hy m)) = top D j :=
  (Attests.eq_attest (Attests.node_cross_top (D := D) (j := j) (i := i)
    (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m) hij hview)).symm

/-- Deterministic equation for consistent cross-controller node attestation. -/
theorem attest_node_cross_consistent_clause {D : LocalStateData.{u}} {j i : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l : (k : D.Ctrl) → k ≠ j → CTime D k}
    {m : (k : D.Ctrl) → k ≠ i → CTime D k}
    (hij : i ≠ j) {r : CTime D i}
    (hview : Attests D (CTime.toTime (l i hij))
      (CTime.toTime (CTime.node i y hy m)) (CTime.toTime r)) :
    attest (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node i y hy m)) =
        CTime.toTime (CTime.node j x hx (CTime.viewsUpdate l hij r)) :=
  (Attests.eq_attest (Attests.node_cross_consistent (D := D) (j := j) (i := i)
    (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m) (r := r)
    hij hview)).symm

/--
Functional-facing form of the same-controller view-top clause from the
attestation figure (Figure 8).
-/
theorem attest_node_same_view_top_clause_of_attest_eq_top {D : LocalStateData.{u}}
    {j k : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l m : (i : D.Ctrl) → i ≠ j → CTime D i}
    (hkj : k ≠ j)
    (hview :
      attest (CTime.toTime (l k hkj)) (CTime.toTime (m k hkj)) = top D k) :
    attest (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node j y hy m)) = top D j := by
  have hgraph := Attests.attest_graph (D := D)
    (CTime.toTime (l k hkj)) (CTime.toTime (m k hkj))
  rw [hview] at hgraph
  exact attest_node_same_view_top_clause (D := D) (j := j) (k := k)
    (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m) hkj hgraph

/--
Functional-facing form of the consistent same-controller node clause from the
attestation figure (Figure 8).
-/
theorem attest_node_same_consistent_clause_of_attest_eq {D : LocalStateData.{u}}
    {j : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l m r : (i : D.Ctrl) → i ≠ j → CTime D i}
    (hxy : D.semilattice.Consistent (D.semilattice.join x y))
    (hviews : ∀ i hij,
      attest (CTime.toTime (l i hij)) (CTime.toTime (m i hij)) =
        CTime.toTime (r i hij)) :
    attest (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node j y hy m)) =
        CTime.toTime (CTime.node j (D.semilattice.join x y) hxy r) := by
  have hviewsRel :
      ∀ i hij, Attests D (CTime.toTime (l i hij)) (CTime.toTime (m i hij))
        (CTime.toTime (r i hij)) := by
    intro i hij
    have hgraph := Attests.attest_graph (D := D)
      (CTime.toTime (l i hij)) (CTime.toTime (m i hij))
    rw [hviews i hij] at hgraph
    exact hgraph
  exact attest_node_same_consistent_clause (D := D) (j := j)
    (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m) (r := r)
    hxy hviewsRel

/--
Functional-facing form of the cross-controller top clause from the attestation figure (Figure 8).
-/
theorem attest_node_cross_top_clause_of_attest_eq_top {D : LocalStateData.{u}}
    {j i : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l : (k : D.Ctrl) → k ≠ j → CTime D k}
    {m : (k : D.Ctrl) → k ≠ i → CTime D k}
    (hij : i ≠ j)
    (hview :
      attest (CTime.toTime (l i hij)) (CTime.toTime (CTime.node i y hy m)) =
        top D i) :
    attest (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node i y hy m)) = top D j := by
  have hgraph := Attests.attest_graph (D := D)
    (CTime.toTime (l i hij)) (CTime.toTime (CTime.node i y hy m))
  rw [hview] at hgraph
  exact attest_node_cross_top_clause (D := D) (j := j) (i := i)
    (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m) hij hgraph

/--
Functional-facing form of the consistent cross-controller node clause from the
attestation figure (Figure 8).
-/
theorem attest_node_cross_consistent_clause_of_attest_eq {D : LocalStateData.{u}}
    {j i : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l : (k : D.Ctrl) → k ≠ j → CTime D k}
    {m : (k : D.Ctrl) → k ≠ i → CTime D k}
    (hij : i ≠ j) {r : CTime D i}
    (hview :
      attest (CTime.toTime (l i hij)) (CTime.toTime (CTime.node i y hy m)) =
        CTime.toTime r) :
    attest (CTime.toTime (CTime.node j x hx l))
      (CTime.toTime (CTime.node i y hy m)) =
        CTime.toTime (CTime.node j x hx (CTime.viewsUpdate l hij r)) := by
  have hgraph := Attests.attest_graph (D := D)
    (CTime.toTime (l i hij)) (CTime.toTime (CTime.node i y hy m))
  rw [hview] at hgraph
  exact attest_node_cross_consistent_clause (D := D) (j := j) (i := i)
    (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m) hij hgraph

/--
Remark 6.4.10 tuple-check support: the cross-controller consistent
node clause both returns the updated tuple and stores the recursively computed
attested time in the target controller's view slot.
-/
theorem attest_node_cross_consistent_clause_and_updated_view {D : LocalStateData.{u}}
    {j i : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l : (k : D.Ctrl) → k ≠ j → CTime D k}
    {m : (k : D.Ctrl) → k ≠ i → CTime D k}
    (hij : i ≠ j) {r : CTime D i}
    (hview : Attests D (CTime.toTime (l i hij))
      (CTime.toTime (CTime.node i y hy m)) (CTime.toTime r)) :
    attest (CTime.toTime (CTime.node j x hx l))
        (CTime.toTime (CTime.node i y hy m)) =
          CTime.toTime (CTime.node j x hx (CTime.viewsUpdate l hij r)) ∧
      CTime.viewsUpdate l hij r i hij = r := by
  exact ⟨attest_node_cross_consistent_clause (D := D) (j := j) (i := i)
      (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m)
      hij hview,
    CTime.viewsUpdate_same l hij r⟩

/--
Functional-facing form of the tuple-check support: the recursive
stored-view result is supplied as a deterministic `attest` equality.
-/
theorem attest_node_cross_consistent_clause_and_updated_view_of_attest_eq
    {D : LocalStateData.{u}}
    {j i : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l : (k : D.Ctrl) → k ≠ j → CTime D k}
    {m : (k : D.Ctrl) → k ≠ i → CTime D k}
    (hij : i ≠ j) {r : CTime D i}
    (hview :
      attest (CTime.toTime (l i hij)) (CTime.toTime (CTime.node i y hy m)) =
        CTime.toTime r) :
    attest (CTime.toTime (CTime.node j x hx l))
        (CTime.toTime (CTime.node i y hy m)) =
          CTime.toTime (CTime.node j x hx (CTime.viewsUpdate l hij r)) ∧
      CTime.viewsUpdate l hij r i hij = r := by
  exact ⟨attest_node_cross_consistent_clause_of_attest_eq (D := D) (j := j) (i := i)
      (x := x) (y := y) (hx := hx) (hy := hy) (l := l) (m := m)
      hij hview,
    CTime.viewsUpdate_same l hij r⟩

/-- Deterministic same-controller commutativity for the attestation `#`. -/
theorem attest_comm_of_same_controller {D : LocalStateData.{u}} {t s : Time D}
    (hctrl : Time.controller t = Time.controller s) : attest t s = attest s t := by
  exact Attests.eq_attest (Attests.comm_of_same_controller hctrl (Attests.attest_graph t s))

/-- Deterministic expansiveness for the attestation `#`. -/
theorem attest_expansive {D : LocalStateData.{u}} (t s : Time D) :
    attest (attest t s) t = attest t s := by
  exact (Attests.eq_attest (Attests.expansive (Attests.attest_graph t s))).symm

private theorem join_top_left {D : LocalStateData.{u}} (x : D.X) :
    D.semilattice.join D.semilattice.top x = D.semilattice.top := by
  calc
    D.semilattice.join D.semilattice.top x = D.semilattice.join x D.semilattice.top := D.semilattice.join_comm D.semilattice.top x
    _ = D.semilattice.top := D.semilattice.le_top x

private theorem join_assoc_top_of_left {D : LocalStateData.{u}} {x y z : D.X}
    (hxy : D.semilattice.join x y = D.semilattice.top) :
    D.semilattice.join x (D.semilattice.join y z) = D.semilattice.top := by
  calc
    D.semilattice.join x (D.semilattice.join y z) = D.semilattice.join (D.semilattice.join x y) z :=
      (D.semilattice.join_assoc x y z).symm
    _ = D.semilattice.join D.semilattice.top z := by rw [hxy]
    _ = D.semilattice.top := join_top_left z

private theorem join_assoc_top_of_right {D : LocalStateData.{u}} {x y z : D.X}
    (hyz : D.semilattice.join y z = D.semilattice.top) :
    D.semilattice.join (D.semilattice.join x y) z = D.semilattice.top := by
  calc
    D.semilattice.join (D.semilattice.join x y) z = D.semilattice.join x (D.semilattice.join y z) :=
      D.semilattice.join_assoc x y z
    _ = D.semilattice.join x D.semilattice.top := by rw [hyz]
    _ = D.semilattice.top := D.semilattice.le_top x

private theorem CTime.toTime_inj {D : LocalStateData.{u}} {j : D.Ctrl}
    {t s : CTime D j} (h : CTime.toTime t = CTime.toTime s) : t = s := by
  cases h
  rfl

private theorem CTime.node_ext {D : LocalStateData.{u}} {j : D.Ctrl}
    {x y : D.X} {hx : D.semilattice.Consistent x} {hy : D.semilattice.Consistent y}
    {l m : (i : D.Ctrl) → i ≠ j → CTime D i}
    (hxy : x = y) (hviews : ∀ i hij, l i hij = m i hij) :
    CTime.node j x hx l = CTime.node j y hy m := by
  cases hxy
  congr
  funext i hij
  exact hviews i hij

/-- Deterministic same-controller associativity for the attestation `#`. -/
theorem attest_assoc_of_same_controller {D : LocalStateData.{u}} {t t' u : Time D}
    (htt' : Time.controller t = Time.controller t')
    (ht'u : Time.controller t' = Time.controller u) :
    attest (attest t t') u = attest t (attest t' u) := by
  exact (Time.rec (D := D)
    (motive_1 := fun t => ∀ t' u : Time D,
      Time.controller t = Time.controller t' →
      Time.controller t' = Time.controller u →
      attest (attest t t') u = attest t (attest t' u))
    (motive_2 := fun _j t => ∀ t' u : Time D,
      Time.controller (CTime.toTime t) = Time.controller t' →
      Time.controller t' = Time.controller u →
      attest (attest (CTime.toTime t) t') u =
        attest (CTime.toTime t) (attest t' u))
    (fun j t' u htt' ht'u => by
      rfl)
    (fun _t ih t' u htt' ht'u => ih t' u htt' ht'u)
    (fun j t' u htt' ht'u => by
      have hleft : attest (bot D j) t' = t' :=
        attest_bot_left_same_controller j t' htt'.symm
      have hright_ctrl : Time.controller (attest t' u) = j := by
        calc
          Time.controller (attest t' u) = Time.controller t' := attest_controller t' u
          _ = j := htt'.symm
      calc
        attest (attest (bot D j) t') u = attest t' u := by rw [hleft]
        _ = attest (bot D j) (attest t' u) :=
          (attest_bot_left_same_controller j (attest t' u) hright_ctrl).symm)
    (fun j x hx l ih t' u htt' ht'u => by
      cases t' with
      | top j' =>
          simp [Time.controller] at htt'
          cases htt'
          rfl
      | consistent t' =>
          cases u with
          | top j'' =>
              simp [Time.controller] at htt' ht'u
              cases htt'
              cases ht'u
              have hleft :
                  attest (attest (CTime.toTime (CTime.node j x hx l)) (CTime.toTime t'))
                    (top D j) =
                    top D j := by
                apply attest_top_right_same_controller
                exact attest_controller _ _
              have hinner : attest (CTime.toTime t') (top D j) = top D j :=
                attest_top_right_same_controller j (CTime.toTime t') rfl
              have hright :
                  attest (CTime.toTime (CTime.node j x hx l))
                    (attest (CTime.toTime t') (top D j)) =
                    top D j := by
                rw [hinner]
                exact attest_top_right_same_controller j
                  (CTime.toTime (CTime.node j x hx l)) rfl
              exact hleft.trans hright.symm
          | consistent u =>
              cases t' with
              | bot j' =>
                  simp [Time.controller] at htt'
                  cases htt'
                  have hleft : attest (CTime.toTime (CTime.node j x hx l)) (bot D j) =
                      CTime.toTime (CTime.node j x hx l) :=
                    attest_bot_right_same_controller j
                      (CTime.toTime (CTime.node j x hx l)) rfl
                  simp [bot] at hleft
                  have hright : attest (bot D j) (CTime.toTime u) = CTime.toTime u :=
                    attest_bot_left_same_controller j (CTime.toTime u)
                      (by simpa [Time.controller, CTime.toTime] using ht'u.symm)
                  calc
                    attest
                        (attest (CTime.toTime (CTime.node j x hx l))
                          (CTime.toTime (CTime.bot j)))
                        (CTime.toTime u) =
                        attest (CTime.toTime (CTime.node j x hx l)) (CTime.toTime u) := by
                          simpa [CTime.toTime] using
                            congrArg (fun r => attest r (CTime.toTime u)) hleft
                    _ = attest (CTime.toTime (CTime.node j x hx l))
                        (attest (CTime.toTime (CTime.bot j)) (CTime.toTime u)) := by
                          simpa [bot, CTime.toTime] using
                            congrArg (fun r => attest (CTime.toTime (CTime.node j x hx l)) r)
                              hright.symm
              | node j' y hy m =>
                  cases u with
                  | bot j'' =>
                      simp [Time.controller] at htt' ht'u
                      cases htt'
                      cases ht'u
                      have hleft :
                          attest
                              (attest (CTime.toTime (CTime.node j x hx l))
                                (CTime.toTime (CTime.node j y hy m)))
                              (bot D j) =
                            attest (CTime.toTime (CTime.node j x hx l))
                              (CTime.toTime (CTime.node j y hy m)) := by
                        apply attest_bot_right_same_controller
                        exact attest_controller _ _
                      have hinner : attest (CTime.toTime (CTime.node j y hy m)) (bot D j) =
                          CTime.toTime (CTime.node j y hy m) :=
                        attest_bot_right_same_controller j
                          (CTime.toTime (CTime.node j y hy m)) rfl
                      have hright :
                          attest (CTime.toTime (CTime.node j x hx l))
                              (attest (CTime.toTime (CTime.node j y hy m)) (bot D j)) =
                            attest (CTime.toTime (CTime.node j x hx l))
                              (CTime.toTime (CTime.node j y hy m)) := by
                        rw [hinner]
                      exact hleft.trans hright.symm
                  | node j'' z hz n =>
                      simp [Time.controller] at htt' ht'u
                      cases htt'
                      cases ht'u
                      simp only [attest, attestAtTime, attestAtCTime, CTime.toTime,
                        Time.controller]
                      rw [dif_pos rfl, dif_pos trivial]
                      by_cases hxy : D.semilattice.join x y = D.semilattice.top
                      · have hx_yz_top : D.semilattice.join x (D.semilattice.join y z) = D.semilattice.top :=
                          join_assoc_top_of_left hxy
                        rw [dif_pos hxy]
                        by_cases hyz : D.semilattice.join y z = D.semilattice.top
                        · simp [hyz, attestAtCTime, Time.controller]
                        · by_cases hyzView :
                              ∃ (k : D.Ctrl) (hkj : k ≠ j),
                                (attestAtCTime (m k hkj) (Time.consistent (n k hkj))).1 =
                                  Time.top k
                          · simp [hyz, hyzView, attestAtCTime, Time.controller]
                          · simp [hyz, hyzView, hx_yz_top, attestAtCTime, Time.controller]
                      · rw [dif_neg hxy]
                        by_cases hxyView :
                            ∃ (k : D.Ctrl) (hkj : k ≠ j),
                              (attestAtCTime (l k hkj) (Time.consistent (m k hkj))).1 =
                                Time.top k
                        · rw [dif_pos hxyView]
                          by_cases hyz : D.semilattice.join y z = D.semilattice.top
                          · simp [hyz, attestAtCTime, Time.controller]
                          · by_cases hyzView :
                                ∃ (k : D.Ctrl) (hkj : k ≠ j),
                                  (attestAtCTime (m k hkj) (Time.consistent (n k hkj))).1 =
                                    Time.top k
                            · simp [hyz, hyzView, attestAtCTime, Time.controller]
                            · have hrightView :
                                  ∃ (k : D.Ctrl) (hkj : k ≠ j),
                                    (attestAtCTime (l k hkj)
                                      (CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)))).1 =
                                      Time.top k := by
                                rcases hxyView with ⟨k, hkj, hlm_top⟩
                                refine ⟨k, hkj, ?_⟩
                                have ihk := ih k hkj (CTime.toTime (m k hkj))
                                  (CTime.toTime (n k hkj)) rfl rfl
                                have hlm_attest :
                                    attest (CTime.toTime (l k hkj))
                                        (CTime.toTime (m k hkj)) =
                                      Time.top k := by
                                  simpa [attest_ctime_eq, CTime.toTime] using hlm_top
                                have hleft_top :
                                    attest
                                        (attest (CTime.toTime (l k hkj))
                                          (CTime.toTime (m k hkj)))
                                        (CTime.toTime (n k hkj)) =
                                      Time.top k := by
                                  rw [hlm_attest]
                                  rfl
                                have hright_top :
                                    attest (CTime.toTime (l k hkj))
                                        (attest (CTime.toTime (m k hkj))
                                          (CTime.toTime (n k hkj))) =
                                      Time.top k :=
                                  ihk.symm.trans hleft_top
                                have hmn_toTime :
                                    CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)) =
                                      (attestAtCTime (m k hkj)
                                        (Time.consistent (n k hkj))).1 :=
                                    Time.toCTimeOfNonTop_toTime
                                    (attestAtCTime (m k hkj)
                                      (Time.consistent (n k hkj)))
                                    (by
                                      intro htop
                                      exact hyzView ⟨k, hkj, htop⟩)
                                rw [attest_ctime_eq] at hright_top
                                rw [attest_ctime_eq] at hright_top
                                have hmn_toTime' :
                                    CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)) =
                                      (attestAtCTime (m k hkj)
                                        (CTime.toTime (n k hkj))).1 := by
                                  simpa [CTime.toTime] using hmn_toTime
                                rw [← hmn_toTime'] at hright_top
                                simpa [attest_ctime_eq] using hright_top
                              by_cases hx_yz : D.semilattice.join x (D.semilattice.join y z) = D.semilattice.top
                              · simp [hyz, hyzView, hx_yz, attestAtCTime, Time.controller]
                              · simp [hyz, hyzView, hx_yz, hrightView, attestAtCTime,
                                  Time.controller]
                        · rw [dif_neg hxyView]
                          by_cases hyz : D.semilattice.join y z = D.semilattice.top
                          · have hxy_z_top : D.semilattice.join (D.semilattice.join x y) z = D.semilattice.top :=
                              join_assoc_top_of_right hyz
                            simp [hyz, hxy_z_top, attestAtCTime, Time.controller]
                          · by_cases hyzView :
                                ∃ (k : D.Ctrl) (hkj : k ≠ j),
                                  (attestAtCTime (m k hkj) (Time.consistent (n k hkj))).1 =
                                    Time.top k
                            · have hleftView :
                                  ∃ (k : D.Ctrl) (hkj : k ≠ j),
                                    (attestAtCTime
                                      (Time.toCTimeOfNonTop
                                        (attestAtCTime (l k hkj)
                                          (Time.consistent (m k hkj)))
                                        (by
                                          intro htop
                                          exact hxyView ⟨k, hkj, htop⟩))
                                      (CTime.toTime (n k hkj))).1 =
                                      Time.top k := by
                                rcases hyzView with ⟨k, hkj, hmn_top⟩
                                refine ⟨k, hkj, ?_⟩
                                have ihk := ih k hkj (CTime.toTime (m k hkj))
                                  (CTime.toTime (n k hkj)) rfl rfl
                                have hmn_attest :
                                    attest (CTime.toTime (m k hkj))
                                        (CTime.toTime (n k hkj)) =
                                      Time.top k := by
                                  simpa [attest_ctime_eq, CTime.toTime] using hmn_top
                                have hright_top :
                                    attest (CTime.toTime (l k hkj))
                                        (attest (CTime.toTime (m k hkj))
                                          (CTime.toTime (n k hkj))) =
                                      Time.top k := by
                                  rw [hmn_attest]
                                  exact attest_top_right_same_controller k
                                    (CTime.toTime (l k hkj)) rfl
                                have hleft_top :
                                    attest
                                        (attest (CTime.toTime (l k hkj))
                                          (CTime.toTime (m k hkj)))
                                        (CTime.toTime (n k hkj)) =
                                      Time.top k :=
                                  ihk.trans hright_top
                                have hlm_toTime :
                                    CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (l k hkj)
                                            (Time.consistent (m k hkj)))
                                          (by
                                            intro htop
                                            exact hxyView ⟨k, hkj, htop⟩)) =
                                      (attestAtCTime (l k hkj)
                                        (CTime.toTime (m k hkj))).1 := by
                                  have hlm_toTime_raw :
                                      CTime.toTime
                                          (Time.toCTimeOfNonTop
                                            (attestAtCTime (l k hkj)
                                              (Time.consistent (m k hkj)))
                                            (by
                                              intro htop
                                              exact hxyView ⟨k, hkj, htop⟩)) =
                                        (attestAtCTime (l k hkj)
                                          (Time.consistent (m k hkj))).1 :=
                                    Time.toCTimeOfNonTop_toTime
                                      (attestAtCTime (l k hkj)
                                        (Time.consistent (m k hkj)))
                                      (by
                                        intro htop
                                        exact hxyView ⟨k, hkj, htop⟩)
                                  simpa [CTime.toTime] using hlm_toTime_raw
                                rw [attest_ctime_eq] at hleft_top
                                rw [← hlm_toTime] at hleft_top
                                simpa [attest_ctime_eq] using hleft_top
                              by_cases hxy_z : D.semilattice.join (D.semilattice.join x y) z = D.semilattice.top
                              · simp [hyz, hyzView, hxy_z, attestAtCTime, Time.controller]
                              · simp [hyz, hyzView, hxy_z, hleftView, attestAtCTime,
                                  Time.controller]
                            · rw [dif_neg hyz, dif_neg hyzView]
                              simp only [attestAtCTime, Time.controller, CTime.toTime]
                              rw [dif_pos trivial, dif_pos trivial]
                              have view_assoc_value :
                                  ∀ k hkj,
                                    (attestAtCTime
                                      (Time.toCTimeOfNonTop
                                        (attestAtCTime (l k hkj)
                                          (Time.consistent (m k hkj)))
                                        (by
                                          intro htop
                                          exact hxyView ⟨k, hkj, htop⟩))
                                      (Time.consistent (n k hkj))).1 =
                                    (attestAtCTime (l k hkj)
                                      (Time.consistent
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)))).1 := by
                                intro k hkj
                                have ihk := ih k hkj (CTime.toTime (m k hkj))
                                  (CTime.toTime (n k hkj)) rfl rfl
                                have hlm_toTime :
                                    CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (l k hkj)
                                            (Time.consistent (m k hkj)))
                                          (by
                                            intro htop
                                            exact hxyView ⟨k, hkj, htop⟩)) =
                                      (attestAtCTime (l k hkj)
                                        (CTime.toTime (m k hkj))).1 := by
                                  have raw :=
                                    Time.toCTimeOfNonTop_toTime
                                      (attestAtCTime (l k hkj)
                                        (Time.consistent (m k hkj)))
                                      (by
                                        intro htop
                                        exact hxyView ⟨k, hkj, htop⟩)
                                  simpa [CTime.toTime] using raw
                                have hmn_toTime :
                                    CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)) =
                                      (attestAtCTime (m k hkj)
                                        (CTime.toTime (n k hkj))).1 := by
                                  have raw :=
                                    Time.toCTimeOfNonTop_toTime
                                      (attestAtCTime (m k hkj)
                                        (Time.consistent (n k hkj)))
                                      (by
                                        intro htop
                                        exact hyzView ⟨k, hkj, htop⟩)
                                  simpa [CTime.toTime] using raw
                                have hlm_attest_time :
                                    CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (l k hkj)
                                            (Time.consistent (m k hkj)))
                                          (by
                                            intro htop
                                            exact hxyView ⟨k, hkj, htop⟩)) =
                                      attest (CTime.toTime (l k hkj))
                                        (CTime.toTime (m k hkj)) := by
                                  calc
                                    CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (l k hkj)
                                            (Time.consistent (m k hkj)))
                                          (by
                                            intro htop
                                            exact hxyView ⟨k, hkj, htop⟩)) =
                                        (attestAtCTime (l k hkj)
                                          (CTime.toTime (m k hkj))).1 := hlm_toTime
                                    _ = attest (CTime.toTime (l k hkj))
                                        (CTime.toTime (m k hkj)) :=
                                      (attest_ctime_eq (l k hkj)
                                        (CTime.toTime (m k hkj))).symm
                                have hmn_attest_time :
                                    CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)) =
                                      attest (CTime.toTime (m k hkj))
                                        (CTime.toTime (n k hkj)) := by
                                  calc
                                    CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)) =
                                        (attestAtCTime (m k hkj)
                                          (CTime.toTime (n k hkj))).1 := hmn_toTime
                                    _ = attest (CTime.toTime (m k hkj))
                                        (CTime.toTime (n k hkj)) :=
                                      (attest_ctime_eq (m k hkj)
                                        (CTime.toTime (n k hkj))).symm
                                have htime :
                                    attest
                                        (CTime.toTime
                                          (Time.toCTimeOfNonTop
                                            (attestAtCTime (l k hkj)
                                              (Time.consistent (m k hkj)))
                                            (by
                                              intro htop
                                              exact hxyView ⟨k, hkj, htop⟩)))
                                        (CTime.toTime (n k hkj)) =
                                      attest (CTime.toTime (l k hkj))
                                        (CTime.toTime
                                          (Time.toCTimeOfNonTop
                                            (attestAtCTime (m k hkj)
                                              (Time.consistent (n k hkj)))
                                            (by
                                              intro htop
                                              exact hyzView ⟨k, hkj, htop⟩))) := by
                                  calc
                                    attest
                                        (CTime.toTime
                                          (Time.toCTimeOfNonTop
                                            (attestAtCTime (l k hkj)
                                              (Time.consistent (m k hkj)))
                                            (by
                                              intro htop
                                              exact hxyView ⟨k, hkj, htop⟩)))
                                        (CTime.toTime (n k hkj)) =
                                        attest
                                          (attest (CTime.toTime (l k hkj))
                                            (CTime.toTime (m k hkj)))
                                          (CTime.toTime (n k hkj)) := by
                                      rw [hlm_attest_time]
                                    _ = attest (CTime.toTime (l k hkj))
                                        (attest (CTime.toTime (m k hkj))
                                          (CTime.toTime (n k hkj))) := ihk
                                    _ = attest (CTime.toTime (l k hkj))
                                        (CTime.toTime
                                          (Time.toCTimeOfNonTop
                                            (attestAtCTime (m k hkj)
                                              (Time.consistent (n k hkj)))
                                            (by
                                              intro htop
                                              exact hyzView ⟨k, hkj, htop⟩))) := by
                                      rw [hmn_attest_time]
                                calc
                                  (attestAtCTime
                                      (Time.toCTimeOfNonTop
                                        (attestAtCTime (l k hkj)
                                          (Time.consistent (m k hkj)))
                                        (by
                                          intro htop
                                          exact hxyView ⟨k, hkj, htop⟩))
                                      (Time.consistent (n k hkj))).1 =
                                      attest
                                        (CTime.toTime
                                          (Time.toCTimeOfNonTop
                                            (attestAtCTime (l k hkj)
                                              (Time.consistent (m k hkj)))
                                            (by
                                              intro htop
                                              exact hxyView ⟨k, hkj, htop⟩)))
                                        (CTime.toTime (n k hkj)) :=
                                    (attest_ctime_eq
                                      (Time.toCTimeOfNonTop
                                        (attestAtCTime (l k hkj)
                                          (Time.consistent (m k hkj)))
                                        (by
                                          intro htop
                                          exact hxyView ⟨k, hkj, htop⟩))
                                      (CTime.toTime (n k hkj))).symm
                                  _ = attest (CTime.toTime (l k hkj))
                                      (CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩))) := htime
                                  _ = (attestAtCTime (l k hkj)
                                      (Time.consistent
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)))).1 :=
                                    attest_ctime_eq (l k hkj)
                                      (CTime.toTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)))
                              have hview_iff :
                                  (∃ k hkj,
                                    (attestAtCTime
                                      (Time.toCTimeOfNonTop
                                        (attestAtCTime (l k hkj)
                                          (Time.consistent (m k hkj)))
                                        (by
                                          intro htop
                                          exact hxyView ⟨k, hkj, htop⟩))
                                      (Time.consistent (n k hkj))).1 =
                                      Time.top k) ↔
                                  (∃ k hkj,
                                    (attestAtCTime (l k hkj)
                                      (Time.consistent
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (m k hkj)
                                            (Time.consistent (n k hkj)))
                                          (by
                                            intro htop
                                            exact hyzView ⟨k, hkj, htop⟩)))).1 =
                                      Time.top k) := by
                                constructor
                                · rintro ⟨k, hkj, htop⟩
                                  exact ⟨k, hkj, (view_assoc_value k hkj).symm.trans htop⟩
                                · rintro ⟨k, hkj, htop⟩
                                  exact ⟨k, hkj, (view_assoc_value k hkj).trans htop⟩
                              have hlocal :
                                  D.semilattice.join (D.semilattice.join x y) z =
                                    D.semilattice.join x (D.semilattice.join y z) :=
                                D.semilattice.join_assoc x y z
                              by_cases hleftLocal : D.semilattice.join (D.semilattice.join x y) z = D.semilattice.top
                              · have hrightLocal : D.semilattice.join x (D.semilattice.join y z) = D.semilattice.top := by
                                  rwa [hlocal] at hleftLocal
                                simp [hleftLocal, hrightLocal]
                              · have hrightLocal :
                                  ¬ D.semilattice.join x (D.semilattice.join y z) = D.semilattice.top := by
                                  intro htop
                                  exact hleftLocal (hlocal.trans htop)
                                rw [dif_neg hleftLocal, dif_neg hrightLocal]
                                by_cases hleftView :
                                    ∃ k hkj,
                                      (attestAtCTime
                                        (Time.toCTimeOfNonTop
                                          (attestAtCTime (l k hkj)
                                            (Time.consistent (m k hkj)))
                                          (by
                                            intro htop
                                            exact hxyView ⟨k, hkj, htop⟩))
                                        (Time.consistent (n k hkj))).1 =
                                        Time.top k
                                · have hrightView := hview_iff.mp hleftView
                                  simp [hleftView, hrightView]
                                · have hrightView :
                                    ¬ ∃ k hkj,
                                      (attestAtCTime (l k hkj)
                                        (Time.consistent
                                          (Time.toCTimeOfNonTop
                                            (attestAtCTime (m k hkj)
                                              (Time.consistent (n k hkj)))
                                            (by
                                              intro htop
                                              exact hyzView ⟨k, hkj, htop⟩)))).1 =
                                        Time.top k := by
                                    intro hview
                                    exact hleftView (hview_iff.mpr hview)
                                  rw [dif_neg hleftView, dif_neg hrightView]
                                  apply congrArg CTime.toTime
                                  apply CTime.node_ext hlocal
                                  intro k hkj
                                  apply CTime.toTime_inj
                                  rw [Time.toCTimeOfNonTop_toTime,
                                    Time.toCTimeOfNonTop_toTime]
                                  exact view_assoc_value k hkj)
    t) t' u htt' ht'u

end LocalStateData

end ContForm.Models.Cut.InductiveConstruction
