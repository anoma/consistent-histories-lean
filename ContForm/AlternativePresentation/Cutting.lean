import ContForm.AlternativePresentation.Semitopology

namespace ContForm.AlternativePresentation

open ContForm.Models.Cut.Consistency
open ContForm.Foundation.Cut.Structure
open ContForm.Foundation.Cut.Flags
open ContForm.Foundation.LocatedSemilattices.TopTrees
open ContForm.Foundation.LocatedSemilattices.TopTrees.BoundedSemilattice

universe u v

/-- A cutting-flag atom generating `CuttingPoset` (Definition 7.7(1)): one of the
flags `nextindex_i`, `cutme_i`, `cutyou_i` of the cutting flag-set of Definition
3.2.1, recorded as a `CutFlagKind` symbol paired with an index `i : ℕ`. -/
structure CuttingFlag where
  kind : CutFlagKind
  index : Nat
  deriving DecidableEq

namespace CuttingFlag

/-- The flag `nextindex_i` of Definition 3.2.1. -/
def nextIndex (i : Nat) : CuttingFlag :=
  ⟨CutFlagKind.nextIndex, i⟩

/-- The flag `cutme_i` of Definition 3.2.1. -/
def cutMe (i : Nat) : CuttingFlag :=
  ⟨CutFlagKind.cutMe, i⟩

/-- The flag `cutyou_i` of Definition 3.2.1. -/
def cutYou (i : Nat) : CuttingFlag :=
  ⟨CutFlagKind.cutYou, i⟩

/-- Send a cutting-flag atom to its label in the concrete carrier `ConcreteTime`
that realizes `CuttingPoset` (Definition 7.7(1)). -/
def toConcrete (flag : CuttingFlag) : ConcreteTime :=
  ConcreteTime.ofFlagKind flag.kind flag.index

/-- The generating `≤`-arrows of Figure 6 (Remark 3.2.2): the covering relations
of Definition 3.2.1(1) `nextindex_j ≤ cutme_j`, (2) `nextindex_j ≤ cutyou_j`, and
(3) `cutyou_j ≤ nextindex_i` when `i < j`. -/
inductive Step : CuttingFlag → CuttingFlag → Prop where
  | next_le_cutMe (j : Nat) : Step (nextIndex j) (cutMe j)
  | next_le_cutYou (j : Nat) : Step (nextIndex j) (cutYou j)
  | cutYou_le_next {i j : Nat} (hij : i < j) : Step (cutYou j) (nextIndex i)

/-- The flag order of `CuttingPoset` on atoms: the reflexive-transitive closure of
the Figure 6 arrows (`Step`), per Definition 7.7(1). -/
inductive Le : CuttingFlag → CuttingFlag → Prop where
  | refl (flag : CuttingFlag) : Le flag flag
  | step {flag flag' : CuttingFlag} (h : Step flag flag') : Le flag flag'
  | trans {a b c : CuttingFlag} (hab : Le a b) (hbc : Le b c) : Le a c

/-- Derived Figure 6 arrow `cutyou_j ≤ cutme_i` for `i < j`, obtained by composing
Definition 3.2.1(3) `cutyou_j ≤ nextindex_i` with (1) `nextindex_i ≤ cutme_i`. -/
theorem cutYou_le_cutMe_of_lt {i j : Nat} (hij : i < j) :
    Le (cutYou j) (cutMe i) := by
  exact Le.trans (Le.step (Step.cutYou_le_next hij)) (Le.step (Step.next_le_cutMe i))

theorem cutMe_le_eq_self_aux {flag flag' : CuttingFlag}
    (h : Le flag flag') : (∃ j : Nat, flag = cutMe j) → flag' = flag := by
  induction h with
  | refl _flag =>
      intro _hcut
      rfl
  | step hstep =>
      intro hcut
      rcases hcut with ⟨_j, hcut⟩
      cases hcut
      cases hstep
  | @trans _start middle _finish _hab _hbc ihab ihbc =>
      intro hcut
      have hmiddle := ihab hcut
      have hmiddle_cut : ∃ j : Nat, middle = cutMe j := by
        rcases hcut with ⟨j, hcut⟩
        exact ⟨j, hmiddle.trans hcut⟩
      exact (ihbc hmiddle_cut).trans hmiddle

/-- In the flag order, `cutme_j` is maximal: no atom lies strictly above it. This
is the geometric fact that `cutme_j` is a leaf of a top branch of Figure 6. -/
theorem cutMe_le_eq_self {j : Nat} {flag : CuttingFlag}
    (h : Le (cutMe j) flag) : flag = cutMe j := by
  exact cutMe_le_eq_self_aux h ⟨j, rfl⟩

/-- `cutme_j ≰ cutyou_j`: the same-index `cutme` and `cutyou` atoms lie on distinct
branches of Figure 6, one direction of Definition 3.2.1(4) (Remark 3.2.2). -/
theorem not_cutMe_le_cutYou_same (j : Nat) :
    ¬ Le (cutMe j) (cutYou j) := by
  intro h
  have hself := cutMe_le_eq_self h
  cases hself

end CuttingFlag

/-- The carrier of `CuttingPoset` (Definition 7.7(1)): the cutting-flag atoms with
the bottom `⊥_CuttingPoset` and top `⊤_CuttingPoset` adjoined. -/
inductive CuttingPosetPoint where
  | bot
  | flag (flag : CuttingFlag)
  | top
  deriving DecidableEq

namespace CuttingPosetPoint

/-- The `CuttingPoset` order (Definition 7.7(1)): the atom order `CuttingFlag.Le`
extended so that `⊥_CuttingPoset` is least and `⊤_CuttingPoset` is greatest. -/
inductive Le : CuttingPosetPoint → CuttingPosetPoint → Prop where
  | refl (point : CuttingPosetPoint) : Le point point
  | bot_le (point : CuttingPosetPoint) : Le bot point
  | le_top (point : CuttingPosetPoint) : Le point top
  | of_flag {flag flag' : CuttingFlag} (h : CuttingFlag.Le flag flag') :
      Le (CuttingPosetPoint.flag flag) (CuttingPosetPoint.flag flag')
  | trans {a b c : CuttingPosetPoint} (hab : Le a b) (hbc : Le b c) : Le a c

/-- Definition 3.2.1(1) in `CuttingPoset`: `nextindex_j ≤ cutme_j`. -/
theorem next_le_cutMe (j : Nat) :
    Le (flag (CuttingFlag.nextIndex j)) (flag (CuttingFlag.cutMe j)) := by
  exact Le.of_flag (CuttingFlag.Le.step (CuttingFlag.Step.next_le_cutMe j))

/-- Definition 3.2.1(2) in `CuttingPoset`: `nextindex_j ≤ cutyou_j`. -/
theorem next_le_cutYou (j : Nat) :
    Le (flag (CuttingFlag.nextIndex j)) (flag (CuttingFlag.cutYou j)) := by
  exact Le.of_flag (CuttingFlag.Le.step (CuttingFlag.Step.next_le_cutYou j))

/-- Definition 3.2.1(3) in `CuttingPoset`: `cutyou_j ≤ nextindex_i` when `i < j`. -/
theorem cutYou_le_next {i j : Nat} (hij : i < j) :
    Le (flag (CuttingFlag.cutYou j)) (flag (CuttingFlag.nextIndex i)) := by
  exact Le.of_flag (CuttingFlag.Le.step (CuttingFlag.Step.cutYou_le_next hij))

/-- Derived Figure 6 arrow in `CuttingPoset`: `cutyou_j ≤ cutme_i` when `i < j`,
composing Definition 3.2.1(3) with (1). -/
theorem cutYou_le_cutMe_of_lt {i j : Nat} (hij : i < j) :
    Le (flag (CuttingFlag.cutYou j)) (flag (CuttingFlag.cutMe i)) := by
  exact Le.of_flag (CuttingFlag.cutYou_le_cutMe_of_lt hij)

theorem top_le_eq_top_aux {point point' : CuttingPosetPoint}
    (h : Le point point') : point = top → point' = top := by
  induction h with
  | refl _point =>
      intro htop
      exact htop
  | bot_le _point =>
      intro htop
      cases htop
  | le_top _point =>
      intro _htop
      rfl
  | of_flag _hflag =>
      intro htop
      cases htop
  | @trans _start _middle _finish _hab _hbc ihab ihbc =>
      intro htop
      exact ihbc (ihab htop)

/-- `⊤_CuttingPoset` is greatest: nothing lies above it. -/
theorem top_le_eq_top {point : CuttingPosetPoint}
    (h : Le top point) : point = top := by
  exact top_le_eq_top_aux h rfl

theorem cutMe_le_eq_self_or_top_aux {point point' : CuttingPosetPoint}
    (h : Le point point') :
    (∃ j : Nat, point = flag (CuttingFlag.cutMe j)) →
    point' = point ∨ point' = top := by
  induction h with
  | refl _point =>
      intro _hcut
      exact Or.inl rfl
  | bot_le _point =>
      intro hcut
      rcases hcut with ⟨_j, hcut⟩
      cases hcut
  | le_top _point =>
      intro _hcut
      exact Or.inr rfl
  | of_flag hflag =>
      intro hcut
      rcases hcut with ⟨_j, hcut⟩
      cases hcut
      have hself := CuttingFlag.cutMe_le_eq_self hflag
      exact Or.inl (congrArg flag hself)
  | @trans _start middle _finish _hab hbc ihab ihbc =>
      intro hcut
      rcases ihab hcut with hmiddle | hmiddle_top
      · have hmiddle_cut : ∃ j : Nat, middle = flag (CuttingFlag.cutMe j) := by
          rcases hcut with ⟨j, hcut⟩
          exact ⟨j, hmiddle.trans hcut⟩
        rcases ihbc hmiddle_cut with hend | hend_top
        · exact Or.inl (hend.trans hmiddle)
        · exact Or.inr hend_top
      · exact Or.inr (top_le_eq_top_aux hbc hmiddle_top)

/-- In `CuttingPoset` the only points above `cutme_j` are `cutme_j` itself and
`⊤_CuttingPoset`: the atom `cutme_j` is a leaf of a top branch of Figure 6. -/
theorem cutMe_le_eq_self_or_top {j : Nat} {point : CuttingPosetPoint}
    (h : Le (flag (CuttingFlag.cutMe j)) point) :
    point = flag (CuttingFlag.cutMe j) ∨ point = top := by
  exact cutMe_le_eq_self_or_top_aux h ⟨j, rfl⟩

/-- `cutme_j ≰ cutyou_j` in `CuttingPoset`: same-index `cutme` and `cutyou` lie on
distinct branches of Figure 6, one direction of Definition 3.2.1(4) (Remark 3.2.2). -/
theorem not_cutMe_le_cutYou_same (j : Nat) :
    ¬ Le (flag (CuttingFlag.cutMe j)) (flag (CuttingFlag.cutYou j)) := by
  intro h
  rcases cutMe_le_eq_self_or_top h with hself | htop
  · cases hself
  · cases htop

/-- Send a `CuttingPoset` point to its label in the concrete carrier `ConcreteTime`
that realizes `CuttingPoset` (Definition 7.7(1)), with `⊥`/`⊤` to `bot`/`top`. -/
def toConcrete : CuttingPosetPoint → ConcreteTime
  | bot => ConcreteTime.bot
  | .flag cf => cf.toConcrete
  | top => ConcreteTime.top

end CuttingPosetPoint

/-- Definition 7.7(1): the cutting-flag bounded semilattice `CuttingPoset`,
realized on the concrete carrier `ConcreteTime` with `ConcreteTime.join`. -/
instance cuttingFlagBoundedSemilattice : BoundedSemilattice ConcreteTime where
  join := ConcreteTime.join
  bot := ConcreteTime.bot
  top := ConcreteTime.top
  join_idem := ConcreteTime.join_idem
  join_comm := ConcreteTime.join_comm
  join_assoc := ConcreteTime.join_assoc
  bot_le := ConcreteTime.join_bot_left
  le_top := ConcreteTime.join_top_right

/-- Definition 7.7(1): `CuttingPoset` is a top-tree (a sequential bounded
semilattice), as required for it to be the generated cutting-flag semilattice. -/
theorem cuttingFlagBoundedSemilattice_isTopTree :
    cuttingFlagBoundedSemilattice.IsTopTree := by
  intro t t'
  cases t <;> cases t' <;>
    simp [cuttingFlagBoundedSemilattice,
      ConcreteTime.join, ConcreteTime.joinChain, ConcreteTime.joinChainCutMe,
      ConcreteTime.chainRank?]
  all_goals repeat split
  all_goals simp_all
  all_goals omega

/--
Soundness of the generated `CuttingPoset` order: whenever `point ≤ point'` holds in
the reflexive-transitive closure of the Figure 6 arrows (Definition 7.7(1)), the
join-order `point.toConcrete ≤ point'.toConcrete` holds in the concrete
cutting-flag bounded semilattice.
-/
theorem cuttingPosetPoint_le_sound {point point' : CuttingPosetPoint}
    (h : CuttingPosetPoint.Le point point') :
    point.toConcrete ≤ point'.toConcrete := by
  induction h with
  | refl point =>
      exact cuttingFlagBoundedSemilattice.le_refl point.toConcrete
  | bot_le point =>
      change ConcreteTime.bot ≤ point.toConcrete
      exact cuttingFlagBoundedSemilattice.bot_le' point.toConcrete
  | le_top point =>
      change point.toConcrete ≤ ConcreteTime.top
      exact cuttingFlagBoundedSemilattice.le_top' point.toConcrete
  | @of_flag flag flag' hflag =>
      have hflag_sound :
          flag.toConcrete ≤ flag'.toConcrete := by
        induction hflag with
        | refl flag =>
            exact cuttingFlagBoundedSemilattice.le_refl flag.toConcrete
        | step hstep =>
            cases hstep with
            | next_le_cutMe j =>
                change ConcreteTime.join (ConcreteTime.nextIndex j) (ConcreteTime.cutMe j) =
                  ConcreteTime.cutMe j
                simp [ConcreteTime.join, ConcreteTime.joinChainCutMe, ConcreteTime.chainRank?]
            | next_le_cutYou j =>
                change ConcreteTime.join (ConcreteTime.nextIndex j) (ConcreteTime.cutYou j) =
                  ConcreteTime.cutYou j
                simp [ConcreteTime.join, ConcreteTime.joinChain, ConcreteTime.chainRank?]
            | @cutYou_le_next i j hij =>
                change ConcreteTime.join (ConcreteTime.cutYou j) (ConcreteTime.nextIndex i) =
                  ConcreteTime.nextIndex i
                simp [ConcreteTime.join, ConcreteTime.joinChain, ConcreteTime.chainRank?]
                omega
        | trans _hab _hbc ihab ihbc =>
            exact cuttingFlagBoundedSemilattice.le_trans ihab ihbc
      simpa [CuttingPosetPoint.toConcrete] using hflag_sound
  | trans _hab _hbc ihab ihbc =>
      exact cuttingFlagBoundedSemilattice.le_trans ihab ihbc

namespace CuttingPosetPoint

/-- `cutyou_j ≰ cutme_j` in `CuttingPoset`: the other direction of the distinct-branch
fact for same-index `cutme`/`cutyou`, Definition 3.2.1(4) (Remark 3.2.2). Proved via
soundness, since `cutyou_j ⊔ cutme_j = ⊤`. -/
theorem not_cutYou_le_cutMe_same (j : Nat) :
    ¬ Le (flag (CuttingFlag.cutYou j)) (flag (CuttingFlag.cutMe j)) := by
  intro h
  have hle := cuttingPosetPoint_le_sound h
  change ConcreteTime.join (ConcreteTime.cutYou j) (ConcreteTime.cutMe j) =
    ConcreteTime.cutMe j at hle
  have hjoin :
      ConcreteTime.join (ConcreteTime.cutYou j) (ConcreteTime.cutMe j) =
        ConcreteTime.top := by
    rw [ConcreteTime.join_comm, ConcreteTime.cutMe_join_cutYou_same]
  rw [hjoin] at hle
  cases hle

end CuttingPosetPoint

namespace CuttingFlag

/-- `cutyou_j ≰ cutme_j` on cutting-flag atoms, the atom-level form of the
distinct-branch fact for same-index `cutme`/`cutyou`, Definition 3.2.1(4). -/
theorem not_cutYou_le_cutMe_same (j : Nat) :
    ¬ Le (cutYou j) (cutMe j) := by
  intro h
  exact CuttingPosetPoint.not_cutYou_le_cutMe_same j (CuttingPosetPoint.Le.of_flag h)

end CuttingFlag

/-- Definition 3.2.1(1) on the concrete carrier of `CuttingPoset`: `nextindex_j ≤ cutme_j`. -/
theorem cuttingFlag_next_le_cutMe (j : Nat) :
    (ConcreteTime.nextIndex j) ≤ (ConcreteTime.cutMe j) := by
  simpa [CuttingPosetPoint.toConcrete, CuttingFlag.toConcrete, ConcreteTime.ofFlagKind]
    using cuttingPosetPoint_le_sound (CuttingPosetPoint.next_le_cutMe j)

/-- Definition 3.2.1(2) on the concrete carrier of `CuttingPoset`: `nextindex_j ≤ cutyou_j`. -/
theorem cuttingFlag_next_le_cutYou (j : Nat) :
    (ConcreteTime.nextIndex j) ≤ (ConcreteTime.cutYou j) := by
  simpa [CuttingPosetPoint.toConcrete, CuttingFlag.toConcrete, ConcreteTime.ofFlagKind]
    using cuttingPosetPoint_le_sound (CuttingPosetPoint.next_le_cutYou j)

/-- Definition 3.2.1(3) on the concrete carrier of `CuttingPoset`: `cutyou_j ≤ nextindex_i`
when `i < j`. -/
theorem cuttingFlag_cutYou_le_next {i j : Nat} (hij : i < j) :
    (ConcreteTime.cutYou j) ≤ (ConcreteTime.nextIndex i) := by
  simpa [CuttingPosetPoint.toConcrete, CuttingFlag.toConcrete, ConcreteTime.ofFlagKind]
    using cuttingPosetPoint_le_sound (CuttingPosetPoint.cutYou_le_next hij)

/-- Derived Figure 6 arrow on the concrete carrier of `CuttingPoset`: `cutyou_j ≤ cutme_i`
when `i < j`, composing Definition 3.2.1(3) with (1). -/
theorem cuttingFlag_cutYou_le_cutMe_of_lt {i j : Nat} (hij : i < j) :
    (ConcreteTime.cutYou j) ≤ (ConcreteTime.cutMe i) := by
  simpa [CuttingPosetPoint.toConcrete, CuttingFlag.toConcrete, ConcreteTime.ofFlagKind]
    using cuttingPosetPoint_le_sound (CuttingPosetPoint.cutYou_le_cutMe_of_lt hij)

/-- Definition 3.2.1(4): the same-index flags `cutme_j` and `cutyou_j` contradict, i.e.
`cutme_j ⊔ cutyou_j = ⊤`. This is the characteristic cross-controller contradiction axiom
(Remark 7.8). -/
theorem cuttingFlag_cutMe_contradicts_cutYou (j : Nat) :
    cuttingFlagBoundedSemilattice.Contradicts
      (ConcreteTime.cutMe j) (ConcreteTime.cutYou j) := by
  change ConcreteTime.join (ConcreteTime.cutMe j) (ConcreteTime.cutYou j) =
    ConcreteTime.top
  simp [ConcreteTime.join, ConcreteTime.joinChainCutMe, ConcreteTime.chainRank?]

/-- Definition 3.2.1(4) as a distinct-branch statement (Remark 3.2.2): the same-index
flags `cutme_j` and `cutyou_j` are incomparable in `CuttingPoset` (neither `≤` the
other), since their join is `⊤`. -/
theorem cuttingFlag_cutMe_cutYou_incomparable (j : Nat) :
    cuttingFlagBoundedSemilattice.Incomparable
      (ConcreteTime.cutMe j) (ConcreteTime.cutYou j) := by
  constructor
  · intro hle
    change ConcreteTime.join (ConcreteTime.cutMe j) (ConcreteTime.cutYou j) =
      ConcreteTime.cutYou j at hle
    rw [ConcreteTime.cutMe_join_cutYou_same] at hle
    cases hle
  · intro hle
    change ConcreteTime.join (ConcreteTime.cutYou j) (ConcreteTime.cutMe j) =
      ConcreteTime.cutMe j at hle
    have hjoin :
        ConcreteTime.join (ConcreteTime.cutYou j) (ConcreteTime.cutMe j) =
          ConcreteTime.top := by
      rw [ConcreteTime.join_comm, ConcreteTime.cutMe_join_cutYou_same]
    rw [hjoin] at hle
    cases hle

end ContForm.AlternativePresentation
