import ContForm.Basic

/-!
Paper section 2.1: Top-trees (sequential bounded semilattices).

-/

/--
Shared abstraction over the paper's contradiction relation. Both bounded
semilattices and located semilattices provide an instance (keyed on the element
type), so the lightning-bolt notation is defined once over this class and
resolves by the operand type rather than being overloaded per structure.
-/
class Contradictory.{w} (α : Type w) where
  contradicts : α → α → Prop

/-- The contradiction relation of Definition 2.1.4, written `a 🗲 b`; resolves to
the `Contradictory` instance for the element type. -/
notation:50 a:51 " 🗲 " b:51 => Contradictory.contradicts a b

namespace ContForm.Foundation.LocatedSemilattices.TopTrees

universe u

/--
Definition 2.1.1.

A bounded semilattice is a typeclass on the carrier type `α`: `join` is the
paper's operation `∨`, with a bottom and top. The derived order is defined below,
because the paper defines `t <= t'` by `t ∨ t' = t'`.
-/
class BoundedSemilattice (α : Type u) where
  join : α → α → α
  bot : α
  top : α
  join_idem : ∀ t : α, join t t = t
  join_comm : ∀ t t' : α, join t t' = join t' t
  join_assoc : ∀ t t' u : α, join (join t t') u = join t (join t' u)
  bot_le : ∀ t : α, join bot t = t
  le_top : ∀ t : α, join t top = top

namespace BoundedSemilattice

variable {α : Type u} [BoundedSemilattice α]

/-- Definition 2.1.1: `t <= t'` means `t ∨ t' = t'`. -/
def le (t t' : α) : Prop :=
  join t t' = t'

/-- Definition 2.1.1: `t < t'` holds when `t ≤ t'` and `t ≠ t'`. -/
def lt (t t' : α) : Prop :=
  le t t' ∧ t ≠ t'

/-!
Notation making formulas resemble the paper: `t ≤ t'` is the order `le`,
`t < t'` is `lt`, `t ⊔ s` is the paper's join `∨` (`join`), and `⊥`/`⊤` are
`bot`/`top`. These resolve from the element type via the `BoundedSemilattice`
instance, available wherever this module is imported.
-/
instance : LE α := ⟨le⟩
instance : LT α := ⟨lt⟩
notation:65 lhs:66 " ⊔ " rhs:66 => BoundedSemilattice.join lhs rhs
notation "⊥" => BoundedSemilattice.bot
notation "⊤" => BoundedSemilattice.top

/-- Definition 2.1.1(2): `t` and `t'` are incomparable when neither `t ≤ t'` nor
`t' ≤ t`. -/
def Incomparable (t t' : α) : Prop :=
  ¬ le t t' ∧ ¬ le t' t

/-- Definition 2.1.1(3): the semilattice is sequential when every join `t ⊔ t'`
is `t`, `t'`, or `⊤`. -/
def Sequential : Prop :=
  ∀ t t' : α, t ⊔ t' = t ∨ t ⊔ t' = t' ∨ t ⊔ t' = top

/-- Definition 2.1.1(4): an element is consistent when it is not `⊤`. -/
def Consistent (t : α) : Prop :=
  t ≠ top

/-- Remark 2.1.3: `top` is not consistent. -/
theorem not_consistent_top : ¬ Consistent (top : α) := by
  intro h
  exact h rfl

/-- Definition 2.1.1(5): a top-tree is a sequential bounded semilattice. -/
def IsTopTree : Prop :=
  Sequential (α := α)

/--
The tree condition of Lemma 2.1.2(3), read order-theoretically: with `⊤`
removed, `⊥` lies below every element, and any two non-top elements below a
common non-top upper bound are comparable — so each element's downset is
linearly ordered.
-/
def TopDeletedOrderTree : Prop :=
  (∀ t : α, t ≠ top → le bot t) ∧
    ∀ {u t t' : α}, u ≠ top → t ≠ top → t' ≠ top →
      le t u → le t' u → le t t' ∨ le t' t

theorem le_refl (t : α) : t ≤ t :=
  join_idem t

theorem le_antisymm
    {t t' : α}
    (htt' : t ≤ t') (ht't : t' ≤ t) : t = t' := by
  have htt' : t ⊔ t' = t' := htt'
  have ht't : t' ⊔ t = t := ht't
  calc
    t = t' ⊔ t := ht't.symm
    _ = t ⊔ t' := join_comm t' t
    _ = t' := htt'

theorem le_trans
    {t t' u : α}
    (htt' : t ≤ t') (ht'u : t' ≤ u) : t ≤ u := by
  have htt' : t ⊔ t' = t' := htt'
  have ht'u : t' ⊔ u = u := ht'u
  show t ⊔ u = u
  calc
    t ⊔ u = t ⊔ (t' ⊔ u) := by rw [ht'u]
    _ = (t ⊔ t') ⊔ u := (join_assoc t t' u).symm
    _ = t' ⊔ u := by rw [htt']
    _ = u := ht'u

theorem bot_le' (t : α) : ⊥ ≤ t :=
  bot_le t

theorem le_top' (t : α) : t ≤ ⊤ :=
  le_top t

/-- Definition 2.1.1: bottom is least for the derived order. -/
theorem le_bot_iff_eq_bot (t : α) :
    t ≤ bot ↔ t = bot := by
  constructor
  · intro h
    exact le_antisymm h (bot_le' t)
  · intro h
    rw [h]
    exact le_refl bot

/-- Definition 2.1.1: top is greatest for the derived order. -/
theorem top_le_iff_eq_top (t : α) :
    top ≤ t ↔ t = top := by
  constructor
  · intro h
    exact (le_antisymm h (le_top' t)).symm
  · intro h
    rw [h]
    exact le_refl top

/-- Definition 2.1.1: being strictly above bottom is the same as not being bottom. -/
theorem bot_lt_iff_ne_bot (t : α) :
    bot < t ↔ t ≠ bot := by
  constructor
  · intro hlt ht
    exact hlt.2 ht.symm
  · intro ht
    exact ⟨bot_le' t, fun h => ht h.symm⟩

/-- `⊥` is consistent exactly when `⊥ ≠ ⊤`. -/
theorem bot_consistent_iff_bot_ne_top :
    Consistent (bot : α) ↔ (bot : α) ≠ top := by
  rfl

/-- `⊥` is consistent exactly when some element is consistent. -/
theorem bot_consistent_iff_exists_consistent :
    Consistent (bot : α) ↔ ∃ t : α, Consistent t := by
  constructor
  · intro hbot
    exact ⟨bot, hbot⟩
  · intro hex hbot_top
    rcases hex with ⟨t, ht⟩
    have htop_le_t : top ≤ t := by
      rw [← hbot_top]
      exact bot_le' t
    exact ht ((top_le_iff_eq_top t).mp htop_le_t)

/-- Some element is consistent exactly when `⊥ ≠ ⊤`. -/
theorem exists_consistent_iff_bot_ne_top :
    (∃ t : α, Consistent t) ↔ (bot : α) ≠ top := by
  constructor
  · intro hex
    exact bot_consistent_iff_bot_ne_top.mp
      (bot_consistent_iff_exists_consistent.mpr hex)
  · intro hbot_top
    exact ⟨bot, bot_consistent_iff_bot_ne_top.mpr hbot_top⟩

theorem join_eq_left_of_right_le
    {t t' : α} (h : t' ≤ t) : t ⊔ t' = t := by
  calc
    t ⊔ t' = t' ⊔ t := join_comm t t'
    _ = t := h

/-- The left input is below its join. -/
theorem le_join_left (t t' : α) : t ≤ (t ⊔ t') := by
  calc
    t ⊔ (t ⊔ t') = (t ⊔ t) ⊔ t' := (join_assoc t t t').symm
    _ = t ⊔ t' := by rw [join_idem]

/-- The right input is below its join. -/
theorem le_join_right (t t' : α) : t' ≤ (t ⊔ t') := by
  calc
    t' ⊔ (t ⊔ t') = t' ⊔ (t' ⊔ t) := by rw [join_comm t t']
    _ = (t' ⊔ t') ⊔ t := (join_assoc t' t' t).symm
    _ = t' ⊔ t := by rw [join_idem]
    _ = t ⊔ t' := join_comm t' t

/-- A join is below any common upper bound. -/
theorem join_le_of_le
    {t t' u : α}
    (htu : t ≤ u) (ht'u : t' ≤ u) : (t ⊔ t') ≤ u := by
  have htu : t ⊔ u = u := htu
  have ht'u : t' ⊔ u = u := ht'u
  calc
    (t ⊔ t') ⊔ u = t ⊔ (t' ⊔ u) := join_assoc t t' u
    _ = t ⊔ u := by rw [ht'u]
    _ = u := htu

/-- Join is monotone in both inputs. -/
theorem join_le_join
    {t t' u u' : α}
    (htu : t ≤ u) (ht'u' : t' ≤ u') : (t ⊔ t') ≤ (u ⊔ u') :=
  join_le_of_le
    (le_trans htu (le_join_left u u'))
    (le_trans ht'u' (le_join_right u u'))

/--
Lemma 2.1.2, equivalence (1)⟺(2): a bounded semilattice is sequential exactly
when incomparable elements join to `⊤`. The remaining equivalence with the tree
condition (3) is `sequential_iff_topDeletedOrderTree`.
-/
theorem sequential_iff_incomparable_join_top :
    Sequential (α := α) ↔ ∀ t t' : α, Incomparable t t' → t ⊔ t' = top := by
  constructor
  · intro hseq t t' hinc
    rcases hseq t t' with hjoin | hjoin | hjoin
    · have ht't : t' ≤ t := by
        calc
          t' ⊔ t = t ⊔ t' := join_comm t' t
          _ = t := hjoin
      exact False.elim (hinc.2 ht't)
    · have htt' : t ≤ t' := by
        exact hjoin
      exact False.elim (hinc.1 htt')
    · exact hjoin
  · intro hincTop t t'
    by_cases htt' : t ≤ t'
    · exact Or.inr (Or.inl htt')
    · by_cases ht't : t' ≤ t
      · exact Or.inl (join_eq_left_of_right_le ht't)
      · exact Or.inr (Or.inr (hincTop t t' ⟨htt', ht't⟩))

/-- Lemma 2.1.2: in a sequential bounded semilattice, incomparable joins are top. -/
theorem incomparable_join_top_of_sequential
    (hseq : Sequential (α := α))
    {t t' : α} (hinc : Incomparable t t') :
    t ⊔ t' = top := by
  exact (sequential_iff_incomparable_join_top.mp hseq) t t' hinc

/-- Lemma 2.1.2: incomparable joins being top implies sequentiality. -/
theorem sequential_of_incomparable_join_top
    (hincTop : ∀ t t' : α, Incomparable t t' → t ⊔ t' = top) :
    Sequential (α := α) := by
  exact sequential_iff_incomparable_join_top.mpr hincTop

/--
Lemma 2.1.2 consequence: in a sequential bounded semilattice, incomparable
elements have no common upper bound below `top`.
-/
theorem common_upper_eq_top_of_incomparable
    (hseq : Sequential (α := α)) {t t' u : α}
    (hinc : Incomparable t t') (htu : t ≤ u) (ht'u : t' ≤ u) :
    u = top := by
  have hjoin_top : t ⊔ t' = top :=
    (sequential_iff_incomparable_join_top.mp hseq) t t' hinc
  have hjoin_le_u : (t ⊔ t') ≤ u := join_le_of_le htu ht'u
  rw [hjoin_top] at hjoin_le_u
  exact (le_antisymm hjoin_le_u (le_top' u)).symm

/--
Lemma 2.1.2 consequence: a common upper bound of incomparable elements in a
sequential bounded semilattice is inconsistent.
-/
theorem not_consistent_common_upper_of_incomparable
    (hseq : Sequential (α := α)) {t t' u : α}
    (hinc : Incomparable t t') (htu : t ≤ u) (ht'u : t' ≤ u) :
    ¬ Consistent u := by
  intro hu
  exact hu (common_upper_eq_top_of_incomparable hseq hinc htu ht'u)

/--
Lemma 2.1.2 consequence: the down-set below any consistent upper bound in a
sequential bounded semilattice is linearly ordered.
-/
theorem comparable_of_common_consistent_upper
    (hseq : Sequential (α := α)) {t t' u : α}
    (htu : t ≤ u) (ht'u : t' ≤ u) (hu : Consistent u) :
    t ≤ t' ∨ t' ≤ t := by
  rcases hseq t t' with hjoin | hjoin | hjoin
  · exact Or.inr (by
      calc
        t' ⊔ t = t ⊔ t' := join_comm t' t
        _ = t := hjoin)
  · exact Or.inl hjoin
  · have hjoin_le_u : (t ⊔ t') ≤ u := join_le_of_le htu ht'u
    rw [hjoin] at hjoin_le_u
    have htop_eq_u : top = u := le_antisymm hjoin_le_u (le_top' u)
    exact False.elim (hu htop_eq_u.symm)

/--
Order-theoretic tree reading of Lemma 2.1.2: sequentiality is equivalent to the top-deleted
order having `bot` as root and linearly ordered principal downsets.
-/
theorem sequential_iff_topDeletedOrderTree :
    Sequential (α := α) ↔ TopDeletedOrderTree (α := α) := by
  constructor
  · intro hseq
    constructor
    · intro t _htop
      exact bot_le' t
    · intro u t t' hu htop_t htop_t' htu ht'u
      exact comparable_of_common_consistent_upper hseq htu ht'u hu
  · intro htree t t'
    by_cases hjoin_top : t ⊔ t' = top
    · exact Or.inr (Or.inr hjoin_top)
    · have ht_ne_top : t ≠ top := by
        intro ht
        apply hjoin_top
        calc
          t ⊔ t' = top ⊔ t' := by rw [ht]
          _ = t' ⊔ top := join_comm top t'
          _ = top := le_top t'
      have ht'_ne_top : t' ≠ top := by
        intro ht'
        apply hjoin_top
        calc
          t ⊔ t' = t ⊔ top := by rw [ht']
          _ = top := le_top t
      have hcomp : t ≤ t' ∨ t' ≤ t :=
        htree.2 hjoin_top ht_ne_top ht'_ne_top
          (le_join_left t t') (le_join_right t t')
      rcases hcomp with htt' | ht't
      · exact Or.inr (Or.inl htt')
      · exact Or.inl (join_eq_left_of_right_le ht't)

/--
Lemma 2.1.2, explicit order-theoretic tree reading: sequentiality gives the
top-deleted tree predicate.
-/
theorem topDeletedOrderTree_of_sequential
    (hseq : Sequential (α := α)) :
    TopDeletedOrderTree (α := α) := by
  exact sequential_iff_topDeletedOrderTree.mp hseq

/--
Lemma 2.1.2, explicit order-theoretic tree reading: the top-deleted tree
predicate gives sequentiality.
-/
theorem sequential_of_topDeletedOrderTree
    (htree : TopDeletedOrderTree (α := α)) :
    Sequential (α := α) := by
  exact sequential_iff_topDeletedOrderTree.mpr htree

/-- Definition 2.1.4: `t` contradicts `t'` when `t ⊔ t' = ⊤`. -/
def Contradicts (t t' : α) : Prop :=
  join t t' = top

/-- The bounded-semilattice contradiction relation supplies the `🗲` notation
via the shared `Contradictory` class; `a 🗲 b` is definitionally `Contradicts`. -/
instance (α) [BoundedSemilattice α] : Contradictory α := ⟨Contradicts⟩

/-- Definition 2.1.4: contradiction is exactly join being `top`. -/
theorem contradicts_iff_join_eq_top (t t' : α) :
    t 🗲 t' ↔ t ⊔ t' = top := by
  rfl

/-- Definition 2.1.4: every element contradicts `top`. -/
theorem contradicts_top_right (t : α) :
    t 🗲 (top : α) :=
  le_top t

/-- Definition 2.1.4: `top` contradicts every element. -/
theorem contradicts_top_left (t : α) :
    (top : α) 🗲 t := by
  show Contradicts top t
  rw [Contradicts, join_comm top t]
  exact le_top t

/-- Remark 2.1.3: `top` contradicts itself. -/
theorem top_contradicts_top :
    (top : α) 🗲 top := by
  exact contradicts_top_right top

/-- Definition 2.1.4: contradiction is symmetric. -/
theorem contradicts_comm {t t' : α} :
    t 🗲 t' → t' 🗲 t := by
  intro h
  show Contradicts t' t
  rw [Contradicts, join_comm t' t]
  exact h

/-- Definition 2.1.4: self-contradiction is exactly being `top`. -/
theorem contradicts_self_iff_eq_top (t : α) :
    t 🗲 t ↔ t = top := by
  constructor
  · intro h
    exact (join_idem t).symm.trans h
  · intro h
    rw [h]
    exact contradicts_top_right top

/-- Definition 2.1.4: consistent elements do not contradict themselves. -/
theorem not_contradicts_self_of_consistent
    {t : α} (ht : Consistent t) : ¬ t 🗲 t := by
  intro h
  exact ht ((contradicts_self_iff_eq_top t).mp h)

/--
Definition 2.1.4 consequence: if comparable elements contradict, the upper
element is `top`.
-/
theorem eq_top_of_le_and_contradicts_right
    {t u : α}
    (htu : t ≤ u) (hcontr : t 🗲 u) : u = top :=
  htu.symm.trans hcontr

/--
Definition 2.1.4 consequence: if comparable elements contradict in the swapped
order, the upper element is `top`.
-/
theorem eq_top_of_le_and_contradicts_left
    {t u : α}
    (htu : t ≤ u) (hcontr : u 🗲 t) : u = top := by
  exact eq_top_of_le_and_contradicts_right htu (contradicts_comm hcontr)

/--
Definition 2.1.4 consequence: a consistent upper bound cannot contradict a lower
element.
-/
theorem not_contradicts_right_of_le_of_consistent
    {t u : α}
    (htu : t ≤ u) (hu : Consistent u) : ¬ t 🗲 u := by
  intro hcontr
  exact hu (eq_top_of_le_and_contradicts_right htu hcontr)

/--
Definition 2.1.4 consequence: a consistent upper bound cannot contradict a lower
element when contradiction is written in the swapped order.
-/
theorem not_contradicts_left_of_le_of_consistent
    {t u : α}
    (htu : t ≤ u) (hu : Consistent u) : ¬ u 🗲 t := by
  intro hcontr
  exact hu (eq_top_of_le_and_contradicts_left htu hcontr)

/-- Lemma 2.1.5 (monotonicity of contradiction): if `t ≤ u`, `t' ≤ u'`, and
`t 🗲 t'`, then `u 🗲 u'`. -/
theorem contradiction_monotone
    {t t' u u' : α}
    (htu : t ≤ u) (ht'u' : t' ≤ u')
    (htt' : t 🗲 t') : u 🗲 u' := by
  have hjoin_le : (t ⊔ t') ≤ (u ⊔ u') :=
    join_le_join htu ht'u'
  rw [htt'] at hjoin_le
  exact (le_antisymm hjoin_le (le_top' (u ⊔ u'))).symm

/-- Lemma 2.1.5: contradiction is monotone in the left input. -/
theorem contradiction_monotone_left
    {t t' u : α}
    (htu : t ≤ u) (htt' : t 🗲 t') :
    u 🗲 t' := by
  exact contradiction_monotone htu (le_refl t') htt'

/-- Lemma 2.1.5: contradiction is monotone in the right input. -/
theorem contradiction_monotone_right
    {t t' u' : α}
    (ht'u' : t' ≤ u') (htt' : t 🗲 t') :
    t 🗲 u' := by
  exact contradiction_monotone (le_refl t) ht'u' htt'

end BoundedSemilattice

/-!
Order-level top-tree builder.

This is support infrastructure for later model construction. It is not a new
paper definition: it packages the inverse direction that the paper uses
informally when a tree-shaped order is intended to carry the join operation.
-/

/--
Specification of a top-tree order from which the join can be reconstructed as
the least common upper bound inside a linearly ordered non-top downset, and as
`top` for elements on different branches.
-/
structure OrderTopTreeSpec where
  Carrier : Type u
  le : Carrier → Carrier → Prop
  bot : Carrier
  top : Carrier
  le_refl : ∀ t : Carrier, le t t
  le_antisymm : ∀ {t t' : Carrier}, le t t' → le t' t → t = t'
  le_trans : ∀ {t t' u : Carrier}, le t t' → le t' u → le t u
  bot_le : ∀ t : Carrier, le bot t
  le_top : ∀ t : Carrier, le t top
  comparable_of_common_consistent_upper :
    ∀ {u t t' : Carrier}, u ≠ top → le t u → le t' u → le t t' ∨ le t' t

namespace OrderTopTreeSpec

instance : CoeSort OrderTopTreeSpec (Type u) where
  coe S := S.Carrier

/-- Join reconstructed from the order: choose the upper comparable element, or `top`. -/
noncomputable def join (S : OrderTopTreeSpec) (t t' : S) : S := by
  classical
  exact if S.le t t' then t' else if S.le t' t then t else S.top

theorem join_eq_right_of_le (S : OrderTopTreeSpec) {t t' : S}
    (htt' : S.le t t') :
    S.join t t' = t' := by
  classical
  simp [join, htt']

theorem join_eq_left_of_le (S : OrderTopTreeSpec) {t t' : S}
    (ht't : S.le t' t) :
    S.join t t' = t := by
  classical
  by_cases htt' : S.le t t'
  · have heq : t = t' := S.le_antisymm htt' ht't
    rw [S.join_eq_right_of_le htt']
    exact heq.symm
  · simp [join, htt', ht't]

theorem le_join_left (S : OrderTopTreeSpec) (t t' : S) :
    S.le t (S.join t t') := by
  classical
  unfold join
  by_cases htt' : S.le t t'
  · simp [htt']
  · by_cases ht't : S.le t' t
    · simpa [htt', ht't] using S.le_refl t
    · simpa [htt', ht't] using S.le_top t

theorem le_join_right (S : OrderTopTreeSpec) (t t' : S) :
    S.le t' (S.join t t') := by
  classical
  unfold join
  by_cases htt' : S.le t t'
  · simpa [htt'] using S.le_refl t'
  · by_cases ht't : S.le t' t
    · simp [htt', ht't]
    · simpa [htt', ht't] using S.le_top t'

theorem join_le_of_le (S : OrderTopTreeSpec) {t t' u : S}
    (htu : S.le t u) (ht'u : S.le t' u) :
    S.le (S.join t t') u := by
  classical
  unfold join
  by_cases htt' : S.le t t'
  · simpa [htt'] using ht'u
  · by_cases ht't : S.le t' t
    · simpa [htt', ht't] using htu
    · by_cases hu : u = S.top
      · subst u
        simpa [htt', ht't] using S.le_refl S.top
      · rcases S.comparable_of_common_consistent_upper hu htu ht'u with hcomp | hcomp
        · exact False.elim (htt' hcomp)
        · exact False.elim (ht't hcomp)

theorem join_le_join (S : OrderTopTreeSpec) {t t' u u' : S}
    (htu : S.le t u) (ht'u' : S.le t' u') :
    S.le (S.join t t') (S.join u u') := by
  exact S.join_le_of_le
    (S.le_trans htu (S.le_join_left u u'))
    (S.le_trans ht'u' (S.le_join_right u u'))

theorem join_idem (S : OrderTopTreeSpec) (t : S) :
    S.join t t = t := by
  exact S.join_eq_right_of_le (S.le_refl t)

theorem join_comm (S : OrderTopTreeSpec) (t t' : S) :
    S.join t t' = S.join t' t := by
  apply S.le_antisymm
  · exact S.join_le_of_le (S.le_join_right t' t) (S.le_join_left t' t)
  · exact S.join_le_of_le (S.le_join_right t t') (S.le_join_left t t')

theorem join_assoc (S : OrderTopTreeSpec) (t t' u : S) :
    S.join (S.join t t') u = S.join t (S.join t' u) := by
  apply S.le_antisymm
  · apply S.join_le_of_le
    · apply S.join_le_of_le
      · exact S.le_join_left t (S.join t' u)
      · exact S.le_trans (S.le_join_left t' u)
          (S.le_join_right t (S.join t' u))
    · exact S.le_trans (S.le_join_right t' u)
        (S.le_join_right t (S.join t' u))
  · apply S.join_le_of_le
    · exact S.le_trans (S.le_join_left t t')
        (S.le_join_left (S.join t t') u)
    · apply S.join_le_of_le
      · exact S.le_trans (S.le_join_right t t')
          (S.le_join_left (S.join t t') u)
      · exact S.le_join_right (S.join t t') u

theorem join_bot_left (S : OrderTopTreeSpec) (t : S) :
    S.join S.bot t = t := by
  exact S.join_eq_right_of_le (S.bot_le t)

theorem join_top_right (S : OrderTopTreeSpec) (t : S) :
    S.join t S.top = S.top := by
  exact S.join_eq_right_of_le (S.le_top t)

/-- The bounded semilattice reconstructed from an order-level top-tree. -/
noncomputable def toBoundedSemilattice (S : OrderTopTreeSpec) :
    BoundedSemilattice S.Carrier where
  join := S.join
  bot := S.bot
  top := S.top
  join_idem := S.join_idem
  join_comm := S.join_comm
  join_assoc := S.join_assoc
  bot_le := S.join_bot_left
  le_top := S.join_top_right

theorem toBoundedSemilattice_le_iff (S : OrderTopTreeSpec) {t t' : S} :
    @BoundedSemilattice.le S.Carrier S.toBoundedSemilattice t t' ↔ S.le t t' := by
  constructor
  · intro h
    change S.join t t' = t' at h
    rw [← h]
    exact S.le_join_left t t'
  · intro h
    change S.join t t' = t'
    exact S.join_eq_right_of_le h

theorem toBoundedSemilattice_sequential (S : OrderTopTreeSpec) :
    @BoundedSemilattice.Sequential S.Carrier S.toBoundedSemilattice := by
  intro t t'
  classical
  change S.join t t' = t ∨ S.join t t' = t' ∨ S.join t t' = S.top
  unfold join
  by_cases htt' : S.le t t'
  · exact Or.inr (Or.inl (by simp [htt']))
  · by_cases ht't : S.le t' t
    · exact Or.inl (by simp [htt', ht't])
    · exact Or.inr (Or.inr (by simp [htt', ht't]))

theorem toBoundedSemilattice_topDeletedOrderTree (S : OrderTopTreeSpec) :
    @BoundedSemilattice.TopDeletedOrderTree S.Carrier S.toBoundedSemilattice := by
  exact
    (@BoundedSemilattice.sequential_iff_topDeletedOrderTree S.Carrier
      S.toBoundedSemilattice).mp
      S.toBoundedSemilattice_sequential

end OrderTopTreeSpec


namespace ConcreteTopTreeExample

/-- Example 2.1.6, carrier. -/
inductive Point where
  | bot
  | a
  | b
  | c
  | d
  | top
  deriving DecidableEq

namespace Point

/-- Example 2.1.6, join table. -/
def join : Point → Point → Point
  | bot, x => x
  | x, bot => x
  | top, _ => top
  | _, top => top
  | a, a => a
  | a, b => b
  | b, a => b
  | a, c => c
  | c, a => c
  | a, d => top
  | d, a => top
  | b, b => b
  | c, c => c
  | d, d => d
  | b, c => top
  | c, b => top
  | b, d => top
  | d, b => top
  | c, d => top
  | d, c => top

theorem join_idem (x : Point) : join x x = x := by
  cases x <;> rfl

theorem join_comm (x y : Point) : join x y = join y x := by
  cases x <;> cases y <;> rfl

theorem join_assoc (x y z : Point) : join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem join_bot_left (x : Point) : join bot x = x := by
  cases x <;> rfl

theorem join_top_right (x : Point) : join x top = top := by
  cases x <;> rfl

end Point

/-- Example 2.1.6, as a bounded semilattice. -/
instance semilattice : BoundedSemilattice Point where
  join := Point.join
  bot := Point.bot
  top := Point.top
  join_idem := Point.join_idem
  join_comm := Point.join_comm
  join_assoc := Point.join_assoc
  bot_le := Point.join_bot_left
  le_top := Point.join_top_right

/-- Example 2.1.6: the example is a top-tree. -/
theorem isTopTree : BoundedSemilattice.IsTopTree (α := Point) := by
  intro x y
  cases x <;> cases y <;> simp [semilattice, Point.join]

theorem join_a_b : Point.a ⊔ Point.b = Point.b := rfl

theorem join_a_c : Point.a ⊔ Point.c = Point.c := rfl

theorem join_bot (x : Point) : (⊥ : Point) ⊔ x = x :=
  Point.join_bot_left x

theorem join_b_c : Point.b ⊔ Point.c = (⊤ : Point) := rfl

theorem join_b_d : Point.b ⊔ Point.d = (⊤ : Point) := rfl

theorem join_c_d : Point.c ⊔ Point.d = (⊤ : Point) := rfl

theorem join_top (x : Point) : x ⊔ (⊤ : Point) = (⊤ : Point) :=
  Point.join_top_right x

/-- Example 2.1.6: `bot < a` in the worked top-tree example. -/
theorem bot_lt_a : Point.bot < Point.a := by
  constructor
  · rfl
  · intro h
    cases h

/-- Example 2.1.6: `a < b` in the worked top-tree example. -/
theorem a_lt_b : Point.a < Point.b := by
  constructor
  · rfl
  · intro h
    cases h

/-- Example 2.1.6: `a < c` in the worked top-tree example. -/
theorem a_lt_c : Point.a < Point.c := by
  constructor
  · rfl
  · intro h
    cases h

/-- Example 2.1.6: `bot < d` in the worked top-tree example. -/
theorem bot_lt_d : Point.bot < Point.d := by
  constructor
  · rfl
  · intro h
    cases h

/-- Example 2.1.6: `b < top` in the worked top-tree example. -/
theorem b_lt_top : Point.b < Point.top := by
  constructor
  · rfl
  · intro h
    cases h

/-- Example 2.1.6: `c < top` in the worked top-tree example. -/
theorem c_lt_top : Point.c < Point.top := by
  constructor
  · rfl
  · intro h
    cases h

/-- Example 2.1.6: `d < top` in the worked top-tree example. -/
theorem d_lt_top : Point.d < Point.top := by
  constructor
  · rfl
  · intro h
    cases h

/-- Example 2.1.6: `bot` is consistent in the concrete worked example. -/
theorem bot_consistent : BoundedSemilattice.Consistent Point.bot := by
  intro h
  cases h

/-- Example 2.1.6: `a` is consistent in the concrete worked example. -/
theorem a_consistent : BoundedSemilattice.Consistent Point.a := by
  intro h
  cases h

/-- Example 2.1.6: `b` is consistent in the concrete worked example. -/
theorem b_consistent : BoundedSemilattice.Consistent Point.b := by
  intro h
  cases h

/-- Example 2.1.6: `c` is consistent in the concrete worked example. -/
theorem c_consistent : BoundedSemilattice.Consistent Point.c := by
  intro h
  cases h

/-- Example 2.1.6: `d` is consistent in the concrete worked example. -/
theorem d_consistent : BoundedSemilattice.Consistent Point.d := by
  intro h
  cases h

/-- Example 2.1.6: `b` and `c` are incomparable continuations of `a`. -/
theorem b_incomparable_c : BoundedSemilattice.Incomparable Point.b Point.c := by
  constructor
  · intro h
    cases h
  · intro h
    cases h

/-- Example 2.1.6: `b` and `d` lie on different branches. -/
theorem b_incomparable_d : BoundedSemilattice.Incomparable Point.b Point.d := by
  constructor
  · intro h
    cases h
  · intro h
    cases h

/-- Example 2.1.6: `c` and `d` lie on different branches. -/
theorem c_incomparable_d : BoundedSemilattice.Incomparable Point.c Point.d := by
  constructor
  · intro h
    cases h
  · intro h
    cases h

theorem b_contradicts_c : Point.b 🗲 Point.c := rfl

theorem b_contradicts_d : Point.b 🗲 Point.d := rfl

theorem not_a_contradicts_b : ¬ Point.a 🗲 Point.b := by
  intro h
  cases h

end ConcreteTopTreeExample


namespace BoundedSemilattice

variable {α : Type u} [BoundedSemilattice α]

/-- Lemma 2.1.7: consistent times are incomparable iff they contradict. -/
theorem incomparable_iff_contradicts_of_consistent
    (hseq : Sequential (α := α)) {t t' : α}
    (ht : Consistent t) (ht' : Consistent t') :
    Incomparable t t' ↔ t 🗲 t' := by
  constructor
  · intro hinc
    exact (sequential_iff_incomparable_join_top.mp hseq) t t' hinc
  · intro hcontr
    constructor
    · intro htt'
      exact ht' (htt'.symm.trans hcontr)
    · intro ht't
      exact ht ((join_eq_left_of_right_le ht't).symm.trans hcontr)

/--
Lemma 2.1.7, forward direction: consistent incomparable times contradict.
-/
theorem contradicts_of_incomparable_of_consistent
    (hseq : Sequential (α := α)) {t t' : α}
    (ht : Consistent t) (ht' : Consistent t')
    (hinc : Incomparable t t') : t 🗲 t' := by
  exact (incomparable_iff_contradicts_of_consistent hseq ht ht').mp hinc

/--
Lemma 2.1.7, reverse direction: consistent contradictory times are
incomparable.
-/
theorem incomparable_of_contradicts_of_consistent
    (hseq : Sequential (α := α)) {t t' : α}
    (ht : Consistent t) (ht' : Consistent t')
    (hcontr : t 🗲 t') : Incomparable t t' := by
  exact (incomparable_iff_contradicts_of_consistent hseq ht ht').mpr hcontr

end BoundedSemilattice

end ContForm.Foundation.LocatedSemilattices.TopTrees
