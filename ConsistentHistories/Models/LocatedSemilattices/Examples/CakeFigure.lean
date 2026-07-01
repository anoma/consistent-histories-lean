import ConsistentHistories.Foundation.LocatedSemilattices.Basic

namespace ConsistentHistories.Models.LocatedSemilattices.Examples

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.LocatedSemilattices.TopTrees

universe u v

/--
If the figure order gives `b ≼ b'` while `b` contradicts `b'`, then `b'` cannot be a
consistent non-top node.
-/
theorem cake_comparable_contradictory_nonterminal_branch_impossible
    {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl] {b b' : Time}
    (hle : b ≼ b') (hcontr : b 🗲 b')
    (hconsistent : ConsistentTime b') : False := by
  exact not_contradicts_right_of_le_of_consistentTime hle hconsistent hcontr

/-- Example 2.3.4: the three controllers `Ctrl = {1, 2, 3}`. -/
inductive CakeFigureCtrl where
  | one
  | two
  | three
  deriving DecidableEq

/-- Example 2.3.4: the eight named non-top nodes `a, b, c, d, e, f, g, h` of Figure 5. -/
inductive CakeFigureNode where
  | a
  | b
  | c
  | d
  | e
  | f
  | g
  | h
  deriving DecidableEq

namespace CakeFigureNode

/-- Example 2.3.4: controller assignment for the named cake figure nodes. -/
def controller : CakeFigureNode → CakeFigureCtrl
  | a => CakeFigureCtrl.one
  | d => CakeFigureCtrl.one
  | e => CakeFigureCtrl.one
  | h => CakeFigureCtrl.one
  | b => CakeFigureCtrl.two
  | c => CakeFigureCtrl.two
  | f => CakeFigureCtrl.two
  | g => CakeFigureCtrl.three

theorem controller_a : controller a = CakeFigureCtrl.one := rfl
theorem controller_b : controller b = CakeFigureCtrl.two := rfl
theorem controller_c : controller c = CakeFigureCtrl.two := rfl
theorem controller_d : controller d = CakeFigureCtrl.one := rfl
theorem controller_e : controller e = CakeFigureCtrl.one := rfl
theorem controller_f : controller f = CakeFigureCtrl.two := rfl
theorem controller_g : controller g = CakeFigureCtrl.three := rfl
theorem controller_h : controller h = CakeFigureCtrl.one := rfl

/-- Example 2.3.4: the Controller 1 nodes are exactly `a`, `d`, `e`, and `h`. -/
theorem controller_eq_one_iff (node : CakeFigureNode) :
    controller node = CakeFigureCtrl.one ↔
      node = a ∨ node = d ∨ node = e ∨ node = h := by
  cases node <;> simp [controller]

/-- Example 2.3.4: the Controller 2 nodes are exactly `b`, `c`, and `f`. -/
theorem controller_eq_two_iff (node : CakeFigureNode) :
    controller node = CakeFigureCtrl.two ↔ node = b ∨ node = c ∨ node = f := by
  cases node <;> simp [controller]

/-- Example 2.3.4: `g` is the only named Controller 3 node in the figure. -/
theorem controller_eq_three_iff (node : CakeFigureNode) :
    controller node = CakeFigureCtrl.three ↔ node = g := by
  cases node <;> simp [controller]

/-- Example 2.3.4: the named same-controller order edges of Figure 5. -/
inductive TopEdge : CakeFigureNode → CakeFigureNode → Prop where
  | a_to_d : TopEdge a d
  | d_to_e : TopEdge d e
  | e_to_h : TopEdge e h
  | b_to_c : TopEdge b c
  | b_to_f : TopEdge b f

/-- Example 2.3.4: exact characterization of the named same-controller order edges. -/
theorem topEdge_iff (source target : CakeFigureNode) :
    TopEdge source target ↔
      (source = a ∧ target = d) ∨
      (source = d ∧ target = e) ∨
      (source = e ∧ target = h) ∨
      (source = b ∧ target = c) ∨
      (source = b ∧ target = f) := by
  constructor
  · intro h
    cases h <;> simp
  · intro h
    rcases h with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact TopEdge.a_to_d
    · exact TopEdge.d_to_e
    · exact TopEdge.e_to_h
    · exact TopEdge.b_to_c
    · exact TopEdge.b_to_f

/-- Example 2.3.4: the named order edges stay within one controller. -/
theorem topEdge_same_controller {source target : CakeFigureNode}
    (h : TopEdge source target) : controller source = controller target := by
  cases h <;> rfl

/-- Example 2.3.4: the transitive closure of the named order edges. -/
inductive TopPrecedes : CakeFigureNode → CakeFigureNode → Prop where
  | edge {source target : CakeFigureNode} : TopEdge source target → TopPrecedes source target
  | trans {source middle target : CakeFigureNode} :
      TopPrecedes source middle → TopPrecedes middle target → TopPrecedes source target

/-- Example 2.3.4: the transitive named order stays within one controller. -/
theorem topPrecedes_same_controller {source target : CakeFigureNode}
    (h : TopPrecedes source target) : controller source = controller target := by
  induction h with
  | edge h => exact topEdge_same_controller h
  | trans _ _ hsource_middle hmiddle_target =>
      exact hsource_middle.trans hmiddle_target

/-- Example 2.3.4: Controller 1 has `a` before `d`. -/
theorem topPrecedes_a_d : TopPrecedes a d := by
  exact TopPrecedes.edge TopEdge.a_to_d

/-- Example 2.3.4: Controller 1 has `d` before `e`. -/
theorem topPrecedes_d_e : TopPrecedes d e := by
  exact TopPrecedes.edge TopEdge.d_to_e

/-- Example 2.3.4: Controller 1 has `e` before `h`. -/
theorem topPrecedes_e_h : TopPrecedes e h := by
  exact TopPrecedes.edge TopEdge.e_to_h

/-- Example 2.3.4: Controller 1 has `a` before `h`. -/
theorem topPrecedes_a_h : TopPrecedes a h := by
  exact TopPrecedes.trans topPrecedes_a_d
    (TopPrecedes.trans topPrecedes_d_e topPrecedes_e_h)

/-- Example 2.3.4: Controller 2 has `b` before `c`. -/
theorem topPrecedes_b_c : TopPrecedes b c := by
  exact TopPrecedes.edge TopEdge.b_to_c

/-- Example 2.3.4: Controller 2 has `b` before `f`. -/
theorem topPrecedes_b_f : TopPrecedes b f := by
  exact TopPrecedes.edge TopEdge.b_to_f

/-- Example 2.3.4: the dashed attestation arcs of Figure 5. -/
inductive AttestationArc : CakeFigureNode → CakeFigureNode → Prop where
  | a_to_b : AttestationArc a b
  | c_to_d : AttestationArc c d
  | f_to_g : AttestationArc f g
  | g_to_h : AttestationArc g h

/-- Example 2.3.4: exact characterization of the dashed attestation arcs. -/
theorem attestationArc_iff (source target : CakeFigureNode) :
    AttestationArc source target ↔
      (source = a ∧ target = b) ∨
      (source = c ∧ target = d) ∨
      (source = f ∧ target = g) ∨
      (source = g ∧ target = h) := by
  constructor
  · intro h
    cases h <;> simp
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact AttestationArc.a_to_b
    · exact AttestationArc.c_to_d
    · exact AttestationArc.f_to_g
    · exact AttestationArc.g_to_h

/-- Example 2.3.4: the only dashed arc into Controller 1's node `d` comes from the upper
fork endpoint `c`. -/
theorem attestationArc_to_d_iff (source : CakeFigureNode) :
    AttestationArc source d ↔ source = c := by
  cases source <;> simp [attestationArc_iff]

/-- Example 2.3.4: the only dashed arc into Controller 1's node `h` comes from Controller
3's node `g`. -/
theorem attestationArc_to_h_iff (source : CakeFigureNode) :
    AttestationArc source h ↔ source = g := by
  cases source <;> simp [attestationArc_iff]

/-- Example 2.3.4: no dashed arc leaves the pre-fork Controller 2 node `b`. -/
theorem not_attestationArc_from_b (target : CakeFigureNode) :
    ¬ AttestationArc b target := by
  intro h
  cases h

/-- Example 2.3.4: transitive dependency along the dashed attestation arcs. -/
inductive AttestationDepends : CakeFigureNode → CakeFigureNode → Prop where
  | arc {source target : CakeFigureNode} :
      AttestationArc source target → AttestationDepends source target
  | trans {source middle target : CakeFigureNode} :
      AttestationDepends source middle →
      AttestationDepends middle target →
      AttestationDepends source target

/-- Example 2.3.4: `b` depends on `a` — Controller 2 attests to Controller 1's state `a`. -/
theorem attestationDepends_a_b : AttestationDepends a b := by
  exact AttestationDepends.arc AttestationArc.a_to_b

/-- Example 2.3.4: `d` depends on `c` — Controller 1 attests to the upper fork endpoint. -/
theorem attestationDepends_c_d : AttestationDepends c d := by
  exact AttestationDepends.arc AttestationArc.c_to_d

/-- Example 2.3.4: `g` depends on `f` — Controller 3's state absorbs the lower fork
endpoint. -/
theorem attestationDepends_f_g : AttestationDepends f g := by
  exact AttestationDepends.arc AttestationArc.f_to_g

/-- Example 2.3.4: `h` depends on `g` — Controller 1 attests to Controller 3's state `g`. -/
theorem attestationDepends_g_h : AttestationDepends g h := by
  exact AttestationDepends.arc AttestationArc.g_to_h

/-- Example 2.3.4: the transitive lower-branch dependency `f → g → h`, so `h` depends on
`f`. -/
theorem attestationDepends_f_h : AttestationDepends f h := by
  exact AttestationDepends.trans attestationDepends_f_g attestationDepends_g_h

/-- Example 2.3.4: since no dashed arc leaves `b`, no dependency path starts at `b`. -/
theorem not_attestationDepends_from_b (target : CakeFigureNode) :
    ¬ AttestationDepends b target := by
  intro h
  have hsource_ne :
      ∀ {source target : CakeFigureNode},
        AttestationDepends source target → source ≠ b := by
    intro source target hdepends
    induction hdepends with
    | arc hArc =>
        intro hsource
        subst hsource
        exact not_attestationArc_from_b _ hArc
    | trans _ _ hsource _ =>
        exact hsource
  exact hsource_ne h rfl

end CakeFigureNode

/-- Example 2.3.4: Controller 1's local chain `⊥ < a < d < e < h < ⊤`. -/
inductive CakeController1Time where
  | bot
  | a
  | d
  | e
  | h
  | top
  deriving DecidableEq

namespace CakeController1Time

/-- Example 2.3.4: Controller 1's local chain join. -/
def join : CakeController1Time → CakeController1Time → CakeController1Time
  | bot, x => x
  | x, bot => x
  | top, _ => top
  | _, top => top
  | h, _ => h
  | _, h => h
  | e, _ => e
  | _, e => e
  | d, _ => d
  | _, d => d
  | a, a => a

theorem join_idem (x : CakeController1Time) : join x x = x := by
  cases x <;> rfl

theorem join_comm (x y : CakeController1Time) : join x y = join y x := by
  cases x <;> cases y <;> rfl

theorem join_assoc (x y z : CakeController1Time) :
    join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem bot_le (x : CakeController1Time) : join bot x = x := by
  cases x <;> rfl

theorem le_top (x : CakeController1Time) : join x top = top := by
  cases x <;> rfl

end CakeController1Time

/-- Example 2.3.4: Controller 1's local row as a bounded semilattice. -/
instance cakeController1Semilattice : BoundedSemilattice CakeController1Time where
  join := CakeController1Time.join
  bot := CakeController1Time.bot
  top := CakeController1Time.top
  join_idem := CakeController1Time.join_idem
  join_comm := CakeController1Time.join_comm
  join_assoc := CakeController1Time.join_assoc
  bot_le := CakeController1Time.bot_le
  le_top := CakeController1Time.le_top

/-- Example 2.3.4: Controller 1's local chain is sequential. -/
theorem cakeController1Semilattice_sequential :
    cakeController1Semilattice.Sequential := by
  intro x y
  cases x <;> cases y <;> simp [cakeController1Semilattice, CakeController1Time.join]

/-- Example 2.3.4: Controller 1 has `a` before `d`. -/
theorem cakeController1_a_le_d :
    CakeController1Time.a ≤ CakeController1Time.d := by
  rfl

/-- Example 2.3.4: Controller 1 has `d` before `e`. -/
theorem cakeController1_d_le_e :
    CakeController1Time.d ≤ CakeController1Time.e := by
  rfl

/-- Example 2.3.4: Controller 1 has `e` before `h`. -/
theorem cakeController1_e_le_h :
    CakeController1Time.e ≤ CakeController1Time.h := by
  rfl

/-- Example 2.3.4: Controller 1 has `a` before `h`. -/
theorem cakeController1_a_le_h :
    CakeController1Time.a ≤ CakeController1Time.h := by
  rfl

/-- Example 2.3.4: Controller 1 has `d` before `h`. -/
theorem cakeController1_d_le_h :
    CakeController1Time.d ≤ CakeController1Time.h := by
  rfl

/-- Example 2.3.4: Controller 1 has `a` strictly before `d`. -/
theorem cakeController1_a_lt_d :
    CakeController1Time.a < CakeController1Time.d := by
  exact ⟨cakeController1_a_le_d, by intro h; cases h⟩

/-- Example 2.3.4: Controller 1 has `d` strictly before `e`. -/
theorem cakeController1_d_lt_e :
    CakeController1Time.d < CakeController1Time.e := by
  exact ⟨cakeController1_d_le_e, by intro h; cases h⟩

/-- Example 2.3.4: Controller 1 has `e` strictly before `h`. -/
theorem cakeController1_e_lt_h :
    CakeController1Time.e < CakeController1Time.h := by
  exact ⟨cakeController1_e_le_h, by intro h; cases h⟩

/-- Example 2.3.4: Controller 1 has `a` strictly before `h`. -/
theorem cakeController1_a_lt_h :
    CakeController1Time.a < CakeController1Time.h := by
  exact ⟨cakeController1_a_le_h, by intro h; cases h⟩

/-- Example 2.3.4: Controller 1 has `d` strictly before `h`. -/
theorem cakeController1_d_lt_h :
    CakeController1Time.d < CakeController1Time.h := by
  exact ⟨cakeController1_d_le_h, by intro h; cases h⟩

/-- Example 2.3.4: `a` is a non-top Controller 1 time. -/
theorem cakeController1_a_consistent :
    cakeController1Semilattice.Consistent CakeController1Time.a := by
  intro h
  cases h

/-- Example 2.3.4: `d` is a non-top Controller 1 time. -/
theorem cakeController1_d_consistent :
    cakeController1Semilattice.Consistent CakeController1Time.d := by
  intro h
  cases h

/-- Example 2.3.4: `e` is a non-top Controller 1 time. -/
theorem cakeController1_e_consistent :
    cakeController1Semilattice.Consistent CakeController1Time.e := by
  intro h
  cases h

/-- Example 2.3.4: `h` is a non-top Controller 1 time. -/
theorem cakeController1_h_consistent :
    cakeController1Semilattice.Consistent CakeController1Time.h := by
  intro h
  cases h

/-- Example 2.3.4: Controller 1's row is a chain, so it has no incomparable non-top pair. -/
theorem cakeController1Semilattice_total_order
    (x y : CakeController1Time) :
    x ≤ y ∨ y ≤ x := by
  cases x <;> cases y <;>
    simp [BoundedSemilattice.le, LE.le, cakeController1Semilattice, CakeController1Time.join]

/-- Example 2.3.4: any two consistent Controller 1 states are non-contradictory. -/
theorem cakeController1_consistent_pair_not_contradicts
    {x y : CakeController1Time}
    (hx : cakeController1Semilattice.Consistent x)
    (hy : cakeController1Semilattice.Consistent y) :
    ¬ x 🗲 y := by
  rcases cakeController1Semilattice_total_order x y with hxy | hyx
  · exact cakeController1Semilattice.not_contradicts_right_of_le_of_consistent hxy hy
  · exact cakeController1Semilattice.not_contradicts_left_of_le_of_consistent hyx hx

/-- Example 2.3.4: Controller 1's `d` and `h` lie on one chain, so they do not contradict. -/
theorem cakeController1_d_not_contradicts_h :
    ¬ CakeController1Time.d 🗲 CakeController1Time.h := by
  exact cakeController1_consistent_pair_not_contradicts
    cakeController1_d_consistent cakeController1_h_consistent

/-- Example 2.3.4: Controller 2's fork times `⊥, b, c, f, ⊤`. -/
inductive CakeController2Time where
  | bot
  | b
  | c
  | f
  | top
  deriving DecidableEq

namespace CakeController2Time

/-- Example 2.3.4: Controller 2 forks at `b` into incomparable endpoints. -/
def join : CakeController2Time → CakeController2Time → CakeController2Time
  | bot, x => x
  | x, bot => x
  | top, _ => top
  | _, top => top
  | b, b => b
  | b, c => c
  | c, b => c
  | b, f => f
  | f, b => f
  | c, c => c
  | f, f => f
  | c, f => top
  | f, c => top

theorem join_idem (x : CakeController2Time) : join x x = x := by
  cases x <;> rfl

theorem join_comm (x y : CakeController2Time) : join x y = join y x := by
  cases x <;> cases y <;> rfl

theorem join_assoc (x y z : CakeController2Time) :
    join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem bot_le (x : CakeController2Time) : join bot x = x := by
  cases x <;> rfl

theorem le_top (x : CakeController2Time) : join x top = top := by
  cases x <;> rfl

end CakeController2Time

/-- Example 2.3.4: Controller 2's fork body as a bounded semilattice. -/
instance cakeController2Semilattice : BoundedSemilattice CakeController2Time where
  join := CakeController2Time.join
  bot := CakeController2Time.bot
  top := CakeController2Time.top
  join_idem := CakeController2Time.join_idem
  join_comm := CakeController2Time.join_comm
  join_assoc := CakeController2Time.join_assoc
  bot_le := CakeController2Time.bot_le
  le_top := CakeController2Time.le_top

/-- Example 2.3.4: Controller 2's fork semilattice is sequential. -/
theorem cakeController2Semilattice_sequential :
    cakeController2Semilattice.Sequential := by
  intro x y
  cases x <;> cases y <;> simp [cakeController2Semilattice, CakeController2Time.join]

/-- Example 2.3.4: the fork state `b` precedes endpoint `c`. -/
theorem cakeController2_b_le_c :
    CakeController2Time.b ≤ CakeController2Time.c := by
  rfl

/-- Example 2.3.4: the fork state `b` precedes endpoint `f`. -/
theorem cakeController2_b_le_f :
    CakeController2Time.b ≤ CakeController2Time.f := by
  rfl

/-- Example 2.3.4: the upper fork endpoint is strictly after `b`. -/
theorem cakeController2_b_lt_c :
    CakeController2Time.b < CakeController2Time.c := by
  exact ⟨cakeController2_b_le_c, by intro h; cases h⟩

/-- Example 2.3.4: the lower fork endpoint is strictly after `b`. -/
theorem cakeController2_b_lt_f :
    CakeController2Time.b < CakeController2Time.f := by
  exact ⟨cakeController2_b_le_f, by intro h; cases h⟩

/-- Example 2.3.4: the pre-fork state `b` is a non-top Controller 2 time. -/
theorem cakeController2_b_consistent :
    cakeController2Semilattice.Consistent CakeController2Time.b := by
  intro h
  cases h

/-- Example 2.3.4: the upper fork endpoint `c` is a non-top Controller 2 time. -/
theorem cakeController2_c_consistent :
    cakeController2Semilattice.Consistent CakeController2Time.c := by
  intro h
  cases h

/-- Example 2.3.4: the lower fork endpoint `f` is a non-top Controller 2 time. -/
theorem cakeController2_f_consistent :
    cakeController2Semilattice.Consistent CakeController2Time.f := by
  intro h
  cases h

/-- Example 2.3.4: the fork endpoints `c` and `f` join to `⊤`. -/
theorem cakeController2_c_join_f_top :
    CakeController2Time.join CakeController2Time.c CakeController2Time.f =
      CakeController2Time.top := by
  rfl

/-- Example 2.3.4: the fork endpoints `c` and `f` are incomparable. -/
theorem cakeController2_c_incomparable_f :
    cakeController2Semilattice.Incomparable CakeController2Time.c CakeController2Time.f := by
  constructor <;> intro h <;>
    simp [BoundedSemilattice.le, cakeController2Semilattice, CakeController2Time.join] at h

/-- Example 2.3.4: the fork endpoints `c` and `f` contradict. -/
theorem cakeController2_c_contradicts_f :
    CakeController2Time.c 🗲 CakeController2Time.f := by
  rfl

/-- Example 2.3.4: Controller 3's local chain `⊥ < g < ⊤`. -/
inductive CakeController3Time where
  | bot
  | g
  | top
  deriving DecidableEq

namespace CakeController3Time

/-- Example 2.3.4: Controller 3's local chain join. -/
def join : CakeController3Time → CakeController3Time → CakeController3Time
  | bot, x => x
  | x, bot => x
  | top, _ => top
  | _, top => top
  | g, g => g

theorem join_idem (x : CakeController3Time) : join x x = x := by
  cases x <;> rfl

theorem join_comm (x y : CakeController3Time) : join x y = join y x := by
  cases x <;> cases y <;> rfl

theorem join_assoc (x y z : CakeController3Time) :
    join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem bot_le (x : CakeController3Time) : join bot x = x := by
  cases x <;> rfl

theorem le_top (x : CakeController3Time) : join x top = top := by
  cases x <;> rfl

end CakeController3Time

/-- Example 2.3.4: Controller 3's local row as a bounded semilattice. -/
instance cakeController3Semilattice : BoundedSemilattice CakeController3Time where
  join := CakeController3Time.join
  bot := CakeController3Time.bot
  top := CakeController3Time.top
  join_idem := CakeController3Time.join_idem
  join_comm := CakeController3Time.join_comm
  join_assoc := CakeController3Time.join_assoc
  bot_le := CakeController3Time.bot_le
  le_top := CakeController3Time.le_top

/-- Example 2.3.4: Controller 3's local chain is sequential. -/
theorem cakeController3Semilattice_sequential :
    cakeController3Semilattice.Sequential := by
  intro x y
  cases x <;> cases y <;> simp [cakeController3Semilattice, CakeController3Time.join]

/-- Example 2.3.4: Controller 3 has bottom before `g`. -/
theorem cakeController3_bot_le_g :
    CakeController3Time.bot ≤ CakeController3Time.g := by
  rfl

/-- Example 2.3.4: Controller 3 has `g` before top. -/
theorem cakeController3_g_le_top :
    CakeController3Time.g ≤ CakeController3Time.top := by
  rfl

/-- Example 2.3.4: Controller 3 has bottom strictly before `g`. -/
theorem cakeController3_bot_lt_g :
    CakeController3Time.bot < CakeController3Time.g := by
  exact ⟨cakeController3_bot_le_g, by intro h; cases h⟩

/-- Example 2.3.4: Controller 3 has `g` strictly before top. -/
theorem cakeController3_g_lt_top :
    CakeController3Time.g < CakeController3Time.top := by
  exact ⟨cakeController3_g_le_top, by intro h; cases h⟩

/-- Example 2.3.4: `g` is a non-top Controller 3 time. -/
theorem cakeController3_g_consistent :
    cakeController3Semilattice.Consistent CakeController3Time.g := by
  intro h
  cases h

/--
Support model for Figure 5: the controller-local times, with bottom and top for each
controller.
-/
def CakeModelLocalTime : CakeFigureCtrl → Type
  | CakeFigureCtrl.one => CakeController1Time
  | CakeFigureCtrl.two => CakeController2Time
  | CakeFigureCtrl.three => CakeController3Time

def cakeModelLocalBot : (p : CakeFigureCtrl) → CakeModelLocalTime p
  | CakeFigureCtrl.one => CakeController1Time.bot
  | CakeFigureCtrl.two => CakeController2Time.bot
  | CakeFigureCtrl.three => CakeController3Time.bot

def cakeModelLocalTop : (p : CakeFigureCtrl) → CakeModelLocalTime p
  | CakeFigureCtrl.one => CakeController1Time.top
  | CakeFigureCtrl.two => CakeController2Time.top
  | CakeFigureCtrl.three => CakeController3Time.top

abbrev CakeModelTime : Type :=
  Sigma CakeModelLocalTime

def cakeModelBot (p : CakeFigureCtrl) : CakeModelTime :=
  ⟨p, cakeModelLocalBot p⟩

def cakeModelTop (p : CakeFigureCtrl) : CakeModelTime :=
  ⟨p, cakeModelLocalTop p⟩

/--
Support attestation for the cake witness. Same-controller attestation is the local
top-tree join; the four dashed arcs return their target time; every other
cross-controller attestation jumps to the target controller's top.
-/
def cakeModelAttest : CakeModelTime → CakeModelTime → CakeModelTime
  | ⟨CakeFigureCtrl.one, target⟩, ⟨CakeFigureCtrl.one, source⟩ =>
      ⟨CakeFigureCtrl.one, CakeController1Time.join target source⟩
  | ⟨CakeFigureCtrl.two, target⟩, ⟨CakeFigureCtrl.two, source⟩ =>
      ⟨CakeFigureCtrl.two, CakeController2Time.join target source⟩
  | ⟨CakeFigureCtrl.three, target⟩, ⟨CakeFigureCtrl.three, source⟩ =>
      ⟨CakeFigureCtrl.three, CakeController3Time.join target source⟩
  | ⟨CakeFigureCtrl.two, CakeController2Time.b⟩,
      ⟨CakeFigureCtrl.one, CakeController1Time.a⟩ =>
      ⟨CakeFigureCtrl.two, CakeController2Time.b⟩
  | ⟨CakeFigureCtrl.one, CakeController1Time.d⟩,
      ⟨CakeFigureCtrl.two, CakeController2Time.c⟩ =>
      ⟨CakeFigureCtrl.one, CakeController1Time.d⟩
  | ⟨CakeFigureCtrl.three, CakeController3Time.g⟩,
      ⟨CakeFigureCtrl.two, CakeController2Time.f⟩ =>
      ⟨CakeFigureCtrl.three, CakeController3Time.g⟩
  | ⟨CakeFigureCtrl.one, CakeController1Time.h⟩,
      ⟨CakeFigureCtrl.three, CakeController3Time.g⟩ =>
      ⟨CakeFigureCtrl.one, CakeController1Time.h⟩
  | ⟨CakeFigureCtrl.one, _⟩, _ => cakeModelTop CakeFigureCtrl.one
  | ⟨CakeFigureCtrl.two, _⟩, _ => cakeModelTop CakeFigureCtrl.two
  | ⟨CakeFigureCtrl.three, _⟩, _ => cakeModelTop CakeFigureCtrl.three

private theorem cakeModel_contradiction_preserving_one_one
    (x x' y y' : CakeController1Time)
    (hcontr : RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      ⟨CakeFigureCtrl.one, y⟩ ⟨CakeFigureCtrl.one, y'⟩) :
    RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      (cakeModelAttest ⟨CakeFigureCtrl.one, x⟩ ⟨CakeFigureCtrl.one, y⟩)
      (cakeModelAttest ⟨CakeFigureCtrl.one, x'⟩ ⟨CakeFigureCtrl.one, y'⟩) := by
  cases x <;> cases x' <;> cases y <;> cases y' <;>
    simp [RawContradicts, cakeModelAttest, cakeModelTop, cakeModelLocalTop,
      CakeController1Time.join] at hcontr ⊢

private theorem cakeModel_contradiction_preserving_one_two
    (x x' : CakeController1Time) (y y' : CakeController2Time)
    (hcontr : RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      ⟨CakeFigureCtrl.two, y⟩ ⟨CakeFigureCtrl.two, y'⟩) :
    RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      (cakeModelAttest ⟨CakeFigureCtrl.one, x⟩ ⟨CakeFigureCtrl.two, y⟩)
      (cakeModelAttest ⟨CakeFigureCtrl.one, x'⟩ ⟨CakeFigureCtrl.two, y'⟩) := by
  cases x <;> cases x' <;> cases y <;> cases y' <;>
    simp [RawContradicts, cakeModelAttest, cakeModelTop, cakeModelLocalTop,
      CakeController1Time.join, CakeController2Time.join] at hcontr ⊢

private theorem cakeModel_contradiction_preserving_one_three
    (x x' : CakeController1Time) (y y' : CakeController3Time)
    (hcontr : RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      ⟨CakeFigureCtrl.three, y⟩ ⟨CakeFigureCtrl.three, y'⟩) :
    RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      (cakeModelAttest ⟨CakeFigureCtrl.one, x⟩ ⟨CakeFigureCtrl.three, y⟩)
      (cakeModelAttest ⟨CakeFigureCtrl.one, x'⟩ ⟨CakeFigureCtrl.three, y'⟩) := by
  cases x <;> cases x' <;> cases y <;> cases y' <;>
    simp [RawContradicts, cakeModelAttest, cakeModelTop, cakeModelLocalTop,
      CakeController1Time.join, CakeController3Time.join] at hcontr ⊢

private theorem cakeModel_contradiction_preserving_two_one
    (x x' : CakeController2Time) (y y' : CakeController1Time)
    (hcontr : RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      ⟨CakeFigureCtrl.one, y⟩ ⟨CakeFigureCtrl.one, y'⟩) :
    RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      (cakeModelAttest ⟨CakeFigureCtrl.two, x⟩ ⟨CakeFigureCtrl.one, y⟩)
      (cakeModelAttest ⟨CakeFigureCtrl.two, x'⟩ ⟨CakeFigureCtrl.one, y'⟩) := by
  cases x <;> cases x' <;> cases y <;> cases y' <;>
    simp [RawContradicts, cakeModelAttest, cakeModelTop, cakeModelLocalTop,
      CakeController1Time.join, CakeController2Time.join] at hcontr ⊢

private theorem cakeModel_contradiction_preserving_two_two
    (x x' y y' : CakeController2Time)
    (hcontr : RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      ⟨CakeFigureCtrl.two, y⟩ ⟨CakeFigureCtrl.two, y'⟩) :
    RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      (cakeModelAttest ⟨CakeFigureCtrl.two, x⟩ ⟨CakeFigureCtrl.two, y⟩)
      (cakeModelAttest ⟨CakeFigureCtrl.two, x'⟩ ⟨CakeFigureCtrl.two, y'⟩) := by
  cases x <;> cases x' <;> cases y <;> cases y' <;>
    simp [RawContradicts, cakeModelAttest, cakeModelTop, cakeModelLocalTop,
      CakeController2Time.join] at hcontr ⊢

private theorem cakeModel_contradiction_preserving_two_three
    (x x' : CakeController2Time) (y y' : CakeController3Time)
    (hcontr : RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      ⟨CakeFigureCtrl.three, y⟩ ⟨CakeFigureCtrl.three, y'⟩) :
    RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      (cakeModelAttest ⟨CakeFigureCtrl.two, x⟩ ⟨CakeFigureCtrl.three, y⟩)
      (cakeModelAttest ⟨CakeFigureCtrl.two, x'⟩ ⟨CakeFigureCtrl.three, y'⟩) := by
  cases x <;> cases x' <;> cases y <;> cases y' <;>
    simp [RawContradicts, cakeModelAttest, cakeModelTop, cakeModelLocalTop,
      CakeController2Time.join, CakeController3Time.join] at hcontr ⊢

private theorem cakeModel_contradiction_preserving_three_one
    (x x' : CakeController3Time) (y y' : CakeController1Time)
    (hcontr : RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      ⟨CakeFigureCtrl.one, y⟩ ⟨CakeFigureCtrl.one, y'⟩) :
    RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      (cakeModelAttest ⟨CakeFigureCtrl.three, x⟩ ⟨CakeFigureCtrl.one, y⟩)
      (cakeModelAttest ⟨CakeFigureCtrl.three, x'⟩ ⟨CakeFigureCtrl.one, y'⟩) := by
  cases x <;> cases x' <;> cases y <;> cases y' <;>
    simp [RawContradicts, cakeModelAttest, cakeModelTop, cakeModelLocalTop,
      CakeController1Time.join, CakeController3Time.join] at hcontr ⊢

private theorem cakeModel_contradiction_preserving_three_two
    (x x' : CakeController3Time) (y y' : CakeController2Time)
    (hcontr : RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      ⟨CakeFigureCtrl.two, y⟩ ⟨CakeFigureCtrl.two, y'⟩) :
    RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      (cakeModelAttest ⟨CakeFigureCtrl.three, x⟩ ⟨CakeFigureCtrl.two, y⟩)
      (cakeModelAttest ⟨CakeFigureCtrl.three, x'⟩ ⟨CakeFigureCtrl.two, y'⟩) := by
  cases x <;> cases x' <;> cases y <;> cases y' <;>
    simp [RawContradicts, cakeModelAttest, cakeModelTop, cakeModelLocalTop,
      CakeController2Time.join, CakeController3Time.join] at hcontr ⊢

private theorem cakeModel_contradiction_preserving_three_three
    (x x' y y' : CakeController3Time)
    (hcontr : RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      ⟨CakeFigureCtrl.three, y⟩ ⟨CakeFigureCtrl.three, y'⟩) :
    RawContradicts Sigma.fst cakeModelAttest cakeModelTop
      (cakeModelAttest ⟨CakeFigureCtrl.three, x⟩ ⟨CakeFigureCtrl.three, y⟩)
      (cakeModelAttest ⟨CakeFigureCtrl.three, x'⟩ ⟨CakeFigureCtrl.three, y'⟩) := by
  cases x <;> cases x' <;> cases y <;> cases y' <;>
    simp [RawContradicts, cakeModelAttest, cakeModelTop, cakeModelLocalTop,
      CakeController3Time.join] at hcontr ⊢

/-- Example 2.3.4: a finite located semilattice realizing Figure 5. -/
instance cakeModelLocatedSemilattice : LocatedSemilattice CakeModelTime CakeFigureCtrl where
  attest := cakeModelAttest
  controller := Sigma.fst
  bot := cakeModelBot
  top := cakeModelTop
  bot_controller := by
    intro p
    cases p <;> rfl
  top_controller := by
    intro p
    cases p <;> rfl
  controller_preserving := by
    intro t s
    rcases t with ⟨p, x⟩
    rcases s with ⟨q, y⟩
    cases p <;> cases q <;> cases x <;> cases y <;> rfl
  self_join_idem := by
    intro t
    rcases t with ⟨p, x⟩
    cases p <;> cases x <;> rfl
  self_join_comm := by
    intro t t' hctrl
    rcases t with ⟨p, x⟩
    rcases t' with ⟨p', x'⟩
    cases p <;> cases p' <;> cases hctrl <;> cases x <;> cases x' <;> rfl
  self_join_assoc := by
    intro t t' u hctrl hctrl'
    rcases t with ⟨p, x⟩
    rcases t' with ⟨p', x'⟩
    rcases u with ⟨p'', x''⟩
    cases p <;> cases p' <;> cases p'' <;> cases hctrl <;>
      cases hctrl' <;> cases x <;> cases x' <;> cases x'' <;> rfl
  self_bot_le := by
    intro p t hctrl
    rcases t with ⟨p', x⟩
    cases p <;> cases p' <;> cases hctrl <;> cases x <;> rfl
  self_le_top := by
    intro p t hctrl
    rcases t with ⟨p', x⟩
    cases p <;> cases p' <;> cases hctrl <;> cases x <;> rfl
  expansive := by
    intro t s
    rcases t with ⟨p, x⟩
    rcases s with ⟨q, y⟩
    cases p <;> cases q <;> cases x <;> cases y <;> rfl
  contradiction_preserving := by
    intro t t' s s' hctrl hctrl' hcontr
    rcases t with ⟨p, x⟩
    rcases t' with ⟨p', x'⟩
    rcases s with ⟨q, y⟩
    rcases s' with ⟨q', y'⟩
    cases p <;> cases p' <;> cases hctrl <;> cases q <;> cases q' <;>
      cases hctrl'
    · exact cakeModel_contradiction_preserving_one_one x x' y y' hcontr
    · exact cakeModel_contradiction_preserving_one_two x x' y y' hcontr
    · exact cakeModel_contradiction_preserving_one_three x x' y y' hcontr
    · exact cakeModel_contradiction_preserving_two_one x x' y y' hcontr
    · exact cakeModel_contradiction_preserving_two_two x x' y y' hcontr
    · exact cakeModel_contradiction_preserving_two_three x x' y y' hcontr
    · exact cakeModel_contradiction_preserving_three_one x x' y y' hcontr
    · exact cakeModel_contradiction_preserving_three_two x x' y y' hcontr
    · exact cakeModel_contradiction_preserving_three_three x x' y y' hcontr

/-- Embedding of the figure's named nodes into the finite cake witness. -/
def cakeModelTimeEmbed : CakeFigureNode → CakeModelTime
  | CakeFigureNode.a => ⟨CakeFigureCtrl.one, CakeController1Time.a⟩
  | CakeFigureNode.b => ⟨CakeFigureCtrl.two, CakeController2Time.b⟩
  | CakeFigureNode.c => ⟨CakeFigureCtrl.two, CakeController2Time.c⟩
  | CakeFigureNode.d => ⟨CakeFigureCtrl.one, CakeController1Time.d⟩
  | CakeFigureNode.e => ⟨CakeFigureCtrl.one, CakeController1Time.e⟩
  | CakeFigureNode.f => ⟨CakeFigureCtrl.two, CakeController2Time.f⟩
  | CakeFigureNode.g => ⟨CakeFigureCtrl.three, CakeController3Time.g⟩
  | CakeFigureNode.h => ⟨CakeFigureCtrl.one, CakeController1Time.h⟩

/--
Example 2.3.4: an existential realizability reading of "we return to Figure 1 and interpret
it as a located semilattice". The paper fixes no total attestation table, only the figure's
named data, so the claim is that *some* located semilattice realizes the figure, not that
there is one canonical structure.

The predicate pins down every datum of the figure: injective embeddings of the three
controllers and eight named nodes into a single located semilattice; the controller
assignment; every named node consistent (non-top); each same-controller order edge `s ≼ t`
as the located order (`attest t s = t`); the fork endpoints `c` and `f` contradicting; and
each dashed attestation arc `s → t` cross-controller with `t` having absorbed the
attestation to `s` (`attest t s = t`).

The witness uses a finite total attestation table: same-controller attestation is the local
top-tree join, the dashed arcs return their target times, and all other cross-controller
attestations return the target controller's top.
-/
theorem cakeFigure_realizable_as_located_semilattice :
    ∃ (Time : Type) (Ctrl : Type) (inst : LocatedSemilattice Time Ctrl)
      (ctrlEmbed : CakeFigureCtrl → Ctrl) (timeEmbed : CakeFigureNode → Time),
      (∀ p q : CakeFigureCtrl, ctrlEmbed p = ctrlEmbed q → p = q) ∧
      (∀ m n : CakeFigureNode, timeEmbed m = timeEmbed n → m = n) ∧
      (∀ n : CakeFigureNode,
        @LocatedSemilattice.controller Time Ctrl inst (timeEmbed n) =
          ctrlEmbed (CakeFigureNode.controller n)) ∧
      (∀ n : CakeFigureNode,
        timeEmbed n ≠
          @LocatedSemilattice.top Time Ctrl inst
            (ctrlEmbed (CakeFigureNode.controller n))) ∧
      (∀ s t : CakeFigureNode, CakeFigureNode.TopPrecedes s t →
        @LocatedSemilattice.attest Time Ctrl inst (timeEmbed t) (timeEmbed s) =
          timeEmbed t) ∧
      @LocatedSemilattice.Contradicts Time Ctrl inst
          (timeEmbed CakeFigureNode.c) (timeEmbed CakeFigureNode.f) ∧
      (∀ s t : CakeFigureNode, CakeFigureNode.AttestationArc s t →
        CakeFigureNode.controller s ≠ CakeFigureNode.controller t ∧
        @LocatedSemilattice.attest Time Ctrl inst (timeEmbed t) (timeEmbed s) =
          timeEmbed t) := by
  refine ⟨CakeModelTime, CakeFigureCtrl, cakeModelLocatedSemilattice, id,
    cakeModelTimeEmbed, ?_⟩
  constructor
  · intro p q h
    exact h
  constructor
  · intro m n h
    cases m <;> cases n <;> cases h <;> rfl
  constructor
  · intro n
    cases n <;> rfl
  constructor
  · intro n htop
    cases n <;> cases htop
  constructor
  · intro s t hprecedes
    induction hprecedes with
    | edge hedge =>
        cases hedge <;> rfl
    | trans hsource_middle hmiddle_target hleft hright =>
        rename_i source middle target
        let L := cakeModelLocatedSemilattice
        have hctrl_source_middle :
            L.controller (cakeModelTimeEmbed source) =
              L.controller (cakeModelTimeEmbed middle) := by
          have hfig := CakeFigureNode.topPrecedes_same_controller hsource_middle
          cases source <;> cases middle <;>
            simp [L, cakeModelLocatedSemilattice, cakeModelTimeEmbed,
              CakeFigureNode.controller] at hfig ⊢
        have hctrl_middle_target :
            L.controller (cakeModelTimeEmbed middle) =
              L.controller (cakeModelTimeEmbed target) := by
          have hfig := CakeFigureNode.topPrecedes_same_controller hmiddle_target
          cases middle <;> cases target <;>
            simp [L, cakeModelLocatedSemilattice, cakeModelTimeEmbed,
              CakeFigureNode.controller] at hfig ⊢
        have hsource_middle_le :
            L.le (cakeModelTimeEmbed source) (cakeModelTimeEmbed middle) := by
          constructor
          · exact hctrl_source_middle
          · calc
              L.attest (cakeModelTimeEmbed source) (cakeModelTimeEmbed middle)
                  = L.attest (cakeModelTimeEmbed middle) (cakeModelTimeEmbed source) :=
                    L.self_join_comm hctrl_source_middle
              _ = cakeModelTimeEmbed middle := hleft
        have hmiddle_target_le :
            L.le (cakeModelTimeEmbed middle) (cakeModelTimeEmbed target) := by
          constructor
          · exact hctrl_middle_target
          · calc
              L.attest (cakeModelTimeEmbed middle) (cakeModelTimeEmbed target)
                  = L.attest (cakeModelTimeEmbed target) (cakeModelTimeEmbed middle) :=
                    L.self_join_comm hctrl_middle_target
              _ = cakeModelTimeEmbed target := hright
        have hsource_target_le :
            L.le (cakeModelTimeEmbed source) (cakeModelTimeEmbed target) :=
          L.le_trans hsource_middle_le hmiddle_target_le
        calc
          L.attest (cakeModelTimeEmbed target) (cakeModelTimeEmbed source)
              = L.attest (cakeModelTimeEmbed source) (cakeModelTimeEmbed target) :=
                L.self_join_comm hsource_target_le.1.symm
          _ = cakeModelTimeEmbed target := hsource_target_le.2
  constructor
  · exact ⟨rfl, rfl⟩
  · intro s t harc
    cases harc <;> exact ⟨(by intro h; cases h), rfl⟩

end ConsistentHistories.Models.LocatedSemilattices.Examples
