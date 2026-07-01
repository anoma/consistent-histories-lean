import ContForm.Models.LocatedSemilattices.Examples.CakeFigure

namespace ContForm.Models.LocatedSemilattices.Examples

open ContForm.Foundation.LocatedSemilattices.Basic
open ContForm.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ContForm.Foundation.LocatedSemilattices.TopTrees

/-- Example 2.3.5: the five plays `⊥, paper, scissors, stone, ⊤`. -/
inductive GamePlay where
  | bot
  | paper
  | scissors
  | stone
  | top
  deriving DecidableEq

namespace GamePlay

/-- Example 2.3.5: the flat join `∨` on plays — distinct middle plays join to `⊤`. -/
def join : GamePlay → GamePlay → GamePlay
  | bot, x => x
  | x, bot => x
  | top, _ => top
  | _, top => top
  | paper, paper => paper
  | scissors, scissors => scissors
  | stone, stone => stone
  | _, _ => top

theorem join_idem (x : GamePlay) : join x x = x := by
  cases x <;> rfl

theorem join_comm (x y : GamePlay) : join x y = join y x := by
  cases x <;> cases y <;> rfl

theorem join_assoc (x y z : GamePlay) :
    join (join x y) z = join x (join y z) := by
  cases x <;> cases y <;> cases z <;> rfl

theorem bot_le (x : GamePlay) : join bot x = x := by
  cases x <;> rfl

theorem le_top (x : GamePlay) : join x top = top := by
  cases x <;> rfl

end GamePlay

/-- Example 2.3.5: the bounded semilattice `Play = {⊥, paper, scissors, stone, ⊤}`. -/
instance gamePlaySemilattice : BoundedSemilattice GamePlay where
  join := GamePlay.join
  bot := GamePlay.bot
  top := GamePlay.top
  join_idem := GamePlay.join_idem
  join_comm := GamePlay.join_comm
  join_assoc := GamePlay.join_assoc
  bot_le := GamePlay.bot_le
  le_top := GamePlay.le_top

/-- Example 2.3.5: `paper ∨ scissors = ⊤`. -/
theorem gamePlay_paper_join_scissors :
    GamePlay.join GamePlay.paper GamePlay.scissors = GamePlay.top := by
  rfl

/-- Example 2.3.5: `paper ∨ paper = paper`. -/
theorem gamePlay_paper_join_paper :
    GamePlay.join GamePlay.paper GamePlay.paper = GamePlay.paper := by
  rfl

/-- Example 2.3.5: `⊥ ∨ stone = stone`. -/
theorem gamePlay_bot_join_stone :
    GamePlay.join GamePlay.bot GamePlay.stone = GamePlay.stone := by
  rfl

/-- Example 2.3.5: `stone ∨ ⊤ = ⊤`. -/
theorem gamePlay_stone_join_top :
    GamePlay.join GamePlay.stone GamePlay.top = GamePlay.top := by
  rfl

/--
Example 2.3.5: the flat play order has no comparisons except bottom below
everything, everything below top, and equality.
-/
theorem gamePlaySemilattice_le_iff (x y : GamePlay) :
    x ≤ y ↔
      x = GamePlay.bot ∨ y = GamePlay.top ∨ x = y := by
  constructor
  · intro h
    cases x <;> cases y <;>
      simp [gamePlaySemilattice, BoundedSemilattice.le, LE.le, GamePlay.join] at h ⊢
  · intro h
    cases x <;> cases y <;>
      simp [gamePlaySemilattice, BoundedSemilattice.le, LE.le, GamePlay.join] at h ⊢

/-- Example 2.3.5: the flat play semilattice is sequential. -/
theorem gamePlaySemilattice_sequential : gamePlaySemilattice.Sequential := by
  intro x y
  cases x <;> cases y <;> simp [gamePlaySemilattice, GamePlay.join]

/-- Example 2.3.5: paper and scissors are contradictory plays. -/
theorem gamePlay_paper_contradicts_scissors :
    GamePlay.paper 🗲 GamePlay.scissors := by
  rfl

/-- Example 2.3.5: paper and stone are contradictory plays. -/
theorem gamePlay_paper_contradicts_stone :
    GamePlay.paper 🗲 GamePlay.stone := by
  rfl

/-- Example 2.3.5: scissors and stone are contradictory plays. -/
theorem gamePlay_scissors_contradicts_stone :
    GamePlay.scissors 🗲 GamePlay.stone := by
  rfl

/-- Example 2.3.5: the two controllers `Ctrl = {Alice, Bob}`. -/
inductive GameCtrl where
  | alice
  | bob
  deriving DecidableEq

/-- Example 2.3.5: game times are controller/play pairs, `Time = Ctrl × Play`. -/
abbrev GameTime := GameCtrl × GamePlay

/-- Example 2.3.5: the three winning cross-controller play pairs `(paper, stone)`,
`(stone, scissors)`, and `(scissors, paper)`. -/
def gameWins : GamePlay → GamePlay → Bool
  | GamePlay.paper, GamePlay.stone => true
  | GamePlay.stone, GamePlay.scissors => true
  | GamePlay.scissors, GamePlay.paper => true
  | _, _ => false

/-- Example 2.3.5: cross-controller attestation on plays — the winner's play on a win, else `⊤`. -/
def gameCrossAttest (play play' : GamePlay) : GamePlay :=
  match play, play' with
  | GamePlay.paper, GamePlay.stone => GamePlay.paper
  | GamePlay.stone, GamePlay.scissors => GamePlay.stone
  | GamePlay.scissors, GamePlay.paper => GamePlay.scissors
  | _, _ => GamePlay.top

/-- Example 2.3.5: attestation `#`, the play join within a controller and the game table
across controllers. -/
def gameAttest : GameTime → GameTime → GameTime
  | (GameCtrl.alice, play), (GameCtrl.alice, play') =>
      (GameCtrl.alice, GamePlay.join play play')
  | (GameCtrl.bob, play), (GameCtrl.bob, play') =>
      (GameCtrl.bob, GamePlay.join play play')
  | (GameCtrl.alice, play), (GameCtrl.bob, play') =>
      (GameCtrl.alice, gameCrossAttest play play')
  | (GameCtrl.bob, play), (GameCtrl.alice, play') =>
      (GameCtrl.bob, gameCrossAttest play play')

/-- Example 2.3.5: the paper-scissors-stone located semilattice `L = (Ctrl, Time, #, ctrl)`. -/
instance simpleGameLocatedSemilattice : LocatedSemilattice GameTime GameCtrl where
  attest := gameAttest
  controller := Prod.fst
  bot p := (p, GamePlay.bot)
  top p := (p, GamePlay.top)
  bot_controller := by
    intro p
    rfl
  top_controller := by
    intro p
    rfl
  controller_preserving := by
    intro t s
    cases t with
    | mk p play =>
        cases s with
        | mk p' _play' =>
            cases p <;> cases p' <;> rfl
  self_join_idem := by
    intro t
    cases t with
    | mk p play =>
        cases p <;> cases play <;> rfl
  self_join_comm := by
    intro t t' hctrl
    cases t with
    | mk p play =>
        cases t' with
        | mk p' play' =>
            cases p <;> cases p' <;> cases play <;> cases play' <;> cases hctrl <;> rfl
  self_join_assoc := by
    intro t t' u hctrl hctrl'
    cases t with
    | mk p play =>
        cases t' with
        | mk p' play' =>
            cases u with
            | mk p'' play'' =>
                cases p <;> cases p' <;> cases p'' <;>
                  cases play <;> cases play' <;> cases play'' <;>
                    cases hctrl <;> cases hctrl' <;> rfl
  self_bot_le := by
    intro p t hctrl
    cases t with
    | mk p' play =>
        cases p <;> cases p' <;> cases play <;> cases hctrl <;> rfl
  self_le_top := by
    intro p t hctrl
    cases t with
    | mk p' play =>
        cases p <;> cases p' <;> cases play <;> cases hctrl <;> rfl
  expansive := by
    intro t s
    cases t with
    | mk p play =>
        cases s with
        | mk p' play' =>
            cases p <;> cases p' <;> cases play <;> cases play' <;> rfl
  contradiction_preserving := by
    intro t t' s s' hctrl hctrl' hcontr
    cases t with
    | mk p play =>
        cases t' with
        | mk p' play' =>
            cases s with
            | mk q opp =>
                cases s' with
                | mk q' opp' =>
                    cases hctrl
                    cases hctrl'
                    cases p <;> cases q <;>
                      cases play <;> cases play' <;> cases opp <;> cases opp' <;>
                        simp [RawContradicts, gameAttest, gameCrossAttest, GamePlay.join]
                          at hcontr ⊢

/-- Example 2.3.5: same-controller attestation is the play join. -/
theorem simpleGame_same_controller_apply
    (p : GameCtrl) (play play' : GamePlay) :
    gameAttest (p, play) (p, play') = (p, GamePlay.join play play') := by
  cases p <;> rfl

/-- Example 2.3.5: the cross-controller table returns the play on a win and `⊤` otherwise. -/
theorem gameCrossAttest_eq_if_wins (play play' : GamePlay) :
    gameCrossAttest play play' =
      if gameWins play play' then play else GamePlay.top := by
  cases play <;> cases play' <;> rfl

/-- Example 2.3.5: cross-controller attestation applies the game table. -/
theorem simpleGame_cross_controller_apply
    (p p' : GameCtrl) (play play' : GamePlay) (h : p ≠ p') :
    gameAttest (p, play) (p', play') =
      (p, if gameWins play play' then play else GamePlay.top) := by
  cases p <;> cases p'
  · contradiction
  · simp [gameAttest, gameCrossAttest_eq_if_wins]
  · simp [gameAttest, gameCrossAttest_eq_if_wins]
  · contradiction

/-- Example 2.3.5: a non-winning cross-controller play goes to `⊤` — a loss, draw, or
invalid round. -/
theorem simpleGame_cross_controller_failure
    (p p' : GameCtrl) (play play' : GamePlay) (hctrl : p ≠ p')
    (hwin : gameWins play play' = false) :
    gameAttest (p, play) (p', play') = (p, GamePlay.top) := by
  rw [simpleGame_cross_controller_apply p p' play play' hctrl]
  simp [hwin]

/-- Example 2.3.5: a winning cross-controller play survives unchanged — a win. -/
theorem simpleGame_cross_controller_success
    (p p' : GameCtrl) (play play' : GamePlay) (hctrl : p ≠ p')
    (hwin : gameWins play play' = true) :
    gameAttest (p, play) (p', play') = (p, play) := by
  rw [simpleGame_cross_controller_apply p p' play play' hctrl]
  simp [hwin]

/-- Example 2.3.5: simple-game attestation is controller-preserving. -/
theorem simpleGameLocatedSemilattice_controller_preserving
    (t s : GameTime) :
    (gameAttest t s).fst = t.fst :=
  simpleGameLocatedSemilattice.controller_preserving t s

/-- Example 2.3.5: simple-game attestation is expansive. -/
theorem simpleGameLocatedSemilattice_expansive
    (t s : GameTime) :
    gameAttest (gameAttest t s) t = gameAttest t s :=
  simpleGameLocatedSemilattice.expansive t s

/-- Example 2.3.5: simple-game attestation is strongly contradiction-preserving. -/
theorem simpleGameLocatedSemilattice_strongly_contradiction_preserving
    {t t' s s' : GameTime} (htt' : t.fst = t'.fst) (hss' : s.fst = s'.fst)
    (hcontr : s 🗲 s') :
    (gameAttest t s) 🗲 (gameAttest t' s') :=
  simpleGameLocatedSemilattice.contradicts_attest htt' hss' hcontr

/-- Example 2.3.5: paper beats stone, so the play survives (a win). -/
theorem simpleGame_paper_beats_stone (p p' : GameCtrl) (h : p ≠ p') :
    gameAttest (p, GamePlay.paper) (p', GamePlay.stone) = (p, GamePlay.paper) := by
  cases p <;> cases p'
  · contradiction
  · decide
  · decide
  · contradiction

/-- Example 2.3.5: stone beats scissors, so the play survives (a win). -/
theorem simpleGame_stone_beats_scissors (p p' : GameCtrl) (h : p ≠ p') :
    gameAttest (p, GamePlay.stone) (p', GamePlay.scissors) = (p, GamePlay.stone) := by
  cases p <;> cases p'
  · contradiction
  · decide
  · decide
  · contradiction

/-- Example 2.3.5: scissors beats paper, so the play survives (a win). -/
theorem simpleGame_scissors_beats_paper (p p' : GameCtrl) (h : p ≠ p') :
    gameAttest (p, GamePlay.scissors) (p', GamePlay.paper) = (p, GamePlay.scissors) := by
  cases p <;> cases p'
  · contradiction
  · decide
  · decide
  · contradiction

/-- Example 2.3.5: `paper` against `⊥` is not a win, so it goes to `⊤`. -/
theorem simpleGame_paper_with_bot_fails (p p' : GameCtrl) (h : p ≠ p') :
    gameAttest (p, GamePlay.paper) (p', GamePlay.bot) = (p, GamePlay.top) := by
  cases p <;> cases p'
  · contradiction
  · decide
  · decide
  · contradiction

/-- Example 2.3.5: `⊥` against `stone` is not a win, so it goes to `⊤`. -/
theorem simpleGame_cross_bottom_stone_fails (p p' : GameCtrl) (h : p ≠ p') :
    gameAttest (p, GamePlay.bot) (p', GamePlay.stone) = (p, GamePlay.top) := by
  cases p <;> cases p'
  · contradiction
  · decide
  · decide
  · contradiction

/-- Remark 2.2.3(2)(b): across distinct controllers attestation need not be commutative —
a paper-scissors-stone witness. -/
theorem simpleGame_attest_not_commutative :
    (GameCtrl.alice, GamePlay.paper) # (GameCtrl.bob, GamePlay.stone) ≠
      (GameCtrl.bob, GamePlay.stone) # (GameCtrl.alice, GamePlay.paper) := by
  change (GameCtrl.alice, GamePlay.paper) ≠ (GameCtrl.bob, GamePlay.top)
  intro h
  cases h

/-- Remark 2.2.3(2)(b): across distinct controllers attestation need not be associative —
a paper-scissors-stone witness. -/
theorem simpleGame_attest_not_associative :
    ((GameCtrl.alice, GamePlay.paper) # (GameCtrl.bob, GamePlay.stone)) # (GameCtrl.bob, GamePlay.bot) ≠
      (GameCtrl.alice, GamePlay.paper) # ((GameCtrl.bob, GamePlay.stone) # (GameCtrl.bob, GamePlay.bot)) := by
  change (GameCtrl.alice, GamePlay.top) ≠ (GameCtrl.alice, GamePlay.paper)
  intro h
  cases h

/-- Remark 2.2.3(2)(b): some located semilattice has non-commutative attestation. -/
theorem exists_locatedSemilattice_attest_not_commutative :
    ∃ (Time : Type) (Ctrl : Type) (inst : LocatedSemilattice Time Ctrl) (t s : Time),
      @LocatedSemilattice.attest Time Ctrl inst t s ≠
        @LocatedSemilattice.attest Time Ctrl inst s t := by
  exact
    ⟨GameTime, GameCtrl, simpleGameLocatedSemilattice,
      (GameCtrl.alice, GamePlay.paper),
      (GameCtrl.bob, GamePlay.stone),
      simpleGame_attest_not_commutative⟩

/-- Remark 2.2.3(2)(b): some located semilattice has non-associative attestation. -/
theorem exists_locatedSemilattice_attest_not_associative :
    ∃ (Time : Type) (Ctrl : Type) (inst : LocatedSemilattice Time Ctrl) (t s u : Time),
      @LocatedSemilattice.attest Time Ctrl inst
          (@LocatedSemilattice.attest Time Ctrl inst t s) u ≠
        @LocatedSemilattice.attest Time Ctrl inst t
          (@LocatedSemilattice.attest Time Ctrl inst s u) := by
  exact
    ⟨GameTime, GameCtrl, simpleGameLocatedSemilattice,
      (GameCtrl.alice, GamePlay.paper),
      (GameCtrl.bob, GamePlay.stone),
      (GameCtrl.bob, GamePlay.bot),
      simpleGame_attest_not_associative⟩

/-- Example 2.3.5: the paper-scissors-stone located semilattice is sequential. -/
theorem simpleGame_sequential : simpleGameLocatedSemilattice.Sequential := by
  intro p t t'
  rcases t with ⟨⟨pt, play⟩, ht⟩
  rcases t' with ⟨⟨pt', play'⟩, ht'⟩
  cases p <;> cases pt <;> cases pt' <;>
    cases play <;> cases play' <;>
      simp [LocatedSemilattice.fiber, simpleGameLocatedSemilattice, gameAttest,
        GamePlay.join] at ht ht' ⊢

/-- Example 2.3.5: the paper-scissors-stone construction is a sequential located semilattice. -/
theorem paperScissorsStone_sequential :
    simpleGameLocatedSemilattice.Sequential := by
  exact simpleGame_sequential

/--
Example 2.3.5: within a fixed controller, the simple-game located order
is exactly the play order.
-/
theorem simpleGameLocatedSemilattice_same_controller_le_iff_play_le
    (p : GameCtrl) (x y : GamePlay) :
    (p, x) ≼ (p, y) ↔
      x ≤ y := by
  cases p <;> cases x <;> cases y <;>
    simp [LocatedSemilattice.le, BoundedSemilattice.le, LE.le, simpleGameLocatedSemilattice,
      gamePlaySemilattice, gameAttest, GamePlay.join]

/--
Example 2.3.5 at the located-semilattice level: same-controller simple-game
times have no comparisons except bottom below everything, everything below top,
and equality.
-/
theorem simpleGameLocatedSemilattice_same_controller_le_iff
    (p : GameCtrl) (x y : GamePlay) :
    (p, x) ≼ (p, y) ↔
      x = GamePlay.bot ∨ y = GamePlay.top ∨ x = y := by
  rw [simpleGameLocatedSemilattice_same_controller_le_iff_play_le,
    gamePlaySemilattice_le_iff]

/--
Example 2.3.5: same-controller simple-game contradiction is exactly
contradiction of the underlying plays.
-/
theorem simpleGameLocatedSemilattice_same_controller_contradicts_iff_play_contradicts
    (p : GameCtrl) (x y : GamePlay) :
    (p, x) 🗲 (p, y) ↔
      x 🗲 y := by
  cases p <;> cases x <;> cases y <;>
    simp [Contradictory.contradicts, LocatedSemilattice.Contradicts, RawContradicts, BoundedSemilattice.Contradicts,
      simpleGameLocatedSemilattice, gamePlaySemilattice, gameAttest, GamePlay.join]

/--
Example 2.3.5: distinct non-bottom, non-top simple-game plays at one
controller contradict.
-/
theorem simpleGameLocatedSemilattice_distinct_nonterminal_plays_contradict
    (p : GameCtrl) {x y : GamePlay}
    (hx_bot : x ≠ GamePlay.bot) (hx_top : x ≠ GamePlay.top)
    (hy_bot : y ≠ GamePlay.bot) (hy_top : y ≠ GamePlay.top)
    (hxy : x ≠ y) :
    (p, x) 🗲 (p, y) := by
  cases p <;> cases x <;> cases y <;>
    simp [Contradictory.contradicts, LocatedSemilattice.Contradicts, RawContradicts, simpleGameLocatedSemilattice,
      gameAttest, GamePlay.join] at hx_bot hx_top hy_bot hy_top hxy ⊢

/-- Example 2.3.5: witness that attestation is not monotone in its second argument. -/
theorem simpleGame_not_monotone_second_component :
    (GameCtrl.bob, GamePlay.bot) ≼ (GameCtrl.bob, GamePlay.stone) ∧
      gameAttest (GameCtrl.alice, GamePlay.paper) (GameCtrl.bob, GamePlay.bot) =
        (GameCtrl.alice, GamePlay.top) ∧
      gameAttest (GameCtrl.alice, GamePlay.paper) (GameCtrl.bob, GamePlay.stone) =
        (GameCtrl.alice, GamePlay.paper) ∧
      ¬ (gameAttest (GameCtrl.alice, GamePlay.paper) (GameCtrl.bob, GamePlay.bot)) ≼ (gameAttest (GameCtrl.alice, GamePlay.paper) (GameCtrl.bob, GamePlay.stone)) := by
  constructor
  · constructor
    · rfl
    · rfl
  constructor
  · rfl
  constructor
  · rfl
  · intro hle
    simp [LocatedSemilattice.le, simpleGameLocatedSemilattice, gameAttest, gameCrossAttest,
      GamePlay.join] at hle

/--
Example 2.3.5: in the simple game, attestation is not monotone in the
second component.
-/
theorem simpleGame_exists_not_monotone_second_component :
    ∃ t s s' : GameTime,
      s ≼ s' ∧
        ¬ (t # s) ≼ (t # s') := by
  refine
    ⟨(GameCtrl.alice, GamePlay.paper),
      (GameCtrl.bob, GamePlay.bot),
      (GameCtrl.bob, GamePlay.stone), ?_⟩
  exact
    ⟨simpleGame_not_monotone_second_component.1,
      simpleGame_not_monotone_second_component.2.2.2⟩

/-- Example 2.3.5: witness that attestation is not monotone in its first argument. -/
theorem simpleGame_not_monotone_first_component :
    (GameCtrl.alice, GamePlay.bot) ≼ (GameCtrl.alice, GamePlay.paper) ∧
      gameAttest (GameCtrl.alice, GamePlay.bot) (GameCtrl.bob, GamePlay.stone) =
        (GameCtrl.alice, GamePlay.top) ∧
      gameAttest (GameCtrl.alice, GamePlay.paper) (GameCtrl.bob, GamePlay.stone) =
        (GameCtrl.alice, GamePlay.paper) ∧
      ¬ (gameAttest (GameCtrl.alice, GamePlay.bot) (GameCtrl.bob, GamePlay.stone)) ≼ (gameAttest (GameCtrl.alice, GamePlay.paper) (GameCtrl.bob, GamePlay.stone)) := by
  constructor
  · constructor
    · rfl
    · rfl
  constructor
  · rfl
  constructor
  · rfl
  · intro hle
    simp [LocatedSemilattice.le, simpleGameLocatedSemilattice, gameAttest, gameCrossAttest,
      GamePlay.join] at hle

/--
Example 2.3.5: in the simple game, attestation is not monotone in the first
component.
-/
theorem simpleGame_exists_not_monotone_first_component :
    ∃ t t' s : GameTime,
      t ≼ t' ∧
        ¬ (t # s) ≼ (t' # s) := by
  refine
    ⟨(GameCtrl.alice, GamePlay.bot),
      (GameCtrl.alice, GamePlay.paper),
      (GameCtrl.bob, GamePlay.stone), ?_⟩
  exact
    ⟨simpleGame_not_monotone_first_component.1,
      simpleGame_not_monotone_first_component.2.2.2⟩

/--
Example 2.3.5: in the simple game, attestation is not monotone in either
component.
-/
theorem simpleGame_exists_not_monotone_either_component :
    (∃ t t' s : GameTime,
      t ≼ t' ∧
        ¬ (t # s) ≼ (t' # s)) ∧
    (∃ t s s' : GameTime,
      s ≼ s' ∧
        ¬ (t # s) ≼ (t # s')) := by
  exact
    ⟨simpleGame_exists_not_monotone_first_component,
      simpleGame_exists_not_monotone_second_component⟩

end ContForm.Models.LocatedSemilattices.Examples
