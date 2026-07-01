import ContForm.Routes.StrongerSafety.Closure

/-!
Paper subsection 6.3, "Additional machinery: chain of cuts".

Throughout this subsection the paper fixes a located semilattice with Cut. The
file formalizes:
* Definition 6.3.1, the chain of cuts of an inactive index (`ChainOfCuts`);
* Lemma 6.3.2, well-definedness of the chain of cuts (`exists_of_inactive`,
  `next_eq_of_current_eq`, `edgeCount_eq_of_same_start`,
  `node_eq_of_same_start_position`, packaged in `exists_unique_nodes_of_inactive`);
* Lemma 6.3.3, that the non-final chain nodes are active in the other derivation
  (`left_chain_right_active_of_least_inconsistent`).
-/

namespace ContForm.Routes.StrongerSafety.Chains

open ContForm.Foundation.Paths.Basic
open ContForm.Routes.Paths.Circuits
open ContForm.Foundation.LocatedSemilattices.Basic
open ContForm.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ContForm.Foundation.Cut.Structure
open ContForm.Foundation.Cut.Structure.LocatedSemilatticeWithCut

universe u v

/--
Definition 6.3.1 (chain of cuts). For a derivation `deriv` (the paper's `Π`) and
an index `start` (the paper's `i`) that is inactive in `Π`, the chain of cuts of
`i` in `Π` is a tuple `(i = i₁, i₂, …, iₙ)`. Here `node` enumerates `i₁,…,iₙ`
over `Fin (edgeCount + 1)`, so `edgeCount = n − 1` counts the Cut edges;
`edgeCount_pos` records that an inactive start differs from the active endpoint,
i.e. `n ≥ 2`. The fields formalize the four defining clauses:
* `first_eq` — clause (1), `i = i₁`;
* `inactive_before_last` — clause (2), `i₁,…,i_{n-1}` are inactive in `Π`;
* `last_active` — clause (3), `iₙ` is active in `Π`;
* `cuts` — clause (4), for each `1 ≤ l < n` there is `k_l ∈ index(Π)` with
  `(Cut_{k_l, i_l, i_{l+1}}) ∈ Π`.
-/
structure ChainOfCuts {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    (deriv : Derivation Time T) (start : T.Index) where
  edgeCount : Nat
  edgeCount_pos : 0 < edgeCount
  node : Fin (edgeCount + 1) → T.Index
  first_eq : node ⟨0, Nat.succ_pos edgeCount⟩ = start
  inactive_before_last :
    ∀ l : Fin edgeCount, deriv.Inactive (node (Fin.castSucc l))
  last_active : deriv.Active (node ⟨edgeCount, Nat.lt_succ_self edgeCount⟩)
  cuts :
    ∀ l : Fin edgeCount, ∃ k : T.Index,
      ContainsCut deriv (T.paperIndex k) (T.paperIndex (node (Fin.castSucc l)))
        (T.paperIndex (node ⟨l.val + 1, Nat.succ_lt_succ l.isLt⟩))

namespace ChainOfCuts

/-- The first node `i_1` of a chain. -/
def first {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {start : T.Index} (chain : ChainOfCuts deriv start) : T.Index :=
  chain.node ⟨0, Nat.succ_pos chain.edgeCount⟩

/-- The final node `i_n` of a chain. -/
def last {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {start : T.Index} (chain : ChainOfCuts deriv start) : T.Index :=
  chain.node ⟨chain.edgeCount, Nat.lt_succ_self chain.edgeCount⟩

/-- The `l`th non-final node of a chain. -/
def current {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {start : T.Index} (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    T.Index :=
  chain.node (Fin.castSucc l)

/-- The node immediately after the `l`th non-final node. -/
def next {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {start : T.Index} (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    T.Index :=
  chain.node ⟨l.val + 1, Nat.succ_lt_succ l.isLt⟩

theorem first_eq_start {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) : chain.first = start := by
  exact chain.first_eq

theorem first_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) : deriv.Inactive start := by
  have hfirst : deriv.Inactive chain.first := chain.inactive_before_last
    ⟨0, chain.edgeCount_pos⟩
  rw [first_eq_start chain] at hfirst
  exact hfirst

theorem last_active' {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) : deriv.Active chain.last := by
  exact chain.last_active

theorem link_contains_cut {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    ∃ k : T.Index, ContainsCut deriv (T.paperIndex k) (T.paperIndex (chain.current l))
      (T.paperIndex (chain.next l)) := by
  exact chain.cuts l

/--
Every chain link exposes the decomposable Cut-prefix data for the Cut that
connects its current node to its next node.
-/
theorem link_cutPrefixData {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    Nonempty
      (Σ upper : T.Index,
        CutPrefixData deriv (T.paperIndex upper) (T.paperIndex (chain.current l))
          (T.paperIndex (chain.next l))) := by
  rcases chain.link_contains_cut l with ⟨upper, hcut⟩
  rcases containsCut_prefixData hcut with ⟨data⟩
  exact ⟨⟨upper, data⟩⟩

theorem link_order {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    ∃ k : T.Index,
      T.paperIndex (chain.next l) < T.paperIndex (chain.current l) ∧
        T.paperIndex (chain.current l) < T.paperIndex k ∧
          ContainsCut deriv (T.paperIndex k) (T.paperIndex (chain.current l))
            (T.paperIndex (chain.next l)) := by
  rcases chain.link_contains_cut l with ⟨k, hcut⟩
  have horder := containsCut_order hcut
  exact ⟨k, horder.1, horder.2, hcut⟩

/--
Uniqueness step of Lemma 6.3.2: because cuts are affine (Proposition 5.2.3), the
Cut into a chain node determines its target, so equal current nodes have equal
next nodes. This is the local fact the paper uses to conclude the successor `i_{l+1}`
is uniquely defined by `i_l`.
-/
theorem next_eq_of_current_eq {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start start' : T.Index}
    (chain : ChainOfCuts deriv start) (chain' : ChainOfCuts deriv start')
    (l : Fin chain.edgeCount) (l' : Fin chain'.edgeCount)
    (hcurrent : chain.current l = chain'.current l') :
    chain.next l = chain'.next l' := by
  rcases chain.link_contains_cut l with ⟨upper, hcut⟩
  rcases chain'.link_contains_cut l' with ⟨upper', hcut'⟩
  have hcut'_same_center :
      ContainsCut deriv (T.paperIndex upper') (T.paperIndex (chain.current l))
        (T.paperIndex (chain'.next l')) := by
    simpa [hcurrent] using hcut'
  have hpaper :
      T.paperIndex (chain.next l) = T.paperIndex (chain'.next l') :=
    ContForm.Routes.PathProperties.FlagNesting.containsCut_same_center_lower_eq
      hcut hcut'_same_center
  apply Fin.ext
  exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hpaper)

/--
Global uniqueness component: two chains from the same start
agree at every numeric position common to both chains.
-/
theorem node_eq_of_same_start_position
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain chain' : ChainOfCuts deriv start) {n : Nat}
    (hn : n ≤ chain.edgeCount) (hn' : n ≤ chain'.edgeCount) :
    chain.node ⟨n, Nat.lt_succ_of_le hn⟩ =
      chain'.node ⟨n, Nat.lt_succ_of_le hn'⟩ := by
  induction n with
  | zero =>
      have hleft :
          chain.node ⟨0, Nat.lt_succ_of_le hn⟩ = start := by
        simpa using chain.first_eq
      have hright :
          chain'.node ⟨0, Nat.lt_succ_of_le hn'⟩ = start := by
        simpa using chain'.first_eq
      exact hleft.trans hright.symm
  | succ n ih =>
      have hn_lt : n < chain.edgeCount := Nat.lt_of_succ_le hn
      have hn'_lt : n < chain'.edgeCount := Nat.lt_of_succ_le hn'
      let l : Fin chain.edgeCount := ⟨n, hn_lt⟩
      let l' : Fin chain'.edgeCount := ⟨n, hn'_lt⟩
      have hcurrent : chain.current l = chain'.current l' := by
        have hprev := ih (Nat.le_of_lt hn_lt) (Nat.le_of_lt hn'_lt)
        simpa [current, l, l'] using hprev
      have hnext := ChainOfCuts.next_eq_of_current_eq chain chain' l l' hcurrent
      simpa [next, l, l'] using hnext

/--
Length uniqueness component: two chains from the same start
have the same number of Cut edges.
-/
theorem edgeCount_eq_of_same_start
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain chain' : ChainOfCuts deriv start) :
    chain.edgeCount = chain'.edgeCount := by
  apply Nat.le_antisymm
  · by_cases hle : chain.edgeCount ≤ chain'.edgeCount
    · exact hle
    have hlt : chain'.edgeCount < chain.edgeCount := Nat.lt_of_not_ge hle
    let l : Fin chain.edgeCount := ⟨chain'.edgeCount, hlt⟩
    have hinactive :
        deriv.Inactive
          (chain.node
            ⟨chain'.edgeCount, Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩) := by
      have h := chain.inactive_before_last l
      simpa [current, l] using h
    have hnode := node_eq_of_same_start_position chain chain'
      (Nat.le_of_lt hlt) (Nat.le_refl chain'.edgeCount)
    have hactive :
        deriv.Active
          (chain.node
            ⟨chain'.edgeCount, Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩) := by
      have hlast :
          deriv.Active
            (chain'.node
              ⟨chain'.edgeCount,
                Nat.lt_succ_of_le (Nat.le_refl chain'.edgeCount)⟩) := by
        simpa using chain'.last_active
      rw [hnode]
      exact hlast
    exact False.elim (hactive hinactive)
  · by_cases hle : chain'.edgeCount ≤ chain.edgeCount
    · exact hle
    have hlt : chain.edgeCount < chain'.edgeCount := Nat.lt_of_not_ge hle
    let l' : Fin chain'.edgeCount := ⟨chain.edgeCount, hlt⟩
    have hinactive :
        deriv.Inactive
          (chain'.node
            ⟨chain.edgeCount, Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩) := by
      have h := chain'.inactive_before_last l'
      simpa [current, l'] using h
    have hnode := node_eq_of_same_start_position chain chain'
      (Nat.le_refl chain.edgeCount) (Nat.le_of_lt hlt)
    have hactive :
        deriv.Active
          (chain'.node
            ⟨chain.edgeCount, Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩) := by
      have hlast :
          deriv.Active
            (chain.node
              ⟨chain.edgeCount,
                Nat.lt_succ_of_le (Nat.le_refl chain.edgeCount)⟩) := by
        simpa using chain.last_active
      rw [← hnode]
      exact hlast
    exact False.elim (hactive hinactive)

theorem next_val_lt_current {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    (chain.next l).val < (chain.current l).val := by
  rcases chain.link_order l with ⟨_k, hnext, _hcurrent, _hcut⟩
  dsimp [Prepath.paperIndex] at hnext
  exact Nat.succ_lt_succ_iff.mp hnext

/-- Lean-indexed form of `next_val_lt_current`. -/
theorem next_paperIndex_lt_current {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    T.paperIndex (chain.next l) < T.paperIndex (chain.current l) := by
  rcases chain.link_order l with ⟨_k, hnext, _hcurrent, _hcut⟩
  exact hnext

/--
Anti-monotonicity of values along chain positions: later tuple positions are no
greater than earlier tuple positions.
-/
theorem node_val_anti_mono {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) {a b : Fin (chain.edgeCount + 1)}
    (hab : a.val ≤ b.val) :
    (chain.node b).val ≤ (chain.node a).val := by
  have hstep :
      ∀ (n : Nat) (hn : n < chain.edgeCount),
        (chain.node ⟨n + 1, Nat.succ_lt_succ hn⟩).val ≤
          (chain.node ⟨n, Nat.lt_succ_of_lt hn⟩).val := by
    intro n hn
    let l : Fin chain.edgeCount := ⟨n, hn⟩
    have hcurrent :
        chain.current l = chain.node ⟨n, Nat.lt_succ_of_lt hn⟩ := by
      rfl
    have hnext :
        chain.next l = chain.node ⟨n + 1, Nat.succ_lt_succ hn⟩ := by
      rfl
    exact Nat.le_of_lt (by simpa [hcurrent, hnext] using chain.next_val_lt_current l)
  have hmono :
      ∀ (d : Nat) (startPos : Nat),
        (hle : startPos + d ≤ chain.edgeCount) →
          (chain.node ⟨startPos + d, Nat.lt_succ_of_le hle⟩).val ≤
            (chain.node
              ⟨startPos, Nat.lt_succ_of_le
                (Nat.le_trans (Nat.le_add_right startPos d) hle)⟩).val := by
    intro d
    induction d with
    | zero =>
        intro _startPos _hle
        exact Nat.le_refl _
    | succ d ih =>
        intro startPos hle
        have hprev_le : startPos + d ≤ chain.edgeCount := by omega
        have hprev_lt : startPos + d < chain.edgeCount := by omega
        have htail :
            (chain.node
              ⟨startPos + (d + 1), Nat.lt_succ_of_le hle⟩).val ≤
              (chain.node
                ⟨startPos + d, Nat.lt_succ_of_le hprev_le⟩).val := by
          have harg1 :
              (⟨startPos + d + 1, Nat.succ_lt_succ hprev_lt⟩ :
                Fin (chain.edgeCount + 1)) =
                ⟨startPos + (d + 1), Nat.lt_succ_of_le hle⟩ := by
            apply Fin.ext
            change startPos + d + 1 = startPos + (d + 1)
            omega
          have harg0 :
              (⟨startPos + d, Nat.lt_succ_of_lt hprev_lt⟩ :
                Fin (chain.edgeCount + 1)) =
                ⟨startPos + d, Nat.lt_succ_of_le hprev_le⟩ := by
            apply Fin.ext
            rfl
          simpa [harg1, harg0] using hstep (startPos + d) hprev_lt
        exact Nat.le_trans htail (ih startPos hprev_le)
  have hb_le : b.val ≤ chain.edgeCount := Nat.le_of_lt_succ b.isLt
  have hdiff : a.val + (b.val - a.val) = b.val := Nat.add_sub_of_le hab
  have hmono' :=
    hmono (b.val - a.val) a.val (by simpa [hdiff] using hb_le)
  have ha_arg :
      (⟨a.val, by omega⟩ : Fin (chain.edgeCount + 1)) = a := Fin.ext rfl
  have hb_arg :
      (⟨a.val + (b.val - a.val), Nat.lt_succ_of_le (by simpa [hdiff] using hb_le)⟩ :
        Fin (chain.edgeCount + 1)) = b := by
    apply Fin.ext
    exact hdiff
  simpa [ha_arg, hb_arg] using hmono'

/-- Lean-indexed form of `node_val_anti_mono`. -/
theorem node_paperIndex_anti_mono {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) {a b : Fin (chain.edgeCount + 1)}
    (hab : a.val ≤ b.val) :
    T.paperIndex (chain.node b) ≤ T.paperIndex (chain.node a) := by
  exact Nat.succ_le_succ (chain.node_val_anti_mono hab)

/--
If one chain link occurs earlier than another, the later current node is below
the earlier link's next node.
-/
theorem current_val_le_next_of_lt {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) {p l : Fin chain.edgeCount}
    (hpl : p.val < l.val) :
    (chain.current l).val ≤ (chain.next p).val := by
  have hpos :
      (⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩ :
          Fin (chain.edgeCount + 1)).val ≤
        (Fin.castSucc l : Fin (chain.edgeCount + 1)).val := by
    simpa using hpl
  have hmono :=
    chain.node_val_anti_mono
      (a := ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩)
      (b := Fin.castSucc l) hpos
  simpa [current, next] using hmono

/--
Global order consequence of Definition 6.3.1: every node
of a chain lies no greater than the first node.
-/
theorem node_val_le_first {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (pos : Fin (chain.edgeCount + 1)) :
    (chain.node pos).val ≤ chain.first.val := by
  have hnode :
      ∀ (n : Nat) (hn : n ≤ chain.edgeCount),
        (chain.node ⟨n, Nat.lt_succ_of_le hn⟩).val ≤
          chain.first.val := by
    intro n
    induction n with
    | zero =>
        intro _hn
        exact Nat.le_refl _
    | succ n ih =>
        intro hn
        have hn_lt : n < chain.edgeCount := Nat.lt_of_succ_le hn
        let l : Fin chain.edgeCount := ⟨n, hn_lt⟩
        have hcurrent :
            chain.current l =
              chain.node ⟨n, Nat.lt_succ_of_le (Nat.le_of_lt hn_lt)⟩ := by
          rfl
        have hnext :
            chain.next l =
              chain.node ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
          rfl
        have hstep :
            (chain.node ⟨n + 1, Nat.lt_succ_of_le hn⟩).val <
              (chain.node ⟨n, Nat.lt_succ_of_le (Nat.le_of_lt hn_lt)⟩).val := by
          simpa [hcurrent, hnext] using chain.next_val_lt_current l
        exact Nat.le_trans (Nat.le_of_lt hstep) (ih (Nat.le_of_lt hn_lt))
  have hpos : pos.val ≤ chain.edgeCount := Nat.le_of_lt_succ pos.isLt
  have hpos_eq :
      (⟨pos.val, Nat.lt_succ_of_le hpos⟩ : Fin (chain.edgeCount + 1)) = pos :=
    Fin.ext rfl
  simpa [hpos_eq] using hnode pos.val hpos

/--
Start-index form of `node_val_le_first`, matching the first component.
-/
theorem node_val_le_start {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (pos : Fin (chain.edgeCount + 1)) :
    (chain.node pos).val ≤ start.val := by
  simpa [chain.first_eq_start] using chain.node_val_le_first pos

/-- Lean-indexed form of `node_val_le_start`. -/
theorem node_paperIndex_le_start {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (pos : Fin (chain.edgeCount + 1)) :
    T.paperIndex (chain.node pos) ≤ T.paperIndex start := by
  exact Nat.succ_le_succ (chain.node_val_le_start pos)

/-- Non-final chain centers are bounded by the chain start. -/
theorem current_val_le_start {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    (chain.current l).val ≤ start.val := by
  simpa [current] using chain.node_val_le_start (Fin.castSucc l)

/-- Lean-indexed form of `current_val_le_start`. -/
theorem current_paperIndex_le_start {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    T.paperIndex (chain.current l) ≤ T.paperIndex start := by
  exact Nat.succ_le_succ (chain.current_val_le_start l)

/-- Every next node in a chain is strictly below the chain start. -/
theorem next_val_lt_start {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    (chain.next l).val < start.val := by
  exact Nat.lt_of_lt_of_le (chain.next_val_lt_current l)
    (chain.current_val_le_start l)

/-- Lean-indexed form of `next_val_lt_start`. -/
theorem next_paperIndex_lt_start {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    T.paperIndex (chain.next l) < T.paperIndex start := by
  exact Nat.succ_lt_succ (chain.next_val_lt_start l)

/--
Endpoint form: the active endpoint of a chain of cuts is
strictly below the inactive starting index.
-/
theorem last_val_lt_start {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) :
    chain.last.val < start.val := by
  have hle : chain.last.val ≤ start.val :=
    chain.node_val_le_start ⟨chain.edgeCount, Nat.lt_succ_self chain.edgeCount⟩
  have hne : chain.last.val ≠ start.val := by
    intro hval
    have hlast_start : chain.last = start := Fin.ext hval
    have hinactiveLast : deriv.Inactive chain.last := by
      rw [hlast_start]
      exact chain.first_inactive
    exact chain.last_active hinactiveLast
  exact Nat.lt_of_le_of_ne hle hne

/-- Lean-indexed form of `last_val_lt_start`. -/
theorem last_paperIndex_lt_start {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) :
    T.paperIndex chain.last < T.paperIndex start := by
  exact Nat.succ_lt_succ chain.last_val_lt_start

/--
Finite crossing fact for Lemma 6.3.3: any
natural value strictly above a later chain center but no greater than the start
is bracketed by an earlier chain link.
-/
theorem exists_previous_link_bracketing_of_between_start_current
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) {m : Nat}
    (hcurrent_m : (chain.current l).val < m)
    (hm_start : m ≤ start.val) :
    ∃ p : Fin chain.edgeCount,
      p.val < l.val ∧ (chain.next p).val < m ∧
        m ≤ (chain.current p).val := by
  have hcross :
      ∀ (n : Nat) (hn : n < chain.edgeCount),
        (chain.current ⟨n, hn⟩).val < m →
          m ≤ start.val →
            ∃ p : Fin chain.edgeCount,
              p.val < n ∧ (chain.next p).val < m ∧
                m ≤ (chain.current p).val := by
    intro n
    induction n with
    | zero =>
        intro _hn hcurrent_m hm_start
        have hstart_m : start.val < m := by
          have hfirst_m : chain.first.val < m := by
            simpa [current, first] using hcurrent_m
          simpa [chain.first_eq_start] using hfirst_m
        exact False.elim ((Nat.not_lt_of_ge hm_start) hstart_m)
    | succ n ih =>
        intro hn hcurrent_m hm_start
        have hn_prev : n < chain.edgeCount :=
          Nat.lt_trans (Nat.lt_succ_self n) hn
        let prev : Fin chain.edgeCount := ⟨n, hn_prev⟩
        let curr : Fin chain.edgeCount := ⟨n + 1, hn⟩
        by_cases hm_prev : m ≤ (chain.current prev).val
        · have hnext_m : (chain.next prev).val < m := by
            have hnext_eq : chain.next prev = chain.current curr := by
              rfl
            simpa [prev, curr, hnext_eq] using hcurrent_m
          exact ⟨prev, Nat.lt_succ_self n, hnext_m, hm_prev⟩
        · rcases ih hn_prev (Nat.lt_of_not_ge hm_prev) hm_start with
            ⟨p, hp, hnext_m, hm_current⟩
          exact
            ⟨p, Nat.lt_trans hp (Nat.lt_succ_self n), hnext_m, hm_current⟩
  exact hcross l.val l.isLt hcurrent_m hm_start

/--
Compatibility transfer used in Lemma 6.3.3:
if a right-side Cut is centered at a left-chain center and cuts are
right-compatible up to the chain start, its lower endpoint is the chain's next
node.
-/
theorem left_chain_rightCompatible_right_cut_lower_eq
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (l : Fin chain.edgeCount)
    {rightUpper rightLower : cd.circuit.right.1.Index}
    (hright :
      ContainsCut cd.rightDerivation
        (cd.circuit.right.1.paperIndex rightUpper)
        (cd.circuit.right.1.paperIndex (cd.rightIndex (chain.current l)))
        (cd.circuit.right.1.paperIndex rightLower)) :
    cd.circuit.left.1.paperIndex (chain.next l) =
      cd.circuit.right.1.paperIndex rightLower := by
  rcases chain.link_contains_cut l with ⟨_leftUpper, hleft⟩
  have hright' :
      ContainsCut cd.rightDerivation
        (cd.circuit.right.1.paperIndex rightUpper)
        (cd.circuit.left.1.paperIndex (chain.current l))
        (cd.circuit.right.1.paperIndex rightLower) := by
    simpa [cd.rightIndex_paperIndex (chain.current l)] using hright
  exact cd.rightCompatibleUpTo_cutLower_eq hcompat
    (chain.current_val_le_start l) hleft hright'

/--
Inactive-opposite-side setup for Lemma 6.3.3: if the corresponding right-side index is inactive,
right compatibility upgrades its Cut witness to a Cut to the left-chain next
node.
-/
theorem left_chain_rightCompatible_right_inactive_matching_cut
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (l : Fin chain.edgeCount)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    ∃ rightUpper rightLower : cd.circuit.right.1.Index,
      cd.circuit.right.1.paperIndex rightLower =
        cd.circuit.left.1.paperIndex (chain.next l) ∧
      ContainsCut cd.rightDerivation
        (cd.circuit.right.1.paperIndex rightUpper)
        (cd.circuit.right.1.paperIndex (cd.rightIndex (chain.current l)))
        (cd.circuit.left.1.paperIndex (chain.next l)) := by
  rcases
      ContForm.Routes.PathProperties.InactiveCuts.inactive_implies_containsCut_center
        cd.rightDerivation hrightInactive with
    ⟨rightUpper, rightLower, _hlower_center, _hcenter_upper, hrightCut⟩
  have hlower_left :
      cd.circuit.left.1.paperIndex (chain.next l) =
        cd.circuit.right.1.paperIndex rightLower :=
    left_chain_rightCompatible_right_cut_lower_eq cd chain hcompat l hrightCut
  exact
    ⟨rightUpper, rightLower, hlower_left.symm, by
      simpa [hlower_left] using hrightCut⟩

/--
Upper-endpoint bound used in Lemma 6.3.3: a
right Cut at a left-chain center cannot have upper endpoint strictly above the
right index of the chain start when that start is right-active.
-/
theorem left_chain_right_cut_upper_le_start_of_start_right_active
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (l : Fin chain.edgeCount)
    {rightUpper : cd.circuit.right.1.Index}
    (hrightCut :
      ContainsCut cd.rightDerivation
        (cd.circuit.right.1.paperIndex rightUpper)
        (cd.circuit.right.1.paperIndex (cd.rightIndex (chain.current l)))
        (cd.circuit.left.1.paperIndex (chain.next l))) :
    rightUpper.val ≤ (cd.rightIndex start).val := by
  exact Nat.le_of_not_gt (by
    intro hstart_upper_val
    have hstart_upper :
        cd.circuit.right.1.paperIndex (cd.rightIndex start) <
          cd.circuit.right.1.paperIndex rightUpper :=
      Nat.succ_lt_succ hstart_upper_val
    have hnext_start_left :
        cd.circuit.left.1.paperIndex (chain.next l) <
          cd.circuit.left.1.paperIndex start :=
      Nat.succ_lt_succ (chain.next_val_lt_start l)
    have hnext_start_right :
        cd.circuit.left.1.paperIndex (chain.next l) <
          cd.circuit.right.1.paperIndex (cd.rightIndex start) := by
      simpa [cd.rightIndex_paperIndex start] using hnext_start_left
    have hinactiveStart :
        cd.rightDerivation.Inactive (cd.rightIndex start) :=
      ContForm.Routes.PathProperties.InactiveCuts.containsCut_brackets_inactive
        hrightCut hnext_start_right hstart_upper
    exact hrightActiveStart hinactiveStart)

/--
Bracketing setup for Lemma 6.3.3: an inactive
right-side occurrence at a left-chain node supplies a matching right Cut whose
upper endpoint is bracketed by an earlier left-chain link.
-/
theorem left_chain_right_inactive_cut_upper_bracketed_by_previous_link
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (l : Fin chain.edgeCount)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    ∃ p : Fin chain.edgeCount,
      ∃ rightUpper rightLower : cd.circuit.right.1.Index,
        p.val < l.val ∧
          cd.circuit.right.1.paperIndex rightLower =
            cd.circuit.left.1.paperIndex (chain.next l) ∧
          ContainsCut cd.rightDerivation
            (cd.circuit.right.1.paperIndex rightUpper)
            (cd.circuit.right.1.paperIndex (cd.rightIndex (chain.current l)))
            (cd.circuit.left.1.paperIndex (chain.next l)) ∧
          (chain.next p).val < rightUpper.val ∧
            rightUpper.val ≤ (chain.current p).val := by
  rcases left_chain_rightCompatible_right_inactive_matching_cut
      cd chain hcompat l hrightInactive with
    ⟨rightUpper, rightLower, hrightLower, hrightCut⟩
  have hcenter_upper_paper :
      cd.circuit.right.1.paperIndex (cd.rightIndex (chain.current l)) <
        cd.circuit.right.1.paperIndex rightUpper :=
    (containsCut_order hrightCut).2
  have hcurrent_upper : (chain.current l).val < rightUpper.val := by
    have hpaper :
        cd.circuit.left.1.paperIndex (chain.current l) <
          cd.circuit.right.1.paperIndex rightUpper := by
      simpa [cd.rightIndex_paperIndex (chain.current l)] using hcenter_upper_paper
    exact Nat.succ_lt_succ_iff.mp hpaper
  have hupper_start : rightUpper.val ≤ start.val := by
    simpa [cd.rightIndex_val start]
      using left_chain_right_cut_upper_le_start_of_start_right_active
        cd chain hrightActiveStart l hrightCut
  rcases chain.exists_previous_link_bracketing_of_between_start_current l
      hcurrent_upper hupper_start with
    ⟨p, hp_l, hnext_upper, hupper_current⟩
  exact
    ⟨p, rightUpper, rightLower, hp_l, hrightLower, hrightCut, hnext_upper,
      hupper_current⟩

/--
Left-side Cut-occurrence witness for Lemma 6.3.3: if a right Cut upper endpoint is bracketed by an
earlier left-chain link, then the corresponding left index is itself cut to a
target no lower than the later chain center.
-/
theorem left_chain_bracketed_right_upper_containsCut_ge_current
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    {p l : Fin chain.edgeCount}
    (hpl : p.val < l.val)
    {rightUpper : cd.circuit.right.1.Index}
    (hnext_upper : (chain.next p).val < rightUpper.val)
    (hupper_current : rightUpper.val ≤ (chain.current p).val) :
    ∃ cutUpper cutLower : cd.Index,
      (chain.current l).val ≤ cutLower.val ∧
        ContainsCut cd.leftDerivation (cd.circuit.left.1.paperIndex cutUpper)
          (cd.circuit.left.1.paperIndex
            (Fin.cast cd.circuit.length_eq.symm rightUpper))
          (cd.circuit.left.1.paperIndex cutLower) := by
  let leftUpper : cd.Index := Fin.cast cd.circuit.length_eq.symm rightUpper
  have hcurrent_l_next_p : (chain.current l).val ≤ (chain.next p).val :=
    chain.current_val_le_next_of_lt hpl
  by_cases hupper_eq_current : rightUpper.val = (chain.current p).val
  · have hleftUpper_eq_current : leftUpper = chain.current p := by
      apply Fin.ext
      simpa [leftUpper] using hupper_eq_current
    rcases chain.link_contains_cut p with ⟨leftCutUpper, hleftCut⟩
    exact
      ⟨leftCutUpper, chain.next p, hcurrent_l_next_p, by
        simpa [leftUpper, hleftUpper_eq_current] using hleftCut⟩
  · have hupper_lt_current : rightUpper.val < (chain.current p).val :=
      Nat.lt_of_le_of_ne hupper_current hupper_eq_current
    rcases chain.link_contains_cut p with ⟨_outerUpper, houter⟩
    have hlower_inner :
        cd.circuit.left.1.paperIndex (chain.next p) <
          cd.circuit.left.1.paperIndex leftUpper := by
      exact Nat.succ_lt_succ (by simpa [leftUpper] using hnext_upper)
    have hinner_center :
        cd.circuit.left.1.paperIndex leftUpper <
          cd.circuit.left.1.paperIndex (chain.current p) := by
      exact Nat.succ_lt_succ (by simpa [leftUpper] using hupper_lt_current)
    rcases
        ContForm.Routes.PathProperties.Matryoshka.matryoshka_cuts_lower_side_indexed
          cd.leftDerivation houter hlower_inner hinner_center with
      ⟨_nestedUpper, nestedLower, _hupper_bound, hlower_bound,
        _hnestedLower_inner, _hinner_nestedUpper, hnested⟩
    have hnext_p_lower : (chain.next p).val ≤ nestedLower.val := by
      exact Nat.succ_le_succ_iff.mp hlower_bound
    have hcurrent_l_lower : (chain.current l).val ≤ nestedLower.val :=
      Nat.le_trans hcurrent_l_next_p hnext_p_lower
    exact ⟨_nestedUpper, nestedLower, hcurrent_l_lower, hnested⟩

/--
Cut-prefix data package for the first contradiction step of Lemma 6.3.3: if a right-side chain node is inactive, then the
matching right Cut and the bracketed left Cut expose the two prefix-ending Cut
occurrences used by the paper's active-prefix argument.
-/
theorem left_chain_right_inactive_cutPrefixData_pair
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (l : Fin chain.edgeCount)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    ∃ rightUpper : cd.circuit.right.1.Index,
      ∃ upper leftCutUpper cutLower : cd.Index,
        upper = Fin.cast cd.circuit.length_eq.symm rightUpper ∧
        (chain.next l).val < cutLower.val ∧
        upper.val ≤ start.val ∧
        Nonempty
          (CutPrefixData cd.leftDerivation
            (cd.circuit.left.1.paperIndex leftCutUpper)
            (cd.circuit.left.1.paperIndex upper)
            (cd.circuit.left.1.paperIndex cutLower)) ∧
        Nonempty
          (CutPrefixData cd.rightDerivation
            (cd.circuit.right.1.paperIndex rightUpper)
            (cd.circuit.right.1.paperIndex (cd.rightIndex (chain.current l)))
            (cd.circuit.left.1.paperIndex (chain.next l))) := by
  rcases left_chain_right_inactive_cut_upper_bracketed_by_previous_link
      cd chain hcompat hrightActiveStart l hrightInactive with
    ⟨p, rightUpper, _rightLower, hp_l, _hrightLower, hrightCut, hnext_upper,
      hupper_current⟩
  let upper : cd.Index := Fin.cast cd.circuit.length_eq.symm rightUpper
  rcases left_chain_bracketed_right_upper_containsCut_ge_current
      cd chain hp_l hnext_upper hupper_current with
    ⟨leftCutUpper, cutLower, hcurrent_l_lower, hleftCut⟩
  have hnext_cutLower : (chain.next l).val < cutLower.val :=
    Nat.lt_of_lt_of_le (chain.next_val_lt_current l) hcurrent_l_lower
  have hupper_start : upper.val ≤ start.val := by
    exact Nat.le_trans hupper_current (chain.current_val_le_start p)
  exact
    ⟨rightUpper, upper, leftCutUpper, cutLower, rfl, hnext_cutLower,
      hupper_start, containsCut_prefixData hleftCut,
      containsCut_prefixData hrightCut⟩

/--
Active-prefix inconsistency bridge for the first contradiction step of paper
Lemma 6.3.3: paired prefix-ending Cuts with a
strictly smaller right target produce an `InconsistentIndex` at their shared
upper endpoint.
-/
theorem cutPrefixData_pair_upper_inconsistent_of_target_lt
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {upper : cd.Index} {rightUpper : cd.circuit.right.1.Index}
    {leftCutK leftCutI rightCutJ rightCutI : Nat}
    (hupper_eq : upper = Fin.cast cd.circuit.length_eq.symm rightUpper)
    (hupper_before : cd.circuit.left.1.paperIndex upper < cd.circuit.length)
    (htarget : rightCutI < leftCutI)
    (leftData :
      CutPrefixData cd.leftDerivation leftCutK
        (cd.circuit.left.1.paperIndex upper) leftCutI)
    (rightData :
      CutPrefixData cd.rightDerivation
        (cd.circuit.right.1.paperIndex rightUpper) rightCutJ rightCutI) :
    cd.InconsistentIndex upper := by
  let rightCutDeriv :=
    Derivation.cut rightData.baseDeriv rightData.hij rightData.hjk
      rightData.hk rightData.hj rightData.hi rightData.hconsistent
  let pref :=
    cd.initialPrefixDerivation leftData.baseDeriv rightCutDeriv
      leftData.base_initialPrefix_final rightData.hprefix
  let hpref : pref.IsInitialPrefix cd :=
    cd.initialPrefixDerivation_isInitialPrefix leftData.baseDeriv rightCutDeriv
      leftData.base_initialPrefix_final rightData.hprefix
  let prefUpper : pref.Index := pref.prefixIndex hpref upper
  have hleftIdx : prefUpper = leftData.idxJ := by
    apply Fin.ext
    have hpaper : cd.circuit.left.1.paperIndex upper =
        leftData.base.paperIndex leftData.idxJ := leftData.cutJ_eq
    have hval : upper.val = leftData.idxJ.val :=
      Nat.succ.inj (by simpa [Prepath.paperIndex] using hpaper)
    simpa [prefUpper] using hval
  have hrightUpper_val : upper.val = rightUpper.val := by
    exact congrArg Fin.val hupper_eq
  have hrightIdxK_val : rightData.idxK.val = rightUpper.val := by
    have hpaper : cd.circuit.right.1.paperIndex rightUpper =
        rightData.base.paperIndex rightData.idxK := rightData.cutK_eq
    exact (Nat.succ.inj (by simpa [Prepath.paperIndex] using hpaper)).symm
  have hrightIdx :
      pref.rightIndex prefUpper = rightData.idxK := by
    apply Fin.ext
    calc
      (pref.rightIndex prefUpper).val = prefUpper.val := rfl
      _ = upper.val := rfl
      _ = rightUpper.val := hrightUpper_val
      _ = rightData.idxK.val := hrightIdxK_val.symm
  have hleftActive : pref.leftDerivation.Active prefUpper := by
    simpa [pref, prefUpper, hleftIdx] using
      ContForm.Routes.PathProperties.InactiveCuts.cutPrefixData_pre_cut_center_active
        leftData
  have hrightActive : pref.rightDerivation.Active (pref.rightIndex prefUpper) := by
    simpa [pref, prefUpper, hrightIdx, rightCutDeriv] using
      ContForm.Routes.PathProperties.InactiveCuts.cutPrefixData_final_cut_upper_active
        rightData
  have hdoublyActive : pref.DoublyActive prefUpper :=
    ⟨hleftActive, hrightActive⟩
  have hleftShape :
      pref.leftTime prefUpper =
        ⋊ leftCutI
          (leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ)
              leftData.tk)) := by
    have hshape := leftData.hj
    simpa [pref, prefUpper, hleftIdx, CircuitDerivation.leftTime,
      leftData.cutI_eq] using hshape
  have hrightShape :
      pref.rightTime prefUpper = ↱ rightCutI rightData.tk := by
    have hshape :
        (Derivation.root rightCutDeriv).get rightData.idxK =
          ↱ (rightData.base.paperIndex rightData.idxI)
            rightData.tk := by
      simp [rightCutDeriv, Derivation.root, Prepath.replace_get_same]
    simpa [pref, prefUpper, hrightIdx, CircuitDerivation.rightTime,
      rightCutDeriv, rightData.cutI_eq] using hshape
  have hbeforePref : pref.circuit.left.1.paperIndex prefUpper < pref.circuit.length := by
    have hpaper := pref.prefixIndex_paperIndex hpref upper
    have hlen : pref.circuit.length = cd.circuit.length := by
      simpa [Circuit.length] using hpref.1.length_eq
    rw [hpaper, hlen]
    exact hupper_before
  have hctrl :=
    pref.controller_eq_before_last prefUpper hbeforePref
  have hrightLe :
      (↱ rightCutI rightData.tk) ≼ (pref.rightTime prefUpper) := by
    rw [hrightShape]
    exact le_refl _
  have hcontrRightLeft :
      (pref.rightTime prefUpper) 🗲 (pref.leftTime prefUpper) := by
    exact
      ContForm.Routes.PathProperties.Compatibility.contradicts_of_nextIndex_le_and_cutMe_eq
        htarget hrightLe hleftShape hctrl.symm
  refine ⟨pref, hpref, ?_⟩
  exact ⟨hdoublyActive, contradicts_symm hcontrRightLeft⟩

/--
Active-prefix inconsistency component for Lemma 6.3.3: if a left-chain node is inactive on the right,
then the paper's paired active-prefix construction yields an
`InconsistentIndex` at or below the chain start.
-/
theorem left_chain_right_inactive_upper_inconsistentIndex
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (l : Fin chain.edgeCount)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    ∃ upper : cd.Index, upper.val ≤ start.val ∧ cd.InconsistentIndex upper := by
  rcases left_chain_right_inactive_cutPrefixData_pair
      cd chain hcompat hrightActiveStart l hrightInactive with
    ⟨rightUpper, upper, leftCutUpper, cutLower, hupper_eq, hnext_cutLower,
      hupper_start, ⟨leftData⟩, ⟨rightData⟩⟩
  have hstart_before :
      cd.circuit.left.1.paperIndex start < cd.circuit.length := by
    let firstLink : Fin chain.edgeCount := ⟨0, chain.edgeCount_pos⟩
    rcases chain.link_order firstLink with
      ⟨linkUpper, _hnext_current, hcurrent_upper, _hcut⟩
    have hcurrent :
        cd.circuit.left.1.paperIndex (chain.current firstLink) <
          cd.circuit.length := by
      exact Nat.lt_of_lt_of_le hcurrent_upper
        (Nat.succ_le_of_lt linkUpper.isLt)
    have hcurrent_eq : chain.current firstLink = start := by
      simpa [current, first] using chain.first_eq_start
    simpa [Circuit.length, hcurrent_eq] using hcurrent
  have hupper_before :
      cd.circuit.left.1.paperIndex upper < cd.circuit.length := by
    have hpaper_le :
        cd.circuit.left.1.paperIndex upper ≤ cd.circuit.left.1.paperIndex start :=
      Nat.succ_le_succ hupper_start
    exact Nat.lt_of_le_of_lt hpaper_le hstart_before
  have htarget :
      cd.circuit.left.1.paperIndex (chain.next l) <
        cd.circuit.left.1.paperIndex cutLower := by
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ hnext_cutLower
  have hinconsistent :
      cd.InconsistentIndex upper :=
    cutPrefixData_pair_upper_inconsistent_of_target_lt
      cd hupper_eq hupper_before htarget leftData rightData
  exact ⟨upper, hupper_start, hinconsistent⟩

/--
Leastness component for Lemma 6.3.3: the
active-prefix contradiction produced from an inactive opposite-side chain node
must occur at the least inconsistent start index. This is the paper's
`k' = i` step, not the full chain-active conclusion.
-/
theorem left_chain_right_inactive_upper_eq_start_of_least_inconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound start : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound start)
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (l : Fin chain.edgeCount)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    ∃ upper : cd.Index,
      upper = start ∧ cd.InconsistentIndex upper := by
  rcases left_chain_right_inactive_upper_inconsistentIndex
      cd chain hcompat hrightActiveStart l hrightInactive with
    ⟨upper, hupper_start, hinconsistent⟩
  have hnot_lt_start : ¬ upper.val < start.val := by
    intro hlt
    exact cd.leastInconsistentAtOrBelow_no_smaller hleast upper hlt hinconsistent
  have hstart_upper : start.val ≤ upper.val := Nat.le_of_not_gt hnot_lt_start
  have hupper_eq : upper = start := by
    apply Fin.ext
    exact Nat.le_antisymm hupper_start hstart_upper
  exact ⟨upper, hupper_eq, hinconsistent⟩

/--
Bracketing component for Lemma 6.3.3: after
leastness forces the inactive right-side Cut's upper endpoint to be the chain
start, any later inactive chain node makes the second chain node inactive on
the right. This is a step toward the paper's `l = 2` conclusion, not the full
chain-active theorem.
-/
theorem left_chain_later_right_inactive_forces_second_right_inactive
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound start : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound start)
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (l : Fin chain.edgeCount) (hpos : 0 < l.val)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    cd.rightDerivation.Inactive
      (cd.rightIndex (chain.next ⟨0, chain.edgeCount_pos⟩)) := by
  let firstLink : Fin chain.edgeCount := ⟨0, chain.edgeCount_pos⟩
  rcases left_chain_right_inactive_cutPrefixData_pair
      cd chain hcompat hrightActiveStart l hrightInactive with
    ⟨rightUpper, upper, leftCutUpper, cutLower, hupper_eq, hnext_cutLower,
      hupper_start, ⟨leftData⟩, ⟨rightData⟩⟩
  have hstart_before :
      cd.circuit.left.1.paperIndex start < cd.circuit.length := by
    rcases chain.link_order firstLink with
      ⟨linkUpper, _hnext_current, hcurrent_upper, _hcut⟩
    have hcurrent :
        cd.circuit.left.1.paperIndex (chain.current firstLink) <
          cd.circuit.length := by
      exact Nat.lt_of_lt_of_le hcurrent_upper
        (Nat.succ_le_of_lt linkUpper.isLt)
    have hcurrent_eq : chain.current firstLink = start := by
      simpa [current, first, firstLink] using chain.first_eq_start
    simpa [Circuit.length, hcurrent_eq] using hcurrent
  have hupper_before :
      cd.circuit.left.1.paperIndex upper < cd.circuit.length := by
    have hpaper_le :
        cd.circuit.left.1.paperIndex upper ≤ cd.circuit.left.1.paperIndex start :=
      Nat.succ_le_succ hupper_start
    exact Nat.lt_of_le_of_lt hpaper_le hstart_before
  have htarget :
      cd.circuit.left.1.paperIndex (chain.next l) <
        cd.circuit.left.1.paperIndex cutLower := by
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ hnext_cutLower
  have hinconsistent :
      cd.InconsistentIndex upper :=
    cutPrefixData_pair_upper_inconsistent_of_target_lt
      cd hupper_eq hupper_before htarget leftData rightData
  have hnot_lt_start : ¬ upper.val < start.val := by
    intro hlt
    exact cd.leastInconsistentAtOrBelow_no_smaller hleast upper hlt hinconsistent
  have hstart_upper : start.val ≤ upper.val := Nat.le_of_not_gt hnot_lt_start
  have hupper_start_eq : upper = start := by
    apply Fin.ext
    exact Nat.le_antisymm hupper_start hstart_upper
  have hrightUpper_start : rightUpper = cd.rightIndex start := by
    apply Fin.ext
    have hcast_val :
        (Fin.cast cd.circuit.length_eq.symm rightUpper).val = start.val := by
      rw [← hupper_eq, hupper_start_eq]
    simpa [CircuitDerivation.rightIndex] using hcast_val
  let rightCutDeriv :=
    Derivation.cut rightData.baseDeriv rightData.hij rightData.hjk
      rightData.hk rightData.hj rightData.hi rightData.hconsistent
  have hcutHere :
      ContainsCut rightCutDeriv
        (rightData.base.paperIndex rightData.idxK)
        (rightData.base.paperIndex rightData.idxJ)
        (rightData.base.paperIndex rightData.idxI) := by
    exact ContainsCut.here rightData.baseDeriv rightData.hij rightData.hjk
      rightData.hk rightData.hj rightData.hi rightData.hconsistent
  have hcutFinalRaw :
      ContainsCut cd.rightDerivation
        (cd.circuit.right.1.paperIndex rightUpper)
        (cd.circuit.right.1.paperIndex (cd.rightIndex (chain.current l)))
        (cd.circuit.left.1.paperIndex (chain.next l)) := by
    have hcutLater :=
      containsCut_of_initialPrefix rightData.hprefix hcutHere
    simpa [rightCutDeriv, rightData.cutK_eq, rightData.cutJ_eq,
      rightData.cutI_eq] using hcutLater
  have hcutFinal :
      ContainsCut cd.rightDerivation
        (cd.circuit.right.1.paperIndex (cd.rightIndex start))
        (cd.circuit.right.1.paperIndex (cd.rightIndex (chain.current l)))
        (cd.circuit.left.1.paperIndex (chain.next l)) := by
    simpa [hrightUpper_start] using hcutFinalRaw
  have hnext_l_second_left :
      cd.circuit.left.1.paperIndex (chain.next l) <
        cd.circuit.left.1.paperIndex (chain.next firstLink) := by
    have hcurrent_second : (chain.current l).val ≤ (chain.next firstLink).val :=
      chain.current_val_le_next_of_lt (p := firstLink) (l := l) hpos
    exact Nat.succ_lt_succ
      (Nat.lt_of_lt_of_le (chain.next_val_lt_current l) hcurrent_second)
  have hnext_l_second_right :
      cd.circuit.left.1.paperIndex (chain.next l) <
        cd.circuit.right.1.paperIndex (cd.rightIndex (chain.next firstLink)) := by
    simpa [cd.rightIndex_paperIndex (chain.next firstLink)] using
      hnext_l_second_left
  have hsecond_start_right :
      cd.circuit.right.1.paperIndex (cd.rightIndex (chain.next firstLink)) <
        cd.circuit.right.1.paperIndex (cd.rightIndex start) := by
    have hsecond_start_left :
        cd.circuit.left.1.paperIndex (chain.next firstLink) <
          cd.circuit.left.1.paperIndex start :=
      chain.next_paperIndex_lt_start firstLink
    simpa [cd.rightIndex_paperIndex (chain.next firstLink),
      cd.rightIndex_paperIndex start] using hsecond_start_left
  exact
    ContForm.Routes.PathProperties.InactiveCuts.containsCut_brackets_inactive
      hcutFinal hnext_l_second_right hsecond_start_right

/--
Active-prefix bridge for Lemma 6.3.3: adjacent Cut-prefix data, where the lower endpoint
of the left Cut is the center of the right Cut and the left center is the right
upper endpoint, makes the shared lower/center index inconsistent by the
paper's second active-prefix contradiction.
-/
theorem cutPrefixData_adjacent_cuts_lower_center_inconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {shared : cd.Index}
    {leftCutK leftCenter rightCutK rightLower : Nat}
    (leftData :
      CutPrefixData cd.leftDerivation leftCutK leftCenter
        (cd.circuit.left.1.paperIndex shared))
    (rightData :
      CutPrefixData cd.rightDerivation rightCutK
        (cd.circuit.left.1.paperIndex shared) rightLower) :
    leftCenter = rightCutK →
    cd.InconsistentIndex shared := by
  intro hcenter_rightUpper
  let leftCutDeriv :=
    Derivation.cut leftData.baseDeriv leftData.hij leftData.hjk
      leftData.hk leftData.hj leftData.hi leftData.hconsistent
  let pref :=
    cd.initialPrefixDerivation leftCutDeriv rightData.baseDeriv
      leftData.hprefix rightData.base_initialPrefix_final
  have hpref : pref.IsInitialPrefix cd :=
    cd.initialPrefixDerivation_isInitialPrefix leftCutDeriv
      rightData.baseDeriv leftData.hprefix rightData.base_initialPrefix_final
  let prefShared : pref.Index := pref.prefixIndex hpref shared
  have hshared_left : prefShared = leftData.idxI := by
    apply Fin.ext
    exact Nat.succ.inj (by
      calc
        pref.circuit.left.1.paperIndex prefShared =
            cd.circuit.left.1.paperIndex shared := by
              simpa [prefShared] using pref.prefixIndex_paperIndex hpref shared
        _ = leftData.base.paperIndex leftData.idxI := leftData.cutI_eq)
  have hrightShared :
      pref.rightIndex leftData.idxI = rightData.idxJ := by
    apply Fin.ext
    exact Nat.succ.inj (by
      calc
        pref.circuit.right.1.paperIndex (pref.rightIndex leftData.idxI) =
            pref.circuit.left.1.paperIndex leftData.idxI :=
              pref.rightIndex_paperIndex leftData.idxI
        _ = leftData.base.paperIndex leftData.idxI := by
              rfl
        _ = cd.circuit.left.1.paperIndex shared := leftData.cutI_eq.symm
        _ = rightData.base.paperIndex rightData.idxJ := rightData.cutJ_eq)
  have hrightCenterUpper :
      pref.rightIndex leftData.idxJ = rightData.idxK := by
    apply Fin.ext
    exact Nat.succ.inj (by
      calc
        pref.circuit.right.1.paperIndex (pref.rightIndex leftData.idxJ) =
            pref.circuit.left.1.paperIndex leftData.idxJ :=
              pref.rightIndex_paperIndex leftData.idxJ
        _ = leftData.base.paperIndex leftData.idxJ := by
              rfl
        _ = leftCenter := leftData.cutJ_eq.symm
        _ = rightCutK := hcenter_rightUpper
        _ = rightData.base.paperIndex rightData.idxK := rightData.cutK_eq)
  have hshared_before :
      pref.circuit.left.1.paperIndex leftData.idxI < pref.circuit.length := by
    have hlt : leftData.idxI.val + 1 < leftData.base.length :=
      Nat.lt_of_le_of_lt (Nat.succ_le_of_lt leftData.hij) leftData.idxJ.isLt
    simpa [pref, leftCutDeriv, Circuit.length, Prepath.paperIndex] using hlt
  have hcenter_before :
      pref.circuit.left.1.paperIndex leftData.idxJ < pref.circuit.length := by
    have hlt : leftData.idxJ.val + 1 < leftData.base.length :=
      Nat.lt_of_le_of_lt (Nat.succ_le_of_lt leftData.hjk) leftData.idxK.isLt
    simpa [pref, leftCutDeriv, Circuit.length, Prepath.paperIndex] using hlt
  let leftInner : Time :=
    leftData.tj # (⋉ (leftData.base.paperIndex leftData.idxJ) leftData.tk)
  let rightInner : Time :=
    rightData.tj # (⋉ (rightData.base.paperIndex rightData.idxJ) rightData.tk)
  have hidxI_ne_K : leftData.idxI ≠ leftData.idxK := by
    intro h
    have hlt : leftData.idxI.val < leftData.idxK.val :=
      Nat.lt_trans leftData.hij leftData.hjk
    exact (Nat.ne_of_lt hlt) (congrArg Fin.val h)
  have hidxJ_ne_K : leftData.idxJ ≠ leftData.idxK := by
    intro h
    exact (Nat.ne_of_lt leftData.hjk) (congrArg Fin.val h)
  have hleftSharedShape :
      pref.leftTime leftData.idxI =
        leftData.ti # (⋊ (leftData.base.paperIndex leftData.idxI) leftInner) := by
    change (Derivation.root leftCutDeriv).get leftData.idxI =
      leftData.ti # (⋊ (leftData.base.paperIndex leftData.idxI) leftInner)
    simp [leftCutDeriv, Derivation.root,
      Prepath.replace_get_ne leftData.base hidxI_ne_K, leftData.hi, leftInner]
  have hrightSharedShape :
      pref.rightTime leftData.idxI =
        ⋊ (rightData.base.paperIndex rightData.idxI) rightInner := by
    change rightData.base.get (pref.rightIndex leftData.idxI) =
      ⋊ (rightData.base.paperIndex rightData.idxI) rightInner
    rw [hrightShared]
    simpa [rightInner] using rightData.hj
  have hleftCenterShape :
      pref.leftTime leftData.idxJ =
        ⋊ (leftData.base.paperIndex leftData.idxI) leftInner := by
    change (Derivation.root leftCutDeriv).get leftData.idxJ =
      ⋊ (leftData.base.paperIndex leftData.idxI) leftInner
    simp [leftCutDeriv, Derivation.root,
      Prepath.replace_get_ne leftData.base hidxJ_ne_K, leftData.hj, leftInner]
  have hrightUpperShape :
      pref.rightTime leftData.idxJ =
        ⋉ (rightData.base.paperIndex rightData.idxJ)
          rightData.tk := by
    change rightData.base.get (pref.rightIndex leftData.idxJ) =
      ⋉ (rightData.base.paperIndex rightData.idxJ) rightData.tk
    rw [hrightCenterUpper]
    exact rightData.hk
  have hsharedCtrl :
      controller (pref.leftTime leftData.idxI) =
        controller (pref.rightTime leftData.idxI) :=
    pref.controller_eq_before_last leftData.idxI hshared_before
  have hcenterCtrl :
      controller (pref.leftTime leftData.idxJ) =
        controller (pref.rightTime leftData.idxJ) :=
    pref.controller_eq_before_last leftData.idxJ hcenter_before
  have hsubCtrl :
      controller leftInner = controller rightData.tk := by
    have hcutCtrl :
        controller
            (⋊ (leftData.base.paperIndex leftData.idxI) leftInner) =
          controller
            (⋉ (rightData.base.paperIndex rightData.idxJ)
              rightData.tk) := by
      simpa [hleftCenterShape, hrightUpperShape] using hcenterCtrl
    calc
      controller leftInner =
          controller
            (⋊ (leftData.base.paperIndex leftData.idxI)
              leftInner) := by
            exact ((⋊ (leftData.base.paperIndex leftData.idxI)).controller_preserving
                leftInner).symm
      _ = controller
            (⋉ (rightData.base.paperIndex rightData.idxJ)
              rightData.tk) := hcutCtrl
      _ = controller rightData.tk :=
            (⋉ (rightData.base.paperIndex rightData.idxJ)).controller_preserving
                rightData.tk
  have hti_tj :
      controller leftData.ti =
        controller rightData.tj := by
    have hrootCtrl :
        controller
            (leftData.ti # (⋊ (leftData.base.paperIndex leftData.idxI)
                leftInner)) =
          controller
            (⋊ (rightData.base.paperIndex rightData.idxI)
              rightInner) := by
      simpa [hleftSharedShape, hrightSharedShape] using hsharedCtrl
    calc
      controller leftData.ti =
          controller
            (leftData.ti # (⋊ (leftData.base.paperIndex leftData.idxI)
                leftInner)) := by
            exact (controller_preserving leftData.ti
              (⋊ (leftData.base.paperIndex leftData.idxI)
                leftInner)).symm
      _ = controller
            (⋊ (rightData.base.paperIndex rightData.idxI)
              rightInner) := hrootCtrl
      _ = controller rightInner :=
            (⋊ (rightData.base.paperIndex rightData.idxI)).controller_preserving
                rightInner
      _ = controller rightData.tj :=
            controller_preserving rightData.tj
              (⋉ (rightData.base.paperIndex rightData.idxJ)
                rightData.tk)
  have hsharedTarget :
      leftData.base.paperIndex leftData.idxI =
        rightData.base.paperIndex rightData.idxJ := by
    exact leftData.cutI_eq.symm.trans rightData.cutJ_eq
  have hsubContr :
      (⋊ (leftData.base.paperIndex leftData.idxI) leftInner) 🗲 (⋉ (rightData.base.paperIndex rightData.idxJ)
          rightData.tk) := by
    have hraw :
        (⋊ (leftData.base.paperIndex leftData.idxI) leftInner) 🗲 (⋉ (leftData.base.paperIndex leftData.idxI)
            rightData.tk) :=
      cutMe_contradicts_cutYou
        (leftData.base.paperIndex leftData.idxI) hsubCtrl
    simpa [hsharedTarget] using hraw
  have hattestedContr :
      (leftData.ti # (⋊ (leftData.base.paperIndex leftData.idxI) leftInner)) 🗲 (rightData.tj # (⋉ (rightData.base.paperIndex rightData.idxJ)
            rightData.tk)) := by
    exact contradiction_preserving hti_tj hsubContr.1 hsubContr
  have hrightLe :
      (rightData.tj # (⋉ (rightData.base.paperIndex rightData.idxJ)
            rightData.tk)) ≼ (⋊ (rightData.base.paperIndex rightData.idxI)
          rightInner) := by
    exact
      (⋊ (rightData.base.paperIndex rightData.idxI)).expansive rightInner
  have hcontrShared :
      (pref.leftTime leftData.idxI) 🗲 (pref.rightTime leftData.idxI) := by
    have hcontr' := contradicts_of_le_right hrightLe hattestedContr
    simpa [hleftSharedShape, hrightSharedShape, rightInner] using hcontr'
  have hleftActive :
      pref.leftDerivation.Active leftData.idxI := by
    have hactive :=
      (ContForm.Routes.PathProperties.InactiveCuts.final_cut_endpoints_active
        leftData.baseDeriv leftData.hij leftData.hjk leftData.hk leftData.hj
        leftData.hi leftData.hconsistent).2
    simpa [pref, leftCutDeriv] using hactive
  have hrightActive :
      pref.rightDerivation.Active (pref.rightIndex leftData.idxI) := by
    have hactive :=
      ContForm.Routes.PathProperties.InactiveCuts.cutPrefixData_pre_cut_center_active
        rightData
    simpa [pref, hrightShared] using hactive
  refine ⟨pref, hpref, ?_, ?_⟩
  · simpa [prefShared, hshared_left] using And.intro hleftActive hrightActive
  · simpa [prefShared, hshared_left] using hcontrShared

/--
Second active-prefix contradiction for Lemma 6.3.3: under leastness, a later inactive right-side
chain node makes the second chain node an inconsistent index.
-/
theorem left_chain_later_right_inactive_second_inconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound start : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound start)
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (l : Fin chain.edgeCount) (hpos : 0 < l.val)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    cd.InconsistentIndex (chain.next ⟨0, chain.edgeCount_pos⟩) := by
  let firstLink : Fin chain.edgeCount := ⟨0, chain.edgeCount_pos⟩
  have htwo : 1 < chain.edgeCount := by omega
  let secondLink : Fin chain.edgeCount := ⟨1, htwo⟩
  have hsecond_current : chain.current secondLink = chain.next firstLink := by
    rfl
  have hsecondInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current secondLink)) := by
    have hsecond :=
      left_chain_later_right_inactive_forces_second_right_inactive
        cd hleast chain hcompat hrightActiveStart l hpos hrightInactive
    simpa [hsecond_current] using hsecond
  have hfirst_current : chain.current firstLink = start := by
    simpa [current, first, firstLink] using chain.first_eq_start
  rcases chain.link_contains_cut firstLink with ⟨leftUpper, hleftCut⟩
  have hleftCutStart :
      ContainsCut cd.leftDerivation
        (cd.circuit.left.1.paperIndex leftUpper)
        (cd.circuit.left.1.paperIndex start)
        (cd.circuit.left.1.paperIndex (chain.next firstLink)) := by
    simpa [hfirst_current] using hleftCut
  rcases containsCut_prefixData hleftCutStart with ⟨firstLeftData⟩
  rcases left_chain_right_inactive_cutPrefixData_pair
      cd chain hcompat hrightActiveStart secondLink hsecondInactive with
    ⟨rightUpper, upper, _leftCutUpper, cutLower, hupper_eq, hnext_cutLower,
      hupper_start, ⟨leftDataForUpper⟩, ⟨rightData⟩⟩
  have hstart_before :
      cd.circuit.left.1.paperIndex start < cd.circuit.length := by
    rcases chain.link_order firstLink with
      ⟨linkUpper, _hnext_current, hcurrent_upper, _hcut⟩
    have hcurrent :
        cd.circuit.left.1.paperIndex (chain.current firstLink) <
          cd.circuit.length := by
      exact Nat.lt_of_lt_of_le hcurrent_upper
        (Nat.succ_le_of_lt linkUpper.isLt)
    simpa [Circuit.length, hfirst_current] using hcurrent
  have hupper_before :
      cd.circuit.left.1.paperIndex upper < cd.circuit.length := by
    have hpaper_le :
        cd.circuit.left.1.paperIndex upper ≤ cd.circuit.left.1.paperIndex start :=
      Nat.succ_le_succ hupper_start
    exact Nat.lt_of_le_of_lt hpaper_le hstart_before
  have htarget :
      cd.circuit.left.1.paperIndex (chain.next secondLink) <
        cd.circuit.left.1.paperIndex cutLower := by
    simpa [Prepath.paperIndex] using Nat.succ_lt_succ hnext_cutLower
  have hinconsistentUpper :
      cd.InconsistentIndex upper :=
    cutPrefixData_pair_upper_inconsistent_of_target_lt
      cd hupper_eq hupper_before htarget leftDataForUpper rightData
  have hnot_lt_start : ¬ upper.val < start.val := by
    intro hlt
    exact cd.leastInconsistentAtOrBelow_no_smaller hleast upper hlt
      hinconsistentUpper
  have hstart_upper : start.val ≤ upper.val := Nat.le_of_not_gt hnot_lt_start
  have hupper_start_eq : upper = start := by
    apply Fin.ext
    exact Nat.le_antisymm hupper_start hstart_upper
  have hcenter_rightUpper :
      cd.circuit.left.1.paperIndex start =
        cd.circuit.right.1.paperIndex rightUpper := by
    have hval : start.val = rightUpper.val := by
      have hcast_val :
          (Fin.cast cd.circuit.length_eq.symm rightUpper).val = start.val := by
        rw [← hupper_eq, hupper_start_eq]
      exact hcast_val.symm
    simp [Prepath.paperIndex, hval]
  exact
    cutPrefixData_adjacent_cuts_lower_center_inconsistent
      cd (shared := chain.next firstLink) firstLeftData
      (by
        simpa [hsecond_current, cd.rightIndex_paperIndex (chain.next firstLink)]
          using rightData)
      hcenter_rightUpper

/--
Lemma 6.3.3. Take the chain's derivation to be the paper's `Π` (left) and the
other to be `Π'` (right), with `start` (the paper's `i`) the least inconsistent
index — hence active in `Π'` (`hrightActiveStart`) and, since it starts a chain of
cuts, inactive in `Π` — and cuts right-compatible up to `start`. Then the chain
nodes `i₁,…,i_{n-1}` — those that clause (2) of Definition 6.3.1 declares inactive
in `Π` — are all active in `Π'`. This is Lemma 6.3.3's conclusion verbatim. (`iₙ`,
the chain's endpoint, is active in `Π` by clause (3), Definition 6.3.1(3); it is
not part of Lemma 6.3.3's conclusion.)
-/
theorem left_chain_right_active_of_least_inconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound start : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound start)
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start)) :
    ∀ l : Fin chain.edgeCount,
      cd.rightDerivation.Active (cd.rightIndex (chain.current l)) := by
  intro l hrightInactive
  let firstLink : Fin chain.edgeCount := ⟨0, chain.edgeCount_pos⟩
  by_cases hzero : l.val = 0
  · have hl_eq : l = firstLink := Fin.ext hzero
    have hcurrent_start : chain.current l = start := by
      rw [hl_eq]
      simpa [current, first, firstLink] using chain.first_eq_start
    exact hrightActiveStart (by simpa [hcurrent_start] using hrightInactive)
  · have hpos : 0 < l.val := Nat.pos_of_ne_zero hzero
    have hinconsistentSecond :
        cd.InconsistentIndex (chain.next firstLink) :=
      left_chain_later_right_inactive_second_inconsistent
        cd hleast chain hcompat hrightActiveStart l hpos hrightInactive
    exact
      cd.leastInconsistentAtOrBelow_no_smaller hleast (chain.next firstLink)
        (chain.next_val_lt_start firstLink) hinconsistentSecond

/--
Paper Lemma 6.3.3, paper-hypothesis form: the paper assumes
the least inconsistent index is active. Since the chain makes it left-inactive,
that activity forces right-activity at the start.
-/
theorem left_chain_right_active_of_least_inconsistent_active
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {bound start : cd.Index}
    (hleast : cd.LeastInconsistentAtOrBelow bound start)
    (hactiveStart : cd.Active start)
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start) :
    ∀ l : Fin chain.edgeCount,
      cd.rightDerivation.Active (cd.rightIndex (chain.current l)) := by
  have hrightActiveStart :
      cd.rightDerivation.Active (cd.rightIndex start) := by
    rcases hactiveStart with hleftActive | hrightActive
    · exact False.elim (hleftActive chain.first_inactive)
    · exact hrightActive
  exact
    left_chain_right_active_of_least_inconsistent
      cd hleast chain hcompat hrightActiveStart

/--
Swapped-side chain-active theorem: applying the left-chain theorem to
`cd.swap` gives the right-chain/left-active form when leastness is stated for
the swapped circuit derivation.
-/
theorem right_chain_left_active_of_least_inconsistent
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {bound start : cd.circuit.right.1.Index}
    (hleast : cd.swap.LeastInconsistentAtOrBelow bound start)
    (chain : ChainOfCuts cd.rightDerivation start)
    (hcompat : cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm start))
    (hleftActiveStart :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm start)) :
    ∀ l : Fin chain.edgeCount,
      cd.leftDerivation.Active
        (Fin.cast cd.circuit.length_eq.symm (chain.current l)) := by
  have hcompatSwap : cd.swap.RightCompatibleUpTo start :=
    cd.swap_rightCompatibleUpTo hcompat
  have hleftStartSwap :
      cd.swap.rightDerivation.Active (cd.swap.rightIndex start) := by
    simpa [CircuitDerivation.swap, cd.swap_rightIndex start] using hleftActiveStart
  have hactiveSwap :
      ∀ l : Fin chain.edgeCount,
        cd.swap.rightDerivation.Active (cd.swap.rightIndex (chain.current l)) :=
    left_chain_right_active_of_least_inconsistent
      cd.swap hleast chain hcompatSwap hleftStartSwap
  intro l
  simpa [CircuitDerivation.swap, cd.swap_rightIndex (chain.current l)]
    using hactiveSwap l

/--
Conditional chain-active consequence: if no
inconsistent index exists at or below the chain start, then every non-final
node in a left chain is active on the right side.
-/
theorem left_chain_right_active_of_no_inconsistentIndex
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (hnoInconsistent :
      ∀ upper : cd.Index, upper.val ≤ start.val → ¬ cd.InconsistentIndex upper) :
    ∀ l : Fin chain.edgeCount,
      cd.rightDerivation.Active (cd.rightIndex (chain.current l)) := by
  intro l hrightInactive
  rcases left_chain_right_inactive_upper_inconsistentIndex
      cd chain hcompat hrightActiveStart l hrightInactive with
    ⟨upper, hupper_start, hinconsistent⟩
  exact hnoInconsistent upper hupper_start hinconsistent

/--
Conditional swapped-side chain-active consequence:
if no inconsistent index exists at or below the right-chain start, then every
non-final node in a right chain is active on the left side.
-/
theorem right_chain_left_active_of_no_inconsistentIndex
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start)
    (hcompat : cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm start))
    (hleftActiveStart :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm start))
    (hnoInconsistent :
      ∀ upper : cd.circuit.right.1.Index, upper.val ≤ start.val →
        ¬ cd.InconsistentIndex (Fin.cast cd.circuit.length_eq.symm upper)) :
    ∀ l : Fin chain.edgeCount,
      cd.leftDerivation.Active
        (Fin.cast cd.circuit.length_eq.symm (chain.current l)) := by
  have hcompatSwap : cd.swap.RightCompatibleUpTo start :=
    cd.swap_rightCompatibleUpTo hcompat
  have hleftStartSwap :
      cd.swap.rightDerivation.Active (cd.swap.rightIndex start) := by
    simpa [CircuitDerivation.swap, cd.swap_rightIndex start] using hleftActiveStart
  have hnoInconsistentSwap :
      ∀ upper : cd.swap.Index, upper.val ≤ start.val →
        ¬ cd.swap.InconsistentIndex upper := by
    intro upper hupper hinconsistentSwap
    have hswapBack :
        cd.swap.swap.InconsistentIndex (cd.swap.rightIndex upper) :=
      cd.swap.swap_inconsistentIndex hinconsistentSwap
    exact hnoInconsistent upper hupper (by
      simpa [CircuitDerivation.swap, Circuit.swap, cd.swap_rightIndex upper]
        using hswapBack)
  have hactiveSwap :
      ∀ l : Fin chain.edgeCount,
        cd.swap.rightDerivation.Active (cd.swap.rightIndex (chain.current l)) :=
    left_chain_right_active_of_no_inconsistentIndex
      cd.swap chain hcompatSwap hleftStartSwap hnoInconsistentSwap
  intro l
  simpa [CircuitDerivation.swap, cd.swap_rightIndex (chain.current l)]
    using hactiveSwap l

/--
Conditional chain-active consequence reindexed by
paper indices. The no-inconsistent-index premise is explicit; this is the
usable conditional form of the paper's active-prefix contradiction step.
-/
theorem left_chain_right_active_of_no_inconsistentIndex_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (hnoInconsistent :
      ∀ upper : cd.Index,
        cd.circuit.left.1.paperIndex upper ≤ cd.circuit.left.1.paperIndex start →
        ¬ cd.InconsistentIndex upper) :
    ∀ l : Fin chain.edgeCount,
      cd.rightDerivation.Active (cd.rightIndex (chain.current l)) := by
  exact
    left_chain_right_active_of_no_inconsistentIndex cd chain hcompat
      hrightActiveStart
      (by
        intro upper hupper_start hinconsistent
        exact hnoInconsistent upper
          (by simpa [Prepath.paperIndex] using Nat.succ_le_succ hupper_start)
          hinconsistent)

/--
Conditional swapped-side chain-active consequence
reindexed by paper indices. The no-inconsistent-index premise is explicit.
-/
theorem right_chain_left_active_of_no_inconsistentIndex_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start)
    (hcompat : cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm start))
    (hleftActiveStart :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm start))
    (hnoInconsistent :
      ∀ upper : cd.circuit.right.1.Index,
        cd.circuit.right.1.paperIndex upper ≤
          cd.circuit.right.1.paperIndex start →
        ¬ cd.InconsistentIndex (Fin.cast cd.circuit.length_eq.symm upper)) :
    ∀ l : Fin chain.edgeCount,
      cd.leftDerivation.Active
        (Fin.cast cd.circuit.length_eq.symm (chain.current l)) := by
  exact
    right_chain_left_active_of_no_inconsistentIndex cd chain hcompat
      hleftActiveStart
      (by
        intro upper hupper_start hinconsistent
        exact hnoInconsistent upper
          (by simpa [Prepath.paperIndex] using Nat.succ_le_succ hupper_start)
          hinconsistent)

/--
Left-side `cutMe` witness for Lemma 6.3.3:
if a right Cut upper endpoint is bracketed by an earlier left-chain link, then
the corresponding left index has a `cutMe` target no lower than the later chain
center.
-/
theorem left_chain_bracketed_right_upper_hasCutMe_ge_current
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    {p l : Fin chain.edgeCount}
    (hpl : p.val < l.val)
    {rightUpper : cd.circuit.right.1.Index}
    (hnext_upper : (chain.next p).val < rightUpper.val)
    (hupper_current : rightUpper.val ≤ (chain.current p).val) :
    ∃ cutLower : cd.Index,
      (chain.current l).val ≤ cutLower.val ∧
        ContForm.Routes.PathProperties.CutmePersistence.HasCutMe
          (cd.circuit.left.1.paperIndex cutLower)
          (cd.leftTime (Fin.cast cd.circuit.length_eq.symm rightUpper)) := by
  rcases left_chain_bracketed_right_upper_containsCut_ge_current
      cd chain hpl hnext_upper hupper_current with
    ⟨_cutUpper, cutLower, hcurrent_l_lower, hleftCut⟩
  let leftUpper : cd.Index := Fin.cast cd.circuit.length_eq.symm rightUpper
  have hcutMe :
      ContForm.Routes.PathProperties.CutmePersistence.HasCutMe
        (cd.circuit.left.1.paperIndex cutLower)
        (cd.leftTime leftUpper) := by
    simpa [CircuitDerivation.leftTime, leftUpper] using
      ContForm.Routes.PathProperties.CutmePersistence.containsCut_center_hasCutMe
        hleftCut leftUpper rfl
  exact ⟨cutLower, hcurrent_l_lower, hcutMe⟩

/--
From an inactive right-side chain node, extract
the final-time contradiction data. This is not an inconsistent-index witness;
the active-prefix route is formalized separately by
`left_chain_right_inactive_upper_inconsistentIndex`.
-/
theorem left_chain_right_inactive_upper_contradiction_data
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (l : Fin chain.edgeCount)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    ∃ upper cutLower : cd.Index,
      ∃ nextBase cutBase : Time,
        cd.circuit.left.1.paperIndex (chain.next l) <
          cd.circuit.left.1.paperIndex cutLower ∧
        (↱ (cd.circuit.left.1.paperIndex (chain.next l)) nextBase) ≼ (cd.rightTime upper) ∧
        cd.leftTime upper =
          ⋊ (cd.circuit.left.1.paperIndex cutLower) cutBase ∧
        upper.val ≤ start.val := by
  rcases left_chain_right_inactive_cut_upper_bracketed_by_previous_link
      cd chain hcompat hrightActiveStart l hrightInactive with
    ⟨p, rightUpper, _rightLower, hp_l, _hrightLower, hrightCut, hnext_upper,
      hupper_current⟩
  let upper : cd.Index := Fin.cast cd.circuit.length_eq.symm rightUpper
  rcases left_chain_bracketed_right_upper_hasCutMe_ge_current
      cd chain hp_l hnext_upper hupper_current with
    ⟨cutLower, hcurrent_l_lower, hcutMe⟩
  rcases hcutMe with ⟨cutBase, hleftShape⟩
  have htarget :
      cd.circuit.left.1.paperIndex (chain.next l) <
        cd.circuit.left.1.paperIndex cutLower := by
    exact Nat.succ_lt_succ
      (Nat.lt_of_lt_of_le (chain.next_val_lt_current l) hcurrent_l_lower)
  rcases containsCut_prefixData hrightCut with ⟨rightData⟩
  have hrightNext :
      (↱ (cd.circuit.left.1.paperIndex (chain.next l))
          rightData.tk) ≼ (cd.rightTime upper) := by
    have hrightIndex : cd.rightIndex upper = rightUpper :=
      cd.rightIndex_castLeft rightUpper
    have hle :
        (↱ (cd.circuit.left.1.paperIndex (chain.next l))
            rightData.tk) ≼ (cd.circuit.right.1.get rightUpper) := by
      simpa using rightData.nextIndex_upper_bound_to_prefix
        rightData.hprefix (upper := rightUpper) rfl
    simpa [CircuitDerivation.rightTime, upper, hrightIndex] using hle
  have hleftShape' :
      cd.leftTime upper =
        ⋊ (cd.circuit.left.1.paperIndex cutLower) cutBase := by
    simpa [upper] using hleftShape
  have hupper_start : upper.val ≤ start.val := by
    exact Nat.le_trans hupper_current (chain.current_val_le_start p)
  exact
    ⟨upper, cutLower, rightData.tk, cutBase, htarget, hrightNext,
      hleftShape', hupper_start⟩

/--
The algebraic data from an inactive right-side chain node gives a final-time
contradiction under the explicit before-last condition. This auxiliary is not
the paper's active-prefix route; the active-prefix inconsistency component is
`left_chain_right_inactive_upper_inconsistentIndex`.
-/
theorem left_chain_right_inactive_upper_contradiction_of_start_before_last
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (hstart_before : cd.circuit.left.1.paperIndex start < cd.circuit.length)
    (l : Fin chain.edgeCount)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    ∃ upper : cd.Index,
      upper.val ≤ start.val ∧
        (cd.leftTime upper) 🗲 (cd.rightTime upper) := by
  rcases left_chain_right_inactive_upper_contradiction_data
      cd chain hcompat hrightActiveStart l hrightInactive with
    ⟨upper, cutLower, nextBase, cutBase, htarget, hrightNext, hleftCutMe,
      hupper_start⟩
  have hupper_before :
      cd.circuit.left.1.paperIndex upper < cd.circuit.length := by
    have hpaper_le :
        cd.circuit.left.1.paperIndex upper ≤ cd.circuit.left.1.paperIndex start :=
      Nat.succ_le_succ hupper_start
    exact Nat.lt_of_le_of_lt hpaper_le hstart_before
  have hctrl :
      controller (cd.rightTime upper) =
        controller (cd.leftTime upper) :=
    (cd.controller_eq_before_last upper hupper_before).symm
  have hcontrRightLeft :
      (cd.rightTime upper) 🗲 (cd.leftTime upper) :=
    ContForm.Routes.PathProperties.Compatibility.contradicts_of_nextIndex_le_and_cutMe_eq
      htarget hrightNext hleftCutMe hctrl
  exact
    ⟨upper, hupper_start, contradicts_symm hcontrRightLeft⟩

/-- A non-final node of a chain lies before the path's final index. -/
theorem current_paperIndex_lt_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) (l : Fin chain.edgeCount) :
    T.paperIndex (chain.current l) < T.length := by
  rcases chain.link_order l with ⟨upper, _hnext_current, hcurrent_upper, _hcut⟩
  exact Nat.lt_of_lt_of_le hcurrent_upper (Nat.succ_le_of_lt upper.isLt)

/--
The first node of a chain of cuts is before the path's final index. This
provides the before-last side condition needed for circuit controller
agreement in later chain arguments.
-/
theorem start_paperIndex_lt_length {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) :
    T.paperIndex start < T.length := by
  let firstLink : Fin chain.edgeCount := ⟨0, chain.edgeCount_pos⟩
  have hcurrent := chain.current_paperIndex_lt_length firstLink
  have hcurrent_eq : chain.current firstLink = start := by
    simpa [current, first] using chain.first_eq_start
  simpa [hcurrent_eq] using hcurrent

/--
With the before-last condition supplied by the
chain structure, an inactive opposite-side node yields a final-time
contradiction. This is not the paper's active-prefix route; use
`left_chain_right_inactive_upper_inconsistentIndex` for the corresponding
`InconsistentIndex` component.
-/
theorem left_chain_right_inactive_upper_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (l : Fin chain.edgeCount)
    (hrightInactive :
      cd.rightDerivation.Inactive (cd.rightIndex (chain.current l))) :
    ∃ upper : cd.Index,
      upper.val ≤ start.val ∧
        (cd.leftTime upper) 🗲 (cd.rightTime upper) := by
  exact left_chain_right_inactive_upper_contradiction_of_start_before_last
    cd chain hcompat hrightActiveStart
    (by
      simpa [Circuit.length] using chain.start_paperIndex_lt_length)
    l hrightInactive

/--
If the final-time
route is given an explicit no-final-contradiction premise at or below the chain
start, then every non-final node in a left chain is active on the right side.
Unlike `left_chain_right_active_of_least_inconsistent`, it discharges the case
with this explicit premise rather than the paper's leastness argument, and it
uses a raw final-time contradiction (`🗲`) rather than the active-prefix
inconsistent-index route.
-/
theorem left_chain_right_active_of_no_final_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (hnoContr :
      ∀ upper : cd.Index, upper.val ≤ start.val →
        ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper)) :
    ∀ l : Fin chain.edgeCount,
      cd.rightDerivation.Active (cd.rightIndex (chain.current l)) := by
  intro l hrightInactive
  rcases left_chain_right_inactive_upper_contradiction
      cd chain hcompat hrightActiveStart l hrightInactive with
    ⟨upper, hupper_start, hcontr⟩
  exact hnoContr upper hupper_start hcontr

/--
If the
final-time route is given an explicit no-final-contradiction premise at or below
a right-chain start, then every non-final node in the right chain is active on
the left side. This is not the paper's active-prefix route or the unconditional lemma.
-/
theorem right_chain_left_active_of_no_final_contradiction
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start)
    (hcompat : cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm start))
    (hleftActiveStart :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm start))
    (hnoContr :
      ∀ upper : cd.circuit.right.1.Index, upper.val ≤ start.val →
        ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper))) :
    ∀ l : Fin chain.edgeCount,
      cd.leftDerivation.Active
        (Fin.cast cd.circuit.length_eq.symm (chain.current l)) := by
  have hcompatSwap : cd.swap.RightCompatibleUpTo start :=
    cd.swap_rightCompatibleUpTo hcompat
  have hleftStartSwap :
      cd.swap.rightDerivation.Active (cd.swap.rightIndex start) := by
    simpa [CircuitDerivation.swap, cd.swap_rightIndex start] using hleftActiveStart
  have hnoContrSwap :
      ∀ upper : cd.swap.Index, upper.val ≤ start.val →
        ¬ (cd.swap.leftTime upper) 🗲 (cd.swap.rightTime upper) := by
    intro upper hupper hcontr
    exact hnoContr upper hupper (by
      simpa [CircuitDerivation.leftTime, CircuitDerivation.rightTime,
        CircuitDerivation.swap, cd.swap_rightIndex upper] using hcontr)
  have hactiveSwap :
      ∀ l : Fin chain.edgeCount,
        cd.swap.rightDerivation.Active (cd.swap.rightIndex (chain.current l)) :=
    left_chain_right_active_of_no_final_contradiction
      cd.swap chain hcompatSwap hleftStartSwap hnoContrSwap
  intro l
  simpa [CircuitDerivation.swap, cd.swap_rightIndex (chain.current l)]
    using hactiveSwap l

/--
Final-time conditional chain-active consequence, reindexed by paper
indices. The no-final-contradiction premise remains explicit, so this is not
the paper's active-prefix route or the unconditional lemma.
-/
theorem left_chain_right_active_of_no_final_contradiction_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time) {start : cd.Index}
    (chain : ChainOfCuts cd.leftDerivation start)
    (hcompat : cd.RightCompatibleUpTo start)
    (hrightActiveStart : cd.rightDerivation.Active (cd.rightIndex start))
    (hnoContr :
      ∀ upper : cd.Index,
        cd.circuit.left.1.paperIndex upper ≤ cd.circuit.left.1.paperIndex start →
        ¬ (cd.leftTime upper) 🗲 (cd.rightTime upper)) :
    ∀ l : Fin chain.edgeCount,
      cd.rightDerivation.Active (cd.rightIndex (chain.current l)) := by
  exact
    left_chain_right_active_of_no_final_contradiction cd chain hcompat
      hrightActiveStart
      (by
        intro upper hupper_start hcontr
        exact hnoContr upper
          (by simpa [Prepath.paperIndex] using Nat.succ_le_succ hupper_start)
          hcontr)

/--
Final-time conditional swapped-side chain-active consequence,
reindexed by paper indices. The no-final-contradiction premise remains
explicit, so this is not the paper's active-prefix route or the unconditional lemma.
-/
theorem right_chain_left_active_of_no_final_contradiction_indexed
    {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] (cd : CircuitDerivation Time)
    {start : cd.circuit.right.1.Index}
    (chain : ChainOfCuts cd.rightDerivation start)
    (hcompat : cd.RightCompatibleUpTo (Fin.cast cd.circuit.length_eq.symm start))
    (hleftActiveStart :
      cd.leftDerivation.Active (Fin.cast cd.circuit.length_eq.symm start))
    (hnoContr :
      ∀ upper : cd.circuit.right.1.Index,
        cd.circuit.right.1.paperIndex upper ≤
          cd.circuit.right.1.paperIndex start →
        ¬ (cd.circuit.right.1.get upper) 🗲 (cd.leftTime (Fin.cast cd.circuit.length_eq.symm upper))) :
    ∀ l : Fin chain.edgeCount,
      cd.leftDerivation.Active
        (Fin.cast cd.circuit.length_eq.symm (chain.current l)) := by
  exact
    right_chain_left_active_of_no_final_contradiction cd chain hcompat
      hleftActiveStart
      (by
        intro upper hupper_start hcontr
        exact hnoContr upper
          (by simpa [Prepath.paperIndex] using Nat.succ_le_succ hupper_start)
          hcontr)

/--
Reverse induction along a chain of cuts: if a predicate holds at the final node
and can be propagated from each next node to the preceding current node, then it
holds at the first node.
-/
theorem reverse_induction {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) {P : T.Index → Prop}
    (hlast : P chain.last)
    (hstep : ∀ l : Fin chain.edgeCount, P (chain.next l) → P (chain.current l)) :
    P chain.first := by
  have hnode :
      ∀ n : Nat, n ≤ chain.edgeCount →
        P (chain.node
          ⟨chain.edgeCount - n, by omega⟩) := by
    intro n hn
    induction n with
    | zero =>
        simpa [last]
          using hlast
    | succ n ih =>
        have hn_le : n ≤ chain.edgeCount := Nat.le_trans (Nat.le_succ n) hn
        have ihnode :
            P (chain.node ⟨chain.edgeCount - n, by omega⟩) :=
          ih hn_le
        let l : Fin chain.edgeCount :=
          ⟨chain.edgeCount - (n + 1), by omega⟩
        have hnext :
            chain.next l =
              chain.node ⟨chain.edgeCount - n, by omega⟩ := by
          have harg :
              (⟨l.val + 1, Nat.succ_lt_succ l.isLt⟩ :
                  Fin (chain.edgeCount + 1)) =
                ⟨chain.edgeCount - n, by omega⟩ := by
            apply Fin.ext
            simp [l]
            omega
          simpa [next] using congrArg chain.node harg
        have hcurrent :
            chain.current l =
              chain.node ⟨chain.edgeCount - (n + 1), by omega⟩ := by
          have harg :
              (Fin.castSucc l : Fin (chain.edgeCount + 1)) =
                ⟨chain.edgeCount - (n + 1), by omega⟩ := by
            apply Fin.ext
            simp [l]
          simpa [current] using congrArg chain.node harg
        have hcurrentP : P (chain.current l) :=
          hstep l (by simpa [hnext] using ihnode)
        simpa [hcurrent] using hcurrentP
  have hfirst :
      P (chain.node ⟨chain.edgeCount - chain.edgeCount, by omega⟩) :=
    hnode chain.edgeCount (Nat.le_refl chain.edgeCount)
  simpa [first] using hfirst

/--
Reverse induction over the positions of a chain of cuts. This is used when the
proof data is indexed by the chain position rather than only by the path index
stored at that position.
-/
theorem reverse_induction_positions {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (chain : ChainOfCuts deriv start) {P : Fin (chain.edgeCount + 1) → Prop}
    (hlast : P ⟨chain.edgeCount, Nat.lt_succ_self chain.edgeCount⟩)
    (hstep : ∀ l : Fin chain.edgeCount,
      P ⟨l.val + 1, Nat.succ_lt_succ l.isLt⟩ → P (Fin.castSucc l)) :
    P ⟨0, Nat.succ_pos chain.edgeCount⟩ := by
  have hpos :
      ∀ n : Nat, n ≤ chain.edgeCount →
        P ⟨chain.edgeCount - n, by omega⟩ := by
    intro n hn
    induction n with
    | zero =>
        simpa using hlast
    | succ n ih =>
        have hn_le : n ≤ chain.edgeCount := Nat.le_trans (Nat.le_succ n) hn
        have ihpos : P ⟨chain.edgeCount - n, by omega⟩ := ih hn_le
        let l : Fin chain.edgeCount :=
          ⟨chain.edgeCount - (n + 1), by omega⟩
        have hnext :
            (⟨l.val + 1, Nat.succ_lt_succ l.isLt⟩ :
                Fin (chain.edgeCount + 1)) =
              ⟨chain.edgeCount - n, by omega⟩ := by
          apply Fin.ext
          simp [l]
          omega
        have hcurrent :
            (Fin.castSucc l : Fin (chain.edgeCount + 1)) =
              ⟨chain.edgeCount - (n + 1), by omega⟩ := by
          apply Fin.ext
          simp [l]
        have hcurrentP : P (Fin.castSucc l) :=
          hstep l (by simpa [hnext] using ihpos)
        simpa [hcurrent] using hcurrentP
  have hfirst : P ⟨chain.edgeCount - chain.edgeCount, by omega⟩ :=
    hpos chain.edgeCount (Nat.le_refl chain.edgeCount)
  simpa using hfirst

/-- One Cut from an inactive node to an active lower node gives a one-edge chain. -/
def single {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {start next upper : T.Index}
    (hstart : deriv.Inactive start)
    (hnext : deriv.Active next)
    (hcut : ContainsCut deriv (T.paperIndex upper) (T.paperIndex start)
      (T.paperIndex next)) :
    ChainOfCuts deriv start := by
  let node : Fin (1 + 1) → T.Index := fun idx =>
    if idx.val = 0 then start else next
  exact
    { edgeCount := 1
      edgeCount_pos := Nat.succ_pos 0
      node := node
      first_eq := by
        simp [node]
      inactive_before_last := by
        intro l
        have hl : l.val = 0 := by omega
        have hlfin : l = 0 := Fin.ext hl
        have hcurrent : node (Fin.castSucc l) = start := by
          simp [node, hlfin]
        simpa [hcurrent] using hstart
      last_active := by
        change deriv.Active next
        exact hnext
      cuts := by
        intro l
        have hl : l.val = 0 := by omega
        have hlfin : l = 0 := Fin.ext hl
        have hcurrent : node (Fin.castSucc l) = start := by
          simp [node, hlfin]
        have hnextNode : node ⟨l.val + 1, Nat.succ_lt_succ l.isLt⟩ = next := by
          simp [node]
        exact ⟨upper, by simpa [hcurrent, hnextNode] using hcut⟩ }

/-- One Cut into the first node of an existing chain prepends a chain edge. -/
def cons {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time} {deriv : Derivation Time T}
    {start next upper : T.Index}
    (hstart : deriv.Inactive start)
    (hcut : ContainsCut deriv (T.paperIndex upper) (T.paperIndex start)
      (T.paperIndex next))
    (tail : ChainOfCuts deriv next) :
    ChainOfCuts deriv start := by
  let node : Fin ((tail.edgeCount + 1) + 1) → T.Index := fun idx =>
    match idx with
    | ⟨0, _⟩ => start
    | ⟨m + 1, hm⟩ => tail.node ⟨m, Nat.succ_lt_succ_iff.mp hm⟩
  exact
    { edgeCount := tail.edgeCount + 1
      edgeCount_pos := Nat.succ_pos tail.edgeCount
      node := node
      first_eq := by
        rfl
      inactive_before_last := by
        intro l
        rcases l with ⟨l, hl⟩
        cases l with
        | zero =>
            change deriv.Inactive start
            exact hstart
        | succ m =>
            have hm : m < tail.edgeCount := Nat.succ_lt_succ_iff.mp hl
            have hnode :
                node (Fin.castSucc ⟨m + 1, hl⟩) =
                  tail.node (Fin.castSucc ⟨m, hm⟩) := by
              rfl
            simpa [hnode] using tail.inactive_before_last ⟨m, hm⟩
      last_active := by
        have hnode :
            node ⟨tail.edgeCount + 1, Nat.lt_succ_self (tail.edgeCount + 1)⟩ =
              tail.node ⟨tail.edgeCount, Nat.lt_succ_self tail.edgeCount⟩ := by
          rfl
        simpa [hnode] using tail.last_active
      cuts := by
        intro l
        rcases l with ⟨l, hl⟩
        cases l with
        | zero =>
            have hcurrent : node 0 = start := by
              rfl
            have hnextNode : node 1 = next := by
              change tail.node 0 = next
              exact tail.first_eq
            exact
              ⟨upper, by
                simpa [hcurrent, hnextNode] using hcut⟩
        | succ m =>
            have hm : m < tail.edgeCount := Nat.succ_lt_succ_iff.mp hl
            rcases tail.cuts ⟨m, hm⟩ with ⟨k, htailCut⟩
            have hcurrent :
                node (Fin.castSucc ⟨m + 1, hl⟩) =
                  tail.node (Fin.castSucc ⟨m, hm⟩) := by
              rfl
            have hnextNode :
                node ⟨m + 1 + 1, Nat.succ_lt_succ hl⟩ =
                  tail.node ⟨m + 1, Nat.succ_lt_succ hm⟩ := by
              rfl
            exact ⟨k, by simpa [hcurrent, hnextNode] using htailCut⟩ }

/--
Existence half of Lemma 6.3.2: an inactive index admits a chain of cuts. The
construction follows the paper's induction on the index — an inactive index is
cut to a strictly lower index (`inactive_implies_containsCut_center`); if that
lower index is active the chain has one edge (`single`), otherwise the inductive
chain from it is prepended (`cons`). The uniqueness half is
`next_eq_of_current_eq` (paper appeal to affine cuts, Proposition 5.2.3).
-/
theorem exists_of_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (hinactive : deriv.Inactive start) : Nonempty (ChainOfCuts deriv start) := by
  rcases
      ContForm.Routes.PathProperties.InactiveCuts.inactive_implies_containsCut_center
        deriv hinactive with
    ⟨cutUpper, cutLower, hcutLower_start, _hstart_cutUpper, hcut⟩
  by_cases hactiveLower : deriv.Active cutLower
  · exact ⟨ChainOfCuts.single hinactive hactiveLower hcut⟩
  · have hinactiveLower : deriv.Inactive cutLower :=
      Classical.not_not.mp hactiveLower
    rcases exists_of_inactive hinactiveLower with ⟨tail⟩
    exact ⟨ChainOfCuts.cons hinactive hcut tail⟩
termination_by start.val
decreasing_by exact hcutLower_start

/--
Lemma 6.3.2 (the chain of cuts is well-defined): an inactive index has a chain of
cuts, and every chain of cuts from that start has the same length and the same
node at each position — so the tuple `(i = i₁, …, iₙ)` of Definition 6.3.1 is
uniquely determined.
-/
theorem exists_unique_nodes_of_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (hinactive : deriv.Inactive start) :
    ∃ chain : ChainOfCuts deriv start,
      ∀ chain' : ChainOfCuts deriv start,
        chain'.edgeCount = chain.edgeCount ∧
          ∀ n : Nat, (hn' : n ≤ chain'.edgeCount) → (hn : n ≤ chain.edgeCount) →
            chain'.node ⟨n, Nat.lt_succ_of_le hn'⟩ =
              chain.node ⟨n, Nat.lt_succ_of_le hn⟩ := by
  rcases ChainOfCuts.exists_of_inactive hinactive with ⟨chain⟩
  refine ⟨chain, ?_⟩
  intro chain'
  exact
    ⟨ChainOfCuts.edgeCount_eq_of_same_start chain' chain,
      fun n hn' hn => ChainOfCuts.node_eq_of_same_start_position chain' chain hn' hn⟩

/--
Lemma 6.3.2 consequence: every inactive index has a strictly lower active
endpoint along its chain of cuts.
-/
theorem exists_active_lower_of_inactive {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {start : T.Index}
    (hinactive : deriv.Inactive start) :
    ∃ lower : T.Index, lower.val < start.val ∧ deriv.Active lower := by
  rcases ChainOfCuts.exists_of_inactive hinactive with ⟨chain⟩
  exact ⟨chain.last, chain.last_val_lt_start, chain.last_active⟩

end ChainOfCuts

end ContForm.Routes.StrongerSafety.Chains
