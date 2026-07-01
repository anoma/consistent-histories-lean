import ConsistentHistories.Routes.PathProperties.MainResult

/-!
Paper §6.2 "Additional machinery: C-closure of T".

Formalizes Definition 6.2.1 — the C-closure `|T|_C` of a set of times `T` with
respect to a set of controllers `C`, the least set of times closed under the
rules (CInit) and (CAttest) of Figure 13 — and Lemma 6.2.2, its three
characterizing properties. Here `controllers` is `C`, `times` is `T`, `#` is
attestation, `le` is `≤`, and `controller` is `ctrl`.
-/

namespace ConsistentHistories.Routes.StrongerSafety.Closure

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice

universe u v

/-- Definition 6.2.1: the C-closure `|T|_C` of the set of times `times` with
respect to the set of controllers `controllers`, defined inductively as the
least set of times closed under Figure 13's two rules. The `init` constructor is
(CInit) / property (1) — a time `t ∈ T` with `ctrl(t) ∈ C` lies in `|T|_C`. The
`attest` constructor is (CAttest) / property (2) — if `t # s ∈ |T|_C` and
`ctrl(s) ∈ C` then `s ∈ |T|_C`. -/
inductive CClosure {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (times : Time → Prop) : Time → Prop where
  | init {t : Time} (hT : times t) (hC : controllers (controller t)) :
      CClosure controllers times t
  | attest {t s : Time} (h : CClosure controllers times (t # s))
      (hC : controllers (controller s)) :
      CClosure controllers times s

namespace CClosure

/-- Definition 6.2.1, minimality: `CClosure` is the *least* set closed under
(CInit) and (CAttest). Any predicate `closed` satisfying property (1) (`hinit`)
and property (2) (`hattest`) contains `|T|_C`. -/
theorem least {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    {controllers : Ctrl → Prop} {times closed : Time → Prop}
    (hinit : ∀ {t : Time}, times t → controllers (controller t) → closed t)
    (hattest : ∀ {t s : Time}, closed (t # s) →
      controllers (controller s) → closed s) :
    ∀ {t : Time}, CClosure controllers times t → closed t := by
  intro t hclosure
  induction hclosure with
  | init hT hC =>
      exact hinit hT hC
  | attest _h hC ih =>
      exact hattest ih hC

/-- Definition 6.2.1, full characterization: `CClosure` satisfies property (1)
(CInit), satisfies property (2) (CAttest), and is the least such set — every
predicate closed under both rules contains it. -/
theorem is_least_closed {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    {controllers : Ctrl → Prop} {times : Time → Prop} :
    (∀ {t : Time}, times t → controllers (controller t) →
      CClosure controllers times t) ∧
      (∀ {t s : Time}, CClosure controllers times (t # s) →
        controllers (controller s) → CClosure controllers times s) ∧
      ∀ {closed : Time → Prop},
        (∀ {t : Time}, times t → controllers (controller t) → closed t) →
        (∀ {t s : Time}, closed (t # s) →
          controllers (controller s) → closed s) →
        ∀ {t : Time}, CClosure controllers times t → closed t := by
  constructor
  · intro _t hT hC
    exact CClosure.init hT hC
  · constructor
    · intro _t _s hclosure hC
      exact CClosure.attest hclosure hC
    · intro closed hinit hattest _t hclosure
      exact CClosure.least hinit hattest hclosure

/-- Lemma 6.2.2(1): if `t ∈ |T|_C` then `ctrl(t) ∈ C`. -/
theorem controller_mem {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    {controllers : Ctrl → Prop} {times : Time → Prop} {t : Time}
    (h : CClosure controllers times t) : controllers (controller t) := by
  cases h with
  | init _hT hC => exact hC
  | attest _h hC => exact hC

/-- Lemma 6.2.2(2): if `t' ≤ t` and `t ∈ |T|_C` then `t' ∈ |T|_C`. -/
theorem of_le {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    {controllers : Ctrl → Prop} {times : Time → Prop} {t' t : Time}
    (hle : le t' t) (h : CClosure controllers times t) :
    CClosure controllers times t' := by
  have hctrl_t : controllers (controller t) := controller_mem h
  have hctrl_t' : controllers (controller t') := by
    rw [hle.1]
    exact hctrl_t
  have hatt_eq : t # t' = t := by
    calc
      t # t' = t' # t := self_join_comm hle.1.symm
      _ = t := hle.2
  have hatt : CClosure controllers times (t # t') := by
    rwa [hatt_eq]
  exact CClosure.attest hatt hctrl_t'

/-- Corollary of Lemma 6.2.2 clauses (2) then (1): if `t' ≤ t` and `t ∈ |T|_C`
then `ctrl(t') ∈ C`. -/
theorem controller_mem_of_le {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    {controllers : Ctrl → Prop} {times : Time → Prop} {t' t : Time}
    (hle : le t' t) (h : CClosure controllers times t) :
    controllers (controller t') := by
  exact CClosure.controller_mem (CClosure.of_le hle h)

/-- Lemma 6.2.2(3), first part: if `t # s ∈ |T|_C` then `t ∈ |T|_C`. -/
theorem left_of_attest {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    {controllers : Ctrl → Prop} {times : Time → Prop} {t s : Time}
    (h : CClosure controllers times (t # s)) :
    CClosure controllers times t := by
  exact of_le (le_attest t s) h

/-- Lemma 6.2.2(3), second part: if `t # s ∈ |T|_C` and `ctrl(s) ∈ C` then
`s ∈ |T|_C`. This is (CAttest) of Figure 13. -/
theorem right_of_attest {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    {controllers : Ctrl → Prop} {times : Time → Prop} {t s : Time}
    (h : CClosure controllers times (t # s))
    (hC : controllers (controller s)) :
    CClosure controllers times s := by
  exact CClosure.attest h hC

/-- Corollary combining Lemma 6.2.2 clauses (2) and (3): if the attestation
`t # s` lies below a C-closed time `u` and `ctrl(s) ∈ C`, then `s ∈ |T|_C`. -/
theorem right_of_attest_le {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    {controllers : Ctrl → Prop} {times : Time → Prop} {t s u : Time}
    (hle : le (t # s) u)
    (hclosed : CClosure controllers times u)
    (hC : controllers (controller s)) :
    CClosure controllers times s := by
  exact CClosure.right_of_attest (CClosure.of_le hle hclosed) hC

/-- Corollary combining Lemma 6.2.2 clauses (2) and (3): if the attestation
`t # s` lies below a C-closed time `u`, then `t ∈ |T|_C`. -/
theorem left_of_attest_le {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    {controllers : Ctrl → Prop} {times : Time → Prop} {t s u : Time}
    (hle : le (t # s) u)
    (hclosed : CClosure controllers times u) :
    CClosure controllers times t := by
  exact CClosure.left_of_attest (CClosure.of_le hle hclosed)

end CClosure

/-- Lemma 6.2.2, all three clauses bundled: (1) `t ∈ |T|_C` implies
`ctrl(t) ∈ C`; (2) `t' ≤ t` with `t ∈ |T|_C` implies `t' ∈ |T|_C`; (3)
`t # s ∈ |T|_C` implies `t ∈ |T|_C`, and if furthermore `ctrl(s) ∈ C` then
`s ∈ |T|_C`. -/
theorem cClosure_is_C_closure {Time : Type v} {Ctrl : Type u} [LocatedSemilattice Time Ctrl]
    (controllers : Ctrl → Prop) (times : Time → Prop) :
    (∀ {t : Time}, CClosure controllers times t → controllers (controller t)) ∧
      (∀ {t' t : Time}, le t' t → CClosure controllers times t →
        CClosure controllers times t') ∧
      (∀ {t s : Time}, CClosure controllers times (t # s) →
        CClosure controllers times t ∧
          (controllers (controller s) → CClosure controllers times s)) := by
  constructor
  · intro t h
    exact CClosure.controller_mem h
  · constructor
    · intro t' t hle h
      exact CClosure.of_le hle h
    · intro t s h
      exact ⟨CClosure.left_of_attest h, fun hC => CClosure.right_of_attest h hC⟩

end ConsistentHistories.Routes.StrongerSafety.Closure
