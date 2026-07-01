import ConsistentHistories.Routes.Paths.Circuits.Circuit

namespace ConsistentHistories.Routes.Paths.Circuits

open ConsistentHistories.Foundation.LocatedSemilattices.Basic
open ConsistentHistories.Foundation.Cut.Flags
open ConsistentHistories.Foundation.Cut.Structure
open ConsistentHistories.Foundation.LocatedSemilattices.Basic.LocatedSemilattice
open ConsistentHistories.Foundation.Cut.Structure.LocatedSemilatticeWithCut
open ConsistentHistories.Foundation.Paths.Basic
open ConsistentHistories.Foundation.Paths.InitialPrefixes

namespace CutPrefixData

/-- Repackage the decomposed `CutPrefixData` record as the existential
`CutPrefixWitness`: the pre-Cut derivation, the `(Cut_{k,j,i})` instance
(Definition 4.3.6(1)), and the fact that the post-Cut derivation is an initial
prefix (Definition 4.2.1) of `deriv`. -/
theorem toWitness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) :
    CutPrefixWitness deriv cutK cutJ cutI := by
  exact
    ⟨data.base, data.baseDeriv, data.idxI, data.idxJ, data.idxK, data.ti,
      data.tj, data.tk, data.hij, data.hjk, data.hk, data.hj, data.hi,
      data.hconsistent, data.cutK_eq, data.cutJ_eq, data.cutI_eq,
      data.hprefix⟩

/-- The pre-Cut derivation is an initial prefix (Definition 4.2.1) of the
one-step-longer derivation whose final rule is that Cut. -/
theorem base_initialPrefix_cut {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) :
    InitialPrefix data.baseDeriv
      (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
        data.hconsistent) := by
  exact InitialPrefix.cut data.baseDeriv (InitialPrefix.refl data.baseDeriv)
    data.hij data.hjk data.hk data.hj data.hi data.hconsistent

/-- The pre-Cut derivation is an initial prefix (Definition 4.2.1) of the final
derivation `deriv`, by transitivity through the Cut. -/
theorem base_initialPrefix_final {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] {T : Prepath Time}
    {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) :
    InitialPrefix data.baseDeriv deriv := by
  exact InitialPrefix.trans data.base_initialPrefix_cut data.hprefix

/--
The center entry `j` of the pre-Cut derivation carries the same controller as
its counterpart in the final path. Along the initial prefix from the pre-Cut
derivation to `deriv`, times increase (Lemma 4.2.2, `≼`), and the controller
component of `≼` is preserved, so the two center controllers coincide.
-/
theorem base_center_controller_eq_final_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI) {center : T.Index}
    (hcenter : cutJ = T.paperIndex center) :
    controller (data.base.get data.idxJ) =
      controller (T.get center) := by
  have hidxJ_paper : data.base.paperIndex data.idxJ = T.paperIndex center := by
    exact data.cutJ_eq.symm.trans hcenter
  have hidxJ_cast :
      Fin.cast data.base_initialPrefix_final.length_eq data.idxJ = center := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hidxJ_paper)
  have hle := InitialPrefix.times_increase data.base_initialPrefix_final data.idxJ
  change (data.base.get data.idxJ) ≼ (T.get (Fin.cast data.base_initialPrefix_final.length_eq data.idxJ)) at hle
  simpa [hidxJ_cast] using hle.1

/--
The lower-endpoint datum for a derivation `laterDeriv` that extends the Cut.
At the lower index `i`, the Cut sets the entry to `t_i # centerTime`; since
times increase along the initial prefix into `laterDeriv` (Lemma 4.2.2), the
later lower endpoint `U.get lower` dominates that attested time, and `centerTime`
carries the same controller as the center entry `T.get center`.
-/
theorem attest_lower_bound_to_prefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T U : Prepath Time} {deriv : Derivation Time T} {laterDeriv : Derivation Time U}
    {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hlater :
      InitialPrefix
        (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
          data.hconsistent)
        laterDeriv)
    {center : T.Index} {lower : U.Index}
    (hcenter : cutJ = T.paperIndex center)
    (hlower : cutI = U.paperIndex lower) :
    ∃ source centerTime : Time,
      (source # centerTime) ≼ (U.get lower) ∧
        controller centerTime = controller (T.get center) := by
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  let centerTime : Time := (Derivation.root dcut).get data.idxJ
  have hidxI_paper : data.base.paperIndex data.idxI = U.paperIndex lower := by
    exact data.cutI_eq.symm.trans hlower
  have hidxJ_paper : data.base.paperIndex data.idxJ = T.paperIndex center := by
    exact data.cutJ_eq.symm.trans hcenter
  have hidxI_cast : Fin.cast hlater.length_eq data.idxI = lower := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hidxI_paper)
  have hidxJ_cast : Fin.cast data.hprefix.length_eq data.idxJ = center := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hidxJ_paper)
  have hshape :
      (Derivation.root dcut).get data.idxI = data.ti # centerTime := by
    have hi_ne_k : data.idxI ≠ data.idxK := by
      intro h
      have hlt : data.idxI.val < data.idxK.val := Nat.lt_trans data.hij data.hjk
      have hval : data.idxI.val = data.idxK.val := congrArg Fin.val h
      rw [← hval] at hlt
      exact Nat.lt_irrefl data.idxI.val hlt
    have hj_ne_k : data.idxJ ≠ data.idxK := by
      intro h
      have hlt : data.idxJ.val < data.idxK.val := data.hjk
      have hval : data.idxJ.val = data.idxK.val := congrArg Fin.val h
      rw [← hval] at hlt
      exact Nat.lt_irrefl data.idxJ.val hlt
    simp [dcut, centerTime, Derivation.root, Prepath.replace_get_ne data.base hi_ne_k,
      Prepath.replace_get_ne data.base hj_ne_k, data.hi, data.hj]
  have hlowerBound :
      (data.ti # centerTime) ≼ (U.get lower) := by
    have hle := InitialPrefix.times_increase hlater data.idxI
    change (dcut.root.get data.idxI) ≼ (U.get (Fin.cast hlater.length_eq data.idxI)) at hle
    rw [hshape] at hle
    simpa [hidxI_cast] using hle
  have hcenterBound := InitialPrefix.times_increase data.hprefix data.idxJ
  have hcenterController :
      controller centerTime = controller (T.get center) := by
    simpa [centerTime, dcut, hidxJ_cast] using hcenterBound.1
  exact ⟨data.ti, centerTime, hlowerBound, hcenterController⟩

/--
Variant of `attest_lower_bound_to_prefix` that exposes the pre-Cut center time
explicitly as the base prefix entry `data.base.get data.idxJ` rather than as an
abstract `centerTime`. The lower endpoint `U.get lower` dominates `source #`
that center entry (times increase, Lemma 4.2.2), and the center entry shares its
controller with `T.get center`.
-/
theorem attest_lower_bound_to_prefix_base_center {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T U : Prepath Time} {deriv : Derivation Time T} {laterDeriv : Derivation Time U}
    {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hlater :
      InitialPrefix
        (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
          data.hconsistent)
        laterDeriv)
    {center : T.Index} {lower : U.Index}
    (hcenter : cutJ = T.paperIndex center)
    (hlower : cutI = U.paperIndex lower) :
    ∃ source : Time,
      (source # (data.base.get data.idxJ)) ≼ (U.get lower) ∧
        controller (data.base.get data.idxJ) =
          controller (T.get center) := by
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hidxI_paper : data.base.paperIndex data.idxI = U.paperIndex lower := by
    exact data.cutI_eq.symm.trans hlower
  have hidxJ_paper : data.base.paperIndex data.idxJ = T.paperIndex center := by
    exact data.cutJ_eq.symm.trans hcenter
  have hidxI_cast : Fin.cast hlater.length_eq data.idxI = lower := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hidxI_paper)
  have hidxJ_cast : Fin.cast data.hprefix.length_eq data.idxJ = center := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hidxJ_paper)
  have hshape :
      (Derivation.root dcut).get data.idxI =
        data.ti # (data.base.get data.idxJ) := by
    have hunchanged :=
      Derivation.cut_root_get_lower_unchanged data.baseDeriv data.hij data.hjk
        data.hk data.hj data.hi data.hconsistent
    rw [hunchanged, data.hi, ← data.hj]
  have hcenter_unchanged :
      (Derivation.root dcut).get data.idxJ = data.base.get data.idxJ := by
    exact Derivation.cut_root_get_center_unchanged data.baseDeriv data.hij
      data.hjk data.hk data.hj data.hi data.hconsistent
  have hlowerBound :
      (data.ti # (data.base.get data.idxJ)) ≼ (U.get lower) := by
    have hle := InitialPrefix.times_increase hlater data.idxI
    change (dcut.root.get data.idxI) ≼ (U.get (Fin.cast hlater.length_eq data.idxI)) at hle
    rw [hshape] at hle
    simpa [hidxI_cast] using hle
  have hcenterBound := InitialPrefix.times_increase data.hprefix data.idxJ
  have hcenterController :
      controller (data.base.get data.idxJ) =
        controller (T.get center) := by
    change (dcut.root.get data.idxJ) ≼ (T.get (Fin.cast data.hprefix.length_eq data.idxJ)) at hcenterBound
    have hctrl := hcenterBound.1
    rw [hcenter_unchanged] at hctrl
    simpa [hidxJ_cast] using hctrl
  exact ⟨data.ti, hlowerBound, hcenterController⟩

/--
A prefix-ending Cut supplies the upper-endpoint datum: the later upper endpoint
is above the `nextIndex` time `↱_i t_k` introduced by the Cut (Lemma 4.2.2).
-/
theorem nextIndex_upper_bound_to_prefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl]
    {T U : Prepath Time} {deriv : Derivation Time T} {laterDeriv : Derivation Time U}
    {cutK cutJ cutI : Nat}
    (data : CutPrefixData deriv cutK cutJ cutI)
    (hlater :
      InitialPrefix
        (Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
          data.hconsistent)
        laterDeriv)
    {upper : U.Index}
    (hupper : cutK = U.paperIndex upper) :
    (↱ cutI data.tk) ≼ (U.get upper) := by
  let dcut :=
    Derivation.cut data.baseDeriv data.hij data.hjk data.hk data.hj data.hi
      data.hconsistent
  have hidxK_paper : data.base.paperIndex data.idxK = U.paperIndex upper := by
    exact data.cutK_eq.symm.trans hupper
  have hidxK_cast : Fin.cast hlater.length_eq data.idxK = upper := by
    apply Fin.ext
    exact Nat.succ.inj (by simpa [Prepath.paperIndex] using hidxK_paper)
  have hshape :
      (Derivation.root dcut).get data.idxK =
        ↱ (data.base.paperIndex data.idxI) data.tk := by
    simp [dcut, Derivation.root, Prepath.replace_get_same]
  have hle := InitialPrefix.times_increase hlater data.idxK
  change (dcut.root.get data.idxK) ≼ (U.get (Fin.cast hlater.length_eq data.idxK)) at hle
  rw [hshape] at hle
  simpa [hidxK_cast, data.cutI_eq.symm] using hle

end CutPrefixData

/-- Every `(Cut_{k,j,i})` occurrence (Definition 4.3.6(1)) in `deriv` yields a
`CutPrefixData`. By induction over `ContainsCut`, the Cut is exposed as the final
rule of an initial prefix (Definition 4.2.1) of `deriv`, and every later rule of
the derivation extends that prefix. -/
theorem containsCut_prefixData {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat},
      ContainsCut deriv cutK cutJ cutI →
        Nonempty (CutPrefixData deriv cutK cutJ cutI) := by
  intro T deriv cutK cutJ cutI hcut
  induction hcut with
  | here deriv hij hjk hk hj hi hconsistent =>
      rename_i T i j k ti tj tk
      exact
        ⟨{
          base := T
          baseDeriv := deriv
          idxI := i
          idxJ := j
          idxK := k
          ti := ti
          tj := tj
          tk := tk
          hij := hij
          hjk := hjk
          hk := hk
          hj := hj
          hi := hi
          hconsistent := hconsistent
          cutK_eq := rfl
          cutJ_eq := rfl
          cutI_eq := rfl
          hprefix :=
            InitialPrefix.refl
              (Derivation.cut deriv hij hjk hk hj hi hconsistent)
        }⟩
  | inc _h changed hlt hflag hconsistent ih =>
      rcases ih with ⟨data⟩
      exact
        ⟨{
          base := data.base
          baseDeriv := data.baseDeriv
          idxI := data.idxI
          idxJ := data.idxJ
          idxK := data.idxK
          ti := data.ti
          tj := data.tj
          tk := data.tk
          hij := data.hij
          hjk := data.hjk
          hk := data.hk
          hj := data.hj
          hi := data.hi
          hconsistent := data.hconsistent
          cutK_eq := data.cutK_eq
          cutJ_eq := data.cutJ_eq
          cutI_eq := data.cutI_eq
          hprefix := InitialPrefix.inc _ data.hprefix changed hlt hflag hconsistent
        }⟩
  | cutMeIntro _h changed target hshape hconsistent ih =>
      rcases ih with ⟨data⟩
      exact
        ⟨{
          base := data.base
          baseDeriv := data.baseDeriv
          idxI := data.idxI
          idxJ := data.idxJ
          idxK := data.idxK
          ti := data.ti
          tj := data.tj
          tk := data.tk
          hij := data.hij
          hjk := data.hjk
          hk := data.hk
          hj := data.hj
          hi := data.hi
          hconsistent := data.hconsistent
          cutK_eq := data.cutK_eq
          cutJ_eq := data.cutJ_eq
          cutI_eq := data.cutI_eq
          hprefix :=
            InitialPrefix.cutMeIntro _ data.hprefix changed target hshape
              hconsistent
        }⟩
  | cutYouIntro _h changed target hshape hconsistent ih =>
      rcases ih with ⟨data⟩
      exact
        ⟨{
          base := data.base
          baseDeriv := data.baseDeriv
          idxI := data.idxI
          idxJ := data.idxJ
          idxK := data.idxK
          ti := data.ti
          tj := data.tj
          tk := data.tk
          hij := data.hij
          hjk := data.hjk
          hk := data.hk
          hj := data.hj
          hi := data.hi
          hconsistent := data.hconsistent
          cutK_eq := data.cutK_eq
          cutJ_eq := data.cutJ_eq
          cutI_eq := data.cutI_eq
          hprefix :=
            InitialPrefix.cutYouIntro _ data.hprefix changed target hshape
              hconsistent
        }⟩
  | cutStep _h hij_final hjk_final hk_final hj_final hi_final hconsistent ih =>
      rcases ih with ⟨data⟩
      exact
        ⟨{
          base := data.base
          baseDeriv := data.baseDeriv
          idxI := data.idxI
          idxJ := data.idxJ
          idxK := data.idxK
          ti := data.ti
          tj := data.tj
          tk := data.tk
          hij := data.hij
          hjk := data.hjk
          hk := data.hk
          hj := data.hj
          hi := data.hi
          hconsistent := data.hconsistent
          cutK_eq := data.cutK_eq
          cutJ_eq := data.cutJ_eq
          cutI_eq := data.cutI_eq
          hprefix :=
            InitialPrefix.cut _ data.hprefix hij_final hjk_final hk_final
              hj_final hi_final hconsistent
        }⟩

/-- Existential form of `containsCut_prefixData`: a `(Cut_{k,j,i})` occurrence
(Definition 4.3.6(1)) is exposed as an initial prefix (Definition 4.2.1) whose
final rule is exactly that Cut. -/
theorem containsCut_prefixWitness {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T : Prepath Time} {deriv : Derivation Time T} {cutK cutJ cutI : Nat},
      ContainsCut deriv cutK cutJ cutI →
        CutPrefixWitness deriv cutK cutJ cutI := by
  intro T deriv cutK cutJ cutI hcut
  rcases containsCut_prefixData hcut with ⟨data⟩
  exact data.toWitness

/-- A `(Cut_{k,j,i})` occurrence (Definition 4.3.6(1)) present in an initial
prefix (Definition 4.2.1) `d1` remains present in every derivation `d2` that
extends it. -/
theorem containsCut_of_initialPrefix {Time : Type v} {Ctrl : Type u} [LocatedSemilatticeWithCut Time Ctrl] :
    ∀ {T1 T2 : Prepath Time} {d1 : Derivation Time T1} {d2 : Derivation Time T2}
      {cutK cutJ cutI : Nat},
      InitialPrefix d1 d2 →
        ContainsCut d1 cutK cutJ cutI →
          ContainsCut d2 cutK cutJ cutI := by
  intro T1 T2 d1 d2 cutK cutJ cutI hprefix hcut
  induction hprefix with
  | refl _deriv =>
      exact hcut
  | inc _deriv _hp changed hlt hflag hconsistent ih =>
      exact ContainsCut.inc (ih hcut) changed hlt hflag hconsistent
  | cutMeIntro _deriv _hp changed target hshape hconsistent ih =>
      exact ContainsCut.cutMeIntro (ih hcut) changed target hshape hconsistent
  | cutYouIntro _deriv _hp changed target hshape hconsistent ih =>
      exact ContainsCut.cutYouIntro (ih hcut) changed target hshape hconsistent
  | cut _deriv _hp hij hjk hk hj hi hconsistent ih =>
      exact ContainsCut.cutStep (ih hcut) hij hjk hk hj hi hconsistent

end ConsistentHistories.Routes.Paths.Circuits
