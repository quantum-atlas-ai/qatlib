/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorExprBoundCode

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Expr Diff Code

Coded Floor constructions for Effective Gauge.
Defines `floorExprBumpDerivativeCode`, `floorExprDiffStep`, `floorExprDiffCode`.
Proves `floorExprDecode_bumpDerivative`, `floorExprDecode_diffCode`, `primrec_floorExprBumpDerivativeCode`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Expr Bump Derivative Code in the Coded Floor construction. -/
def floorExprBumpDerivativeCode (axis : ℕ) : ℕ :=
  floorExprNode 6 (Nat.pair (floorExprNode 0 (Nat.pair 0 2))
    (floorExprNode 4 (Nat.pair (floorExprNode 1 (axis%3))
      (floorExprNode 0 (Nat.pair 0 3)))))

/-- Original `floorExprDecode_bumpDerivative` guarantee for the `FloorExprDiffCode` construction; the complete source hypotheses are retained. -/
theorem floorExprDecode_bumpDerivative (axis : ℕ) :
    floorExprDecode (floorExprBumpDerivativeCode axis)=floorBumpDerivativeExpr (floorExprAxis axis) := by
  simp [floorExprBumpDerivativeCode,floorExprDecode_node,floorBumpDerivativeExpr,
    floorExprInteger,floorExprAxis]

/-- Definition of floor Expr Diff Step in the Coded Floor construction. -/
def floorExprDiffStep (axis n a b u : ℕ) : ℕ :=
  if n=0 then floorExprNode 0 0 else
    let tag := (n-1).unpair.1
    let p := (n-1).unpair.2
    [floorExprNode 0 0,
      floorExprNode 0 (Nat.pair (if axis%3=p%3 then 1 else 0) 0),
      floorExprNode 0 0,
      floorExprNode 6 (Nat.pair (floorExprNode 3 (p+1)) (floorExprBumpDerivativeCode axis)),
      floorExprNode 4 (Nat.pair a b),floorExprNode 5 u,
      floorExprNode 4 (Nat.pair (floorExprNode 6 (Nat.pair a p.unpair.2))
        (floorExprNode 6 (Nat.pair p.unpair.1 b))),
      floorExprNode 6 (Nat.pair (floorExprNode 8 p) u),
      floorExprNode 5 (floorExprNode 6 (Nat.pair (floorExprNode 7 p) u))].getD tag (floorExprNode 0 0)

/-- Definition of floor Expr Diff Code in the Coded Floor construction. -/
def floorExprDiffCode (axis n : ℕ) : ℕ :=
  if hn : n=0 then floorExprNode 0 0 else
    let p := (n-1).unpair.2
    floorExprDiffStep axis n (floorExprDiffCode axis p.unpair.1)
      (floorExprDiffCode axis p.unpair.2) (floorExprDiffCode axis p)
termination_by n
decreasing_by
  all_goals
    have hp : (n-1).unpair.2<n := (Nat.unpair_right_le _).trans_lt (by omega)
    first
    | exact (Nat.unpair_left_le _).trans_lt hp
    | exact (Nat.unpair_right_le _).trans_lt hp
    | exact hp

/-- Original `floorExprDecode_diffCode` guarantee for the `FloorExprDiffCode` construction; the complete source hypotheses are retained. -/
theorem floorExprDecode_diffCode (axis n : ℕ) :
    floorExprDecode (floorExprDiffCode axis n)=floorJetDiff (floorExprAxis axis) (floorExprDecode n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      have hz : floorExprDecode 0=FloorJetExpr.integer 0 := by rw [floorExprDecode]; simp
      rw [floorExprDiffCode,dif_pos rfl]
      rw [floorExprDecode_node,hz]
      norm_num [floorExprInteger,floorJetDiff]
    · have hp : (n-1).unpair.2<n := (Nat.unpair_right_le _).trans_lt (by omega)
      have ha := (Nat.unpair_left_le (n-1).unpair.2).trans_lt hp
      have hb := (Nat.unpair_right_le (n-1).unpair.2).trans_lt hp
      rw [floorExprDiffCode,dif_neg hn]
      conv_rhs => rw [floorExprDecode,dif_neg hn]
      unfold floorExprDiffStep
      rw [if_neg hn]
      dsimp only
      generalize ht : (n-1).unpair.1=tag
      by_cases htag : tag<9
      · interval_cases tag <;>
          simp [floorExprDecode_node,floorJetDiff,floorExprInteger,
            floorExprDecode_bumpDerivative,ih _ ha,ih _ hb,ih _ hp]
        · have heq : floorExprAxis axis=floorExprAxis (n-1).unpair.2 ↔
              axis%3=(n-1).unpair.2%3 := by simp [Fin.ext_iff,floorExprAxis]
          simp only [heq]
      · have h0 : tag≠0 := by omega
        have h1 : tag≠1 := by omega
        have h2 : tag≠2 := by omega
        have h3 : tag≠3 := by omega
        have h4 : tag≠4 := by omega
        have h5 : tag≠5 := by omega
        have h6 : tag≠6 := by omega
        have h7 : tag≠7 := by omega
        have h8 : tag≠8 := by omega
        rw [List.getD_eq_default _ _ (by simp; omega)]
        simp [floorExprDecode_node,floorJetDiff,floorExprInteger,h0,h1,h2,h3,h4,h5,h6,h7,h8]

/-- Original `primrec_floorExprBumpDerivativeCode` guarantee for the `FloorExprDiffCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorExprBumpDerivativeCode : Primrec floorExprBumpDerivativeCode := by
  have haxis := Primrec.nat_mod.comp Primrec.id (Primrec.const 3)
  have hcoord := primrec_floorExprNode.comp (Primrec.const 1) haxis
  have hinner := primrec_floorExprNode.comp (Primrec.const 4)
    (Primrec₂.natPair.comp hcoord (Primrec.const (floorExprNode 0 (Nat.pair 0 3))))
  exact primrec_floorExprNode.comp (Primrec.const 6)
    (Primrec₂.natPair.comp (Primrec.const (floorExprNode 0 (Nat.pair 0 2))) hinner)

/-- Original `primrec_floorExprDiffStep` guarantee for the `FloorExprDiffCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorExprDiffStep : Primrec (fun q : ℕ × ℕ × ℕ × ℕ × ℕ =>
    floorExprDiffStep q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have haxis : Primrec (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.1) := Primrec.fst
  have hn : Primrec (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hu : Primrec (fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hparts := Primrec.unpair.comp (Primrec.nat_sub.comp hn (Primrec.const 1))
  have ht := Primrec.fst.comp hparts
  have hp := Primrec.snd.comp hparts
  have hleft := Primrec.fst.comp (Primrec.unpair.comp hp)
  have hright := Primrec.snd.comp (Primrec.unpair.comp hp)
  have hcoord := Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp haxis (Primrec.const 3))
      (Primrec.nat_mod.comp hp (Primrec.const 3))) (Primrec.const 1) (Primrec.const 0)
  have h1 := primrec_floorExprNode.comp (Primrec.const 0)
    (Primrec₂.natPair.comp hcoord (Primrec.const 0))
  have h3 := primrec_floorExprNode.comp (Primrec.const 6)
    (Primrec₂.natPair.comp (primrec_floorExprNode.comp (Primrec.const 3) (Primrec.succ.comp hp))
      (primrec_floorExprBumpDerivativeCode.comp haxis))
  have h4 := primrec_floorExprNode.comp (Primrec.const 4) (Primrec₂.natPair.comp ha hb)
  have h5 := primrec_floorExprNode.comp (Primrec.const 5) hu
  have h6 := primrec_floorExprNode.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (primrec_floorExprNode.comp (Primrec.const 6) (Primrec₂.natPair.comp ha hright))
      (primrec_floorExprNode.comp (Primrec.const 6) (Primrec₂.natPair.comp hleft hb)))
  have h7 := primrec_floorExprNode.comp (Primrec.const 6)
    (Primrec₂.natPair.comp (primrec_floorExprNode.comp (Primrec.const 8) hp) hu)
  have h8 := primrec_floorExprNode.comp (Primrec.const 5)
    (primrec_floorExprNode.comp (Primrec.const 6)
      (Primrec₂.natPair.comp (primrec_floorExprNode.comp (Primrec.const 7) hp) hu))
  have hlist := Primrec.list_cons.comp (Primrec.const (floorExprNode 0 0))
    (Primrec.list_cons.comp h1 (Primrec.list_cons.comp (Primrec.const (floorExprNode 0 0))
      (Primrec.list_cons.comp h3 (Primrec.list_cons.comp h4 (Primrec.list_cons.comp h5
        (Primrec.list_cons.comp h6 (Primrec.list_cons.comp h7
          (Primrec.list_cons.comp h8 (Primrec.const [])))))))))
  exact Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) (Primrec.const (floorExprNode 0 0))
    ((Primrec.list_getD (floorExprNode 0 0)).comp hlist ht)

/-- Definition of floor Expr Diff From in the Coded Floor construction. -/
def floorExprDiffFrom (axis : ℕ) (history : List ℕ) : ℕ :=
  let n := history.length
  let p := (n-1).unpair.2
  floorExprDiffStep axis n (history.getD p.unpair.1 0)
    (history.getD p.unpair.2 0) (history.getD p 0)

/-- Original `computable_floorExprDiffCode` guarantee for the `FloorExprDiffCode` construction; the complete source hypotheses are retained. -/
theorem computable_floorExprDiffCode : Computable₂ floorExprDiffCode := by
  have hn : Primrec (fun q : ℕ × List ℕ => q.2.length) := Primrec.list_length.comp Primrec.snd
  have hp := (Primrec.snd.comp Primrec.unpair).comp (Primrec.nat_sub.comp hn (Primrec.const 1))
  have ha := (Primrec.list_getD 0).comp Primrec.snd ((Primrec.fst.comp Primrec.unpair).comp hp)
  have hb := (Primrec.list_getD 0).comp Primrec.snd ((Primrec.snd.comp Primrec.unpair).comp hp)
  have hu := (Primrec.list_getD 0).comp Primrec.snd hp
  have hg : Computable₂ (fun (axis : ℕ) (history : List ℕ) => some (floorExprDiffFrom axis history)) :=
    (Primrec.option_some.comp (primrec_floorExprDiffStep.comp
      (Primrec.fst.pair (hn.pair (ha.pair (hb.pair hu)))))).to_comp
  apply Computable.nat_strong_rec _ hg
  intro axis n
  simp only [floorExprDiffFrom,List.length_map,List.length_range]
  by_cases hn : n=0
  · subst n
    rw [floorExprDiffCode]
    simp [floorExprDiffStep]
  · have hp : (n-1).unpair.2<n := (Nat.unpair_right_le _).trans_lt (by omega)
    have ha := (Nat.unpair_left_le (n-1).unpair.2).trans_lt hp
    have hb := (Nat.unpair_right_le (n-1).unpair.2).trans_lt hp
    rw [floorExprDiffCode,dif_neg hn]
    rw [floorExprHistory_getD _ n _ ha,floorExprHistory_getD _ n _ hb,floorExprHistory_getD _ n _ hp]

end Qatlib.Concepts.EffectiveGauge.CodedFloor
