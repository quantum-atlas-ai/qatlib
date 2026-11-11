/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorJetSyntax
import Mathlib.Computability.PartrecCode

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Expr Codec

Coded Floor constructions for Effective Gauge.
Defines `floorExprNode`, `floorExprAxis`, `floorExprInteger`.
Proves `floorExprDecode_node`, `floorExprInteger_pair`, `floorExprAxis_val`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Natural-number syntax. Zero and unknown tags decode to the zero constant. -/
def floorExprNode (tag payload : ℕ) : ℕ := Nat.succ (Nat.pair tag payload)

/-- Definition of floor Expr Axis in the Coded Floor construction. -/
def floorExprAxis (n : ℕ) : Fin 3 := ⟨n%3,Nat.mod_lt _ (by decide)⟩

/-- Definition of floor Expr Integer in the Coded Floor construction. -/
def floorExprInteger (payload : ℕ) : ℤ :=
  (payload.unpair.1 : ℤ)-(payload.unpair.2 : ℤ)

/-- Definition of floor Expr Encode in the Coded Floor construction. -/
def floorExprEncode : FloorJetExpr → ℕ
  | .integer z => floorExprNode 0 (Nat.pair z.toNat (-z).toNat)
  | .coordinate i => floorExprNode 1 i.val
  | .parameter => floorExprNode 2 0
  | .flat n => floorExprNode 3 n
  | .add f g => floorExprNode 4 (Nat.pair (floorExprEncode f) (floorExprEncode g))
  | .neg f => floorExprNode 5 (floorExprEncode f)
  | .mul f g => floorExprNode 6 (Nat.pair (floorExprEncode f) (floorExprEncode g))
  | .sin f => floorExprNode 7 (floorExprEncode f)
  | .cos f => floorExprNode 8 (floorExprEncode f)

/-- Definition of floor Expr Decode in the Coded Floor construction. -/
def floorExprDecode (n : ℕ) : FloorJetExpr :=
  if hn : n=0 then .integer 0 else
    let tag := (n-1).unpair.1
    let p := (n-1).unpair.2
    if tag=0 then .integer (floorExprInteger p)
    else if tag=1 then .coordinate (floorExprAxis p)
    else if tag=2 then .parameter
    else if tag=3 then .flat p
    else if tag=4 then .add (floorExprDecode p.unpair.1) (floorExprDecode p.unpair.2)
    else if tag=5 then .neg (floorExprDecode p)
    else if tag=6 then .mul (floorExprDecode p.unpair.1) (floorExprDecode p.unpair.2)
    else if tag=7 then .sin (floorExprDecode p)
    else if tag=8 then .cos (floorExprDecode p)
    else .integer 0
termination_by n
decreasing_by
  all_goals
    have hp : (n-1).unpair.2<n :=
      (Nat.unpair_right_le (n-1)).trans_lt (by omega)
    first
    | exact (Nat.unpair_left_le _).trans_lt hp
    | exact (Nat.unpair_right_le _).trans_lt hp
    | exact hp

/-- Original `floorExprDecode_node` guarantee for the `FloorExprCodec` construction; the complete source hypotheses are retained. -/
theorem floorExprDecode_node (tag p : ℕ) :
    floorExprDecode (floorExprNode tag p)=
      if tag=0 then .integer (floorExprInteger p)
      else if tag=1 then .coordinate (floorExprAxis p)
      else if tag=2 then .parameter
      else if tag=3 then .flat p
      else if tag=4 then .add (floorExprDecode p.unpair.1) (floorExprDecode p.unpair.2)
      else if tag=5 then .neg (floorExprDecode p)
      else if tag=6 then .mul (floorExprDecode p.unpair.1) (floorExprDecode p.unpair.2)
      else if tag=7 then .sin (floorExprDecode p)
      else if tag=8 then .cos (floorExprDecode p)
      else .integer 0 := by
  rw [floorExprDecode]
  simp only [floorExprNode,Nat.succ_ne_zero,↓reduceDIte,Nat.succ_sub_one,Nat.unpair_pair]

/-- Original `floorExprInteger_pair` guarantee for the `FloorExprCodec` construction; the complete source hypotheses are retained. -/
theorem floorExprInteger_pair (z : ℤ) :
    floorExprInteger (Nat.pair z.toNat (-z).toNat)=z := by
  simp only [floorExprInteger,Nat.unpair_pair]
  omega

/-- Original `floorExprAxis_val` guarantee for the `FloorExprCodec` construction; the complete source hypotheses are retained. -/
theorem floorExprAxis_val (i : Fin 3) : floorExprAxis i.val=i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

/-- Original `floorExprDecode_encode` guarantee for the `FloorExprCodec` construction; the complete source hypotheses are retained. -/
theorem floorExprDecode_encode (e : FloorJetExpr) : floorExprDecode (floorExprEncode e)=e := by
  induction e with
  | integer z => rw [floorExprEncode,floorExprDecode_node]; simp only [ite_true,floorExprInteger_pair]
  | coordinate i => rw [floorExprEncode,floorExprDecode_node]; norm_num [floorExprAxis_val]
  | parameter => rw [floorExprEncode,floorExprDecode_node]; norm_num
  | flat n => rw [floorExprEncode,floorExprDecode_node]; norm_num
  | add f g hf hg =>
    rw [floorExprEncode,floorExprDecode_node]
    norm_num [hf,hg]
  | neg f hf => rw [floorExprEncode,floorExprDecode_node]; norm_num [hf]
  | mul f g hf hg =>
    rw [floorExprEncode,floorExprDecode_node]
    norm_num [hf,hg]
  | sin f hf => rw [floorExprEncode,floorExprDecode_node]; norm_num [hf]
  | cos f hf => rw [floorExprEncode,floorExprDecode_node]; norm_num [hf]

/-- Original `floorExprNode_payload_lt` guarantee for the `FloorExprCodec` construction; the complete source hypotheses are retained. -/
theorem floorExprNode_payload_lt (tag p : ℕ) : p<floorExprNode tag p :=
  Nat.lt_succ_of_le (Nat.right_le_pair tag p)

/-- Original `floorExprNode_left_lt` guarantee for the `FloorExprCodec` construction; the complete source hypotheses are retained. -/
theorem floorExprNode_left_lt (tag a b : ℕ) : a<floorExprNode tag (Nat.pair a b) :=
  (Nat.left_le_pair a b).trans_lt (floorExprNode_payload_lt tag _)

/-- Original `floorExprNode_right_lt` guarantee for the `FloorExprCodec` construction; the complete source hypotheses are retained. -/
theorem floorExprNode_right_lt (tag a b : ℕ) : b<floorExprNode tag (Nat.pair a b) :=
  (Nat.right_le_pair a b).trans_lt (floorExprNode_payload_lt tag _)

/-- Original `primrec_floorExprNode` guarantee for the `FloorExprCodec` construction; the complete source hypotheses are retained. -/
theorem primrec_floorExprNode : Primrec₂ floorExprNode :=
  Primrec.succ.comp Primrec₂.natPair

end Qatlib.Concepts.EffectiveGauge.CodedFloor
