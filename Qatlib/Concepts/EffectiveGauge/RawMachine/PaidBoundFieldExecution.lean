/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundFieldControl

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Field Execution

Raw Machine constructions for Effective Gauge.
Proves `square_fee`, `drain_fee`, `raw_fields`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidBoundCompression.Fields

/-- Original `square_fee` guarantee for the `PaidBoundFieldExecution` construction; the complete source hypotheses are retained. -/
private theorem square_fee (a b L : ℕ) (h : a+b≤L) :
    500*(1+a+b)^2≤500*(1+L)^2 :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- Original `drain_fee` guarantee for the `PaidBoundFieldExecution` construction; the complete source hypotheses are retained. -/
private theorem drain_fee (n L : ℕ) (h : n≤L) : n^2+3*n+3≤10*(1+L)^2 := by
  have hh := Nat.pow_le_pow_left h 2
  nlinarith

/-- Actual parsing of the original four-natural bound answer into four
binary field banks. Raw input, accumulated re-encoding, scratch and local
registers are cleared. There is no free rational reduction or sign test. -/
theorem raw_fields (q : RedundantRational.Frac) :
    Stacks.Execution program (TM2.init Slot.raw (PaidRationalBridge.encode q).reverse)
      ⟨none,default,state (operands q.num.1.bits q.num.2.bits q.den.1.bits q.den.2.bits) [] [] []⟩
      (3000*(1+(PaidRationalBridge.encode q).length)^2) := by
  let p := q.num.1
  let n := q.num.2
  let r := q.den.1
  let s := q.den.2
  let bits := PaidFractionInverse.input p n r s
  let L := bits.length
  let a0 : Fin 4 → CanonicalCodec.Bits := fun _ => []
  let a1 := Function.update a0 0 p.bits
  let a2 := Function.update a1 1 n.bits
  let a3 := Function.update a2 2 r.bits
  let a4 := Function.update a3 3 s.bits
  let fields := operands p.bits n.bits r.bits s.bits
  have hlen := PaidFractionInverse.input_length p n r s
  change L=_ at hlen
  have e0 := start_call bits default
  have e1 := (read_call 0 p (CanonicalCodec.natBits n++(CanonicalCodec.natBits r++CanonicalCodec.natBits s))
    [] a0 (putIO default none) rfl).mono
      (square_fee _ _ L (by simp only [List.length_append,List.length_nil]; omega))
  have e2 := (read_call 1 n (CanonicalCodec.natBits r++CanonicalCodec.natBits s)
    (CanonicalCodec.natBits p).reverse a1 (readLast p) rfl).mono
      (square_fee _ _ L (by simp only [List.length_append,List.length_reverse]; omega))
  have e3 := (read_call 2 r (CanonicalCodec.natBits s)
    (CanonicalCodec.natBits p++CanonicalCodec.natBits n).reverse a2 (readLast n) rfl).mono
      (square_fee _ _ L (by simp only [List.length_append,List.length_reverse]; omega))
  have e4 := (read_call 3 s []
    (CanonicalCodec.natBits p++(CanonicalCodec.natBits n++CanonicalCodec.natBits r)).reverse a3 (readLast r) rfl).mono
      (square_fee _ _ L (by simp only [List.length_append,List.length_reverse,List.length_nil]; omega))
  simp only [List.append_nil,List.reverse_append,List.append_assoc] at e1 e2 e3 e4
  have er := (((e0.trans e1).trans e2).trans e3).trans e4
  have ha : a4=fields := by funext i; fin_cases i <;> rfl
  change Stacks.Execution program _ ⟨some (.discard 0),readLast s,state a4 [] [] _⟩ _ at er
  rw [ha] at er
  simp only [←List.reverse_append,List.append_assoc] at er
  have ed := (discard_call fields bits.reverse (readLast s)).mono
    (drain_fee _ L (by simp only [List.length_reverse]; exact le_rfl))
  have ef := done_step fields (putIO (readLast s) none)
  have all := (er.trans ed).trans ef
  have hi : (⟨some (.start 0),default,state a0 bits.reverse [] []⟩ : Config)=TM2.init Slot.raw bits.reverse := by
    congr 1
    funext k
    cases k <;> rfl
  rw [hi] at all
  apply all.mono
  change ((20*(1+L)^2+500*(1+L)^2+500*(1+L)^2+500*(1+L)^2+
    500*(1+L)^2)+10*(1+L)^2)+1≤3000*(1+L)^2
  have hp : 0<(1+L)^2 := by positivity
  omega

end PaidBoundCompression.Fields
end Qatlib.Concepts.EffectiveGauge.RawMachine
