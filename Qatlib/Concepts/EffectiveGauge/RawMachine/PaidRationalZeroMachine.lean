/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidRationalZeroControl

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Rational Zero Machine

Raw Machine constructions for Effective Gauge.
Proves `zero_state`, `initial_state`, `source_exec_raw`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidRationalZero

/-- Original `zero_state` guarantee for the `PaidRationalZeroMachine` construction; the complete source hypotheses are retained. -/
private theorem zero_state (out : CanonicalCodec.Bits) :
    state [] out (fun _ => [])=Function.update (fun _ => []) outputSlot out := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

/-- Original `initial_state` guarantee for the `PaidRationalZeroMachine` construction; the complete source hypotheses are retained. -/
private theorem initial_state (bits : CanonicalCodec.Bits) :
    (TM2.init rawSlot bits.reverse : Config)=
      ⟨some (.invoke default),default,
        state [] [] (TM2.init PaidFractionInverse.Slot.raw bits.reverse : PaidFractionInverse.Config).stk⟩ := by
  have h : Function.update (fun _ : Slot => []) rawSlot bits.reverse=
      state [] [] (TM2.init PaidFractionInverse.Slot.raw bits.reverse : PaidFractionInverse.Config).stk := by
    funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  change (⟨some (.invoke default),default,_⟩ : Config)=_
  rw [h]

/-- Original `source_exec_raw` guarantee for the `PaidRationalZeroMachine` construction; the complete source hypotheses are retained. -/
theorem source_exec_raw (p n r s : ℕ) :
    Stacks.Execution program (TM2.init rawSlot (PaidFractionInverse.input p n r s).reverse)
      ⟨none,default,Function.update (fun _ => []) outputSlot
        [twoZeroBits (PaidFractionInverse.output p n r s)]⟩
      (11000*(1+(PaidFractionInverse.input p n r s).length)^2) := by
  let bits := PaidFractionInverse.output p n r s
  have ee := (((inverse_call p n r s).trans (transfer_call bits)).trans (tag_step bits)).trans
    (drain_call bits.tail.tail (twoZeroBits bits))
  have hf : Stacks.Execution program ⟨some .done,default,state [] [twoZeroBits bits] (fun _ => [])⟩
      ⟨none,default,state [] [twoZeroBits bits] (fun _ => [])⟩ 1 := ⟨1,rfl,le_rfl⟩
  have hh := ee.trans hf
  rw [←initial_state,zero_state] at hh
  apply hh.mono
  have hr := PaidFractionInverse.output_length p n r s
  change bits.length≤(PaidFractionInverse.input p n r s).length+2 at hr
  have ht : bits.tail.tail.length≤bits.length := by simp only [List.length_tail]; omega
  have hlen : bits.length≤2*(1+(PaidFractionInverse.input p n r s).length) := by omega
  have hr2 := Nat.mul_le_mul hlen hlen
  have ht2 := Nat.mul_le_mul ht ht
  have hpos : 1≤(1+(PaidFractionInverse.input p n r s).length)^2 := Nat.one_le_pow 2 _ (by omega)
  have hlin : 1+(PaidFractionInverse.input p n r s).length≤
      (1+(PaidFractionInverse.input p n r s).length)^2 := Nat.le_pow (by decide)
  nlinarith only [hr2,ht2,ht,hlen,hpos,hlin]

/-- The Boolean is physically written by the native program from the first
 two bits of the same inverse execution's output, including cancellation. -/
theorem source_exec (q : RedundantRational.Frac) :
    Stacks.Execution program (TM2.init rawSlot (PaidRationalBridge.encode q).reverse)
      ⟨none,default,Function.update (fun _ => []) outputSlot [decide (q.num.1=q.num.2)]⟩
      (11000*(1+(PaidRationalBridge.encode q).length)^2) := by
  have hh := source_exec_raw q.num.1 q.num.2 q.den.1 q.den.2
  rw [PaidRationalBridge.inverse_output_codec,inverse_prefix] at hh
  exact hh

/-- Original `raw_machine` guarantee for the `PaidRationalZeroMachine` construction; the complete source hypotheses are retained. -/
theorem raw_machine :
    ∃ (states coef : ℕ) (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))), 0<coef ∧
      ∀ q : RedundantRational.Frac,
        CanonicalCodec.Runs machine (PaidRationalBridge.encode q) [decide (q.num.1=q.num.2)]
          (coef*(1+(PaidRationalBridge.encode q).length)^2)
          (coef*(1+(PaidRationalBridge.encode q).length)^2) := by
  obtain ⟨states,machine,coef,hcoef,hcompile⟩ := Stacks.raw_compiler program rawSlot outputSlot
  refine ⟨states,coef*11005,machine,by omega,?_⟩
  intro q
  obtain ⟨steps,hr,hc⟩ := source_exec q
  have hh := hcompile (PaidRationalBridge.encode q) [decide (q.num.1=q.num.2)] steps default hr
  have hpos : 1≤(1+(PaidRationalBridge.encode q).length)^2 := Nat.one_le_pow 2 _ (by omega)
  have hb : coef*((1+(PaidRationalBridge.encode q).length)^2+
      Stacks.stackRunClock program steps (TM2.init rawSlot (PaidRationalBridge.encode q).reverse)+
      (1+([decide (q.num.1=q.num.2)] : CanonicalCodec.Bits).length)^2)≤
      (coef*11005)*(1+(PaidRationalBridge.encode q).length)^2 := by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    simp only [List.length_singleton]
    omega
  simpa only [List.reverse_singleton] using runs_mono hh hb hb

end PaidRationalZero
end Qatlib.Concepts.EffectiveGauge.RawMachine
