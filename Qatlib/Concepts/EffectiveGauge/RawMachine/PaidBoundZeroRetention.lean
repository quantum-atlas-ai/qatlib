/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidOriginalBoundZero

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Zero Retention

Raw Machine constructions for Effective Gauge.
Defines `Slot`, `Local`, `savedSlot`.
Proves `copyCode_injective`, `frame_target`, `copy_call`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidBoundZeroRetention

/-- Abbreviation for Slot in the Raw Machine construction. -/
abbrev Slot := PaidRationalZero.Slot ⊕ Fin 2
/-- Abbreviation for Local in the Raw Machine construction. -/
abbrev Local := PaidRationalZero.Local × Option Bool
/-- Abbreviation for saved Slot in the Raw Machine construction. -/
abbrev savedSlot : Slot := .inr 0
/-- Abbreviation for temp Slot in the Raw Machine construction. -/
abbrev tempSlot : Slot := .inr 1
/-- Abbreviation for output Slot in the Raw Machine construction. -/
abbrev outputSlot : Slot := .inl PaidRationalZero.outputSlot
/-- Constructors for Label in the Raw Machine construction. -/
inductive Label where
  | copy (l : NatEmit.Label)
  | zero (l : PaidRationalZero.Label)
  | done
  deriving DecidableEq,Fintype
/-- Initialize the machine label at its first instruction. -/
instance : Inhabited Label := ⟨.copy .emit⟩
/-- Abbreviation for Config in the Raw Machine construction. -/
abbrev Config := TM2.Cfg (fun _ : Slot => Bool) Label Local

/-- Definition of state in the Raw Machine construction. -/
def state (saved : CanonicalCodec.Bits) (work : PaidRationalZero.Slot → CanonicalCodec.Bits) :
    Slot → CanonicalCodec.Bits := StackCall.leftFrame (Stacks.stackPair saved []) work

/-- Definition of get Zero in the Raw Machine construction. -/
def getZero (v : Local) := v.1
/-- Definition of put Zero in the Raw Machine construction. -/
def putZero (v : Local) (w : PaidRationalZero.Local) : Local := (w,v.2)
/-- Definition of get IO in the Raw Machine construction. -/
def getIO (v : Local) := v.2
/-- Definition of put IO in the Raw Machine construction. -/
def putIO (v : Local) (w : Option Bool) : Local := (v.1,w)
/-- Definition of copy Code in the Raw Machine construction. -/
def copyCode : Fin 3 → Slot | 0 => savedSlot | 1 => tempSlot | _ => .inl PaidRationalZero.rawSlot

/-- Definition of program in the Raw Machine construction. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .copy l => StackCall.stmt copyCode Label.copy (.zero default) getIO putIO (NatEmit.program l)
  | .zero l => StackCall.stmt Sum.inl Label.zero .done getZero putZero (PaidRationalZero.program l)
  | .done => .load (fun _ => default) .halt

/-- Original `copyCode_injective` guarantee for the `PaidBoundZeroRetention` construction; the complete source hypotheses are retained. -/
private theorem copyCode_injective : Function.Injective copyCode := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [copyCode]

/-- Original `frame_target` guarantee for the `PaidBoundZeroRetention` construction; the complete source hypotheses are retained. -/
private theorem frame_target (S T : Slot → CanonicalCodec.Bits) (data : Fin 3 → CanonicalCodec.Bits)
    (hi : ∀ k,T (copyCode k)=data k)
    (ho : ∀ j,(∀ k,copyCode k≠j) → T j=S j) : StackCall.frame copyCode S data=T := by
  classical
  funext j
  by_cases hj : ∃ k,copyCode k=j
  · obtain ⟨k,rfl⟩ := hj
    rw [StackCall.frame_at copyCode S data copyCode_injective,hi]
  · rw [WordValidator.frame_outside copyCode S data j (by simpa using hj)]
    exact (ho j (by simpa using hj)).symm

/-- A real readonly copy preserves the sole original bound answer and
prepares the native zero tester. The copy's quadratic clock is paid. -/
theorem copy_call (bits : CanonicalCodec.Bits) :
    Stacks.Execution program ⟨some (.copy .emit),default,state bits (fun _ => [])⟩
      ⟨some (.zero default),default,
        state bits (Function.update (fun _ => []) PaidRationalZero.rawSlot bits.reverse)⟩
      (25*(1+bits.length)^2) := by
  let S := state bits (fun _ => [])
  let T := state bits (Function.update (fun _ => []) PaidRationalZero.rawSlot bits.reverse)
  have hi : StackCall.frame copyCode S (Parsing.triple bits [] [])=S :=
    StackCall.frame_same copyCode S _ copyCode_injective (by intro k; fin_cases k <;> rfl)
  have hf : StackCall.frame copyCode S (Parsing.triple bits [] bits.reverse)=T := by
    apply frame_target S T
    · intro k; fin_cases k <;> rfl
    · intro j hj
      cases j with
      | inl k =>
        have hk : k≠PaidRationalZero.rawSlot := fun h => hj 2 (congrArg Sum.inl h.symm)
        dsimp only [S,T,state,StackCall.leftFrame,Sum.elim]
        simp only [Function.update_of_ne hk]
      | inr k =>
        fin_cases k
        · exact (hj 0 rfl).elim
        · exact (hj 1 rfl).elim
  obtain ⟨hr,hc⟩ := NatEmit.copy_complete bits [] none
  obtain ⟨hn,hnc⟩ := StackCall.execution copyCode Label.copy (.zero default) getIO putIO
    (StackCall.frame copyCode S)
    (fun data k => StackCall.frame_at copyCode S data copyCode_injective k)
    (fun data k b => StackCall.frame_update copyCode S data copyCode_injective k b)
    (fun _ _ => rfl) (fun _ _ _ => rfl) NatEmit.program program (fun _ => rfl)
    default (2*bits.length+3) _ _ hr
  have hv : putIO (default : Local) none=default := rfl
  simp only [List.append_nil] at hn
  refine ⟨2*bits.length+3,?_,?_⟩
  · simpa only [StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,
      Option.getD_none,hi,hf,hv] using hn
  · have hb := NatEmit.copy_clock_bound bits [] none
    simp only [List.length_nil,Nat.add_zero] at hb
    simpa only [StackCall.cfg,Option.map_some,Option.getD_some,hi,hv] using hnc.trans_le hb

/-- The same copied answer is tested while its saved original bytes remain
frozen. No second bound-program call is used. -/
theorem zero_call (q : RedundantRational.Frac) :
    Stacks.Execution program
      ⟨some (.zero default),default,
        state (PaidRationalBridge.encode q) (TM2.init PaidRationalZero.rawSlot (PaidRationalBridge.encode q).reverse : PaidRationalZero.Config).stk⟩
      ⟨some .done,default,state (PaidRationalBridge.encode q)
        (Function.update (fun _ => []) PaidRationalZero.outputSlot [decide (q.num.1=q.num.2)])⟩
      (11000*(1+(PaidRationalBridge.encode q).length)^2) := by
  obtain ⟨steps,hr,hc⟩ := PaidRationalZero.source_exec q
  obtain ⟨hn,hnc⟩ := StackCall.execution Sum.inl Label.zero .done getZero putZero
    (StackCall.leftFrame (Stacks.stackPair (PaidRationalBridge.encode q) []))
    (fun S k => StackCall.leftFrame_at (Stacks.stackPair (PaidRationalBridge.encode q) []) S k)
    (fun S k b => StackCall.leftFrame_update (Stacks.stackPair (PaidRationalBridge.encode q) []) S k b)
    (fun _ _ => rfl) (fun _ _ _ => rfl) PaidRationalZero.program program (fun _ => rfl)
    default steps _ _ hr
  have hdefault : putZero (default : Local) default = default := rfl
  refine ⟨steps,?_,?_⟩
  · simpa only [TM2.init,hdefault,StackCall.cfg,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,state] using hn
  · simpa only [TM2.init,hdefault,StackCall.cfg,Option.map_some,Option.getD_some,state] using hnc.trans_le hc

/-- Original `retained_zero_execution` guarantee for the `PaidBoundZeroRetention` construction; the complete source hypotheses are retained. -/
theorem retained_zero_execution (q : RedundantRational.Frac) :
    Stacks.Execution program
      ⟨some (.copy .emit),default,state (PaidRationalBridge.encode q) (fun _ => [])⟩
      ⟨none,default,state (PaidRationalBridge.encode q)
        (Function.update (fun _ => []) PaidRationalZero.outputSlot [decide (q.num.1=q.num.2)])⟩
      (11026*(1+(PaidRationalBridge.encode q).length)^2) := by
  have ee := (copy_call (PaidRationalBridge.encode q)).trans (zero_call q)
  have hf : Stacks.Execution program
      ⟨some .done,default,state (PaidRationalBridge.encode q)
        (Function.update (fun _ => []) PaidRationalZero.outputSlot [decide (q.num.1=q.num.2)])⟩
      ⟨none,default,state (PaidRationalBridge.encode q)
        (Function.update (fun _ => []) PaidRationalZero.outputSlot [decide (q.num.1=q.num.2)])⟩ 1 :=
    ⟨1,rfl,le_rfl⟩
  apply (ee.trans hf).mono
  have hp : 1≤(1+(PaidRationalBridge.encode q).length)^2 := Nat.one_le_pow 2 _ (by omega)
  omega

end PaidBoundZeroRetention
end Qatlib.Concepts.EffectiveGauge.RawMachine
