/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidConditionalBoundSourceCall

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Conditional Bound Emitter

Raw Machine constructions for Effective Gauge.
Defines `activeReplies`, `emitLabel`, `emitConfig`.
Proves `emitCode_injective`, `emit_stage`, `remaining_step`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open CanonicalCodec.TM
namespace PaidConditionalBoundBank

/-- Original `emitCode_injective` guarantee for the `PaidConditionalBoundEmitter` construction; the complete source hypotheses are retained. -/
private theorem emitCode_injective (i : Fin 9) : Function.Injective (emitCode i) := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [emitCode]

/-- Original `emit_stage` guarantee for the `PaidConditionalBoundEmitter` construction; the complete source hypotheses are retained. -/
theorem emit_stage {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (stop i : Fin 9) (saved : Fin 9 → CanonicalCodec.Bits) (out : CanonicalCodec.Bits) :
    Stacks.Execution (program machine)
      ⟨some (.emit stop i 0),default,sourceState saved out (fun _ => [])⟩
      ⟨some (afterEmit stop i),default,
        sourceState (Function.update saved i []) ((saved i).reverse++out) (fun _ => [])⟩
      (PaidBoundBank.emitBudget saved out i) := by
  let S := sourceState saved out (fun _ => [])
  have ee := transfer_call machine (emitCode i) (emitCode_injective i)
    (Label.emit stop i) (afterEmit stop i) (fun _ => rfl) S
  simp only [show emitCode i 0 = savedSlot i from rfl,
    show emitCode i 1 = outputSlot from rfl] at ee
  have hs : S (savedSlot i)=saved i := rfl
  have ho : S outputSlot=out := rfl
  have hf : Function.update (Function.update S (savedSlot i) []) outputSlot ((saved i).reverse++out)=
      sourceState (Function.update saved i []) ((saved i).reverse++out) (fun _ => []) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k =>
      cases k with
      | inl k => rfl
      | inr k =>
        cases k with
        | inl j =>
          dsimp only [S,sourceState,state,savedSlot,outputSlot,Sum.elim]
          simp only [Function.update_apply]
          grind
        | inr j => fin_cases j <;> rfl
  rw [hs,ho,hf] at ee
  exact ee

/-- Definition of active Replies in the Raw Machine construction. -/
def activeReplies (replies : Fin 9 → CanonicalCodec.Bits) (stop : Fin 9) (i : Fin 9) : CanonicalCodec.Bits :=
  if i.val≤stop.val then replies i else []

/-- Definition of emit Label in the Raw Machine construction. -/
def emitLabel {states : ℕ} (stop : Fin 9) (n : ℕ) : Label states :=
  if h : n≤stop.val then .emit stop ⟨n,by omega⟩ 0 else .done

/-- Definition of emit Config in the Raw Machine construction. -/
def emitConfig (states : ℕ) (replies : Fin 9 → CanonicalCodec.Bits) (stop : Fin 9) (flag : Bool) (n : ℕ) : Config states :=
  ⟨some (emitLabel stop n),default,
    sourceState (PaidBoundBank.remaining (activeReplies replies stop) n)
      ((PaidBoundBank.emitted (activeReplies replies stop) n).reverse++[flag]) (fun _ => [])⟩

/-- Definition of emit Prefix Budget in the Raw Machine construction. -/
def emitPrefixBudget (replies : Fin 9 → CanonicalCodec.Bits) (stop : Fin 9) (flag : Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => emitPrefixBudget replies stop flag n+
      if h : n≤stop.val then PaidBoundBank.emitBudget (PaidBoundBank.remaining (activeReplies replies stop) n)
        ((PaidBoundBank.emitted (activeReplies replies stop) n).reverse++[flag]) ⟨n,by omega⟩ else 0

/-- Original `remaining_step` guarantee for the `PaidConditionalBoundEmitter` construction; the complete source hypotheses are retained. -/
private theorem remaining_step (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) (hn : n<9) :
    Function.update (PaidBoundBank.remaining replies n) ⟨n,hn⟩ []=PaidBoundBank.remaining replies (n+1) := by
  funext j
  by_cases h : j=⟨n,hn⟩
  · subst j; simp [PaidBoundBank.remaining]
  · have hv : j.val≠n := fun he => h (Fin.ext he)
    rw [Function.update_of_ne h]
    dsimp only [PaidBoundBank.remaining]
    split_ifs <;> first | rfl | omega

/-- Original `emit_prefix` guarantee for the `PaidConditionalBoundEmitter` construction; the complete source hypotheses are retained. -/
theorem emit_prefix {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (replies : Fin 9 → CanonicalCodec.Bits) (stop : Fin 9) (flag : Bool) (n : ℕ) (hn : n≤stop.val+1) :
    Stacks.Execution (program machine) (emitConfig states replies stop flag 0)
      (emitConfig states replies stop flag n) (emitPrefixBudget replies stop flag n) := by
  induction n with
  | zero => exact ⟨0,rfl,le_rfl⟩
  | succ n ih =>
    have hns : n≤stop.val := by omega
    have hn9 : n<9 := by omega
    let i : Fin 9 := ⟨n,hn9⟩
    have ee := emit_stage machine stop i (PaidBoundBank.remaining (activeReplies replies stop) n)
      ((PaidBoundBank.emitted (activeReplies replies stop) n).reverse++[flag])
    rw [remaining_step (activeReplies replies stop) n hn9] at ee
    have hreply : PaidBoundBank.remaining (activeReplies replies stop) n i=activeReplies replies stop i := by
      simp [PaidBoundBank.remaining,i]
    rw [hreply] at ee
    have hi : emitConfig states replies stop flag n=
        ⟨some (.emit stop i 0),default,sourceState (PaidBoundBank.remaining (activeReplies replies stop) n)
          ((PaidBoundBank.emitted (activeReplies replies stop) n).reverse++[flag]) (fun _ => [])⟩ := by
      simp only [emitConfig,emitLabel,dif_pos hns,i]
    have hl : emitLabel (states := states) stop (n+1)=afterEmit stop i := by
      dsimp only [emitLabel,afterEmit,i]
      by_cases h : n<stop.val
      · simp only [dif_pos h,dif_pos (show n+1≤stop.val by omega)]
      · simp only [dif_neg h,dif_neg (show ¬n+1≤stop.val by omega)]
    have ho : emitConfig states replies stop flag (n+1)=
        ⟨some (afterEmit stop i),default,sourceState (PaidBoundBank.remaining (activeReplies replies stop) (n+1))
          ((activeReplies replies stop i).reverse++
            ((PaidBoundBank.emitted (activeReplies replies stop) n).reverse++[flag])) (fun _ => [])⟩ := by
      simp only [emitConfig,hl,PaidBoundBank.emitted,dif_pos hn9,List.reverse_append,List.append_assoc,i]
    rw [←hi,←ho] at ee
    simpa only [emitPrefixBudget,dif_pos hns] using (ih (by omega)).trans ee

/-- Original `empty_output` guarantee for the `PaidConditionalBoundEmitter` construction; the complete source hypotheses are retained. -/
private theorem empty_output (out : CanonicalCodec.Bits) :
    sourceState (fun _ => []) out (fun _ => [])=Function.update (fun _ => []) outputSlot out := by
  funext k
  cases k with
  | inl k => rfl
  | inr k =>
    cases k with
    | inl k => rfl
    | inr k =>
      cases k with
      | inl k => rfl
      | inr k => fin_cases k <;> rfl

/-- Definition of bank Output in the Raw Machine construction. -/
def bankOutput (replies : Fin 9 → CanonicalCodec.Bits) (stop : Fin 9) (flag : Bool) : CanonicalCodec.Bits :=
  flag::PaidBoundBank.emitted (activeReplies replies stop) (stop.val+1)

/-- Emit exactly the active answers, preserving the tested branch as the
first wire bit and leaving all other banks empty. -/
theorem emit_active {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (replies : Fin 9 → CanonicalCodec.Bits) (stop : Fin 9) (flag : Bool) :
    Stacks.Execution (program machine)
      ⟨some (.emit stop 0 0),default,sourceState (activeReplies replies stop) [flag] (fun _ => [])⟩
      ⟨none,default,Function.update (fun _ => []) outputSlot (bankOutput replies stop flag).reverse⟩
      (emitPrefixBudget replies stop flag (stop.val+1)+1) := by
  have ee := emit_prefix machine replies stop flag (stop.val+1) le_rfl
  have hi : emitConfig states replies stop flag 0=
      ⟨some (.emit stop 0 0),default,sourceState (activeReplies replies stop) [flag] (fun _ => [])⟩ := by
    have h0 : PaidBoundBank.remaining (activeReplies replies stop) 0=activeReplies replies stop := by
      funext j; exact if_neg (Nat.not_lt_zero j.val)
    simp [emitConfig,emitLabel,h0,PaidBoundBank.emitted]
  have hz : PaidBoundBank.remaining (activeReplies replies stop) (stop.val+1)=(fun _ => []) := by
    funext j
    dsimp only [PaidBoundBank.remaining,activeReplies]
    split_ifs <;> first | rfl | omega
  have ho : emitConfig states replies stop flag (stop.val+1)=
      ⟨some .done,default,Function.update (fun _ => []) outputSlot (bankOutput replies stop flag).reverse⟩ := by
    simp [emitConfig,emitLabel,hz,empty_output,bankOutput,List.reverse_cons]
  rw [hi,ho] at ee
  have hf : Stacks.Execution (program machine)
      ⟨some .done,default,Function.update (fun _ => []) outputSlot (bankOutput replies stop flag).reverse⟩
      ⟨none,default,Function.update (fun _ => []) outputSlot (bankOutput replies stop flag).reverse⟩ 1 :=
    ⟨1,rfl,le_rfl⟩
  exact ee.trans hf

end PaidConditionalBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
