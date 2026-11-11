/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidConditionalBoundEmitter

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Conditional Bound Bank Execution

Raw Machine constructions for Effective Gauge.
Defines `higherLabel`, `higherConfig`, `higherPrefixBudget`.
Proves `collected_step`, `higher_prefix`, `first_collected`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidConditionalBoundBank

/-- Definition of higher Label in the Raw Machine construction. -/
def higherLabel {states : ℕ} (n : ℕ) : Label states :=
  if h : n<9 then .begin ⟨n,h⟩ else .emit 8 0 0

/-- Definition of higher Config in the Raw Machine construction. -/
def higherConfig (states : ℕ) (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) : Config states :=
  ⟨some (higherLabel n),default,sourceState (PaidBoundBank.collected replies n) [false] (fun _ => [])⟩

/-- Definition of higher Prefix Budget in the Raw Machine construction. -/
def higherPrefixBudget (replies : Fin 9 → CanonicalCodec.Bits) (time : Fin 9 → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => higherPrefixBudget replies time k+
      if h : k+1<9 then PaidBoundBank.stageBudget ⟨k+1,h⟩ (replies ⟨k+1,h⟩) (time ⟨k+1,h⟩) else 0

/-- Original `collected_step` guarantee for the `PaidConditionalBoundBankExecution` construction; the complete source hypotheses are retained. -/
private theorem collected_step (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) (hn : n<9) :
    Function.update (PaidBoundBank.collected replies n) ⟨n,hn⟩ (replies ⟨n,hn⟩)=PaidBoundBank.collected replies (n+1) := by
  funext j
  by_cases h : j=⟨n,hn⟩
  · subst j; simp [PaidBoundBank.collected]
  · have hv : j.val≠n := fun he => h (Fin.ext he)
    rw [Function.update_of_ne h]
    dsimp only [PaidBoundBank.collected]
    split_ifs <;> first | rfl | omega

/-- Original `higher_prefix` guarantee for the `PaidConditionalBoundBankExecution` construction; the complete source hypotheses are retained. -/
theorem higher_prefix {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (replies : Fin 9 → CanonicalCodec.Bits) (time space : Fin 9 → ℕ)
    (hrun : ∀ i,CanonicalCodec.Runs machine (PaidBoundBank.queryBits i) (replies i) (time i) (space i))
    (k : ℕ) (hk : k≤8) :
    Stacks.Execution (program machine) (higherConfig states replies 1)
      (higherConfig states replies (k+1)) (higherPrefixBudget replies time k) := by
  induction k with
  | zero => exact ⟨0,rfl,le_rfl⟩
  | succ k ih =>
    have hn9 : k+1<9 := by omega
    let i : Fin 9 := ⟨k+1,hn9⟩
    have ee := source_stage machine i (PaidBoundBank.collected replies (k+1)) [false]
      (replies i) (time i) (space i) (hrun i) (by simp [PaidBoundBank.collected,i])
    rw [collected_step replies (k+1) hn9] at ee
    have hi : higherConfig states replies (k+1)=
        ⟨some (.begin i),default,sourceState (PaidBoundBank.collected replies (k+1)) [false] (fun _ => [])⟩ := by
      simp only [higherConfig,higherLabel,dif_pos hn9,i]
    have hne : i≠0 := by
      intro h
      have hv := congrArg Fin.val h
      dsimp only [i,Fin.val_zero] at hv
      omega
    have hl : afterStore i=higherLabel (states := states) (k+1+1) := by
      simp only [afterStore,if_neg hne,higherLabel]
      rfl
    have ho : higherConfig states replies (k+1+1)=
        ⟨some (afterStore i),default,sourceState (PaidBoundBank.collected replies (k+1+1)) [false] (fun _ => [])⟩ := by
      rw [hl]
      rfl
    rw [←hi,←ho] at ee
    simpa only [higherPrefixBudget,dif_pos hn9] using (ih (by omega)).trans ee

/-- Only the used branch contributes source and emitter clocks. -/
def bankBudget (replies : Fin 9 → CanonicalCodec.Bits) (time : Fin 9 → ℕ) (flag : Bool) : ℕ :=
  (PaidBoundBank.stageBudget 0 (replies 0) (time 0)+11033*(1+(replies 0).length)^2)+
    if flag then emitPrefixBudget replies 0 true 1+1 else
      higherPrefixBudget replies time 8+(emitPrefixBudget replies 8 false 9+1)

/-- Original `first_collected` guarantee for the `PaidConditionalBoundBankExecution` construction; the complete source hypotheses are retained. -/
private theorem first_collected (replies : Fin 9 → CanonicalCodec.Bits) :
    Function.update (fun _ => []) 0 (replies 0)=PaidBoundBank.collected replies 1 := by
  funext j
  by_cases h : j=0
  · subst j; simp [PaidBoundBank.collected]
  · have hj : j.val≠0 := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h,PaidBoundBank.collected,if_neg (show ¬j.val<1 by omega)]

/-- Original `first_active` guarantee for the `PaidConditionalBoundBankExecution` construction; the complete source hypotheses are retained. -/
private theorem first_active (replies : Fin 9 → CanonicalCodec.Bits) :
    Function.update (fun _ => []) 0 (replies 0)=activeReplies replies 0 := by
  funext j
  by_cases h : j=0
  · subst j; simp [activeReplies]
  · have hj : j.val≠0 := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h,activeReplies,Fin.val_zero,if_neg (show ¬j.val≤0 by omega)]

/-- Original `all_active` guarantee for the `PaidConditionalBoundBankExecution` construction; the complete source hypotheses are retained. -/
private theorem all_active (replies : Fin 9 → CanonicalCodec.Bits) : activeReplies replies 8=replies := by
  funext j
  exact if_pos (by have hj := j.isLt; omega)

/-- The first bound is called once, then the actual generated flag selects
one answer or the remaining eight calls. The same run writes the wire payload. -/
theorem bank_execution {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (answers : Fin 9 → RedundantRational.Frac) (time space : Fin 9 → ℕ)
    (hrun : ∀ i,i.val≤(if decide ((answers 0).num.1=(answers 0).num.2) then (0 : Fin 9) else 8).val →
      CanonicalCodec.Runs machine (PaidBoundBank.queryBits i)
        (PaidRationalBridge.encode (answers i)) (time i) (space i)) :
    Stacks.Execution (program machine) (TM2.init sourceRaw [])
      ⟨none,default,Function.update (fun _ => []) outputSlot
        (bankOutput (fun i => PaidRationalBridge.encode (answers i))
          (if decide ((answers 0).num.1=(answers 0).num.2) then 0 else 8)
          (decide ((answers 0).num.1=(answers 0).num.2))).reverse⟩
      (bankBudget (fun i => PaidRationalBridge.encode (answers i)) time
        (decide ((answers 0).num.1=(answers 0).num.2))) := by
  let replies := fun i => PaidRationalBridge.encode (answers i)
  have ee := first_and_choose machine (answers 0) (time 0) (space 0) (hrun 0 (Nat.zero_le _))
  cases hflag : decide ((answers 0).num.1=(answers 0).num.2) with
  | false =>
    simp only [hflag,branchChoice,Bool.false_eq_true,if_false] at ee ⊢
    have hs : sourceState (Function.update (fun _ => []) 0 (replies 0)) [false] (fun _ => [])=
        sourceState (PaidBoundBank.collected replies 1) [false] (fun _ => []) := by rw [first_collected]
    have hi : higherConfig states replies 1=
        ⟨some (.begin 1),default,sourceState (Function.update (fun _ => []) 0 (replies 0)) [false] (fun _ => [])⟩ := by
      simp only [higherConfig,higherLabel,show 1<9 by decide,dif_pos]
      rw [←hs]
      rfl
    simp only [hflag,Bool.false_eq_true,if_false] at hrun
    have hm := higher_prefix machine replies time space
      (fun i => hrun i (by have hi := i.isLt; omega)) 8 (by decide)
    have he := emit_active machine replies 8 false
    have ha : PaidBoundBank.collected replies 9=replies := by funext j; exact if_pos j.isLt
    have ho : higherConfig states replies 9=
        ⟨some (.emit 8 0 0),default,sourceState (activeReplies replies 8) [false] (fun _ => [])⟩ := by
      simp [higherConfig,higherLabel,ha,all_active]
    rw [hi,ho] at hm
    have hh := (ee.trans hm).trans he
    simpa [bankBudget,replies,Nat.add_assoc] using hh
  | true =>
    simp only [hflag,branchChoice,if_true] at ee ⊢
    have ha := first_active replies
    rw [ha] at ee
    have he := emit_active machine replies 0 true
    simpa [bankBudget,replies] using ee.trans he

end PaidConditionalBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
