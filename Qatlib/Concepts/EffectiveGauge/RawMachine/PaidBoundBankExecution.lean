/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundBankControl

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Bank Execution

Raw Machine constructions for Effective Gauge.
Defines `collected`, `sourceLabel`, `sourceConfig`.
Proves `collected_step`, `source_prefix`, `remaining_step`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport
open CanonicalCodec.TM
namespace PaidBoundBank

/-- Definition of collected in the Raw Machine construction. -/
def collected (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) (j : Fin 9) : CanonicalCodec.Bits :=
  if j.val<n then replies j else []

/-- Definition of source Label in the Raw Machine construction. -/
def sourceLabel {states : ℕ} (n : ℕ) : Label states :=
  if h : n<9 then .begin ⟨n,h⟩ else .emit 0 0

/-- Definition of source Config in the Raw Machine construction. -/
def sourceConfig (states : ℕ) (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) : Config states :=
  ⟨some (sourceLabel n),default,frame (collected replies n) [] (fun _ => [])⟩

/-- Definition of source Prefix Budget in the Raw Machine construction. -/
def sourcePrefixBudget (replies : Fin 9 → CanonicalCodec.Bits) (time : Fin 9 → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sourcePrefixBudget replies time n+
      if h : n<9 then stageBudget ⟨n,h⟩ (replies ⟨n,h⟩) (time ⟨n,h⟩) else 0

/-- Original `collected_step` guarantee for the `PaidBoundBankExecution` construction; the complete source hypotheses are retained. -/
private theorem collected_step (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) (hn : n<9) :
    Function.update (collected replies n) ⟨n,hn⟩ (replies ⟨n,hn⟩)=collected replies (n+1) := by
  funext j
  by_cases h : j=⟨n,hn⟩
  · subst j
    simp [collected]
  · have hv : j.val≠n := fun he => h (Fin.ext he)
    rw [Function.update_of_ne h]
    dsimp only [collected]
    split_ifs <;> first | rfl | omega

/-- Original `source_prefix` guarantee for the `PaidBoundBankExecution` construction; the complete source hypotheses are retained. -/
theorem source_prefix {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (replies : Fin 9 → CanonicalCodec.Bits) (time space : Fin 9 → ℕ)
    (hrun : ∀ i, CanonicalCodec.Runs machine (queryBits i) (replies i) (time i) (space i))
    (n : ℕ) (hn : n≤9) :
    Stacks.Execution (program machine) (sourceConfig states replies 0)
      (sourceConfig states replies n) (sourcePrefixBudget replies time n) := by
  induction n with
  | zero => exact ⟨0,rfl,le_rfl⟩
  | succ n ih =>
    have hn9 : n<9 := by omega
    let i : Fin 9 := ⟨n,hn9⟩
    have ee := source_stage machine i (collected replies n) [] (replies i) (time i) (space i)
      (hrun i) (by simp [collected,i])
    rw [collected_step replies n hn9] at ee
    have hi : sourceConfig states replies n=
        ⟨some (.begin i),default,frame (collected replies n) [] (fun _ => [])⟩ := by
      simp [sourceConfig,sourceLabel,hn9,i]
    have ho : sourceConfig states replies (n+1)=
        ⟨some (nextSource i),default,frame (collected replies (n+1)) [] (fun _ => [])⟩ := rfl
    rw [←hi,←ho] at ee
    simpa only [sourcePrefixBudget,dif_pos hn9] using (ih (by omega)).trans ee

/-- Definition of remaining in the Raw Machine construction. -/
def remaining (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) (j : Fin 9) : CanonicalCodec.Bits :=
  if j.val<n then [] else replies j

/-- Definition of emitted in the Raw Machine construction. -/
def emitted (replies : Fin 9 → CanonicalCodec.Bits) : ℕ → CanonicalCodec.Bits
  | 0 => []
  | n+1 => emitted replies n++if h : n<9 then replies ⟨n,h⟩ else []

/-- Definition of emit Label in the Raw Machine construction. -/
def emitLabel {states : ℕ} (n : ℕ) : Label states :=
  if h : n<9 then .emit ⟨n,h⟩ 0 else .done

/-- Definition of emit Config in the Raw Machine construction. -/
def emitConfig (states : ℕ) (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) : Config states :=
  ⟨some (emitLabel n),default,frame (remaining replies n) (emitted replies n).reverse (fun _ => [])⟩

/-- Definition of emit Prefix Budget in the Raw Machine construction. -/
def emitPrefixBudget (replies : Fin 9 → CanonicalCodec.Bits) : ℕ → ℕ
  | 0 => 0
  | n+1 => emitPrefixBudget replies n+
      if h : n<9 then emitBudget (remaining replies n) (emitted replies n).reverse ⟨n,h⟩ else 0

/-- Original `remaining_step` guarantee for the `PaidBoundBankExecution` construction; the complete source hypotheses are retained. -/
private theorem remaining_step (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) (hn : n<9) :
    Function.update (remaining replies n) ⟨n,hn⟩ []=remaining replies (n+1) := by
  funext j
  by_cases h : j=⟨n,hn⟩
  · subst j
    simp [remaining]
  · have hv : j.val≠n := fun he => h (Fin.ext he)
    rw [Function.update_of_ne h]
    dsimp only [remaining]
    split_ifs <;> first | rfl | omega

/-- Original `emit_prefix` guarantee for the `PaidBoundBankExecution` construction; the complete source hypotheses are retained. -/
theorem emit_prefix {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (replies : Fin 9 → CanonicalCodec.Bits) (n : ℕ) (hn : n≤9) :
    Stacks.Execution (program machine) (emitConfig states replies 0)
      (emitConfig states replies n) (emitPrefixBudget replies n) := by
  induction n with
  | zero => exact ⟨0,rfl,le_rfl⟩
  | succ n ih =>
    have hn9 : n<9 := by omega
    let i : Fin 9 := ⟨n,hn9⟩
    have ee := emit_stage machine i (remaining replies n) (emitted replies n).reverse
    rw [remaining_step replies n hn9] at ee
    have hreply : remaining replies n i=replies i := by simp [remaining,i]
    rw [hreply] at ee
    have hi : emitConfig states replies n=
        ⟨some (.emit i 0),default,frame (remaining replies n) (emitted replies n).reverse (fun _ => [])⟩ := by
      simp [emitConfig,emitLabel,hn9,i]
    have ho : emitConfig states replies (n+1)=
        ⟨some (nextEmit i),default,frame (remaining replies (n+1))
          ((replies i).reverse++(emitted replies n).reverse) (fun _ => [])⟩ := by
      simp only [emitConfig,emitted,dif_pos hn9,List.reverse_append]
      rfl
    rw [←hi,←ho] at ee
    simpa only [emitPrefixBudget,dif_pos hn9] using (ih (by omega)).trans ee

/-- Original `empty_frame` guarantee for the `PaidBoundBankExecution` construction; the complete source hypotheses are retained. -/
private theorem empty_frame (out : CanonicalCodec.Bits) :
    frame (fun _ => []) out (fun _ => [])=Function.update (fun _ => []) outputSlot out := by
  funext k
  cases k with
  | inl k =>
    dsimp only [frame,StackCall.leftFrame,frozen,outputSlot]
    simp only [Function.update_apply]
    grind
  | inr k =>
    cases k with
    | inl j =>
      dsimp only [frame,StackCall.leftFrame,frozen,outputSlot]
      simp only [Function.update_apply]
      grind
    | inr j =>
      fin_cases j
      rfl

/-- Definition of bank Output in the Raw Machine construction. -/
def bankOutput (replies : Fin 9 → CanonicalCodec.Bits) : CanonicalCodec.Bits := emitted replies 9

/-- Definition of bank Budget in the Raw Machine construction. -/
def bankBudget (replies : Fin 9 → CanonicalCodec.Bits) (time : Fin 9 → ℕ) : ℕ :=
  sourcePrefixBudget replies time 9+emitPrefixBudget replies 9+1

/-- Original `bank_execution` guarantee for the `PaidBoundBankExecution` construction; the complete source hypotheses are retained. -/
theorem bank_execution {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1)))
    (replies : Fin 9 → CanonicalCodec.Bits) (time space : Fin 9 → ℕ)
    (hrun : ∀ i, CanonicalCodec.Runs machine (queryBits i) (replies i) (time i) (space i)) :
    Stacks.Execution (program machine) (TM2.init rawSlot [])
      ⟨none,default,Function.update (fun _ => []) outputSlot (bankOutput replies).reverse⟩
      (bankBudget replies time) := by
  have hs := source_prefix machine replies time space hrun 9 (by decide)
  have he := emit_prefix machine replies 9 (by decide)
  have hc : sourceConfig states replies 9=emitConfig states replies 0 := by
    have h1 : collected replies 9=replies := by
      funext j; exact if_pos j.isLt
    have h2 : remaining replies 0=replies := by
      funext j; exact if_neg (Nat.not_lt_zero j.val)
    simp [sourceConfig,sourceLabel,h1,emitConfig,emitLabel,h2,emitted]
  have hfirst : sourceConfig states replies 0=TM2.init rawSlot [] := by
    have h0 : collected replies 0=(fun _ => []) := by
      funext j; exact if_neg (Nat.not_lt_zero j.val)
    simp only [sourceConfig,sourceLabel,show 0<9 by decide,dif_pos,h0,empty_frame]
    simp only [TM2.init,Function.update_eq_self]
    rfl
  have hlast : emitConfig states replies 9=
      ⟨some .done,default,Function.update (fun _ => []) outputSlot (bankOutput replies).reverse⟩ := by
    have h0 : remaining replies 9=(fun _ => []) := by
      funext j; exact if_pos j.isLt
    simp [emitConfig,emitLabel,h0,empty_frame,bankOutput]
  rw [hfirst,hc] at hs
  rw [hlast] at he
  have hf : Stacks.Execution (program machine)
      ⟨some .done,default,Function.update (fun _ => []) outputSlot (bankOutput replies).reverse⟩
      ⟨none,default,Function.update (fun _ => []) outputSlot (bankOutput replies).reverse⟩ 1 :=
    ⟨1,rfl,le_rfl⟩
  exact (hs.trans he).trans hf

end PaidBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
