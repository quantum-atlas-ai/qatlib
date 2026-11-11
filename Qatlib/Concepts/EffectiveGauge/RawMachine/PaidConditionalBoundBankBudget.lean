/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidConditionalBoundBankMachine

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Conditional Bound Bank Budget

Raw Machine constructions for Effective Gauge.
Proves `active_length`, `output_length`, `higherPrefixBudget_bound`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidConditionalBoundBank

/-- Original `active_length` guarantee for the `PaidConditionalBoundBankBudget` construction; the complete source hypotheses are retained. -/
private theorem active_length (replies : Fin 9 → CanonicalCodec.Bits) (stop : Fin 9) (B : ℕ)
    (hsize : ∀ i,i.val≤stop.val → (replies i).length≤B) :
    ∀ i,(activeReplies replies stop i).length≤B := by
  intro i
  dsimp only [activeReplies]
  split_ifs with hi
  · exact hsize i hi
  · exact Nat.zero_le _

/-- Original `output_length` guarantee for the `PaidConditionalBoundBankBudget` construction; the complete source hypotheses are retained. -/
theorem output_length (replies : Fin 9 → CanonicalCodec.Bits) (stop : Fin 9) (flag : Bool) (B : ℕ)
    (hsize : ∀ i,i.val≤stop.val → (replies i).length≤B) :
    (bankOutput replies stop flag).length≤9*B+1 := by
  have hh := PaidBoundBank.emitted_length (activeReplies replies stop) B
    (active_length replies stop B hsize) (stop.val+1)
  simp only [bankOutput,List.length_cons]
  have hs := stop.isLt
  nlinarith only [hh,hs,Nat.zero_le B]

/-- Original `higherPrefixBudget_bound` guarantee for the `PaidConditionalBoundBankBudget` construction; the complete source hypotheses are retained. -/
theorem higherPrefixBudget_bound (replies : Fin 9 → CanonicalCodec.Bits) (time : Fin 9 → ℕ)
    (B : ℕ) (hsize : ∀ i,(replies i).length≤B) (htime : ∀ i,time i≤B) (k : ℕ) :
    higherPrefixBudget replies time k≤k*1006000*(1+B)^2 := by
  induction k with
  | zero => simp [higherPrefixBudget]
  | succ k ih =>
    rw [higherPrefixBudget]
    split_ifs with hk
    · have hs := PaidBoundBank.stageBudget_bound ⟨k+1,hk⟩ (replies ⟨k+1,hk⟩) (time ⟨k+1,hk⟩) B
        (hsize _) (htime _)
      nlinarith only [ih,hs]
    · nlinarith only [ih,Nat.zero_le ((1+B)^2)]

/-- Original `emitPrefixBudget_bound` guarantee for the `PaidConditionalBoundBankBudget` construction; the complete source hypotheses are retained. -/
theorem emitPrefixBudget_bound (replies : Fin 9 → CanonicalCodec.Bits) (stop : Fin 9) (flag : Bool)
    (B : ℕ) (hsize : ∀ i,i.val≤stop.val → (replies i).length≤B) (n : ℕ) (hn : n≤stop.val+1) :
    emitPrefixBudget replies stop flag n≤n*30*(1+B)^2 := by
  have ha := active_length replies stop B hsize
  induction n with
  | zero => simp [emitPrefixBudget]
  | succ n ih =>
    have hns : n≤stop.val := by omega
    have hn9 : n<9 := by omega
    have hh := ih (by omega)
    have hlen := PaidBoundBank.emitted_length (activeReplies replies stop) B ha n
    have hr := ha ⟨n,hn9⟩
    have hr2 := Nat.mul_le_mul hr hr
    have hout : (PaidBoundBank.emitted (activeReplies replies stop) n).length+1≤9*B+1 := by nlinarith
    have hm := Nat.mul_le_mul hr hout
    have hp : 1≤(1+B)^2 := Nat.one_le_pow 2 _ (by omega)
    rw [emitPrefixBudget,dif_pos hns]
    have he : PaidBoundBank.emitBudget (PaidBoundBank.remaining (activeReplies replies stop) n)
        ((PaidBoundBank.emitted (activeReplies replies stop) n).reverse++[flag]) ⟨n,hn9⟩≤30*(1+B)^2 := by
      simp only [PaidBoundBank.emitBudget,PaidBoundBank.remaining,Nat.lt_irrefl,if_false,
        List.length_append,List.length_reverse,List.length_singleton]
      nlinarith only [hr2,hr,hm,hp,Nat.zero_le B]
    nlinarith only [hh,he]

/-- Neither time nor raw field lengths of unused high-order answers occur
in these premises on the zero-first branch. -/
theorem bankBudget_bound (replies : Fin 9 → CanonicalCodec.Bits) (time : Fin 9 → ℕ) (flag : Bool) (B : ℕ)
    (hsize : ∀ i,i.val≤(if flag then (0 : Fin 9) else 8).val → (replies i).length≤B)
    (htime : ∀ i,i.val≤(if flag then (0 : Fin 9) else 8).val → time i≤B) :
    1+bankBudget replies time flag+
        (1+(bankOutput replies (if flag then 0 else 8) flag).length)^2≤11000000*(1+B)^2 := by
  have hs0 := hsize 0 (Nat.zero_le _)
  have ht0 := htime 0 (Nat.zero_le _)
  have hfirst := PaidBoundBank.stageBudget_bound 0 (replies 0) (time 0) B hs0 ht0
  have hz := Nat.pow_le_pow_left (Nat.add_le_add_left hs0 1) 2
  have ho := output_length replies (if flag then 0 else 8) flag B hsize
  have hw : 1+(bankOutput replies (if flag then 0 else 8) flag).length≤10*(1+B) := by omega
  have hw2 := Nat.mul_le_mul hw hw
  have hp : 1≤(1+B)^2 := Nat.one_le_pow 2 _ (by omega)
  cases flag with
  | false =>
    simp only [Bool.false_eq_true,if_false] at hsize htime hfirst hz hw2 ⊢
    have hs : ∀ i,(replies i).length≤B := fun i => hsize i (by have hi := i.isLt; omega)
    have ht : ∀ i,time i≤B := fun i => htime i (by have hi := i.isLt; omega)
    have hh := higherPrefixBudget_bound replies time B hs ht 8
    have he := emitPrefixBudget_bound replies 8 false B hsize 9 (by decide)
    dsimp only [bankBudget]
    simp only [Bool.false_eq_true,if_false]
    nlinarith only [hfirst,hz,hh,he,hw2,hp]
  | true =>
    simp only [if_true] at hsize htime hfirst hz hw2 ⊢
    have he := emitPrefixBudget_bound replies 0 true B hsize 1 (by decide)
    dsimp only [bankBudget]
    simp only [if_true]
    nlinarith only [hfirst,hz,he,hw2,hp]

/-- One source-specialized binary machine with a bound on exactly the
queries its generated runtime flag activates. Space is still a quadratic
visited-radius estimate, not the original solver's linear-space theorem. -/
theorem bank_machine_quadratic {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) :
    ∃ (compiledStates : ℕ) (compiled : TM0.Machine CanonicalCodec.TM.Symbol (Fin (compiledStates+1)))
      (coef : ℕ), 0<coef ∧
      ∀ (answers : Fin 9 → RedundantRational.Frac) (time space : Fin 9 → ℕ) (B : ℕ),
        let replies := fun i => PaidRationalBridge.encode (answers i)
        let flag := decide ((answers 0).num.1=(answers 0).num.2)
        let stop : Fin 9 := if flag then 0 else 8
        (∀ i,i.val≤stop.val → CanonicalCodec.Runs machine (PaidBoundBank.queryBits i) (replies i) (time i) (space i)) →
        (∀ i,i.val≤stop.val → (replies i).length≤B) → (∀ i,i.val≤stop.val → time i≤B) →
        CanonicalCodec.Runs compiled [] (bankOutput replies stop flag) (coef*(1+B)^2) (coef*(1+B)^2) := by
  obtain ⟨compiledStates,compiled,coef,hcoef,hcompiled⟩ := bank_machine machine
  refine ⟨compiledStates,compiled,coef*11000000,by omega,?_⟩
  intro answers time space B
  dsimp only
  intro hrun hsize htime
  have hh := hcompiled answers time space hrun
  have hb := Nat.mul_le_mul_left coef (bankBudget_bound (fun i => PaidRationalBridge.encode (answers i)) time
    (decide ((answers 0).num.1=(answers 0).num.2)) B hsize htime)
  rw [←Nat.mul_assoc] at hb
  exact runs_mono hh hb hb

end PaidConditionalBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
