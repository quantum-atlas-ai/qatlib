/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundBankMachine

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Bank Budget

Raw Machine constructions for Effective Gauge.
Proves `queryBits_length`, `emitted_length`, `stageBudget_bound`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.WordComposition.PaidMachineSupport
open CanonicalCodec.TM
namespace PaidBoundBank

/-- Original `queryBits_length` guarantee for the `PaidBoundBankBudget` construction; the complete source hypotheses are retained. -/
theorem queryBits_length (i : Fin 9) : (queryBits i).length≤9 := by
  fin_cases i <;> decide

/-- Original `emitted_length` guarantee for the `PaidBoundBankBudget` construction; the complete source hypotheses are retained. -/
theorem emitted_length (replies : Fin 9 → CanonicalCodec.Bits) (B : ℕ)
    (hsize : ∀ i, (replies i).length≤B) (n : ℕ) :
    (emitted replies n).length≤n*B := by
  induction n with
  | zero => simp [emitted]
  | succ n ih =>
    rw [emitted,List.length_append]
    split_ifs with hn
    · have hh := hsize ⟨n,hn⟩; nlinarith only [ih,hh]
    · simp only [List.length_nil]; nlinarith only [ih,Nat.zero_le B]

/-- Original `stageBudget_bound` guarantee for the `PaidBoundBankBudget` construction; the complete source hypotheses are retained. -/
theorem stageBudget_bound (i : Fin 9) (reply : CanonicalCodec.Bits) (time B : ℕ)
    (hr : reply.length≤B) (ht : time≤B) :
    stageBudget i reply time≤1006000*(1+B)^2 := by
  have hq := queryBits_length i
  have hquery : 1+(queryBits i).length*((queryBits i).length+2)≤100 := by
    nlinarith
  have htq : 1+(queryBits i).length+time≤10*(1+B) := by omega
  have hsquare := Nat.mul_le_mul htq htq
  have hr2 := Nat.mul_le_mul hr hr
  have hpos : 1≤(1+B)^2 := Nat.one_le_pow 2 _ (by omega)
  dsimp only [stageBudget,RawCall.budget]
  nlinarith only [hquery,hsquare,hr2,hr,hpos,Nat.zero_le B]

/-- Original `sourcePrefixBudget_bound` guarantee for the `PaidBoundBankBudget` construction; the complete source hypotheses are retained. -/
theorem sourcePrefixBudget_bound (replies : Fin 9 → CanonicalCodec.Bits) (time : Fin 9 → ℕ)
    (B : ℕ) (hsize : ∀ i,(replies i).length≤B) (htime : ∀ i,time i≤B) (n : ℕ) :
    sourcePrefixBudget replies time n≤n*1006000*(1+B)^2 := by
  induction n with
  | zero => simp [sourcePrefixBudget]
  | succ n ih =>
    rw [sourcePrefixBudget]
    split_ifs with hn
    · have hh := stageBudget_bound ⟨n,hn⟩ (replies ⟨n,hn⟩) (time ⟨n,hn⟩) B
        (hsize _) (htime _)
      nlinarith only [ih,hh]
    · nlinarith only [ih,Nat.zero_le ((1+B)^2)]

/-- Original `emitPrefixBudget_bound` guarantee for the `PaidBoundBankBudget` construction; the complete source hypotheses are retained. -/
theorem emitPrefixBudget_bound (replies : Fin 9 → CanonicalCodec.Bits) (B : ℕ)
    (hsize : ∀ i,(replies i).length≤B) (n : ℕ) (hn : n≤9) :
    emitPrefixBudget replies n≤n*30*(1+B)^2 := by
  induction n with
  | zero => simp [emitPrefixBudget]
  | succ n ih =>
    have hn9 : n<9 := by omega
    have hh := ih (by omega)
    have hlen := emitted_length replies B hsize n
    have hr := hsize ⟨n,hn9⟩
    have hr2 := Nat.mul_le_mul hr hr
    have hout : (emitted replies n).length≤9*B := by nlinarith
    have hm := Nat.mul_le_mul hr hout
    have hpos : 1≤(1+B)^2 := Nat.one_le_pow 2 _ (by omega)
    rw [emitPrefixBudget,dif_pos hn9]
    have he : emitBudget (remaining replies n) (emitted replies n).reverse ⟨n,hn9⟩≤30*(1+B)^2 := by
      simp only [emitBudget,remaining,Nat.lt_irrefl,if_false,List.length_reverse]
      nlinarith only [hr2,hr,hm,hpos,Nat.zero_le B]
    nlinarith only [hh,he]

/-- Original `bankBudget_bound` guarantee for the `PaidBoundBankBudget` construction; the complete source hypotheses are retained. -/
theorem bankBudget_bound (replies : Fin 9 → CanonicalCodec.Bits) (time : Fin 9 → ℕ)
    (B : ℕ) (hsize : ∀ i,(replies i).length≤B) (htime : ∀ i,time i≤B) :
    1+bankBudget replies time+(1+(bankOutput replies).length)^2≤10000000*(1+B)^2 := by
  have hs := sourcePrefixBudget_bound replies time B hsize htime 9
  have he := emitPrefixBudget_bound replies B hsize 9 (by decide)
  have ho := emitted_length replies B hsize 9
  have hob : 1+(bankOutput replies).length≤9*(1+B) := by dsimp only [bankOutput]; omega
  have ho2 := Nat.mul_le_mul hob hob
  have hpos : 1≤(1+B)^2 := Nat.one_le_pow 2 _ (by omega)
  dsimp only [bankBudget]
  nlinarith only [hs,he,ho2,hpos,Nat.zero_le B]

/-- Actual output-writing lengths remain explicit in B. No canonical-value
size estimate, uniform loader constant, or linear-space conclusion is used. -/
theorem bank_machine_quadratic {states : ℕ}
    (machine : TM0.Machine CanonicalCodec.TM.Symbol (Fin (states+1))) :
    ∃ (compiledStates : ℕ) (compiled : TM0.Machine CanonicalCodec.TM.Symbol (Fin (compiledStates+1)))
      (coef : ℕ), 0<coef ∧
      ∀ (replies : Fin 9 → CanonicalCodec.Bits) (time space : Fin 9 → ℕ) (B : ℕ),
        (∀ i, CanonicalCodec.Runs machine (queryBits i) (replies i) (time i) (space i)) →
        (∀ i,(replies i).length≤B) → (∀ i,time i≤B) →
        CanonicalCodec.Runs compiled [] (bankOutput replies)
          (coef*(1+B)^2) (coef*(1+B)^2) := by
  obtain ⟨compiledStates,compiled,coef,hcoef,hcompiled⟩ := bank_machine machine
  refine ⟨compiledStates,compiled,coef*10000000,by omega,?_⟩
  intro replies time space B hrun hsize htime
  have hh := hcompiled replies time space hrun
  have hb := Nat.mul_le_mul_left coef (bankBudget_bound replies time B hsize htime)
  rw [←Nat.mul_assoc] at hb
  exact runs_mono hh hb hb

end PaidBoundBank
end Qatlib.Concepts.EffectiveGauge.RawMachine
