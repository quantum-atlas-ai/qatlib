/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.ClockBridge.ExecutionRemainderDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdaptiveCP.BranchTrace

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem clause16_finite_bit_charge {S O X : Type} [Fintype S] [Fintype X] {D E : ℕ}
    (P : JointProgram S O X D E) : jointFiniteBitCharge P = maxCharge P :=
  rfl

theorem clause16_zero_price_branch {S O X : Type} [Fintype X] {D E : ℕ}
    (P : JointProgram S O X D E) (s : S) (h : P.cost s = 0) :
    zeroPriceBranch P s ∧ P.cost s = 0 :=
  ⟨h, h⟩

theorem clause16_fair_bit_charge {D E : ℕ} (k m : ℕ) {X : Type} [Fintype X]
    (I : Instrument X D E) : (fairBitProgram k m I).cost () = k :=
  rfl

theorem clause16_endpoint :
    (∀ {S O X : Type} [Fintype S] [Fintype X] {D E : ℕ} (P : JointProgram S O X D E),
      jointFiniteBitCharge P = maxCharge P) ∧
    (∀ {S O X : Type} [Fintype X] {D E : ℕ} (P : JointProgram S O X D E) (s : S)
      (h : P.cost s = 0), zeroPriceBranch P s ∧ P.cost s = 0) ∧
    (∀ {D E : ℕ} (k m : ℕ) {X : Type} [Fintype X] (I : Instrument X D E),
      (fairBitProgram k m I).cost () = k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S O X instS instX D E P
    exact clause16_finite_bit_charge P
  · intro S O X inst D E P s h
    exact clause16_zero_price_branch P s h
  · intro D E k m X inst I
    exact clause16_fair_bit_charge k m I

end Qatlib.Concepts.MixedInstrument.ClockBridge
