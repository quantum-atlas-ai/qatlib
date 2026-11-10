/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.QAlgorithms97.MainResults.ParityPromise

open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

def bitParity {m : ℕ} (y : Reg m) : Bool :=
  decide ((Finset.univ.filter fun i => y i).card % 2 = 1)

def parityFun {n m : ℕ} (f : Reg n → Reg m) : Reg n → Bool :=
  fun x => bitParity (f x)

def ParityConstant {n m : ℕ} (f : Reg n → Reg m) : Prop :=
  DJConstant (parityFun f)

def ParityBalanced {n m : ℕ} (f : Reg n → Reg m) : Prop :=
  DJBalanced (parityFun f)

theorem parityPromise_one_run {n m : ℕ} (f : Reg n → Reg m) :
    (ParityConstant f →
        MeasureProb (djFinalState (parityFun f)) ({ZeroStr n} : Finset (Reg n)) = 1) ∧
    (ParityBalanced f →
        MeasureProb (djFinalState (parityFun f)) ({ZeroStr n} : Finset (Reg n)) = 0 ∧
        MeasureProb (djFinalState (parityFun f))
          (Finset.univ.erase (ZeroStr n)) = 1) ∧
    QueryCount (djCircuit n) = 1 :=
  deutschJozsa_single_query (parityFun f)

theorem parityPromise_cases {n m : ℕ} (f : Reg n → Reg m) :
    ParityConstant f ↔
      ∃ b : Bool, ∀ x, bitParity (f x) = b :=
  Iff.rfl

end Qatlib.Papers.QAlgorithms97.MainResults.ParityPromise
