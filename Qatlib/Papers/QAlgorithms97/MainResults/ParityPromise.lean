/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

/-!
# Deutsch-Jozsa for output parity promises

A register-valued function induces the Boolean function `parityFun` by taking output parity.
Applying Deutsch-Jozsa to that Boolean function gives deterministic discrimination between the
parity-constant and parity-balanced promises, with the query count of `djCircuit`, as discussed
in [CleveEtAl1998].

## Main statements

* `parityPromise_one_run`: the output probabilities for the induced parity oracle.
* `parityPromise_cases`: an explicit characterization of parity constancy.

## References

* [Cleve et al., 1998][CleveEtAl1998]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.QAlgorithms97.MainResults.ParityPromise

open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

/-- The parity of a Boolean output register, true exactly when its number of true bits is odd. -/
def bitParity {m : ℕ} (y : Reg m) : Bool :=
  decide ((Finset.univ.filter fun i => y i).card % 2 = 1)

/-- The Boolean function obtained by taking the parity of each output of `f`. -/
def parityFun {n m : ℕ} (f : Reg n → Reg m) : Reg n → Bool :=
  fun x => bitParity (f x)

/-- The promise that the output parity of `f` is constant over all inputs. -/
def ParityConstant {n m : ℕ} (f : Reg n → Reg m) : Prop :=
  DJConstant (parityFun f)

/-- The promise that the induced Boolean output-parity function is balanced. -/
def ParityBalanced {n m : ℕ} (f : Reg n → Reg m) : Prop :=
  DJBalanced (parityFun f)

/-- The Deutsch-Jozsa state for the induced parity function distinguishes parity-constant from
parity-balanced inputs with certainty, and `djCircuit` has one query [Cleve et al., Section
3][CleveEtAl1998]. -/
theorem parityPromise_one_run {n m : ℕ} (f : Reg n → Reg m) :
    (ParityConstant f →
        MeasureProb (djFinalState (parityFun f)) ({ZeroStr n} : Finset (Reg n)) = 1) ∧
    (ParityBalanced f →
        MeasureProb (djFinalState (parityFun f)) ({ZeroStr n} : Finset (Reg n)) = 0 ∧
        MeasureProb (djFinalState (parityFun f))
          (Finset.univ.erase (ZeroStr n)) = 1) ∧
    QueryCount (djCircuit n) = 1 :=
  deutschJozsa_single_query (parityFun f)

/-- The parity-constant promise is equivalent to the existence of a single Boolean parity value
shared by every output [CleveEtAl1998]. -/
theorem parityPromise_cases {n m : ℕ} (f : Reg n → Reg m) :
    ParityConstant f ↔
      ∃ b : Bool, ∀ x, bitParity (f x) = b :=
  Iff.rfl

end Qatlib.Papers.QAlgorithms97.MainResults.ParityPromise
