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

namespace Qatlib.Papers.QAlgorithms97.MainResults.Deutsch

open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

theorem deutsch_constant_vs_balanced (f : Reg 1 → Bool) :
    (DJConstant f → MeasureProb (djFinalState f) ({ZeroStr 1} : Finset (Reg 1)) = 1) ∧
    (DJBalanced f →
      MeasureProb (djFinalState f) ({ZeroStr 1} : Finset (Reg 1)) = 0 ∧
      MeasureProb (djFinalState f) ((Finset.univ.erase (ZeroStr 1) : Finset (Reg 1))) = 1) ∧
    QueryCount (djCircuit 1) = 1 :=
  deutschJozsa_single_query f

end Qatlib.Papers.QAlgorithms97.MainResults.Deutsch
