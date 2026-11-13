/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

/-!
# One-query Deutsch discrimination

The one-bit specialization of the Deutsch-Jozsa circuit deterministically distinguishes constant
from balanced Boolean functions. The theorem `deutsch_constant_vs_balanced` combines the
corresponding output probabilities with an exact one-query count, following [CleveEtAl1998].

## Main statements

* `deutsch_constant_vs_balanced`: deterministic constant-versus-balanced discrimination in one
  query.

## References

* [Cleve et al., 1998][CleveEtAl1998]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.QAlgorithms97.MainResults.Deutsch

open Qatlib.Papers.QAlgorithms97.MainResults.DeutschJozsa

/-- For a one-bit Boolean function, the Deutsch circuit returns zero with probability one when
constant and a nonzero outcome with probability one when balanced, using one query [Cleve et
al., Section 2][CleveEtAl1998]. -/
theorem deutsch_constant_vs_balanced (f : Reg 1 → Bool) :
    (DJConstant f → MeasureProb (djFinalState f) ({ZeroStr 1} : Finset (Reg 1)) = 1) ∧
    (DJBalanced f →
      MeasureProb (djFinalState f) ({ZeroStr 1} : Finset (Reg 1)) = 0 ∧
      MeasureProb (djFinalState f) ((Finset.univ.erase (ZeroStr 1) : Finset (Reg 1))) = 1) ∧
    QueryCount (djCircuit 1) = 1 :=
  deutschJozsa_single_query f

end Qatlib.Papers.QAlgorithms97.MainResults.Deutsch
