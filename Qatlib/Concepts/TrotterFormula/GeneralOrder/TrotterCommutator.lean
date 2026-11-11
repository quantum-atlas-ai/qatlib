/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Common imports for Trotter commutator estimates

This module provides a common import surface for the Trotter commutator definitions and
Euclidean operator-norm tools. Its imported API includes grouped integral remainders, segmented
product words, multiplicative defects, and Gibbs normalization data used in the product-formula
setting of [ChildsEtAl2021Trotter].

## Main statements

* `groupedIntegralRemainder`: imported grouped commutator-integral expression.
* `segmentWord`: imported list of repeated exponential factors.
* `segmentMultiplicativeDefect`: imported relative defect of a segmented product.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

set_option autoImplicit false
set_option maxHeartbeats 400000

open Matrix Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator

section Gibbs

open scoped ComplexOrder

end Gibbs

section Lchs

open scoped ComplexOrder

end Lchs

section GroupedIntegral

open Set

variable {I : Type} [Fintype I] [DecidableEq I]

end GroupedIntegral

section GroupedIntegralBaked

variable {I : Type} [Fintype I]

end GroupedIntegralBaked

section Tariff

variable {I : Type} [Fintype I]

end Tariff

section FiniteRange

end FiniteRange

section OverlapChains

variable {S ι : Type} [Fintype S] [Fintype ι]

end OverlapChains

section MultiplicativeDefect

variable {I : Type} [Fintype I]

end MultiplicativeDefect

section LocalObservableBudget

end LocalObservableBudget

section LongRangeTail

end LongRangeTail

end Qatlib.Concepts.TrotterFormula.GeneralOrder
