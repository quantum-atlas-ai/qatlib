/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.CopyExponent.LowRankExponentiationRestrictedStat
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityQuan

/-!
# Restricted Gram-matrix exponentiation bound

`lowRankExponentiationRestricted` proves the fresh-copy exponentiation specification for Gram
density matrices formed from normalized states and nonnegative normalized weights. It supplies
dyadic trace-norm precision and the specified resource tuple.

This formalizes a restricted Gram-matrix setting related to the density-matrix exponentiation
application in [LloydMohseniRebentrost2014].

## Main statements

* `lowRankExponentiationRestricted`: proves the restricted exponentiation specification.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CopyEvolution.SelfTomography

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.CopyExponent
open Matrix
open scoped ComplexOrder

/-- Proves dyadic fresh-copy exponentiation precision and exact resource counts for the
restricted Gram density-matrix family related to [LloydMohseniRebentrost2014]. -/
theorem lowRankExponentiationRestricted : LowRankExponentiationRestricted := by
  intro r d T k ψ hψ w hw hsumw t ht s Y hY
  have hd := (gramFirstRegisterDensity r d ψ hψ w hw hsumw).2.2
  exact copy_precision_same_protocol_and_four_resource_counts r s T k (gramMatrix ψ w) t Y hd hY ht

end Qatlib.Concepts.CopyEvolution.CopyExponent
