/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.GramStatePreparationSubgoalStat
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityQuan

/-!
# Finite reflection preparation of Gram states

This module proves `gramStatePreparationSubgoal` by transporting a normalized Gram state to a
bit register and applying finite known-state synthesis. The resulting legal reflection word
prepares the embedded target state exactly with length at most `128 * (n + 1) ^ 2 * 4 ^ n`.

The mathematical background is described in [NielsenChuang2010].

## Main statements

* `gramStatePreparationSubgoal`: exact preparation of a relabeled Gram state by a bounded legal
  reflection word.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.SelfTomography

/-- Proves exact preparation of an embedded, relabeled normalized Gram state by legal reflection
gates, with word length at most `128 * (n + 1) ^ 2 * 4 ^ n`. -/
theorem gramStatePreparationSubgoal : GramStatePreparationSubgoal := by
  intro r d n e ψ hψ w hw hsumw
  have hgram := (gramFirstRegisterDensity r d ψ hψ w hw hsumw).1
  have htransport := normalized_relabelState e hgram
  exact known_complex_state_actual_local_preparation n (relabelState e (gramState ψ w)) htransport

end Qatlib.Concepts.CopyEvolution.SelfTomography
