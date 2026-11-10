/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.GramStatePreparationSubgoalStat
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CopyEvolution.GramReadout (gramColumn gramMatrix gramState)

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.SelfTomography

theorem gramStatePreparationSubgoal : GramStatePreparationSubgoal := by
  intro r d n e ψ hψ w hw hsumw
  have hgram := (gramFirstRegisterDensity r d ψ hψ w hw hsumw).1
  have htransport := normalized_relabelState e hgram
  exact known_complex_state_actual_local_preparation n (relabelState e (gramState ψ w)) htransport

end Qatlib.Concepts.CopyEvolution.SelfTomography
