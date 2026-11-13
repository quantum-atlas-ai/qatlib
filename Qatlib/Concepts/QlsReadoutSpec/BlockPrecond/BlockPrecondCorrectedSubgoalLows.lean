/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPrecondCorrectedSubgoalStat
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.PreconditionedEncoding
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.PreconditioningParameters

/-!
# Corrected block preconditioning guarantees

This module proves `blockPreconditioningCorrectedSubgoal` by assembling the one-flag encoding
construction, state-scaling identities, consistency-dependent pseudoinverse formula, and
preconditioned singular gap. The consistency hypothesis ensures the scaling commutes with the
range projector, which is needed for the pseudoinverse product identity.

Projected block encodings and pseudoinverse transformations are central to quantum singular
value transformation [GilyenSuLowWiebe2019].

## Main statements

* `blockPreconditioningCorrectedSubgoal`: Establishes the corrected encoding and spectral
  guarantees.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

/-- Establishes `BlockPreconditioningCorrectedSubgoal`, combining the preconditioned encoding,
scaling inverses, consistency-dependent pseudoinverse identities, and the norm and
singular-gap bounds with parameter `2 * c ^ 2 * κ`. -/
theorem blockPreconditioningCorrectedSubgoal : BlockPreconditioningCorrectedSubgoal := by
  constructor
  · intro H I O _ _ _ _ _ _ A U L R b s henc hb hs0 hs1
    have hinv:=stateScaling_inverse s b hs0.ne' hb
    exact ⟨preconditionedUnitary_blockEncoding L b s U henc.left_isometry hb hs0 hs1 henc.unitary,
      preconditioned_projectedEncoding A U L R b s henc hb hs0 hs1,
      stateScaling_intertwining L b s henc.left_isometry,hinv.1,hinv.2⟩
  constructor
  · intro I O _ _ _ _ A b s hs0 _hs1 hb hconsistent
    exact ⟨stateScaling_pseudoinverse_of_consistent A s b hs0.ne' hb hconsistent,
      stateScaling_pseudoinverse_direction_of_consistent A s b hs0.ne' hb hconsistent⟩
  · intro I O _ _ _ _ A b κ t c s hb hκ hc ht hs hgap hconsistent hτ
    have hn:=preconditioned_pseudoinverse_norm A b κ t c s hb hκ hc ht hs hgap hconsistent hτ.2
    exact ⟨hn,singular_gap_of_pseudoinverse_norm _ (2*c^2*κ) (by positivity) hn⟩
end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
