/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# Readout — feedback evaluation, RPA energy readout, thermal network

RiccatiWang26, arXiv:2609.37207v1.
Retained formalized declaration: the `thermalDynamics` definition used to state the
thermal-network readout.  Propositions 4.1, 4.2, Corollary 4.3, Lemmas G.1 and G.2 are
not formalized in this layer; no declaration below claims them.

The readout statements would be the paper's "returns a classical estimate with error at
most `ε` and failure probability at most `δ`" form.  Amplitude estimation is not
formalized here, so only the readout-layer definition is recorded.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.Applications

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## Proposition 4.1: finite-horizon feedback readout -/

/-! ## Proposition 4.2: RPA solution encoding and energy readout -/

/-! ## Corollary 4.3: the thermal network -/

/-! ## Lemma G.1: thermal-network inputs -/

/-- The path-Laplacian thermal dynamics `A_c = -ν I - κ L`, `b_c = e₁`, `P_T = 0` of (G.9). -/
def thermalDynamics (ν κ : ℝ) (L : Sq n) : Sq n := (-ν) • (1 : Sq n) - κ • L

/-! ## Lemma G.2: DRE parameters for the thermal network -/

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Applications
