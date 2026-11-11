/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm

open Qatlib.Concepts.SchattenDiamond.DiamondNorm

set_option backward.isDefEq.respectTransparency false

/-!
# `SourceAbstract` — Abstract: two simpler SDP formulations (claim c007)

Watrous, *Simpler semidefinite programs for completely bounded norms*,
fixed arXiv:1207.5726v2 (2012), abstract, p.1.

The abstract announces two new, simpler semidefinite-programming formulations of
the completely bounded trace and spectral norms (the spectral version follows by
Eq. (1)). Both formulations are made explicit in the body:

* the maximum-output-fidelity formulation of §2 (Theorem 5), and
* the Choi–Jamiołkowski formulation of §3 (Theorem 6),

and each computes `|||Φ|||₁`. This file records the abstract's content as the
conjunction that both formulated values equal the completely bounded trace norm.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ENNReal

namespace Qatlib.Papers.BddNormSDP12.MainResults.SourceAbstract

open Qatlib.Concepts.SdpDuality.StrongDuality
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.RandCompile.ChannelBudget

/-- Fixed arXiv:1207.5726v2 abstract, p.1. The paper's two formulations both
compute the completely bounded trace norm of `Φ`:

* the maximum-output-fidelity value
  `maxOutputRootFidelity (canonicalStinespringLeft Φ) (canonicalStinespringRight D E)`
  of §2 (Theorem 5), and
* the two-density Choi value `diamondChoiValue Φ` of §3 (Theorem 6).

Reuses `finiteDiamondNorm_canonical_maxOutputFidelity` and
`finiteDiamondNorm_eq_choi`; the completely bounded spectral norm follows from
Eq. (1) (claim c001). -/
theorem two_simpler_sdp_formulations {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondNorm T =
        maxOutputRootFidelity (canonicalStinespringLeft T) (canonicalStinespringRight D E) ∧
      finiteDiamondNorm T = diamondChoiValue T :=
  ⟨finiteDiamondNorm_canonical_maxOutputFidelity T, finiteDiamondNorm_eq_choi T⟩

end Qatlib.Papers.BddNormSDP12.MainResults.SourceAbstract
