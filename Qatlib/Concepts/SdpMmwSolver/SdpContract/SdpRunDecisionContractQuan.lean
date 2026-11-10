/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpRunDecisionContractStat
import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpDualSampleOutputQuan
import Qatlib.Concepts.SdpMmwSolver.BranchProofs.SdpLargerTriggerRunQuan
import Qatlib.Concepts.SdpMmwSolver.BranchProofs.SdpDualCertificateMacroQuan
import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpWeakDuality
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.BranchProofs

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

theorem sdpRunDecisionContract : SdpRunDecisionContract := by
  intro D m A Cv b y j₀ α R δ ε η hD hα hα1 hR hδ hδ1 hε hη hsmall hεcap hA hCv hb hA0 hb0
  constructor
  · rintro ⟨t₀,_ht,hprior,hfail⟩
    exact sdpLargerTriggerRun D m A Cv b y j₀ α R δ ε η t₀
      hD hα hR hδ hδ1 hε hεcap (fun i => (hA i).1) hCv.1 hb hA0 hb0 hprior hfail
  · intro hround
    have hcert := sdpDualCertificateMacro D m A Cv b y j₀ α R δ ε η
      hD hα hα1 hR hδ hε hη hsmall hA hCv hb hA0 hb0 hround
    have hsample := sdpDualSampleOutput D m y j₀ α R δ η hα hR hδ
      (fun t i => (hround t).1 i)
    refine ⟨hsample.1,hsample.2.1,hsample.2.2.1,hsample.2.2.2.1,hcert.2.1,hcert.2.2,?_⟩
    intro X hX hconstraints
    exact (sdp_weak_duality_trace_bound D m A Cv b
      (sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η)) X
      hcert.1 hcert.2.2 hX hconstraints).trans hcert.2.1

end Qatlib.Concepts.SdpMmwSolver.SdpContract
