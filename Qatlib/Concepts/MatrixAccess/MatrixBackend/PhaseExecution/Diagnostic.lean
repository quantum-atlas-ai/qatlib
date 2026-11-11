/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Fallback
import Qatlib.Concepts.LocalMachine.LocalTransport.MatrixRepresentationBridgesDefs

set_option backward.isDefEq.respectTransparency false

/-! Original the finite producer construction fixed-degree sign-family counter diagnostic.
It compares the actual producer to the separately declared numeric formula;
no grid is executed and no hardware/bit-time or other-backend lower bound is claimed. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend

/-- A whole actual named family at fixed degree three: the table grows
exponentially in tolerance bits, while the separately assigned formula is linear.
This is the producer's arithmetic counter, not a hardware/bit-time lower bound. -/
theorem fixed_sign_fallback_cost (eps : ℚ) (heps : 0<eps) (hsmall : eps<1) :
    let e := signPhaseInput 1 eps
    let actual := finitePhaseSynthesis e.coeffs e.deg e.tol
    actual.backendCalls=1 ∧
      actual.tableMultiplications=2^(phaseToleranceBits eps+12)-1 ∧
      (e.deg+1)*(phaseToleranceBits e.tol+1)<actual.tableMultiplications := by
  have hs : (scoreData (rationalSignCoefficients 1) (3^1)
      ⟨gone,List.replicate (3^1) gone⟩).1.1=1 := by decide +kernel
  have hr : ¬ (scoreData (rationalSignCoefficients 1) (3^1)
      ⟨gone,List.replicate (3^1) gone⟩).1.1 ≤ (1/2 : ℚ)^phaseToleranceBits eps := by
    rw [hs]
    exact not_le_of_gt ((phaseTolerance_le eps heps).trans_lt hsmall)
  have hc := finite_phase_rejected_table_cost (rationalSignCoefficients 1) (3^1) eps hr
  have hconst : Nat.clog 2 (32*phaseConstant (3^1))=12 := by decide +kernel
  have hg : phaseGridBits (3^1) (phaseToleranceBits eps)=phaseToleranceBits eps+12 := by
    rw [phaseGridBits,hconst]
  rw [hg] at hc
  refine ⟨hc.1,hc.2,?_⟩
  change 4*(phaseToleranceBits eps+1)<
    (finitePhaseSynthesis (rationalSignCoefficients 1) (3^1) eps).tableMultiplications
  rw [hc.2,pow_add]
  norm_num only [show (2^12 : ℕ)=4096 by decide]
  have hk : phaseToleranceBits eps+1≤2^phaseToleranceBits eps :=
    Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hp : 0<2^phaseToleranceBits eps := by positivity
  omega


end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
