/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.PolynomialStep.ActualEulerVariance
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction

/-!
# Discarding the environment contracts Euler error

The theorem `actualEuler_discard_contract` compares the reduced Euler error with the discrepancy
between the joint Euler outer product and the inflated ideal outer product. It specializes
trace-norm contraction under environment discard to the normalized-environment step analysis of
[LloydEtAl2020].

## Main statements

* `actualEuler_discard_contract`: For a normalized environment vector, the reduced Euler
  trace-norm discrepancy is at most the corresponding joint outer-product discrepancy.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

open Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Model

/-- For a normalized environment vector, the reduced Euler trace-norm discrepancy is at most the
corresponding joint outer-product discrepancy [LloydEtAl2020]. -/
theorem actualEuler_discard_contract {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (F : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (hq : (∑ a : E,Complex.normSq (q a))=1)
    (x : I→ℂ) (c : ℂ) :
    (actualEulerReduced F q x c-outer (idealEulerVector F q x c)).traceNorm≤
      (outer ((1-c •F)*ᵥ inflate q x)-outer (inflate q (idealEulerVector F q x c))).traceNorm := by
  have hH := (Matrix.posSemidef_vecMulVec_self_star ((1-c •F)*ᵥ inflate q x)).isHermitian.sub
    (Matrix.posSemidef_vecMulVec_self_star (inflate q (idealEulerVector F q x c))).isHermitian
  have h := Qatlib.Concepts.ReferenceError.DensityToRaw.traceRight_hermitian_trace_contraction
    (outer ((1-c •F)*ᵥ inflate q x)-outer (inflate q (idealEulerVector F q x c))) hH
  rw [Matrix.traceRight_sub,reducedOuter_product q hq] at h
  exact h

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
