/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialCircuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped BigOperators Classical

def TiPolynomialTransitionKernel : Prop :=
  (∀ (n t : ℕ) [NeZero n] (p : Fin n → ℂ) (l : Fin (2*n)),
    ApplyGate (QFTMatrix (2*n))ᴴ (tiPolynomialState n t p) l =
      if l.val % 2 = t % 2 then
        (Real.sqrt (n : ℝ) : ℂ)⁻¹ * tiPolyEval p (tiMomentumRoot n l)
      else 0) ∧
  ∀ (n t : ℕ) [NeZero n] (_ : 0 < t) (a b : Fin n → ℂ),
    (∀ z : ℂ, z^n = (-1 : ℂ)^t → ‖tiPolyEval a z‖ = ‖tiPolyEval b z‖) →
    (∀ l : Fin (2*n), ‖tiTransitionPhase n t a b l‖ = 1) ∧
    tiPolynomialTransition n t a b ∈ Matrix.unitaryGroup (Fin (2*n)) ℂ ∧
    tiTranslation n * tiPolynomialTransition n t a b =
      tiPolynomialTransition n t a b * tiTranslation n ∧
    ApplyGate (tiPolynomialTransition n t a b)
      (ApplyGate (PhaseOracle (ospBit n 0)) (tiPolynomialState n (t-1) a)) =
        tiPolynomialState n t b

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
