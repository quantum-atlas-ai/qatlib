/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialCircuit

/-!
# Statement of the polynomial transition kernel

This module packages the Fourier-coordinate formula and the one-step transition guarantees into
the proposition `TiPolynomialTransitionKernel`. The invariant algorithm setting appears in
[FarhiEtAl1999], and the polynomial constraints underlying the transition appear in
[ChildsLandahlParrilo2007].

The first part specifies the parity-supported Fourier transform of `tiPolynomialState`. The
second part requires positive time and equality of the two polynomial norms at roots of `z^n =
(-1)^t`, and then states unit-modulus phases, unitarity, translation commutation, and the
desired oracle-followed-by-transition state identity.

## Main statements

* `TiPolynomialTransitionKernel` is the conjunction of the Fourier-coordinate identity and the
  conditional one-step transition properties.

## References

- [Farhi et al., 1999][FarhiEtAl1999], translation-invariant ordered-search algorithms.
* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007], polynomial descriptions of
  ordered-search feasibility.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped BigOperators Classical

/-- Packages the parity-supported Fourier formula for polynomial states and the conditional
guarantees for a positive-time transition. Equal polynomial norms on the relevant roots
imply unit-modulus phases, unitarity, translation commutation, and the
oracle-followed-by-transition state identity. -/
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
