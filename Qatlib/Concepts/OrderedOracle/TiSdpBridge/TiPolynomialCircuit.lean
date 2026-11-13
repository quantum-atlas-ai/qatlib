/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchInstance
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation

/-!
# Polynomial states and circuits for invariant ordered search

This module defines the concrete states, Fourier phases, translation matrix, circuit words, and
readout data used to realize polynomial witnesses for invariant ordered search. The construction
belongs to the setting of [FarhiEtAl1999] and the polynomial and semidefinite approach of
[ChildsLandahlParrilo2007]. The definitions `tiPolynomialState`, `tiPolynomialTransition`, and
`tiPolynomialQueryWord` specify vectors and matrices before any normalization or unitarity
conditions are imposed.

`tiPolynomialState` places a coefficient vector in two halves with relative sign `(-1)^t`, while
`tiPolynomialTransition` conjugates a diagonal phase matrix by the Fourier matrix.
`tiPolynomialPreparedWord` adds Fourier preparation, and `tiPolynomialReadoutVector` and
`tiFoldedEvent` provide two readout descriptions.

## Main statements

* `tiTransitionPhase` defines the active-parity ratio of polynomial evaluations, with value one
  at zero denominators and inactive modes.
- `tiPolynomialQueryWord` and `tiInvariantQueryWord` alternate queries with the specified gates.
- `tiTranslation` represents cyclic translation on `Fin (2*n)`.

## References

- [Farhi et al., 1999][FarhiEtAl1999], invariant algorithms for ordered insertion.
* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007], polynomial and semidefinite
  formulations of ordered search.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped BigOperators Classical

/-- Embeds the coefficient vector `p` into two halves of a vector on `Fin (2*n)`, scaled by `1 /
sqrt 2`, with relative sign `(-1)^t` on the second half. -/
def tiPolynomialState (n t : ℕ) (p : Fin n → ℂ) : QState (Fin (2*n)) := fun i =>
  (Real.sqrt 2 : ℂ)⁻¹ *
    if h : i.val < n then p ⟨i.val,h⟩
    else (-1 : ℂ)^t * p ⟨i.val-n,by have := i.isLt; omega⟩

/-- Defines the momentum root at mode `l` as the negative integer power `primRoot (2*n) ^
(-l.val)`. -/
def tiMomentumRoot (n : ℕ) (l : Fin (2*n)) : ℂ :=
  primRoot (2*n) ^ (-(l.val : ℤ))

/-- Defines the phase at active-parity modes by the negative ratio of the polynomial evaluations
of `b` and `a`. The value is one when the denominator vanishes or the mode has inactive
parity. -/
def tiTransitionPhase (n t : ℕ) (a b : Fin n → ℂ) (l : Fin (2*n)) : ℂ :=
  if l.val % 2 = t % 2 then
    if tiPolyEval a (tiMomentumRoot n l) = 0 then 1
    else -tiPolyEval b (tiMomentumRoot n l) / tiPolyEval a (tiMomentumRoot n l)
  else 1

/-- Defines the transition matrix by conjugating the diagonal matrix of `tiTransitionPhase`
values with `QFTMatrix (2*n)`. -/
def tiPolynomialTransition (n t : ℕ) (a b : Fin n → ℂ) :
    Matrix (Fin (2*n)) (Fin (2*n)) ℂ :=
  QFTMatrix (2*n) * Matrix.diagonal (tiTransitionPhase n t a b) * (QFTMatrix (2*n))ᴴ

/-- Defines cyclic translation on `Fin (2*n)` as the permutation matrix of `finShiftEquiv
(2*n)`. -/
def tiTranslation (n : ℕ) [NeZero n] : Matrix (Fin (2*n)) (Fin (2*n)) ℂ :=
  permMatrix (finShiftEquiv (2*n))

/-- Builds `k` consecutive rounds, each consisting of a query followed by the polynomial
transition from `p r` to `p (r+1)` at time `r+1`. -/
def tiPolynomialQueryWord (n k : ℕ) (p : ℕ → Fin n → ℂ) : Circuit (Fin (2*n)) :=
  (List.range k).flatMap fun r =>
    [Qatlib.Foundations.QueryWordCore.Circuit.Step.query,Qatlib.Foundations.QueryWordCore.Circuit.Step.gate (tiPolynomialTransition n (r+1) (p r) (p (r+1)))]

/-- Prepends the Fourier matrix gate to `tiPolynomialQueryWord n k p` to form the prepared
circuit word. -/
def tiPolynomialPreparedWord (n k : ℕ) (p : ℕ → Fin n → ℂ) : Circuit (Fin (2*n)) :=
  Qatlib.Foundations.QueryWordCore.Circuit.Step.gate (QFTMatrix (2*n)) :: tiPolynomialQueryWord n k p

/-- Defines the readout vector for output `y` by embedding `Ket y` as a polynomial state at time
`k`. -/
def tiPolynomialReadoutVector (n k : ℕ) (y : Fin n) : QState (Fin (2*n)) :=
  tiPolynomialState n k (Ket y)

/-- Defines the set of coordinates in `Fin (2*n)` whose values reduce to `y.val` modulo `n`. -/
def tiFoldedEvent (n : ℕ) (y : Fin n) : Finset (Fin (2*n)) :=
  Finset.univ.filter fun i => i.val % n = y.val

/-- Builds `k` rounds of a query followed by `U (r+1)`, for round indices `r` from zero through
`k-1`. -/
def tiInvariantQueryWord (n k : ℕ)
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ) : Circuit (Fin (2*n)) :=
  (List.range k).flatMap fun r => [Qatlib.Foundations.QueryWordCore.Circuit.Step.query,Qatlib.Foundations.QueryWordCore.Circuit.Step.gate (U (r+1))]

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
