/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchInstance
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout


namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Matrix
open scoped BigOperators Classical

def tiPolynomialState (n t : ℕ) (p : Fin n → ℂ) : QState (Fin (2*n)) := fun i =>
  (Real.sqrt 2 : ℂ)⁻¹ *
    if h : i.val < n then p ⟨i.val,h⟩
    else (-1 : ℂ)^t * p ⟨i.val-n,by have := i.isLt; omega⟩

def tiMomentumRoot (n : ℕ) (l : Fin (2*n)) : ℂ :=
  primRoot (2*n) ^ (-(l.val : ℤ))

def tiTransitionPhase (n t : ℕ) (a b : Fin n → ℂ) (l : Fin (2*n)) : ℂ :=
  if l.val % 2 = t % 2 then
    if tiPolyEval a (tiMomentumRoot n l) = 0 then 1
    else -tiPolyEval b (tiMomentumRoot n l) / tiPolyEval a (tiMomentumRoot n l)
  else 1

def tiPolynomialTransition (n t : ℕ) (a b : Fin n → ℂ) :
    Matrix (Fin (2*n)) (Fin (2*n)) ℂ :=
  QFTMatrix (2*n) * Matrix.diagonal (tiTransitionPhase n t a b) * (QFTMatrix (2*n))ᴴ

def tiTranslation (n : ℕ) [NeZero n] : Matrix (Fin (2*n)) (Fin (2*n)) ℂ :=
  permMatrix (finShiftEquiv (2*n))

def tiPolynomialQueryWord (n k : ℕ) (p : ℕ → Fin n → ℂ) : Circuit (Fin (2*n)) :=
  (List.range k).flatMap fun r =>
    [Qatlib.Foundations.QueryWordCore.Circuit.Step.query,Qatlib.Foundations.QueryWordCore.Circuit.Step.gate (tiPolynomialTransition n (r+1) (p r) (p (r+1)))]

def tiPolynomialPreparedWord (n k : ℕ) (p : ℕ → Fin n → ℂ) : Circuit (Fin (2*n)) :=
  Qatlib.Foundations.QueryWordCore.Circuit.Step.gate (QFTMatrix (2*n)) :: tiPolynomialQueryWord n k p

def tiPolynomialReadoutVector (n k : ℕ) (y : Fin n) : QState (Fin (2*n)) :=
  tiPolynomialState n k (Ket y)

def tiFoldedEvent (n : ℕ) (y : Fin n) : Finset (Fin (2*n)) :=
  Finset.univ.filter fun i => i.val % n = y.val

def tiInvariantQueryWord (n k : ℕ)
    (U : ℕ → Matrix (Fin (2*n)) (Fin (2*n)) ℂ) : Circuit (Fin (2*n)) :=
  (List.range k).flatMap fun r => [Qatlib.Foundations.QueryWordCore.Circuit.Step.query,Qatlib.Foundations.QueryWordCore.Circuit.Step.gate (U (r+1))]

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
