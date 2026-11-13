/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.Phi3Universal.QtmUniform

/-!
# Acceptance of an all-cell QTM tour

The module compares the acceptance mass of a finite-window all-cell tour with the output
probability of `compositeCellCircuit V`. Under the stated tape layout and head-position
assumptions, the tour after `n * (k + 1) + 1` steps reproduces the last output wire's acceptance
probability. See [Yao1993].

## Main statements

* `composite_cell_tour_acceptance`: equates the tour acceptance mass with the composite circuit
  output probability.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmUniversality

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.Phi3Universal.QtmUniform

set_option maxHeartbeats 2000000 in

/-- For unitary cell gates and the stated initial tape layout, the all-cell QTM tour after `n *
(k + 1) + 1` steps has acceptance mass equal to the composite circuit's last-wire acceptance
probability. This is the composite-cell simulation statement associated with Theorem 3 of
[Yao1993]. -/
theorem composite_cell_tour_acceptance {n k w : ℕ} (hn : 0 < n)
    (V : Fin n → Fin k → Matrix Bool Bool ℂ)
    (hV : ∀ i j, V i j ∈ Matrix.unitaryGroup Bool ℂ)
    (base : WindowCfg w (AllCellState n k) Bool) (x : Reg n) (hw : n ≤ w)
    (hhead : base.head.val = w)
    (hx : ∀ c : Fin n, base.tape (allCellTourPos c.val c.isLt hw) = x c)
    (i : ℕ) (hi : i < n) (hlast : i + 1 = n) :
    (∑ c ∈ (Finset.univ : Finset (WindowCfg w (AllCellState n k) Bool)).filter
        (fun c => c.state = (.acc : AllCellState n k)),
      BornProb ((windowStep (t := w) (allCellLocalQTM hn V hV)) ^ (n * (k + 1) + 1) *ᵥ
        Ket (allCellStartCfg base)) c)
      = AcceptProbAt ⟨i, hi⟩
        (Run (1 : Matrix (Reg n) (Reg n) ℂ) (compositeCellCircuit V) (Ket x)) :=
  allCellTour_acceptProb hn V hV base x hw hhead hx i hi hlast

end Qatlib.Papers.QCircuitYao93.QtmUniversality
