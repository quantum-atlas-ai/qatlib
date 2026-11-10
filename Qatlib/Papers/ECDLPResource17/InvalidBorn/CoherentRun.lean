/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.ECDLPResource17.InvalidBorn.ActualFailure
import Qatlib.Concepts.TensorRegisters.CohGraph.Controlled
import Qatlib.Concepts.TensorRegisters.CohGraph.GraphOverlap
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.InvalidBorn

open Qatlib.Concepts.CurveGroups.AffineAdd
open Qatlib.Concepts.FiniteCounts.OffsetWord
open Qatlib.Concepts.TensorRegisters.CohGraph

theorem source_coherent_bit_run (p w : ℕ) [Fact p.Prime] (hp : p ≤ 2^w)
    {a b : ZMod p} (P : (shortCurve a b).Point) (m n : ℕ)
    (a0 : AddSubgroup.zmultiples P) :
    let E := primeFieldEncoding p w hp
    let gate := fun kl : (Fin (n+1) → Bool) × (Fin (n+1) → Bool) =>
      bitWordPermutation E (cyclicWord P m (List.ofFn kl.1) (List.ofFn kl.2))
    let initial := fun _ : (Fin (n+1) → Bool) × (Fin (n+1) → Bool) =>
      pointBits E (a0 : (shortCurve a b).Point)
    controlledUnitary gate (graphState initial) =
      graphState (fun kl => bitRun E (initial kl)
        (cyclicWord P m (List.ofFn kl.1) (List.ofFn kl.2))) ∧
    ‖controlledUnitary gate (graphState initial)‖ = 1 := by
  (try dsimp only)
  constructor
  · simpa only [bitWordPermutation_apply] using controlledUnitary_graph
      (fun kl : (Fin (n+1) → Bool) × (Fin (n+1) → Bool) =>
        bitWordPermutation (primeFieldEncoding p w hp)
          (cyclicWord P m (List.ofFn kl.1) (List.ofFn kl.2)))
      (fun _ => pointBits (primeFieldEncoding p w hp) (a0 : (shortCurve a b).Point))
  · rw [LinearIsometryEquiv.norm_map]
    exact graphState_norm _

theorem source_coherent_defect (p w : ℕ) [Fact p.Prime] (hp : p ≤ 2^w)
    {a b : ZMod p} (P : (shortCurve a b).Point) (m n : ℕ)
    (a0 : AddSubgroup.zmultiples P) :
    let E := primeFieldEncoding p w hp
    let actual := fun kl : (Fin (n+1) → Bool) × (Fin (n+1) → Bool) =>
      bitRun E (pointBits E (a0 : (shortCurve a b).Point))
        (cyclicWord P m (List.ofFn kl.1) (List.ofFn kl.2))
    let target := fun kl : (Fin (n+1) → Bool) × (Fin (n+1) → Bool) =>
      pointBits E ((a0 + binaryValue (List.ofFn kl.1) • cyclicGenerator P +
        binaryValue (List.ofFn kl.2) • (m • cyclicGenerator P) : AddSubgroup.zmultiples P) :
          (shortCurve a b).Point)
    1 - (inner ℂ (graphState actual) (graphState target)).re =
      ((PMF.uniformOfFintype' ((Fin (n+1) → Bool) × (Fin (n+1) → Bool))).toOuterMeasure
        {kl | bitError E P m (List.ofFn kl.1) (List.ofFn kl.2) a0}).toReal :=
  graph_defect_uniform _ _

end Qatlib.Papers.ECDLPResource17.InvalidBorn
