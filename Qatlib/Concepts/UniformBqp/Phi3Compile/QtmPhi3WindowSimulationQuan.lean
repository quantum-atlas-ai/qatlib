/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3WindowSimulationStat
import Qatlib.Concepts.QtmSimulation.Phi3Compilation.QtmCellPhi3CompilationQuan
import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3ReferenceTransport
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.UniformBqp.Phi3Compile
open Matrix
open scoped Classical

theorem qtmWindowBasisCode_injective {Q A : Type} (t b : ℕ)
    (e : CellState Q A → Reg b) (he : Function.Injective e) :
    Function.Injective (qtmWindowBasisCode t b e) := by
  intro r s h
  funext i
  apply he
  funext u
  have hh := congrFun h ((finProdFinEquiv (m := 2*t+1) (n := b)) (i,u))
  simpa only [qtmWindowBasisCode, Equiv.symm_apply_apply] using! hh

theorem qtmPhi3State_normalized {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (t b : ℕ) (e : CellState Q A → Reg b)
    (he : Function.Injective e) {ψ : QState (WReg t Q A)} (hψ : Normalized ψ) :
    Normalized (qtmPhi3State t b e ψ) :=
  qtmKnownWireEmbed_normalized (knownPrefixWires ((2*t+1)*b) 3)
    (finiteBasisPadState_normalized (qtmWindowBasisCode t b e)
      (qtmWindowBasisCode_injective t b e he) hψ)

theorem qtmPhi3State_apply_basis {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (t b : ℕ) (e : CellState Q A → Reg b)
    (he : Function.Injective e) (ψ : QState (WReg t Q A)) (r : WReg t Q A) :
    qtmPhi3State t b e ψ (qtmPhi3Basis t b e r) = ψ r := by
  unfold qtmPhi3State qtmPhi3Basis
  rw [qtmKnownWireEmbed_apply_image]
  exact finiteBasisPadState_apply_image (qtmWindowBasisCode t b e)
    (qtmWindowBasisCode_injective t b e he) ψ r

theorem qtmPhi3WindowSimulation : QtmPhi3WindowSimulation := by
  intro Q _ _ A _ _ M b n t hb hn ht hnt
  let e := finiteBasisCode (CellState Q A) b hb
  have he : Function.Injective e := finiteBasisCode_injective hb
  obtain ⟨G,hG,hfix,hstep⟩ := gUnitExistence Q A M
  obtain ⟨gs,hgs,hq,hc,hlen,hr⟩ := qtmCellPhi3Compilation Q A b t t e G he hG
  refine ⟨gs,hgs,hq,hc,hlen,?_⟩
  intro x c
  have hinit := qtmPhi3State_normalized t b e he
    (normalized_ket (windowEncode (initWindowCfg M n x)))
  have href := qtmPhi3_reference_run Q A M n t ht G hfix hstep x
  have hout : Run 1 (phi3Compile gs)
      (qtmPhi3State t b e (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M n x)))) =
      qtmPhi3State t b e (windowEmbed ((windowStep M)^t *ᵥ Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M n x))) :=
    (hr _).trans (congrArg (qtmPhi3State t b e) href)
  refine ⟨hinit,hgs.normalized_run (Submonoid.one_mem _) hinit,hout,?_⟩
  rw [hout]
  change ‖qtmPhi3State t b e (windowEmbed ((windowStep M)^t *ᵥ Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M n x)))
    (qtmPhi3Basis t b e (windowEncode c))‖^2 =
    ‖((windowStep M)^t *ᵥ Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M n x)) c‖^2
  rw [qtmPhi3State_apply_basis t b e he,qtmPhi3_windowEmbed_image]

end Qatlib.Concepts.UniformBqp.Phi3Compile
