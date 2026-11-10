/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline
open Qatlib

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LaurentPolys.FiniteBitCost
open Polynomial Matrix

noncomputable def rhwQSPBridgeMatrix (a b c d : ℂ) : Matrix Bool Bool ℂ :=
  fun i j => if i then (if j then d else c) else (if j then b else a)

noncomputable def rhwQSPBridgeDiagonal (w : ℂ) : Matrix Bool Bool ℂ := rhwQSPBridgeMatrix w 0 0 w⁻¹

noncomputable def rhwQSPBridgeFactor (γ : ℂ) : Matrix Bool Bool ℂ :=
  let c : ℂ := (((Real.sqrt (1+Complex.normSq γ))⁻¹:ℝ):ℂ)
  rhwQSPBridgeMatrix c (c*γ) (-c*star γ) c

noncomputable def rhwQSPBridgePair (gs : List ℂ) (z : ℂ) : Matrix Bool Bool ℂ :=
  let p := nlftSU2 gs
  rhwQSPBridgeMatrix (star (p.1.eval z)) (p.2.eval z) (-star (p.2.eval z)) (p.1.eval z)

noncomputable def rhwQSPBridgeWord (w : ℂ) : List ℂ → Matrix Bool Bool ℂ
  | [] => rhwQSPBridgeDiagonal w⁻¹
  | g::gs => rhwQSPBridgeFactor g*rhwQSPBridgeDiagonal w*rhwQSPBridgeWord w gs

noncomputable def rhwQSPBridgePhase (φ : ℝ) : Matrix Bool Bool ℂ :=
  rhwQSPBridgeMatrix (Complex.exp ((φ:ℂ)*Complex.I)) 0 0 (Complex.exp (-(φ:ℂ)*Complex.I))

noncomputable def rhwQSPBridgeSignal (x : ℝ) : Matrix Bool Bool ℂ :=
  rhwQSPBridgeMatrix (x:ℂ) (Complex.I*(Real.sqrt (1-x^2):ℂ)) (Complex.I*(Real.sqrt (1-x^2):ℂ)) (x:ℂ)

noncomputable def rhwQSPBridgeCoefficient (φ : ℝ) : ℂ := Complex.I*(Real.tan φ:ℂ)

noncomputable def rhwQSPBridgeGammas (ψ : ℕ → ℝ) : ℕ → List ℂ
  | 0 => [rhwQSPBridgeCoefficient (ψ 0)]
  | d+1 => rhwQSPBridgeCoefficient (ψ (d+1)) :: (rhwQSPBridgeGammas ψ d ++ [rhwQSPBridgeCoefficient (ψ (d+1))])

noncomputable def rhwQSPBridgeOperator (ψ : ℕ → ℝ) (x : ℝ) : ℕ → Matrix Bool Bool ℂ
  | 0 => rhwQSPBridgePhase (ψ 0)
  | d+1 => rhwQSPBridgePhase (ψ (d+1))*rhwQSPBridgeSignal x*rhwQSPBridgeOperator ψ x d*rhwQSPBridgeSignal x*rhwQSPBridgePhase (ψ (d+1))

noncomputable def rhwQSPBridgeCentered (d : ℕ) (gs : List ℂ) (z : ℂ) : Matrix Bool Bool ℂ :=
  let p := nlftSU2 gs
  let b := (z^d)⁻¹*p.2.eval z
  rhwQSPBridgeMatrix (star (p.1.eval z)) b (-star b) (p.1.eval z)

end Qatlib.Concepts.LaurentPolys.FiniteBitCost
