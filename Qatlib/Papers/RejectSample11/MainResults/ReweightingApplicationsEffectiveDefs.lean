/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.CoherentReweightingCore
import Qatlib.Concepts.Waterfill.LevelFidelity.CoherentReweighting
import Qatlib.Concepts.NativeNumerics.WaterFilling
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedQueryCircuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib.Concepts.Waterfill.LevelFidelity
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Papers.RejectSample11.MainResults

set_option autoImplicit false

open Matrix
open Qatlib
open scoped BigOperators ComplexOrder ENNReal

variable {m : ℕ}

def bhspPiQ {n : ℕ} (fHat : Fin (2 ^ n) → ℚ) : Fin (2 ^ n) → ℚ := fun w => |fHat w|

def flatSigmaQ (m : ℕ) (c : ℚ) : Fin m → ℚ := fun _ => c

def bhspClipQ {n : ℕ} (fHat : Fin (2 ^ n) → ℚ) (c : ℚ) (γ : ℝ) : Fin (2 ^ n) → ℝ :=
  fun w => min |(fHat w : ℝ)| (γ * (c : ℝ))

theorem bhspClipQ_identification {n : ℕ} (fHat : Fin (2 ^ n) → ℚ) (c : ℚ) (γ : ℝ)
    (w : Fin (2 ^ n)) :
    bhspClipQ fHat c γ w = levelFill (bhspPiQ fHat) (flatSigmaQ _ c) γ w := by
  unfold bhspClipQ bhspPiQ flatSigmaQ levelFill
  rw [Rat.cast_abs]

theorem bhspClipQ_eq_bhspEps {n : ℕ} (h2 : n = 2) (fHat : Fin (2 ^ n) → ℚ) (γ : ℝ)
    (w : Fin (2 ^ n)) :
    bhspClipQ fHat (1 / 2 : ℚ) γ w = bhspEps (fun x => (fHat x : ℝ)) γ w := by
  subst h2
  have hbeta : (fun x : Fin (2 ^ 2) => (fHat x : ℝ)) w = (fHat w : ℝ) := rfl
  have hdiv : ((1 / 2 : ℚ) : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  have hsqrt : Real.sqrt ((2 : ℝ) ^ 2) = 2 := Real.sqrt_sq (by norm_num)
  have hscale : γ * ((1 / 2 : ℚ) : ℝ) = γ / Real.sqrt ((2 : ℝ) ^ 2) := by
    rw [hdiv, hsqrt]
    ring
  unfold bhspClipQ bhspEps
  rw [hbeta, hscale]

end Qatlib.Papers.RejectSample11.MainResults
