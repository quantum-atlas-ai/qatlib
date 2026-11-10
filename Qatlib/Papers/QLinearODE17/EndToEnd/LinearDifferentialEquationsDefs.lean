/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.EndToEnd.LinearDifferentialConstruction
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearODE17.EndToEnd

open Qatlib.Papers.QLinearODE17.EndToEnd

structure SourceAccessLedger where

  controlledPreparations : ℕ

  oracleCalls : ℕ

  classicalBits : ℕ

  peakWorkspace : ℕ
  deriving DecidableEq, Repr

def sourceAccessLedger (m ρ : ℕ) (bits workspace : ℕ) : SourceAccessLedger where
  controlledPreparations := (m + 1) * ρ
  oracleCalls := m + 1
  classicalBits := bits
  peakWorkspace := workspace

def amplifiedQueryCount (r nq : ℕ) : ℕ := r * nq

def amplifiedGateCount (r g : ℕ) : ℕ := r * g

noncomputable def dyadicMagnitude (x : ℝ) (bits : ℕ) : ℝ :=
  (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits

noncomputable def finiteDigitErrorBudget (bits : ℕ) : ℝ := 1 / 2 ^ bits

end Qatlib.Papers.QLinearODE17.EndToEnd
