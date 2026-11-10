/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib
open Qatlib

open Matrix

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

noncomputable def Fig3Circuit {J I : Type} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (U : J → Matrix I I ℂ) (A B : Matrix J J ℂ) :
    Matrix (J × I) (J × I) ℂ :=
  TensorGate B 1 * (Select U * TensorGate A 1)

noncomputable def Fig3SuccessProb {J I : Type} [Fintype J] [DecidableEq J] [Fintype I]
    [DecidableEq I] (U : J → Matrix I I ℂ) (A B : Matrix J J ℂ) (j₀ : J) (ψ : QState I) :
    ℝ :=
  MeasureProb (ApplyGate (Fig3Circuit U A B) (TensorState (Ket j₀) ψ))
    ({j₀} ×ˢ Finset.univ)
end Qatlib.Concepts.CoherentSim.ResetDiscard
