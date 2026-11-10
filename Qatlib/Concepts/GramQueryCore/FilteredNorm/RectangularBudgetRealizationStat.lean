/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def RectangularBudgetRealization : Prop :=
  ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
    sourceRectValue A Z = filteredGamma2 (sourceRectLift A) (fun j => sourceRectLift (Z j)) ∧
    (∀ w : ℝ, 0 ≤ w →
      (sourceRectValue A Z ≤ ENNReal.ofReal w ↔ sourceRectCert n A Z w)) ∧
    (sourceRectValue A Z < ⊤ → ∃ (w : ℝ) (m : ℕ)
      (u : R → Fin n → QState (Fin m)) (v : S → Fin n → QState (Fin m)),
      0 ≤ w ∧ m ≤ n*(Fintype.card R+Fintype.card S) ∧
      sourceRectValue A Z = ENNReal.ofReal w ∧
      (∀ r s, A r s = ∑ j, Z j r s * ∑ k, star (u r j k)*v s j k) ∧
      (∀ r, ∑ j, ‖toEuclidean_fromVec (u r j)‖^2 ≤ w) ∧
      (∀ s, ∑ j, ‖toEuclidean_fromVec (v s j)‖^2 ≤ w))
end Qatlib.Concepts.GramQueryCore.FilteredNorm
