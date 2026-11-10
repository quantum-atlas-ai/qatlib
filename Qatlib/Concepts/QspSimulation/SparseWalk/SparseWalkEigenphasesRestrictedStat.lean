/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

namespace Qatlib.Concepts.QspSimulation.SparseWalk

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open scoped Matrix.Norms.L2Operator

def SparseWalkEigenphasesRestricted : Prop :=
  ∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (H : Matrix I I ℂ) (c : ℝ), 0 < c → ‖(c : ℂ) • H‖ ≤ 1 →
    ∀ (L R : Matrix W I ℂ) (S : Matrix W W ℂ),
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry L → Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry R →
      L.conjTranspose * R = (c : ℂ) • H →
      S ∈ Matrix.unitaryGroup W ℂ → S.conjTranspose = S → S * S = 1 →
      S * L = R →
      ∀ (ψ : I → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) → ∀ (ev : ℝ), H *ᵥ ψ = (ev : ℂ) • ψ →
        ∃ (wp wm : W → ℂ) (ap am : ℝ),

          (∑ j, ‖wp j‖ ^ 2 = 1) ∧ (∑ j, ‖wm j‖ ^ 2 = 1) ∧
          (|c * ev| < 1 → (∑ j, (star (wp j)) * wm j = 0)) ∧

          (∃ V : Matrix W W ℂ, V ∈ Matrix.unitaryGroup W ℂ ∧
            V = Complex.I • S * (2 • (L * L.conjTranspose) - 1) ∧

            V *ᵥ wp = Complex.exp (Complex.I * ((Real.arcsin (c * ev) : ℂ))) • wp ∧
            V *ᵥ wm = -(Complex.exp (Complex.I * (-((Real.arcsin (c * ev) : ℂ))))) • wm) ∧

          (L *ᵥ ψ) = ((1/Real.sqrt 2 : ℝ) : ℂ) •
              (Complex.exp (Complex.I * (ap : ℂ)) • wp
                + Complex.exp (Complex.I * (am : ℂ)) • wm)

end Qatlib.Concepts.QspSimulation.SparseWalk
