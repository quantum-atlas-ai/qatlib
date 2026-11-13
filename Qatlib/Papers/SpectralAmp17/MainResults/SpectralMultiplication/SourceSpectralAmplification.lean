/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PaperModel
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Matrix.Spectrum

set_option backward.isDefEq.respectTransparency false

/-!
# SourceSpectralAmplification — resource specifications

**Statement only — not proved in Qatlib.**

The paper's quantum algorithm is not constructed in this module. Declarations
ending in `_statement` specify abstract output accuracy and resource targets;
they are propositions, with no existence proof or counted implementation.
The legacy record fields alone do not certify execution costs.
-/

set_option autoImplicit false

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

namespace Qatlib.Papers.SpectralAmp17.MainResults.SpectralMultiplication

/-- **Statement only — not proved in Qatlib.**
Resource and accuracy specification for `theorem2_spectralMultiplication`.
No circuit, oracle implementation, or execution-cost theorem is supplied here.
The existential record is a specification, not evidence of an algorithm. -/
def theorem2_spectralMultiplication_statement
    {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (F : StandardForm S A) (Λ ε : ℝ)
    (hΛ_ge : ‖F.H‖ ≤ Λ) (hΛ_le : Λ ≤ F.α) (hΛ_pos : 0 < Λ)
    (hε_pos : 0 < ε) (hε_small : ε ≤ Λ / F.α) : Prop :=
    ∃ (F' : StandardForm S (A × Fin 4)),
      F'.Uᴴ * F'.U = 1 ∧ 0 ≤ F'.queries ∧ 0 ≤ F'.gates ∧
      F'.α = 2 * Λ ∧
      (1 / (2 * Λ)) * ‖F'.H - F.H‖ ≤ ε ∧
      bigOConst F'.queries (F.α / Λ * Real.log (1 / ε))

/-- **Statement only — not proved in Qatlib.**
Resource and accuracy specification for `theorem3_lowEnergySubspace`.
No circuit, oracle implementation, or execution-cost theorem is supplied here.
The existential record is a specification, not evidence of an algorithm. -/
def theorem3_lowEnergySubspace_statement
    {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (F : StandardForm S A) (Δ ε : ℝ) (P : Matrix S S ℂ)
    (hΔ_pos : 0 < Δ) (hΔ_one : Δ < 1) (hε_pos : 0 < ε)
    (hP : IsLowEnergyProjector F.H F.α Δ P) : Prop :=
    ∃ (F' : StandardForm S (A × Fin 4)),
      F'.Uᴴ * F'.U = 1 ∧ 0 ≤ F'.queries ∧ 0 ≤ F'.gates ∧
      F'.α = Δ * F.α ∧
      ‖P * (((Δ * F.α : ℝ) : ℂ)⁻¹ • F'.H -
              ((Δ * F.α : ℝ) : ℂ)⁻¹ • (F.H + (F.α * (1 - Δ)) • (1 : Matrix S S ℂ))) * P‖ ≤ ε ∧
      bigOConst F'.queries
        (Δ⁻¹ ^ (1 / 2 : ℝ) * Real.log (1 / (Δ * ε)) ^ (3 / 2 : ℝ))

/-- **Statement only — not proved in Qatlib.**
Resource and accuracy specification for `corollary2_lowEnergySimulation`.
No circuit, oracle implementation, or execution-cost theorem is supplied here.
The existential record is a specification, not evidence of an algorithm. -/
def corollary2_lowEnergySimulation_statement
    {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (F : StandardForm S A) (Δ t ε : ℝ) (P : Matrix S S ℂ)
    (hΔ_pos : 0 < Δ) (hΔ_one : Δ < 1) (ht : 0 ≤ t) (hε_pos : 0 < ε)
    (hP : IsLowEnergyProjector F.H F.α Δ P) : Prop :=
    ∃ (X : Matrix S S ℂ) (Q : ℝ),
      0 ≤ Q ∧
      ‖P * (X - timeEvolution F.H t) * P‖ ≤ ε ∧
      bigOConst Q
        (t * F.α * Real.sqrt Δ * Real.log (t * F.α / ε) ^ (3 / 2 : ℝ) +
          Δ⁻¹ ^ (1 / 2 : ℝ) * Real.log (t * F.α / ε) ^ (5 / 2 : ℝ))

end Qatlib.Papers.SpectralAmp17.MainResults.SpectralMultiplication
