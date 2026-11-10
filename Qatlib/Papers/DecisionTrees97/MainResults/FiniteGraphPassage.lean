/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.FinitePassage
import Qatlib.Concepts.GraphLaplacian.LaplacianPsd.ComplexLaplacian
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LchsSimulation.StaticLchs.FinitePassage
open Qatlib.Concepts.GraphLaplacian.LaplacianPsd
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.DecisionTrees97.MainResults

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def sourceClassicalKernel (t : ℝ) : Matrix V V ℂ :=
  NormedSpace.exp ((-t : ℝ) • G.lapMatrix ℂ)

theorem source_generator_entries (i j : V) :
    G.lapMatrix ℂ i j =
      if i = j then (G.degree i : ℂ) else if G.Adj i j then -1 else 0 := by
  simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
    Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
  by_cases h : i = j
  · subst j
    simp
  · by_cases he : G.Adj i j <;> simp [h, he]

theorem source_heat_eq_cauchy_target (t : ℝ) :
    sourceClassicalKernel G t = staticNonunitaryEvolution (G.lapMatrix ℂ) 0 t := by
  simp [sourceClassicalKernel, staticNonunitaryEvolution]

theorem finite_unique_endpoint_transfer (T p : ℝ) (hT : 0 ≤ T)
    (hp : 0 < p) (hp1 : p ≤ 1) (target start : V)
    (hsignal : p ≤ (sourceClassicalKernel G T target start).re) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 33 * T / p ∧
      hamiltonianEvolution (G.lapMatrix ℂ) t ∈ Matrix.unitaryGroup V ℂ ∧
      Normalized (ApplyGate (hamiltonianEvolution (G.lapMatrix ℂ) t) (Ket start)) ∧
      p ^ 2 / 16 ≤ MeasureProb
        (ApplyGate (hamiltonianEvolution (G.lapMatrix ℂ) t) (Ket start)) {target} := by
  apply heat_entry_forces_born_success (G.lapMatrix ℂ) T p (complex_laplacian_posSemidef G)
    (G.isSymm_lapMatrix ℂ) hT hp hp1 target start
  rw [← source_heat_eq_cauchy_target]
  exact hsignal

end Qatlib.Papers.DecisionTrees97.MainResults
