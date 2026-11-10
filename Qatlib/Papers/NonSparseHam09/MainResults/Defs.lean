/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def maxNorm [Nonempty ι] (H : Matrix ι ι ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : ι =>
    Finset.univ.sup' Finset.univ_nonempty fun j : ι => ‖H i j‖

def mcnNorm [Nonempty ι] (H : Matrix ι ι ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j : ι => Real.sqrt (∑ i : ι, ‖H i j‖ ^ 2)

def l1Norm [Nonempty ι] (H : Matrix ι ι ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j : ι => ∑ i : ι, ‖H i j‖

def absMatrix (H : Matrix ι ι ℂ) : Matrix ι ι ℝ := fun i j => ‖H i j‖

def specNorm {𝕜 : Type*} [RCLike 𝕜] (H : Matrix ι ι 𝕜) : ℝ := by
  letI := Matrix.instL2OpNormedAddCommGroup (m := ι) (n := ι) (𝕜 := 𝕜)
  exact ‖H‖

def timeEvolution (H : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H)

def matrixGraph (H : Matrix ι ι ℂ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (H i j ≠ 0 ∨ H j i ≠ 0)
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

def GraphArboricityLE {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ F : Fin k → SimpleGraph V,
    (∀ l, (F l).IsAcyclic) ∧ ∀ i j, G.Adj i j ↔ ∃ l, (F l).Adj i j

def circulantMatrix {M : ℕ} (s : Fin M → ℝ) : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ :=
  fun i j =>
    let d := (j.val + (2 * M + 1) - i.val) % (2 * M + 1)
    if h0 : d = 0 then 0
    else if h1 : d ≤ M then s ⟨d - 1, by omega⟩
    else
      have hd : d < 2 * M + 1 := Nat.mod_lt _ (by omega)
      s ⟨2 * M - d, by omega⟩

structure DiscreteTimeWalk (ι : Type*) [Fintype ι] [DecidableEq ι] where

  size : ℕ

  step : Matrix (Fin size) (Fin size) ℂ

  step_unitary : step ∈ Matrix.unitaryGroup (Fin size) ℂ

  vertexState : ι → Fin size

def WalkSimulates (H : Matrix ι ι ℂ) (t δ : ℝ) (n : ℕ) : Prop :=
  ∃ W : DiscreteTimeWalk ι,
    (∀ a b, W.step a b ≠ 0 → ∃ i j, W.vertexState i = a ∧ W.vertexState j = b ∧
      (i = j ∨ H i j ≠ 0 ∨ H j i ≠ 0)) ∧
    ∀ i j, ‖((W.step ^ n) (W.vertexState i) (W.vertexState j)) - timeEvolution H t i j‖ ≤ δ

abbrev RowOracle (ι : Type*) := ι → ι → ℂ

abbrev PhaseOracle (ι : Type*) := ι → ι → ℂ

def phaseEntry (H : Matrix ι ι ℂ) (i j : ι) : ℂ :=
  if H i j = 0 then 1 else H i j / (‖H i j‖ : ℂ)

inductive ProgramStep (Oracle W : Type*) where

  | unitary (M : Matrix W W ℂ)

  | query (Q : Oracle → Matrix W W ℂ)

structure QuantumQueryAlgorithm (Oracle W : Type*) [Fintype W] [DecidableEq W] where

  init : W → ℂ

  init_normalized : ∑ w : W, ‖init w‖ ^ 2 = 1

  program : List (ProgramStep Oracle W)

  program_unitary : ∀ s ∈ program, ∀ M, s = ProgramStep.unitary M →
    M ∈ Matrix.unitaryGroup W ℂ

  program_query_unitary : ∀ s ∈ program, ∀ Q, s = ProgramStep.query Q →
    ∀ O, Q O ∈ Matrix.unitaryGroup W ℂ

def ProgramStep.apply {Oracle W : Type*} [Fintype W] (s : ProgramStep Oracle W)
    (O : Oracle) (v : W → ℂ) : W → ℂ :=
  match s with
  | .unitary M => M *ᵥ v
  | .query Q => Q O *ᵥ v

def QuantumQueryAlgorithm.run {Oracle W : Type*} [Fintype W] [DecidableEq W]
    (A : QuantumQueryAlgorithm Oracle W) (O : Oracle) : W → ℂ :=
  A.program.foldl (fun v s => s.apply O v) A.init

def QuantumQueryAlgorithm.queryCount {Oracle W : Type*} [Fintype W] [DecidableEq W]
    (A : QuantumQueryAlgorithm Oracle W) : ℕ :=
  (A.program.filter (fun s => match s with | .query _ => true | _ => false)).length

def acceptProb {W : Type*} [Fintype W] (v : W → ℂ) (accept : Finset W) : ℝ :=
  ∑ w ∈ accept, ‖v w‖ ^ 2

def SimulatesWithQueries (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (t δ : ℝ) (q : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (A : QuantumQueryAlgorithm (RowOracle ι) W) (readout : W → ι → ℂ),
    A.queryCount ≤ q ∧
    ∑ k : ι,
      ‖(∑ w : W, readout w k * A.run (fun i j => H i j) w) - (timeEvolution H t *ᵥ ψ) k‖ ^ 2
        ≤ δ ^ 2

def SimulatesPhaseWithQueries (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (t δ : ℝ) (q : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (A : Matrix ι ι ℝ → QuantumQueryAlgorithm (PhaseOracle ι) W) (readout : W → ι → ℂ),
    (A (absMatrix H)).queryCount ≤ q ∧
    ∑ k : ι,
      ‖(∑ w : W, readout w k * (A (absMatrix H)).run (phaseEntry H) w)
          - (timeEvolution H t *ᵥ ψ) k‖ ^ 2 ≤ δ ^ 2

def signOf : Bool → ℝ
  | true => 1
  | false => -1

def signVec {M : ℕ} (b : Fin M → Bool) : Fin M → ℝ := fun i => signOf (b i)

def probOf (M : ℕ) (E : (Fin M → Bool) → Prop) : ℝ := by
  classical
  exact (Finset.univ.filter (fun b : Fin M → Bool => E b)).card / (2 : ℝ) ^ M

def promiseStrings (M B : ℕ) : Finset (Fin M → Bool) := by
  classical
  exact Finset.univ.filter (fun b : Fin M → Bool =>
    (∑ i, signVec b i = (B : ℝ)) ∨ (∑ i, signVec b i = -(B : ℝ)))

def promiseB (M : ℕ) : ℕ := 2 * Nat.floor (Real.sqrt (M * Real.log M) / 2) + M % 2

def promiseSet (M : ℕ) : Finset (Fin M → Bool) := promiseStrings M (promiseB M)

def AvgDecidesWithQueries (M B : ℕ) (q : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QuantumQueryAlgorithm (Fin M → Bool) W) (accept : Finset W),
    A.queryCount ≤ q ∧
    ∀ b ∈ promiseStrings M B,
      (if ∑ i, signVec b i = (B : ℝ) then (2 : ℝ) / 3 ≤ acceptProb (A.run b) accept
       else (2 : ℝ) / 3 ≤ 1 - acceptProb (A.run b) accept)

end Qatlib.Papers.NonSparseHam09.MainResults
