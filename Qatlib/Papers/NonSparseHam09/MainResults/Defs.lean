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

/-!
# Matrix norms and Hamiltonian simulation interfaces

Defines entry, column, and spectral norms, the entrywise absolute-value matrix, Hamiltonian
evolution, and graph arboricity. It also introduces finite quantum-query programs and simulation
predicates, together with Boolean sign strings and the finite promise distributions used in
lower-bound statements. See [ChildsKothari2010] for the surrounding analysis.

## Main statements

* `specNorm`: The Euclidean operator norm of a finite real or complex matrix.
* `QuantumQueryAlgorithm`: A normalized initial state and a finite program whose fixed and
  oracle-dependent step matrices are unitary.
* `promiseStrings`: The finite set of Boolean strings whose associated sign sum equals `B` or
  `-B`.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The maximum absolute value of an entry of a complex matrix on a finite nonempty index type. -/
def maxNorm [Nonempty ι] (H : Matrix ι ι ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : ι =>
    Finset.univ.sup' Finset.univ_nonempty fun j : ι => ‖H i j‖

/-- The maximum Euclidean column norm of a complex matrix on a finite nonempty index type. -/
def mcnNorm [Nonempty ι] (H : Matrix ι ι ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j : ι => Real.sqrt (∑ i : ι, ‖H i j‖ ^ 2)

/-- The maximum column sum of entry norms for a complex matrix on a finite nonempty index type. -/
def l1Norm [Nonempty ι] (H : Matrix ι ι ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j : ι => ∑ i : ι, ‖H i j‖

/-- The real matrix of entrywise complex norms. -/
def absMatrix (H : Matrix ι ι ℂ) : Matrix ι ι ℝ := fun i j => ‖H i j‖

/-- The Euclidean operator norm of a finite real or complex matrix. -/
def specNorm {𝕜 : Type*} [RCLike 𝕜] (H : Matrix ι ι 𝕜) : ℝ := by
  letI := Matrix.instL2OpNormedAddCommGroup (m := ι) (n := ι) (𝕜 := 𝕜)
  exact ‖H‖

/-- The matrix exponential `exp(-i * t * H)` defining Hamiltonian time evolution. -/
def timeEvolution (H : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H)

/-- The simple graph connecting distinct indices when at least one of the two corresponding
matrix entries is nonzero. -/
def matrixGraph (H : Matrix ι ι ℂ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (H i j ≠ 0 ∨ H j i ≠ 0)
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- The predicate that a graph's edges are the union of the edges of `k` acyclic graphs on the
same vertex type. -/
def GraphArboricityLE {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ F : Fin k → SimpleGraph V,
    (∀ l, (F l).IsAcyclic) ∧ ∀ i j, G.Adj i j ↔ ∃ l, (F l).Adj i j

/-- The `(2 * M + 1)`-dimensional symmetric circulant matrix with zero diagonal and off-diagonal
first-row entries given by `s` followed by its reversal. -/
def circulantMatrix {M : ℕ} (s : Fin M → ℝ) : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ :=
  fun i j =>
    let d := (j.val + (2 * M + 1) - i.val) % (2 * M + 1)
    if h0 : d = 0 then 0
    else if h1 : d ≤ M then s ⟨d - 1, by omega⟩
    else
      have hd : d < 2 * M + 1 := Nat.mod_lt _ (by omega)
      s ⟨2 * M - d, by omega⟩

/-- A finite-dimensional unitary step matrix together with a map from vertices to basis-state
indices. -/
structure DiscreteTimeWalk (ι : Type*) [Fintype ι] [DecidableEq ι] where

  size : ℕ

  step : Matrix (Fin size) (Fin size) ℂ

  step_unitary : step ∈ Matrix.unitaryGroup (Fin size) ℂ

  vertexState : ι → Fin size

/-- The existence of a discrete-time walk whose step support obeys the stated matrix-graph
condition and whose `n`th power approximates each designated time-evolution entry within
`δ`. -/
def WalkSimulates (H : Matrix ι ι ℂ) (t δ : ℝ) (n : ℕ) : Prop :=
  ∃ W : DiscreteTimeWalk ι,
    (∀ a b, W.step a b ≠ 0 → ∃ i j, W.vertexState i = a ∧ W.vertexState j = b ∧
      (i = j ∨ H i j ≠ 0 ∨ H j i ≠ 0)) ∧
    ∀ i j, ‖((W.step ^ n) (W.vertexState i) (W.vertexState j)) - timeEvolution H t i j‖ ≤ δ

/-- A matrix-entry oracle represented as a function `ι → ι → ℂ`. -/
abbrev RowOracle (ι : Type*) := ι → ι → ℂ

/-- A phase-oracle interface represented as a function `ι → ι → ℂ`. -/
abbrev PhaseOracle (ι : Type*) := ι → ι → ℂ

/-- The normalized complex phase of `H i j`, with value one when that entry is zero. -/
def phaseEntry (H : Matrix ι ι ℂ) (i j : ι) : ℂ :=
  if H i j = 0 then 1 else H i j / (‖H i j‖ : ℂ)

/-- A program step given either by a fixed matrix or by an oracle-dependent matrix. -/
inductive ProgramStep (Oracle W : Type*) where

  | unitary (M : Matrix W W ℂ)

  | query (Q : Oracle → Matrix W W ℂ)

/-- A normalized initial state and a finite program whose fixed and oracle-dependent step
matrices are unitary. -/
structure QuantumQueryAlgorithm (Oracle W : Type*) [Fintype W] [DecidableEq W] where

  init : W → ℂ

  init_normalized : ∑ w : W, ‖init w‖ ^ 2 = 1

  program : List (ProgramStep Oracle W)

  program_unitary : ∀ s ∈ program, ∀ M, s = ProgramStep.unitary M →
    M ∈ Matrix.unitaryGroup W ℂ

  program_query_unitary : ∀ s ∈ program, ∀ Q, s = ProgramStep.query Q →
    ∀ O, Q O ∈ Matrix.unitaryGroup W ℂ

/-- The action of a program step on a vector, using its fixed matrix or its query matrix
evaluated at `O`. -/
def ProgramStep.apply {Oracle W : Type*} [Fintype W] (s : ProgramStep Oracle W)
    (O : Oracle) (v : W → ℂ) : W → ℂ :=
  match s with
  | .unitary M => M *ᵥ v
  | .query Q => Q O *ᵥ v

/-- The final vector obtained by applying all program steps in list order to the initial state. -/
def QuantumQueryAlgorithm.run {Oracle W : Type*} [Fintype W] [DecidableEq W]
    (A : QuantumQueryAlgorithm Oracle W) (O : Oracle) : W → ℂ :=
  A.program.foldl (fun v s => s.apply O v) A.init

/-- The number of query steps in a quantum-query program. -/
def QuantumQueryAlgorithm.queryCount {Oracle W : Type*} [Fintype W] [DecidableEq W]
    (A : QuantumQueryAlgorithm Oracle W) : ℕ :=
  (A.program.filter (fun s => match s with | .query _ => true | _ => false)).length

/-- The sum of squared coordinate norms over the accepting basis states. -/
def acceptProb {W : Type*} [Fintype W] (v : W → ℂ) (accept : Finset W) : ℝ :=
  ∑ w ∈ accept, ‖v w‖ ^ 2

/-- The existence of a matrix-entry query algorithm and linear readout using at most `q` queries
with squared Euclidean error at most `δ²` from the evolved input vector. -/
def SimulatesWithQueries (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (t δ : ℝ) (q : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (A : QuantumQueryAlgorithm (RowOracle ι) W) (readout : W → ι → ℂ),
    A.queryCount ≤ q ∧
    ∑ k : ι,
      ‖(∑ w : W, readout w k * A.run (fun i j => H i j) w) - (timeEvolution H t *ᵥ ψ) k‖ ^ 2
        ≤ δ ^ 2

/-- The existence of a query-algorithm family indexed by entrywise magnitudes and a linear
readout, whose run on `phaseEntry H` uses at most `q` queries and has squared Euclidean
error at most `δ²`. -/
def SimulatesPhaseWithQueries (H : Matrix ι ι ℂ) (ψ : ι → ℂ) (t δ : ℝ) (q : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (A : Matrix ι ι ℝ → QuantumQueryAlgorithm (PhaseOracle ι) W) (readout : W → ι → ℂ),
    (A (absMatrix H)).queryCount ≤ q ∧
    ∑ k : ι,
      ‖(∑ w : W, readout w k * (A (absMatrix H)).run (phaseEntry H) w)
          - (timeEvolution H t *ᵥ ψ) k‖ ^ 2 ≤ δ ^ 2

/-- The real sign map sending `true` to one and `false` to negative one. -/
def signOf : Bool → ℝ
  | true => 1
  | false => -1

/-- The real sign vector obtained by applying `signOf` to each bit. -/
def signVec {M : ℕ} (b : Fin M → Bool) : Fin M → ℝ := fun i => signOf (b i)

/-- The fraction of length-`M` Boolean strings satisfying the event `E`, with denominator `2^M`. -/
def probOf (M : ℕ) (E : (Fin M → Bool) → Prop) : ℝ := by
  classical
  exact (Finset.univ.filter (fun b : Fin M → Bool => E b)).card / (2 : ℝ) ^ M

/-- The finite set of Boolean strings whose associated sign sum equals `B` or `-B`. -/
def promiseStrings (M B : ℕ) : Finset (Fin M → Bool) := by
  classical
  exact Finset.univ.filter (fun b : Fin M → Bool =>
    (∑ i, signVec b i = (B : ℝ)) ∨ (∑ i, signVec b i = -(B : ℝ)))

/-- The parity-adjusted bias `2 * floor(√(M * log M) / 2) + M % 2`. -/
def promiseB (M : ℕ) : ℕ := 2 * Nat.floor (Real.sqrt (M * Real.log M) / 2) + M % 2

/-- The promise strings with bias `promiseB M`. -/
def promiseSet (M : ℕ) : Finset (Fin M → Bool) := promiseStrings M (promiseB M)

/-- The existence of a quantum-query algorithm using at most `q` queries that distinguishes the
two promised sign sums with success probability at least `2 / 3` on every promise string. -/
def AvgDecidesWithQueries (M B : ℕ) (q : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : QuantumQueryAlgorithm (Fin M → Bool) W) (accept : Finset W),
    A.queryCount ≤ q ∧
    ∀ b ∈ promiseStrings M B,
      (if ∑ i, signVec b i = (B : ℝ) then (2 : ℝ) / 3 ≤ acceptProb (A.run b) accept
       else (2 : ℝ) / 3 ≤ 1 - acceptProb (A.run b) accept)

end Qatlib.Papers.NonSparseHam09.MainResults
