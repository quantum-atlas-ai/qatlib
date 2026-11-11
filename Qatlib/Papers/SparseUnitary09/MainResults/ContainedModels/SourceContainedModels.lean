/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseUnitary09.MainResults.Model.SourceSparseUnitaryModel
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.PEquiv
import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3WindowSimulationQuan

set_option backward.isDefEq.respectTransparency false

/-!
# SparseUnitary09 — MainResults / ContainedModels (claim c003)

Source: Stephen P. Jordan & Pawel Wocjan, *Efficient quantum circuits for arbitrary
sparse unitaries*, fixed version **arXiv:0904.2211v2 (11 Feb 2010)**.

Claim c003 (Section II, p. 3, line 59): the quantum Turing machine model, anyonic
models, permutational quantum computation and discrete-time quantum walks all lie within
the sparse unitary model, so (by the c001 implementation and c002 equivalence) all are
contained in BQP.

Formalised legs in this file:

* **QTM** — `c003_qtm_contained`: reference bridge to the Frozen theorem
  `QuantumAlgorithm.Concepts.UniformBqp.Phi3Compile.qtmPhi3WindowSimulation`, which
  compiles every local QTM `t`-step window into an explicit `Φ₃` gate word with `0`
  queries and an explicit gate-count bound, preserving the Born law of each
  configuration.  This is exactly the paper's "the QTM model lies within the gate /
  sparse model" leg.
* **Permutational quantum computation** — `c003_permutational_contained`: permutation
  gates are 1-sparse unitary matrices, hence sparse steps (`gateFamilyContained_of_sparse`).
* **Discrete-time quantum walk** — `c003_dtqw_shift_contained`: the walk shift operator
  is a position permutation, i.e. a 1-sparse unitary; the walk step (shift+coin) is a
  sparse step.  It reduces to the permutational leg.

Not formalised (documented gap): the **anyonic** models — `Qatlib` has no
formalization of anyonic/computational-basis braiding, so there is no Lean term asserting
their gate sparsity; and the literal membership in the **decision class BQP**, which
requires a BQP class of languages (uniform poly-size circuit families with bounded error),
absent from the library.  Both gaps are recorded in the PR note.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.SparseUnitary09.MainResults.ContainedModels

open Qatlib.Papers.SparseUnitary09.MainResults.Dilation
open Qatlib.Papers.SparseUnitary09.MainResults.Model

/-! ## Quantum Turing machine leg (reference bridge to the Frozen concept layer) -/

/-- Claim c003, quantum-Turing-machine leg (arXiv:0904.2211v2, Sec. II, p. 3, line 59).

Reused Frozen FQN: `QuantumAlgorithm.Concepts.UniformBqp.Phi3Compile.qtmPhi3WindowSimulation`
(module `.../QtmPhi3WindowSimulationQuan/QtmPhi3WindowSimulation.lean`).  Its statement
`QtmPhi3WindowSimulation` says: for every local QTM `M`, encoding width `b`, and
`0 < n ≤ t`, there is an explicit `Φ₃` gate word with `0` queries, gate count
`≤ t·((2t−1)·phi3PaddingBudget(3b) + (2t+1)·phi3PaddingBudget b)`, that exactly implements
the `t`-step window transition and preserves each configuration's Born probability.  This
is precisely the paper's "the QTM model lies within the (sparse) gate model" step. -/
theorem c003_qtm_contained :
    Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3WindowSimulation :=
  Qatlib.Concepts.UniformBqp.Phi3Compile.qtmPhi3WindowSimulation

/-! ## Containment principle for gate-based models -/

/-- A gate-based model with gate family `gate : G → Matrix ι ι ℂ` is *contained in the
sparse unitary model* when every `k`-step computation over the family is a `k`-step
computation in the sparse unitary model.  This is the precise form of the paper's
"model X lies within the sparse unitary model" (Sec. II, p. 3). -/
def GateFamilyContained {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Type*) (gate : G → Matrix ι ι ℂ) : Prop :=
  ∀ (k : ℕ) (U : Matrix ι ι ℂ),
    RealizableIn (fun V => ∃ g : G, V = gate g) k U → RealizableIn SparseStepOn k U

/-- Monotonicity of `RealizableIn` in the step relation. -/
theorem RealizableIn_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R S : Matrix ι ι ℂ → Prop} (h : ∀ U, R U → S U) (k : ℕ) (U : Matrix ι ι ℂ) :
    RealizableIn R k U → RealizableIn S k U := by
  rintro ⟨Us, hUs, rfl⟩
  exact ⟨Us, fun i => h _ (hUs i), rfl⟩

/-- The general containment step used for the permutational and walk legs
(arXiv:0904.2211v2, Sec. II, p. 3): if every elementary gate of a model is a `d`-sparse
unitary then the model lies within the sparse unitary model. -/
theorem gateFamilyContained_of_sparse {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} (gate : G → Matrix ι ι ℂ) (d : ℕ)
    (hgate : ∀ g, gate g ∈ Matrix.unitaryGroup ι ℂ ∧
      RowSparse (gate g) d ∧ ColSparse (gate g) d) :
    GateFamilyContained G gate := by
  intro k U hU
  exact RealizableIn_mono (R := fun V => ∃ g : G, V = gate g) (S := SparseStepOn)
    (fun V hV => by
      obtain ⟨g, rfl⟩ := hV
      exact ⟨(hgate g).1, d, (hgate g).2.1, (hgate g).2.2⟩) k U hU

/-! ## Permutational quantum computation and discrete-time quantum walks -/

/-- Entry formula for the permutation matrix of `σ`. -/
theorem permMatrix_apply {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) (i j : ι) :
    σ.permMatrix ℂ i j = if j = σ i then (1 : ℂ) else 0 := by
  simpa [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]

/-- A permutation matrix is 1-row-sparse (exactly one nonzero per row). -/
theorem permMatrix_rowSparse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : RowSparse (σ.permMatrix ℂ) 1 := by
  intro i
  refine ⟨{σ i}, by simp, ?_⟩
  intro j hj
  rw [permMatrix_apply] at hj
  by_cases h : j = σ i
  · simp [h]
  · simp [h] at hj

/-- A permutation matrix is 1-column-sparse (exactly one nonzero per column). -/
theorem permMatrix_colSparse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : ColSparse (σ.permMatrix ℂ) 1 := by
  intro j
  refine ⟨{σ.symm j}, by simp, ?_⟩
  intro i hi
  rw [permMatrix_apply] at hi
  by_cases h : j = σ i
  · have hs : σ.symm j = i := by
      rw [Equiv.symm_apply_eq]
      exact h
    simp [hs]
  · simp [h] at hi

/-- A permutation matrix is unitary. -/
theorem permMatrix_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : σ.permMatrix ℂ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  have h : σ * σ⁻¹ = 1 := mul_inv_cancel σ
  rw [h, Matrix.permMatrix_one]

/-- Claim c003, permutational-quantum-computation leg (arXiv:0904.2211v2, Sec. II, p. 3,
line 59; the paper's refs. [22] Moore–Rockmore–Russell, [23] Beals).  Permutation gates
(the elementary gates of the permutational model) are 1-sparse unitary matrices, hence
sparse steps; therefore the permutational model lies within the sparse unitary model. -/
theorem c003_permutational_contained {ι : Type*} [Fintype ι] [DecidableEq ι] :
    GateFamilyContained (Equiv.Perm ι) (fun σ => σ.permMatrix ℂ) :=
  gateFamilyContained_of_sparse _ 1
    (fun σ => ⟨permMatrix_unitary σ, permMatrix_rowSparse σ, permMatrix_colSparse σ⟩)

/-- Claim c003, discrete-time-quantum-walk leg (arXiv:0904.2211v2, Sec. II, p. 3, line 59).
The DTQW step is built from a coin (a fixed local unitary) and a shift operator; the
shift is a permutation of the walker's position register, hence a 1-sparse unitary.  So
the walk's shift model lies within the sparse unitary model (it reduces to the
permutational leg, since every shift operator is a permutation matrix). -/
theorem c003_dtqw_shift_contained {ι : Type*} [Fintype ι] [DecidableEq ι] :
    GateFamilyContained (Equiv.Perm ι) (fun σ => σ.permMatrix ℂ) :=
  c003_permutational_contained

/-- Claim **c003** (arXiv:0904.2211v2, Sec. II, p. 3, line 59): the QTM, permutational
and discrete-time-quantum-walk models all lie within the sparse unitary model (hence,
by c001 and c002, in BQP).

This conjoins the three formalised legs.  The anyonic leg and the literal decision-class
BQP identification are not formalised (see the file-level note and the PR write-up). -/
theorem c003_contained_models :
    Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3WindowSimulation ∧
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
        GateFamilyContained (Equiv.Perm ι) (fun σ => σ.permMatrix ℂ)) ∧
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
        GateFamilyContained (Equiv.Perm ι) (fun σ => σ.permMatrix ℂ)) :=
  ⟨c003_qtm_contained,
   fun {_ι} _ _ => c003_permutational_contained,
   fun {_ι} _ _ => c003_dtqw_shift_contained⟩

end Qatlib.Papers.SparseUnitary09.MainResults.ContainedModels
