/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LCU
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Parallel QSVT circuit compilation

This module compiles branch-dependent alternating phase sequences into adjoint-query circuits
sharing `parallelOracle`. `compileParallelQSVT` evaluates to the block selection of the
branchwise sequences and has one query per phase-list entry and one additional explicit gate.

Pairing phases with their complex conjugates gives `compileRealPartQSVT`. The counted
realization theorems encode the real response polynomial on the appropriate blocks of a
Hermitian dilation, or equivalently as odd, left, and right singular-value transforms, in the
framework of [GilyenSuLowWiebe2019].

## Main statements

* `evaluate_compileParallelQSVT`: evaluation of the parallel compiler.
* `counts_compileRealPartQSVT`: exact query and gate counts.
* `realPartQSVT_odd_counted_singularEncoding`: the odd singular transform.
* `realPartQSVT_even_right_counted_singularEncoding`: the even right singular transform.

## References

* [Gilyén, Su, Low, and Wiebe, 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.BlockEncoding.LCU
set_option warningAsError false


open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.CopyEvolution.Discriminate

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open Kronecker

section SelectAlgebra

variable {J H : Type*} [Fintype J] [Fintype H] [DecidableEq J] [DecidableEq H]

omit [DecidableEq H] in

/-- Multiplication of block selections is selection of the blockwise products. -/
theorem parallel_select_mul (U V : J → Matrix H H ℂ) :
    select U * select V = select (fun j => U j * V j) := by
  ext ⟨j, i⟩ ⟨k, l⟩
  by_cases h : j = k
  · subst k
    simp [select, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, ite_mul]
  · simp [select, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, ite_mul, h]

omit [Fintype J] [Fintype H] [DecidableEq H] in

/-- The conjugate transpose of a block selection is selection of the conjugate-transposed
blocks. -/
theorem parallel_select_adjoint (U : J → Matrix H H ℂ) :
    (select U)ᴴ = select (fun j => (U j)ᴴ) := by
  ext ⟨j, i⟩ ⟨k, l⟩
  by_cases h : j = k
  · subst k
    simp [select, Matrix.conjTranspose_apply]
  · simp [select, Matrix.conjTranspose_apply, h, Ne.symm h]

omit [Fintype J] [Fintype H] in

/-- Selecting the identity on every branch gives the identity matrix. -/
theorem parallel_select_one : select (fun _ : J => (1 : Matrix H H ℂ)) = 1 := by
  ext ⟨j, i⟩ ⟨k, l⟩
  by_cases h : j = k
  · subst k
    simp [select, Matrix.one_apply]
  · simp [select, Matrix.one_apply, h]

/-- The oracle applying the same matrix `U` on every branch of an index register. -/
noncomputable def parallelOracle (U : Matrix H H ℂ) : Matrix (J × H) (J × H) ℂ :=
  select (fun _ : J => U)

omit [Fintype J] [Fintype H] [DecidableEq H] in

/-- The parallel oracle is the Kronecker product of the branch-register identity with `U`. -/
theorem parallelOracle_eq_kronecker (U : Matrix H H ℂ) :
    parallelOracle (J := J) U = (1 : Matrix J J ℂ) ⊗ₖ U := by
  ext ⟨j, i⟩ ⟨k, l⟩
  simp [parallelOracle, select, Matrix.one_apply, ite_mul]

omit [Fintype J] [Fintype H] [DecidableEq H] in

/-- The adjoint parallel oracle is the parallel oracle for `Uᴴ`. -/
theorem parallelOracle_adjoint (U : Matrix H H ℂ) :
    (parallelOracle (J := J) U)ᴴ = parallelOracle (J := J) Uᴴ := by
  exact parallel_select_adjoint (fun _ : J => U)

/-- The parallel oracle is unitary whenever its underlying oracle is unitary. -/
theorem parallelOracle_unitary {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    parallelOracle (J := J) U ∈ Matrix.unitaryGroup (J × H) ℂ :=
  select_unitary _ (fun _ => hU)

/-- Selecting phase rotations about an orthogonal projector gives a unitary matrix when every
selected phase has modulus one. -/
theorem parallelPhase_unitary {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    (z : J → ℂ) (hz : ∀ j, IsPhase (z j)) :
    select (fun j => phaseRotation P (z j)) ∈ Matrix.unitaryGroup (J × H) ℂ :=
  select_unitary _ (fun j => phaseRotation_unitary hP (hz j))

end SelectAlgebra

section Compilation

variable {J H : Type*} [Fintype J] [Fintype H] [DecidableEq J] [DecidableEq H]

/-- The recursive adjoint-query circuit compiling branch-dependent alternating phase sequences
with a common oracle. -/
noncomputable def compileParallelQSVT (P Q : Matrix H H ℂ) (base : J → ℂ) :
    List (J → ℂ) → List (AdjointStep (J × H))
  | [] => [.gate (select (fun j => phaseRotation Q (base j)))]
  | z :: zs => .gate (select (fun j => phaseRotation Q (z j))) :: .forward ::
      (compileParallelQSVT Q P base zs).map swapQueries

/-- The compiled parallel circuit evaluates to the block selection of the branchwise
`phasedAlternating` matrices. -/
theorem evaluate_compileParallelQSVT (U P Q : Matrix H H ℂ) (base : J → ℂ)
    (zs : List (J → ℂ)) :
    evaluate (parallelOracle U) (compileParallelQSVT P Q base zs) =
      select (fun j => phasedAlternating U P Q (base j) (zs.map (fun z => z j))) := by
  induction zs generalizing U P Q with
  | nil => simp [compileParallelQSVT, evaluate, instructionMatrix, phasedAlternating]
  | cons z zs ih =>
    simp only [compileParallelQSVT, evaluate, instructionMatrix, evaluate_swapQueries,
      parallelOracle_adjoint, ih]
    rw [parallelOracle, parallel_select_mul, parallel_select_mul]
    congr 1
    funext j
    simp [phasedAlternating, Matrix.mul_assoc]

omit [Fintype J] [Fintype H] in

/-- The compiled parallel QSVT circuit uses one oracle query per phase-list entry. -/
theorem queryCount_compileParallelQSVT (P Q : Matrix H H ℂ) (base : J → ℂ)
    (zs : List (J → ℂ)) :
    adjointQueryCount (compileParallelQSVT P Q base zs) = zs.length := by
  induction zs generalizing P Q with
  | nil => rfl
  | cons z zs ih => simp [compileParallelQSVT, adjointQueryCount, ih]

omit [Fintype J] [Fintype H] in

/-- The compiled parallel QSVT circuit has `zs.length + 1` explicit gates. -/
theorem gateCount_compileParallelQSVT (P Q : Matrix H H ℂ) (base : J → ℂ)
    (zs : List (J → ℂ)) :
    adjointGateCount (compileParallelQSVT P Q base zs) = zs.length + 1 := by
  induction zs generalizing P Q with
  | nil => rfl
  | cons z zs ih => simp [compileParallelQSVT, adjointGateCount, ih]

/-- For a unitary oracle, orthogonal projectors, and unit phases, the compiled parallel QSVT
circuit evaluates to a unitary matrix. -/
theorem evaluate_compileParallelQSVT_unitary {U P Q : Matrix H H ℂ}
    (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (base : J → ℂ) (hb : ∀ j, IsPhase (base j)) (zs : List (J → ℂ))
    (hzs : ∀ z ∈ zs, ∀ j, IsPhase (z j)) :
    evaluate (parallelOracle U) (compileParallelQSVT P Q base zs) ∈
      Matrix.unitaryGroup (J × H) ℂ := by
  rw [evaluate_compileParallelQSVT]
  apply select_unitary
  intro j
  apply phasedAlternating_unitary hU hP hQ (hb j)
  intro w hw
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
  exact hzs z hz j

/-- Swapping the queries in the parallel compilation evaluates to branchwise alternating
sequences with oracle `Uᴴ` and exchanged projectors. -/
theorem evaluate_compileParallelQSVT_swap (U P Q : Matrix H H ℂ) (base : J → ℂ)
    (zs : List (J → ℂ)) :
    evaluate (parallelOracle U) ((compileParallelQSVT Q P base zs).map swapQueries) =
      select (fun j => phasedAlternating Uᴴ Q P (base j) (zs.map (fun z => z j))) := by
  rw [evaluate_swapQueries, parallelOracle_adjoint, evaluate_compileParallelQSVT]

omit [Fintype J] [Fintype H] in

/-- Swapping queries preserves the parallel compilation counts: `zs.length` queries and
`zs.length + 1` gates. -/
theorem counts_compileParallelQSVT_swap (P Q : Matrix H H ℂ) (base : J → ℂ)
    (zs : List (J → ℂ)) :
    adjointQueryCount ((compileParallelQSVT Q P base zs).map swapQueries) = zs.length ∧
      adjointGateCount ((compileParallelQSVT Q P base zs).map swapQueries) = zs.length + 1 := by
  simp [queryCount_compileParallelQSVT, gateCount_compileParallelQSVT]

end Compilation

/-- The Boolean phase family choosing `z` on the true branch and its complex conjugate on the
false branch. -/
noncomputable def conjugateParallelPhase (z : ℂ) : Bool → ℂ :=
  fun b => if b then z else star z

/-- The list of Boolean phase families pairing each phase with its complex conjugate. -/
noncomputable def conjugateParallelPhases (zs : List ℂ) : List (Bool → ℂ) :=
  zs.map conjugateParallelPhase

/-- Evaluating the conjugate phase families on a Boolean branch yields `zs` on true and `zs.map
star` on false. -/
theorem conjugateParallelPhases_branch (zs : List ℂ) (b : Bool) :
    (conjugateParallelPhases zs).map (fun z => z b) =
      if b then zs else zs.map star := by
  cases b <;> simp [conjugateParallelPhases, conjugateParallelPhase, List.map_map,
    Function.comp_def]

section ConjugateCompilation

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The conjugate parallel circuit selects the original alternating phase sequence on true and
its conjugated-phase sequence on false. -/
theorem evaluate_conjugateParallelQSVT (U P Q : Matrix H H ℂ) (base : ℂ)
    (zs : List ℂ) :
    evaluate (parallelOracle U)
      (compileParallelQSVT P Q (conjugateParallelPhase base) (conjugateParallelPhases zs)) =
      select (fun b : Bool => if b then phasedAlternating U P Q base zs
        else phasedAlternating U P Q (star base) (zs.map star)) := by
  rw [evaluate_compileParallelQSVT]
  congr 1
  funext b
  cases b <;> simp [conjugateParallelPhases_branch, conjugateParallelPhase]

omit [Fintype H] in

/-- The conjugate parallel compilation uses `zs.length` queries and `zs.length + 1` gates. -/
theorem counts_conjugateParallelQSVT (P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    adjointQueryCount
      (compileParallelQSVT P Q (conjugateParallelPhase base) (conjugateParallelPhases zs)) =
        zs.length ∧
    adjointGateCount
      (compileParallelQSVT P Q (conjugateParallelPhase base) (conjugateParallelPhases zs)) =
        zs.length + 1 := by
  simp [queryCount_compileParallelQSVT, gateCount_compileParallelQSVT, conjugateParallelPhases]

end ConjugateCompilation

section RealPartCompilation

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The adjoint-query circuit compiling the two conjugate phase branches used by real-part QSVT. -/
noncomputable def compileRealPartQSVT (P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    List (AdjointStep (Bool × H)) :=
  compileParallelQSVT P Q (conjugateParallelPhase base) (conjugateParallelPhases zs)

/-- The real-part compilation evaluates to `realPartQSVT`. -/
theorem evaluate_compileRealPartQSVT (U P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    evaluate (parallelOracle U) (compileRealPartQSVT P Q base zs) =
      realPartQSVT U P Q base zs := by
  exact evaluate_conjugateParallelQSVT U P Q base zs

omit [Fintype H] in

/-- The real-part QSVT compilation uses `zs.length` queries and `zs.length + 1` gates. -/
theorem counts_compileRealPartQSVT (P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    adjointQueryCount (compileRealPartQSVT P Q base zs) = zs.length ∧
      adjointGateCount (compileRealPartQSVT P Q base zs) = zs.length + 1 :=
  counts_conjugateParallelQSVT P Q base zs

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- For an odd-length phase sequence, a circuit encodes the upper-right block of the real
response polynomial evaluated on the Hermitian dilation of `A`. It uses `zs.length` queries
and `zs.length + 1` gates. -/
theorem realPartQSVT_odd_counted_realization {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1) :
    ∃ cs : List (AdjointStep (Bool × H)),
      ProjectedUnitaryEncoding
        (aeval (hermitianDilation A) (realPartPolynomial (responseP base zs))).toBlocks₁₂
        (evaluate (parallelOracle U) cs) (averageFrame L) (averageFrame R) ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨compileRealPartQSVT (rangeProjector R) (rangeProjector L) base zs, ?_,
    (counts_compileRealPartQSVT _ _ _ _).1, (counts_compileRealPartQSVT _ _ _ _).2⟩
  rw [evaluate_compileRealPartQSVT]
  exact realPartQSVT_odd_projectedEncoding h hb zs hzs hodd

/-- For an even-length phase sequence, a circuit encodes the upper-left block of the real
response polynomial on the Hermitian dilation, using the averaged left frame. Its counts are
`zs.length` queries and `zs.length + 1` gates. -/
theorem realPartQSVT_even_left_counted_realization {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ∃ cs : List (AdjointStep (Bool × H)),
      ProjectedUnitaryEncoding
        (aeval (hermitianDilation A) (realPartPolynomial (responseP base zs))).toBlocks₁₁
        (evaluate (parallelOracle U) cs) (averageFrame L) (averageFrame L) ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨compileRealPartQSVT (rangeProjector R) (rangeProjector L) base zs, ?_,
    (counts_compileRealPartQSVT _ _ _ _).1, (counts_compileRealPartQSVT _ _ _ _).2⟩
  rw [evaluate_compileRealPartQSVT]
  exact realPartQSVT_even_left_projectedEncoding h hb zs hzs heven

/-- For an even-length phase sequence, a circuit encodes the lower-right block of the real
response polynomial on the Hermitian dilation, using the averaged right frame. Its counts
are `zs.length` queries and `zs.length + 1` gates. -/
theorem realPartQSVT_even_right_counted_realization {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ∃ cs : List (AdjointStep (Bool × H)),
      ProjectedUnitaryEncoding
        (aeval (hermitianDilation A) (realPartPolynomial (responseP base zs))).toBlocks₂₂
        (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame R) ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨(compileRealPartQSVT (rangeProjector L) (rangeProjector R) base zs).map swapQueries,
    ?_, ?_, ?_⟩
  · rw [evaluate_swapQueries, parallelOracle_adjoint, evaluate_compileRealPartQSVT]
    exact realPartQSVT_even_right_projectedEncoding h hb zs hzs heven
  · rw [adjointQueryCount_swapQueries]
    exact (counts_compileRealPartQSVT _ _ _ _).1
  · rw [adjointGateCount_swapQueries]
    exact (counts_compileRealPartQSVT _ _ _ _).2

/-- For an odd-length phase sequence, a circuit encodes the odd singular-value transform with
response equal to the real part of the response polynomial. It uses `zs.length` queries and
`zs.length + 1` gates, as in real-polynomial QSVT [GilyenSuLowWiebe2019]. -/
theorem realPartQSVT_odd_counted_singularEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1) :
    ∃ cs : List (AdjointStep (Bool × H)),
      ProjectedUnitaryEncoding
        (oddSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ)))
        (evaluate (parallelOracle U) cs) (averageFrame L) (averageFrame R) ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  rw [← realPartResponse_odd_eq_singularTransform h base zs hodd]
  exact realPartQSVT_odd_counted_realization h hb zs hzs hodd

/-- For an even-length phase sequence, a circuit encodes the left singular-value transform given
by the real response polynomial, with `zs.length` queries and `zs.length + 1` gates. -/
theorem realPartQSVT_even_left_counted_singularEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ∃ cs : List (AdjointStep (Bool × H)),
      ProjectedUnitaryEncoding
        (leftSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ)))
        (evaluate (parallelOracle U) cs) (averageFrame L) (averageFrame L) ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  rw [← realPartResponse_even_left_eq_singularTransform h base zs heven]
  exact realPartQSVT_even_left_counted_realization h hb zs hzs heven

/-- For an even-length phase sequence, a circuit encodes the right singular-value transform
given by the real response polynomial. It uses `zs.length` queries and `zs.length + 1`
gates, as in real-polynomial QSVT [GilyenSuLowWiebe2019]. -/
theorem realPartQSVT_even_right_counted_singularEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ∃ cs : List (AdjointStep (Bool × H)),
      ProjectedUnitaryEncoding
        (rightSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ)))
        (evaluate (parallelOracle U) cs) (averageFrame R) (averageFrame R) ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  rw [← realPartResponse_even_right_eq_singularTransform h base zs heven]
  exact realPartQSVT_even_right_counted_realization h hb zs hzs heven

end RealPartCompilation

end Qatlib.Concepts.CopyEvolution.Discriminate
