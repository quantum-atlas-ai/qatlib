/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LCU
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
import Mathlib.LinearAlgebra.Matrix.Kronecker
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

theorem parallel_select_mul (U V : J → Matrix H H ℂ) :
    select U * select V = select (fun j => U j * V j) := by
  ext ⟨j, i⟩ ⟨k, l⟩
  by_cases h : j = k
  · subst k
    simp [select, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, ite_mul]
  · simp [select, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, ite_mul, h]

omit [Fintype J] [Fintype H] [DecidableEq H] in

theorem parallel_select_adjoint (U : J → Matrix H H ℂ) :
    (select U)ᴴ = select (fun j => (U j)ᴴ) := by
  ext ⟨j, i⟩ ⟨k, l⟩
  by_cases h : j = k
  · subst k
    simp [select, Matrix.conjTranspose_apply]
  · simp [select, Matrix.conjTranspose_apply, h, Ne.symm h]

omit [Fintype J] [Fintype H] in

theorem parallel_select_one : select (fun _ : J => (1 : Matrix H H ℂ)) = 1 := by
  ext ⟨j, i⟩ ⟨k, l⟩
  by_cases h : j = k
  · subst k
    simp [select, Matrix.one_apply]
  · simp [select, Matrix.one_apply, h]

noncomputable def parallelOracle (U : Matrix H H ℂ) : Matrix (J × H) (J × H) ℂ :=
  select (fun _ : J => U)

omit [Fintype J] [Fintype H] [DecidableEq H] in

theorem parallelOracle_eq_kronecker (U : Matrix H H ℂ) :
    parallelOracle (J := J) U = (1 : Matrix J J ℂ) ⊗ₖ U := by
  ext ⟨j, i⟩ ⟨k, l⟩
  simp [parallelOracle, select, Matrix.one_apply, ite_mul]

omit [Fintype J] [Fintype H] [DecidableEq H] in

theorem parallelOracle_adjoint (U : Matrix H H ℂ) :
    (parallelOracle (J := J) U)ᴴ = parallelOracle (J := J) Uᴴ := by
  exact parallel_select_adjoint (fun _ : J => U)

theorem parallelOracle_unitary {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    parallelOracle (J := J) U ∈ Matrix.unitaryGroup (J × H) ℂ :=
  select_unitary _ (fun _ => hU)

theorem parallelPhase_unitary {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    (z : J → ℂ) (hz : ∀ j, IsPhase (z j)) :
    select (fun j => phaseRotation P (z j)) ∈ Matrix.unitaryGroup (J × H) ℂ :=
  select_unitary _ (fun j => phaseRotation_unitary hP (hz j))

end SelectAlgebra

section Compilation

variable {J H : Type*} [Fintype J] [Fintype H] [DecidableEq J] [DecidableEq H]

noncomputable def compileParallelQSVT (P Q : Matrix H H ℂ) (base : J → ℂ) :
    List (J → ℂ) → List (AdjointStep (J × H))
  | [] => [.gate (select (fun j => phaseRotation Q (base j)))]
  | z :: zs => .gate (select (fun j => phaseRotation Q (z j))) :: .forward ::
      (compileParallelQSVT Q P base zs).map swapQueries

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

theorem queryCount_compileParallelQSVT (P Q : Matrix H H ℂ) (base : J → ℂ)
    (zs : List (J → ℂ)) :
    adjointQueryCount (compileParallelQSVT P Q base zs) = zs.length := by
  induction zs generalizing P Q with
  | nil => rfl
  | cons z zs ih => simp [compileParallelQSVT, adjointQueryCount, ih]

omit [Fintype J] [Fintype H] in

theorem gateCount_compileParallelQSVT (P Q : Matrix H H ℂ) (base : J → ℂ)
    (zs : List (J → ℂ)) :
    adjointGateCount (compileParallelQSVT P Q base zs) = zs.length + 1 := by
  induction zs generalizing P Q with
  | nil => rfl
  | cons z zs ih => simp [compileParallelQSVT, adjointGateCount, ih]

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

theorem evaluate_compileParallelQSVT_swap (U P Q : Matrix H H ℂ) (base : J → ℂ)
    (zs : List (J → ℂ)) :
    evaluate (parallelOracle U) ((compileParallelQSVT Q P base zs).map swapQueries) =
      select (fun j => phasedAlternating Uᴴ Q P (base j) (zs.map (fun z => z j))) := by
  rw [evaluate_swapQueries, parallelOracle_adjoint, evaluate_compileParallelQSVT]

omit [Fintype J] [Fintype H] in

theorem counts_compileParallelQSVT_swap (P Q : Matrix H H ℂ) (base : J → ℂ)
    (zs : List (J → ℂ)) :
    adjointQueryCount ((compileParallelQSVT Q P base zs).map swapQueries) = zs.length ∧
      adjointGateCount ((compileParallelQSVT Q P base zs).map swapQueries) = zs.length + 1 := by
  simp [queryCount_compileParallelQSVT, gateCount_compileParallelQSVT]

end Compilation

noncomputable def conjugateParallelPhase (z : ℂ) : Bool → ℂ :=
  fun b => if b then z else star z

noncomputable def conjugateParallelPhases (zs : List ℂ) : List (Bool → ℂ) :=
  zs.map conjugateParallelPhase

theorem conjugateParallelPhases_branch (zs : List ℂ) (b : Bool) :
    (conjugateParallelPhases zs).map (fun z => z b) =
      if b then zs else zs.map star := by
  cases b <;> simp [conjugateParallelPhases, conjugateParallelPhase, List.map_map,
    Function.comp_def]

section ConjugateCompilation

variable {H : Type*} [Fintype H] [DecidableEq H]

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

noncomputable def compileRealPartQSVT (P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    List (AdjointStep (Bool × H)) :=
  compileParallelQSVT P Q (conjugateParallelPhase base) (conjugateParallelPhases zs)

theorem evaluate_compileRealPartQSVT (U P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    evaluate (parallelOracle U) (compileRealPartQSVT P Q base zs) =
      realPartQSVT U P Q base zs := by
  exact evaluate_conjugateParallelQSVT U P Q base zs

omit [Fintype H] in

theorem counts_compileRealPartQSVT (P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    adjointQueryCount (compileRealPartQSVT P Q base zs) = zs.length ∧
      adjointGateCount (compileRealPartQSVT P Q base zs) = zs.length + 1 :=
  counts_conjugateParallelQSVT P Q base zs

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

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
