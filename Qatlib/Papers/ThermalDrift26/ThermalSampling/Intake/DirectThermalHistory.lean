/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.DirectThermalPreparationError
import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.FiniteThermalAmplification
import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.ThermalSourcePrefixes

/-!
# Stored Direct Thermal Source Histories

This module constructs a live quantum register with a persistent classical history for the
direct thermal source associated with [JiangEtAl2026]. `preparedSourceChannel`,
`storedSourceStep`, and `storedSourceRun` append preparations and sampled index-outcome records
while preserving positivity and trace; `storedSourceRun_ideal` identifies the exact preparation
with `pathSourceMatrix`.

`historyReport` turns complete histories into finite reports, and `recordDensityLaw` and
`recordDensityState` recover record probabilities and conditional live states. Preparation and
index-law errors accumulate linearly in the number of steps and remain bounded after reporting,
including for the concrete preparation supplied by `thermalActualOAAWord`.

## Main statements

* `storedSourceRun_error` bounds the full run error by the number of steps times the single-step
  preparation and index errors.
* `storedSourceRun_ideal` and `historyReport_pathSource` identify the ideal stored and reported
  matrices with path-instrument outputs.
* `storedSourceRun_report_budget` and `thermalActualOAA_history_report_budget` give the reported
  half trace norm bound `N * (epsilon + delta)`.
* `recordDensityState_block`, `recordDensity_reassemble`, and `historyReport_blockDiagonal`
  describe the classical record blocks and their conditional density operators.

## References

* [Jiang et al., 2026][JiangEtAl2026]: Jiyu Jiang, Mingrui Jing, Jizhe Lai, Xin Wang, and Lei
  Zhang. *Thermal-Drift Sampling: Generating Thermal Ensembles for Learning Many-Body Systems*.
  2026.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open scoped BigOperators ComplexOrder

/-- The linear map that forms the Kronecker product of the fixed preparation state `eta.val`
with its input and reindexes it into two ancilla blocks. -/
def appendPreparationState {d : ℕ} (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    MatrixMap (Fin d) (Fin d ⊕ Fin d) ℂ where
  toFun A := Matrix.reindex (ancillaSumEquiv d) (ancillaSumEquiv d) (Matrix.kronecker eta.val A)
  map_add' := by intro A B; ext i k; simp [Matrix.reindex_apply, mul_add]
  map_smul' := by intro z A; ext i k; simp [Matrix.reindex_apply, mul_left_comm]

/-- Appending the density operator `eta` sends positive semidefinite live matrices to positive
semidefinite matrices. -/
theorem appendPreparationState_positive {d : ℕ} (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    (appendPreparationState (d := d) eta).IsPositive := by
  intro A hA
  exact (eta.property.1.PosSemidef_kronecker hA).submatrix _

/-- Appending the density operator `eta` preserves the trace of every live matrix. -/
theorem appendPreparationState_tracePreserving {d : ℕ} (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    (appendPreparationState (d := d) eta).IsTracePreserving := by
  intro A
  change Matrix.trace ((Matrix.kronecker eta.val A).submatrix
    (ancillaSumEquiv d).symm (ancillaSumEquiv d).symm) = _
  rw [Qatlib.Concepts.PauliClifford.ExactRank.tensorPauliTrace_submatrix]
  calc
    _ = Matrix.trace eta.val * Matrix.trace A := Matrix.trace_kronecker eta.val A
    _ = _ := by rw [eta.property.2, one_mul]

/-- The source channel on live matrices obtained by appending `eta`, applying the direct readout
for index `j`, retaining the index in a tagged register, and averaging with probabilities
`p.prob j`. -/
def preparedSourceChannel {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    MatrixMap (Fin d) ((Fin d ⊕ Fin d) × Fin L) ℂ :=
  ∑ j : Fin L, (p.prob j : ℂ) •
    ((tagIndex L d j).comp ((directReadoutMap F j).comp (appendPreparationState eta)))

/-- Embedding a matrix into the register block tagged by `j` preserves positive
semidefiniteness. -/
private theorem tag_positive (L d : ℕ) (j : Fin L) : (tagIndex L d j).IsPositive := by
  intro A hA
  exact hA.mul_mul_conjTranspose_same _

/-- Embedding a matrix into the register block tagged by `j` preserves its trace. -/
private theorem tag_tp (L d : ℕ) (j : Fin L) : (tagIndex L d j).IsTracePreserving := by
  intro A
  have h : (indexEmbedding L d j)ᴴ * indexEmbedding L d j = 1 := by
    ext a b
    simp [indexEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  change Matrix.trace (indexEmbedding L d j * A * (indexEmbedding L d j)ᴴ) = _
  rw [Matrix.trace_mul_comm (indexEmbedding L d j * A), ← Matrix.mul_assoc, h, Matrix.one_mul]

/-- The prepared source channel sends positive semidefinite live matrices to positive
semidefinite matrices. -/
theorem preparedSourceChannel_positive {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) : (preparedSourceChannel F p eta).IsPositive := by
  intro A hA
  simp only [preparedSourceChannel, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  apply Matrix.posSemidef_sum
  intro j _
  apply Matrix.PosSemidef.smul
  · exact tag_positive L d j
      (directReadoutMap_positive F j (appendPreparationState_positive eta hA))
  · exact_mod_cast p.nonneg j

/-- The prepared source channel preserves the trace of every live matrix. -/
theorem preparedSourceChannel_tracePreserving {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) : (preparedSourceChannel F p eta).IsTracePreserving := by
  intro A
  have ht (j : Fin L) : Matrix.trace
      (tagIndex L d j (directReadoutMap F j (appendPreparationState eta A))) = Matrix.trace A :=
    (tag_tp L d j _).trans
      ((directReadoutMap_tracePreserving F j _).trans (appendPreparationState_tracePreserving eta A))
  simp only [preparedSourceChannel, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp_rw [ht]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, p.sum_one, Complex.ofReal_one, one_mul]

/-- On a live density operator `rho`, the source channel with preparation `eta` equals the joint
prepared readout viewed as a map on the preparation matrix. -/
theorem preparedSourceChannel_eq_joint {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    preparedSourceChannel F p eta rho.val = jointPreparedReadout F p rho eta.val := by
  simp only [preparedSourceChannel, jointPreparedReadout, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply]
  rfl

/-- The linear map that transports both matrix indices along the finite equivalence `e`. -/
def basisReindex {I J : Type} [Fintype I] [Fintype J] (e : I ≃ J) : MatrixMap I J ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap

/-- Transporting both matrix indices along a finite equivalence preserves positive
semidefiniteness. -/
theorem basisReindex_positive {I J : Type} [Fintype I] [Fintype J] (e : I ≃ J) :
    (basisReindex e).IsPositive := by
  intro A hA
  exact hA.submatrix _

/-- Transporting both matrix indices along a finite equivalence preserves the matrix trace. -/
theorem basisReindex_tracePreserving {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) : (basisReindex e).IsTracePreserving := by
  intro A
  change Matrix.trace (A.submatrix e.symm e.symm) = Matrix.trace A
  rw [Qatlib.Concepts.PauliClifford.ExactRank.tensorPauliTrace_submatrix]

/-- The type of length-`N` histories whose entries record a sampled index in `Fin L` and a
Boolean readout outcome. -/
abbrev SourceHistory (L N : ℕ) := Fin N → (Fin L × Bool)
/-- The basis type for a live `d`-dimensional register together with a length-`N` source
history. -/
abbrev SourceRegister (L d N : ℕ) := Fin d × SourceHistory L N

/-- The finite basis equivalence flattening the live register and its history into a register of
size `d * Fintype.card (SourceHistory L N)`. -/
def historyInputEquiv (L d N : ℕ) :
    SourceRegister L d N ≃ Fin (d * Fintype.card (SourceHistory L N)) :=
  (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)).trans finProdFinEquiv

/-- The basis equivalence that converts a flattened live-history register, ancilla outcome, and
sampled index into the live register with that index-outcome pair appended to its history. -/
def historyOutputEquiv (L d N : ℕ) :
    ((Fin (d * Fintype.card (SourceHistory L N)) ⊕
      Fin (d * Fintype.card (SourceHistory L N))) × Fin L) ≃ SourceRegister L d (N+1) :=
  ((Equiv.prodCongr (ancillaSumEquiv _).symm (Equiv.refl _)).trans
    (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) (historyInputEquiv L d N).symm) (Equiv.refl _))).trans
  { toFun := fun x => (x.1.2.1, Fin.snoc x.1.2.2 (x.2, Qatlib.Foundations.PureStateMath.boolEquivFin2.symm x.1.1))
    invFun := fun x => ((Qatlib.Foundations.PureStateMath.boolEquivFin2 (x.2 (Fin.last N)).2,
      (x.1, Fin.init x.2)), (x.2 (Fin.last N)).1)
    left_inv := by rintro ⟨⟨b,i,w⟩,j⟩; simp
    right_inv := by rintro ⟨i,w⟩; simp }

/-- One source step on the live register with stored history: flatten the input, apply the
prepared source channel with each reflection extended by the identity on the history, then
append the new record by reindexing. -/
def storedSourceStep {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) (N : ℕ) :
    MatrixMap (SourceRegister L d N) (SourceRegister L d (N+1)) ℂ :=
  (basisReindex (historyOutputEquiv L d N)).comp
    ((preparedSourceChannel (withReferenceFamily F (Fintype.card (SourceHistory L N))) p eta).comp
      (basisReindex (historyInputEquiv L d N)))

/-- A stored source step maps positive semidefinite matrices to positive semidefinite matrices. -/
theorem storedSourceStep_positive {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) (N : ℕ) :
    (storedSourceStep F p eta N).IsPositive := by
  intro A hA
  exact basisReindex_positive _ (preparedSourceChannel_positive _ _ _ (basisReindex_positive _ hA))

/-- A stored source step preserves the trace of every live-history matrix. -/
theorem storedSourceStep_tracePreserving {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) (N : ℕ) :
    (storedSourceStep F p eta N).IsTracePreserving := by
  intro A
  exact (basisReindex_tracePreserving _ _).trans
    ((preparedSourceChannel_tracePreserving _ _ _ _).trans (basisReindex_tracePreserving _ A))

/-- For a positive semidefinite input of trace one, replacing the preparation `ideal` by
`native` and the index law `p` by `q` changes one stored step by at most the preparation
trace norm plus `sum j, |q.prob j - p.prob j|`. -/
theorem storedSourceStep_error {L d N : ℕ} (F : ReflectionFamily L d)
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (ideal native : Qatlib.Foundations.PureStateMath.DensityOperator 2)
    (rho : Matrix (SourceRegister L d N) (SourceRegister L d N) ℂ)
    (hrho : rho.PosSemidef) (htrace : Matrix.trace rho = 1) :
    Matrix.traceNorm (storedSourceStep F q native N rho - storedSourceStep F p ideal N rho) ≤
      Matrix.traceNorm (native.val - ideal.val) + ∑ j : Fin L, |q.prob j - p.prob j| := by
  let r := Fintype.card (SourceHistory L N)
  let sigma : Qatlib.Foundations.PureStateMath.DensityOperator (d*r) := ⟨basisReindex (historyInputEquiv L d N) rho,
    basisReindex_positive _ hrho, (basisReindex_tracePreserving _ rho).trans htrace⟩
  have h := jointPreparedReadout_total_error (withReferenceFamily F r) p q sigma ideal native
  have hn := jointPreparedReadout_positive (withReferenceFamily F r) q sigma native.property.1
  have hi := jointPreparedReadout_positive (withReferenceFamily F r) p sigma ideal.property.1
  have hc := Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction
    (basisReindex (historyOutputEquiv L d N)) (basisReindex_positive _) (basisReindex_tracePreserving _)
    (hn.isHermitian.sub hi.isHermitian)
  change Matrix.traceNorm (basisReindex (historyOutputEquiv L d N)
    (preparedSourceChannel (withReferenceFamily F r) q native sigma.val) -
    basisReindex (historyOutputEquiv L d N)
    (preparedSourceChannel (withReferenceFamily F r) p ideal sigma.val)) ≤ _
  simpa only [map_sub, preparedSourceChannel_eq_joint] using! hc.trans h

/-- The basis equivalence identifying the live register with the live register paired with its
unique empty history. -/
def emptyHistoryEquiv (L d : ℕ) : Fin d ≃ SourceRegister L d 0 where
  toFun i := (i, Fin.elim0)
  invFun x := x.1
  left_inv _ := rfl
  right_inv x := by
    change (x.1, Fin.elim0) = x
    refine Prod.ext rfl ?_
    funext j
    exact Fin.elim0 j

/-- The recursively defined state after `N` stored source steps, initialized from `rho` with an
empty history and using index law `p` and preparation `eta` at every step. -/
def storedSourceRun {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    (N : ℕ) → Matrix (SourceRegister L d N) (SourceRegister L d N) ℂ
  | 0 => basisReindex (emptyHistoryEquiv L d) rho.val
  | N+1 => storedSourceStep F p eta N (storedSourceRun F p eta rho N)

/-- The matrix produced after any number of stored source steps is positive semidefinite. -/
theorem storedSourceRun_positive {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (N : ℕ) :
    (storedSourceRun F p eta rho N).PosSemidef := by
  induction N with
  | zero => exact basisReindex_positive _ rho.property.1
  | succ N ih => exact storedSourceStep_positive F p eta N ih

/-- The matrix produced after any number of stored source steps has trace one. -/
theorem storedSourceRun_trace {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (N : ℕ) :
    Matrix.trace (storedSourceRun F p eta rho N) = 1 := by
  induction N with
  | zero => exact (basisReindex_tracePreserving _ rho.val).trans rho.property.2
  | succ N ih => exact (storedSourceStep_tracePreserving F p eta N _).trans ih

/-- The trace norm between the native run using `q` and the ideal-preparation run using `p` is
at most `N` times the sum of the single-preparation trace norm and the index-law absolute
probability difference. -/
theorem storedSourceRun_error {L d : ℕ} (F : ReflectionFamily L d)
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (ideal native : Qatlib.Foundations.PureStateMath.DensityOperator 2)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (N : ℕ) :
    Matrix.traceNorm (storedSourceRun F q native rho N - storedSourceRun F p ideal rho N) ≤
      (N : ℝ) * (Matrix.traceNorm (native.val - ideal.val) +
        ∑ j : Fin L, |q.prob j - p.prob j|) := by
  induction N with
  | zero => simp [storedSourceRun]
  | succ N ih =>
    have hs := storedSourceStep_error F p q ideal native
      (storedSourceRun F q native rho N) (storedSourceRun_positive F q native rho N)
      (storedSourceRun_trace F q native rho N)
    have hc := Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction
      (storedSourceStep F p ideal N) (storedSourceStep_positive F p ideal N)
      (storedSourceStep_tracePreserving F p ideal N)
      ((storedSourceRun_positive F q native rho N).isHermitian.sub
        (storedSourceRun_positive F p ideal rho N).isHermitian)
    rw [map_sub] at hc
    have he : storedSourceRun F q native rho (N+1) - storedSourceRun F p ideal rho (N+1) =
      (storedSourceStep F q native N (storedSourceRun F q native rho N) -
        storedSourceStep F p ideal N (storedSourceRun F q native rho N)) +
      (storedSourceStep F p ideal N (storedSourceRun F q native rho N) -
        storedSourceStep F p ideal N (storedSourceRun F p ideal rho N)) := by
      simp only [storedSourceRun]; abel
    rw [he]
    have ht := (Matrix.traceNorm_add_le _ _).trans (add_le_add hs (hc.trans ih))
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using! ht

/-- If the native preparation is within trace norm `2 * epsilon` of `rotationState a` and the
index laws are within total variation `delta`, the two length-`N` stored runs are within
half trace norm `N * (epsilon + delta)`. -/
theorem storedSourceRun_native_budget {L d : ℕ} (F : ReflectionFamily L d)
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (native : Qatlib.Foundations.PureStateMath.DensityOperator 2)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (N : ℕ) (epsilon delta : ℝ)
    (hprep : Matrix.traceNorm (native.val - (rotationState a).val) ≤ 2 * epsilon)
    (hindex : (1/2 : ℝ) * (∑ j : Fin L, |q.prob j - p.prob j|) ≤ delta) :
    (1/2 : ℝ) * Matrix.traceNorm
      (storedSourceRun F q native rho N - storedSourceRun F p (rotationState a) rho N) ≤
        (N : ℝ) * (epsilon + delta) := by
  have h := storedSourceRun_error F p q (rotationState a) native rho N
  have hn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

/-- The tagged matrix has entry `A u v` when both index labels equal `j`, and has entry zero
otherwise. -/
private theorem tagIndex_apply {L d : ℕ} (j : Fin L)
    (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ)
    (u v : Fin d ⊕ Fin d) (k l : Fin L) :
    tagIndex L d j A (u,k) (v,l) = if k=j ∧ l=j then A u v else 0 := by
  by_cases hk : k=j <;> by_cases hl : l=j <;>
    simp [tagIndex, MatrixMap.conj, Matrix.mul_apply, indexEmbedding,
      Matrix.conjTranspose_apply, hk, hl]

/-- After flattening the live-history basis, the extended reflection has entry `F.sigma j i k`
when the two histories coincide and zero otherwise. -/
private theorem historySigma_apply {L d N : ℕ} (F : ReflectionFamily L d) (j : Fin L)
    (i k : Fin d) (w v : SourceHistory L N) :
    (withReferenceFamily F (Fintype.card (SourceHistory L N))).sigma j
      (historyInputEquiv L d N (i,w)) (historyInputEquiv L d N (k,v)) =
      if w=v then F.sigma j i k else 0 := by
  simp [withReferenceFamily, historyInputEquiv, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.kroneckerMap_apply,
    Matrix.one_apply]

/-- After flattening the live-history basis, the extended weak operator has the original
live-register entry when the histories coincide and zero otherwise. -/
private theorem historyWeak_apply {L d N : ℕ} (F : ReflectionFamily L d)
    (a : ℝ) (j : Fin L) (b : Bool) (i k : Fin d) (w v : SourceHistory L N) :
    weakOperator (withReferenceFamily F (Fintype.card (SourceHistory L N))) a j b
      (historyInputEquiv L d N (i,w)) (historyInputEquiv L d N (k,v)) =
      if w=v then weakOperator F a j b i k else 0 := by
  simp only [weakOperator, Matrix.add_apply, Matrix.smul_apply, historySigma_apply,
    Matrix.one_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Pulling the extended weak operator back to the live-history basis gives the Kronecker
product of the original weak operator with the identity on histories. -/
private theorem historyWeak_submatrix {L d N : ℕ} (F : ReflectionFamily L d)
    (a : ℝ) (j : Fin L) (b : Bool) :
    (weakOperator (withReferenceFamily F (Fintype.card (SourceHistory L N))) a j b).submatrix
      (historyInputEquiv L d N) (historyInputEquiv L d N) =
      Matrix.kronecker (weakOperator F a j b) (1 : Matrix (SourceHistory L N) (SourceHistory L N) ℂ) := by
  ext ⟨i,w⟩ ⟨k,v⟩
  simp only [Matrix.submatrix_apply, historyWeak_apply]
  split_ifs <;> simp_all

/-- Each pair of history blocks of an extended ideal-instrument branch is obtained by applying
the original ideal branch to the corresponding live-register block. -/
private theorem historyBranch_block {L d N : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (j : Fin L) (b : Bool)
    (A : Matrix (SourceRegister L d N) (SourceRegister L d N) ℂ)
    (i k : Fin d) (w v : SourceHistory L N) :
    (idealInstrument (withReferenceFamily F (Fintype.card (SourceHistory L N))) p a).branch (j,b)
      (basisReindex (historyInputEquiv L d N) A)
      (historyInputEquiv L d N (i,w)) (historyInputEquiv L d N (k,v)) =
      (idealInstrument F p a).branch (j,b) (fun x y => A (x,w) (y,v)) i k := by
  rw [idealInstrument_branch_weak, idealInstrument_branch_weak]
  simp only [Matrix.smul_apply, smul_eq_mul]
  congr 1
  have h : ((weakOperator (withReferenceFamily F (Fintype.card (SourceHistory L N))) a j b) *
      basisReindex (historyInputEquiv L d N) A *
      weakOperator (withReferenceFamily F (Fintype.card (SourceHistory L N))) a j b).submatrix
      (historyInputEquiv L d N) (historyInputEquiv L d N) =
    Matrix.kronecker (weakOperator F a j b) (1 : Matrix (SourceHistory L N) (SourceHistory L N) ℂ) *
      A * Matrix.kronecker (weakOperator F a j b) (1 : Matrix (SourceHistory L N) (SourceHistory L N) ℂ) := by
    rw [← Matrix.submatrix_mul_equiv _ _ _ (historyInputEquiv L d N),
      ← Matrix.submatrix_mul_equiv _ _ _ (historyInputEquiv L d N), historyWeak_submatrix]
    congr 2
    ext x y
    simp [basisReindex, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply]
  have he := congrFun (congrFun h (i,w)) (k,v)
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply] using! he

/-- The inverse output equivalence sends a history ending in `(j, b)` to the flattened previous
history in the ancilla block selected by `b`, tagged with `j`. -/
private theorem historyOutputEquiv_symm_snoc {L d N : ℕ}
    (i : Fin d) (w : SourceHistory L N) (j : Fin L) (b : Bool) :
    (historyOutputEquiv L d N).symm (i,Fin.snoc w (j,b)) =
      ((if b then Sum.inr (historyInputEquiv L d N (i,w)) else
        Sum.inl (historyInputEquiv L d N (i,w))),j) := by
  cases b <;> simp [historyOutputEquiv, ancillaSumEquiv,
      Qatlib.Foundations.PureStateMath.boolEquivFin2]

/-- For a positive semidefinite trace-one input and preparation `rotationState a`, a stored-step
entry between appended histories vanishes unless their new outcomes agree; when they agree
it is the corresponding ideal branch applied to the previous history block. -/
private theorem storedSourceStep_ideal_apply {L d N : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ)
    (A : Matrix (SourceRegister L d N) (SourceRegister L d N) ℂ)
    (hA : A.PosSemidef) (htr : Matrix.trace A = 1)
    (i k : Fin d) (w v : SourceHistory L N) (j l : Fin L) (b c : Bool) :
    storedSourceStep F p (rotationState a) N A
      (i,Fin.snoc w (j,b)) (k,Fin.snoc v (l,c)) =
      if (j,b)=(l,c) then
        (idealInstrument F p a).branch (j,b) (fun x y => A (x,w) (y,v)) i k else 0 := by
  let sigma : Qatlib.Foundations.PureStateMath.DensityOperator (d * Fintype.card (SourceHistory L N)) :=
    ⟨basisReindex (historyInputEquiv L d N) A, basisReindex_positive _ hA,
      (basisReindex_tracePreserving _ A).trans htr⟩
  change basisReindex (historyOutputEquiv L d N)
    (preparedSourceChannel (withReferenceFamily F _) p (rotationState a) sigma.val) _ _ = _
  rw [preparedSourceChannel_eq_joint, jointPreparedReadout_ideal]
  change idealJointReadoutMatrix (withReferenceFamily F _) p a sigma
    ((historyOutputEquiv L d N).symm (i,Fin.snoc w (j,b)))
    ((historyOutputEquiv L d N).symm (k,Fin.snoc v (l,c))) = _
  rw [historyOutputEquiv_symm_snoc, historyOutputEquiv_symm_snoc]
  simp only [idealJointReadoutMatrix, Matrix.sum_apply, tagIndex_apply]
  by_cases hj : j=l
  · subst l
    cases b <;> cases c <;>
      simp [-idealInstrument_branch, Matrix.fromBlocks, historyBranch_block, sigma]
  · have hjl (x : Fin L) : ¬(j=x ∧ l=x) := by
      rintro ⟨rfl,rfl⟩
      exact hj rfl
    simp [hjl, hj]

/-- The block diagonal live-history matrix whose block at history `w` is the unnormalized output
of the length-`N` path instrument on `rho`. -/
def pathSourceMatrix {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (a : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (N : ℕ) :
    Matrix (SourceRegister L d N) (SourceRegister L d N) ℂ :=
  Matrix.blockDiagonal (fun w => (pathInstrument F p a N).branch w rho.val)

/-- With the exact rotation preparation, the entire stored source run equals the block diagonal
matrix of ideal path-instrument outputs. -/
theorem storedSourceRun_ideal {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (N : ℕ) :
    storedSourceRun F p (rotationState a) rho N = pathSourceMatrix F p a rho N := by
  induction N with
  | zero =>
    ext ⟨i,w⟩ ⟨k,v⟩
    have hw : w=v := Subsingleton.elim _ _
    simp [storedSourceRun, basisReindex, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply,
      emptyHistoryEquiv, pathSourceMatrix, Matrix.blockDiagonal_apply, pathInstrument_branch,
      pathKraus, hw]
  | succ N ih =>
    ext ⟨i,w'⟩ ⟨k,v'⟩
    obtain ⟨⟨o,w⟩, hw'⟩ := (Fin.snocEquiv (fun _ : Fin (N+1) => Fin L × Bool)).surjective w'
    obtain ⟨⟨o',v⟩, hv'⟩ := (Fin.snocEquiv (fun _ : Fin (N+1) => Fin L × Bool)).surjective v'
    change Fin.snoc w o = w' at hw'
    change Fin.snoc v o' = v' at hv'
    subst w'
    subst v'
    rcases o with ⟨j,b⟩
    rcases o' with ⟨l,c⟩
    rw [storedSourceRun, storedSourceStep_ideal_apply F p a _
      (storedSourceRun_positive F p (rotationState a) rho N)
      (storedSourceRun_trace F p (rotationState a) rho N), ih]
    by_cases hw : w=v <;> by_cases ho : (j,b)=(l,c)
    · subst v
      cases ho
      simp [-pathInstrument_branch, -idealInstrument_branch, pathSourceMatrix,
        Matrix.blockDiagonal_apply, pathInstrument_branch_snoc]
    · simp [ho, pathSourceMatrix, Matrix.blockDiagonal_apply, Fin.snoc_inj]
    · have hzero : (fun x y => pathSourceMatrix F p a rho N (x,w) (y,v)) = (0 : Qatlib.Foundations.PureStateMath.Operator d) := by
        ext x y
        simp [pathSourceMatrix, Matrix.blockDiagonal_apply, hw]
      rw [hzero]
      simp [pathSourceMatrix, Matrix.blockDiagonal_apply, hw, Fin.snoc_inj]
    · simp [ho, pathSourceMatrix, Matrix.blockDiagonal_apply, Fin.snoc_inj]

/-- The Kraus matrix that selects a fixed history `w`, preserves the live basis index, and
replaces that history by its report value. -/
def historyReportKraus {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (report : SourceHistory L N → R) (w : SourceHistory L N) :
    Matrix (Fin d × R) (SourceRegister L d N) ℂ :=
  fun x y => if x.1=y.1 ∧ x.2=report w ∧ y.2=w then 1 else 0

/-- The adjoint product of a history-report Kraus matrix is the projector onto the history-`w`
subspace. -/
private theorem historyReportKraus_product {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (report : SourceHistory L N → R) (w u v : SourceHistory L N) (i k : Fin d) :
    ((historyReportKraus (d := d) report w)ᴴ * historyReportKraus (d := d) report w) (i,u) (k,v) =
      if u=w ∧ v=w then (1 : Qatlib.Foundations.PureStateMath.Operator d) i k else 0 := by
  by_cases hu : u=w <;> by_cases hv : v=w <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      historyReportKraus, hu, hv, Matrix.one_apply, ite_and, eq_comm]

set_option maxHeartbeats 800000 in

/-- Conjugation by the Kraus matrix for `w` places the diagonal history block `A (i, w) (k, w)`
in the report block `report w` and gives zero in other report blocks. -/
private theorem historyReportKraus_conj {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (report : SourceHistory L N → R) (w : SourceHistory L N)
    (A : Matrix (SourceRegister L d N) (SourceRegister L d N) ℂ)
    (i k : Fin d) (r s : R) :
    (historyReportKraus (d := d) report w * A * (historyReportKraus (d := d) report w)ᴴ) (i,r) (k,s) =
      if r=report w ∧ s=report w then A (i,w) (k,w) else 0 := by
  by_cases hr : r=report w <;> by_cases hs : s=report w <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      historyReportKraus, hr, hs, ite_and, apply_ite]

/-- The adjoint products of the reporting Kraus matrices sum to the identity over all histories. -/
private theorem historyReportKraus_complete {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (report : SourceHistory L N → R) :
    ∑ w, (historyReportKraus (d := d) report w)ᴴ * historyReportKraus (d := d) report w =
      (1 : Matrix (SourceRegister L d N) (SourceRegister L d N) ℂ) := by
  ext ⟨i,u⟩ ⟨k,v⟩
  rw [Matrix.sum_apply]
  simp_rw [historyReportKraus_product]
  by_cases huv : u=v
  · subst v
    simp [Matrix.one_apply]
  · have h (w : SourceHistory L N) : ¬(u=w ∧ v=w) := by
      rintro ⟨rfl,rfl⟩
      exact huv rfl
    simp [h, huv]

/-- The Kraus channel that reads the stored history, replaces it by `report w`, and retains the
live register. -/
def historyReport {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (report : SourceHistory L N → R) : MatrixMap (SourceRegister L d N) (Fin d × R) ℂ :=
  MatrixMap.of_kraus (historyReportKraus (d := d) report) (historyReportKraus (d := d) report)

/-- The history-report channel preserves positive semidefiniteness. -/
theorem historyReport_positive {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (report : SourceHistory L N → R) : (historyReport (d := d) report).IsPositive :=
  MatrixMap.of_kraus_isPositive _

/-- The history-report channel preserves the matrix trace. -/
theorem historyReport_tracePreserving {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (report : SourceHistory L N → R) : (historyReport (d := d) report).IsTracePreserving :=
  MatrixMap.IsTracePreserving.of_kraus_isTracePreserving _ _ (historyReportKraus_complete report)

/-- Reporting an ideal path-source matrix gives a block diagonal matrix whose report block is
the sum of path-instrument outputs over histories with that report value. -/
theorem historyReport_pathSource {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d)
    (report : SourceHistory L N → R) :
    historyReport report (pathSourceMatrix F p a rho N) =
      Matrix.blockDiagonal (fun r => ∑ w : SourceHistory L N,
        if report w=r then (pathInstrument F p a N).branch w rho.val else 0) := by
  ext ⟨i,r⟩ ⟨k,s⟩
  simp only [historyReport, MatrixMap.of_kraus_eq_sum_conj, LinearMap.sum_apply,
    MatrixMap.conj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    historyReportKraus_conj, pathSourceMatrix, Matrix.blockDiagonal_apply_eq]
  by_cases hrs : r=s
  · subst s
    simp only [and_self, Matrix.blockDiagonal_apply_eq, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : r=report w <;> simp [hw, eq_comm]
  · have h (w : SourceHistory L N) : ¬(r=report w ∧ s=report w) := by
      rintro ⟨rfl,rfl⟩
      exact hrs rfl
    simp [h, Matrix.blockDiagonal_apply, hrs]

/-- If the preparation trace norm error is at most `2 * epsilon` and the index total variation
error is at most `delta`, applying any finite history report leaves the native length-`N`
run within half trace norm `N * (epsilon + delta)` of the reported ideal path-source matrix. -/
theorem storedSourceRun_report_budget {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (F : ReflectionFamily L d) (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (native : Qatlib.Foundations.PureStateMath.DensityOperator 2)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (report : SourceHistory L N → R) (epsilon delta : ℝ)
    (hprep : Matrix.traceNorm (native.val - (rotationState a).val) ≤ 2 * epsilon)
    (hindex : (1/2 : ℝ) * (∑ j : Fin L, |q.prob j - p.prob j|) ≤ delta) :
    (1/2 : ℝ) * Matrix.traceNorm
      (historyReport report (storedSourceRun F q native rho N) -
        historyReport report (pathSourceMatrix F p a rho N)) ≤
      (N : ℝ) * (epsilon+delta) := by
  have h := storedSourceRun_native_budget F p q a native rho N epsilon delta hprep hindex
  have hc := Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction (historyReport report)
    (historyReport_positive report) (historyReport_tracePreserving report)
    ((storedSourceRun_positive F q native rho N).isHermitian.sub
      (storedSourceRun_positive F p (rotationState a) rho N).isHermitian)
  rw [storedSourceRun_ideal, map_sub] at hc
  exact (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 1/2)).trans (by
    simpa only [storedSourceRun_ideal] using! h)

/-- For the legal `thermalActualOAAWord`, assume the nonnegative differences of the target
cosine and sine from the dyadic coefficients are at most `e`, with `6 * e^2 <= epsilon^2`
and nonnegative `a` and `epsilon`. If the index-law total variation error is at most
`delta`, its preparation yields a reported length-`N` source run within half trace norm `N *
(epsilon + delta)` of the reported ideal path-source matrix. -/
theorem thermalActualOAA_history_report_budget {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (F : ReflectionFamily L d) (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d)
    (report : SourceHistory L N → R) (b w w0 w1 pad : ℕ) (hcap : b≤w+2)
    (htotal : w0+w1+pad+pad=2^b) (a e epsilon delta : ℝ) (ha : 0≤a)
    (hc : 0≤directCos a-thermalDyadicCoefficient b w0)
    (hs : 0≤directSin a-thermalDyadicCoefficient b w1)
    (hcE : directCos a-thermalDyadicCoefficient b w0≤e)
    (hsE : directSin a-thermalDyadicCoefficient b w1≤e)
    (heps : 6*e^2≤epsilon^2) (heps0 : 0≤epsilon)
    (hindex : (1/2:ℝ)*(∑ j : Fin L,|q.prob j-p.prob j|)≤delta) :
    (1/2:ℝ)*Matrix.traceNorm
      (historyReport report (storedSourceRun F q
        (wordPreparationState ((b+1)+w) (thermalActualOAAWord b w w0 w1 pad)
          (thermalActualOAA_legal b w w0 w1 pad hcap htotal)) rho N) -
        historyReport report (pathSourceMatrix F p a rho N)) ≤ (N:ℝ)*(epsilon+delta) :=
  storedSourceRun_report_budget F p q a _ rho report epsilon delta
    (wordPreparation_error _ _ _ a epsilon heps0
      (thermalActualOAA_hclean b w w0 w1 pad hcap htotal a e epsilon ha hc hs hcE hsE heps)) hindex

/-- The principal live-register block of a matrix obtained by fixing both record indices to `r`. -/
def recordDensityBlock {d : ℕ} {R : Type} [Fintype R]
    (A : Matrix (Fin d × R) (Fin d × R) ℂ) (r : R) : Qatlib.Foundations.PureStateMath.Operator d :=
  A.submatrix (fun i => (i,r)) (fun i => (i,r))

/-- Every principal record block of a positive semidefinite live-record matrix is positive
semidefinite. -/
private theorem recordDensityBlock_pos {d : ℕ} {R : Type} [Fintype R]
    (A : Matrix (Fin d × R) (Fin d × R) ℂ) (hA : A.PosSemidef) (r : R) :
    (recordDensityBlock A r).PosSemidef := hA.submatrix _

/-- The probability distribution on records obtained from the real traces of the principal
record blocks of a positive semidefinite trace-one matrix. -/
def recordDensityLaw {d : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (A : Matrix (Fin d × R) (Fin d × R) ℂ) (hA : A.PosSemidef) (htr : Matrix.trace A=1) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist R where
  prob r := (Matrix.trace (recordDensityBlock A r)).re
  nonneg r := (RCLike.nonneg_iff.mp (recordDensityBlock_pos A hA r).trace_nonneg).1
  sum_one := by
    have he : (∑ r, Matrix.trace (recordDensityBlock A r))=Matrix.trace A := by
      simp only [recordDensityBlock, Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply,
        Fintype.sum_prod_type]
      rw [Finset.sum_comm]
    rw [← Complex.re_sum, he, htr, Complex.one_re]

/-- The complex trace of a principal record block equals the real record probability embedded
into the complex numbers. -/
private theorem recordDensityBlock_trace {d : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (A : Matrix (Fin d × R) (Fin d × R) ℂ) (hA : A.PosSemidef) (htr : Matrix.trace A=1) (r : R) :
    Matrix.trace (recordDensityBlock A r)=((recordDensityLaw A hA htr).prob r : ℂ) := by
  have hi := (RCLike.nonneg_iff.mp (recordDensityBlock_pos A hA r).trace_nonneg).2
  apply Complex.ext
  · rfl
  · simpa using! hi

/-- The conditional live density operator at record `r`, formed by dividing its block by its
positive probability and using the supplied reference density operator when that probability
is zero. -/
def recordDensityState {d : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (A : Matrix (Fin d × R) (Fin d × R) ℂ) (hA : A.PosSemidef) (htr : Matrix.trace A=1)
    (reference : R → Qatlib.Foundations.PureStateMath.DensityOperator d) (r : R) : Qatlib.Foundations.PureStateMath.DensityOperator d := by
  classical
  by_cases hz : (recordDensityLaw A hA htr).prob r=0
  · exact reference r
  · refine ⟨((((recordDensityLaw A hA htr).prob r)⁻¹ : ℝ) : ℂ) • recordDensityBlock A r, ?_, ?_⟩
    · exact (recordDensityBlock_pos A hA r).smul
        (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr ((recordDensityLaw A hA htr).nonneg r)))
    · rw [Matrix.trace_smul, recordDensityBlock_trace A hA htr r, smul_eq_mul]
      exact_mod_cast inv_mul_cancel₀ hz

/-- Multiplying the conditional density operator at a record by its record probability recovers
that record's principal block, including the zero-probability case. -/
theorem recordDensityState_block {d : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (A : Matrix (Fin d × R) (Fin d × R) ℂ) (hA : A.PosSemidef) (htr : Matrix.trace A=1)
    (reference : R → Qatlib.Foundations.PureStateMath.DensityOperator d) (r : R) :
    ((recordDensityLaw A hA htr).prob r : ℂ) • (recordDensityState A hA htr reference r).val=
      recordDensityBlock A r := by
  classical
  by_cases hz : (recordDensityLaw A hA htr).prob r=0
  · rw [hz, Complex.ofReal_zero, zero_smul]
    symm
    apply (Matrix.PosSemidef.trace_eq_zero_iff (recordDensityBlock_pos A hA r)).mp
    rw [recordDensityBlock_trace A hA htr r, hz, Complex.ofReal_zero]
  · simp only [recordDensityState, hz, dite_false, smul_smul]
    have hc : ((recordDensityLaw A hA htr).prob r : ℂ) *
        ((((recordDensityLaw A hA htr).prob r)⁻¹ : ℝ) : ℂ)=1 := by
      exact_mod_cast mul_inv_cancel₀ hz
    rw [hc, one_smul]

/-- The block diagonal matrix formed from record probabilities times conditional density
operators equals the block diagonal matrix of the original principal record blocks. -/
theorem recordDensity_reassemble {d : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (A : Matrix (Fin d × R) (Fin d × R) ℂ) (hA : A.PosSemidef) (htr : Matrix.trace A=1)
    (reference : R → Qatlib.Foundations.PureStateMath.DensityOperator d) :
    Matrix.blockDiagonal (fun r => ((recordDensityLaw A hA htr).prob r : ℂ) •
      (recordDensityState A hA htr reference r).val) =
      Matrix.blockDiagonal (fun r => recordDensityBlock A r) := by
  congr 1
  funext r
  exact recordDensityState_block A hA htr reference r

/-- Every output of the history-report channel is block diagonal in its report register and is
recovered by assembling its principal report blocks. -/
theorem historyReport_blockDiagonal {L d N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (report : SourceHistory L N → R)
    (A : Matrix (SourceRegister L d N) (SourceRegister L d N) ℂ) :
    Matrix.blockDiagonal (fun r => recordDensityBlock (historyReport report A) r) =
      historyReport report A := by
  ext ⟨i,r⟩ ⟨k,s⟩
  rw [Matrix.blockDiagonal_apply]
  by_cases hrs : r=s
  · subst s
    simp [recordDensityBlock]
  · simp only [hrs, if_false]
    symm
    simp only [historyReport, MatrixMap.of_kraus_eq_sum_conj, LinearMap.sum_apply,
      MatrixMap.conj, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply, historyReportKraus_conj]
    have h (w : SourceHistory L N) : ¬(r=report w ∧ s=report w) := by
      rintro ⟨rfl,rfl⟩
      exact hrs rfl
    simp [h]

end Qatlib.Papers.ThermalDrift26.ThermalSampling
