/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.DirectThermalSourceCircuit
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Concepts.GibbsMetropolis.RationalBath.ApproximateRationalGibbs
import Mathlib.Tactic.FinCases
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix
open scoped BigOperators ComplexOrder

def ancillaSumEquiv (d : ℕ) : (Fin 2 × Fin d) ≃ (Fin d ⊕ Fin d) where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun x := match x with | Sum.inl i => (0,i) | Sum.inr i => (1,i)
  left_inv := by rintro ⟨b,i⟩; fin_cases b <;> rfl
  right_inv := by intro x; cases x <;> rfl

def appendLiveState {d : ℕ} (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : MatrixMap (Fin 2) (Fin d ⊕ Fin d) ℂ where
  toFun eta := Matrix.reindex (ancillaSumEquiv d) (ancillaSumEquiv d) (Matrix.kronecker eta rho.val)
  map_add' := by
    intro A B
    ext i k
    simp [Matrix.reindex_apply, add_mul]
  map_smul' := by
    intro z A
    ext i k
    simp [Matrix.reindex_apply, mul_assoc]

theorem appendLiveState_positive {d : ℕ} (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : (appendLiveState rho).IsPositive := by
  intro A hA
  change ((Matrix.kronecker A rho.val).submatrix (ancillaSumEquiv d).symm (ancillaSumEquiv d).symm).PosSemidef
  exact (hA.PosSemidef_kronecker rho.property.1).submatrix _

theorem appendLiveState_tracePreserving {d : ℕ} (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    (appendLiveState rho).IsTracePreserving := by
  intro A
  change Matrix.trace ((Matrix.kronecker A rho.val).submatrix
    (ancillaSumEquiv d).symm (ancillaSumEquiv d).symm) = _
  rw [Qatlib.Concepts.PauliClifford.ExactRank.tensorPauliTrace_submatrix]
  calc
    _ = Matrix.trace A * Matrix.trace rho.val := Matrix.trace_kronecker A rho.val
    _ = _ := by rw [rho.property.2, mul_one]

theorem appendLiveState_error {d : ℕ} (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (ideal native : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    Matrix.traceNorm (appendLiveState rho native.val - appendLiveState rho ideal.val) ≤
      Matrix.traceNorm (native.val - ideal.val) := by
  rw [← map_sub]
  exact Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction _
    (appendLiveState_positive rho) (appendLiveState_tracePreserving rho)
    (native.property.1.isHermitian.sub ideal.property.1.isHermitian)

def controlledReadoutUnitary {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  ancillaHadamard d * controlledReflection F j

private theorem controlledReadoutUnitary_isometry {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    (controlledReadoutUnitary F j).Isometry := by
  have hH : (ancillaHadamard d)ᴴ * ancillaHadamard d = 1 := ancillaHadamard_isometry d
  have hC : (controlledReflection F j)ᴴ * controlledReflection F j = 1 :=
      controlledReflection_isometry F j
  change (controlledReadoutUnitary F j)ᴴ * controlledReadoutUnitary F j = 1
  unfold controlledReadoutUnitary
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (controlledReflection F j)ᴴ * ((ancillaHadamard d)ᴴ * ancillaHadamard d) *
      controlledReflection F j := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hH, Matrix.mul_one, hC]

def ancillaProjector (d : ℕ) (b : Bool) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  if b then Matrix.fromBlocks 0 0 0 (1 : Qatlib.Foundations.PureStateMath.Operator d) else Matrix.fromBlocks (1 : Qatlib.Foundations.PureStateMath.Operator d) 0 0 0

def directReadoutKraus {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) (b : Bool) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  ancillaProjector d b * controlledReadoutUnitary F j

private theorem ancillaProjector_complete (d : ℕ) :
    (ancillaProjector d true)ᴴ * ancillaProjector d true +
      (ancillaProjector d false)ᴴ * ancillaProjector d false = 1 := by
  simp only [ancillaProjector, Bool.false_eq_true, reduceIte, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero]
  rw [Matrix.fromBlocks_add]
  simp only [zero_add, add_zero, Matrix.fromBlocks_one]

theorem directReadoutKraus_complete {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    ∑ b : Bool, (directReadoutKraus F j b)ᴴ * directReadoutKraus F j b = 1 := by
  rw [Fintype.sum_bool]
  simp only [directReadoutKraus, Matrix.conjTranspose_mul]
  calc
    _ = (controlledReadoutUnitary F j)ᴴ *
      ((ancillaProjector d true)ᴴ * ancillaProjector d true +
        (ancillaProjector d false)ᴴ * ancillaProjector d false) * controlledReadoutUnitary F j := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 1 := by
      rw [ancillaProjector_complete, Matrix.mul_one]
      exact controlledReadoutUnitary_isometry F j

def directReadoutMap {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    MatrixMap (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  MatrixMap.of_kraus (directReadoutKraus F j) (directReadoutKraus F j)

theorem directReadoutMap_positive {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    (directReadoutMap F j).IsPositive := MatrixMap.of_kraus_isPositive _

theorem directReadoutMap_tracePreserving {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L) :
    (directReadoutMap F j).IsTracePreserving :=
  MatrixMap.IsTracePreserving.of_kraus_isTracePreserving _ _ (directReadoutKraus_complete F j)

theorem directReadout_preparation_error {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (ideal native : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    Matrix.traceNorm (directReadoutMap F j (appendLiveState rho native.val) -
      directReadoutMap F j (appendLiveState rho ideal.val)) ≤
        Matrix.traceNorm (native.val - ideal.val) := by
  have hX : (appendLiveState rho native.val - appendLiveState rho ideal.val).IsHermitian :=
    (appendLiveState_positive rho native.property.1).isHermitian.sub
      (appendLiveState_positive rho ideal.property.1).isHermitian
  calc
    _ = Matrix.traceNorm (directReadoutMap F j
        (appendLiveState rho native.val - appendLiveState rho ideal.val)) := by rw [map_sub]
    _ ≤ Matrix.traceNorm (appendLiveState rho native.val - appendLiveState rho ideal.val) :=
      Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction _
        (directReadoutMap_positive F j) (directReadoutMap_tracePreserving F j) hX
    _ ≤ _ := appendLiveState_error rho ideal native

def preparedReadout {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (eta : Qatlib.Foundations.PureStateMath.Operator 2) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  directReadoutMap F j (appendLiveState rho eta)

theorem preparedReadout_postprocess_error {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (ideal native : Qatlib.Foundations.PureStateMath.DensityOperator 2)
    {J : Type} [Fintype J] [DecidableEq J]
    (post : MatrixMap (Fin d ⊕ Fin d) J ℂ) (hpos : post.IsPositive) (htp : post.IsTracePreserving) :
    Matrix.traceNorm (post (preparedReadout F j rho native.val) -
      post (preparedReadout F j rho ideal.val)) ≤ Matrix.traceNorm (native.val - ideal.val) := by
  have hn : (preparedReadout F j rho native.val).PosSemidef :=
    directReadoutMap_positive F j (appendLiveState_positive rho native.property.1)
  have hi : (preparedReadout F j rho ideal.val).PosSemidef :=
    directReadoutMap_positive F j (appendLiveState_positive rho ideal.property.1)
  calc
    _ = Matrix.traceNorm (post (preparedReadout F j rho native.val - preparedReadout F j rho ideal.val)) :=
      by rw [map_sub]
    _ ≤ Matrix.traceNorm (preparedReadout F j rho native.val - preparedReadout F j rho ideal.val) :=
      Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction post hpos htp (hn.isHermitian.sub hi.isHermitian)
    _ ≤ _ := directReadout_preparation_error F j rho ideal native

def rotationVector (a : ℝ) : Qatlib.Foundations.PureStateMath.QState (Fin 2) :=
    ![(directCos a : ℂ), (directSin a : ℂ)]

private theorem rotationVector_normalized (a : ℝ) : Qatlib.Foundations.PureStateMath.Normalized (rotationVector a) := by
  simp [Qatlib.Foundations.PureStateMath.Normalized, rotationVector, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, direct_rotation_normalized]

def rotationState (a : ℝ) : Qatlib.Foundations.PureStateMath.DensityOperator 2 :=
  ⟨Qatlib.Foundations.PureStateMath.Reflection.outerProduct (rotationVector a), Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density (rotationVector_normalized a)⟩

private theorem appendLiveState_blocks {d : ℕ} (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (eta : Qatlib.Foundations.PureStateMath.Operator 2) :
    appendLiveState rho eta = Matrix.fromBlocks
      (eta 0 0 • rho.val) (eta 0 1 • rho.val) (eta 1 0 • rho.val) (eta 1 1 • rho.val) := by
  ext i k
  cases i <;> cases k <;>
    simp [appendLiveState, Matrix.reindex_apply, ancillaSumEquiv, Matrix.fromBlocks, smul_eq_mul]

private theorem prepared_rotation_blocks {d : ℕ} (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (a : ℝ) :
    appendLiveState rho (rotationState a).val =
      ancillaRotation d (directCos a) (directSin a) * Matrix.fromBlocks rho.val 0 0 0 *
        (ancillaRotation d (directCos a) (directSin a))ᴴ := by
  rw [appendLiveState_blocks]
  simp only [ancillaRotation, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, map_neg,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.one_mul,
    Matrix.mul_one, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ext i k
  cases i <;> cases k <;>
    simp [rotationState, rotationVector, Qatlib.Foundations.PureStateMath.Reflection.outerProduct, Matrix.fromBlocks, Matrix.smul_apply,
      smul_eq_mul, mul_assoc]
  all_goals ring

private theorem pinching_blocks {d : ℕ} (X : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) :
    (∑ b : Bool, ancillaProjector d b * X * (ancillaProjector d b)ᴴ) =
      Matrix.fromBlocks (Matrix.toBlocks₁₁ X) 0 0 (Matrix.toBlocks₂₂ X) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X]
  simp [ancillaProjector, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_add]

theorem directReadoutMap_eq {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L)
    (X : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) :
    directReadoutMap F j X = Matrix.fromBlocks
      (Matrix.toBlocks₁₁ (controlledReadoutUnitary F j * X * (controlledReadoutUnitary F j)ᴴ)) 0 0
      (Matrix.toBlocks₂₂ (controlledReadoutUnitary F j * X * (controlledReadoutUnitary F j)ᴴ)) := by
  rw [← pinching_blocks]
  simp only [directReadoutMap, MatrixMap.of_kraus_eq_sum_conj, LinearMap.sum_apply,
    MatrixMap.conj, LinearMap.coe_mk, AddHom.coe_mk, directReadoutKraus, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.mul_assoc]

theorem preparedReadout_ideal {L d : ℕ} (F : ReflectionFamily L d) (j : Fin L)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (a : ℝ) :
    preparedReadout F j rho (rotationState a).val = Matrix.fromBlocks
      (directBranch F (directCos a) (directSin a) j false * rho.val *
        (directBranch F (directCos a) (directSin a) j false)ᴴ) 0 0
      (directBranch F (directCos a) (directSin a) j true * rho.val *
        (directBranch F (directCos a) (directSin a) j true)ᴴ) := by
  unfold preparedReadout
  rw [directReadoutMap_eq, prepared_rotation_blocks]
  have he : controlledReadoutUnitary F j *
      (ancillaRotation d (directCos a) (directSin a) * Matrix.fromBlocks rho.val 0 0 0 *
        (ancillaRotation d (directCos a) (directSin a))ᴴ) * (controlledReadoutUnitary F j)ᴴ =
      directCircuit F (directCos a) (directSin a) j * Matrix.fromBlocks rho.val 0 0 0 *
        (directCircuit F (directCos a) (directSin a) j)ᴴ := by
    simp only [directCircuit, controlledReadoutUnitary, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (directCircuit F (directCos a) (directSin a) j)]
  simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₂₂]
  rfl

def indexEmbedding (L d : ℕ) (j : Fin L) :
    Matrix ((Fin d ⊕ Fin d) × Fin L) (Fin d ⊕ Fin d) ℂ := fun x y => if x = (y,j) then 1 else 0

private theorem indexEmbedding_isometry (L d : ℕ) (j : Fin L) : (indexEmbedding L d j).Isometry := by
  ext a b
  simp [indexEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

def tagIndex (L d : ℕ) (j : Fin L) : MatrixMap (Fin d ⊕ Fin d) ((Fin d ⊕ Fin d) × Fin L) ℂ :=
  MatrixMap.conj (indexEmbedding L d j)

private theorem tagIndex_positive (L d : ℕ) (j : Fin L) : (tagIndex L d j).IsPositive := by
  intro A hA
  exact hA.mul_mul_conjTranspose_same _

private theorem tagIndex_tracePreserving (L d : ℕ) (j : Fin L) : (tagIndex L d j).IsTracePreserving := by
  intro A
  change Matrix.trace (indexEmbedding L d j * A * (indexEmbedding L d j)ᴴ) = _
  rw [Matrix.trace_mul_comm (indexEmbedding L d j * A), ← Matrix.mul_assoc,
    indexEmbedding_isometry L d j, Matrix.one_mul]

def jointPreparedReadout {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : MatrixMap (Fin 2) ((Fin d ⊕ Fin d) × Fin L) ℂ :=
  ∑ j : Fin L, (p.prob j : ℂ) •
    ((tagIndex L d j).comp ((directReadoutMap F j).comp (appendLiveState rho)))

theorem jointPreparedReadout_positive {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : (jointPreparedReadout F p rho).IsPositive := by
  intro A hA
  simp only [jointPreparedReadout, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply]
  apply Matrix.posSemidef_sum
  intro j _
  apply Matrix.PosSemidef.smul
  · exact tagIndex_positive L d j (directReadoutMap_positive F j (appendLiveState_positive rho hA))
  · exact_mod_cast p.nonneg j

theorem jointPreparedReadout_tracePreserving {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : (jointPreparedReadout F p rho).IsTracePreserving := by
  intro A
  have ht (j : Fin L) : Matrix.trace
      (tagIndex L d j (directReadoutMap F j (appendLiveState rho A))) = Matrix.trace A :=
    (tagIndex_tracePreserving L d j _).trans
      ((directReadoutMap_tracePreserving F j _).trans (appendLiveState_tracePreserving rho A))
  simp only [jointPreparedReadout, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp_rw [ht]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, p.sum_one, Complex.ofReal_one, one_mul]

theorem jointPreparedReadout_error {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (ideal native : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    Matrix.traceNorm (jointPreparedReadout F p rho native.val - jointPreparedReadout F p rho ideal.val) ≤
      Matrix.traceNorm (native.val - ideal.val) := by
  rw [← map_sub]
  exact Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction _
    (jointPreparedReadout_positive F p rho) (jointPreparedReadout_tracePreserving F p rho)
    (native.property.1.isHermitian.sub ideal.property.1.isHermitian)

def indexState {L : ℕ} (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) : Qatlib.Foundations.PureStateMath.DensityOperator L :=
  ⟨Matrix.diagonal (fun j => (p.prob j : ℂ)), by
    constructor
    · rw [Matrix.posSemidef_diagonal_iff]
      intro j
      exact_mod_cast p.nonneg j
    · rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, p.sum_one, Complex.ofReal_one]⟩

def indexControlledReadout {L d : ℕ} (F : ReflectionFamily L d)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    MatrixMap (Fin L) ((Fin d ⊕ Fin d) × Fin L) ℂ where
  toFun A := ∑ j : Fin L, A j j • tagIndex L d j (preparedReadout F j rho eta.val)
  map_add' := by intro A B; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro z A; simp [Finset.smul_sum, smul_smul]

theorem indexControlledReadout_positive {L d : ℕ} (F : ReflectionFamily L d)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) : (indexControlledReadout F rho eta).IsPositive := by
  intro A hA
  apply Matrix.posSemidef_sum
  intro j _
  apply Matrix.PosSemidef.smul
  · exact tagIndex_positive L d j
      (directReadoutMap_positive F j (appendLiveState_positive rho eta.property.1))
  · exact hA.diag_nonneg

theorem indexControlledReadout_tracePreserving {L d : ℕ} (F : ReflectionFamily L d)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    (indexControlledReadout F rho eta).IsTracePreserving := by
  intro A
  have ht (j : Fin L) : Matrix.trace (tagIndex L d j (preparedReadout F j rho eta.val)) = 1 :=
    (tagIndex_tracePreserving L d j _).trans
      ((directReadoutMap_tracePreserving F j _).trans
        ((appendLiveState_tracePreserving rho eta.val).trans eta.property.2))
  simp only [indexControlledReadout, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul]
  simp_rw [ht, mul_one]
  rfl

theorem jointPreparedReadout_indexState {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    jointPreparedReadout F p rho eta.val = indexControlledReadout F rho eta (indexState p).val := by
  simp only [jointPreparedReadout, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    indexControlledReadout, LinearMap.coe_mk, AddHom.coe_mk, indexState, Matrix.diagonal_apply_eq, preparedReadout]

theorem indexState_error {L : ℕ} (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) :
    Matrix.traceNorm ((indexState q).val - (indexState p).val) =
      ∑ j : Fin L, |q.prob j - p.prob j| := by
  have he : (indexState q).val - (indexState p).val =
      Matrix.diagonal (fun j => ((q.prob j - p.prob j : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [indexState]
    · simp [indexState, h]
  rw [he, Qatlib.Concepts.GibbsMetropolis.RationalBath.real_diagonal_traceNorm]

theorem jointPreparedReadout_index_error {L d : ℕ} (F : ReflectionFamily L d)
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (eta : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    Matrix.traceNorm (jointPreparedReadout F q rho eta.val - jointPreparedReadout F p rho eta.val) ≤
      ∑ j : Fin L, |q.prob j - p.prob j| := by
  rw [jointPreparedReadout_indexState, jointPreparedReadout_indexState, ← map_sub]
  exact (Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction _
    (indexControlledReadout_positive F rho eta) (indexControlledReadout_tracePreserving F rho eta)
    ((indexState q).property.1.isHermitian.sub (indexState p).property.1.isHermitian)).trans_eq (indexState_error p q)

theorem jointPreparedReadout_total_error {L d : ℕ} (F : ReflectionFamily L d)
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (ideal native : Qatlib.Foundations.PureStateMath.DensityOperator 2) :
    Matrix.traceNorm (jointPreparedReadout F q rho native.val - jointPreparedReadout F p rho ideal.val) ≤
      Matrix.traceNorm (native.val - ideal.val) + ∑ j : Fin L, |q.prob j - p.prob j| := by
  have he : jointPreparedReadout F q rho native.val - jointPreparedReadout F p rho ideal.val =
      (jointPreparedReadout F q rho native.val - jointPreparedReadout F q rho ideal.val) +
        (jointPreparedReadout F q rho ideal.val - jointPreparedReadout F p rho ideal.val) := by abel
  rw [he]
  exact (Matrix.traceNorm_add_le _ _).trans (add_le_add
    (jointPreparedReadout_error F q rho ideal native) (jointPreparedReadout_index_error F p q rho ideal))

def idealJointReadoutMatrix {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (a : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    Matrix ((Fin d ⊕ Fin d) × Fin L) ((Fin d ⊕ Fin d) × Fin L) ℂ :=
  ∑ j : Fin L, tagIndex L d j (Matrix.fromBlocks
    ((idealInstrument F p a).branch (j,false) rho.val) 0 0
    ((idealInstrument F p a).branch (j,true) rho.val))

theorem jointPreparedReadout_ideal {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (a : ℝ) :
    jointPreparedReadout F p rho (rotationState a).val = idealJointReadoutMatrix F p a rho := by
  simp only [jointPreparedReadout, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    idealJointReadoutMatrix]
  apply Finset.sum_congr rfl
  intro j _
  change (p.prob j : ℂ) • tagIndex L d j (preparedReadout F j rho (rotationState a).val) = _
  rw [← map_smul, preparedReadout_ideal, Matrix.fromBlocks_smul, smul_zero,
    directBranch_matches_ideal, directBranch_matches_ideal]

theorem native_jointReadout_budget {L d : ℕ} (F : ReflectionFamily L d)
    (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (a : ℝ) (native : Qatlib.Foundations.PureStateMath.DensityOperator 2)
    (epsilon delta : ℝ)
    (hprep : Matrix.traceNorm (native.val - (rotationState a).val) ≤ 2 * epsilon)
    (hindex : (1 / 2 : ℝ) * (∑ j : Fin L, |q.prob j - p.prob j|) ≤ delta) :
    (1 / 2 : ℝ) * Matrix.traceNorm
      (jointPreparedReadout F q rho native.val - idealJointReadoutMatrix F p a rho) ≤ epsilon + delta := by
  rw [← jointPreparedReadout_ideal]
  have h := jointPreparedReadout_total_error F p q rho (rotationState a) native
  linarith

def withReferenceFamily {L d : ℕ} (F : ReflectionFamily L d) (r : ℕ) : ReflectionFamily L (d * r) where
  sigma j := (Qatlib.Foundations.PureStateMath.TensorGate (F.sigma j) (1 : Qatlib.Foundations.PureStateMath.Operator r)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  hermitian j := by
    have hj : (F.sigma j)ᴴ = F.sigma j := F.hermitian j
    have ht : (Qatlib.Foundations.PureStateMath.TensorGate (F.sigma j) (1 : Qatlib.Foundations.PureStateMath.Operator r)).IsHermitian := by
      change (Qatlib.Foundations.PureStateMath.TensorGate (F.sigma j) (1 : Qatlib.Foundations.PureStateMath.Operator r))ᴴ = _
      rw [Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, hj,
          Matrix.conjTranspose_one]
    exact ht.submatrix _
  square j := by
    rw [Matrix.submatrix_mul_equiv, Qatlib.Foundations.PureStateMath.tensorGate_mul, F.square, Matrix.one_mul, Qatlib.Foundations.PureStateMath.tensorGate_one,
      Matrix.submatrix_one_equiv]

theorem rotation_work_discard_error {r : ℕ}
    (ideal native : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ)
    (hi : ideal.PosSemidef) (hn : native.PosSemidef) :
    Matrix.traceNorm (Matrix.traceRight native - Matrix.traceRight ideal) ≤ Matrix.traceNorm (native - ideal) := by
  rw [← Matrix.traceRight_sub]
  exact Qatlib.Concepts.ReferenceError.DensityToRaw.traceRight_hermitian_trace_contraction _
      (hn.isHermitian.sub hi.isHermitian)

end Qatlib.Papers.ThermalDrift26.ThermalSampling
