/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.DiamondStabilization
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationProtocol
import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftCore

/-!
# Diamond-norm stabilization and qDRIFT consumers

This module applies input-dimension stabilization of the diamond norm to concrete operator maps
and channel-error bounds, in the quantum information framework of [Watrous2018]. It computes the
diamond norm of transposition and exhibits a maximally entangled input attaining it in positive
dimension.

The qDRIFT results combine stabilized trace-norm bounds for arbitrary ancillary inputs with
finite diamond distance and sampling-resource ledgers, using the randomized simulation setting
of [Campbell2019].

## Main statements

* `diamond_transpose_entangled_witness`: computes the diamond norm of transposition and an
  attaining input.
* `diamond_stabilized_channel_error_consumer`: characterizes a distance bound using an
  input-sized ancilla.
* `fair_qdrift_stabilized_raw_and_ledgers`: combines stabilized error estimates with circuit and
  sampling resources.

## References

* [Watrous, 2018][Watrous2018]
* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

namespace Qatlib.Concepts.RandCompile.FairBitSampling
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Matrix transposition as a complex-linear map on `D`-dimensional operators. -/
def transposeMap (D : ℕ) : Operator D →ₗ[ℂ] Operator D where
  toFun := Matrix.transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The bipartite vector with diagonal amplitudes `1 / sqrt D` and zero off-diagonal amplitudes. -/
noncomputable def maximallyEntangled (D : ℕ) : QState (Fin D × Fin D) :=
  fun p => if p.1 = p.2 then (Real.sqrt (D : ℝ) : ℂ)⁻¹ else 0

/-- Tensoring transposition with an ancillary identity swaps the system row and column indices
while retaining the ancillary indices. -/
theorem diamond_tensorLeft_transpose_apply {D r : ℕ}
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (a b : Fin D × Fin r) :
    tensorLeft (transposeMap D) X a b = X (b.1,a.2) (a.1,b.2) := rfl

/-- The partial transpose of a rank-one operator formed from two unit bipartite vectors has
trace norm at most `D`. -/
theorem diamond_transpose_unit_rank_one_bound (D : ℕ)
    (u v : QState (Fin D × Fin D))
    (hu : ∑ i, star (u i) * u i = 1) (hv : ∑ i, star (v i) * v i = 1) :
    Matrix.traceNorm (tensorLeft (transposeMap D) (fun i j => u i * star (v j))) ≤ (D : ℝ) := by
  classical
  let A := tensorLeft (transposeMap D) (fun i j => u i * star (v j))
  obtain ⟨U,hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1
  let x : ((Fin D × Fin D) × (Fin D × Fin D)) → ℂ :=
    fun p => star (U.val p.1 p.2)
  let y : ((Fin D × Fin D) × (Fin D × Fin D)) → ℂ :=
    fun p => A p.2 p.1
  have hUiso : U.valᴴ * U.val = 1 := by
    ext a b
    by_cases hab : a = b <;>
      simpa [Matrix.star_eq_conjTranspose, Matrix.one_apply, hab] using
        congrFun (congrFun U.property.1 a) b
  have hcol (j : Fin D × Fin D) : ∑ i, ‖U.val i j‖ ^ 2 = 1 := by
    have hj := congrArg Complex.re (congrFun (congrFun hUiso j) j)
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow, Complex.ofReal_re] using hj
  have hxn : ‖toEuclidean_fromVec x‖ = (D : ℝ) := by
    have hx : ‖toEuclidean_fromVec x‖ ^ 2 = (D : ℝ)^2 := by
      rw [norm_toEuclidean_fromVec_sq]
      simp only [x, norm_star]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [← pow_two, hcol, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, mul_one]

    exact (sq_eq_sq₀ (norm_nonneg _) (Nat.cast_nonneg D)).mp hx
  have hun : ∑ i, ‖u i‖^2 = 1 := by
    simpa [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
        Complex.ofReal_re] using congrArg Complex.re hu
  have hvn : ∑ i, ‖v i‖^2 = 1 := by
    simpa [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
        Complex.ofReal_re] using congrArg Complex.re hv
  have hyn : ‖toEuclidean_fromVec y‖ = 1 := by
    have hy : ‖toEuclidean_fromVec y‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_fromVec_sq]
      simp only [y, A, diamond_tensorLeft_transpose_apply, norm_mul, norm_star, mul_pow,
        Fintype.sum_prod_type]
      simp only [Fintype.sum_prod_type] at hun hvn
      calc
        _ = ∑ a : Fin D, ∑ b : Fin D,
            (∑ d : Fin D, ‖u (a,d)‖^2) * (∑ c : Fin D, ‖v (c,b)‖^2) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm
        _ = (∑ i : Fin D, ∑ j : Fin D, ‖u (i,j)‖^2) *
            (∑ i : Fin D, ∑ j : Fin D, ‖v (i,j)‖^2) := by
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul]
          congr 1
          exact Finset.sum_comm
        _ = 1 := by rw [hun,hvn]; norm_num
    have := (sq_eq_sq₀ (norm_nonneg (toEuclidean_fromVec y)) (by norm_num : (0 : ℝ) ≤ 1)).mp
      (by simpa using hy)
    exact this
  have he : inner ℂ (toEuclidean_fromVec x) (toEuclidean_fromVec y) = (U.val * A).trace := by
    rw [inner_euclidean_fromVec, inner_apply]
    simp [x,y, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
  calc
    Matrix.traceNorm A = ((U.val * A).trace).re := hU.symm
    _ ≤ ‖(U.val * A).trace‖ := Complex.re_le_norm _
    _ ≤ ‖toEuclidean_fromVec x‖ * ‖toEuclidean_fromVec y‖ := by
      rw [← he]
      exact norm_inner_le_norm _ _
    _ = (D : ℝ) := by rw [hxn,hyn]; ring

/-- In positive dimension, the maximally entangled vector is normalized and the partial
transpose of its outer product has trace norm `D`. -/
theorem diamond_transpose_maximally_entangled (D : ℕ) (hD : 0 < D) :
    Normalized (maximallyEntangled D) ∧
    Matrix.traceNorm (tensorLeft (transposeMap D) (outerProduct (maximallyEntangled D))) = (D : ℝ) := by
  letI : NeZero D := ⟨ne_of_gt hD⟩
  have hn : Normalized (maximallyEntangled D) := quditResource_normalized D
  refine ⟨hn,?_⟩
  let W : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := permMatrix (Equiv.prodComm _ _)
  have hW : W ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ := qudit_equiv_perm_unitary _
  have hc : (Real.sqrt (D:ℝ):ℂ)⁻¹ * star ((Real.sqrt (D:ℝ):ℂ)⁻¹) = (D:ℂ)⁻¹ := by
    calc
      _ = (((Real.sqrt (D:ℝ):ℂ))^2)⁻¹ := by simp [pow_two]
      _ = _ := by rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg D)]
                  simp only [Complex.ofReal_natCast]
  have hc' : (Real.sqrt (D:ℝ):ℂ)⁻¹ * (Real.sqrt (D:ℝ):ℂ)⁻¹ = (D:ℂ)⁻¹ := by
    simpa using hc
  have he : tensorLeft (transposeMap D) (outerProduct (maximallyEntangled D)) = (D:ℂ)⁻¹ • W := by
    ext a b
    rw [diamond_tensorLeft_transpose_apply]
    simp only [outerProduct, maximallyEntangled, Matrix.smul_apply, smul_eq_mul, W,
      permMatrix, Matrix.of_apply, Equiv.prodComm_apply, Prod.ext_iff]
    by_cases h1 : a.1 = b.2 <;> by_cases h2 : a.2 = b.1 <;>
      simp [h1,h2,Ne.symm,hc']
  have hnorm : Matrix.traceNorm W = (D:ℝ)^2 := by
    have h := Matrix.traceNorm_isometry_left (A := (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ))
      (u := W) (by
        ext a b
        by_cases hab : a = b <;> simpa [Matrix.star_eq_conjTranspose,Matrix.one_apply,hab] using
          congrFun (congrFun hW.1 a) b)
    rw [Matrix.mul_one] at h
    rw [h]
    have hp :=
        (Matrix.PosSemidef.one : (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ).PosSemidef).traceNorm_eq_trace
    simpa [Matrix.trace, Matrix.one_apply, pow_two] using congrArg Complex.re hp
  rw [he, Matrix.traceNorm_smul, norm_inv, Complex.norm_natCast, hnorm]
  have hDr : (D:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  field_simp

/-- Partial transposition with an input-sized ancilla increases trace norm by at most a factor
of `D`. -/
theorem diamond_transpose_input_bound (D : ℕ)
    (X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    Matrix.traceNorm (tensorLeft (transposeMap D) X) ≤ (D:ℝ) * Matrix.traceNorm X := by
  obtain ⟨s,u,v,hs,hX,_,htrace,hunit⟩ := diamond_svd_trace_decomposition X
  let P : (Fin D × Fin D) → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    fun i a b => u i a * star (v i b)
  have hP (i : Fin D × Fin D) : Matrix.traceNorm (tensorLeft (transposeMap D) (P i)) ≤ (D:ℝ) :=
    diamond_transpose_unit_rank_one_bound D (u i) (v i) (hunit i).1 (hunit i).2
  have hsum : tensorLeft (transposeMap D) X = ∑ i, (s i : ℂ) • tensorLeft (transposeMap D) (P i) := by
    change diamondAmplification (transposeMap D) D X = _
    rw [hX, map_sum]
    simp only [map_smul]
    rfl
  calc
    _ ≤ ∑ i, Matrix.traceNorm ((s i : ℂ) • tensorLeft (transposeMap D) (P i)) := by
      rw [hsum]
      exact diamond_traceNorm_sum_le Finset.univ _
    _ = ∑ i, s i * Matrix.traceNorm (tensorLeft (transposeMap D) (P i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_of_nonneg (hs i)]
    _ ≤ ∑ i, s i * (D:ℝ) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hP i) (hs i)
    _ = (D:ℝ) * Matrix.traceNorm X := by rw [htrace]; simp [Finset.sum_mul, mul_comm]

/-- The finite diamond norm of transposition is `D`; in positive dimension, the normalized
maximally entangled vector gives an outer product whose partial transpose has trace norm
`D`. -/
theorem diamond_transpose_entangled_witness : ∀ D : ℕ,
    finiteDiamondNorm (transposeMap D) = ENNReal.ofReal (D:ℝ) ∧
    (0 < D → Normalized (maximallyEntangled D) ∧
      Matrix.traceNorm (tensorLeft (transposeMap D) (outerProduct (maximallyEntangled D))) = (D:ℝ)) := by
  intro D
  refine ⟨?_,diamond_transpose_maximally_entangled D⟩
  rw [diamond_input_dimension_stabilization]
  apply le_antisymm
  · exact (diamondAtInput_le_iff_uniform _ _ (Nat.cast_nonneg D)).mpr
      (diamond_transpose_input_bound D)
  · by_cases hD : 0 < D
    · obtain ⟨hn,he⟩ := diamond_transpose_maximally_entangled D hD
      have hx : Matrix.traceNorm (outerProduct (maximallyEntangled D)) = 1 := by
        have hp := (outerProduct_posSemidef (maximallyEntangled D)).traceNorm_eq_trace
        rw [trace_outerProduct] at hp
        have := congrArg Complex.re hp
        have hn' : ∑ i, ‖maximallyEntangled D i‖^2 = 1 := hn
        simpa [← Complex.ofReal_pow, hn'] using this
      unfold diamondAtInput
      rw [← he]
      exact le_iSup_of_le (outerProduct (maximallyEntangled D)) (by simp [hx])
    · have hz : D = 0 := by omega
      subst D
      simp

/-- For nonnegative `δ`, finite diamond distance at most `δ / 2` is equivalent to a trace-norm
bound with factor `δ` using an input-sized ancilla. A uniform bound over all ancillary
dimensions also implies that distance bound. -/
theorem diamond_stabilized_channel_error_consumer : ∀ (D E : ℕ)
    (T S : Operator D →ₗ[ℂ] Operator E) (δ : ℝ), 0 ≤ δ →
    (finiteDiamondDistance T S ≤ ENNReal.ofReal (δ/2) ↔
      ∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
        Matrix.traceNorm (tensorLeft (T-S) X) ≤ δ * Matrix.traceNorm X) ∧
    ((∀ r : ℕ, ∀ X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
      Matrix.traceNorm (tensorLeft (T-S) X) ≤ δ * Matrix.traceNorm X) →
      finiteDiamondDistance T S ≤ ENNReal.ofReal (δ/2)) := by
  intro D E T S δ hδ
  have hh : (1/2 : ℝ≥0∞) * ENNReal.ofReal δ = ENNReal.ofReal (δ/2) := by
    rw [show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
    congr 1
    ring
  have hhalf : finiteDiamondDistance T S ≤ ENNReal.ofReal (δ/2) ↔
      finiteDiamondNorm (T-S) ≤ ENNReal.ofReal δ := by
    constructor
    · intro h
      calc
        _ = 2 * finiteDiamondDistance T S := by
          unfold finiteDiamondDistance
          rw [← mul_assoc]
          rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ 2 * ENNReal.ofReal (δ/2) := mul_le_mul le_rfl h bot_le bot_le
        _ = ENNReal.ofReal δ := by
          rw [← hh, ← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
              one_mul]
    · intro h
      unfold finiteDiamondDistance
      rw [← hh]
      exact mul_le_mul le_rfl h bot_le bot_le
  constructor
  · rw [hhalf, diamond_input_dimension_stabilization]
    exact diamondAtInput_le_iff_uniform (T-S) δ hδ
  · intro h
    exact hhalf.mpr ((finiteDiamondNorm_le_iff_uniform D E (T-S) δ hδ).mpr h)

/-- Two input-sized ancillary trace-norm bounds with nonnegative factors `δ` and `ε` give finite
diamond distance at most `(δ + ε) / 2` between the endpoints and a uniform ancillary bound
with factor `δ + ε`. -/
theorem diamond_stabilized_channel_error_chain {D E : ℕ}
    (T S U : Operator D →ₗ[ℂ] Operator E) (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hTS : ∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      Matrix.traceNorm (tensorLeft (T-S) X) ≤ δ * Matrix.traceNorm X)
    (hSU : ∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      Matrix.traceNorm (tensorLeft (S-U) X) ≤ ε * Matrix.traceNorm X) :
    finiteDiamondDistance T U ≤ ENNReal.ofReal ((δ+ε)/2) ∧
    ∀ r : ℕ, ∀ X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
      Matrix.traceNorm (tensorLeft (T-U) X) ≤ (δ+ε) * Matrix.traceNorm X := by
  have hfixed (X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
      Matrix.traceNorm (tensorLeft (T-U) X) ≤ (δ+ε) * Matrix.traceNorm X := by
    rw [← sub_add_sub_cancel T S U, diamond_tensorLeft_add]
    exact (Matrix.traceNorm_add_le _ _).trans
      ((add_le_add (hTS X) (hSU X)).trans_eq (by ring))
  exact ⟨(diamond_stabilized_channel_error_consumer D E T U (δ+ε) (add_nonneg hδ hε)).1.mpr hfixed,
    diamond_uniform_bound_of_input_bound (T-U) (δ+ε) hfixed⟩

/-- Positive weight mass, a valid time bound, and Hermitian contraction terms give input-sized
and arbitrary-ancilla trace-norm error factor `(1/2)^s` and finite diamond distance at most
`(1/2)^s / 2` at the computed budgets. Every sampled circuit is unitary with zero oracle
queries, `n` gates, and the stated bit and comparison bounds. -/
theorem fair_qdrift_stabilized_raw_and_ledgers : ∀ (L D T s : ℕ)
    (w : Fin L → ℕ) (j0 : Fin L) (K : Fin L → Operator D) (t : ℝ),
    0 < weightTotal w → |t| ≤ T → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    let n := fairQdriftSteps (weightTotal w) T s
    let R := fairQdriftFuel n s
    (∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      Matrix.traceNorm (tensorLeft
        (fairQdriftActualMap w j0 n R K t -
          conjBranch (HamiltonianEvolution (∑ j, (w j:ℂ) • K j) t)) X) ≤
        ((2:ℝ)⁻¹)^s * Matrix.traceNorm X) ∧
    (∀ r : ℕ, ∀ X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
      Matrix.traceNorm (tensorLeft
        (fairQdriftActualMap w j0 n R K t -
          conjBranch (HamiltonianEvolution (∑ j, (w j:ℂ) • K j) t)) X) ≤
        ((2:ℝ)⁻¹)^s * Matrix.traceNorm X) ∧
    finiteDiamondDistance (fairQdriftActualMap w j0 n R K t)
      (conjBranch (HamiltonianEvolution (∑ j, (w j:ℂ) • K j) t)) ≤
      ENNReal.ofReal (((2:ℝ)⁻¹)^s/2) ∧
    (∀ omega : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal w)),
      IsUnitaryCircuit (fairQdriftCircuit w j0 n R K t omega) ∧
      QueryCount (fairQdriftCircuit w j0 n R K t omega) = 0 ∧
      GateCount (fairQdriftCircuit w j0 n R K t omega) = n ∧
      (∑ k, (fairQdriftPick w j0 R (omega k)).2.1) ≤ n * Nat.clog 2 (weightTotal w) * R ∧
      (∑ k, (fairQdriftPick w j0 R (omega k)).2.2) ≤ n * L * R) := by
  intro L D T s w j0 K t hW ht hK
  (try dsimp only)
  have hb := fair_qdrift_computed_finite_diamond_and_ledgers L D T s w j0 K t hW ht hK
  have hfixed := (diamond_stabilized_channel_error_consumer D D _ _ (((2:ℝ)⁻¹)^s)
    (by positivity)).1.mp hb.1
  exact ⟨hfixed, diamond_uniform_bound_of_input_bound _ _ hfixed, hb.1, hb.2⟩

/-- Zero total weight gives zero finite diamond distance from the target evolution and zero
trace-norm error for every ancillary dimension and input operator. -/
theorem fair_qdrift_zero_mass_stabilized {L D : ℕ} (w : Fin L → ℕ) (j0 : Fin L)
    (n R : ℕ) (K : Fin L → Operator D) (t : ℝ) (hW : weightTotal w = 0) :
    finiteDiamondDistance (fairQdriftActualMap w j0 n R K t)
      (conjBranch (HamiltonianEvolution (∑ j, (w j:ℂ) • K j) t)) = 0 ∧
    ∀ r : ℕ, ∀ X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
      Matrix.traceNorm (tensorLeft
        (fairQdriftActualMap w j0 n R K t -
          conjBranch (HamiltonianEvolution (∑ j, (w j:ℂ) • K j) t)) X) = 0 := by
  obtain ⟨hA,hB⟩ := fairQdriftActualMap_zero w j0 n R K t hW
  constructor
  · simp [hA,hB,finiteDiamondDistance]
  · intro r X
    rw [hA,hB,sub_self]
    change Matrix.traceNorm (0 : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) = 0
    exact Matrix.traceNorm_zero

end Qatlib.Concepts.RandCompile.FairBitSampling
