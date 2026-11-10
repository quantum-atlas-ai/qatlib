/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.SchattenDiamondDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorLeft
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.CStarAlgebra.Matrix
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Qatlib.Concepts.SchattenDiamond.DiamondNorm

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram.SchattenDiamond

open Matrix Qatlib
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {D E r : ℕ}

def amplifyFactor {D E r : ℕ} (C : Matrix (Fin D) (Fin E) ℂ) :
    Matrix (Fin D × Fin r) (Fin E × Fin r) ℂ :=
  fun p q => if p.2 = q.2 then C p.1 q.1 else 0

def blockRep {E r : ℕ} (M : Matrix (Fin E) (Fin E) ℂ) :
    Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ :=
  fun p q => if p.2 = q.2 then M p.1 q.1 else 0

private lemma star_ite_zero (c : Prop) [Decidable c] (v : ℂ) :
    star (if c then v else 0) = if c then star v else 0 := by
  by_cases hc : c <;> simp [hc]

private lemma sum_ite_col {D r : ℕ} (f : Fin D × Fin r → ℂ) (s : Fin r) :
    ∑ p : Fin D × Fin r, (if p.2 = s then f p else 0) = ∑ d : Fin D, f (d, s) := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ s fun t => f (d, t)]
  simp

theorem tensorLeft_eq_sum_amplified {D E r : ℕ} {T : Operator D →ₗ[ℂ] Operator E}
    (F : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.CbFactorization T)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    tensorLeft T X =
      ∑ j, (amplifyFactor (r := r) (F.A j))ᴴ * X * (amplifyFactor (r := r) (F.B j)) := by
  classical
  ext x y
  have hR : ∀ j : Fin (D * D * E * E),
      ((amplifyFactor (r := r) (F.A j))ᴴ * X * (amplifyFactor (r := r) (F.B j))) x y
        = ∑ d, ∑ d', star (F.A j d x.1) * X (d, x.2) (d', y.2) * F.B j d' y.1 := by
    intro j
    calc ((amplifyFactor (r := r) (F.A j))ᴴ * X * (amplifyFactor (r := r) (F.B j))) x y
        = ∑ q : Fin D × Fin r,
            ((amplifyFactor (r := r) (F.A j))ᴴ * X) x q
              * (if q.2 = y.2 then F.B j q.1 y.1 else 0) := by
          simp only [Matrix.mul_apply, amplifyFactor]
      _ = ∑ q : Fin D × Fin r, (if q.2 = y.2 then
            ((amplifyFactor (r := r) (F.A j))ᴴ * X) x q * F.B j q.1 y.1 else 0) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          by_cases hq : q.2 = y.2 <;> simp [hq]
      _ = ∑ d' : Fin D,
            ((amplifyFactor (r := r) (F.A j))ᴴ * X) x (d', y.2) * F.B j d' y.1 :=
          sum_ite_col _ y.2
      _ = ∑ d' : Fin D, (∑ p : Fin D × Fin r,
            (if p.2 = x.2 then star (F.A j p.1 x.1) * X p (d', y.2) else 0))
            * F.B j d' y.1 := by
          refine Finset.sum_congr rfl fun d' _ => ?_
          have hexp : ((amplifyFactor (r := r) (F.A j))ᴴ * X) x (d', y.2)
              = ∑ p : Fin D × Fin r,
                (if p.2 = x.2 then star (F.A j p.1 x.1) * X p (d', y.2) else 0) := by
            simp only [Matrix.mul_apply, conjTranspose_apply, amplifyFactor, star_ite_zero,
              ite_mul, zero_mul]
          rw [hexp]
      _ = ∑ d' : Fin D,
            (∑ d : Fin D, star (F.A j d x.1) * X (d, x.2) (d', y.2)) * F.B j d' y.1 := by
          refine Finset.sum_congr rfl fun d' _ => ?_
          rw [sum_ite_col (fun p => star (F.A j p.1 x.1) * X p (d', y.2)) x.2]
      _ = ∑ d : Fin D, ∑ d' : Fin D,
            star (F.A j d x.1) * X (d, x.2) (d', y.2) * F.B j d' y.1 := by
          simp_rw [Finset.sum_mul]
          exact Finset.sum_comm
  have hL : tensorLeft T X x y
      = ∑ j, ∑ d' : Fin D,
          (∑ d : Fin D, star (F.A j d x.1) * X (d, x.2) (d', y.2)) * F.B j d' y.1 := by
    have hrepr := F.repr (fun i i' => X (i, x.2) (i', y.2))
    simp only [tensorLeft]
    rw [hrepr]
    simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply]
  rw [hL]
  simp only [Matrix.sum_apply, hR]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem sum_amplifyFactor_mul_conjTranspose {D E r : ℕ}
    {N : ℕ} (C : Fin N → Matrix (Fin D) (Fin E) ℂ) :
    ∑ j, amplifyFactor (r := r) (C j) * (amplifyFactor (r := r) (C j))ᴴ
      = blockRep (E := D) (r := r) (∑ j, C j * (C j)ᴴ) := by
  classical
  ext x y
  by_cases hxy : x.2 = y.2
  · have hentry : ∀ j : Fin N, (amplifyFactor (r := r) (C j)
        * (amplifyFactor (r := r) (C j))ᴴ) x y
        = ∑ e : Fin E, C j x.1 e * star (C j y.1 e) := by
      intro j
      simp only [Matrix.mul_apply, conjTranspose_apply, amplifyFactor, star_ite_zero]
      rw [← hxy]
      have hstep : ∀ p : Fin E × Fin r,
          (if x.2 = p.2 then C j x.1 p.1 else 0)
              * (if x.2 = p.2 then star (C j y.1 p.1) else 0)
            = if x.2 = p.2 then C j x.1 p.1 * star (C j y.1 p.1) else 0 := by
        intro p
        by_cases hp : x.2 = p.2 <;> simp [hp]
      have hsum : (∑ p : Fin E × Fin r,
          (if x.2 = p.2 then C j x.1 p.1 else 0)
              * (if x.2 = p.2 then star (C j y.1 p.1) else 0))
          = ∑ p : Fin E × Fin r,
            if x.2 = p.2 then C j x.1 p.1 * star (C j y.1 p.1) else 0 :=
        Finset.sum_congr rfl fun p _ => hstep p
      rw [hsum]
      have hcol : (∑ p : Fin E × Fin r,
          if x.2 = p.2 then C j x.1 p.1 * star (C j y.1 p.1) else 0)
          = ∑ e : Fin E, C j x.1 e * star (C j y.1 e) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_eq_single_of_mem x.2 (Finset.mem_univ x.2) fun t _ ht => by
          simp [Ne.symm ht]]
        simp
      rw [hcol]
    simp only [Matrix.sum_apply, hentry, blockRep, hxy, if_true, Matrix.mul_apply,
      conjTranspose_apply]
  · have h0 : ∀ j : Fin N, (amplifyFactor (r := r) (C j)
        * (amplifyFactor (r := r) (C j))ᴴ) x y = 0 := by
      intro j
      simp only [Matrix.mul_apply, conjTranspose_apply, amplifyFactor, star_ite_zero]
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases h1 : x.2 = p.2
      · rw [if_pos h1, if_neg]
        · simp
        · intro h2
          exact hxy (h1.trans h2.symm)
      · rw [if_neg h1, zero_mul]
    simp only [Matrix.sum_apply, h0, Finset.sum_const_zero]
    simp only [blockRep, hxy, if_false, Matrix.sum_apply]

open EuclideanSpace in

private lemma norm_toLp_sq {ι : Type} [Fintype ι] (f : ι → ℂ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℂ ι)‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

open EuclideanSpace in

private lemma norm_toLp {ι : Type} [Fintype ι] (f : ι → ℂ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℂ ι)‖ = Real.sqrt (∑ i, ‖f i‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← norm_toLp_sq]

open EuclideanSpace in

private lemma inner_toLp_mulVec {m n : Type} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) (v : m → ℂ) (u : n → ℂ) :
    inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 (M *ᵥ u))
      = inner ℂ (WithLp.toLp 2 (Mᴴ *ᵥ v)) (WithLp.toLp 2 u) := by
  rw [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_toLp_toLp,
    Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, dotProduct_comm,
    Matrix.dotProduct_mulVec]
  simp only [dotProduct, Matrix.vecMul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

open EuclideanSpace in

private lemma opNorm_le_of_mulVec_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    {c : ℝ} (hc : 0 ≤ c) (A : Matrix m n ℂ)
    (h : ∀ x : n → ℂ, ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ m)‖
      ≤ c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖) :
    ‖A‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have h1 : ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := m) (n := n)).trans
      LinearMap.toContinuousLinearMap) A x
      = (WithLp.toLp 2 (A *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℂ m) := by
    rw [LinearEquiv.trans_apply]
    exact Matrix.toLpLin_apply 2 2 A x
  rw [h1]
  calc ‖(WithLp.toLp 2 (A *ᵥ (WithLp.ofLp x)) : EuclideanSpace ℂ m)‖
      ≤ c * ‖(WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℂ n)‖ :=
        h (WithLp.ofLp x)
    _ = c * ‖x‖ := by rw [WithLp.toLp_ofLp]

open EuclideanSpace in
open EuclideanSpace in

private lemma norm_toLp_mulVec_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) (v : n → ℂ) :
    ‖((WithLp.toLp 2 (M *ᵥ v) : EuclideanSpace ℂ m))‖
      ≤ ‖M‖ * ‖((WithLp.toLp 2 v : EuclideanSpace ℂ n))‖ := by
  have hF : ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := m) (n := n)).trans
      LinearMap.toContinuousLinearMap) M ((WithLp.toLp 2 v : EuclideanSpace ℂ n))
      = (WithLp.toLp 2 (M *ᵥ v) : EuclideanSpace ℂ m) := by
    rw [LinearEquiv.trans_apply]
    exact Matrix.toLpLin_toLp 2 2 M v
  have h2 := ContinuousLinearMap.le_opNorm
    (((Matrix.toEuclideanLin (𝕜 := ℂ) (m := m) (n := n)).trans
      LinearMap.toContinuousLinearMap) M) ((WithLp.toLp 2 v : EuclideanSpace ℂ n))
  rw [hF, ← Matrix.l2_opNorm_def] at h2
  exact h2

private lemma abs_sum_le {ι : Type} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, a i * b i‖ ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  have hinner : (∑ i, a i * b i)
      = inner ℂ (WithLp.toLp 2 fun i => star (a i)) (WithLp.toLp 2 b) := by
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [dotProduct, Pi.star_apply, star_star]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  calc ‖∑ i, a i * b i‖
      = ‖(inner ℂ (WithLp.toLp 2 fun i => star (a i)) (WithLp.toLp 2 b) : ℂ)‖ := by
            rw [hinner]
    _ ≤ ‖(WithLp.toLp 2 fun i => star (a i) : EuclideanSpace ℂ ι)‖
        * ‖(WithLp.toLp 2 b : EuclideanSpace ℂ ι)‖ :=
          norm_inner_le_norm _ _
    _ = Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
        have hA : ∑ i, ‖star (a i)‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [norm_star]
        rw [norm_toLp, norm_toLp, hA]

open EuclideanSpace in

private theorem opNorm_le_entry {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  classical
  refine opNorm_le_of_mulVec_le (Real.sqrt_nonneg _) A ?_
  intro x
  have hx : Real.sqrt (∑ j, ‖x j‖ ^ 2)
      = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ := (norm_toLp x).symm
  have hrow : ∀ i : m, ‖(A *ᵥ x) i‖
      ≤ Real.sqrt (∑ j, ‖A i j‖ ^ 2) * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ := by
    intro i
    have hi := abs_sum_le (A i) x
    calc ‖(A *ᵥ x) i‖ = ‖∑ j, A i j * x j‖ := by simp [Matrix.mulVec, dotProduct]
      _ ≤ Real.sqrt (∑ j, ‖A i j‖ ^ 2) * Real.sqrt (∑ j, ‖x j‖ ^ 2) := hi
      _ = Real.sqrt (∑ j, ‖A i j‖ ^ 2) * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ := by
            rw [hx]
  have hS : (0:ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by positivity
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [norm_toLp_sq, mul_pow, Real.sq_sqrt hS]
  calc ∑ i, ‖(A *ᵥ x) i‖ ^ 2
      ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hi2 := sq_le_sq'
              ((neg_nonpos.mpr (by positivity)).trans (norm_nonneg _)) (hrow i)
            rw [mul_pow, Real.sq_sqrt (x := ∑ j, ‖A i j‖ ^ 2) (by positivity)] at hi2
            exact hi2
      _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 := by
            rw [Finset.sum_mul]

open EuclideanSpace in

private theorem blockRep_norm_le {E r : ℕ} (M : Matrix (Fin E) (Fin E) ℂ) :
    ‖(blockRep (E := E) (r := r) M)‖ ≤ ‖M‖ := by
  refine opNorm_le_of_mulVec_le (norm_nonneg _) _ ?_
  intro x
  have hentry : ∀ p : Fin E × Fin r, (blockRep (E := E) (r := r) M *ᵥ x) p
      = (M *ᵥ (fun e' => x (e', p.2))) p.1 := by
    intro p
    simp only [Matrix.mulVec, blockRep, dotProduct]
    rw [Fintype.sum_prod_type]
    have hsum : (∑ e' : Fin E, ∑ t : Fin r,
        (if p.2 = t then M p.1 e' else 0) * x (e', t))
        = ∑ e' : Fin E, ∑ t : Fin r,
          if p.2 = t then M p.1 e' * x (e', t) else 0 :=
      Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun t _ => by
        by_cases h : p.2 = t <;> simp [h]
    rw [hsum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [Finset.sum_eq_single_of_mem p.2 (Finset.mem_univ p.2) fun t _ ht => by
      simp [Ne.symm ht]]
    simp
  have hcol : ∀ s : Fin r,
      ‖((WithLp.toLp 2 (M *ᵥ (fun e' => x (e', s))) : EuclideanSpace ℂ (Fin E)))‖
        ≤ ‖M‖ * ‖((WithLp.toLp 2 (fun e' => x (e', s)) : EuclideanSpace ℂ (Fin E)))‖ :=
    fun s => norm_toLp_mulVec_le M _
  have hcolsq : ∀ s : Fin r, (∑ e : Fin E, ‖(M *ᵥ (fun e' => x (e', s))) e‖ ^ 2)
      ≤ ‖M‖ ^ 2 * (∑ e : Fin E, ‖x (e, s)‖ ^ 2) := by
    intro s
    have h := hcol s
    have h2 := sq_le_sq' ((neg_nonpos.mpr (by positivity)).trans (norm_nonneg _)) h
    rw [norm_toLp_sq, mul_pow, norm_toLp_sq] at h2
    exact h2
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [norm_toLp_sq, mul_pow, norm_toLp_sq]
  calc ∑ p : Fin E × Fin r, ‖(blockRep (E := E) (r := r) M *ᵥ x) p‖ ^ 2
      = ∑ p : Fin E × Fin r, ‖(M *ᵥ (fun e' => x (e', p.2))) p.1‖ ^ 2 :=
          Finset.sum_congr rfl fun p _ => by rw [hentry p]
      _ = ∑ s : Fin r, ∑ e : Fin E, ‖(M *ᵥ (fun e' => x (e', s))) e‖ ^ 2 := by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_comm
      _ ≤ ∑ s : Fin r, ‖M‖ ^ 2 * (∑ e : Fin E, ‖x (e, s)‖ ^ 2) :=
            Finset.sum_le_sum fun s _ => hcolsq s
      _ = ‖M‖ ^ 2 * (∑ e : Fin E, ∑ s : Fin r, ‖x (e, s)‖ ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
      _ = ‖M‖ ^ 2 * (∑ p : Fin E × Fin r, ‖x p‖ ^ 2) := by
            rw [Fintype.sum_prod_type]

private lemma conjTranspose_amplifyFactor {D E r : ℕ} (C : Matrix (Fin D) (Fin E) ℂ) :
    (amplifyFactor (r := r) C)ᴴ = amplifyFactor (r := r) (Cᴴ) := by
  ext p q
  simp only [conjTranspose_apply, amplifyFactor, star_ite_zero]
  by_cases h : p.2 = q.2
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun h2 => h h2.symm), if_neg h]

theorem amplifyFactor_conjTranspose_mul {D E r : ℕ} (C : Matrix (Fin D) (Fin E) ℂ) :
    (amplifyFactor (r := r) C)ᴴ * amplifyFactor (r := r) C
      = blockRep (E := E) (r := r) (Cᴴ * C) := by
  have h := sum_amplifyFactor_mul_conjTranspose (r := r) (fun _ : Fin 1 => Cᴴ)
  simp only [Fin.sum_univ_one] at h
  rw [← conjTranspose_amplifyFactor, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at h
  exact h

theorem norm_amplifyFactor_le {D E r : ℕ} (C : Matrix (Fin D) (Fin E) ℂ) :
    ‖amplifyFactor (r := r) C‖ ≤ ‖C‖ := by
  have h1 : ‖amplifyFactor (r := r) C‖ ^ 2 ≤ ‖C‖ ^ 2 := by
    calc ‖amplifyFactor (r := r) C‖ ^ 2
        = ‖(amplifyFactor (r := r) C)ᴴ * amplifyFactor (r := r) C‖ := by
              rw [Matrix.l2_opNorm_conjTranspose_mul_self]; ring
      _ = ‖blockRep (E := E) (r := r) (Cᴴ * C)‖ := by rw [amplifyFactor_conjTranspose_mul]
      _ ≤ ‖Cᴴ * C‖ := blockRep_norm_le _
      _ = ‖C‖ * ‖C‖ := Matrix.l2_opNorm_conjTranspose_mul_self C
      _ = ‖C‖ ^ 2 := by ring
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

private lemma opNorm_one_le {n : Type} [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  refine opNorm_le_of_mulVec_le zero_le_one _ fun x => ?_
  simp [Matrix.one_mulVec]

private lemma opNorm_le_one_of_conjTranspose_mul {n : Type} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) : ‖U‖ ≤ 1 := by
  have h : ‖U‖ * ‖U‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hU]
    exact opNorm_one_le
  nlinarith [norm_nonneg U, h]

private lemma re_star_mul_self (c : ℂ) : (star c * c).re = ‖c‖ ^ 2 := by
  rw [Complex.mul_re]
  show c.re * c.re - (-c.im) * c.im = ‖c‖ ^ 2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private lemma trace_conjTranspose_mul_re {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) :
    ((Aᴴ * A).trace).re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hexp : (Aᴴ * A).trace = ∑ i, ∑ j, star (A j i) * A j i := by
    simp [Matrix.trace, Matrix.mul_apply, conjTranspose_apply]
  rw [hexp]
  simp only [Complex.re_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => re_star_mul_self _

private lemma sq_le_sq_of_le {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) (hb : 0 ≤ b) :
    a ^ 2 ≤ b ^ 2 :=
  sq_le_sq' ((neg_nonpos.mpr hb).trans ha) h

private lemma opNorm_sq_le_trace_re {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ‖A‖ ^ 2 ≤ ((Aᴴ * A).trace).re := by
  refine le_trans (sq_le_sq_of_le (norm_nonneg _) (opNorm_le_entry A) (Real.sqrt_nonneg _)) ?_
  rw [Real.sq_sqrt (by positivity), trace_conjTranspose_mul_re]

private lemma sum_mul_le_sqrt {J : Type} [Fintype J] (p q : J → ℝ) :
    (∑ j, p j * q j) ≤ Real.sqrt (∑ j, (p j) ^ 2) * Real.sqrt (∑ j, (q j) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset J) p q
  have hsq : ((∑ j, p j * q j)) ^ 2
      ≤ (Real.sqrt (∑ j, (p j) ^ 2) * Real.sqrt (∑ j, (q j) ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    exact h
  exact (abs_le_of_sq_le_sq' hsq
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2

private lemma traceNorm_sum_le {n : Type} [Fintype n] [DecidableEq n] {J : Type} [Fintype J]
    (M : J → Matrix n n ℂ) :
    Matrix.traceNorm (∑ j, M j) ≤ ∑ j, Matrix.traceNorm (M j) := by
  classical
  have main : ∀ s : Finset J, Matrix.traceNorm (∑ j ∈ s, M j)
      ≤ ∑ j ∈ s, Matrix.traceNorm (M j) := fun s =>
    Finset.induction_on s
      (by simp)
      (fun x s hx ih => by
        rw [Finset.sum_insert hx, Finset.sum_insert hx]
        exact (Matrix.traceNorm_add_le _ _).trans (add_le_add le_rfl ih))
  exact main Finset.univ

theorem traceNorm_tensorLeft_le_factorization {D E r : ℕ}
    {T : Operator D →ₗ[ℂ] Operator E}
    (F : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.CbFactorization T)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (tensorLeft T X)
      ≤ Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm F * Matrix.traceNorm X := by
  have key : ∀ j : Fin (D * D * E * E),
      Matrix.traceNorm ((amplifyFactor (r := r) (F.A j))ᴴ * X
          * amplifyFactor (r := r) (F.B j))
      ≤ ‖amplifyFactor (r := r) (F.A j)‖ * ‖amplifyFactor (r := r) (F.B j)‖
        * Matrix.traceNorm X := by
    intro j
    obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U
      ((amplifyFactor (r := r) (F.A j))ᴴ * X * amplifyFactor (r := r) (F.B j))).left
    have hUu := (@Matrix.mem_unitaryGroup_iff' (Fin E × Fin r)
      (fun a b => Classical.propDecidable (a = b)) _ ℂ _ _).mp U.prop
    rw [Matrix.star_eq_conjTranspose] at hUu
    have hUn : ‖U.val‖ ≤ 1 :=
      @opNorm_le_one_of_conjTranspose_mul (Fin E × Fin r) _
        (fun a b => Classical.propDecidable (a = b)) _ hUu
    have hcyc : (U.val * ((amplifyFactor (r := r) (F.A j))ᴴ * X
          * amplifyFactor (r := r) (F.B j))).trace
        = ((amplifyFactor (r := r) (F.B j) * U.val
            * (amplifyFactor (r := r) (F.A j))ᴴ) * X).trace := by
      rw [← Matrix.mul_assoc U.val ((amplifyFactor (r := r) (F.A j))ᴴ * X)
          (amplifyFactor (r := r) (F.B j)),
        Matrix.trace_mul_comm (U.val * ((amplifyFactor (r := r) (F.A j))ᴴ * X))
          (amplifyFactor (r := r) (F.B j)),
        ← Matrix.mul_assoc (amplifyFactor (r := r) (F.B j)) U.val
          ((amplifyFactor (r := r) (F.A j))ᴴ * X),
        ← Matrix.mul_assoc (amplifyFactor (r := r) (F.B j) * U.val)
          ((amplifyFactor (r := r) (F.A j))ᴴ) X]
    have hBU : ‖amplifyFactor (r := r) (F.B j) * U.val‖
        ≤ ‖amplifyFactor (r := r) (F.B j)‖ := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      calc ‖amplifyFactor (r := r) (F.B j)‖ * ‖U.val‖
          ≤ ‖amplifyFactor (r := r) (F.B j)‖ * 1 :=
            mul_le_mul_of_nonneg_left hUn (norm_nonneg _)
        _ = ‖amplifyFactor (r := r) (F.B j)‖ := mul_one _
    calc Matrix.traceNorm ((amplifyFactor (r := r) (F.A j))ᴴ * X
          * amplifyFactor (r := r) (F.B j))
        = Complex.re ((U.val * ((amplifyFactor (r := r) (F.A j))ᴴ * X
            * amplifyFactor (r := r) (F.B j))).trace) := hU.symm
      _ ≤ ‖((amplifyFactor (r := r) (F.B j) * U.val
            * (amplifyFactor (r := r) (F.A j))ᴴ) * X).trace‖ := by
              rw [hcyc]
              exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ ≤ Matrix.traceNorm ((amplifyFactor (r := r) (F.B j) * U.val
            * (amplifyFactor (r := r) (F.A j))ᴴ) * X) :=
              Matrix.abs_trace_le_traceNorm _
      _ ≤ ‖amplifyFactor (r := r) (F.B j) * U.val
            * (amplifyFactor (r := r) (F.A j))ᴴ‖ * Matrix.traceNorm X :=
              Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
      _ ≤ ‖(amplifyFactor (r := r) (F.A j))ᴴ‖ * ‖amplifyFactor (r := r) (F.B j)‖
            * Matrix.traceNorm X := by
              refine mul_le_mul ?_ le_rfl (Matrix.traceNorm_nonneg _)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              calc ‖amplifyFactor (r := r) (F.B j) * U.val
                    * (amplifyFactor (r := r) (F.A j))ᴴ‖
                    ≤ ‖amplifyFactor (r := r) (F.B j) * U.val‖
                      * ‖(amplifyFactor (r := r) (F.A j))ᴴ‖ := Matrix.l2_opNorm_mul _ _
                _ ≤ ‖amplifyFactor (r := r) (F.B j)‖
                      * ‖(amplifyFactor (r := r) (F.A j))ᴴ‖ :=
                      mul_le_mul_of_nonneg_right hBU (norm_nonneg _)
                _ = ‖(amplifyFactor (r := r) (F.A j))ᴴ‖
                      * ‖amplifyFactor (r := r) (F.B j)‖ := mul_comm _ _
      _ = ‖amplifyFactor (r := r) (F.A j)‖ * ‖amplifyFactor (r := r) (F.B j)‖
            * Matrix.traceNorm X := by rw [Matrix.l2_opNorm_conjTranspose]
  have hsqrt : (∑ j : Fin (D * D * E * E), ‖amplifyFactor (r := r) (F.A j)‖
        * ‖amplifyFactor (r := r) (F.B j)‖)
      ≤ Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm F := by
    have hA : (∑ j, ‖amplifyFactor (r := r) (F.A j)‖ ^ 2)
        ≤ ∑ j, ((F.A j)ᴴ * (F.A j)).trace.re :=
      Finset.sum_le_sum fun j _ =>
        sq_le_sq_of_le (norm_nonneg _) (norm_amplifyFactor_le _) (norm_nonneg _)
          |>.trans (opNorm_sq_le_trace_re _)
    have hB : (∑ j, ‖amplifyFactor (r := r) (F.B j)‖ ^ 2)
        ≤ ∑ j, ((F.B j)ᴴ * (F.B j)).trace.re :=
      Finset.sum_le_sum fun j _ =>
        sq_le_sq_of_le (norm_nonneg _) (norm_amplifyFactor_le _) (norm_nonneg _)
          |>.trans (opNorm_sq_le_trace_re _)
    unfold Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm
    exact (sum_mul_le_sqrt _ _).trans
      (mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc Matrix.traceNorm (tensorLeft T X)
      = Matrix.traceNorm (∑ j, (amplifyFactor (r := r) (F.A j))ᴴ * X
          * amplifyFactor (r := r) (F.B j)) := by rw [tensorLeft_eq_sum_amplified]
    _ ≤ ∑ j, Matrix.traceNorm ((amplifyFactor (r := r) (F.A j))ᴴ * X
          * amplifyFactor (r := r) (F.B j)) := traceNorm_sum_le _
    _ ≤ ∑ j, ‖amplifyFactor (r := r) (F.A j)‖ * ‖amplifyFactor (r := r) (F.B j)‖
          * Matrix.traceNorm X := Finset.sum_le_sum fun j _ => key j
    _ = (∑ j, ‖amplifyFactor (r := r) (F.A j)‖ * ‖amplifyFactor (r := r) (F.B j)‖)
          * Matrix.traceNorm X := by rw [Finset.sum_mul]
    _ ≤ Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm F * Matrix.traceNorm X :=
          mul_le_mul_of_nonneg_right hsqrt (Matrix.traceNorm_nonneg _)

theorem diamondNorm_le_cbFactorizationNorm {D E : ℕ} {T : Operator D →ₗ[ℂ] Operator E}
    (F : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.CbFactorization T) :
    Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm T
      ≤ ENNReal.ofReal (Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm F) := by
  have hd : 0 ≤ Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm F := by
    unfold Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact (Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_le_iff_uniform D E T _ hd).mpr
    fun r X => traceNorm_tensorLeft_le_factorization F X

theorem frontier1 {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm T
      ≤ Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbNormDual T := by
  unfold Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbNormDual
  exact le_iInf fun F => diamondNorm_le_cbFactorizationNorm F

theorem cbNormDual_lt_top_of_strictlyFeasible {D E : ℕ} {T : Operator D →ₗ[ℂ] Operator E}
    (h : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.CbStrictlyFeasible T) :
    Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbNormDual T < ⊤ := by
  obtain ⟨F, -⟩ := h
  refine lt_of_le_of_lt ?_
    (ENNReal.ofReal_lt_top (r := Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm F))
  unfold Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbNormDual
  exact iInf_le _ F

theorem finiteDiamondNorm_lt_top_of_strictlyFeasible {D E : ℕ}
    {T : Operator D →ₗ[ℂ] Operator E}
    (h : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.CbStrictlyFeasible T) :
    Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm T < ⊤ :=
  lt_of_le_of_lt (frontier1 T) (cbNormDual_lt_top_of_strictlyFeasible h)

theorem trace_bias_le_traceNorm_sub {D E r : ℕ}
    (T S : Operator D →ₗ[ℂ] Operator E)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (M : Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ) (hM : ‖M‖ ≤ 1) :
    |(M * tensorLeft T X).trace.re - (M * tensorLeft S X).trace.re|
      ≤ Matrix.traceNorm (tensorLeft (T - S) X) := by
  have hre : (M * tensorLeft T X).trace.re - (M * tensorLeft S X).trace.re
      = ((M * tensorLeft (T - S) X).trace).re := by
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.mul_sub,
      ← Qatlib.Concepts.SchattenDiamond.DiamondNorm.diamond_tensorLeft_map_sub]
  rw [hre]
  calc |((M * tensorLeft (T - S) X).trace).re|
      ≤ ‖(M * tensorLeft (T - S) X).trace‖ := Complex.abs_re_le_norm _
    _ ≤ Matrix.traceNorm (M * tensorLeft (T - S) X) :=
          Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖M‖ * Matrix.traceNorm (tensorLeft (T - S) X) :=
          Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ Matrix.traceNorm (tensorLeft (T - S) X) :=
          (mul_le_mul_of_nonneg_right hM (Matrix.traceNorm_nonneg _)).trans (one_mul _).le

theorem channel_discrimination_bias_le_factorization {D E r : ℕ}
    (T S : Operator D →ₗ[ℂ] Operator E)
    (F : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.CbFactorization (T - S))
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (M : Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ) (hM : ‖M‖ ≤ 1) :
    |(M * tensorLeft T X).trace.re - (M * tensorLeft S X).trace.re|
      ≤ Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm F * Matrix.traceNorm X :=
  (trace_bias_le_traceNorm_sub T S X M hM).trans
    (traceNorm_tensorLeft_le_factorization F X)

theorem channel_discrimination_bias_le_diamond {D E r : ℕ}
    (T S : Operator D →ₗ[ℂ] Operator E)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (M : Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ) (hM : ‖M‖ ≤ 1) :
    ENNReal.ofReal |(M * tensorLeft T X).trace.re - (M * tensorLeft S X).trace.re|
      ≤ Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (T - S)
        * ENNReal.ofReal (Matrix.traceNorm X) := by
  calc ENNReal.ofReal |(M * tensorLeft T X).trace.re - (M * tensorLeft S X).trace.re|
      ≤ ENNReal.ofReal (Matrix.traceNorm (tensorLeft (T - S) X)) :=
          ENNReal.ofReal_le_ofReal (trace_bias_le_traceNorm_sub T S X M hM)
    _ ≤ Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm (T - S)
          * ENNReal.ofReal (Matrix.traceNorm X) :=
          Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_apply (T - S) r X

end Qatlib.Concepts.FiniteLocc.LOCCProgram.SchattenDiamond
