/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtDefs
import Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterizationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSPGily
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17AuxBessel
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedLowc
import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedLowc
import Qatlib.Concepts.SignalPrimitive.SparseSim.SparseSimCorrectedRestrictedLowc
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Phase-synthesis counts and QSP perturbation bounds

This module proves response-scaling identities, a quadratic bound for completed-pair synthesis,
and stability estimates for phase-perturbed QSP words. In particular, `qspWord_entry_lipschitz`
bounds entrywise error by the phase-list length times the uniform phase error.

`lcCorrectedQ_bounds` supplies explicit bounds for the corrected Jacobi-Anger truncation degree
used in the signal-processing framework of [LowChuang2017].

## Main statements

* `lqSynthCount_le_of_completed`: bound recursive synthesis operations.
* `qspWord_entry_lipschitz`: control word entries under phase perturbations.
* `lcCorrectedQ_bounds`: bound the corrected truncation degree.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.QspSimulation.SparseWalk
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.SparseSim
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 800000

open Matrix Polynomial
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib
open Qatlib.Concepts.QspSimulation.SparseWalk Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.SignalPrimitive.SparseSim

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared

/-- Both response polynomials scale linearly with the initial complex phase parameter. -/
private theorem response_base_linear' (base : ℂ) (zs : List ℂ) :
    responseP base zs = C base * responseP 1 zs ∧
    responseQ base zs = C base * responseQ 1 zs := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [responseP_cons, responseQ_cons, ih.1, ih.2]
    constructor <;> ring

/-- For a unit-modulus initial phase, responses with initial value one are obtained by
multiplication by its conjugate. -/
theorem responseP_one_of_phase {z0 : ℂ} (hz0 : IsPhase z0) (zs : List ℂ) :
    responseP 1 zs = C (star z0) * responseP z0 zs ∧
    responseQ 1 zs = C (star z0) * responseQ z0 zs := by
  have h := response_base_linear' z0 zs
  constructor
  · rw [h.1]
    calc responseP 1 zs = C 1 * responseP 1 zs := by simp
      _ = C (star z0 * z0) * responseP 1 zs := by rw [hz0]
      _ = C (star z0) * (C z0 * responseP 1 zs) := by rw [C_mul]; ring
  · rw [h.2]
    calc responseQ 1 zs = C 1 * responseQ 1 zs := by simp
      _ = C (star z0 * z0) * responseQ 1 zs := by rw [hz0]
      _ = C (star z0) * (C z0 * responseQ 1 zs) := by rw [C_mul]; ring

/-- For a completed polynomial pair, the recursive synthesis count is at most `lqSynthOpCount
n`. -/
theorem lqSynthCount_le_of_completed (n : ℕ) (P Q : Polynomial ℂ)
    (h : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair n P Q) : lqSynthCount n P Q ≤ lqSynthOpCount n := by
  induction n generalizing P Q with
  | zero =>
    have h0 : lqSynthCount 0 P Q = 0 := by rfl
    have hop : lqSynthOpCount 0 = 0 := by rfl
    rw [h0, hop]
  | succ n ih =>
    have hstep :=
        Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair.inverse_step
        (n := n) (P := P) (Q := Q) h
    have hPnd : P.natDegree ≤ n + 1 := Polynomial.natDegree_le_of_degree_le h.degreeP
    have hQnd : Q.natDegree ≤ n := by
      rcases eq_or_ne Q 0 with rfl | hQ0
      · simp
      · have hk := (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr h.degreeQ
        omega
    have hopEq : lqSynthOpCount n = n * (8 * n + 28) := by rfl
    have hcount_eq : lqSynthCount (n + 1) P Q
        = 12 + 8 * (max P.natDegree Q.natDegree + 1) +
          lqSynthCount n
            (inverseResponseP (alignPhase (P.coeff (n + 1)) (Q.coeff n)) P Q)
            (inverseResponseQ (alignPhase (P.coeff (n + 1)) (Q.coeff n)) P Q) := by
      simp [lqSynthCount]
    rw [hcount_eq]
    have hrec := (ih _ _ hstep.2).trans_eq hopEq
    have htermle : max P.natDegree Q.natDegree + 1 ≤ n + 2 := by omega
    have hA : 12 + 8 * (max P.natDegree Q.natDegree + 1) +
        lqSynthCount n
          (inverseResponseP (alignPhase (P.coeff (n + 1)) (Q.coeff n)) P Q)
          (inverseResponseQ (alignPhase (P.coeff (n + 1)) (Q.coeff n)) P Q)
        ≤ 12 + 8 * (n + 2) + n * (8 * n + 28) := by omega
    have hB : (12 : ℕ) + 8 * (n + 2) + n * (8 * n + 28) ≤ lqSynthOpCount (n + 1) := by
      have hdef : lqSynthOpCount (n + 1) = (n + 1) * (8 * (n + 1) + 28) := by rfl
      rw [hdef]
      have e1 : (12 : ℕ) + 8 * (n + 2) + n * (8 * n + 28) = 8 * n * n + 36 * n + 28 := by ring
      have e2 : (n + 1) * (8 * (n + 1) + 28) = 8 * n * n + 44 * n + 36 := by ring
      omega
    exact hA.trans hB

open scoped Matrix.Norms.L2Operator

/-- The difference between two complex phase exponentials is at most twice the absolute
difference of their real angles. -/
private theorem norm_exp_I_sub_le (a a' : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((a' : ℂ) * Complex.I)‖
      ≤ 2 * |a - a'| := by
  have hE : ∀ t : ℝ, Complex.exp ((t : ℂ) * Complex.I)
      = ((Real.cos t : ℝ) : ℂ) + (((Real.sin t : ℝ) : ℂ)) * Complex.I := by
    intro t
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hsplit : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((a' : ℂ) * Complex.I)
      = ((Real.cos a - Real.cos a' : ℝ) : ℂ)
        + (((Real.sin a - Real.sin a' : ℝ) : ℂ)) * Complex.I := by
    rw [hE a, hE a']
    push_cast
    ring
  have hs' : ‖(((Real.sin a - Real.sin a' : ℝ) : ℂ)) * Complex.I‖
      = |Real.sin a - Real.sin a'| := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  calc ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((a' : ℂ) * Complex.I)‖
      = ‖((Real.cos a - Real.cos a' : ℝ) : ℂ)
          + (((Real.sin a - Real.sin a' : ℝ) : ℂ)) * Complex.I‖ := by rw [hsplit]
    _ ≤ ‖((Real.cos a - Real.cos a' : ℝ) : ℂ)‖
        + ‖(((Real.sin a - Real.sin a' : ℝ) : ℂ)) * Complex.I‖ := norm_add_le _ _
    _ = |Real.cos a - Real.cos a'| + |Real.sin a - Real.sin a'| := by
        rw [Complex.norm_real, Real.norm_eq_abs, hs']
    _ ≤ 2 * |a - a'| := by
        have h1 := Real.abs_cos_sub_cos_le a a'
        have h2 := Real.abs_sin_sub_sin_le a a'
        linarith

/-- A multiplicative left fold with initial accumulator `a` equals `a` times the fold starting
at one. -/
private theorem foldl_mul_prefix' {M : Type*} [Monoid M] (l : List M) (a : M) :
    List.foldl (· * ·) a l = a * List.foldl (· * ·) 1 l := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (1 * x), one_mul, mul_assoc]

/-- Expands a nonempty QSP word into its leading signal-phase factor and the remaining word. -/
private theorem qspWord_cons (a : ℝ) (rest : List ℝ) (x : ℝ) :
    QSPWord (a :: rest) x
      = (SignalMatrix x * PhaseRotation a) * QSPWord rest x := by
  simp only [QSPWord, List.map_cons, List.foldl_cons, one_mul]
  exact foldl_mul_prefix' _ _

/-- A two-dimensional unitary preserves the Euclidean norm of a vector. -/
private theorem unitary_mulVec_norm {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    ‖toEuclidean_fromVec (U *ᵥ v)‖ = ‖toEuclidean_fromVec v‖ := by
  have hI : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry U :=
      (Matrix.mem_unitaryGroup_iff').mp hU
  exact isometry_mulVec_norm hI v

/-- The Euclidean norm of a sum of two vectors is bounded by the sum of their norms. -/
private theorem norm_toEuclidean_add_le (u v : Fin 2 → ℂ) :
    ‖toEuclidean_fromVec (u + v)‖
      ≤ ‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec v‖ := by
  have h : toEuclidean_fromVec (u + v)
      = toEuclidean_fromVec u + toEuclidean_fromVec v := rfl
  rw [h]
  exact norm_add_le _ _

/-- Changing a phase-rotation angle from `a` to `a'` changes its action on `w` by at most `2 *
|a - a'| * ‖w‖`. -/
private theorem phaseRotation_sub_mulVec_norm (a a' : ℝ) (w : Fin 2 → ℂ) :
    ‖toEuclidean_fromVec (PhaseRotation a *ᵥ w - PhaseRotation a' *ᵥ w)‖
      ≤ 2 * |a - a'| * ‖toEuclidean_fromVec w‖ := by
  have hsub : PhaseRotation a *ᵥ w - PhaseRotation a' *ᵥ w
      = (PhaseRotation a - PhaseRotation a') *ᵥ w := by
    rw [Matrix.sub_mulVec]
  have hdiag : PhaseRotation a - PhaseRotation a'
      = Matrix.diagonal (fun b : Fin 2 =>
          if b = 0 then Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((a' : ℂ) * Complex.I)
          else Complex.exp (((-(a : ℝ)) : ℂ) * Complex.I)
            - Complex.exp (((-(a' : ℝ)) : ℂ) * Complex.I)) := by
    simp only [PhaseRotation, Matrix.diagonal_sub]
    congr 1
    funext b
    fin_cases b <;> simp
  rw [hsub]
  have hentry : ∀ b : Fin 2,
      ‖((PhaseRotation a - PhaseRotation a') *ᵥ w) b‖ ≤ 2 * |a - a'| * ‖w b‖ := by
    intro b
    rw [hdiag, Matrix.mulVec_diagonal, norm_mul]
    by_cases hb : b = 0
    · subst hb
      rw [if_pos rfl]
      exact mul_le_mul_of_nonneg_right (norm_exp_I_sub_le a a') (norm_nonneg _)
    · rw [if_neg hb]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h := norm_exp_I_sub_le (-(a : ℝ)) (-(a' : ℝ))
      have e : (-(a : ℝ)) - (-(a' : ℝ)) = -(a - a') := by ring
      rw [e, abs_neg] at h
      simp only [Complex.ofReal_neg] at h
      exact h
  have hterm : ∀ b : Fin 2,
      ‖((PhaseRotation a - PhaseRotation a') *ᵥ w) b‖ ^ 2
        ≤ (2 * |a - a'|) ^ 2 * ‖w b‖ ^ 2 := by
    intro b
    have h := mul_self_le_mul_self (norm_nonneg _) (hentry b)
    have eL : ‖((PhaseRotation a - PhaseRotation a') *ᵥ w) b‖
        * ‖((PhaseRotation a - PhaseRotation a') *ᵥ w) b‖
        = ‖((PhaseRotation a - PhaseRotation a') *ᵥ w) b‖ ^ 2 := (sq _).symm
    have eR : (2 * |a - a'| * ‖w b‖) * (2 * |a - a'| * ‖w b‖)
        = (2 * |a - a'|) ^ 2 * ‖w b‖ ^ 2 := by ring
    rw [eL, eR] at h
    exact h
  have hsq : ‖toEuclidean_fromVec ((PhaseRotation a - PhaseRotation a') *ᵥ w)‖ ^ 2
      ≤ (2 * |a - a'|) ^ 2 * ‖toEuclidean_fromVec w‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => hterm b
  have hsq' : ‖toEuclidean_fromVec ((PhaseRotation a - PhaseRotation a') *ᵥ w)‖ ^ 2
      ≤ (2 * |a - a'| * ‖toEuclidean_fromVec w‖) ^ 2 := by
    rw [mul_pow]
    exact hsq
  have hfin := abs_le_of_sq_le_sq hsq'
    (by positivity : (0 : ℝ) ≤ 2 * |a - a'| * ‖toEuclidean_fromVec w‖)
  rwa [abs_of_nonneg (norm_nonneg _)] at hfin

/-- Equal-length QSP words whose paired phases differ by at most `ε` act on a vector with error
at most `2 * length * ε` times its norm. -/
private theorem qspWord_sub_vec (φ φ' : List ℝ) (ε : ℝ) (hlen : φ.length = φ'.length)
    (_hε : 0 ≤ ε) (hzip : ∀ p ∈ φ.zip φ', |p.1 - p.2| ≤ ε)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (v : Fin 2 → ℂ) :
    ‖toEuclidean_fromVec (QSPWord φ x *ᵥ v - QSPWord φ' x *ᵥ v)‖
      ≤ (φ.length : ℝ) * (2 * ε) * ‖toEuclidean_fromVec v‖ := by
  induction φ generalizing φ' with
  | nil =>
    have hnil : φ' = [] := by
      cases φ' with
      | nil => rfl
      | cons a' rest' => simp at hlen
    subst hnil
    rw [sub_self]
    have h0 : toEuclidean_fromVec (0 : Fin 2 → ℂ) = 0 := rfl
    rw [h0, norm_zero]
    simp
  | cons a rest ih =>
    have hcons' : ∃ a' rest', φ' = a' :: rest' := by
      cases φ' with
      | nil => simp at hlen
      | cons a' rest' => exact ⟨a', rest', rfl⟩
    obtain ⟨a', rest', rfl⟩ := hcons'
    have hda : |a - a'| ≤ ε := by
      have hmem : (a, a') ∈ (a :: rest).zip (a' :: rest') := by
        rw [List.zip_cons_cons]
        exact List.mem_cons_self
      have hzip0 := hzip (a, a') hmem
      simpa using! hzip0
    have hlen' : rest.length = rest'.length := by
      simp at hlen; exact hlen
    have hzip' : ∀ p ∈ rest.zip rest', |p.1 - p.2| ≤ ε := by
      intro p hp
      have hmem : p ∈ (a :: rest).zip (a' :: rest') := by
        rw [List.zip_cons_cons]
        exact List.mem_cons_of_mem _ hp
      exact hzip p hmem
    have hrec := ih rest' hlen' hzip'
    have hW : SignalMatrix x * PhaseRotation a ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      Submonoid.mul_mem _ (signalMatrix_unitary hx.1 hx.2) (phaseRotation_unitary a)
    have hword' : QSPWord rest' x ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      qspWord_unitary rest' hx.1 hx.2
    have hsplit : QSPWord (a :: rest) x *ᵥ v - QSPWord (a' :: rest') x *ᵥ v
        = (SignalMatrix x * PhaseRotation a) *ᵥ
            (QSPWord rest x *ᵥ v - QSPWord rest' x *ᵥ v)
          + (SignalMatrix x * PhaseRotation a - SignalMatrix x * PhaseRotation a') *ᵥ
            (QSPWord rest' x *ᵥ v) := by
      simp only [qspWord_cons, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub,
        Matrix.sub_mulVec]
      abel
    have e4 : (SignalMatrix x * PhaseRotation a - SignalMatrix x * PhaseRotation a') *ᵥ
          (QSPWord rest' x *ᵥ v)
          = SignalMatrix x *ᵥ (PhaseRotation a *ᵥ (QSPWord rest' x *ᵥ v)
              - PhaseRotation a' *ᵥ (QSPWord rest' x *ᵥ v)) := by
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_sub]
    have e3 := phaseRotation_sub_mulVec_norm a a' (QSPWord rest' x *ᵥ v)
    rw [unitary_mulVec_norm hword' v] at e3
    have hgoal' : ((a :: rest).length : ℝ) * (2 * ε) * ‖toEuclidean_fromVec v‖
        = (rest.length : ℝ) * (2 * ε) * ‖toEuclidean_fromVec v‖
          + 2 * ε * ‖toEuclidean_fromVec v‖ := by
      rw [show ((a :: rest).length : ℝ) = (rest.length : ℝ) + 1 from by simp]
      ring
    have hwn : 0 ≤ ‖toEuclidean_fromVec v‖ := norm_nonneg _
    have h1 : 2 * |a - a'| * ‖toEuclidean_fromVec v‖
        ≤ 2 * ε * ‖toEuclidean_fromVec v‖ :=
      mul_le_mul_of_nonneg_right (by linarith) hwn
    rw [hsplit, e4, hgoal']
    calc ‖toEuclidean_fromVec
          ((SignalMatrix x * PhaseRotation a) *ᵥ (QSPWord rest x *ᵥ v - QSPWord rest' x *ᵥ v)
            + SignalMatrix x *ᵥ (PhaseRotation a *ᵥ (QSPWord rest' x *ᵥ v)
                - PhaseRotation a' *ᵥ (QSPWord rest' x *ᵥ v)))‖
        ≤ ‖toEuclidean_fromVec
            ((SignalMatrix x * PhaseRotation a) *ᵥ
              (QSPWord rest x *ᵥ v - QSPWord rest' x *ᵥ v))‖
          + ‖toEuclidean_fromVec (SignalMatrix x *ᵥ (PhaseRotation a *ᵥ
              (QSPWord rest' x *ᵥ v) - PhaseRotation a' *ᵥ (QSPWord rest' x *ᵥ v)))‖ :=
            norm_toEuclidean_add_le _ _
      _ = ‖toEuclidean_fromVec (QSPWord rest x *ᵥ v - QSPWord rest' x *ᵥ v)‖
          + ‖toEuclidean_fromVec (SignalMatrix x *ᵥ (PhaseRotation a *ᵥ
              (QSPWord rest' x *ᵥ v) - PhaseRotation a' *ᵥ (QSPWord rest' x *ᵥ v)))‖ := by
            rw [unitary_mulVec_norm hW _]
      _ ≤ (rest.length : ℝ) * (2 * ε) * ‖toEuclidean_fromVec v‖
          + 2 * |a - a'| * ‖toEuclidean_fromVec v‖ := by
            apply add_le_add hrec
            rw [unitary_mulVec_norm (signalMatrix_unitary hx.1 hx.2)]
            exact e3
      _ ≤ (rest.length : ℝ) * (2 * ε) * ‖toEuclidean_fromVec v‖
          + 2 * ε * ‖toEuclidean_fromVec v‖ := add_le_add le_rfl h1

/-- On `[-1, 1]`, corresponding entries of equal-length QSP words differ by at most `4 * length
* ε` when each phase differs by at most `ε`. -/
theorem qspWord_entry_lipschitz (φ φ' : List ℝ) (ε : ℝ) (hlen : φ.length = φ'.length)
    (hε : 0 ≤ ε) (hzip : ∀ p ∈ φ.zip φ', |p.1 - p.2| ≤ ε)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (i j : Fin 2) :
    ‖QSPWord φ x i j - QSPWord φ' x i j‖ ≤ 4 * (φ.length : ℝ) * ε := by
  have hvec := qspWord_sub_vec φ φ' ε hlen hε hzip hx (Pi.single j (1 : ℂ))
  have hsub : QSPWord φ x *ᵥ (Pi.single j (1 : ℂ)) - QSPWord φ' x *ᵥ (Pi.single j (1 : ℂ))
      = (QSPWord φ x - QSPWord φ' x) *ᵥ (Pi.single j (1 : ℂ)) := by
    rw [← Matrix.sub_mulVec]
  rw [hsub] at hvec
  have h1 : ‖toEuclidean_fromVec (Pi.single j (1 : ℂ))‖ = 1 := by
    have hsq1 : ‖toEuclidean_fromVec (Pi.single j (1 : ℂ))‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_fromVec_sq, Finset.sum_eq_single_of_mem j
        (Finset.mem_univ j)
        (fun b _ hb => by simp [Pi.single_eq_of_ne hb])]
      simp
    rw [← Real.sqrt_sq (norm_nonneg _), hsq1, Real.sqrt_one]
  rw [h1] at hvec
  have hgen : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      (M *ᵥ (Pi.single j (1 : ℂ))) i = M i j := by
    intro M
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [← Matrix.sub_apply, ← hgen (QSPWord φ x - QSPWord φ' x)]
  have hnorm : ‖((QSPWord φ x - QSPWord φ' x) *ᵥ (Pi.single j (1 : ℂ))) i‖
      ≤ ‖toEuclidean_fromVec ((QSPWord φ x - QSPWord φ' x) *ᵥ (Pi.single j (1 : ℂ)))‖ := by
    have h2 := norm_toEuclidean_fromVec_sq
      ((QSPWord φ x - QSPWord φ' x) *ᵥ (Pi.single j (1 : ℂ)))
    have h3 : ‖((QSPWord φ x - QSPWord φ' x) *ᵥ (Pi.single j (1 : ℂ))) i‖ ^ 2
        ≤ ∑ k, ‖((QSPWord φ x - QSPWord φ' x) *ᵥ (Pi.single j (1 : ℂ))) k‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun k =>
          ‖((QSPWord φ x - QSPWord φ' x) *ᵥ (Pi.single j (1 : ℂ))) k‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    rw [← h2] at h3
    have hnn : 0 ≤ ‖toEuclidean_fromVec
        ((QSPWord φ x - QSPWord φ' x) *ᵥ (Pi.single j (1 : ℂ)))‖ := norm_nonneg _
    have hni : 0 ≤ ‖((QSPWord φ x - QSPWord φ' x) *ᵥ (Pi.single j (1 : ℂ))) i‖ :=
      norm_nonneg _
    have h4 := abs_le_of_sq_le_sq h3 hnn
    rwa [abs_of_nonneg hni] at h4
  refine le_trans (hnorm.trans hvec) ?_
  have hlennn : (0 : ℝ) ≤ (φ.length : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- For nonnegative `u`, the logarithm satisfies `u / (1 + u) ≤ log (1 + u)`. -/
private theorem log_one_add_ge_div (u : ℝ) (hu : 0 ≤ u) :
    u / (1 + u) ≤ Real.log (1 + u) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have key : Real.exp (u / (1 + u)) ≤ 1 + u := by
    have hpre : -(u / (1 + u)) + 1 ≤ Real.exp (-(u / (1 + u))) :=
      Real.add_one_le_exp _
    have hEq1 : -(u / (1 + u)) + 1 = (1 + u)⁻¹ := by
      field_simp
      ring
    have hEq2 : Real.exp (-(u / (1 + u))) = (Real.exp (u / (1 + u)))⁻¹ := by
      rw [Real.exp_neg]
    rw [hEq1, hEq2] at hpre
    exact (inv_le_inv₀ h1 (Real.exp_pos _)).mp hpre
  exact (Real.le_log_iff_exp_le h1).mpr key

/-- For nonnegative time and `0 < ε ≤ 1`, the corrected truncation degree is at least `3 * τ`
and satisfies the stated linear-logarithmic and logarithmic-ratio upper bounds. -/
theorem lcCorrectedQ_bounds (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    3 * τ ≤ (lcCorrectedQ τ ε : ℝ) ∧
    (lcCorrectedQ τ ε : ℝ) ≤ 3 * τ + 3 * Real.log (32 / ε) + 8 ∧
    (lcCorrectedQ τ ε : ℝ) ≤
      4 * (Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1) + 2) := by
  have hLpos : (0 : ℝ) < Real.log (32 / ε) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hε]
    linarith
  have hLnn : (0 : ℝ) ≤ Real.log (32 / ε) := hLpos.le
  have hm : (0 : ℝ) < max τ 1 := lt_of_lt_of_le (by norm_num) (le_max_right τ 1)
  have hupos : (0 : ℝ) < Real.log (32 / ε) / max τ 1 := div_pos hLpos hm
  have hℓpos : (0 : ℝ) < Real.log (1 + Real.log (32 / ε) / max τ 1) := by
    refine Real.log_pos ?_
    linarith
  have hℓ_le : Real.log (1 + Real.log (32 / ε) / max τ 1)
      ≤ Real.log (32 / ε) / max τ 1 := by
    have hpos : (0 : ℝ) < 1 + Real.log (32 / ε) / max τ 1 := by linarith
    have hlog := Real.log_le_sub_one_of_pos hpos
    linarith
  have hleceil : (3 : ℝ) * τ ≤ (⌈3 * τ⌉₊ : ℝ) := Nat.le_ceil _
  have hbr1 : (⌈3 * τ⌉₊ : ℝ) + 1 ≤ (lcCorrectedQ τ ε : ℝ) := by
    unfold lcCorrectedQ
    exact_mod_cast Nat.le_max_left _ _
  have hbr2 : (4 : ℝ) ≤ (lcCorrectedQ τ ε : ℝ) := by
    have hnat : (4 : ℕ) ≤ lcCorrectedQ τ ε := by
      unfold lcCorrectedQ
      exact le_trans (le_max_left 4 _)
        (le_max_right (⌈3 * τ⌉₊ + 1) (max 4 _))
    exact_mod_cast hnat
  have hceil3 : (⌈3 * τ⌉₊ : ℝ) < 3 * τ + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hτ)
  have hceilX : (⌈3 * Real.log (32 / ε) /
      Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ : ℝ)
      < 3 * Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1) + 1 :=
    Nat.ceil_lt_add_one (by positivity)

  have hkey : 3 * Real.log (32 / ε)
      ≤ 3 * (max τ 1 + Real.log (32 / ε))
        * Real.log (1 + Real.log (32 / ε) / max τ 1) := by
    have h1 : 3 * (max τ 1 + Real.log (32 / ε))
        * (Real.log (32 / ε) / max τ 1 / (1 + Real.log (32 / ε) / max τ 1))
        ≤ 3 * (max τ 1 + Real.log (32 / ε))
          * Real.log (1 + Real.log (32 / ε) / max τ 1) :=
      mul_le_mul_of_nonneg_left
        (log_one_add_ge_div (Real.log (32 / ε) / max τ 1) hupos.le)
        (by positivity)
    have h2 : 3 * (max τ 1 + Real.log (32 / ε))
        * (Real.log (32 / ε) / max τ 1 / (1 + Real.log (32 / ε) / max τ 1))
        = 3 * Real.log (32 / ε) := by
      have hmu : max τ 1 * (Real.log (32 / ε) / max τ 1) = Real.log (32 / ε) := by
        rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hm)]
      field_simp
    linarith
  have hX : 3 * Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)
      ≤ 3 * (max τ 1 + Real.log (32 / ε)) := by
    rw [div_le_iff₀ hℓpos]
    exact hkey

  refine ⟨by linarith, ?_, ?_⟩
  · have hmle : max τ 1 ≤ τ + 1 := by
      rcases le_or_gt 1 τ with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right (by linarith : τ ≤ 1)]; linarith
    have hb1 : (⌈3 * τ⌉₊ : ℝ) + 1 ≤ 3 * τ + 3 * Real.log (32 / ε) + 8 := by linarith
    have hb2 : (4 : ℝ) ≤ 3 * τ + 3 * Real.log (32 / ε) + 8 := by linarith
    have hb3 : (⌈3 * Real.log (32 / ε) /
        Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ : ℝ) + 1
        ≤ 3 * τ + 3 * Real.log (32 / ε) + 8 := by linarith
    have hq : (lcCorrectedQ τ ε : ℝ)
        = max ((⌈3 * τ⌉₊ : ℝ) + 1)
            (max 4 ((⌈3 * Real.log (32 / ε) /
              Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ : ℝ) + 1)) := by
      unfold lcCorrectedQ
      push_cast
      simp
    rw [hq]
    exact max_le hb1 (max_le hb2 hb3)
  · have hLdivnn : (0 : ℝ)
        ≤ Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1) := by
      positivity

    have hkeyceil : ∀ r : ℝ, 0 ≤ r → (⌈3 * r⌉₊ : ℝ) + 1 ≤ 4 * (r + 2) := by
      intro r hr
      have hA : (⌈3 * r⌉₊ : ℝ) < 3 * r + 1 :=
        Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hr)
      have hB : (3 : ℝ) * r ≤ 4 * (r + 2) := by linarith
      linarith
    have h3form : 3 * Real.log (32 / ε)
          / Real.log (1 + Real.log (32 / ε) / max τ 1)
        = 3 * (Real.log (32 / ε)
          / Real.log (1 + Real.log (32 / ε) / max τ 1)) := by ring
    have hc3 : (⌈3 * Real.log (32 / ε) /
        Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ : ℝ) + 1
        ≤ 4 * (Real.log (32 / ε) /
          Real.log (1 + Real.log (32 / ε) / max τ 1) + 2) := by
      rw [h3form]
      exact hkeyceil _ hLdivnn
    have hc2 : (4 : ℝ) ≤ 4 * (Real.log (32 / ε) /
      Real.log (1 + Real.log (32 / ε) / max τ 1) + 2) := by
      have h1 : (4 : ℝ) ≤ 4 * 2 := by norm_num
      have h2 : (4 : ℝ) * 2 ≤ 4 * (Real.log (32 / ε) /
        Real.log (1 + Real.log (32 / ε) / max τ 1) + 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        linarith
      linarith
    have hc1 : (⌈3 * τ⌉₊ : ℝ) + 1
        ≤ 4 * (Real.log (32 / ε) /
          Real.log (1 + Real.log (32 / ε) / max τ 1) + 2) := by
      rcases le_or_gt 1 τ with hτ1 | hτ1
      · have hmτ : max τ 1 = τ := max_eq_left hτ1
        rw [hmτ] at hℓpos hℓ_le ⊢
        have hLge : τ ≤ Real.log (32 / ε)
            / Real.log (1 + Real.log (32 / ε) / τ) := by
          rw [le_div_iff₀ hℓpos]
          calc τ * Real.log (1 + Real.log (32 / ε) / τ)
              ≤ τ * (Real.log (32 / ε) / τ) :=
                mul_le_mul_of_nonneg_left hℓ_le (by positivity)
            _ = Real.log (32 / ε) := by
                rw [mul_comm, div_mul_cancel₀ _ (by positivity)]
        have h2 : (3 : ℝ) * τ ≤ 3 * (Real.log (32 / ε)
          / Real.log (1 + Real.log (32 / ε) / τ)) := by linarith
        have h3 : (3 : ℝ) * (Real.log (32 / ε)
            / Real.log (1 + Real.log (32 / ε) / τ)) + 2
            ≤ 4 * (Real.log (32 / ε)
              / Real.log (1 + Real.log (32 / ε) / τ) + 2) := by
          have hnn : (0 : ℝ) ≤ Real.log (32 / ε)
            / Real.log (1 + Real.log (32 / ε) / τ) := by positivity
          linarith
        linarith
      · have hτle : τ ≤ 1 := by linarith
        have hceil : (⌈3 * τ⌉₊ : ℝ) + 1 ≤ 4 := by
          have hnat : ⌈3 * τ⌉₊ ≤ 3 :=
            (Nat.ceil_le).mpr (by linarith : (3 : ℝ) * τ ≤ 3)
          have hcast : (⌈3 * τ⌉₊ : ℝ) ≤ (3 : ℝ) := by exact_mod_cast hnat
          linarith
        have hRge : (8 : ℝ) ≤ 4 * (Real.log (32 / ε)
            / Real.log (1 + Real.log (32 / ε) / max τ 1) + 2) := by
          have h1 : (8 : ℝ) ≤ 4 * (Real.log (32 / ε)
            / Real.log (1 + Real.log (32 / ε) / max τ 1)) + 8 := by linarith
          linarith
        linarith
    have hq : (lcCorrectedQ τ ε : ℝ)
        = max ((⌈3 * τ⌉₊ : ℝ) + 1)
            (max 4 ((⌈3 * Real.log (32 / ε) /
              Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ : ℝ) + 1)) := by
      unfold lcCorrectedQ
      push_cast
      simp
    rw [hq]
    exact max_le hc1 (max_le hc2 hc3)
end Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtShared
