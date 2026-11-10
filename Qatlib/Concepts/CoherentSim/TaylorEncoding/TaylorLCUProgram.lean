/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation
import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.CoherentSim.TaylorEncoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false

abbrev TaylorWordLabel (J : Type) (K : ℕ) := (Σ l : Fin (K + 1), Fin l.val → J) ⊕ Bool

def taylorEmptyWord (J : Type) : Fin 0 → J := fun i => i.elim0

def taylorEmptyLabel (J : Type) (K : ℕ) : TaylorWordLabel J K :=
  Sum.inl ⟨0, taylorEmptyWord J⟩

def taylorWordLen {J : Type} {K : ℕ} : TaylorWordLabel J K → ℕ
  | Sum.inl w => w.1.val
  | Sum.inr _ => 0

noncomputable def taylorWordCoefficient {J : Type} (h : J → ℝ) (τ : ℝ) {K : ℕ}
    (w : Σ l : Fin (K + 1), Fin l.val → J) : ℂ :=
  ((-Complex.I * (τ : ℂ)) ^ (w.1.val : ℕ) / (w.1.val.factorial : ℂ)) *
    ∏ i, ((h (w.2 i) : ℂ))

def taylorLambda {J : Type} [Fintype J] (h : J → ℝ) : ℝ := ∑ j, |h j|

noncomputable def taylorS0 {J : Type} [Fintype J] (h : J → ℝ) (τ : ℝ) (K : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (K + 1), (taylorLambda h * |τ|) ^ l / l.factorial

noncomputable def taylorCoeff {J : Type} [Fintype J] (h : J → ℝ) (τ : ℝ) (K : ℕ) :
    TaylorWordLabel J K → ℂ :=
  fun x => match x with
    | Sum.inl w => taylorWordCoefficient h τ w
    | Sum.inr b => if b then (2 - taylorS0 h τ K) / 2 else -(2 - taylorS0 h τ K) / 2

noncomputable def taylorAmplitudeReal {J : Type} [Fintype J] (h : J → ℝ) (τ : ℝ) (K : ℕ)
    (x : TaylorWordLabel J K) : ℝ := Real.sqrt (‖taylorCoeff h τ K x‖ / 2)

section Balancing

variable {J : Type} [Fintype J]

theorem taylor_sum_prod_abs (h : J → ℝ) (l : ℕ) :
    ∑ w : Fin l → J, ∏ i, |h (w i)| = (taylorLambda h) ^ l := by
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum
    (fun _ : Fin l => (Finset.univ : Finset J)) (fun (_ : Fin l) (j : J) => |h j|),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, taylorLambda]

theorem abs_taylorWordCoefficient (h : J → ℝ) (τ : ℝ) {K : ℕ}
    (w : Σ l : Fin (K + 1), Fin l.val → J) :
    ‖taylorWordCoefficient h τ w‖ =
      |τ| ^ (w.1.val : ℕ) / w.1.val.factorial * ∏ i, |h (w.2 i)| := by
  have h1 : ‖(-Complex.I * (τ : ℂ)) ^ (w.1.val : ℕ)‖ = |τ| ^ (w.1.val : ℕ) := by
    rw [norm_pow, show -Complex.I * (τ : ℂ) = -(Complex.I * (τ : ℂ)) from by ring, norm_neg,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖∏ i, ((h (w.2 i) : ℂ))‖ = ∏ i, |h (w.2 i)| := by
    rw [Complex.norm_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [taylorWordCoefficient, norm_mul, norm_div, h1, h2, Complex.norm_natCast]

theorem taylorS0_lt_two (h : J → ℝ) (τ : ℝ) (K : ℕ)
    (hτ : taylorLambda h * |τ| ≤ 1 / 2) : taylorS0 h τ K ≤ 2 - (1 / 2 : ℝ) ^ K := by
  have hpos : 0 ≤ taylorLambda h * |τ| := mul_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)
    (abs_nonneg _)
  have hfact : ∀ l : ℕ, (1 : ℝ) ≤ (l.factorial : ℝ) := fun l => by exact_mod_cast l.factorial_pos
  have hterm : ∀ l ∈ Finset.range (K + 1),
      (taylorLambda h * |τ|) ^ l / l.factorial ≤ (1 / 2 : ℝ) ^ l := by
    intro l _
    refine (div_le_iff₀ (by positivity : (0 : ℝ) < (l.factorial : ℝ))).2 ?_
    refine le_trans (pow_le_pow_left₀ hpos hτ l) ?_
    exact le_mul_of_one_le_right (by positivity) (hfact l)
  calc taylorS0 h τ K = ∑ l ∈ Finset.range (K + 1), (taylorLambda h * |τ|) ^ l / l.factorial :=
        rfl
    _ ≤ ∑ l ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ l :=
        Finset.sum_le_sum hterm
    _ = 2 - (1 / 2 : ℝ) ^ K := by
        rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
        field_simp
        ring

theorem taylorCoeff_inl (h : J → ℝ) (τ : ℝ) {K : ℕ}
    (w : Σ l : Fin (K + 1), Fin l.val → J) :
    taylorCoeff h τ K (Sum.inl w) = taylorWordCoefficient h τ w := rfl

theorem taylor_sum_norm_eq_two (h : J → ℝ) (τ : ℝ) (K : ℕ)
    (hτ : taylorLambda h * |τ| ≤ 1 / 2) : ∑ x, ‖taylorCoeff h τ K x‖ = 2 := by
  have hs0 := taylorS0_lt_two h τ K hτ
  have half : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
  have hpad : (0 : ℝ) ≤ 2 - taylorS0 h τ K := by linarith
  have hinl : ∑ w : Σ l : Fin (K + 1), Fin l.val → J, ‖taylorWordCoefficient h τ w‖
      = taylorS0 h τ K := by
    rw [Fintype.sum_sigma]
    have hinner : ∀ l : Fin (K + 1),
        ∑ w' : Fin l.val → J, ‖taylorWordCoefficient h τ ⟨l, w'⟩‖
          = (taylorLambda h * |τ|) ^ l.val / l.val.factorial := by
      intro l
      have hval : ∀ w' : Fin l.val → J, ‖taylorWordCoefficient h τ ⟨l, w'⟩‖
          = |τ| ^ l.val / l.val.factorial * ∏ i, |h (w' i)| := by
        intro w'
        simpa using abs_taylorWordCoefficient h τ ⟨l, w'⟩
      rw [Finset.sum_congr rfl fun w' _ => hval w', ← Finset.mul_sum,
        taylor_sum_prod_abs h l.val, mul_pow]
      ring
    rw [Finset.sum_congr rfl fun l _ => hinner l]
    rw [Fin.sum_univ_eq_sum_range
      (fun v => (taylorLambda h * |τ|) ^ v / v.factorial) (K + 1), taylorS0]
  have hinr : ∑ b : Bool, ‖taylorCoeff h τ K (Sum.inr b)‖ = 2 - taylorS0 h τ K := by
    have hnorm : ∀ z : ℝ, 0 ≤ z → ‖(z : ℂ)‖ = z := by
      intro z hz
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
    have hpdiv : (0 : ℝ) ≤ (2 - taylorS0 h τ K) / 2 := by positivity
    have hval : ∀ b : Bool, ‖taylorCoeff h τ K (Sum.inr b)‖ = (2 - taylorS0 h τ K) / 2 := by
      intro b
      cases b with
      | false =>
          rw [show taylorCoeff h τ K (Sum.inr false) = -(((2 - taylorS0 h τ K) / 2 : ℝ) : ℂ) from by
              simp only [taylorCoeff]
              push_cast
              ring, norm_neg, hnorm _ hpdiv]
      | true =>
          rw [show taylorCoeff h τ K (Sum.inr true) = (((2 - taylorS0 h τ K) / 2 : ℝ) : ℂ) from by
              simp [taylorCoeff], hnorm _ hpdiv]
    rw [Fintype.sum_bool, hval false, hval true]
    linarith
  have hinl' : ∑ w : Σ l : Fin (K + 1), Fin l.val → J, ‖taylorCoeff h τ K (Sum.inl w)‖
      = taylorS0 h τ K := by
    rw [Finset.sum_congr rfl fun w _ => by rw [taylorCoeff_inl h τ w]]
    exact hinl
  rw [Fintype.sum_sum_type, hinl', hinr]
  linarith

theorem taylor_amplitude_sq_sum (h : J → ℝ) (τ : ℝ) (K : ℕ)
    (hτ : taylorLambda h * |τ| ≤ 1 / 2) :
    ∑ x, (taylorAmplitudeReal h τ K x) ^ 2 = 1 := by
  simp only [taylorAmplitudeReal,
    Real.sq_sqrt (div_nonneg (norm_nonneg _) zero_le_two)]
  rw [← Finset.sum_div, taylor_sum_norm_eq_two h τ K hτ]
  norm_num

end Balancing

section Program

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

noncomputable def taylorFrame (j0 : J) (K : ℕ) :
    Matrix (TaylorWordLabel J K × (Bool × (J × I))) I ℂ :=
  Matrix.of fun x i => if x = (taylorEmptyLabel J K, (false, (j0, i))) then (1 : ℂ) else 0

private def taylorFrameMap (j0 : J) {K : ℕ} : I → TaylorWordLabel J K × (Bool × (J × I)) :=
  fun i => (taylorEmptyLabel J K, (false, (j0, i)))

private theorem taylorFrameMap_injective (j0 : J) {K : ℕ} :
    Function.Injective (taylorFrameMap (I := I) (K := K) j0) := by
  intro a b hab
  simp only [taylorFrameMap, Prod.mk.injEq] at hab
  simp at hab
  exact hab

private theorem isIsometry_of_delta' {X : Type} [Fintype X] [DecidableEq X]
    {Y : Type} [Fintype Y] [DecidableEq Y] {f : Y → X} (hf : Function.Injective f)
    (V : Matrix X Y ℂ) (hV : ∀ x y, V x y = if x = f y then (1 : ℂ) else 0) :
    IsIsometry V := by
  unfold IsIsometry
  ext y₁ y₂
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, hV, Matrix.one_apply]
  by_cases h : y₁ = y₂
  · subst h
    rw [Finset.sum_eq_single (f y₁)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro x _
      have hne : f y₁ ≠ f y₂ := fun hh => h (hf hh)
      by_cases hx : x = f y₁
      · rw [hx]
        simp [hne]
      · by_cases hx' : x = f y₂
        · rw [hx']
          simp [Ne.symm hne]
        · simp [hx]

theorem taylorFrame_isIsometry (j0 : J) (K : ℕ) : IsIsometry (taylorFrame (I := I) j0 K) :=
  isIsometry_of_delta' (taylorFrameMap_injective j0) _ fun _ _ => rfl

def taylorSwapAddr {J : Type} [DecidableEq J] (j0 a : J) : J → J :=
  fun x => if x = j0 then a else if x = a then j0 else x

theorem taylorSwapAddr_involutive {J : Type} [DecidableEq J] (j0 a : J) :
    Function.Involutive (taylorSwapAddr j0 a) := by
  intro x
  by_cases h1 : x = j0
  · by_cases h2 : a = j0
    · have hxa : x = a := h1.trans h2.symm
      subst hxa
      simp [taylorSwapAddr]
    · have e1 : taylorSwapAddr j0 a x = a := by simp [taylorSwapAddr, h1]
      have e2 : taylorSwapAddr j0 a a = j0 := by simp [taylorSwapAddr, h2]
      show taylorSwapAddr j0 a (taylorSwapAddr j0 a x) = x
      rw [e1, e2, h1]
  · by_cases h2 : x = a
    · have e1 : taylorSwapAddr j0 a x = j0 := by simp [taylorSwapAddr, h2]
      have e2 : taylorSwapAddr j0 a j0 = a := by simp [taylorSwapAddr]
      show taylorSwapAddr j0 a (taylorSwapAddr j0 a x) = x
      rw [e1, e2, h2]
    · have e1 : taylorSwapAddr j0 a x = x := by simp [taylorSwapAddr, h1, h2]
      show taylorSwapAddr j0 a (taylorSwapAddr j0 a x) = x
      rw [e1, e1]

def taylorActive {J : Type} {K : ℕ} (w : Σ l : Fin (K + 1), Fin l.val → J) (j : Fin K) : Bool :=
  (j : ℕ) < w.1.val

def taylorWordAt {J : Type} {K : ℕ} (j0 : J) (w : Σ l : Fin (K + 1), Fin l.val → J)
    (j : Fin K) : J :=
  if h : (j : ℕ) < w.1.val then w.2 ⟨j, h⟩ else j0

def taylorRouteSwap (j0 : J) {K : ℕ} (j : Fin K) :
    TaylorWordLabel J K × (Bool × (J × I)) → TaylorWordLabel J K × (Bool × (J × I)) :=
  fun x => match x.1 with
    | Sum.inl w =>
        (x.1, (xor x.2.1 (taylorActive w j),
          (if taylorActive w j then taylorSwapAddr j0 (taylorWordAt j0 w j) x.2.2.1
            else x.2.2.1, x.2.2.2)))
    | Sum.inr _ => x

theorem taylorRouteSwap_involutive (j0 : J) {K : ℕ} (j : Fin K) :
    Function.Involutive (taylorRouteSwap (I := I) (K := K) j0 j) := by
  intro ⟨wl, f, a, d⟩
  match wl with
  | Sum.inl w =>
      cases hact : taylorActive w j with
      | true =>
          have h1 : taylorRouteSwap j0 j (Sum.inl w, (f, (a, d)))
              = (Sum.inl w, (!f, (taylorSwapAddr j0 (taylorWordAt j0 w j) a, d))) := by
            simp [taylorRouteSwap, hact]
          have h2 : taylorRouteSwap j0 j
              (Sum.inl w, (!f, (taylorSwapAddr j0 (taylorWordAt j0 w j) a, d)))
              = (Sum.inl w, (!(!f), (taylorSwapAddr j0 (taylorWordAt j0 w j)
                  (taylorSwapAddr j0 (taylorWordAt j0 w j) a), d))) := by
            simp [taylorRouteSwap, hact]
          rw [h1, h2, taylorSwapAddr_involutive j0 (taylorWordAt j0 w j) a]
          simp [Bool.not_not]
      | false =>
          have h1 : taylorRouteSwap j0 j (Sum.inl w, (f, (a, d)))
              = (Sum.inl w, (f, (a, d))) := by
            simp [taylorRouteSwap, hact]
          calc taylorRouteSwap j0 j (taylorRouteSwap j0 j (Sum.inl w, (f, (a, d))))
              = taylorRouteSwap j0 j (Sum.inl w, (f, (a, d))) := congrArg _ h1
            _ = (Sum.inl w, (f, (a, d))) := h1
  | Sum.inr b => rfl

noncomputable def taylorRouteMatrix (j0 : J) {K : ℕ} (j : Fin K) :
    Matrix (TaylorWordLabel J K × (Bool × (J × I))) (TaylorWordLabel J K × (Bool × (J × I))) ℂ :=
  permMatrix (taylorRouteSwap (I := I) j0 j)

theorem taylorRouteMatrix_unitary (j0 : J) {K : ℕ} (j : Fin K) :
    taylorRouteMatrix (I := I) j0 j ∈
      Matrix.unitaryGroup (TaylorWordLabel J K × (Bool × (J × I))) ℂ :=
  permMatrix_unitary (taylorRouteSwap_involutive j0 j)

noncomputable def taylorQuery (U : J → Matrix I I ℂ) (K : ℕ) :
    Matrix (TaylorWordLabel J K × (Bool × (J × I))) (TaylorWordLabel J K × (Bool × (J × I))) ℂ :=
  TensorGate (1 : Matrix (TaylorWordLabel J K) (TaylorWordLabel J K) ℂ)
    (controlOracle (select U))

theorem taylorQuery_unitary (U : J → Matrix I I ℂ) (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ)
    (K : ℕ) :
    taylorQuery U K ∈
      Matrix.unitaryGroup (TaylorWordLabel J K × (Bool × (J × I))) ℂ :=
  tensorGate_unitary (Matrix.unitaryGroup _ ℂ).one_mem
    (controlOracle_unitary (select_unitary U hU))

noncomputable def taylorPhaseGate (h : J → ℝ) (τ : ℝ) (K : ℕ) :
    Matrix (TaylorWordLabel J K) (TaylorWordLabel J K) ℂ :=
  Matrix.diagonal (fun x => coefficientPhase (taylorCoeff h τ K x))

theorem taylorPhaseGate_unitary (h : J → ℝ) (τ : ℝ) (K : ℕ) :
    taylorPhaseGate h τ K ∈ Matrix.unitaryGroup (TaylorWordLabel J K) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, taylorPhaseGate,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  exact coefficientPhase_unit _

noncomputable def taylorPrepare (h : J → ℝ) (τ : ℝ) (K : ℕ) : Matrix (TaylorWordLabel J K) (TaylorWordLabel J K) ℂ :=
  nonnegativePrepare (fun x => Real.sqrt (‖taylorCoeff h τ K x‖ / 2)) (taylorEmptyLabel J K)

theorem taylorPrepare_column (h : J → ℝ) (τ : ℝ) (K : ℕ) (x : TaylorWordLabel J K) :
    taylorPrepare h τ K x (taylorEmptyLabel J K)
      = (Real.sqrt (‖taylorCoeff h τ K x‖ / 2) : ℂ) :=
  nonnegativePrepare_column _ _ (fun _ => Real.sqrt_nonneg _) x

theorem taylorPrepare_unitary (h : J → ℝ) (τ : ℝ) (K : ℕ)
    (hτ : taylorLambda h * |τ| ≤ 1 / 2) :
    taylorPrepare h τ K ∈ Matrix.unitaryGroup (TaylorWordLabel J K) ℂ :=
  nonnegativePrepare_unitary _ _ (fun _ => Real.sqrt_nonneg _)
    (taylor_amplitude_sq_sum h τ K hτ)

noncomputable def taylorQueryRouteStep (j0 : J) {K : ℕ} (j : Fin K) :
    List (AdjointStep (TaylorWordLabel J K × (Bool × (J × I)))) :=
  [.gate (taylorRouteMatrix j0 j), .forward, .gate (taylorRouteMatrix j0 j)]

noncomputable def taylorBlockList (j0 : J) (K : ℕ) : (n : ℕ) → n ≤ K →
    List (AdjointStep (TaylorWordLabel J K × (Bool × (J × I))))
  | 0, _ => []
  | n + 1, hn =>
      taylorQueryRouteStep j0 (K := K) ⟨n, Nat.lt_of_succ_le hn⟩ ++
        taylorBlockList j0 K n (Nat.le_of_succ_le hn)

noncomputable def taylorSelectProductAux (U : J → Matrix I I ℂ) (j0 : J) (K : ℕ) :
    (n : ℕ) → n ≤ K →
    Matrix (TaylorWordLabel J K × (Bool × (J × I))) (TaylorWordLabel J K × (Bool × (J × I))) ℂ
  | 0, _ => 1
  | n + 1, hn =>
      taylorRouteMatrix j0 (K := K) ⟨n, Nat.lt_of_succ_le hn⟩ * taylorQuery U K *
        taylorRouteMatrix j0 (K := K) ⟨n, Nat.lt_of_succ_le hn⟩ *
        taylorSelectProductAux U j0 K n (Nat.le_of_succ_le hn)

noncomputable def taylorLCUWord (h : J → ℝ) (j0 : J) (τ : ℝ) (K : ℕ) :
    List (AdjointStep (TaylorWordLabel J K × (Bool × (J × I)))) :=
  [.gate (TensorGate (taylorPrepare h τ K)ᴴ
      (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ)),
    .gate (TensorGate (taylorPhaseGate h τ K)
      (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))] ++
    taylorBlockList j0 K K le_rfl ++
    [.gate (TensorGate (taylorPrepare h τ K)
      (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))]

noncomputable def taylorLCUUnitary (h : J → ℝ) (U : J → Matrix I I ℂ) (j0 : J) (τ : ℝ)
    (K : ℕ) :
    Matrix (TaylorWordLabel J K × (Bool × (J × I))) (TaylorWordLabel J K × (Bool × (J × I))) ℂ :=
  TensorGate (taylorPrepare h τ K)ᴴ (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ) *
    TensorGate (taylorPhaseGate h τ K) (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ) *
    taylorSelectProductAux U j0 K K le_rfl *
    TensorGate (taylorPrepare h τ K) (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ)

private theorem counts_taylorBlockList (j0 : J) (K : ℕ) : ∀ (n : ℕ) (hn : n ≤ K),
    adjointQueryCount (taylorBlockList (I := I) j0 K n hn) = n ∧
    adjointGateCount (taylorBlockList (I := I) j0 K n hn) = 2 * n := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ m ih =>
      intro hm
      have hblock : taylorBlockList (I := I) j0 K (m + 1) hm
          = taylorQueryRouteStep (I := I) j0 (K := K) ⟨m, Nat.lt_of_succ_le hm⟩ ++
            taylorBlockList (I := I) j0 K m (Nat.le_of_succ_le hm) := rfl
      rw [hblock, adjointQueryCount_append, adjointGateCount_append,
        (ih (Nat.le_of_succ_le hm)).1, (ih (Nat.le_of_succ_le hm)).2]
      simp only [taylorQueryRouteStep, adjointQueryCount, adjointGateCount]
      exact ⟨by omega, by omega⟩

private theorem taylorBlockList_wellFormed (j0 : J) (K : ℕ) : ∀ (n : ℕ) (hn : n ≤ K),
    WellFormedAdjointCircuit (taylorBlockList (I := I) j0 K n hn) := by
  intro n
  induction n with
  | zero => intro _; exact WellFormedAdjointCircuit.nil
  | succ m ih =>
      intro hm
      have hblock : taylorBlockList (I := I) j0 K (m + 1) hm
          = taylorQueryRouteStep (I := I) j0 (K := K) ⟨m, Nat.lt_of_succ_le hm⟩ ++
            taylorBlockList (I := I) j0 K m (Nat.le_of_succ_le hm) := rfl
      rw [hblock]
      refine WellFormedAdjointCircuit.append ?_ (ih (Nat.le_of_succ_le hm))
      simp only [taylorQueryRouteStep, WellFormedAdjointCircuit.gate_cons_iff,
        WellFormedAdjointCircuit.forward_cons_iff, WellFormedAdjointCircuit.nil, and_true]
      exact ⟨taylorRouteMatrix_unitary j0 ⟨m, Nat.lt_of_succ_le hm⟩,
        taylorRouteMatrix_unitary j0 ⟨m, Nat.lt_of_succ_le hm⟩⟩

theorem taylor_lcu_actual_prepare_select_and_counts (h : J → ℝ) (j0 : J) (τ : ℝ) (K : ℕ)
    (hτ : (∑ j, |h j|) * |τ| ≤ 1 / 2) :
    IsIsometry (taylorFrame (I := I) j0 K) ∧
      WellFormedAdjointCircuit (taylorLCUWord (I := I) h j0 τ K) ∧
    adjointQueryCount (taylorLCUWord (I := I) h j0 τ K) = K ∧
    adjointGateCount (taylorLCUWord (I := I) h j0 τ K) = 2 * K + 3 := by
  have hlam : taylorLambda h * |τ| ≤ 1 / 2 := hτ
  have hP : taylorPrepare h τ K ∈ Matrix.unitaryGroup (TaylorWordLabel J K) ℂ :=
    taylorPrepare_unitary h τ K hlam
  have hPw : ∀ (A : Matrix (TaylorWordLabel J K) (TaylorWordLabel J K) ℂ),
      A ∈ Matrix.unitaryGroup (TaylorWordLabel J K) ℂ →
      TensorGate A (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ) ∈
        Matrix.unitaryGroup (TaylorWordLabel J K × (Bool × (J × I))) ℂ :=
    fun A hA => tensorGate_unitary hA (Matrix.unitaryGroup _ ℂ).one_mem
  have hwf1 : WellFormedAdjointCircuit
      ([.gate (TensorGate (taylorPrepare h τ K)ᴴ
        (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ)),
        .gate (TensorGate (taylorPhaseGate h τ K)
        (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))] :
        List (AdjointStep (TaylorWordLabel J K × (Bool × (J × I))))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact ⟨hPw _ (adjoint_unitary hP), hPw _ (taylorPhaseGate_unitary h τ K)⟩
  have hwf3 : WellFormedAdjointCircuit
      ([.gate (TensorGate (taylorPrepare h τ K)
        (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))] :
        List (AdjointStep (TaylorWordLabel J K × (Bool × (J × I))))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact hPw _ hP
  have hq := counts_taylorBlockList (I := I) j0 K K le_rfl
  refine ⟨taylorFrame_isIsometry j0 K, ?_, ?_, ?_⟩
  · rw [taylorLCUWord]
    exact WellFormedAdjointCircuit.append (WellFormedAdjointCircuit.append hwf1
      (taylorBlockList_wellFormed (I := I) j0 K K le_rfl)) hwf3
  · rw [taylorLCUWord, adjointQueryCount_append, adjointQueryCount_append, hq.1]
    simp only [adjointQueryCount]
    simp
  · rw [taylorLCUWord, adjointGateCount_append, adjointGateCount_append, hq.2]
    simp only [adjointGateCount]
    omega

noncomputable def taylorBranchFrame (j0 : J) (K : ℕ) (wl : TaylorWordLabel J K) :
    Matrix (TaylorWordLabel J K × (Bool × (J × I))) I ℂ :=
  Matrix.of fun x i => if (wl, (false, (j0, i))) = x then (1 : ℂ) else 0

noncomputable def taylorBranchStep (U : J → Matrix I I ℂ) {K : ℕ} (j : Fin K)
    (wl : TaylorWordLabel J K) : Matrix I I ℂ :=
  match wl with
  | Sum.inl w => if h : (j : ℕ) < w.1.val then U (w.2 ⟨j, h⟩) else 1
  | Sum.inr _ => 1

noncomputable def taylorBranchWord (U : J → Matrix I I ℂ) (K : ℕ) :
    (n : ℕ) → n ≤ K → TaylorWordLabel J K → Matrix I I ℂ
  | 0, _, _ => 1
  | n + 1, hn, wl =>
      taylorBranchStep U ⟨n, Nat.lt_of_succ_le hn⟩ wl *
        taylorBranchWord U K n (Nat.le_of_succ_le hn) wl

private theorem taylorBranchFrame_mulVec (j0 : J) (K : ℕ) (wl : TaylorWordLabel J K)
    (ψ : QState I) (x : TaylorWordLabel J K × (Bool × (J × I))) :
    (taylorBranchFrame j0 K wl *ᵥ ψ) x =
      if x.1 = wl ∧ x.2 = (false, (j0, x.2.2.2)) then ψ x.2.2.2 else 0 := by
  obtain ⟨wl', f, a, d⟩ := x
  show (∑ i, taylorBranchFrame j0 K wl (wl', (f, (a, d))) i * ψ i) =
      (if wl' = wl ∧ (f, (a, d)) = (false, (j0, d)) then ψ d else 0)
  by_cases hw : wl' = wl
  · by_cases hf : f = false
    · by_cases ha : a = j0
      · simp [taylorBranchFrame, hw, hf, ha]
      · simp only [taylorBranchFrame, Matrix.of_apply, Prod.mk.injEq, hw, hf, ha,
          show j0 ≠ a from fun h => ha h.symm]
        simp
    · simp [taylorBranchFrame, hw, hf]
  · simp [taylorBranchFrame, show wl ≠ wl' from fun h => hw h.symm]
    intro h1
    exact absurd h1 hw

private noncomputable def taylorSectorFrame (K : ℕ) (wl : TaylorWordLabel J K)
    (b : Bool) (a : J) : Matrix (TaylorWordLabel J K × (Bool × (J × I))) I ℂ :=
  Matrix.of fun x i => if x = (wl, (b, (a, i))) then 1 else 0

private theorem mul_taylorSectorFrame {K : ℕ} (A : Matrix
    (TaylorWordLabel J K × (Bool × (J × I)))
    (TaylorWordLabel J K × (Bool × (J × I))) ℂ)
    (wl : TaylorWordLabel J K) (b : Bool) (a : J) (x : TaylorWordLabel J K × (Bool × (J × I))) (i : I) :
    (A * taylorSectorFrame (I := I) K wl b a) x i = A x (wl, (b, (a, i))) := by
  simp [Matrix.mul_apply, taylorSectorFrame, mul_ite]

private theorem taylorSectorFrame_mul (K : ℕ) (wl : TaylorWordLabel J K)
    (b : Bool) (a : J) (V : Matrix I I ℂ) (x : TaylorWordLabel J K × (Bool × (J × I))) (i : I) :
    (taylorSectorFrame (I := I) K wl b a * V) x i =
      if x.1 = wl ∧ x.2.1 = b ∧ x.2.2.1 = a then V x.2.2.2 i else 0 := by
  rcases x with ⟨w, f, j, d⟩
  by_cases hw : w = wl <;> by_cases hf : f = b <;> by_cases hj : j = a <;>
    simp [Matrix.mul_apply, taylorSectorFrame, hw, hf, hj, ite_mul]

private theorem taylorQuery_sector (U : J → Matrix I I ℂ) (K : ℕ)
    (wl : TaylorWordLabel J K) (b : Bool) (a : J) :
    taylorQuery U K * taylorSectorFrame (I := I) K wl b a =
      taylorSectorFrame (I := I) K wl b a * (if b then U a else 1) := by
  ext ⟨w, f, j, d⟩ i
  rw [mul_taylorSectorFrame, taylorSectorFrame_mul]
  by_cases hw : w = wl <;> by_cases hj : j = a <;> cases f <;> cases b <;>
    simp [taylorQuery, TensorGate, controlOracle, select,
      Matrix.one_apply, hw, hj]

private theorem taylorRoute_sector (j0 : J) {K : ℕ} (j : Fin K)
    (wl : TaylorWordLabel J K) (b : Bool) (a : J) :
    taylorRouteMatrix (I := I) j0 j * taylorSectorFrame (I := I) K wl b a =
      match wl with
      | Sum.inl w => taylorSectorFrame (I := I) K wl (xor b (taylorActive w j))
          (if taylorActive w j then taylorSwapAddr j0 (taylorWordAt j0 w j) a else a)
      | Sum.inr _ => taylorSectorFrame (I := I) K wl b a := by
  ext x i
  rw [mul_taylorSectorFrame]
  cases wl <;> rfl

private theorem taylorPosition_sector (U : J → Matrix I I ℂ) (j0 : J) {K : ℕ}
    (j : Fin K) (wl : TaylorWordLabel J K) :
    (taylorRouteMatrix (I := I) j0 j * taylorQuery U K * taylorRouteMatrix (I := I) j0 j) *
        taylorSectorFrame (I := I) K wl false j0 =
      taylorSectorFrame (I := I) K wl false j0 * taylorBranchStep U j wl := by
  simp only [Matrix.mul_assoc]
  rw [taylorRoute_sector]
  cases wl with
  | inr b =>
      rw [taylorQuery_sector]
      simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_one]
      rw [taylorRoute_sector]
      simp [taylorBranchStep]
  | inl w =>
      by_cases hj : j.val < w.1.val
      · simp only [taylorActive, hj, decide_true, Bool.false_xor,
          ↓reduceIte, taylorWordAt, taylorSwapAddr]
        rw [taylorQuery_sector, ← Matrix.mul_assoc, taylorRoute_sector]
        by_cases ha : w.2 ⟨j, hj⟩ = j0 <;>
          simp [taylorActive, hj, taylorWordAt, taylorSwapAddr, taylorBranchStep, ha]
      · simp only [taylorActive, hj, decide_false, Bool.xor_false,
          Bool.false_eq_true, ↓reduceIte]
        rw [taylorQuery_sector]
        simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_one]
        rw [taylorRoute_sector]
        simp [taylorActive, hj, taylorBranchStep]

private theorem taylorSelectProduct_sector (U : J → Matrix I I ℂ) (j0 : J) (K : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ K) (wl : TaylorWordLabel J K),
      taylorSelectProductAux U j0 K n hn * taylorSectorFrame (I := I) K wl false j0 =
        taylorSectorFrame (I := I) K wl false j0 * taylorBranchWord U K n hn wl := by
  intro n
  induction n with
  | zero => intro hn wl; simp [taylorSelectProductAux, taylorBranchWord]
  | succ n ih =>
      intro hn wl
      simp only [taylorSelectProductAux, taylorBranchWord]
      rw [Matrix.mul_assoc, ih, ← Matrix.mul_assoc, taylorPosition_sector, Matrix.mul_assoc]

theorem taylorSelectProduct_branch (U : J → Matrix I I ℂ) (j0 : J) (K n : ℕ)
    (hn : n ≤ K) (wl : TaylorWordLabel J K) :
    taylorSelectProductAux U j0 K n hn * taylorBranchFrame j0 K wl =
      taylorBranchFrame j0 K wl * taylorBranchWord U K n hn wl := by
  have he : taylorBranchFrame (I := I) j0 K wl = taylorSectorFrame (I := I) K wl false j0 := by
    ext x i
    simp only [taylorBranchFrame, taylorSectorFrame, Matrix.of_apply, eq_comm]
  rw [he]
  exact taylorSelectProduct_sector U j0 K n hn wl

private theorem evaluate_taylorBlockList (U : J → Matrix I I ℂ) (j0 : J) (K : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ K),
      evaluate (taylorQuery U K) (taylorBlockList j0 K n hn) =
        taylorSelectProductAux U j0 K n hn := by
  intro n
  induction n with
  | zero => intro hn; rfl
  | succ n ih =>
      intro hn
      simp only [taylorBlockList, evaluate_append, ih, taylorQueryRouteStep,
        evaluate, instructionMatrix, Matrix.mul_one, taylorSelectProductAux]

      simp only [Matrix.mul_assoc]

private noncomputable def taylorScratchFrame (j0 : J) (K : ℕ) :
    Matrix (TaylorWordLabel J K × (Bool × (J × I))) (TaylorWordLabel J K × I) ℂ :=
  Matrix.of fun x y => if x = (y.1, (false, (j0, y.2))) then 1 else 0

private theorem taylorScratchFrame_isIsometry (j0 : J) (K : ℕ) :
    IsIsometry (taylorScratchFrame (I := I) j0 K) := by
  apply isIsometry_of_delta' (f := fun y => (y.1, (false, (j0, y.2))))
  · intro a b hab
    simpa only [Prod.mk.injEq, and_true, true_and, Prod.ext_iff] using hab
  · intro x y; rfl

private theorem taylorScratchFrame_select (j0 : J) (K : ℕ)
    (V : TaylorWordLabel J K → Matrix I I ℂ)
    (x : TaylorWordLabel J K × (Bool × (J × I))) (wl : TaylorWordLabel J K) (i : I) :
    (taylorScratchFrame (I := I) j0 K * select V) x (wl, i) =
      (taylorSectorFrame (I := I) K wl false j0 * V wl) x i := by
  simp [Matrix.mul_apply, select, taylorScratchFrame, taylorSectorFrame,
    Fintype.sum_prod_type, mul_ite]

private theorem taylorSelectProduct_scratch (U : J → Matrix I I ℂ) (j0 : J) (K : ℕ) :
    taylorSelectProductAux U j0 K K le_rfl * taylorScratchFrame (I := I) j0 K =
      taylorScratchFrame (I := I) j0 K * select (taylorBranchWord U K K le_rfl) := by
  ext x ⟨wl, i⟩
  rw [taylorScratchFrame_select]
  change (taylorSelectProductAux U j0 K K le_rfl * taylorSectorFrame (I := I) K wl false j0) x i = _
  rw [taylorSelectProduct_sector]

private theorem taylorScratchFrame_mul {O : Type} (j0 : J) (K : ℕ)
    (V : Matrix (TaylorWordLabel J K × I) O ℂ)
    (x : TaylorWordLabel J K × (Bool × (J × I))) (y : O) :
    (taylorScratchFrame (I := I) j0 K * V) x y =
      if x.2.1 = false ∧ x.2.2.1 = j0 then V (x.1, x.2.2.2) y else 0 := by
  rcases x with ⟨wl, b, j, d⟩
  cases b <;> by_cases hj : j = j0
  · have hs : ∀ z, taylorScratchFrame (I := I) j0 K (wl, false, j, d) z =
        if z = (wl, d) then 1 else 0 := by
      intro ⟨w, i⟩
      simp only [taylorScratchFrame, Matrix.of_apply, Prod.mk.injEq, hj,
        true_and, eq_comm]
    simp only [Matrix.mul_apply, hs, ite_mul, one_mul, zero_mul]
    simp [hj]
  all_goals simp [Matrix.mul_apply, taylorScratchFrame, hj]

private theorem taylorTensor_scratch {K : ℕ}
    (A : Matrix (TaylorWordLabel J K) (TaylorWordLabel J K) ℂ) (j0 : J) :
    TensorGate A (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ) *
        taylorScratchFrame (I := I) j0 K =
      taylorScratchFrame (I := I) j0 K * TensorGate A (1 : Matrix I I ℂ) := by
  ext ⟨wl, b, j, d⟩ ⟨w, i⟩
  rw [taylorScratchFrame_mul]
  change (TensorGate A (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ) *
    taylorSectorFrame (I := I) K w false j0) (wl, b, j, d) i = _
  rw [mul_taylorSectorFrame]
  by_cases hb : b = false <;> by_cases hj : j = j0 <;>
    simp [tensorGate_apply, Matrix.one_apply, hb, hj]

private theorem taylorPrepare_frame (h : J → ℝ) (τ : ℝ) (K : ℕ) (j0 : J) :
    TensorGate (taylorPrepare h τ K) (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ) *
        taylorFrame (I := I) j0 K =
      taylorScratchFrame (I := I) j0 K *
        prepareLift (I := I) (fun w => (taylorAmplitudeReal h τ K w : ℂ)) := by
  ext ⟨wl, b, j, d⟩ i
  change (TensorGate (taylorPrepare h τ K) (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ) *
    taylorSectorFrame (I := I) K (taylorEmptyLabel J K) false j0) (wl, b, j, d) i = _
  rw [mul_taylorSectorFrame]
  rw [taylorScratchFrame_mul]
  cases b <;> by_cases hj : j = j0 <;>
    simp [tensorGate_apply, taylorPrepare_column, taylorAmplitudeReal,
      Matrix.one_apply, prepareLift, hj]

private theorem evaluate_taylorLCUWord (h : J → ℝ) (U : J → Matrix I I ℂ)
    (j0 : J) (τ : ℝ) (K : ℕ) :
    evaluate (taylorQuery U K) (taylorLCUWord h j0 τ K) =
      taylorLCUUnitary h U j0 τ K := by
  simp only [taylorLCUWord, evaluate_append, evaluate_taylorBlockList,
    evaluate, instructionMatrix, Matrix.mul_one, taylorLCUUnitary, Matrix.mul_assoc]

private theorem taylorPhase_select (h : J → ℝ) (τ : ℝ) (K : ℕ)
    (B : TaylorWordLabel J K → Matrix I I ℂ) :
    TensorGate (taylorPhaseGate h τ K) (1 : Matrix I I ℂ) * select B =
      select (phaseAbsorbed (taylorCoeff h τ K) B) := by
  have he : TensorGate (taylorPhaseGate h τ K) (1 : Matrix I I ℂ) =
      select (fun w => coefficientPhase (taylorCoeff h τ K w) • (1 : Matrix I I ℂ)) := by
    ext ⟨w, i⟩ ⟨v, j⟩
    by_cases hw : w = v <;>
      simp [taylorPhaseGate, tensorGate_apply, select, Matrix.smul_apply, hw]
  rw [he, parallel_select_mul]
  congr 1
  funext w
  simp [phaseAbsorbed]

private theorem taylor_lcu_corner_sum_mass (h : J → ℝ) (U : J → Matrix I I ℂ)
    (j0 : J) (τ : ℝ) (K : ℕ) (hm : ∑ x, ‖taylorCoeff h τ K x‖ = 2) :
    compress (taylorFrame (I := I) j0 K) (evaluate (taylorQuery U K) (taylorLCUWord h j0 τ K))
        (taylorFrame (I := I) j0 K) =
      ∑ w, (taylorCoeff h τ K w / 2) • taylorBranchWord U K K le_rfl w := by
  let P := TensorGate (taylorPrepare h τ K)
    (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ)
  let S := taylorScratchFrame (I := I) j0 K
  let a := fun w => (taylorAmplitudeReal h τ K w : ℂ)
  let F : Matrix (TaylorWordLabel J K × I) I ℂ := prepareLift a
  let D := TensorGate (taylorPhaseGate h τ K)
    (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ)
  let B := taylorBranchWord U K K le_rfl
  have hPF : P * taylorFrame (I := I) j0 K = S * F := taylorPrepare_frame h τ K j0
  have hS : Sᴴ * S = 1 := taylorScratchFrame_isIsometry j0 K
  have hD : D * S = S * TensorGate (taylorPhaseGate h τ K) (1 : Matrix I I ℂ) :=
    taylorTensor_scratch _ j0
  have hB : taylorSelectProductAux U j0 K K le_rfl * S = S * select B :=
    taylorSelectProduct_scratch U j0 K
  have hA : a = coefficientAmplitude (taylorCoeff h τ K) := by
    funext w
    simp only [a, taylorAmplitudeReal, coefficientAmplitude, coefficientMass, hm]
  have hmm : coefficientMass (taylorCoeff h τ K) = 2 := hm
  have hE : evaluate (taylorQuery U K) (taylorLCUWord h j0 τ K) =
      Pᴴ * D * taylorSelectProductAux U j0 K K le_rfl * P := by
    rw [evaluate_taylorLCUWord]
    simp only [taylorLCUUnitary, P, D, tensorGate_conjTranspose, Matrix.conjTranspose_one]
  calc
    _ = (P * taylorFrame (I := I) j0 K)ᴴ * D * taylorSelectProductAux U j0 K K le_rfl *
        (P * taylorFrame (I := I) j0 K) := by
      simp only [compress, hE, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Fᴴ * Sᴴ * D * taylorSelectProductAux U j0 K K le_rfl * S * F := by
      rw [hPF]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Fᴴ * (Sᴴ * (D * S)) * select B * F := by
      simp only [Matrix.mul_assoc, hB]
    _ = Fᴴ * (Sᴴ * S) * (TensorGate (taylorPhaseGate h τ K) (1 : Matrix I I ℂ) *
        select B) * F := by rw [hD]; simp only [Matrix.mul_assoc]
    _ = compress F (select (phaseAbsorbed (taylorCoeff h τ K) B)) F := by
      rw [hS, taylorPhase_select]
      simp only [compress, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by
      simp only [F]
      rw [prepare_select_compress, hA, coefficientLCU_matrix _ _ (by rw [hmm]; norm_num)]
      simp only [hmm, Complex.ofReal_ofNat, B]

private theorem taylor_lcu_corner_sum (h : J → ℝ) (U : J → Matrix I I ℂ)
    (j0 : J) (τ : ℝ) (K : ℕ) (hτ : taylorLambda h * |τ| ≤ 1 / 2) :
    compress (taylorFrame (I := I) j0 K) (evaluate (taylorQuery U K) (taylorLCUWord h j0 τ K))
        (taylorFrame (I := I) j0 K) =
      ∑ w, (taylorCoeff h τ K w / 2) • taylorBranchWord U K K le_rfl w :=
  taylor_lcu_corner_sum_mass h U j0 τ K (taylor_sum_norm_eq_two h τ K hτ)

private noncomputable def taylorMatrixWord (U : J → Matrix I I ℂ) :
    (l : ℕ) → (Fin l → J) → Matrix I I ℂ
  | 0, _ => 1
  | l + 1, w => U (w (Fin.last l)) * taylorMatrixWord U l (fun i => w i.castSucc)

private theorem taylorBranchWord_prefix (U : J → Matrix I I ℂ) (K : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ K) (l : Fin (K + 1)) (w : Fin l.val → J) (hl : n ≤ l.val),
      taylorBranchWord U K n hn (Sum.inl ⟨l, w⟩) =
        taylorMatrixWord U n (fun i => w ⟨i.val, lt_of_lt_of_le i.isLt hl⟩) := by
  intro n
  induction n with
  | zero => intro hn l w hl; rfl
  | succ n ih =>
      intro hn l w hl
      have hj : n < l.val := Nat.lt_of_succ_le hl
      simp only [taylorBranchWord, taylorBranchStep, dif_pos hj, taylorMatrixWord]
      rw [ih (Nat.le_of_succ_le hn) l w (Nat.le_of_succ_le hl)]
      rfl

private theorem taylorBranchWord_saturated (U : J → Matrix I I ℂ) (K : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ K) (l : Fin (K + 1)) (w : Fin l.val → J) (_hl : l.val ≤ n),
      taylorBranchWord U K n hn (Sum.inl ⟨l, w⟩) = taylorMatrixWord U l.val w := by
  intro n
  induction n with
  | zero =>
      intro hn l w hl
      rcases l with ⟨l, hlK⟩
      have he : l = 0 := Nat.eq_zero_of_le_zero hl
      subst l
      rfl
  | succ n ih =>
      intro hn l w hl
      rcases l with ⟨l, hlK⟩
      change l ≤ n + 1 at hl
      by_cases he : l = n + 1
      · subst l
        exact taylorBranchWord_prefix U K (n + 1) hn ⟨n + 1, hlK⟩ w le_rfl
      · have hln : l ≤ n := by omega
        have hj : ¬ n < l := by omega
        simp only [taylorBranchWord, taylorBranchStep, dif_neg hj, Matrix.one_mul]
        exact ih (Nat.le_of_succ_le hn) ⟨l, hlK⟩ w hln

private theorem taylorBranchWord_padding (U : J → Matrix I I ℂ) (K : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ K) (b : Bool), taylorBranchWord U K n hn (Sum.inr b) = 1 := by
  intro n
  induction n with
  | zero => intro hn b; rfl
  | succ n ih => intro hn b; simp [taylorBranchWord, taylorBranchStep, ih]

private theorem taylor_sum_matrix_words (h : J → ℝ) (U : J → Matrix I I ℂ) (l : ℕ) :
    ∑ w : Fin l → J, (∏ i, (h (w i) : ℂ)) • taylorMatrixWord U l w =
      (∑ j, (h j : ℂ) • U j) ^ l := by
  induction l with
  | zero => simp [taylorMatrixWord]
  | succ l ih =>
      rw [← (Fin.snocEquiv (fun _ : Fin (l + 1) => J)).sum_comp,
        Fintype.sum_prod_type]
      simp only [Fin.snocEquiv_apply, taylorMatrixWord, Fin.snoc_last, Fin.snoc_castSucc,
        Fin.prod_univ_castSucc]
      calc
        _ = ∑ j, (h j : ℂ) • U j *
            (∑ w : Fin l → J, (∏ i, (h (w i) : ℂ)) • taylorMatrixWord U l w) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = _ := by rw [ih, ← Finset.sum_mul, pow_succ']

private theorem taylor_coefficient_matrix_sum (h : J → ℝ) (U : J → Matrix I I ℂ)
    (τ : ℝ) (K : ℕ) :
    ∑ wl, taylorCoeff h τ K wl • taylorBranchWord U K K le_rfl wl =
      Polynomial.aeval (∑ j, (h j : ℂ) • U j) (exponentialTaylorPolynomial τ (K + 1)) := by
  have hpad : ∑ b : Bool, taylorCoeff h τ K (Sum.inr b) •
      taylorBranchWord U K K le_rfl (Sum.inr b) = 0 := by
    simp only [taylorBranchWord_padding, taylorCoeff, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte]
    module
  rw [Fintype.sum_sum_type, hpad, add_zero, Fintype.sum_sigma,
    aeval_exponentialTaylorPolynomial]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro l _
  have hb (w : Fin l.val → J) :
      taylorBranchWord U K K le_rfl (Sum.inl ⟨l, w⟩) = taylorMatrixWord U l.val w :=
    taylorBranchWord_saturated U K K le_rfl l w (by omega)
  simp only [taylorCoeff_inl, hb, taylorWordCoefficient, mul_smul]
  rw [← Finset.smul_sum, taylor_sum_matrix_words]
  simp only [_root_.smul_pow, smul_smul, div_eq_mul_inv, mul_comm]

theorem taylor_actual_lcu_corner_polynomial (h : J → ℝ) (U : J → Matrix I I ℂ)
    (j0 : J) (τ : ℝ) (K : ℕ) (_hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ)
    (hτ : (∑ j, |h j|) * |τ| ≤ 1 / 2) :
    compress (taylorFrame j0 K) (evaluate (taylorQuery U K) (taylorLCUWord h j0 τ K))
        (taylorFrame j0 K) =
      (1 / 2 : ℂ) • Polynomial.aeval (∑ j, (h j : ℂ) • U j)
        (exponentialTaylorPolynomial τ (K + 1)) := by
  rw [taylor_lcu_corner_sum h U j0 τ K hτ, ← taylor_coefficient_matrix_sum h U τ K,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [smul_smul]
  congr 1
  ring

set_option maxHeartbeats 800000 in

theorem taylor_derived_matrix_exponential_remainder
    (h : J → ℝ) (U : J → Matrix I I ℂ) (τ : ℝ) (K : ℕ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ ∧ (U j).IsHermitian)
    (hτ : (∑ j, |h j|) * |τ| ≤ 1 / 2) :
    ‖Polynomial.aeval (∑ j, (h j : ℂ) • U j) (exponentialTaylorPolynomial τ (K + 1)) -
      hamiltonianEvolution (∑ j, (h j : ℂ) • U j) τ‖ ≤ (1 / 2 : ℝ) ^ K := by
  let H : Matrix I I ℂ := ∑ j, (h j : ℂ) • U j
  let X : Matrix I I ℂ := (-Complex.I * (τ : ℂ)) • H
  have hH : ‖H‖ ≤ ∑ j, |h j| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (l2_norm_unitary_le_one (hU j).1)
  have hX : ‖X‖ ≤ 1 / 2 := by
    have hc : ‖-Complex.I * (τ : ℂ)‖ = |τ| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    calc ‖X‖ = |τ| * ‖H‖ := by rw [norm_smul, hc]
      _ ≤ |τ| * ∑ j, |h j| := mul_le_mul_of_nonneg_left hH (abs_nonneg _)
      _ ≤ 1 / 2 := by simpa [mul_comm] using hτ
  let f : ℕ → Matrix I I ℂ := fun n => (n.factorial : ℂ)⁻¹ • X ^ n
  have hf : Summable f := NormedSpace.expSeries_summable' X
  have hfn : Summable fun n => ‖f n‖ := NormedSpace.norm_expSeries_summable' X
  have ht : ∑' n, f n = NormedSpace.exp X := (NormedSpace.exp_series_hasSum_exp' X).tsum_eq
  have htail : NormedSpace.exp X - ∑ n ∈ Finset.range (K + 1), f n =
      ∑' n, f (n + (K + 1)) := by
    have hs := hf.sum_add_tsum_nat_add (K + 1)
    rw [ht] at hs
    exact eq_sub_of_add_eq' hs |>.symm
  have hterm : ∀ n, 0 < n → ‖f n‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro n hnpos
    have hfact : (1 : ℝ) ≤ n.factorial := by exact_mod_cast n.factorial_pos
    calc ‖f n‖ = (n.factorial : ℝ)⁻¹ * ‖X ^ n‖ := by
          simp [f, norm_smul, norm_inv]
      _ ≤ (n.factorial : ℝ)⁻¹ * ‖X‖ ^ n :=
          mul_le_mul_of_nonneg_left (norm_pow_le' X hnpos) (by positivity)
      _ ≤ (n.factorial : ℝ)⁻¹ * (1 / 2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hX _) (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ n := by
          exact mul_le_of_le_one_left (by positivity) ((inv_le_one₀ (by positivity)).2 hfact)
  have hn : Summable fun n => ‖f (n + (K + 1))‖ := (summable_nat_add_iff _).2 hfn
  have hg : Summable fun n => (1 / 2 : ℝ) ^ (n + (K + 1)) :=
    (summable_nat_add_iff _).2 (summable_geometric_of_norm_lt_one (by norm_num))
  rw [aeval_exponentialTaylorPolynomial, norm_sub_rev]
  change ‖NormedSpace.exp X - ∑ n ∈ Finset.range (K + 1), f n‖ ≤ _
  rw [htail]
  calc ‖∑' n, f (n + (K + 1))‖ ≤ ∑' n, ‖f (n + (K + 1))‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, (1 / 2 : ℝ) ^ (n + (K + 1)) := hn.tsum_le_tsum (fun n => hterm _ (by omega)) hg
    _ = (1 / 2 : ℝ) ^ K := by
      simp only [pow_add]
      rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      simp [pow_succ]
      ring

theorem taylorLCUWord_counts (h : J → ℝ) (j0 : J) (τ : ℝ) (K : ℕ) :
    adjointQueryCount (taylorLCUWord (I := I) h j0 τ K) = K ∧
      adjointGateCount (taylorLCUWord (I := I) h j0 τ K) = 2 * K + 3 := by
  obtain ⟨hq, hg⟩ := counts_taylorBlockList (I := I) j0 K K le_rfl
  simp only [taylorLCUWord, adjointQueryCount_append, adjointGateCount_append,
    hq, hg, adjointQueryCount, adjointGateCount]
  constructor <;> omega

theorem taylor_actual_scale_two_evolution_encoding (h : J → ℝ) (U : J → Matrix I I ℂ)
    (j0 : J) (τ : ℝ) (K : ℕ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ ∧ (U j).IsHermitian)
    (hτ : (∑ j, |h j|) * |τ| ≤ 1 / 2) :
    BlockEncoding (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) τ)
      (evaluate (taylorQuery U K) (taylorLCUWord h j0 τ K))
      (taylorFrame j0 K) (taylorFrame j0 K) 2 ((1 / 2 : ℝ) ^ K) := by
  have hbody := (taylor_lcu_actual_prepare_select_and_counts (I := I) h j0 τ K hτ).2.1
  refine ⟨hbody.evaluate_unitary (taylorQuery_unitary U (fun j => (hU j).1) K),
    taylorFrame_isIsometry j0 K, taylorFrame_isIsometry j0 K, by norm_num,
    by positivity, ?_⟩
  rw [taylor_actual_lcu_corner_polynomial h U j0 τ K (fun j => (hU j).1) hτ,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  norm_num
  rw [norm_sub_rev]
  exact taylor_derived_matrix_exponential_remainder h U τ K hU hτ

theorem taylorS0_le_two_ln2 {J : Type} [Fintype J] [DecidableEq J]
    (h : J → ℝ) (τ : ℝ) (K : ℕ)
    (hτ : taylorLambda h * |τ| ≤ Real.log 2) :
    taylorS0 h τ K ≤ 2 := by
  have hpos : 0 ≤ taylorLambda h * |τ| :=
    mul_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (abs_nonneg _)
  have hsum : Summable fun n : ℕ => (taylorLambda h * |τ|) ^ n / n.factorial :=
    Real.summable_pow_div_factorial _
  have he : (∑' n : ℕ, (taylorLambda h * |τ|) ^ n / n.factorial)
      = Real.exp (taylorLambda h * |τ|) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    congr 1
    funext n
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  calc taylorS0 h τ K = ∑ l ∈ Finset.range (K + 1), (taylorLambda h * |τ|) ^ l / l.factorial :=
        rfl
    _ ≤ ∑' n : ℕ, (taylorLambda h * |τ|) ^ n / n.factorial :=
        hsum.sum_le_tsum _
          (fun l _ => div_nonneg (pow_nonneg hpos _) (by positivity))
    _ = Real.exp (taylorLambda h * |τ|) := he
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hτ
    _ = 2 := Real.exp_log (by norm_num)

theorem taylor_sum_norm_eq_two_ln2 {J : Type} [Fintype J] [DecidableEq J]
    (h : J → ℝ) (τ : ℝ) (K : ℕ)
    (hτ : taylorLambda h * |τ| ≤ Real.log 2) :
    ∑ x, ‖taylorCoeff h τ K x‖ = 2 := by
  have hs0 := taylorS0_le_two_ln2 h τ K hτ
  have hpad : (0 : ℝ) ≤ 2 - taylorS0 h τ K := by linarith
  have hinl : ∑ w : Σ l : Fin (K + 1), Fin l.val → J, ‖taylorWordCoefficient h τ w‖
      = taylorS0 h τ K := by
    rw [Fintype.sum_sigma]
    have hinner : ∀ l : Fin (K + 1),
        ∑ w' : Fin l.val → J, ‖taylorWordCoefficient h τ ⟨l, w'⟩‖
          = (taylorLambda h * |τ|) ^ l.val / l.val.factorial := by
      intro l
      have hval : ∀ w' : Fin l.val → J, ‖taylorWordCoefficient h τ ⟨l, w'⟩‖
          = |τ| ^ l.val / l.val.factorial * ∏ i, |h (w' i)| := by
        intro w'
        simpa using abs_taylorWordCoefficient h τ ⟨l, w'⟩
      rw [Finset.sum_congr rfl fun w' _ => hval w', ← Finset.mul_sum,
        taylor_sum_prod_abs h l.val, mul_pow]
      ring
    rw [Finset.sum_congr rfl fun l _ => hinner l]
    rw [Fin.sum_univ_eq_sum_range
      (fun v => (taylorLambda h * |τ|) ^ v / v.factorial) (K + 1), taylorS0]
  have hinr : ∑ b : Bool, ‖taylorCoeff h τ K (Sum.inr b)‖ = 2 - taylorS0 h τ K := by
    have hnorm : ∀ z : ℝ, 0 ≤ z → ‖(z : ℂ)‖ = z := by
      intro z hz
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
    have hpdiv : (0 : ℝ) ≤ (2 - taylorS0 h τ K) / 2 := by positivity
    have hval : ∀ b : Bool, ‖taylorCoeff h τ K (Sum.inr b)‖ = (2 - taylorS0 h τ K) / 2 := by
      intro b
      cases b with
      | false =>
          rw [show taylorCoeff h τ K (Sum.inr false) = -(((2 - taylorS0 h τ K) / 2 : ℝ) : ℂ) from by
              simp only [taylorCoeff]
              push_cast
              ring, norm_neg, hnorm _ hpdiv]
      | true =>
          rw [show taylorCoeff h τ K (Sum.inr true) = (((2 - taylorS0 h τ K) / 2 : ℝ) : ℂ) from by
              simp [taylorCoeff], hnorm _ hpdiv]
    rw [Fintype.sum_bool, hval false, hval true]
    linarith
  have hinl' : ∑ w : Σ l : Fin (K + 1), Fin l.val → J, ‖taylorCoeff h τ K (Sum.inl w)‖
      = taylorS0 h τ K := by
    rw [Finset.sum_congr rfl fun w _ => by rw [taylorCoeff_inl h τ w]]
    exact hinl
  rw [Fintype.sum_sum_type, hinl', hinr]
  linarith

theorem taylorPrepare_unitary_ln2 {J : Type} [Fintype J] [DecidableEq J]
    (h : J → ℝ) (τ : ℝ) (K : ℕ)
    (hτ : taylorLambda h * |τ| ≤ Real.log 2) :
    taylorPrepare h τ K ∈ Matrix.unitaryGroup (TaylorWordLabel J K) ℂ := by
  refine nonnegativePrepare_unitary _ _ (fun _ => Real.sqrt_nonneg _) ?_
  simp only [Real.sq_sqrt (div_nonneg (norm_nonneg _) zero_le_two)]
  rw [← Finset.sum_div, taylor_sum_norm_eq_two_ln2 h τ K hτ]
  norm_num

theorem taylor_lcu_actual_prepare_select_and_counts_ln2 {J I : Type}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (h : J → ℝ) (j0 : J) (τ : ℝ) (K : ℕ)
    (hτ : (∑ j, |h j|) * |τ| ≤ Real.log 2) :
    IsIsometry (taylorFrame (I := I) j0 K) ∧
      WellFormedAdjointCircuit (taylorLCUWord (I := I) h j0 τ K) ∧
    adjointQueryCount (taylorLCUWord (I := I) h j0 τ K) = K ∧
    adjointGateCount (taylorLCUWord (I := I) h j0 τ K) = 2 * K + 3 := by
  have hlam : taylorLambda h * |τ| ≤ Real.log 2 := hτ
  have hP : taylorPrepare h τ K ∈ Matrix.unitaryGroup (TaylorWordLabel J K) ℂ :=
    taylorPrepare_unitary_ln2 h τ K hlam
  have hPw : ∀ (A : Matrix (TaylorWordLabel J K) (TaylorWordLabel J K) ℂ),
      A ∈ Matrix.unitaryGroup (TaylorWordLabel J K) ℂ →
      TensorGate A (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ) ∈
        Matrix.unitaryGroup (TaylorWordLabel J K × (Bool × (J × I))) ℂ :=
    fun A hA => tensorGate_unitary hA (Matrix.unitaryGroup _ ℂ).one_mem
  have hwf1 : WellFormedAdjointCircuit
      ([.gate (TensorGate (taylorPrepare h τ K)ᴴ
        (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ)),
        .gate (TensorGate (taylorPhaseGate h τ K)
        (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))] :
        List (AdjointStep (TaylorWordLabel J K × (Bool × (J × I))))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact ⟨hPw _ (adjoint_unitary hP), hPw _ (taylorPhaseGate_unitary h τ K)⟩
  have hwf3 : WellFormedAdjointCircuit
      ([.gate (TensorGate (taylorPrepare h τ K)
        (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))] :
        List (AdjointStep (TaylorWordLabel J K × (Bool × (J × I))))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact hPw _ hP
  have hq := counts_taylorBlockList (I := I) j0 K K le_rfl
  refine ⟨taylorFrame_isIsometry j0 K, ?_, ?_, ?_⟩
  · rw [taylorLCUWord]
    exact WellFormedAdjointCircuit.append (WellFormedAdjointCircuit.append hwf1
      (taylorBlockList_wellFormed (I := I) j0 K K le_rfl)) hwf3
  · rw [taylorLCUWord, adjointQueryCount_append, adjointQueryCount_append, hq.1]
    simp only [adjointQueryCount]
    simp
  · rw [taylorLCUWord, adjointGateCount_append, adjointGateCount_append, hq.2]
    simp only [adjointGateCount]
    omega

theorem taylor_actual_lcu_corner_polynomial_ln2 {J I : Type}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (h : J → ℝ) (U : J → Matrix I I ℂ) (j0 : J) (τ : ℝ) (K : ℕ)
    (_hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ)
    (hτ : (∑ j, |h j|) * |τ| ≤ Real.log 2) :
    compress (taylorFrame j0 K) (evaluate (taylorQuery U K) (taylorLCUWord h j0 τ K))
        (taylorFrame j0 K) =
      (1 / 2 : ℂ) • Polynomial.aeval (∑ j, (h j : ℂ) • U j)
        (exponentialTaylorPolynomial τ (K + 1)) := by
  rw [taylor_lcu_corner_sum_mass h U j0 τ K
      (taylor_sum_norm_eq_two_ln2 h τ K (by exact hτ)),
    ← taylor_coefficient_matrix_sum h U τ K, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [smul_smul]
  congr 1
  ring

end Program

end Qatlib.Concepts.CoherentSim.TaylorEncoding
