/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrtBounds
import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessExt
import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareMachine
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareRawSqrt
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessExt
open Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace output1

def tableAmps {D : ℕ} (t : DenseTable D) : Option (Fin D) → RatComplex :=
  fun a =>
    match a with
    | none => ratZero
    | some i => t i

@[simp] theorem tableAmps_none {D : ℕ} (t : DenseTable D) :
    tableAmps t none = ratZero := rfl

@[simp] theorem tableAmps_some {D : ℕ} (t : DenseTable D) (i : Fin D) :
    tableAmps t (some i) = t i := rfl

def tableReadCount (D : ℕ) : ℕ := D

theorem tableReadCount_eq (D : ℕ) : tableReadCount D = D := rfl

theorem tableMass_terms {D : ℕ} :
    (Finset.univ : Finset (Option (Fin D))).card = D + 1 := by
  simp [Fintype.card_option]

theorem tableMass_eq {D : ℕ} (t : DenseTable D) :
    rationalWeightMass (fun a => ratSq (tableAmps t a)) =
      ∑ a, ratSq (tableAmps t a) := rfl

theorem tablePrepare_state_error {D : ℕ} (k : ℕ) (ψ : QState (Option (Fin D)))
    (hψ : ‖stateVector ψ‖ = 1) (hψ0 : ψ none = 0) (t : DenseTable D)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ i : Fin D, ‖ratToComplex (t i) - ψ (some i)‖ ≤ η)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * η < 1) :
    ‖stateVector (prepareMatrix k (fun a => ratSq (tableAmps t a)) (tableAmps t) *ᵥ
        Qatlib.Foundations.PureStateMath.Ket none) - stateVector ψ‖
      ≤ 32 * (D + 1) / 2 ^ k + 2 * Real.sqrt ((D + 1 : ℝ)) * η := by
  refine generalPrepare_state_error k ψ hψ (tableAmps t) (tableAmps_none t) ?_ hgap
  intro a
  cases a with
  | none => simp [ratToComplex, ratZero, hψ0, hη0]
  | some i => exact hη i

theorem tablePrepare_state_error_epsilon {D : ℕ} (ε : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ψ : QState (Option (Fin D))) (hψ : ‖stateVector ψ‖ = 1) (hψ0 : ψ none = 0)
    (t : DenseTable D)
    (hη : ∀ i : Fin D, ‖ratToComplex (t i) - ψ (some i)‖
      ≤ (ε : ℝ) / (8 * Real.sqrt ((D + 1 : ℝ)))) :
    ‖stateVector (prepareMatrix (precisionFor D (ε / 2))
          (fun a => ratSq (tableAmps t a)) (tableAmps t) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector ψ‖ ≤ (ε : ℝ) := by
  refine generalPrepare_state_error_epsilon ε hε hε1 ψ hψ (tableAmps t)
    (tableAmps_none t) ?_
  intro a
  cases a with
  | none =>
      have hpos : 0 ≤ (ε : ℝ) / (8 * Real.sqrt ((D + 1 : ℝ))) := by positivity
      simp [ratToComplex, ratZero, hψ0, hpos]
  | some i => exact hη i

def entryBitCost (p : ℕ) : ℕ := 2 * (p + 1) + 1

def normalizationSquares (D : ℕ) : ℕ := 2 * (D + 1)

def normalizationAdds (D : ℕ) : ℕ := D

def normalizationOps (D : ℕ) : ℕ := normalizationSquares D + normalizationAdds D

def tableReadBitCost (D p : ℕ) : ℕ := tableReadCount D * entryBitCost p

def normalizationBitCost (D p : ℕ) : ℕ := normalizationOps D * (p + 1) ^ 2

def prepareChainCost (D p : ℕ) : ℕ :=
  tableReadBitCost D p + normalizationBitCost D p

theorem prepareChainCost_decomposes (D p : ℕ) :
    prepareChainCost D p = tableReadBitCost D p + normalizationBitCost D p := rfl

theorem normalizationOps_eq (D : ℕ) : normalizationOps D = 2 * (D + 1) + D := rfl

theorem prepareChainCost_le (D p : ℕ) :
    prepareChainCost D p ≤ 8 * (D + 1) * (p + 1) ^ 3 := by
  have hD : D ≤ D + 1 := by omega
  have hp : 1 ≤ p + 1 := by omega
  have hsq : (p + 1) ^ 2 ≤ (p + 1) ^ 3 := by
    calc
      (p + 1) ^ 2 = (p + 1) ^ 2 * 1 := by ring
      _ ≤ (p + 1) ^ 2 * (p + 1) := Nat.mul_le_mul_left _ hp
      _ = (p + 1) ^ 3 := by ring
  have hp3 : p + 1 ≤ (p + 1) ^ 3 := by
    calc
      p + 1 = (p + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (p + 1) * (p + 1) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow 2 (p + 1) hp)
      _ = (p + 1) ^ 3 := by ring
  have hread : tableReadBitCost D p ≤ 3 * (D + 1) * (p + 1) ^ 3 := by
    have hb : entryBitCost p ≤ 3 * (p + 1) := by
      dsimp [entryBitCost]
      omega
    calc
      tableReadBitCost D p = D * entryBitCost p := rfl
      _ ≤ D * (3 * (p + 1)) := Nat.mul_le_mul_left D hb
      _ ≤ (D + 1) * (3 * (p + 1)) := Nat.mul_le_mul_right _ hD
      _ ≤ (D + 1) * (3 * (p + 1) ^ 3) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 hp3)
      _ = 3 * (D + 1) * (p + 1) ^ 3 := by ring
  have hnorm : normalizationBitCost D p ≤ 3 * (D + 1) * (p + 1) ^ 3 := by
    have hm : normalizationOps D ≤ 3 * (D + 1) := by
      dsimp [normalizationOps, normalizationSquares, normalizationAdds]
      omega
    calc
      normalizationBitCost D p = normalizationOps D * (p + 1) ^ 2 := rfl
      _ ≤ (3 * (D + 1)) * (p + 1) ^ 2 := Nat.mul_le_mul_right _ hm
      _ ≤ (3 * (D + 1)) * (p + 1) ^ 3 := Nat.mul_le_mul_left _ hsq
      _ = 3 * (D + 1) * (p + 1) ^ 3 := by ring
  calc
    prepareChainCost D p = tableReadBitCost D p + normalizationBitCost D p := rfl
    _ ≤ 3 * (D + 1) * (p + 1) ^ 3 + 3 * (D + 1) * (p + 1) ^ 3 :=
      Nat.add_le_add hread hnorm
    _ = 6 * (D + 1) * (p + 1) ^ 3 := by ring
    _ ≤ 8 * (D + 1) * (p + 1) ^ 3 := by
      simpa only [Nat.mul_assoc] using!
        (Nat.mul_le_mul_right ((D + 1) * (p + 1) ^ 3) (by omega : 6 ≤ 8))

noncomputable def sqrtTarget {D : ℕ} (q : Fin D → ℚ) : QState (Option (Fin D)) :=
  fun a => match a with
    | none => 0
    | some i => ((Real.sqrt (q i : ℝ) : ℝ) : ℂ)

@[simp] theorem sqrtTarget_none {D : ℕ} (q : Fin D → ℚ) :
    sqrtTarget q none = 0 := rfl

@[simp] theorem sqrtTarget_some {D : ℕ} (q : Fin D → ℚ) (i : Fin D) :
    sqrtTarget q (some i) = ((Real.sqrt (q i : ℝ) : ℝ) : ℂ) := rfl

theorem norm_sqrtTarget_sq {D : ℕ} (q : Fin D → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ‖stateVector (sqrtTarget q)‖ ^ 2 = ∑ i, (q i : ℝ) := by
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.stateVector_norm_sq_sum, Fintype.sum_option]
  simp only [sqrtTarget_none, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [sqrtTarget_some, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (show (0 : ℝ) ≤ (q i : ℝ) by exact_mod_cast hq i)]

theorem normalized_sqrtTarget {D : ℕ} (q : Fin D → ℚ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, (q i : ℝ) = 1) :
    ‖stateVector (sqrtTarget q)‖ = 1 := by
  have hsq := norm_sqrtTarget_sq q hq
  rw [hsum] at hsq
  have hn := norm_nonneg (stateVector (sqrtTarget q))
  nlinarith

def bracketTable {D : ℕ} (q : Fin D → ℚ) (S : ℚ) (k : ℕ) : DenseTable D :=
  fun i => (sqrtLo (q i) S k, 0)

theorem bracketTable_eta {D : ℕ} (q : Fin D → ℚ) (S : ℚ) (k : ℕ) (hS : 0 < S)
    (hq : ∀ i, 0 ≤ q i) (hSq : ∀ i, q i ≤ S * S) :
    ∀ i : Fin D,
      ‖ratToComplex (bracketTable q S k i) - sqrtTarget q (some i)‖
        ≤ ((S / (2 : ℚ) ^ k : ℚ) : ℝ) := by
  intro i
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    sqrtInterval_certified (q i) S k hS (hq i) (hSq i)
  have hw : ((sqrtHi (q i) S k : ℚ) : ℝ) - ((sqrtLo (q i) S k : ℚ) : ℝ)
      = ((S / (2 : ℚ) ^ k : ℚ) : ℝ) := by
    exact_mod_cast h6
  have hdiff : ratToComplex (bracketTable q S k i) - sqrtTarget q (some i)
      = ((((sqrtLo (q i) S k : ℚ) : ℝ) - Real.sqrt (q i : ℝ) : ℝ) : ℂ) := by
    simp only [bracketTable, ratToComplex, sqrtTarget]
    push_cast
    ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_sub_le_iff]
  constructor <;> linarith

theorem bracketTablePrepare_state_error {D : ℕ} (q : Fin D → ℚ) (S : ℚ) (k : ℕ)
    (hS : 0 < S) (hq : ∀ i, 0 ≤ q i) (hSq : ∀ i, q i ≤ S * S)
    (hsum : ∑ i, (q i : ℝ) = 1)
    (hgap : Real.sqrt ((D + 1 : ℝ)) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ) < 1) :
    ‖stateVector (prepareMatrix k
          (fun a => ratSq (tableAmps (bracketTable q S k) a))
          (tableAmps (bracketTable q S k)) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (sqrtTarget q)‖
      ≤ 32 * (D + 1) / 2 ^ k
          + 2 * Real.sqrt ((D + 1 : ℝ)) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ) := by
  have hψ : ‖stateVector (sqrtTarget q)‖ = 1 := normalized_sqrtTarget q hq hsum
  have hψ0 : sqrtTarget q none = 0 := rfl
  have hη0 : (0 : ℝ) ≤ ((S / (2 : ℚ) ^ k : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ S / (2 : ℚ) ^ k := by positivity
    exact_mod_cast this
  exact tablePrepare_state_error (D := D) k (sqrtTarget q) hψ hψ0 (bracketTable q S k)
    hη0 (bracketTable_eta q S k hS hq hSq) hgap

theorem bracketTablePrepare_state_error_width {D : ℕ} (q : Fin D → ℚ) (S : ℚ)
    (hS : 0 < S) (hq : ∀ i, 0 ≤ q i) (hSq : ∀ i, q i ≤ S * S)
    (hsum : ∑ i, (q i : ℝ) = 1) (b : ℕ)
    (hgap : Real.sqrt ((D + 1 : ℝ)) / 2 ^ b < 1) :
    ‖stateVector (prepareMatrix (widthPrecision S b)
          (fun a => ratSq (tableAmps (bracketTable q S (widthPrecision S b)) a))
          (tableAmps (bracketTable q S (widthPrecision S b))) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (sqrtTarget q)‖
      ≤ (32 * (D + 1) + 2 * Real.sqrt ((D + 1 : ℝ))) / 2 ^ b := by
  have hw := widthPrecision_spec S hS b
  have hwp : b ≤ widthPrecision S b := by unfold widthPrecision; omega
  have hcast : ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ) ≤ 1 / (2 : ℝ) ^ b := by
    have hcast' : ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ)
        ≤ ((1 / (2 : ℚ) ^ b : ℚ) : ℝ) := by
      exact_mod_cast hw
    simpa using! hcast'
  have hgapsqrt : Real.sqrt ((D + 1 : ℝ)) *
      ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ) < 1 := by
    have hs : (0 : ℝ) ≤ Real.sqrt ((D + 1 : ℝ)) := Real.sqrt_nonneg _
    have hle := mul_le_mul_of_nonneg_left hcast hs
    have h2 : Real.sqrt ((D + 1 : ℝ)) * (1 / (2 : ℝ) ^ b)
        = Real.sqrt ((D + 1 : ℝ)) / 2 ^ b := by ring
    linarith
  have hmain := bracketTablePrepare_state_error q S (widthPrecision S b) hS hq hSq
    hsum hgapsqrt
  have h1 : 32 * ((D : ℝ) + 1) / 2 ^ widthPrecision S b
      ≤ 32 * ((D : ℝ) + 1) / 2 ^ b := by
    refine div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 32 * ((D : ℝ) + 1) by positivity)
      (show (0 : ℝ) < 2 ^ b by positivity) ?_
    exact pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hwp
  have h2 : 2 * Real.sqrt ((D + 1 : ℝ)) *
        ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ)
      ≤ 2 * Real.sqrt ((D + 1 : ℝ)) * (1 / 2 ^ b) := by
    refine mul_le_mul_of_nonneg_left hcast
        (show (0 : ℝ) ≤ 2 * Real.sqrt ((D + 1 : ℝ)) by positivity)
  have h3 : 2 * Real.sqrt ((D + 1 : ℝ)) * (1 / 2 ^ b)
      = 2 * Real.sqrt ((D + 1 : ℝ)) / 2 ^ b := by ring
  calc
    _ ≤ 32 * ((D : ℝ) + 1) / 2 ^ widthPrecision S b +
          2 * Real.sqrt ((D + 1 : ℝ)) *
            ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ) := hmain
    _ ≤ 32 * ((D : ℝ) + 1) / 2 ^ b
          + 2 * Real.sqrt ((D + 1 : ℝ)) * (1 / 2 ^ b) := by
      linarith
    _ = (32 * ((D : ℝ) + 1) + 2 * Real.sqrt ((D + 1 : ℝ))) / 2 ^ b := by ring

theorem frontier1 :
    ((∀ (D : ℕ) (t : DenseTable D), tableAmps t none = ratZero ∧
        (∀ i : Fin D, tableAmps t (some i) = t i) ∧
        (Finset.univ : Finset (Option (Fin D))).card = D + 1 ∧
        rationalWeightMass (fun a => ratSq (tableAmps t a)) =
          ∑ a, ratSq (tableAmps t a))) ∧
    (∀ (D : ℕ) (k : ℕ) (ψ : QState (Option (Fin D)))
        (_hψ : ‖stateVector ψ‖ = 1) (_hψ0 : ψ none = 0) (t : DenseTable D)
        (η : ℝ), 0 ≤ η →
        (∀ i : Fin D, ‖ratToComplex (t i) - ψ (some i)‖ ≤ η) →
        Real.sqrt ((D + 1 : ℝ)) * η < 1 →
        ‖stateVector (prepareMatrix k (fun a => ratSq (tableAmps t a)) (tableAmps t) *ᵥ
            Qatlib.Foundations.PureStateMath.Ket none) - stateVector ψ‖
          ≤ 32 * (D + 1) / 2 ^ k + 2 * Real.sqrt ((D + 1 : ℝ)) * η) ∧
    (∀ (D : ℕ) (ε : ℚ), 0 < ε → ε ≤ 1 →
        ∀ (ψ : QState (Option (Fin D))) (_hψ : ‖stateVector ψ‖ = 1)
          (_hψ0 : ψ none = 0) (t : DenseTable D),
        (∀ i : Fin D, ‖ratToComplex (t i) - ψ (some i)‖
          ≤ (ε : ℝ) / (8 * Real.sqrt ((D + 1 : ℝ)))) →
        ‖stateVector (prepareMatrix (precisionFor D (ε / 2))
              (fun a => ratSq (tableAmps t a)) (tableAmps t) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
            - stateVector ψ‖ ≤ (ε : ℝ)) ∧
    (∀ D p : ℕ,
      prepareChainCost D p = tableReadBitCost D p + normalizationBitCost D p ∧
        normalizationOps D = 2 * (D + 1) + D ∧
        tableReadCount D = D ∧
        prepareChainCost D p ≤ 8 * (D + 1) * (p + 1) ^ 3) ∧
    (∀ (D : ℕ) (q : Fin D → ℚ) (S : ℚ) (k : ℕ), 0 < S →
      (∀ i, 0 ≤ q i) → (∀ i, q i ≤ S * S) → (∑ i, (q i : ℝ) = 1) →
      Real.sqrt ((D + 1 : ℝ)) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ) < 1 →
      ‖stateVector (prepareMatrix k
            (fun a => ratSq (tableAmps (bracketTable q S k) a))
            (tableAmps (bracketTable q S k)) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (sqrtTarget q)‖
        ≤ 32 * (D + 1) / 2 ^ k
            + 2 * Real.sqrt ((D + 1 : ℝ)) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)) ∧
    (∀ (D : ℕ) (q : Fin D → ℚ) (S : ℚ), 0 < S →
      (∀ i, 0 ≤ q i) → (∀ i, q i ≤ S * S) → (∑ i, (q i : ℝ) = 1) →
      ∀ b : ℕ, Real.sqrt ((D + 1 : ℝ)) / 2 ^ b < 1 →
      ‖stateVector (prepareMatrix (widthPrecision S b)
            (fun a => ratSq (tableAmps (bracketTable q S (widthPrecision S b)) a))
            (tableAmps (bracketTable q S (widthPrecision S b))) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (sqrtTarget q)‖
        ≤ (32 * (D + 1) + 2 * Real.sqrt ((D + 1 : ℝ))) / 2 ^ b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro D t
    exact ⟨tableAmps_none t, tableAmps_some t, tableMass_terms, tableMass_eq t⟩
  · intro D k ψ hψ hψ0 t η hη0 hη hgap
    exact tablePrepare_state_error k ψ hψ hψ0 t hη0 hη hgap
  · intro D ε hε hε1 ψ hψ hψ0 t hη
    exact tablePrepare_state_error_epsilon ε hε hε1 ψ hψ hψ0 t hη
  · intro D p
    exact ⟨prepareChainCost_decomposes D p, normalizationOps_eq D,
      tableReadCount_eq D, prepareChainCost_le D p⟩
  · intro D q S k hS hq hSq hsum hgap
    exact bracketTablePrepare_state_error q S k hS hq hSq hsum hgap
  · intro D q S hS hq hSq hsum b hgap
    exact bracketTablePrepare_state_error_width q S hS hq hSq hsum b hgap

noncomputable def normTarget {D : ℕ} (q : Fin D → ℚ) (m : ℝ) :
    QState (Option (Fin D)) :=
  fun a =>
    match a with
    | none => 0
    | some i => ((Real.sqrt ((q i : ℝ) / m) : ℝ) : ℂ)

@[simp] theorem normTarget_none {D : ℕ} (q : Fin D → ℚ) (m : ℝ) :
    normTarget q m none = 0 := rfl

@[simp] theorem normTarget_some {D : ℕ} (q : Fin D → ℚ) (m : ℝ) (i : Fin D) :
    normTarget q m (some i) = ((Real.sqrt ((q i : ℝ) / m) : ℝ) : ℂ) := rfl

theorem norm_normTarget {D : ℕ} (q : Fin D → ℚ) (hq : ∀ i, 0 ≤ q i)
    {m : ℝ} (hm : 0 < m) (hsum : ∑ i, (q i : ℝ) = m) :
    ‖stateVector (normTarget q m)‖ = 1 := by
  have hsq : ‖stateVector (normTarget q m)‖ ^ 2 = 1 := by
    rw [Qatlib.Concepts.LocalMachine.LocalTransport.stateVector_norm_sq_sum, Fintype.sum_option]
    have hterm : ∀ i : Fin D, ‖normTarget q m (some i)‖ ^ 2 = (q i : ℝ) / m := by
      intro i
      have hnn : (0 : ℝ) ≤ (q i : ℝ) / m := div_nonneg (by exact_mod_cast hq i) hm.le
      rw [normTarget_some, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hnn]
    simp only [normTarget_none, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_div, hsum,
      div_self (ne_of_gt hm)]
  nlinarith [norm_nonneg (stateVector (normTarget q m))]

def scaledBracketTable {D : ℕ} (q : Fin D → ℚ) (S r : ℚ) (k : ℕ) : DenseTable D :=
  fun i => (sqrtLo (q i) S k * r, 0)

theorem scaledBracketTable_eta {D : ℕ} (q : Fin D → ℚ) (S r : ℚ) (k : ℕ)
    (hS : 0 < S) (hq : ∀ i, 0 ≤ q i) (hSq : ∀ i, q i ≤ S * S)
    (hr : 0 ≤ r) {m : ℝ} (_hm : 0 < m) :
    ∀ i : Fin D,
      ‖ratToComplex (scaledBracketTable q S r k i) - normTarget q m (some i)‖
        ≤ (r : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
            + (S : ℝ) * |(r : ℝ) - 1 / Real.sqrt m| := by
  intro i
  obtain ⟨hlo0, hlohi, hhiS, -, -, hwidth, hloRoot, hrootHi⟩ :=
    sqrtInterval_certified (q i) S k hS (hq i) (hSq i)
  have hqcast : (0 : ℝ) ≤ (q i : ℝ) := by exact_mod_cast hq i
  have hrR : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hw : ((sqrtHi (q i) S k : ℚ) : ℝ) - ((sqrtLo (q i) S k : ℚ) : ℝ)
      = ((S / (2 : ℚ) ^ k : ℚ) : ℝ) := by exact_mod_cast hwidth
  have hroot_le_S : Real.sqrt (q i : ℝ) ≤ (S : ℝ) := by
    have hhi : ((sqrtHi (q i) S k : ℚ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast hhiS
    exact hrootHi.trans hhi
  have hlo_abs : |((sqrtLo (q i) S k : ℚ) : ℝ) - Real.sqrt (q i : ℝ)|
      ≤ ((S / (2 : ℚ) ^ k : ℚ) : ℝ) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hsqrt_div : Real.sqrt ((q i : ℝ) / m) = Real.sqrt (q i : ℝ) / Real.sqrt m :=
    Real.sqrt_div hqcast m
  have hcast_entry : ((sqrtLo (q i) S k * r : ℚ) : ℝ)
      = ((sqrtLo (q i) S k : ℚ) : ℝ) * (r : ℝ) := by push_cast; ring
  have halg : ((sqrtLo (q i) S k * r : ℚ) : ℝ) - Real.sqrt ((q i : ℝ) / m)
      = (r : ℝ) * (((sqrtLo (q i) S k : ℚ) : ℝ) - Real.sqrt (q i : ℝ))
        + Real.sqrt (q i : ℝ) * ((r : ℝ) - 1 / Real.sqrt m) := by
    rw [hsqrt_div, hcast_entry]; ring
  have hdiff : ratToComplex (scaledBracketTable q S r k i) - normTarget q m (some i)
      = (((((sqrtLo (q i) S k * r : ℚ) : ℝ) - Real.sqrt ((q i : ℝ) / m)) : ℝ) : ℂ) := by
    simp only [scaledBracketTable, ratToComplex, normTarget]
    push_cast
    ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, halg]
  have hroot_nonneg : (0 : ℝ) ≤ Real.sqrt (q i : ℝ) := Real.sqrt_nonneg _
  calc
    |(r : ℝ) * (((sqrtLo (q i) S k : ℚ) : ℝ) - Real.sqrt (q i : ℝ))
        + Real.sqrt (q i : ℝ) * ((r : ℝ) - 1 / Real.sqrt m)|
        ≤ |(r : ℝ) * (((sqrtLo (q i) S k : ℚ) : ℝ) - Real.sqrt (q i : ℝ))|
          + |Real.sqrt (q i : ℝ) * ((r : ℝ) - 1 / Real.sqrt m)| := abs_add_le _ _
    _ = (r : ℝ) * |((sqrtLo (q i) S k : ℚ) : ℝ) - Real.sqrt (q i : ℝ)|
          + Real.sqrt (q i : ℝ) * |(r : ℝ) - 1 / Real.sqrt m| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hrR, abs_of_nonneg hroot_nonneg]
    _ ≤ (r : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
          + (S : ℝ) * |(r : ℝ) - 1 / Real.sqrt m| := by
        gcongr

theorem scaledTablePrepare_state_error {D : ℕ} (k : ℕ) (q : Fin D → ℚ)
    (S r : ℚ) (hS : 0 < S) (hq : ∀ i, 0 ≤ q i) (hSq : ∀ i, q i ≤ S * S)
    (hr : 0 ≤ r) {m : ℝ} (hm : 0 < m) (hsum : ∑ i, (q i : ℝ) = m)
    (hgap : Real.sqrt ((D + 1 : ℝ)) *
      ((r : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
        + (S : ℝ) * |(r : ℝ) - 1 / Real.sqrt m|) < 1) :
    ‖stateVector (prepareMatrix k
          (fun a => ratSq (tableAmps (scaledBracketTable q S r k) a))
          (tableAmps (scaledBracketTable q S r k)) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (normTarget q m)‖
      ≤ 32 * (D + 1) / 2 ^ k
          + 2 * Real.sqrt ((D + 1 : ℝ)) *
              ((r : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
                + (S : ℝ) * |(r : ℝ) - 1 / Real.sqrt m|) := by
  have hψ : ‖stateVector (normTarget q m)‖ = 1 := norm_normTarget q hq hm hsum
  have hψ0 : normTarget q m none = 0 := rfl
  have hw0 : (0 : ℝ) ≤ ((S / (2 : ℚ) ^ k : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ S / (2 : ℚ) ^ k := by positivity
    exact_mod_cast this
  have hSreal : (0 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS.le
  have hη0 : (0 : ℝ) ≤ (r : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
      + (S : ℝ) * |(r : ℝ) - 1 / Real.sqrt m| :=
    add_nonneg (mul_nonneg (by exact_mod_cast hr) hw0)
      (mul_nonneg hSreal (abs_nonneg _))
  exact tablePrepare_state_error k (normTarget q m) hψ hψ0
    (scaledBracketTable q S r k) hη0
    (scaledBracketTable_eta q S r k hS hq hSq hr hm) hgap

def invSqrtFactor (m S' : ℚ) (j : ℕ) : ℚ :=
  ((1 : ℚ) / sqrtLo m S' j + (1 : ℚ) / sqrtHi m S' j) / 2

theorem invSqrtFactor_spec {m S' : ℚ} {j : ℕ} (hm : 0 < m) (hS' : 0 < S')
    (hmS' : m ≤ S' * S') (ha : 0 < sqrtLo m S' j) :
    0 ≤ invSqrtFactor m S' j ∧
      |(invSqrtFactor m S' j : ℝ) - 1 / Real.sqrt (m : ℝ)|
        ≤ ((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
            / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2) := by
  obtain ⟨hlo0, hlohi, -, -, -, hwidth, hloRoot, hrootHi⟩ :=
    sqrtInterval_certified m S' j hS' hm.le hmS'
  have haR : (0 : ℝ) < ((sqrtLo m S' j : ℚ) : ℝ) := by exact_mod_cast ha
  have hlo_le_hi : ((sqrtLo m S' j : ℚ) : ℝ) ≤ ((sqrtHi m S' j : ℚ) : ℝ) := by
    exact_mod_cast hlohi
  have hw : ((sqrtHi m S' j : ℚ) : ℝ) - ((sqrtLo m S' j : ℚ) : ℝ)
      = ((S' / (2 : ℚ) ^ j : ℚ) : ℝ) := by exact_mod_cast hwidth
  have hwpos : (0 : ℝ) < ((S' / (2 : ℚ) ^ j : ℚ) : ℝ) := by
    have : (0 : ℚ) < S' / (2 : ℚ) ^ j := by positivity
    exact_mod_cast this
  have hrootpos : (0 : ℝ) < Real.sqrt (m : ℝ) := by linarith
  have hb_le : 1 / ((sqrtHi m S' j : ℚ) : ℝ) ≤ 1 / Real.sqrt (m : ℝ) :=
    one_div_le_one_div_of_le hrootpos hrootHi
  have ha_ge : 1 / Real.sqrt (m : ℝ) ≤ 1 / ((sqrtLo m S' j : ℚ) : ℝ) :=
    one_div_le_one_div_of_le haR hloRoot
  have hcast : (invSqrtFactor m S' j : ℝ)
      = (1 / ((sqrtLo m S' j : ℚ) : ℝ) + 1 / ((sqrtHi m S' j : ℚ) : ℝ)) / 2 := by
    simp only [invSqrtFactor]
    push_cast
    ring
  have hpos : (0 : ℝ) < (1 / ((sqrtLo m S' j : ℚ) : ℝ)
      + 1 / ((sqrtHi m S' j : ℚ) : ℝ)) / 2 := by
    have h1 : (0 : ℝ) < 1 / ((sqrtLo m S' j : ℚ) : ℝ) := by positivity
    have h2 : (0 : ℝ) < 1 / ((sqrtHi m S' j : ℚ) : ℝ) := by
      have : (0 : ℝ) < ((sqrtHi m S' j : ℚ) : ℝ) := by linarith
      positivity
    positivity
  constructor
  · have hq : (0 : ℚ) < invSqrtFactor m S' j := by
      unfold invSqrtFactor
      have h1 : (0 : ℚ) < 1 / sqrtLo m S' j := by positivity
      have h2 : (0 : ℚ) < 1 / sqrtHi m S' j := by
        have hhi : (0 : ℚ) < sqrtHi m S' j := lt_of_lt_of_le ha hlohi
        positivity
      positivity
    exact le_of_lt hq
  · have hmid_le : (1 / ((sqrtLo m S' j : ℚ) : ℝ)
        + 1 / ((sqrtHi m S' j : ℚ) : ℝ)) / 2 - 1 / Real.sqrt (m : ℝ)
        ≤ ((1 / ((sqrtLo m S' j : ℚ) : ℝ))
            - 1 / ((sqrtHi m S' j : ℚ) : ℝ)) / 2 := by
      linarith [hb_le]
    have hmid_ge : -(((1 / ((sqrtLo m S' j : ℚ) : ℝ))
            - 1 / ((sqrtHi m S' j : ℚ) : ℝ)) / 2)
        ≤ (1 / ((sqrtLo m S' j : ℚ) : ℝ)
          + 1 / ((sqrtHi m S' j : ℚ) : ℝ)) / 2 - 1 / Real.sqrt (m : ℝ) := by
      linarith [ha_ge]
    have hmid : |(1 / ((sqrtLo m S' j : ℚ) : ℝ)
        + 1 / ((sqrtHi m S' j : ℚ) : ℝ)) / 2 - 1 / Real.sqrt (m : ℝ)|
        ≤ ((1 / ((sqrtLo m S' j : ℚ) : ℝ))
            - 1 / ((sqrtHi m S' j : ℚ) : ℝ)) / 2 :=
      abs_le.mpr ⟨hmid_ge, hmid_le⟩
    have hbR : (0 : ℝ) < ((sqrtHi m S' j : ℚ) : ℝ) := by linarith
    have hfrac : (1 / ((sqrtLo m S' j : ℚ) : ℝ))
        - 1 / ((sqrtHi m S' j : ℚ) : ℝ)
        = (((S' / (2 : ℚ) ^ j : ℚ) : ℝ))
          / (((sqrtLo m S' j : ℚ) : ℝ) * ((sqrtHi m S' j : ℚ) : ℝ)) := by
      rw [← inv_eq_one_div, ← inv_eq_one_div,
        inv_sub_inv (ne_of_gt haR) (ne_of_gt hbR), hw]
    have hprod : ((sqrtLo m S' j : ℚ) : ℝ) * ((sqrtLo m S' j : ℚ) : ℝ)
        ≤ ((sqrtLo m S' j : ℚ) : ℝ) * ((sqrtHi m S' j : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlo_le_hi (le_of_lt haR)
    have hden : (0 : ℝ) < ((sqrtLo m S' j : ℚ) : ℝ) * ((sqrtLo m S' j : ℚ) : ℝ) :=
      mul_pos haR haR
    have hstep : (((S' / (2 : ℚ) ^ j : ℚ) : ℝ))
          / (((sqrtLo m S' j : ℚ) : ℝ) * ((sqrtHi m S' j : ℚ) : ℝ))
        ≤ ((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
          / (((sqrtLo m S' j : ℚ) : ℝ) * ((sqrtLo m S' j : ℚ) : ℝ)) :=
      div_le_div_of_nonneg_left (le_of_lt hwpos) hden hprod
    rw [hcast]
    refine hmid.trans ?_
    rw [hfrac]
    calc
      (((S' / (2 : ℚ) ^ j : ℚ) : ℝ))
            / (((sqrtLo m S' j : ℚ) : ℝ) * ((sqrtHi m S' j : ℚ) : ℝ)) / 2
          ≤ (((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
              / (((sqrtLo m S' j : ℚ) : ℝ) * ((sqrtLo m S' j : ℚ) : ℝ))) / 2 := by
            linarith [hstep]
      _ = ((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
            / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2) := by
            ring

theorem scaledTablePrepare_state_error_factor {D : ℕ} (k j : ℕ) (q : Fin D → ℚ)
    (S S' m : ℚ) (hS : 0 < S) (hq : ∀ i, 0 ≤ q i) (hSq : ∀ i, q i ≤ S * S)
    (hm : 0 < m) (hS' : 0 < S') (hmS' : m ≤ S' * S')
    (ha : 0 < sqrtLo m S' j) (hsum : ∑ i, (q i : ℝ) = (m : ℝ))
    (hgap : Real.sqrt ((D + 1 : ℝ)) *
      ((invSqrtFactor m S' j : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
        + (S : ℝ) * (((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
            / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2))) < 1) :
    ‖stateVector (prepareMatrix k
          (fun a => ratSq (tableAmps
            (scaledBracketTable q S (invSqrtFactor m S' j) k) a))
          (tableAmps (scaledBracketTable q S (invSqrtFactor m S' j) k)) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (normTarget q (m : ℝ))‖
      ≤ 32 * (D + 1) / 2 ^ k
          + 2 * Real.sqrt ((D + 1 : ℝ)) *
              ((invSqrtFactor m S' j : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
                + (S : ℝ) * (((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
                    / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2))) := by
  obtain ⟨hr0, hrerr⟩ := invSqrtFactor_spec hm hS' hmS' ha
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hSreal : (0 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS.le
  have hε0 : (0 : ℝ) ≤ ((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
      / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2) := by
    have hw0 : (0 : ℝ) ≤ ((S' / (2 : ℚ) ^ j : ℚ) : ℝ) := by
      have : (0 : ℚ) ≤ S' / (2 : ℚ) ^ j := by positivity
      exact_mod_cast this
    have hsq : (0 : ℝ) < ((sqrtLo m S' j : ℚ) : ℝ) ^ 2 := by
      have : (0 : ℝ) < ((sqrtLo m S' j : ℚ) : ℝ) := by exact_mod_cast ha
      positivity
    positivity
  have hη_eq : (S : ℝ) * |(invSqrtFactor m S' j : ℝ) - 1 / Real.sqrt (m : ℝ)|
      ≤ (S : ℝ) * (((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
          / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hrerr hSreal
  have hgap' : Real.sqrt ((D + 1 : ℝ)) *
      ((invSqrtFactor m S' j : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
        + (S : ℝ) * |(invSqrtFactor m S' j : ℝ) - 1 / Real.sqrt (m : ℝ)|) < 1 := by
    refine lt_of_le_of_lt ?_ hgap
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    linarith
  have hmain := scaledTablePrepare_state_error (D := D) k q S
    (invSqrtFactor m S' j) hS hq hSq hr0 (m := (m : ℝ)) hmR hsum hgap'
  refine hmain.trans ?_
  have hη_le : (invSqrtFactor m S' j : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
      + (S : ℝ) * |(invSqrtFactor m S' j : ℝ) - 1 / Real.sqrt (m : ℝ)|
      ≤ (invSqrtFactor m S' j : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
        + (S : ℝ) * (((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
            / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2)) := by
    linarith
  have hg := mul_le_mul_of_nonneg_left hη_le
    (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt ((D + 1 : ℝ)))
  linarith

theorem scaledTablePrepare_state_error_width {D : ℕ} (q : Fin D → ℚ)
    (S S' m μ : ℚ) (b : ℕ) (hS : 0 < S) (hq : ∀ i, 0 ≤ q i)
    (hSq : ∀ i, q i ≤ S * S) (hm : 0 < m) (hS' : 0 < S') (hmS' : m ≤ S' * S')
    (hμ0 : 0 < μ) (hμm : μ ≤ m) (hsum : ∑ i, (q i : ℝ) = (m : ℝ))
    (hsmall : 1 / (2 : ℝ) ^ b ≤ Real.sqrt (μ : ℝ) / 2)
    (hgap : Real.sqrt ((D + 1 : ℝ)) *
      ((2 / Real.sqrt (μ : ℝ) + 2 * (S : ℝ) / (μ : ℝ)) / 2 ^ b) < 1) :
    ‖stateVector (prepareMatrix (widthPrecision S b)
          (fun a => ratSq (tableAmps (scaledBracketTable q S
            (invSqrtFactor m S' (widthPrecision S' b)) (widthPrecision S b)) a))
          (tableAmps (scaledBracketTable q S
            (invSqrtFactor m S' (widthPrecision S' b)) (widthPrecision S b)))
          *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (normTarget q (m : ℝ))‖
      ≤ (32 * (D + 1) + 4 * Real.sqrt ((D + 1 : ℝ)) / Real.sqrt (μ : ℝ)
          + 4 * (S : ℝ) * Real.sqrt ((D + 1 : ℝ)) / (μ : ℝ)) / 2 ^ b := by
  have hkb : b ≤ widthPrecision S b := by unfold widthPrecision; omega
  have hjb : b ≤ widthPrecision S' b := by unfold widthPrecision; omega
  have hμR : (0 : ℝ) < Real.sqrt (μ : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hμ0)
  have hμle : Real.sqrt (μ : ℝ) ≤ Real.sqrt (m : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hμm)
  have hwR : ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ) ≤ 1 / (2 : ℝ) ^ b := by
    have h : ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ)
        ≤ ((1 / (2 : ℚ) ^ b : ℚ) : ℝ) := by
      exact_mod_cast widthPrecision_spec S hS b
    simpa using! h
  have hw'R : ((S' / (2 : ℚ) ^ widthPrecision S' b : ℚ) : ℝ) ≤ 1 / (2 : ℝ) ^ b := by
    have h : ((S' / (2 : ℚ) ^ widthPrecision S' b : ℚ) : ℝ)
        ≤ ((1 / (2 : ℚ) ^ b : ℚ) : ℝ) := by
      exact_mod_cast widthPrecision_spec S' hS' b
    simpa using! h
  obtain ⟨-, -, -, -, -, mwidth, mloRoot, mrootHi⟩ :=
    sqrtInterval_certified m S' (widthPrecision S' b) hS' hm.le hmS'
  have mwR : ((sqrtHi m S' (widthPrecision S' b) : ℚ) : ℝ)
      - ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ)
      = ((S' / (2 : ℚ) ^ widthPrecision S' b : ℚ) : ℝ) := by exact_mod_cast mwidth
  have hlo_ge : Real.sqrt (μ : ℝ) / 2 ≤ ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) := by
    have h1 : Real.sqrt (m : ℝ) - ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ)
        ≤ 1 / (2 : ℝ) ^ b := by
      linarith
    linarith
  have ha : 0 < sqrtLo m S' (widthPrecision S' b) := by
    have : (0 : ℝ) < ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) := by linarith
    exact_mod_cast this
  have haR : (0 : ℝ) < ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) := by
    exact_mod_cast ha
  have hrcast : (invSqrtFactor m S' (widthPrecision S' b) : ℝ)
      = (1 / ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ)
          + 1 / ((sqrtHi m S' (widthPrecision S' b) : ℚ) : ℝ)) / 2 := by
    simp only [invSqrtFactor]
    push_cast
    ring
  have hmlohi : ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ)
      ≤ ((sqrtHi m S' (widthPrecision S' b) : ℚ) : ℝ) := by
    exact_mod_cast (sqrtInterval_certified m S' (widthPrecision S' b) hS' hm.le hmS').2.1
  have hr_le : (invSqrtFactor m S' (widthPrecision S' b) : ℝ)
      ≤ 2 / Real.sqrt (μ : ℝ) := by
    rw [hrcast]
    have hinv : 1 / ((sqrtHi m S' (widthPrecision S' b) : ℚ) : ℝ)
        ≤ 1 / ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) :=
      one_div_le_one_div_of_le haR hmlohi
    have hhalf : (1 / ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ)
        + 1 / ((sqrtHi m S' (widthPrecision S' b) : ℚ) : ℝ)) / 2
        ≤ 1 / ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) := by
      linarith
    refine hhalf.trans ?_
    rw [div_le_iff₀ haR]
    calc (1 : ℝ) = (2 / Real.sqrt (μ : ℝ)) * (Real.sqrt (μ : ℝ) / 2) := by
          field_simp
      _ ≤ (2 / Real.sqrt (μ : ℝ))
            * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left hlo_ge (by positivity)
  have hε_bound : ((S' / (2 : ℚ) ^ widthPrecision S' b : ℚ) : ℝ)
        / (2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2)
      ≤ 2 / ((2 : ℝ) ^ b * (μ : ℝ)) := by
    have hsq : (μ : ℝ) / 2
        ≤ 2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2 := by
      have h1 : (Real.sqrt (μ : ℝ) / 2) ^ 2
          ≤ ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlo_ge 2
      have h2 : (Real.sqrt (μ : ℝ) / 2) ^ 2 = (μ : ℝ) / 4 := by
        rw [div_pow, Real.sq_sqrt (by exact_mod_cast hμ0.le)]
        norm_num
      nlinarith
    have hden : (0 : ℝ) < 2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2 := by
      positivity
    have hstep : ((S' / (2 : ℚ) ^ widthPrecision S' b : ℚ) : ℝ)
          / (2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2)
        ≤ (1 / (2 : ℝ) ^ b)
          / (2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hw'R (le_of_lt hden)
    have hstep2 : (1 / (2 : ℝ) ^ b)
          / (2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2)
        ≤ (1 / (2 : ℝ) ^ b) / ((μ : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    have hfinal : (1 / (2 : ℝ) ^ b) / ((μ : ℝ) / 2)
        = 2 / ((2 : ℝ) ^ b * (μ : ℝ)) := by
      field_simp
    exact hstep.trans (hstep2.trans (le_of_eq hfinal))
  have hη_bounded : (invSqrtFactor m S' (widthPrecision S' b) : ℝ)
        * ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ)
      + (S : ℝ) * (((S' / (2 : ℚ) ^ widthPrecision S' b : ℚ) : ℝ)
          / (2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2))
      ≤ (2 / Real.sqrt (μ : ℝ) + 2 * (S : ℝ) / (μ : ℝ)) / 2 ^ b := by
    have hw0 : (0 : ℝ) ≤ ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ) := by
      have : (0 : ℚ) ≤ S / (2 : ℚ) ^ widthPrecision S b := by positivity
      exact_mod_cast this
    have hp0 : (0 : ℝ) ≤ 2 / Real.sqrt (μ : ℝ) := by positivity
    have h1 : (invSqrtFactor m S' (widthPrecision S' b) : ℝ)
          * ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ)
        ≤ (2 / Real.sqrt (μ : ℝ)) * (1 / (2 : ℝ) ^ b) :=
      mul_le_mul hr_le hwR hw0 hp0
    have hSreal : (0 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS.le
    have h2 : (S : ℝ) * (((S' / (2 : ℚ) ^ widthPrecision S' b : ℚ) : ℝ)
          / (2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2))
        ≤ (S : ℝ) * (2 / ((2 : ℝ) ^ b * (μ : ℝ))) :=
      mul_le_mul_of_nonneg_left hε_bound hSreal
    have heq : (2 / Real.sqrt (μ : ℝ)) * (1 / (2 : ℝ) ^ b)
        + (S : ℝ) * (2 / ((2 : ℝ) ^ b * (μ : ℝ)))
        = (2 / Real.sqrt (μ : ℝ) + 2 * (S : ℝ) / (μ : ℝ)) / 2 ^ b := by
      field_simp
    linarith
  have hgap' : Real.sqrt ((D + 1 : ℝ)) *
      ((invSqrtFactor m S' (widthPrecision S' b) : ℝ)
        * ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ)
        + (S : ℝ) * (((S' / (2 : ℚ) ^ widthPrecision S' b : ℚ) : ℝ)
            / (2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2))) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hη_bounded (Real.sqrt_nonneg _)) hgap
  have hmain := scaledTablePrepare_state_error_factor (widthPrecision S b)
    (widthPrecision S' b) q S S' m hS hq hSq hm hS' hmS' ha hsum hgap'
  refine hmain.trans ?_
  have h1 : 32 * ((D : ℝ) + 1) / 2 ^ widthPrecision S b
      ≤ 32 * ((D : ℝ) + 1) / 2 ^ b := by
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact pow_le_pow_right₀ (by norm_num) hkb
  have h2 : 2 * Real.sqrt ((D + 1 : ℝ)) *
      ((invSqrtFactor m S' (widthPrecision S' b) : ℝ)
        * ((S / (2 : ℚ) ^ widthPrecision S b : ℚ) : ℝ)
        + (S : ℝ) * (((S' / (2 : ℚ) ^ widthPrecision S' b : ℚ) : ℝ)
            / (2 * ((sqrtLo m S' (widthPrecision S' b) : ℚ) : ℝ) ^ 2)))
      ≤ 2 * Real.sqrt ((D + 1 : ℝ)) *
        ((2 / Real.sqrt (μ : ℝ) + 2 * (S : ℝ) / (μ : ℝ)) / 2 ^ b) :=
    mul_le_mul_of_nonneg_left hη_bounded (by positivity)
  have hconst : 32 * ((D : ℝ) + 1) / 2 ^ b
      + 2 * Real.sqrt ((D + 1 : ℝ)) *
        ((2 / Real.sqrt (μ : ℝ) + 2 * (S : ℝ) / (μ : ℝ)) / 2 ^ b)
      = (32 * ((D : ℝ) + 1) + 4 * Real.sqrt ((D + 1 : ℝ)) / Real.sqrt (μ : ℝ)
          + 4 * (S : ℝ) * Real.sqrt ((D + 1 : ℝ)) / (μ : ℝ)) / 2 ^ b := by
    field_simp
    ring
  linarith

def normalizationBracketSteps (j : ℕ) : ℕ := j

def prepareChainOpsNormalized (D j : ℕ) : ℕ :=
  normalizationOps D + normalizationBracketSteps j

def prepareChainBitCostNormalized (D p j : ℕ) : ℕ :=
  tableReadBitCost D p + prepareChainOpsNormalized D j * (p + 1) ^ 2

theorem prepareChainOpsNormalized_eq (D j : ℕ) :
    prepareChainOpsNormalized D j = 2 * (D + 1) + D + j := rfl

theorem prepareChainBitCostNormalized_le (D p j : ℕ) :
    prepareChainBitCostNormalized D p j ≤ 16 * (D + j + 1) * (p + 1) ^ 3 := by
  have hp : 1 ≤ p + 1 := by omega
  have hsq : (p + 1) ^ 2 ≤ (p + 1) ^ 3 := by
    calc
      (p + 1) ^ 2 = (p + 1) ^ 2 * 1 := by ring
      _ ≤ (p + 1) ^ 2 * (p + 1) := Nat.mul_le_mul_left _ hp
      _ = (p + 1) ^ 3 := by ring
  have hbase := prepareChainCost_le D p
  have hread : prepareChainCost D p ≤ 8 * (D + j + 1) * (p + 1) ^ 3 := by
    refine hbase.trans ?_
    exact Nat.mul_le_mul_right _ (by omega)
  have hops : normalizationBracketSteps j ≤ j + 1 := by
    dsimp [normalizationBracketSteps]; omega
  have hbracket : normalizationBracketSteps j * (p + 1) ^ 2
      ≤ (j + 1) * (p + 1) ^ 3 := by
    calc
      normalizationBracketSteps j * (p + 1) ^ 2
          ≤ (j + 1) * (p + 1) ^ 2 := Nat.mul_le_mul_right _ hops
      _ ≤ (j + 1) * (p + 1) ^ 3 := Nat.mul_le_mul_left _ hsq
  have hnorm : prepareChainOpsNormalized D j * (p + 1) ^ 2
      ≤ normalizationOps D * (p + 1) ^ 2 + (j + 1) * (p + 1) ^ 3 := by
    have hsplit : prepareChainOpsNormalized D j * (p + 1) ^ 2
        = normalizationOps D * (p + 1) ^ 2
          + normalizationBracketSteps j * (p + 1) ^ 2 := by
      rw [prepareChainOpsNormalized, Nat.add_mul]
    rw [hsplit]
    exact Nat.add_le_add_left hbracket _
  have htotal : prepareChainBitCostNormalized D p j
      ≤ 8 * (D + j + 1) * (p + 1) ^ 3 + (j + 1) * (p + 1) ^ 3 := by
    dsimp [prepareChainBitCostNormalized]
    calc
      tableReadBitCost D p + prepareChainOpsNormalized D j * (p + 1) ^ 2
          ≤ tableReadBitCost D p + (normalizationOps D * (p + 1) ^ 2
              + (j + 1) * (p + 1) ^ 3) := Nat.add_le_add_left hnorm _
      _ = (tableReadBitCost D p + normalizationOps D * (p + 1) ^ 2)
            + (j + 1) * (p + 1) ^ 3 := by ring
      _ = prepareChainCost D p + (j + 1) * (p + 1) ^ 3 := by
        rw [prepareChainCost, normalizationBitCost]
      _ ≤ 8 * (D + j + 1) * (p + 1) ^ 3 + (j + 1) * (p + 1) ^ 3 :=
        Nat.add_le_add_right hread _
  calc
    prepareChainBitCostNormalized D p j
        ≤ 8 * (D + j + 1) * (p + 1) ^ 3 + (j + 1) * (p + 1) ^ 3 := htotal
    _ = (8 * (D + j + 1) + (j + 1)) * (p + 1) ^ 3 := by ring
    _ ≤ 16 * (D + j + 1) * (p + 1) ^ 3 := by
      have : 8 * (D + j + 1) + (j + 1) ≤ 16 * (D + j + 1) := by omega
      exact Nat.mul_le_mul_right _ this

theorem frontier2 :
    (∀ (D : ℕ) (q : Fin D → ℚ) (m : ℝ), (∀ i, 0 ≤ q i) → 0 < m →
      (∑ i, (q i : ℝ)) = m → ‖stateVector (normTarget q m)‖ = 1) ∧
    (∀ (D : ℕ) (q : Fin D → ℚ) (S r : ℚ) (k : ℕ) (m : ℝ),
      0 < S → (∀ i, 0 ≤ q i) → (∀ i, q i ≤ S * S) → 0 ≤ r → 0 < m →
      ∀ i : Fin D,
        ‖ratToComplex (scaledBracketTable q S r k i) - normTarget q m (some i)‖
          ≤ (r : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
              + (S : ℝ) * |(r : ℝ) - 1 / Real.sqrt m|) ∧
    (∀ (D : ℕ) (k : ℕ) (q : Fin D → ℚ) (S r : ℚ) (m : ℝ),
      0 < S → (∀ i, 0 ≤ q i) → (∀ i, q i ≤ S * S) → 0 ≤ r → 0 < m →
      (∑ i, (q i : ℝ)) = m →
      Real.sqrt ((D + 1 : ℝ)) *
        ((r : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
          + (S : ℝ) * |(r : ℝ) - 1 / Real.sqrt m|) < 1 →
      ‖stateVector (prepareMatrix k
            (fun a => ratSq (tableAmps (scaledBracketTable q S r k) a))
            (tableAmps (scaledBracketTable q S r k)) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (normTarget q m)‖
        ≤ 32 * (D + 1) / 2 ^ k
            + 2 * Real.sqrt ((D + 1 : ℝ)) *
                ((r : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
                  + (S : ℝ) * |(r : ℝ) - 1 / Real.sqrt m|)) ∧
    (∀ (m S' : ℚ) (j : ℕ), 0 < m → 0 < S' → m ≤ S' * S' → 0 < sqrtLo m S' j →
      0 ≤ invSqrtFactor m S' j ∧
        |(invSqrtFactor m S' j : ℝ) - 1 / Real.sqrt (m : ℝ)|
          ≤ ((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
              / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2)) ∧
    (∀ (D : ℕ) (k j : ℕ) (q : Fin D → ℚ) (S S' m : ℚ),
      0 < S → (∀ i, 0 ≤ q i) → (∀ i, q i ≤ S * S) → 0 < m → 0 < S' →
      m ≤ S' * S' → 0 < sqrtLo m S' j → (∑ i, (q i : ℝ)) = (m : ℝ) →
      Real.sqrt ((D + 1 : ℝ)) *
        ((invSqrtFactor m S' j : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
          + (S : ℝ) * (((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
              / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2))) < 1 →
      ‖stateVector (prepareMatrix k
            (fun a => ratSq (tableAmps
              (scaledBracketTable q S (invSqrtFactor m S' j) k) a))
            (tableAmps (scaledBracketTable q S (invSqrtFactor m S' j) k)) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (normTarget q (m : ℝ))‖
        ≤ 32 * (D + 1) / 2 ^ k
            + 2 * Real.sqrt ((D + 1 : ℝ)) *
                ((invSqrtFactor m S' j : ℝ) * ((S / (2 : ℚ) ^ k : ℚ) : ℝ)
                  + (S : ℝ) * (((S' / (2 : ℚ) ^ j : ℚ) : ℝ)
                      / (2 * ((sqrtLo m S' j : ℚ) : ℝ) ^ 2)))) ∧
    (∀ (D : ℕ) (q : Fin D → ℚ) (S S' m μ : ℚ) (b : ℕ), 0 < S →
      (∀ i, 0 ≤ q i) → (∀ i, q i ≤ S * S) → 0 < m → 0 < S' → m ≤ S' * S' →
      0 < μ → μ ≤ m → (∑ i, (q i : ℝ)) = (m : ℝ) →
      1 / (2 : ℝ) ^ b ≤ Real.sqrt (μ : ℝ) / 2 →
      Real.sqrt ((D + 1 : ℝ)) *
        ((2 / Real.sqrt (μ : ℝ) + 2 * (S : ℝ) / (μ : ℝ)) / 2 ^ b) < 1 →
      ‖stateVector (prepareMatrix (widthPrecision S b)
            (fun a => ratSq (tableAmps (scaledBracketTable q S
              (invSqrtFactor m S' (widthPrecision S' b)) (widthPrecision S b)) a))
            (tableAmps (scaledBracketTable q S
              (invSqrtFactor m S' (widthPrecision S' b)) (widthPrecision S b)))
            *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (normTarget q (m : ℝ))‖
        ≤ (32 * (D + 1) + 4 * Real.sqrt ((D + 1 : ℝ)) / Real.sqrt (μ : ℝ)
            + 4 * (S : ℝ) * Real.sqrt ((D + 1 : ℝ)) / (μ : ℝ)) / 2 ^ b) ∧
    (∀ (D p j : ℕ),
      prepareChainOpsNormalized D j = 2 * (D + 1) + D + j ∧
        prepareChainBitCostNormalized D p j
          ≤ 16 * (D + j + 1) * (p + 1) ^ 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro D q m hq hm hsum
    exact norm_normTarget q hq hm hsum
  · intro D q S r k m hS hq hSq hr hm
    exact scaledBracketTable_eta q S r k hS hq hSq hr hm
  · intro D k q S r m hS hq hSq hr hm hsum hgap
    exact scaledTablePrepare_state_error k q S r hS hq hSq hr hm hsum hgap
  · intro m S' j hm hS' hmS' ha
    exact invSqrtFactor_spec hm hS' hmS' ha
  · intro D k j q S S' m hS hq hSq hm hS' hmS' ha hsum hgap
    exact scaledTablePrepare_state_error_factor k j q S S' m hS hq hSq hm hS'
      hmS' ha hsum hgap
  · intro D q S S' m μ b hS hq hSq hm hS' hmS' hμ0 hμm hsum hsmall hgap
    exact scaledTablePrepare_state_error_width q S S' m μ b hS hq hSq hm hS' hmS'
      hμ0 hμm hsum hsmall hgap
  · intro D p j
    exact ⟨prepareChainOpsNormalized_eq D j, prepareChainBitCostNormalized_le D p j⟩

end output1

end Qatlib.Concepts.MbqcFlow.FlowDecision
