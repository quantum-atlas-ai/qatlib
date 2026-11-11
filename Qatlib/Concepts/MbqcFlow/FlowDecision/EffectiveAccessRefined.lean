/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec

/-!
# Certified preparation and checked table access

This module bounds state-preparation error for certified complex tables by combining
finite-precision circuit error with perturbation of normalized table snapshots.
`certPrepare_error` separates these contributions, and `certErr_le` proves geometric decay of
the certified table error. Finite quantum states and reversible computation provide the
background in [NielsenChuang2010].

`checkedLookup_word` compiles enabled, range-checked table lookup into a reversible Boolean-DAG
circuit with explicit node and gate bounds. The remaining statements expose QRAM contract
charges and address coverage, together with descent and halving properties of the Euclidean
remainder sequence.

## Main statements

* `certPrepare_error`: controls preparation from a certified snapshot under positive mass and
  closeness hypotheses.
* `checkedLookup_value`: identifies enabled lookup values and rejects addresses outside the
  table.
* `checkedLookup_word`: gives reversible lookup semantics and circuit counts.
* `remSeq_halving`: bounds a later Euclidean remainder by half the current term.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess
open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.MatrixAccess.RitzPipeline

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open Qatlib
open Qatlib
open Qatlib.Concepts.TableAccess.LookupCompile
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option autoImplicit false

/-- The squared norm of a complex number is the sum of the squares of its real and imaginary
parts. -/
private theorem complexSq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The unnormalized complex state of the precision-`k` approximations in a certified table,
extended by zero at `none`. -/
noncomputable def certRawState {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    QState (Option (Fin D)) :=
  fun a => match a with
    | none => 0
    | some i => ratToComplex ((T.entry i).approx k)

/-- The unnormalized state of a certified table's exact complex values, extended by zero at
`none`. -/
noncomputable def certRawValues {D : ℕ} (T : CertifiedTable D) : QState (Option (Fin D)) :=
  fun a => match a with
    | none => 0
    | some i => (T.entry i).value

/-- The squared Euclidean norm of a certified table's raw exact state equals its exact mass. -/
private theorem certRawValues_sq {D : ℕ} (T : CertifiedTable D) :
    ‖stateVector (certRawValues T)‖ ^ 2 = certMass T := by
  have hsum : (∑ a : Option (Fin D), ‖certRawValues T a‖ ^ 2)
      = ∑ i : Fin D, (((T.entry i).value.re) ^ 2 + ((T.entry i).value.im) ^ 2) := by
    rw [Fintype.sum_option]
    simp [certRawValues, complexSq]
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.stateVector_norm_sq_sum, hsum]
  rfl

/-- The squared Euclidean norm of the raw approximate state equals the snapshot mass coerced to
the reals. -/
private theorem certRawState_sq {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    ‖stateVector (certRawState T k)‖ ^ 2 = (certSnapshotMass T k : ℝ) := by
  have hsum : (∑ a : Option (Fin D), ‖certRawState T k a‖ ^ 2)
      = (∑ i : Fin D, (((T.entry i).approx k).1 ^ 2 + ((T.entry i).approx k).2 ^ 2) : ℝ) := by
    rw [Fintype.sum_option]
    simp [certRawState, complexSq, ratToComplex_re, ratToComplex_im]
  have h2 : (∑ i : Fin D,
      (((T.entry i).approx k).1 ^ 2 + ((T.entry i).approx k).2 ^ 2) : ℝ)
      = (certSnapshotMass T k : ℝ) := by
    simp only [certSnapshotMass, certSnapshotAmp, ratSq]
    norm_cast
  rw [Qatlib.Concepts.LocalMachine.LocalTransport.stateVector_norm_sq_sum, hsum, h2]

/-- The Euclidean norm of the raw exact state is the square root of the certified mass. -/
private theorem certRawValues_norm {D : ℕ} (T : CertifiedTable D) :
    ‖stateVector (certRawValues T)‖ = Real.sqrt (certMass T) := by
  have hsq := certRawValues_sq T
  have hn : 0 ≤ certMass T := by
    have h := sq_nonneg (‖stateVector (certRawValues T)‖)
    rw [hsq] at h
    linarith
  have h1 : (Real.sqrt (certMass T)) ^ 2 = certMass T := Real.sq_sqrt hn
  have hn2 : 0 ≤ ‖stateVector (certRawValues T)‖ := norm_nonneg _
  have hn3 : 0 ≤ Real.sqrt (certMass T) := Real.sqrt_nonneg _
  nlinarith

/-- The Euclidean norm of the raw approximate state is the square root of the snapshot mass. -/
private theorem certRawState_norm {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    ‖stateVector (certRawState T k)‖ = Real.sqrt (certSnapshotMass T k : ℝ) := by
  have hsq := certRawState_sq T k
  have hn : 0 ≤ (certSnapshotMass T k : ℝ) := by
    have h := sq_nonneg (‖stateVector (certRawState T k)‖)
    rw [hsq] at h
    linarith
  have h1 : (Real.sqrt (certSnapshotMass T k : ℝ)) ^ 2 = (certSnapshotMass T k : ℝ) :=
    Real.sq_sqrt hn
  have hn2 : 0 ≤ ‖stateVector (certRawState T k)‖ := norm_nonneg _
  have hn3 : 0 ≤ Real.sqrt (certSnapshotMass T k : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- The certified target vector is the raw exact vector scaled by the inverse square root of its
mass. -/
private theorem certTarget_eq {D : ℕ} (T : CertifiedTable D) :
    stateVector (certTarget T) = (Real.sqrt (certMass T))⁻¹ • stateVector (certRawValues T) := by
  have h : certTarget T = (Real.sqrt (certMass T))⁻¹ • certRawValues T := by
    funext a
    cases a with
    | none => simp [certTarget, certRawValues]
    | some i =>
      simp [certTarget, certRawValues, div_eq_mul_inv]
      <;> ring
  rw [stateVector, h, WithLp.toLp_smul]

/-- The normalized snapshot vector is the raw approximate vector scaled by the inverse square
root of its mass. -/
private theorem certSnapshotState_eq {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    stateVector (certSnapshotState T k)
      = (Real.sqrt (certSnapshotMass T k : ℝ))⁻¹ • stateVector (certRawState T k) := by
  have h : certSnapshotState T k
      = (Real.sqrt (certSnapshotMass T k : ℝ))⁻¹ • certRawState T k := by
    funext a
    cases a with
    | none => simp [certSnapshotState, certRawState]
    | some i =>
      simp [certSnapshotState, certRawState, certSnapshotAmp, div_eq_mul_inv]
      <;> ring
  rw [stateVector, h, WithLp.toLp_smul]

/-- The Euclidean distance between raw approximate and exact certified states is at most `sqrt D
* T.err k`. -/
private theorem certRaw_diff_le {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    ‖stateVector (certRawState T k) - stateVector (certRawValues T)‖
      ≤ Real.sqrt D * (T.err k : ℝ) := by
  have hsub : stateVector (certRawState T k) - stateVector (certRawValues T)
      = stateVector (certRawState T k - certRawValues T) := by
    simp only [stateVector, WithLp.toLp_sub]
  have hsum : (∑ a : Option (Fin D),
        ‖(certRawState T k - certRawValues T) a‖ ^ 2)
      = ∑ i : Fin D,
        ‖ratToComplex ((T.entry i).approx k) - (T.entry i).value‖ ^ 2 := by
    rw [Fintype.sum_option]
    simp [certRawState, certRawValues]
  have hsq : ‖stateVector (certRawState T k) - stateVector (certRawValues T)‖ ^ 2
      ≤ D * (T.err k : ℝ) ^ 2 := by
    rw [hsub, Qatlib.Concepts.LocalMachine.LocalTransport.stateVector_norm_sq_sum, hsum]
    have h1 : (∑ i : Fin D,
          ‖ratToComplex ((T.entry i).approx k) - (T.entry i).value‖ ^ 2)
        ≤ ∑ _i : Fin D, (T.err k : ℝ) ^ 2 := by
      refine Finset.sum_le_sum (s := (Finset.univ : Finset (Fin D))) ?_
      intro i _
      have hc := T.certified k i
      have hsq' : ‖ratToComplex ((T.entry i).approx k) - (T.entry i).value‖
          ≤ (T.err k : ℝ) := by simpa using! hc
      have herr : 0 ≤ (T.err k : ℝ) := by exact_mod_cast (T.err_nonneg k)
      have hxn : 0 ≤ ‖ratToComplex ((T.entry i).approx k) - (T.entry i).value‖ :=
        norm_nonneg _
      nlinarith [sq_nonneg (‖ratToComplex ((T.entry i).approx k) - (T.entry i).value‖),
        herr, hxn]
    have h3 : (∑ _i : Fin D, (T.err k : ℝ) ^ 2) = D * (T.err k : ℝ) ^ 2 := by simp
    linarith
  have hn := T.err_nonneg k
  have hc : 0 ≤ Real.sqrt D * (T.err k : ℝ) := by positivity
  have hsqc : (Real.sqrt D * (T.err k : ℝ)) ^ 2 = D * (T.err k : ℝ) ^ 2 := by
    have hD := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ D)
    ring_nf at hD ⊢
    nlinarith
  nlinarith [sq_nonneg (‖stateVector (certRawState T k) - stateVector (certRawValues T)‖)]

/-- For nonzero Euclidean vectors `p` and `z` with `‖p - z‖ ≤ ‖z‖ / 2`, their normalized
distance is at most `4 * ‖p - z‖ / ‖z‖`. -/
private theorem normalized_diff_le {D : ℕ}
    (p z : EuclideanSpace ℂ (Option (Fin D)))
    (hp : 0 < ‖p‖) (hz : 0 < ‖z‖) (hhalf : ‖p - z‖ ≤ ‖z‖ / 2) :
    ‖(‖p‖⁻¹ : ℝ) • p - (‖z‖⁻¹ : ℝ) • z‖ ≤ 4 * ‖p - z‖ / ‖z‖ := by
  have hsplit : (‖p‖⁻¹ : ℝ) • p - (‖z‖⁻¹ : ℝ) • z
      = (‖p‖⁻¹ : ℝ) • (p - z) + ((‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)) • z := by
    have h : ∀ (a b c : EuclideanSpace ℂ (Option (Fin D))),
        a - c = (a - b) + (b - c) := by
      intro a b c
      calc a - c = (a - b + b) - c := by rw [sub_add_cancel]
        _ = ((a - b) + b) - c := by rfl
        _ = (a - b) + (b - c) := by rw [add_sub_assoc]
    calc (‖p‖⁻¹ : ℝ) • p - (‖z‖⁻¹ : ℝ) • z
        = ((‖p‖⁻¹ : ℝ) • p - (‖p‖⁻¹ : ℝ) • z)
          + ((‖p‖⁻¹ : ℝ) • z - (‖z‖⁻¹ : ℝ) • z) := h _ _ _
      _ = (‖p‖⁻¹ : ℝ) • (p - z) + ((‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)) • z := by
        rw [← smul_sub, ← sub_smul]
  have hzp : ‖z - p‖ = ‖p - z‖ := norm_sub_rev _ _
  have htri_z : ‖z‖ ≤ ‖z - p‖ + ‖p‖ := by
    have hx := norm_add_le (z - p) p
    rw [sub_add_cancel] at hx
    exact hx
  have hhalf' : ‖z‖ / 2 ≤ ‖p‖ := by linarith
  have hre : |‖z‖ - ‖p‖| ≤ ‖p - z‖ := by
    have h1 : ‖z‖ - ‖p‖ ≤ ‖z - p‖ := by linarith
    have h2 : ‖p‖ - ‖z‖ ≤ ‖p - z‖ := by
      have hx := norm_add_le (p - z) z
      rw [sub_add_cancel] at hx
      linarith
    rw [abs_le]
    constructor <;> linarith
  have hinv : |(‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)| ≤ ‖p - z‖ / (‖p‖ * ‖z‖) := by
    have hne : (‖p‖ : ℝ) ≠ 0 := by positivity
    have hne' : (‖z‖ : ℝ) ≠ 0 := by positivity
    have hfield : (‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)
        = (‖z‖ - ‖p‖) / (‖p‖ * ‖z‖) := by
      field_simp
    have hmul : 0 < ‖p‖ * ‖z‖ := by positivity
    calc |(‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)| = |(‖z‖ - ‖p‖) / (‖p‖ * ‖z‖)| := by rw [hfield]
      _ = |‖z‖ - ‖p‖| / (‖p‖ * ‖z‖) := by rw [abs_div, abs_of_pos hmul]
      _ ≤ ‖p - z‖ / (‖p‖ * ‖z‖) := by
        have h1 : |‖z‖ - ‖p‖| / (‖p‖ * ‖z‖) ≤ ‖p - z‖ / (‖p‖ * ‖z‖) := by
          gcongr
        exact h1
  have hmain : ‖(‖p‖⁻¹ : ℝ) • p - (‖z‖⁻¹ : ℝ) • z‖
      ≤ 2 * ‖p - z‖ / ‖p‖ := by
    rw [hsplit]
    have htri := norm_add_le ((‖p‖⁻¹ : ℝ) • (p - z))
      (((‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)) • z)
    have e1 : ‖(‖p‖⁻¹ : ℝ) • (p - z)‖ = (‖p‖⁻¹ : ℝ) * ‖p - z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖p‖⁻¹)]
    have e2 : ‖((‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)) • z‖
        = |(‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)| * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    have hpos : (0:ℝ) < ‖p‖ := hp
    calc ‖(‖p‖⁻¹ : ℝ) • (p - z) + ((‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)) • z‖
        ≤ ‖(‖p‖⁻¹ : ℝ) • (p - z)‖ + ‖((‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)) • z‖ := htri
      _ = (‖p‖⁻¹ : ℝ) * ‖p - z‖ + |(‖p‖⁻¹ : ℝ) - (‖z‖⁻¹ : ℝ)| * ‖z‖ := by
        rw [e1, e2]
      _ ≤ (‖p‖⁻¹ : ℝ) * ‖p - z‖ + (‖p - z‖ / (‖p‖ * ‖z‖)) * ‖z‖ := by
        gcongr
      _ = 2 * ‖p - z‖ / ‖p‖ := by field_simp; ring
  have hhalfp : ‖z‖ / 2 ≤ ‖p‖ := hhalf'
  have hpos2 : (0:ℝ) < ‖p‖ := by linarith
  calc ‖(‖p‖⁻¹ : ℝ) • p - (‖z‖⁻¹ : ℝ) • z‖ ≤ 2 * ‖p - z‖ / ‖p‖ := hmain
    _ ≤ 2 * ‖p - z‖ / (‖z‖ / 2) := by
      gcongr
    _ = 4 * ‖p - z‖ / ‖z‖ := by ring

/-- The loaded certified snapshot has mass `certSnapshotMass T k`. -/
private theorem certSnapshotLoaded_mass {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    (certSnapshotLoaded T k).mass = certSnapshotMass T k := rfl

/-- The loaded certified snapshot has amplitude table `certSnapshotAmpOpt T k`. -/
private theorem certSnapshotLoaded_amp {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    (certSnapshotLoaded T k).amp = certSnapshotAmpOpt T k := rfl

/-- The loaded certified snapshot has weights `certSnapshotWeights T k`. -/
private theorem certSnapshotLoaded_weights {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    (certSnapshotLoaded T k).weights = certSnapshotWeights T k := rfl

/-- The target of the loaded certified snapshot is `certSnapshotState T k`. -/
private theorem certSnapshotLoaded_target {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    loadedTarget (certSnapshotLoaded T k) = certSnapshotState T k := by
  funext a
  cases a with
  | none => rfl
  | some i => rfl

/-- For positive exact and snapshot masses with `2 * sqrt D * T.err k ≤ sqrt (certMass T)`,
normalized snapshot error is at most `4 * sqrt D * T.err k / sqrt (certMass T)`. -/
private theorem certSnapshot_target_le {D : ℕ} (T : CertifiedTable D) (k : ℕ)
    (hmass : 0 < certMass T) (hsnap : 0 < certSnapshotMass T k)
    (hnear : 2 * Real.sqrt D * (T.err k : ℝ) ≤ Real.sqrt (certMass T)) :
    ‖stateVector (certSnapshotState T k) - stateVector (certTarget T)‖
      ≤ 4 * Real.sqrt D * (T.err k : ℝ) / Real.sqrt (certMass T) := by
  have hnormP : ‖stateVector (certRawState T k)‖ = Real.sqrt (certSnapshotMass T k : ℝ) :=
    certRawState_norm T k
  have hnormZ : ‖stateVector (certRawValues T)‖ = Real.sqrt (certMass T) :=
    certRawValues_norm T
  have hinvP : (Real.sqrt (certSnapshotMass T k : ℝ))⁻¹
      = (‖stateVector (certRawState T k)‖⁻¹ : ℝ) := by rw [hnormP]
  have hinvZ : (Real.sqrt (certMass T))⁻¹
      = (‖stateVector (certRawValues T)‖⁻¹ : ℝ) := by rw [hnormZ]
  have hposP : 0 < ‖stateVector (certRawState T k)‖ := by
    rw [hnormP]
    have h1 : (0 : ℝ) < (certSnapshotMass T k : ℝ) := by exact_mod_cast hsnap
    exact Real.sqrt_pos.2 h1
  have hposZ : 0 < ‖stateVector (certRawValues T)‖ := by
    rw [hnormZ]
    exact Real.sqrt_pos.2 hmass
  have hdiff : ‖stateVector (certRawState T k) - stateVector (certRawValues T)‖
      ≤ Real.sqrt D * (T.err k : ℝ) := certRaw_diff_le T k
  have hhalf : ‖stateVector (certRawState T k) - stateVector (certRawValues T)‖
      ≤ ‖stateVector (certRawValues T)‖ / 2 := by
    have h1 : Real.sqrt D * (T.err k : ℝ) ≤ Real.sqrt (certMass T) / 2 := by linarith
    rw [hnormZ]
    linarith
  have hmain := normalized_diff_le (stateVector (certRawState T k))
    (stateVector (certRawValues T)) hposP hposZ hhalf
  have hLHS :
      ‖(‖stateVector (certRawState T k)‖⁻¹ : ℝ) • stateVector (certRawState T k)
          - (‖stateVector (certRawValues T)‖⁻¹ : ℝ) • stateVector (certRawValues T)‖
        = ‖stateVector (certSnapshotState T k) - stateVector (certTarget T)‖ := by
    rw [certSnapshotState_eq, certTarget_eq, hinvP, hinvZ]
  rw [hLHS] at hmain
  have hfinal : 4 * ‖stateVector (certRawState T k) - stateVector (certRawValues T)‖
        / ‖stateVector (certRawValues T)‖
      ≤ 4 * Real.sqrt D * (T.err k : ℝ) / Real.sqrt (certMass T) := by
    rw [hnormZ]
    have hsq : 0 < Real.sqrt (certMass T) := Real.sqrt_pos.2 hmass
    have hmul : ‖stateVector (certRawState T k) - stateVector (certRawValues T)‖
        ≤ Real.sqrt D * (T.err k : ℝ) := hdiff
    have hmul4 : 4 * ‖stateVector (certRawState T k) - stateVector (certRawValues T)‖
        ≤ 4 * Real.sqrt D * (T.err k : ℝ) := by
      have := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    rw [div_le_iff₀ hsq, div_mul_cancel₀ _ hsq.ne']
    exact hmul4
  linarith

/-- Under positive mass and snapshot-closeness hypotheses, certified preparation error is at
most `32 * (D + 1) / 2^k + 4 * sqrt D * T.err k / sqrt (certMass T)`. -/
theorem certPrepare_error {D : ℕ} (T : CertifiedTable D) (k : ℕ)
    (hmass : 0 < certMass T)
    (hsnap : 0 < certSnapshotMass T k)
    (hnear : 2 * Real.sqrt D * (T.err k : ℝ) ≤ Real.sqrt (certMass T)) :
    ‖stateVector (prepareMatrix k (certSnapshotWeights T k) (certSnapshotAmpOpt T k) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
        - stateVector (certTarget T)‖
      ≤ 32 * (D + 1) / 2 ^ k + 4 * Real.sqrt D * (T.err k : ℝ) / Real.sqrt (certMass T) := by
  have hLpos : 0 < (certSnapshotLoaded T k).mass := by
    rw [certSnapshotLoaded_mass]
    exact_mod_cast hsnap
  have herr := prepareMatrix_state_error k (certSnapshotLoaded T k) hLpos
  have hamp : (certSnapshotLoaded T k).amp = certSnapshotAmpOpt T k :=
    certSnapshotLoaded_amp T k
  have hw : (certSnapshotLoaded T k).weights = certSnapshotWeights T k :=
    certSnapshotLoaded_weights T k
  have hprep : stateVector (prepareMatrix k (certSnapshotLoaded T k).weights
        (certSnapshotLoaded T k).amp *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
      = stateVector (prepareMatrix k (certSnapshotWeights T k)
          (certSnapshotAmpOpt T k) *ᵥ Qatlib.Foundations.PureStateMath.Ket none) := by
    rw [hw, hamp]
  rw [hprep] at herr
  rw [certSnapshotLoaded_target] at herr
  have hnorm := certSnapshot_target_le T k hmass hsnap hnear
  have htri : ‖stateVector (prepareMatrix k (certSnapshotWeights T k)
        (certSnapshotAmpOpt T k) *ᵥ Qatlib.Foundations.PureStateMath.Ket none) - stateVector (certTarget T)‖
      ≤ ‖stateVector (prepareMatrix k (certSnapshotWeights T k)
          (certSnapshotAmpOpt T k) *ᵥ Qatlib.Foundations.PureStateMath.Ket none) - stateVector (certSnapshotState T k)‖
        + ‖stateVector (certSnapshotState T k) - stateVector (certTarget T)‖ := by
    have h := dist_triangle
      (stateVector (prepareMatrix k (certSnapshotWeights T k) (certSnapshotAmpOpt T k) *ᵥ Qatlib.Foundations.PureStateMath.Ket none))
      (stateVector (certSnapshotState T k)) (stateVector (certTarget T))
    simp only [dist_eq_norm] at h
    exact h
  linarith

/-- The certified error at precision `k` is bounded by the initial error divided by `2^k`. -/
theorem certErr_le {D : ℕ} (T : CertifiedTable D) : ∀ k,
    (T.err k : ℝ) ≤ (T.err 0 : ℝ) / 2 ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h := T.halving k
    calc (T.err (k + 1) : ℝ) ≤ (T.err k : ℝ) / 2 := h
      _ ≤ ((T.err 0 : ℝ) / 2 ^ k) / 2 :=
        div_le_div_of_nonneg_right ih (by norm_num : (0 : ℝ) ≤ 2)
      _ = (T.err 0 : ℝ) / 2 ^ (k + 1) := by ring

/-- Collects the certified preparation error bound, geometric decay of table error, and
decomposition of the preparation word's length into phase and weight words. -/
theorem clause1_endpoint :
    (∀ (D : ℕ) (T : CertifiedTable D) (k : ℕ),
      0 < certMass T → 0 < certSnapshotMass T k →
      2 * Real.sqrt D * (T.err k : ℝ) ≤ Real.sqrt (certMass T) →
      ‖stateVector (prepareMatrix k (certSnapshotWeights T k) (certSnapshotAmpOpt T k) *ᵥ Qatlib.Foundations.PureStateMath.Ket none)
          - stateVector (certTarget T)‖
        ≤ 32 * (D + 1) / 2 ^ k + 4 * Real.sqrt D * (T.err k : ℝ) / Real.sqrt (certMass T)) ∧
    (∀ (D : ℕ) (T : CertifiedTable D) (k : ℕ),
      (T.err k : ℝ) ≤ (T.err 0 : ℝ) / 2 ^ k) ∧
    (∀ (D : ℕ) (T : CertifiedTable D) (k : ℕ),
      (prepareWord k (certSnapshotWeights T k) (certSnapshotAmpOpt T k)).length
        = (phaseWord k (certSnapshotAmpOpt T k)).length
          + (rationalWeightWord (certSnapshotWeights T k) k).length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro D T k hm hs hn
    exact certPrepare_error T k hm hs hn
  · intro D T k
    exact certErr_le T k
  · intro D T k
    simp [prepareWord]

/-- A conjunction of address-bit tests over a list evaluates to true exactly when every listed
address wire equals the corresponding bit of `s`. -/
private theorem matching_list (a b : ℕ) (s : Fin (2 ^ a))
    (x : Reg (inputs a b)) (ls : List (Fin a)) :
    eval (ls.foldr (fun i z => Expr.conj
      (if s.val.testBit i.val then .var (addressWire a b i)
        else .neg (.var (addressWire a b i))) z) (.constant true)) x = true ↔
      ∀ i ∈ ls, x (addressWire a b i) = s.val.testBit i.val := by
  induction ls with
  | nil => simp [eval]
  | cons i ls ih =>
    cases ht : s.val.testBit i.val <;>
      simp [List.foldr_cons, eval, ht, ih, Bool.and_eq_true]

/-- The address-matching expression evaluates to true exactly when every address wire matches
the corresponding bit of `s`. -/
private theorem matching_true (a b : ℕ) (s : Fin (2 ^ a)) (x : Reg (inputs a b)) :
    eval (matchExpr a b s) x = true ↔
      ∀ i : Fin a, x (addressWire a b i) = s.val.testBit i.val := by
  simpa only [matchExpr, List.mem_finRange, forall_const] using!
    matching_list a b s x (List.finRange a)

/-- Two rows in `Fin (2^a)` are equal if all their `a` address bits agree. -/
private theorem row_ext (a : ℕ) (r s : Fin (2 ^ a))
    (h : ∀ i : Fin a, r.val.testBit i.val = s.val.testBit i.val) : r = s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < a
  · exact h ⟨i, hi⟩
  · have hp : 2 ^ a ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (r.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (s.isLt.trans_le hp)]

/-- On a register encoding row `r`, the expression matching row `s` evaluates to true exactly
when `s = r`. -/
private theorem matching_value (a b : ℕ) (x : Reg (inputs a b))
    (r s : Fin (2 ^ a))
    (hx : ∀ i : Fin a, x (addressWire a b i) = r.val.testBit i.val) :
    eval (matchExpr a b s) x = if s = r then true else false := by
  by_cases hs : s = r
  · subst s
    simpa using! (matching_true a b r x).mpr hx
  · have hn : eval (matchExpr a b s) x ≠ true := by
      intro he
      have hm := (matching_true a b s x).mp he
      exact hs (row_ext a s r (fun i => (hm i).symm.trans (hx i)))
    cases he : eval (matchExpr a b s) x <;> simp_all

/-- A checked lookup expression for one output bit has at most `1 + D * (2 * a + 5)` nodes. -/
private theorem checkedLookup_nodes (a b D : ℕ) (hD : D ≤ 2 ^ a) (j : Fin b) :
    nodes (checkedLookupExpr a b D hD j) ≤ 1 + D * (2 * a + 5) := by
  have hm : ∀ (s : Fin (2 ^ a)), nodes (matchExpr a b s) ≤ 2 * a + 1 := by
    intro s
    have h : ∀ ls : List (Fin a),
        nodes (ls.foldr (fun i z => Expr.conj
          (if s.val.testBit i.val then .var (addressWire a b i)
            else .neg (.var (addressWire a b i))) z) (.constant true)) ≤ 2 * ls.length + 1 := by
      intro ls
      induction ls with
      | nil => simp [nodes]
      | cons i ls ih =>
        cases ht : s.val.testBit i.val <;> simp only [List.foldr_cons, ht,
          Bool.false_eq_true, ↓reduceIte, nodes, List.length_cons] <;> omega
    simpa only [matchExpr, List.length_finRange] using! h (List.finRange a)
  have h : ∀ ls : List (Fin (2 ^ a)),
      nodes (ls.foldr (fun s z => Expr.xor (.conj (.var (enableWire a b))
        (.conj (matchExpr a b s) (.var (tableWire a b s j)))) z) (.constant false))
        ≤ 1 + ls.length * (2 * a + 5) := by
    intro ls
    induction ls with
    | nil => simp [nodes]
    | cons s ls ih =>
      have hm' := hm s
      simp only [List.foldr_cons, nodes, List.length_cons]
      nlinarith
  simpa only [checkedLookupExpr, List.length_map, List.length_finRange] using!
    h ((List.finRange D).map (Fin.castLE hD))

/-- On an address encoding row `r`, checked lookup returns the enabled table bit when `r < D`
and false otherwise. -/
theorem checkedLookup_value (a b D : ℕ) (hD : D ≤ 2 ^ a)
    (x : Reg (inputs a b)) (r : Fin (2 ^ a)) (j : Fin b)
    (hx : ∀ i : Fin a, x (addressWire a b i) = r.val.testBit i.val) :
    eval (checkedLookupExpr a b D hD j) x =
      if r.val < D then (x (enableWire a b) && x (tableWire a b r j)) else false := by
  have hfold : ∀ (ls : List (Fin (2 ^ a))) (hnd : ls.Nodup),
      eval (ls.foldr (fun s z => Expr.xor (.conj (.var (enableWire a b))
        (.conj (matchExpr a b s) (.var (tableWire a b s j)))) z) (.constant false)) x =
        if r ∈ ls then (x (enableWire a b) && x (tableWire a b r j)) else false := by
    intro ls hnd
    induction ls with
    | nil => simp [eval]
    | cons s ls ih =>
      have hnot := (List.nodup_cons.mp hnd).1
      have htail := (List.nodup_cons.mp hnd).2
      rw [List.foldr_cons]
      simp only [eval, matching_value a b x r s hx, ih htail]
      by_cases hs : s = r
      · subst s
        simp [hnot]
      · simp [hs, Ne.symm hs]
  have hmem : r ∈ (List.finRange D).map (Fin.castLE hD) ↔ r.val < D := by
    constructor
    · intro hm
      obtain ⟨s, hs, heq⟩ := List.mem_map.mp hm
      have hcast : (Fin.castLE hD s).val = s.val := rfl
      have hv : s.val = r.val := by
        have h := congrArg Fin.val heq
        rwa [hcast] at h
      rw [← hv]
      exact s.isLt
    · intro hr
      refine List.mem_map.mpr ⟨⟨r.val, hr⟩, List.mem_finRange _, ?_⟩
      apply Fin.ext
      rfl
  have hn := hfold ((List.finRange D).map (Fin.castLE hD))
    ((List.nodup_finRange D).map (Fin.castLE_injective hD))
  simp only [checkedLookupExpr] at hn ⊢
  by_cases hr : r.val < D
  · have hr' : r ∈ (List.finRange D).map (Fin.castLE hD) := hmem.mpr hr
    rw [hn]
    simp [hr', hr]
  · have hr' : r ∉ (List.finRange D).map (Fin.castLE hD) := fun hm => hr (hmem.mp hm)
    rw [hn]
    simp [hr', hr]

/-- Loading an index into a register establishes the corresponding `loadedIndexBits` predicate. -/
theorem loadIndex_bits {D : ℕ} (a b : ℕ) (i : Fin D) (x : Reg (inputs a b)) :
    loadedIndexBits a b i (loadIndex a b i x) := by
  intro j
  simp [loadedIndexBits, loadIndex, addressWire]

/-- Loading an address index preserves every register wire at position at least `a`. -/
private theorem loadIndex_other {D : ℕ} (a b : ℕ) (i : Fin D) (x : Reg (inputs a b))
    (w : Fin (inputs a b)) (hw : a ≤ w.val) : loadIndex a b i x w = x w := by
  simp [loadIndex]
  omega

/-- After loading index `i`, checked lookup returns the conjunction of the enable bit and the
indexed table bit. -/
theorem checkedLookup_loaded {D : ℕ} (a b : ℕ) (hD : D ≤ 2 ^ a) (i : Fin D) (j : Fin b)
    (x : Reg (inputs a b)) :
    eval (checkedLookupExpr a b D hD j) (loadIndex a b i x) =
      ((x (enableWire a b) && x (tableWire a b (Fin.castLE hD i) j)) : Bool) := by
  have hi : i.val < D := i.isLt
  have hx : ∀ k : Fin a, (loadIndex a b i x) (addressWire a b k) = i.val.testBit k.val := by
    intro k
    have hk : (addressWire a b k).val = k.val := rfl
    simp [loadIndex, addressWire, hk]
  have hr : (Fin.castLE hD i).val = i.val := rfl
  have hcast : (Fin.castLE hD i).val < D := by rw [hr]; exact hi
  have hval := checkedLookup_value a b D hD (loadIndex a b i x) (Fin.castLE hD i) j hx
  have hen : a ≤ (enableWire a b).val := by
    have : (enableWire a b).val = a + 2 ^ a * b := rfl
    omega
  have htb : a ≤ (tableWire a b (Fin.castLE hD i) j).val := by
    have : (tableWire a b (Fin.castLE hD i) j).val = a + (Fin.castLE hD i).val * b + j.val := rfl
    omega
  rw [hval, if_pos hcast, loadIndex_other a b i x (enableWire a b) hen,
    loadIndex_other a b i x (tableWire a b (Fin.castLE hD i) j) htb]

/-- Checked lookup has a reflection-legal Boolean-DAG compilation with zero queries, at most `30
* k + b` gates, and `k ≤ b * (1 + D * (2 * a + 5))` internal nodes. It XORs the checked
table values into the output, and two copies restore the embedded input. -/
theorem checkedLookup_word (a b D : ℕ) (hD : D ≤ 2 ^ a) :
    ∃ (k : ℕ) (g : BooleanDAG (inputs a b) k) (out : Fin b → Fin (inputs a b + k)),
      k ≤ b * (1 + D * (2 * a + 5)) ∧
      reflectionLegal (booleanDAGSteps g out) ∧
      QueryCount (reflectionCompile (booleanDAGSteps g out)) = 0 ∧
      GateCount (reflectionCompile (booleanDAGSteps g out)) ≤ 30 * k + b ∧
      (∀ (ψ : QState (Reg (inputs a b) × Reg b)),
        Run (1 : Matrix (Reg (inputs a b + k + b)) (Reg (inputs a b + k + b)) ℂ)
          (reflectionCompile (booleanDAGSteps g out))
          (booleanDAGEmbed (inputs a b) k b ψ) =
          ∑ xy, ψ xy • Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (inputs a b) k b xy.1
            (fun j => xy.2 j ^^ eval (checkedLookupExpr a b D hD j) xy.1))) ∧
      (∀ (ψ : QState (Reg (inputs a b) × Reg b)),
        Run (1 : Matrix (Reg (inputs a b + k + b)) (Reg (inputs a b + k + b)) ℂ)
          ((reflectionCompile (booleanDAGSteps g out)) ++
            (reflectionCompile (booleanDAGSteps g out)))
          (booleanDAGEmbed (inputs a b) k b ψ) =
          booleanDAGEmbed (inputs a b) k b ψ) := by
  obtain ⟨k, g, out, hk, hval⟩ :=
    g1 (inputs a b) b (fun j => checkedLookupExpr a b D hD j)
  have hr := boolean_dag_resources g out
  have hout (x : Reg (inputs a b)) (y : Reg b) :
      booleanDAGOutput g out x y = (fun j => y j ^^ eval (checkedLookupExpr a b D hD j) x) := by
    funext j
    change (y j ^^ booleanDAGValue g x (out j)) = _
    rw [hval]
  have hinv (x : Reg (inputs a b)) (y : Reg b) :
      booleanDAGOutput g out x (booleanDAGOutput g out x y) = y := by
    funext j
    change ((y j ^^ booleanDAGValue g x (out j)) ^^ booleanDAGValue g x (out j)) = y j
    simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  have hk' : k ≤ b * (1 + D * (2 * a + 5)) := by
    have h3 : (∑ j, nodes (checkedLookupExpr a b D hD j))
        ≤ ∑ _j : Fin b, (1 + D * (2 * a + 5)) := by
      refine Finset.sum_le_sum (s := (Finset.univ : Finset (Fin b))) ?_
      intro j _
      exact checkedLookup_nodes a b D hD j
    have h4 : (∑ _j : Fin b, (1 + D * (2 * a + 5))) = b * (1 + D * (2 * a + 5)) := by
      simp
    calc k ≤ ∑ j, nodes (checkedLookupExpr a b D hD j) := hk
      _ ≤ b * (1 + D * (2 * a + 5)) := by linarith
  refine ⟨k, g, out, hk', hr.1, hr.2.2.1, ?_, ?_, ?_⟩
  · rw [hr.2.2.2]
    exact hr.2.1
  · intro ψ
    simpa only [hout] using! boolean_dag_coherent g out ψ
  · intro ψ
    rw [run_append, boolean_dag_coherent]
    simp only [run_reflectionCompile_sum, run_reflectionCompile_smul, boolean_dag_basis,
      hinv, booleanDAGEmbed]

/-- A QRAM contract's paid entry count equals its row count. -/
theorem qram_paid_reads {D : ℕ} (c : QramContract D) : c.paidEntries = c.rows :=
  c.paid_reads_rows

/-- The total charge of a QRAM contract is at least its row count for every access count. -/
theorem qram_total_charge {D : ℕ} (c : QramContract D) (n : ℕ) :
    c.rows ≤ c.totalCharge n := by
  rw [QramContract.totalCharge, qram_paid_reads]
  omega

/-- A QRAM contract's address space has at least as many addresses as table rows. -/
theorem qram_address_covers {D : ℕ} (c : QramContract D) : c.rows ≤ 2 ^ c.addressWidth :=
  c.rows_le

/-- If the per-access charge is positive, equal total charges imply equal access counts. -/
theorem qram_per_access_constant {D : ℕ} (c : QramContract D) (hpos : 0 < c.perAccess)
    (n m : ℕ) (hn : c.totalCharge n = c.totalCharge m) : n = m := by
  simp only [QramContract.totalCharge] at hn
  exact Nat.mul_right_cancel hpos (Nat.add_left_cancel hn)

/-- Checked QRAM lookup has a Boolean-DAG compilation with at most `b * (1 + D * (2 * a + 5))`
internal nodes and at most `30 * k + b` gates. -/
theorem qram_gate_bound (a b D : ℕ) (hD : D ≤ 2 ^ a) :
    ∃ (k : ℕ) (g : BooleanDAG (inputs a b) k) (out : Fin b → Fin (inputs a b + k)),
      k ≤ b * (1 + D * (2 * a + 5)) ∧
      GateCount (reflectionCompile (booleanDAGSteps g out)) ≤ 30 * k + b := by
  obtain ⟨k, g, out, hk, _, _, hg, _, _⟩ := checkedLookup_word a b D hD
  exact ⟨k, g, out, hk, hg⟩

/-- The explicit lookup bit-time expression `b * (1 + D * (2 * a + 5)) + a`. -/
def qramBitTime (a b D : ℕ) : ℕ := b * (1 + D * (2 * a + 5)) + a

/-- The explicit register-space expression `a + 2^a * b + 1 + b` for address, table, enable, and
output bits. -/
def qramPeakSpace (a b D : ℕ) : ℕ := a + (2 ^ a) * b + 1 + b

/-- For natural numbers `0 < y < x`, the remainder `x % y` is at most `x / 2`. -/
private theorem mod_le_half {x y : ℕ} (hxy : y < x) (hy : 0 < y) : x % y ≤ x / 2 := by
  by_cases h : y ≤ x / 2
  · have h1 : x % y < y := Nat.mod_lt x hy
    omega
  · have h2 : x / 2 < y := by omega
    have hxy2 : x < y * 2 := (Nat.div_lt_iff_lt_mul (k := 2) (x := x) (y := y)
      (by omega : 0 < 2)).mp h2
    have h3 : x / y = 1 := by
      have hy1 : 0 < y := hy
      exact Nat.div_eq_of_lt_le (k := 1) (by omega : 1 * y ≤ x) (by omega : x < 2 * y)
    have h4 : x % y = x - y := by
      have := Nat.mod_add_div x y
      rw [h3] at this
      omega
    rw [h4]
    omega

/-- Once the remainder sequence is zero, its next term is also zero. -/
private theorem remSeq_zero_of_zero {a b : ℕ} (n : ℕ) (h : remSeq (n + 1) a b = 0) :
    remSeq (n + 2) a b = 0 := by
  rw [remSeq]
  rw [if_pos (by simp [h])]

/-- If consecutive remainder terms are equal and the earlier term is positive, the following
term is zero. -/
private theorem remSeq_zero_of_eq {a b : ℕ} (n : ℕ)
    (h : remSeq (n + 1) a b = remSeq n a b) (hpos : 0 < remSeq n a b) :
    remSeq (n + 2) a b = 0 := by
  rw [remSeq]
  rw [if_neg (by omega)]
  rw [h]
  exact Nat.mod_self _

/-- From index one onward, the next remainder is zero when the current term is zero and
otherwise is the previous term modulo the current term. -/
private theorem remSeq_step {a b : ℕ} (n : ℕ) (hn : 1 ≤ n) :
    remSeq (n + 1) a b = if remSeq n a b = 0 then 0
      else remSeq (n - 1) a b % remSeq n a b := by
  have h : n + 1 = (n - 1) + 2 := by omega
  have h2 : (n - 1) + 1 = n := by omega
  rw [h, remSeq, h2]

/-- From index one onward, a positive next remainder is strictly smaller than the current
remainder. -/
theorem remSeq_strict {a b : ℕ} (n : ℕ) (hn : 1 ≤ n) (h : 0 < remSeq (n + 1) a b) :
    remSeq (n + 1) a b < remSeq n a b := by
  have hpos : 0 < remSeq n a b := by
    by_contra hc
    have hz : remSeq (n + 1) a b = 0 := by
      rw [remSeq_step n hn]
      rw [if_pos (by omega)]
    have hnlt : ¬ 0 < remSeq (n + 1) a b := by
      rw [hz]
      exact Nat.not_lt_zero _
    exact absurd h hnlt
  rw [remSeq_step n hn, if_neg (by omega)]
  exact Nat.mod_lt _ hpos

/-- If the next remainder is positive and strictly smaller than the current term, twice the
following remainder is at most the current term. -/
theorem remSeq_halving {a b : ℕ} (n : ℕ)
    (h1 : 0 < remSeq (n + 1) a b) (h2 : remSeq (n + 1) a b < remSeq n a b) :
    remSeq (n + 2) a b * 2 ≤ remSeq n a b := by
  have hstep : remSeq (n + 2) a b = remSeq n a b % remSeq (n + 1) a b := by
    rw [remSeq]
    rw [if_neg (by omega)]
  rw [hstep]
  have hh := mod_le_half h2 h1
  omega

/-- The arithmetic cost expression `2 * (Nat.log2 b + 2)`. -/
def gcdPrice (b : ℕ) : ℕ := 2 * (Nat.log2 b + 2)

/-- The cost expression `gcdPrice b` is at least four. -/
theorem gcdPrice_pos (b : ℕ) : 4 ≤ gcdPrice b := by
  unfold gcdPrice
  omega

/-- Collects loaded-index lookup correctness, out-of-range rejection, reversible lookup
compilation with explicit resource bounds, and the QRAM row-charge lower bound. -/
theorem clause2_endpoint :
    (∀ {D : ℕ} (a b : ℕ) (hD : D ≤ 2 ^ a) (i : Fin D) (j : Fin b) (x : Reg (inputs a b)),
      eval (checkedLookupExpr a b D hD j) (loadIndex a b i x) =
        ((x (enableWire a b) && x (tableWire a b (Fin.castLE hD i) j)) : Bool)) ∧
    (∀ {D : ℕ} (a b : ℕ) (hD : D ≤ 2 ^ a) (x : Reg (inputs a b)) (r : Fin (2 ^ a)) (j : Fin b),
      (∀ i : Fin a, x (addressWire a b i) = r.val.testBit i.val) →
      eval (checkedLookupExpr a b D hD j) x =
        if r.val < D then (x (enableWire a b) && x (tableWire a b r j)) else false) ∧
    (∀ (a b D : ℕ) (hD : D ≤ 2 ^ a),
      ∃ (k : ℕ) (g : BooleanDAG (inputs a b) k) (out : Fin b → Fin (inputs a b + k)),
        k ≤ b * (1 + D * (2 * a + 5)) ∧
        reflectionLegal (booleanDAGSteps g out) ∧
        QueryCount (reflectionCompile (booleanDAGSteps g out)) = 0 ∧
        GateCount (reflectionCompile (booleanDAGSteps g out)) ≤ 30 * k + b ∧
        (∀ (ψ : QState (Reg (inputs a b) × Reg b)),
          Run (1 : Matrix (Reg (inputs a b + k + b)) (Reg (inputs a b + k + b)) ℂ)
            (reflectionCompile (booleanDAGSteps g out))
            (booleanDAGEmbed (inputs a b) k b ψ) =
            ∑ xy, ψ xy • Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (inputs a b) k b xy.1
              (fun j => xy.2 j ^^ eval (checkedLookupExpr a b D hD j) xy.1))) ∧
        (∀ (ψ : QState (Reg (inputs a b) × Reg b)),
          Run (1 : Matrix (Reg (inputs a b + k + b)) (Reg (inputs a b + k + b)) ℂ)
            ((reflectionCompile (booleanDAGSteps g out)) ++
              (reflectionCompile (booleanDAGSteps g out)))
            (booleanDAGEmbed (inputs a b) k b ψ) =
            booleanDAGEmbed (inputs a b) k b ψ)) ∧
    (∀ {D : ℕ} (c : QramContract D) (n : ℕ), c.rows ≤ c.totalCharge n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D a b hD i j x
    exact checkedLookup_loaded a b hD i j x
  · intro D a b hD x r j hx
    exact checkedLookup_value a b D hD x r j hx
  · intro a b D hD
    exact checkedLookup_word a b D hD
  · intro D c n
    exact qram_total_charge c n

/-- Collects QRAM row and address accounting, lookup gate bounds, remainder descent and halving,
the lower bound on `gcdPrice`, and certified approximation error and width bounds. -/
theorem clause3_endpoint :
    (∀ {D : ℕ} (c : QramContract D), c.paidEntries = c.rows) ∧
    (∀ {D : ℕ} (c : QramContract D), c.rows ≤ 2 ^ c.addressWidth) ∧
    (∀ (a b D : ℕ) (hD : D ≤ 2 ^ a),
      ∃ (k : ℕ) (g : BooleanDAG (inputs a b) k) (out : Fin b → Fin (inputs a b + k)),
        k ≤ b * (1 + D * (2 * a + 5)) ∧
        GateCount (reflectionCompile (booleanDAGSteps g out)) ≤ 30 * k + b) ∧
    (∀ (a b : ℕ) (n : ℕ) (hn : 1 ≤ n) (h : 0 < remSeq (n + 1) a b),
      remSeq (n + 1) a b < remSeq n a b) ∧
    (∀ (a b : ℕ) (n : ℕ) (h1 : 0 < remSeq (n + 1) a b)
      (h2 : remSeq (n + 1) a b < remSeq n a b),
      remSeq (n + 2) a b * 2 ≤ remSeq n a b) ∧
    (∀ (b : ℕ), 4 ≤ gcdPrice b) ∧
    (∀ {D : ℕ} (T : CertifiedTable D) (k : ℕ),
      (T.err k : ℝ) ≤ (T.err 0 : ℝ) / 2 ^ k) ∧
    (∀ {D : ℕ} (T : CertifiedTable D) (k : ℕ) (i : Fin D),
      ((T.entry i).approx k).1.num.natAbs < 2 ^ T.width ∧
        ((T.entry i).approx k).2.den < 2 ^ T.width) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro D c
    exact qram_paid_reads c
  · intro D c
    exact qram_address_covers c
  · intro a b D hD
    exact qram_gate_bound a b D hD
  · intro a b n hn h
    exact remSeq_strict n hn h
  · intro a b n h1 h2
    exact remSeq_halving n h1 h2
  · intro b
    exact gcdPrice_pos b
  · intro D T k
    exact certErr_le T k
  · intro D T k i
    exact T.bounded k i

end Qatlib.Concepts.MbqcFlow.FlowDecision
