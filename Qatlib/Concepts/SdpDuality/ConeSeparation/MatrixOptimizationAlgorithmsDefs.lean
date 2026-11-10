/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Pi
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open scoped BigOperators

noncomputable def sdpInnerEps (δ R : ℝ) : ℝ := δ / (28 * R ^ 2)

noncomputable def sdpInnerEpsPrime (δ R : ℝ) : ℝ := -Real.log (1 - sdpInnerEps δ R)

noncomputable def sdpRoundCount (n δ R : ℝ) : ℝ := 500 * R ^ 3 * Real.log n / δ ^ 2

noncomputable def sdpKLoopCount (m δ R : ℝ) : ℕ :=
  Nat.ceil (8 * Real.log m * R ^ 2 / sdpInnerEps δ R ^ 2)

noncomputable def sdpNLoopCount (α δ R : ℝ) : ℕ := Nat.ceil (α / sdpInnerEps δ R)

noncomputable def sdpCopyCountM (n m δ R ξ : ℝ) : ℝ :=
  80 * Real.rpow (Real.log (8 * R ^ 2 * n * m / sdpInnerEps δ R)) (1 + ξ) /
    sdpInnerEps δ R ^ 2

noncomputable def sdpSampleCountL (n m δ R ξ : ℝ) : ℝ :=
  80 * Real.rpow (Real.log (n * m)) (1 + ξ) / sdpInnerEps δ R ^ 2

noncomputable def sdpCopyCountQ (n m δ R ξ : ℝ) : ℝ :=
  1000000 * R ^ 6 * Real.rpow (Real.log (n * m)) (2 + ξ) / δ ^ 4

noncomputable def sdpWeightCopies (n m δ R α ξ G : ℝ) : ℝ :=
  10 * Real.log m / sdpInnerEps δ R ^ 2 *
    (((sdpKLoopCount m δ R : ℝ) * α / sdpInnerEps δ R) * sdpCopyCountM n m δ R ξ +
      sdpCopyCountQ n m δ R ξ) * G +
    2 * (sdpKLoopCount m δ R : ℝ) * α / sdpInnerEps δ R *
      sdpCopyCountM n m δ R ξ * sdpSampleCountL n m δ R ξ

noncomputable def sdpHamiltonianElementQueries (T s : ℝ) : ℝ := T * s

noncomputable def sdpGibbsSparseCalls (dim β sparsity prec : ℝ) : ℝ :=
  Real.sqrt dim * β * sparsity / prec

noncomputable def sdpSparseGibbsH (m δ R : ℝ) : ℝ := Real.sqrt m * R ^ 2 / δ

noncomputable def sdpSparseGibbsM (n s δ R : ℝ) : ℝ := Real.sqrt n * s ^ 2 * R ^ 9 / δ ^ 6

noncomputable def sdpMeasTime (n s pe ε : ℝ) : ℝ :=
  s / ε ^ 2 * (Real.log (4 * n * s / (pe * ε))) ^ 4

noncomputable def sdpMeasCopies (pe ε : ℝ) : ℝ := Real.log (1 / pe) / ε ^ 2

noncomputable def sdpThm4Time (δ R G_h G_M Tmeas : ℝ) : ℝ :=
  R ^ 21 / δ ^ 11 * G_h * G_M + R ^ 13 / δ ^ 5 * Tmeas

noncomputable def sdpCor5Time (n m s δ R : ℝ) : ℝ :=
  Real.sqrt n * Real.sqrt m * s ^ 2 * R ^ 32 / δ ^ 18

noncomputable def sdpFailureProbBase (n m δ R : ℝ) : ℝ :=
  (R / δ) ^ 18 * (n * m) ^ 10

noncomputable def sdpFailureProb (n m δ R ξ : ℝ) : ℝ :=
  sdpFailureProbBase n m δ R * Real.exp (-Real.rpow (Real.log (n * m)) ξ)

structure SdpCostLedger where

  inputAccess : ℝ

  gibbsPrepare : ℝ

  prepareCopies : ℝ

  estimationTime : ℝ

  elementaryGates : ℝ

  integerBits : ℕ

  peakSpaceBits : ℕ

def HasSdpSparseInputs {n m : ℕ} (s : ℕ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (Cv : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  0 < s ∧
  (∀ i r, ((Finset.univ.filter (fun c : Fin n => A i r c ≠ 0)).card ≤ s)) ∧
  (∀ r, ((Finset.univ.filter (fun c : Fin n => Cv r c ≠ 0)).card ≤ s))

noncomputable def sdpPrecisionBits (prec : ℝ) : ℕ :=
  Nat.ceil (Real.log (1 / prec) / Real.log 2) + 1

def sdpIntegerBits (words bits : ℕ) : ℕ := words * bits

def sdpPeakSpaceBits (n m : ℕ) (precBits : ℕ) : ℕ :=
  3 * (Nat.clog 2 (max 2 n) + Nat.clog 2 (max 2 m) + precBits)

def HasSdpFixedGateBackend (D : ℕ) (tableBits : ℕ) (ε : ℝ) : Prop :=
  0 < ε → ε ≤ 1 / 2 →
    ∃ (w : ℕ) (gs : List FiniteGateCode),
      finiteWordLegal w gs = true ∧
        gs.length ≤ (64 * D + 128) * (Nat.ceil ((1 / ε) ^ 2) + 1) ∧
        w ≤ 2 * D + sdpIntegerBits 2 tableBits + 8

end Qatlib.Concepts.SdpDuality.ConeSeparation
