/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Pi
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# Resource formulas for quantum SDP algorithms

This module collects precision, loop, copy, query, measurement, runtime, and failure expressions
for the quantum SDP setting of [BrandaoSvore2017]. The definitions begin with `sdpInnerEps` and
feed into quantities such as `sdpWeightCopies`, `sdpThm4Time`, and `sdpCor5Time`; they are
explicit formulas rather than resource bounds proved in this module. `SdpCostLedger` stores the
corresponding accounting categories.

`HasSdpSparseInputs` requires positive row sparsity and bounds the number of nonzero entries in
each input row. The bit formulas specify precision and storage charges. `HasSdpFixedGateBackend`
requires the existence of a legal finite gate word with stated length and width bounds when the
tolerance lies in `(0,1/2]`; its condition contains no target-operation or approximation
requirement.

## Main statements

* `sdpInnerEps`, `sdpRoundCount`, and the loop and copy counts: parameter formulas for the
  algorithm.
* `sdpWeightCopies`, `sdpThm4Time`, and `sdpCor5Time`: composite resource expressions.
* `sdpFailureProb`: a polynomial prefactor multiplied by an exponential factor.
* `SdpCostLedger` and `HasSdpSparseInputs`: resource fields and a row sparsity predicate.
* `sdpPrecisionBits`, `sdpIntegerBits`, and `sdpPeakSpaceBits`: bit accounting formulas.
* `HasSdpFixedGateBackend`: bounded legal finite gate words at positive tolerances at most one
  half.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open scoped BigOperators

/-- Defines the inner precision `δ / (28*R^2)`. -/
noncomputable def sdpInnerEps (δ R : ℝ) : ℝ := δ / (28 * R ^ 2)

/-- Defines the transformed inner precision `-Real.log (1 - sdpInnerEps δ R)`. -/
noncomputable def sdpInnerEpsPrime (δ R : ℝ) : ℝ := -Real.log (1 - sdpInnerEps δ R)

/-- Defines the real round-count expression `500*R^3*Real.log n/δ^2`. -/
noncomputable def sdpRoundCount (n δ R : ℝ) : ℝ := 500 * R ^ 3 * Real.log n / δ ^ 2

/-- Defines the natural candidate-loop count as the ceiling of `8*Real.log m*R^2/(sdpInnerEps δ
R)^2`. -/
noncomputable def sdpKLoopCount (m δ R : ℝ) : ℕ :=
  Nat.ceil (8 * Real.log m * R ^ 2 / sdpInnerEps δ R ^ 2)

/-- Defines the natural mass-grid loop count as `Nat.ceil (α / sdpInnerEps δ R)`. -/
noncomputable def sdpNLoopCount (α δ R : ℝ) : ℕ := Nat.ceil (α / sdpInnerEps δ R)

/-- Defines the real copy-count expression `80*(Real.log (8*R^2*n*m/ε))^(1+ξ)/ε^2`, with real
powers and `ε = sdpInnerEps δ R`. -/
noncomputable def sdpCopyCountM (n m δ R ξ : ℝ) : ℝ :=
  80 * Real.rpow (Real.log (8 * R ^ 2 * n * m / sdpInnerEps δ R)) (1 + ξ) /
    sdpInnerEps δ R ^ 2

/-- Defines the real sample-count expression `80*(Real.log (n*m))^(1+ξ)/ε^2`, with real powers
and `ε = sdpInnerEps δ R`. -/
noncomputable def sdpSampleCountL (n m δ R ξ : ℝ) : ℝ :=
  80 * Real.rpow (Real.log (n * m)) (1 + ξ) / sdpInnerEps δ R ^ 2

/-- Defines the real copy-count expression `1000000*R^6*(Real.log (n*m))^(2+ξ)/δ^4`, using a
real power for the logarithmic factor. -/
noncomputable def sdpCopyCountQ (n m δ R ξ : ℝ) : ℝ :=
  1000000 * R ^ 6 * Real.rpow (Real.log (n * m)) (2 + ξ) / δ ^ 4

/-- Combines the resource formulas as `10*Real.log m/ε^2 * (γ*α/ε*M + Q)*G + 2*γ*α/ε*M*L`. Here
`ε`, `γ`, `M`, `Q`, and `L` denote `sdpInnerEps`, `sdpKLoopCount`, `sdpCopyCountM`,
`sdpCopyCountQ`, and `sdpSampleCountL` at the supplied parameters, with `γ` cast to the
reals. -/
noncomputable def sdpWeightCopies (n m δ R α ξ G : ℝ) : ℝ :=
  10 * Real.log m / sdpInnerEps δ R ^ 2 *
    (((sdpKLoopCount m δ R : ℝ) * α / sdpInnerEps δ R) * sdpCopyCountM n m δ R ξ +
      sdpCopyCountQ n m δ R ξ) * G +
    2 * (sdpKLoopCount m δ R : ℝ) * α / sdpInnerEps δ R *
      sdpCopyCountM n m δ R ξ * sdpSampleCountL n m δ R ξ

/-- Defines the Hamiltonian-entry query expression as the product `T*s`. -/
noncomputable def sdpHamiltonianElementQueries (T s : ℝ) : ℝ := T * s

/-- Defines the sparse Gibbs-call expression `Real.sqrt dim * β * sparsity / prec`. -/
noncomputable def sdpGibbsSparseCalls (dim β sparsity prec : ℝ) : ℝ :=
  Real.sqrt dim * β * sparsity / prec

/-- Defines the real resource expression `Real.sqrt m * R^2 / δ` for the sparse Gibbs
Hamiltonian contribution. -/
noncomputable def sdpSparseGibbsH (m δ R : ℝ) : ℝ := Real.sqrt m * R ^ 2 / δ

/-- Defines the real resource expression `Real.sqrt n * s^2 * R^9 / δ^6` for the sparse Gibbs
matrix contribution. -/
noncomputable def sdpSparseGibbsM (n s δ R : ℝ) : ℝ := Real.sqrt n * s ^ 2 * R ^ 9 / δ ^ 6

/-- Defines the measurement-time expression `s/ε^2 * (Real.log (4*n*s/(pe*ε)))^4`. -/
noncomputable def sdpMeasTime (n s pe ε : ℝ) : ℝ :=
  s / ε ^ 2 * (Real.log (4 * n * s / (pe * ε))) ^ 4

/-- Defines the measurement-copy expression `Real.log (1/pe)/ε^2`. -/
noncomputable def sdpMeasCopies (pe ε : ℝ) : ℝ := Real.log (1 / pe) / ε ^ 2

/-- Defines the combined time expression `R^21/δ^11 * G_h * G_M + R^13/δ^5 * Tmeas`. -/
noncomputable def sdpThm4Time (δ R G_h G_M Tmeas : ℝ) : ℝ :=
  R ^ 21 / δ ^ 11 * G_h * G_M + R ^ 13 / δ ^ 5 * Tmeas

/-- Defines the real time expression `Real.sqrt n * Real.sqrt m * s^2 * R^32 / δ^18`. -/
noncomputable def sdpCor5Time (n m s δ R : ℝ) : ℝ :=
  Real.sqrt n * Real.sqrt m * s ^ 2 * R ^ 32 / δ ^ 18

/-- Defines the polynomial failure-expression prefactor `(R/δ)^18 * (n*m)^10`. -/
noncomputable def sdpFailureProbBase (n m δ R : ℝ) : ℝ :=
  (R / δ) ^ 18 * (n * m) ^ 10

/-- Multiplies `sdpFailureProbBase n m δ R` by `Real.exp (-Real.rpow (Real.log (n*m)) ξ)` to
define the failure expression. -/
noncomputable def sdpFailureProb (n m δ R ξ : ℝ) : ℝ :=
  sdpFailureProbBase n m δ R * Real.exp (-Real.rpow (Real.log (n * m)) ξ)

/-- Stores real charges for input access, Gibbs preparation, copy preparation, estimation time,
and elementary gates, together with natural integer-bit and peak-space charges. The
structure itself imposes no inequalities on these fields. -/
structure SdpCostLedger where

  inputAccess : ℝ

  gibbsPrepare : ℝ

  prepareCopies : ℝ

  estimationTime : ℝ

  elementaryGates : ℝ

  integerBits : ℕ

  peakSpaceBits : ℕ

/-- Requires `s > 0` and at most `s` nonzero entries in every row of each constraint matrix and
of `Cv`. -/
def HasSdpSparseInputs {n m : ℕ} (s : ℕ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (Cv : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  0 < s ∧
  (∀ i r, ((Finset.univ.filter (fun c : Fin n => A i r c ≠ 0)).card ≤ s)) ∧
  (∀ r, ((Finset.univ.filter (fun c : Fin n => Cv r c ≠ 0)).card ≤ s))

/-- Defines the precision-bit count as `Nat.ceil (Real.log (1/prec)/Real.log 2) + 1`. -/
noncomputable def sdpPrecisionBits (prec : ℝ) : ℕ :=
  Nat.ceil (Real.log (1 / prec) / Real.log 2) + 1

/-- Defines the integer storage charge for `words` words of `bits` bits as their product. -/
def sdpIntegerBits (words bits : ℕ) : ℕ := words * bits

/-- Defines the peak-space expression `3*(Nat.clog 2 (max 2 n) + Nat.clog 2 (max 2 m) +
precBits)`. -/
def sdpPeakSpaceBits (n m : ℕ) (precBits : ℕ) : ℕ :=
  3 * (Nat.clog 2 (max 2 n) + Nat.clog 2 (max 2 m) + precBits)

/-- For `0 < ε ≤ 1/2`, requires a legal finite gate word of length at most `(64*D+128)*(Nat.ceil
((1/ε)^2)+1)` and width at most `2*D+sdpIntegerBits 2 tableBits+8`. This predicate specifies
word legality and size bounds without relating the word to a target operation. -/
def HasSdpFixedGateBackend (D : ℕ) (tableBits : ℕ) (ε : ℝ) : Prop :=
  0 < ε → ε ≤ 1 / 2 →
    ∃ (w : ℕ) (gs : List FiniteGateCode),
      finiteWordLegal w gs = true ∧
        gs.length ≤ (64 * D + 128) * (Nat.ceil ((1 / ε) ^ 2) + 1) ∧
        w ≤ 2 * D + sdpIntegerBits 2 tableBits + 8

end Qatlib.Concepts.SdpDuality.ConeSeparation
