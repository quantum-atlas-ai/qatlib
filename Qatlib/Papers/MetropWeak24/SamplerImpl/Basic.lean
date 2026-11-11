/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import Qatlib.Concepts.MatrixExpTrace.ExpPerturbation
import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.RankOneTraceNormEquality
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option backward.isDefEq.respectTransparency false

/-!
# Weak-measurement quantum Metropolis: shared vocabulary

Source: Jiaqing Jiang, Sandy Irani, *Quantum Metropolis Sampling via Weak
Measurement*, arXiv:2406.16023 (v1). This module fixes the paper-layer
vocabulary used by every claim of the `MetropWeak24.SamplerImpl` block.

* `QOp n` is the space of `n`-qubit operators `Operator (2 ^ n)`.
* `SuperOp n` is the space of linear superoperators on `QOp n`.
* `StarNorm T` is the paper's `|T|_⋆`, the induced trace norm (supremum of
  `|T A|_1` over `|A|_1 = 1`); it is Frozen's `InducedTraceNorm`.
* `SchattenOne A` is the paper's `|A|_1`, related to Physlib's
  `Matrix.traceNorm` by `schattenOne_eq_traceNorm`.
* `superExp L t` is `exp (t • L)` on superoperators, `evolve L t ρ = superExp L t ρ`.

The analytic toolkit below (triangle inequality, unitary invariance, trace
duality) is proved from Physlib's `Matrix.traceNorm` API.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.MetropWeak24.SamplerImpl

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ## Registers and superoperators -/

/-- The operator space of an `n`-qubit register, `|H(n)|`. -/
abbrev QOp (n : ℕ) := Operator (2 ^ n)

/-- Linear superoperators `H(n) → H(n)`. -/
abbrev SuperOp (n : ℕ) := QOp n →ₗ[ℂ] QOp n

/-- The paper's superoperator star norm `|T|_⋆` (induced trace norm). -/
noncomputable def StarNorm {n : ℕ} (T : SuperOp n) : ℝ := InducedTraceNorm T

/-- Local instance bridges letting `NormedSpace.exp` act on continuous linear
superoperators (same pattern as the frozen GKSL vocabulary). -/
local instance clmSeminormedRing {n : ℕ} :
    SeminormedRing (QOp n →L[ℂ] QOp n) :=
  ContinuousLinearMap.toSeminormedRing

local instance clmNormedAlgebra {n : ℕ} :
    NormedAlgebra ℂ (QOp n →L[ℂ] QOp n) :=
  ContinuousLinearMap.toNormedAlgebra

local instance clmIsTopologicalRing {n : ℕ} :
    IsTopologicalRing (QOp n →L[ℂ] QOp n) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- The superoperator exponential `exp (t • L)` of a generator `L`. -/
noncomputable def superExp {n : ℕ} (L : SuperOp n) (t : ℝ) : SuperOp n :=
  (NormedSpace.exp ((t : ℂ) • L.toContinuousLinearMap) :
    QOp n →L[ℂ] QOp n).toLinearMap

/-- The semigroup action `e^{tL}(ρ)`. -/
noncomputable def evolve {n : ℕ} (L : SuperOp n) (t : ℝ) (ρ : QOp n) : QOp n :=
  superExp L t ρ

/-- The Gibbs density matrix `ρ_β = e^{-βH}/tr e^{-βH}`. -/
noncomputable def gibbsState {n : ℕ} (H : QOp n) (β : ℝ) : QOp n :=
  (Matrix.trace (NormedSpace.exp (-(β) • H)))⁻¹ • NormedSpace.exp (-(β) • H)

/-! ## Trace-norm toolkit -/

/-- Repository `SchattenOne` (`cfc Real.sqrt` version) equals Physlib's
`Matrix.traceNorm` (`CFC.sqrt` version), pointwise. -/
theorem schattenOne_eq_traceNorm {D : ℕ} (A : Operator D) :
    SchattenOne A = Matrix.traceNorm A := by
  have hpsd : (A.conjTranspose * A).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self A
  rw [Matrix.traceNorm, SchattenOne,
    CFC.sqrt_eq_real_sqrt _ (Matrix.PosSemidef.nonneg hpsd),
    cfcₙ_eq_cfc (by fun_prop) (by simp)]
  rfl

/-- `|A|_1 ≥ 0`. -/
theorem schattenOne_nonneg {D : ℕ} (A : Operator D) : 0 ≤ SchattenOne A := by
  rw [schattenOne_eq_traceNorm]
  exact Matrix.traceNorm_nonneg A

/-- `|A + B|_1 ≤ |A|_1 + |B|_1`. -/
theorem schattenOne_add_le {D : ℕ} (A B : Operator D) :
    SchattenOne (A + B) ≤ SchattenOne A + SchattenOne B := by
  rw [schattenOne_eq_traceNorm, schattenOne_eq_traceNorm, schattenOne_eq_traceNorm]
  exact Matrix.traceNorm_add_le A B

/-- `|−A|_1 = |A|_1`. -/
theorem schattenOne_neg {D : ℕ} (A : Operator D) : SchattenOne (-A) = SchattenOne A := by
  rw [schattenOne_eq_traceNorm, schattenOne_eq_traceNorm, Matrix.traceNorm_neg]

/-- `|A − B|_1 = |B − A|_1`. -/
theorem schattenOne_sub_comm {D : ℕ} (A B : Operator D) :
    SchattenOne (A - B) = SchattenOne (B - A) := by
  rw [← schattenOne_neg (A - B), neg_sub]

/-- `|Aᴴ|_1 = |A|_1`. -/
theorem schattenOne_conjTranspose {D : ℕ} (A : Operator D) :
    SchattenOne (Aᴴ) = SchattenOne A := by
  rw [schattenOne_eq_traceNorm, schattenOne_eq_traceNorm, Matrix.traceNorm_conjTranspose]

/-- `|c • A|_1 = ‖c‖ · |A|_1`. -/
theorem schattenOne_smul {D : ℕ} (c : ℂ) (A : Operator D) :
    SchattenOne (c • A) = ‖c‖ * SchattenOne A := by
  rw [schattenOne_eq_traceNorm, schattenOne_eq_traceNorm, Matrix.traceNorm_smul]

/-- Trace duality: `‖tr A‖ ≤ |A|_1`. -/
theorem abs_trace_le_schattenOne {D : ℕ} (A : Operator D) :
    ‖Matrix.trace A‖ ≤ SchattenOne A := by
  rw [schattenOne_eq_traceNorm]
  exact Matrix.abs_trace_le_traceNorm A

/-- Sandwiching between contractions does not increase the trace norm. -/
theorem schattenOne_sandwich_le {D : ℕ} {S M T : Operator D}
    (hS : ‖S‖ ≤ 1) (hT : ‖T‖ ≤ 1) :
    SchattenOne (S * M * T) ≤ SchattenOne M := by
  rw [schattenOne_eq_traceNorm, schattenOne_eq_traceNorm]
  exact Matrix.traceNorm_sandwich_le hS hT

/-- The trace norm of a rank-one operator is bounded by the product of the
Hilbert norms of its two vectors. -/
theorem schattenOne_rankOne_le {D : ℕ} (u v : Fin D → ℂ) :
    SchattenOne (Matrix.vecMulVec u (star v)) ≤
      Real.sqrt ((∑ i, Complex.normSq (u i)) * (∑ i, Complex.normSq (v i))) := by
  rw [schattenOne_eq_traceNorm]
  exact Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_rankOne_le u v

end Qatlib.Papers.MetropWeak24.SamplerImpl
