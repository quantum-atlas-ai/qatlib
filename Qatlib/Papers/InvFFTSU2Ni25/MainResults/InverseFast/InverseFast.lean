/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.InvFFTSU2Ni25.MainResults.SourceModel.SourceModel

@[expose] public section


/-!
# InvFFTSU2Ni25 / MainResults — the inverse nonlinear FFT

Fixed paper: arXiv:2505.12615v1, Hongkang Ni, Rahul Sarkar, Lexing Ying, Lin Lin.
Source: Algorithm 1 and item (ii) of the paper's list of contributions (PDF p. 2,
Section 4.2 pp. 13--19); numerical stability is Theorem 5.6 (Section 5.5).

Claim (ii): the standard layer-stripping algorithm costs `O(n²)`; Algorithm 1 (the
inverse nonlinear FFT) computes the same inverse NLFT with `O(n log² n)` arithmetic
operations and `O(n)` space, and is numerically stable under the assumptions of
Theorem 5.6.

The exact inverse and the operation counts are *not* reproved here: the shared
implementation block `Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline`
already contains a complete proof (`algorithm1`, `algorithm1Finite`,
`layerStripSU2_operations`, `inverseNLFFTFiniteSU2_operations`). This paper-layer
theorem reassembles them into the paper's single statement; the numerical-stability
clause (bits of precision `O(log² n + log n log η⁻¹ + log ε⁻¹)`) is the separate
`theorem5_6_numerical_stability`, since it is an independent
analysis result rather than an operation count.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Polynomial

namespace Qatlib.Papers.InvFFTSU2Ni25.MainResults

open Qatlib.Concepts.NativeNumerics.NlfftPipeline
open Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline

/-- complexity part (paper item (ii), Section 4.2, Algorithm 1):
for an input pair `(A, B) = (a*, b)` of degree `≤ d` satisfying the SU(2) identity,
the finite-FFT inverse nonlinear FFT
* returns `d + 1` read-off coefficients whose forward NLFT is exactly `(A, B)`,
* uses at most `2048 (d+1) (⌈log₂(d+1)⌉ + 5)²` arithmetic operations (the paper's
  `O(n log² n)` bound), and
* the classical layer-stripping baseline costs exactly `3 (d+1)² + 8 (d+1)` = `O(n²)`.

The numerical-stability clause of item (ii) is `theorem5_6_numerical_stability`. -/
theorem mainResult_inverseFast (d : ℕ) (A B : Polynomial ℂ)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d)
    (hid : A * conjRevN d A + B * conjRevN d B = X ^ d)
    (h0im : (A.coeff 0).im = 0) (h0re : 0 < (A.coeff 0).re) :
    (inverseNLFFTFiniteSU2 A B (d + 1)).gammas.length = d + 1 ∧
    nlftSU2 (inverseNLFFTFiniteSU2 A B (d + 1)).gammas = (A, B) ∧
    (inverseNLFFTFiniteSU2 A B (d + 1)).operations
      ≤ 2048 * (d + 1) * (Nat.clog 2 (d + 1) + 5) ^ 2 ∧
    (layerStripSU2 A B (d + 1)).operations = 3 * (d + 1) ^ 2 + 8 * (d + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inverseNLFFTFiniteSU2_gammas_length A B (d + 1)
  · have hex : LayerStripExact A B (d + 1) :=
      layerStripExact_of_pos A B (d + 1) h0im h0re
    have hsame := inverseNLFFTFiniteSU2_gammas A B (d + 1) hex
    rw [hsame.1]
    exact (layerStripSU2_correct d A B hA hB hid h0im h0re).1
  · exact inverseNLFFTFiniteSU2_operations A B (d + 1) (by omega)
  · exact layerStripSU2_operations A B (d + 1)

/-- quotient form: the fast inverse costs at most
`2048 n (⌈log₂ n⌉ + 5)²` operations at `n = d + 1` coefficients, while the baseline
costs `3 n² + 8 n`; this is the paper's `O(n log² n)` versus `O(n²)` comparison. -/
theorem mainResult_inverseFast_cost_comparison (n : ℕ) (hn : 1 ≤ n)
    (A B : Polynomial ℂ) :
    (inverseNLFFTFiniteSU2 A B n).operations ≤ 2048 * n * (Nat.clog 2 n + 5) ^ 2 ∧
    (layerStripSU2 A B n).operations = 3 * n ^ 2 + 8 * n :=
  ⟨inverseNLFFTFiniteSU2_operations A B n hn, layerStripSU2_operations A B n⟩

end Qatlib.Papers.InvFFTSU2Ni25.MainResults
