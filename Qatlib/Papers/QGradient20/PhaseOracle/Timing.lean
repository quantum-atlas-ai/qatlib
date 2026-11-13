/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.PhaseOracle.HermitianQpe

/-!
# Phase estimation with reciprocal register scaling

This module specializes Hermitian phase evolution to parameter `1 / M`. The results identify the
resulting eigenvector packet and the evolution time of each power. See [GaoEtAl2021] for the
paper context.

## Main statements

* `source_shrunk_actual_packet`: At evolution parameter `1 / M`, QPE on an eigenvector has phase
  kernel at `-λ / M` and preserves that eigenvector.
* `source_shrunk_power`: The `j`th power of evolution with parameter `1 / M` is Hamiltonian
  evolution at time `2 * π * j / M`.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Papers.QGradient20.PhaseOracle
namespace Qatlib.Papers.QGradient20.PhaseOracle.Timing
variable {I : Type} [Fintype I] [DecidableEq I]

/-- At evolution parameter `1 / M`, QPE on an eigenvector has phase kernel at `-λ / M` and
preserves that eigenvector. See [GaoEtAl2021]. -/
theorem source_shrunk_actual_packet (D : Matrix I I ℂ) (hD : D.IsHermitian) (M : ℕ) (j : I) :
    qpeOutput M (phaseEvolution D (1/(M:ℝ))) (hD.eigenvectorBasis j : I→ℂ)=
      TensorState (qpeKernel M (-hD.eigenvalues j/(M:ℝ))) (hD.eigenvectorBasis j : I→ℂ) := by
  have he : -(1/(M:ℝ))*hD.eigenvalues j= -hD.eigenvalues j/(M:ℝ) := by ring
  simpa only [he] using actual_eigen_qpe_packet D hD (1/(M:ℝ)) M j

/-- The `j`th power of evolution with parameter `1 / M` is Hamiltonian evolution at time `2 * π
* j / M`. -/
theorem source_shrunk_power (D : Matrix I I ℂ) (M j : ℕ) :
    phaseEvolution D (1/(M:ℝ))^j=HamiltonianEvolution D (2*Real.pi*(j:ℝ)/(M:ℝ)) := by
  simpa only [mul_one_div] using phaseEvolution_power D (1/(M:ℝ)) j

end Qatlib.Papers.QGradient20.PhaseOracle.Timing
