/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# MIC lower-bound framework (Theorem 1.3)

Paper: arXiv:2608.18839v3, Theorem 1.3 (page 3 of the PDF):

> To perform mixedness testing with adaptively chosen measurements from `M`, we
> need at least `n = Ω(4^N / (ε² √(‖L_M‖_op ‖L_M‖₁)))` total copies, where
> `‖L_M‖_* = sup_{M ∈ M} ‖L_M‖_*`.

Here `L_M` is the measurement information channel (MIC) of §5.1: for a POVM
`{M_x}`, `L_M(Δ) = Σ_x (Tr(M_x Δ)/Tr M_x) M_x`, and the norms are the operator
and trace norms of that channel, taken as suprema over the measurement family
`M`.  The model is `MeasurementModel N` (a finite-outcome POVM family with
`k` outcomes) together with `AdaptiveFamilyProtocol`, whose transcript mass is
defined through the Born rule for adaptively chosen measurements.

The protocol is required to draw its measurements from the model family:
`∀ m, ∃ m₀, T.effect m = hmodel.effect m₀`.

## Mathematical background and scope

* Fixed source: arXiv:2608.18839v3, Theorem 1.3, proof in §5.1 (Le Cam's
  two-point method, Definition 5.2 hard instances, Theorem 5.3 normalization,
  Lemma 5.4 KL bound, Theorem 5.6 mutual information).
* Proof outline: (i) hard-instance ensemble `σ_z = ρ_mm + Δ_z` over
  `z ~ Rad(1/2)^{⊗ℓ}` with `ℓ = Θ(log(4^N / …))`; (ii) Le Cam's inequality
  bounds the testing error by the total variation / KL between the mixture
  outcome law and the maximally mixed outcome law; (iii) Lemma 5.4 bounds the
  KL divergence by `(c² ln4 ε²/ℓ) ‖L_M‖_op · Σ_m I(z_m; x^i)`; (iv) Theorem 5.6
  bounds the mutual information by `n·ℓ` (one bit per copy through the MIC);
  (v) trading `ε²` versus `n` and inverting gives the stated `Ω`.
* Scope note: this module imports the paper-local model and describes the
  lower-bound framework. Le Cam's two-point inequality, the KL divergence
  chain rule for adaptive transcript laws, and the spectral-norm conversion
  between channel norms and total variation are outside the scope of this file.
* Related definitions: `SourceModel.micMap`, `micForm`, `micOperatorNorm`,
  `micTraceNorm`, `MeasurementModel.micLop`, `MeasurementModel.micL1`,
  `MeasurementModel.micScale`, `AdaptiveFamilyProtocol`,
  `adaptiveAcceptProb`, `hardInstanceDelta`, `hardInstanceState`.
  The quantities in Lemma 5.4's KL bound are defined in `LowerBound/KLBound.lean`.
* For an `IsAdaptiveMixednessTester`, Le Cam's method and Pinsker's inequality
  (`‖p - q‖₁² ≤ 2 d_KL(p‖q)`) relate testing error to transcript divergence.
  The factorization of `adaptiveTranscriptMass` gives the adaptive chain rule;
  the final asymptotic inversion uses `4^N = (2^N)²` and the `ε²` denominators.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.LowerBound


end Qatlib.Papers.MixednessTest26.MainResults.LowerBound
