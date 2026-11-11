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

## Proof status (scaffolds removed; statements in branch history c93d182c6)

* Fixed source: arXiv:2608.18839v3, Theorem 1.3, proof in §5.1 (Le Cam's
  two-point method, Definition 5.2 hard instances, Theorem 5.3 normalization,
  Lemma 5.4 KL bound, Theorem 5.6 mutual information).
* Key proof route: (i) hard-instance ensemble `σ_z = ρ_mm + Δ_z` over
  `z ~ Rad(1/2)^{⊗ℓ}` with `ℓ = Θ(log(4^N / …))`; (ii) Le Cam's inequality
  bounds the testing error by the total variation / KL between the mixture
  outcome law and the maximally mixed outcome law; (iii) Lemma 5.4 bounds the
  KL divergence by `(c² ln4 ε²/ℓ) ‖L_M‖_op · Σ_m I(z_m; x^i)`; (iv) Theorem 5.6
  bounds the mutual information by `n·ℓ` (one bit per copy through the MIC);
  (v) trading `ε²` versus `n` and inverting gives the stated `Ω`.
* Lean gap: Le Cam's two-point inequality, the KL divergence chain rule for
  adaptive transcript laws, and the spectral-norm conversion between channel
  norms and total variation are not formalized.  The statement records the
  faithful lower-bound shape for the paper-local model.
* Reusable dependencies: `SourceModel.micMap`, `micForm`, `micOperatorNorm`,
  `micTraceNorm`, `MeasurementModel.micLop`, `MeasurementModel.micL1`,
  `MeasurementModel.micScale`, `AdaptiveFamilyProtocol`,
  `adaptiveAcceptProb`, `hardInstanceDelta`, `hardInstanceState`.
  The KL bound will be reused from `LowerBound/KLBound.lean` (Lemma 5.4).
* Suggested tactics: start from `IsAdaptiveMixednessTester` and Le Cam
  (`‖p - q‖₁² ≤ 2 d_KL(p‖q)` after Pinsker), use the transcript factorization
  of `adaptiveTranscriptMass`, then `nlinarith` for the asymptotic inversion
  (`4^N = (2^N)²`, `ε²` denominators).
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.LowerBound


end Qatlib.Papers.MixednessTest26.MainResults.LowerBound
