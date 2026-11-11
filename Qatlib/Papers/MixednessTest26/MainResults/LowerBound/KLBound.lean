/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MixednessTest26.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Distinguishability from the maximally mixed state (Lemma 5.4)

Paper: arXiv:2608.18839v3, Lemma 5.4 (page 18 of the PDF):

> Given the state ensemble defined in Definition 5.2,
> `E_{x^n} d_KL( q_{x^{i+1}|x^i} ‖ p_{x^{i+1}|x^i} )
>    ≤ (c² ln 4 · ε² / ℓ) ‖L_M‖_op Σ_{m=1}^ℓ I(z_m; x^i)`
> for `i = 1, 2, …, n`.

Here `z ~ Rad(1/2)^{⊗ℓ}` indexes the hard-instance ensemble
`σ_z = ρ_mm + Δ_z` of Definition 5.2, `q` is the outcome law under the mixture
`E_{z} σ_z` and `p` the outcome law under `ρ_mm`; `x^i` is the transcript of the
first `i` adaptively chosen measurements, and `I(z_m; x^i)` is the mutual
information between the `m`-th hard-instance bit and that transcript.  The
channel is the measurement information channel `L_M` of §5.1, with operator
norm sup'ed over the measurement family.

All transcript laws in this file are the Born-rule masses defined in
`Model/SourceModel.lean` (`adaptiveTranscriptMass`), so the statement is
coupled to the concrete protocol semantics.

## Proof status (scaffolds removed; statements in branch history c93d182c6)

* Fixed source: arXiv:2608.18839v3, Lemma 5.4, proof in §5.1 (equations
  (5)–(6) and the following Born-rule computation).
* Key proof route: (i) bound `d_KL(q‖p) ≤ d_{χ²}(q‖p)`; (ii) express the
  χ²-divergence through `β_i(x)² = (q(x)-p(x))²/p(x)`; (iii) use the Born rule
  `q(x) = Tr(M_x σ)` and `p(x) = Tr(M_x ρ_mm)` together with
  `Tr(M_x Δ_z) = (cε/(d√ℓ)) Σ_m z_m Tr(M_x V_m)`; (iv) Cauchy–Schwarz over
  the measurement information channel yields the `‖L_M‖_op` factor; (v) the
  chain rule for mutual information gives the sum `Σ_m I(z_m; x^i)`.
* Lean gap: the χ²-to-KL inequality for finite outcome laws, the Cauchy–Schwarz
  step over the MIC, and the mutual-information chain rule for the adaptive
  transcript factorization are not formalized.  The definitions below make the
  statement precise against the paper-local protocol model.
* Reusable dependencies: `SourceModel.micOperatorNorm`, `hardInstanceDelta`,
  `hardInstanceState`, `adaptiveTranscriptMass`; the (removed scaffold)
  `LowerBound/Framework.lean` and `LowerBound/SingleQubit.lean` statements.
* Suggested tactics: prove `Real.log_le_sub_one_of_pos`-based
  `d_KL ≤ d_χ²` for `Fin k` laws, expand `adaptiveTranscriptMass` recursively,
  apply `Finset.sum_le_sum` with a per-outcome Cauchy–Schwarz bound, then close
  the mutual-information identity by `Finset.sum_comm` and `Real.log` algebra.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MixednessTest26.MainResults.LowerBound

open Qatlib.Foundations.PureStateMath

/-- Supremum of the MIC operator norm over the measurement family of a protocol. -/
noncomputable def protocolMicLop {N k : ℕ} {M : Type}
    (T : AdaptiveFamilyProtocol N k M) : ℝ :=
  sSup {r : ℝ | ∃ m : M, r = micOperatorNorm (T.effect m)}

/-- Transcript mass of the hard-instance mixture `E_{z ~ Rad(1/2)^{⊗ℓ}} σ_z`
over a transcript `h`. -/
noncomputable def hardMixtureMass {N ℓ k : ℕ} {M : Type} (c ε : ℝ)
    (V : Fin ℓ → PauliObservable N) (T : AdaptiveFamilyProtocol N k M)
    (h : List (Fin k)) : ℝ :=
  (1 / (2 : ℝ) ^ ℓ) *
    ∑ z : Fin ℓ → Bool, adaptiveTranscriptMass T (hardInstanceState c ε V z) [] h

/-- Transcript mass of the maximally mixed state `ρ_mm` over a transcript `h`. -/
noncomputable def uniformTranscriptMass {N k : ℕ} {M : Type}
    (T : AdaptiveFamilyProtocol N k M) (h : List (Fin k)) : ℝ :=
  adaptiveTranscriptMass T
    (maximallyMixed (2 ^ N) (two_pow_pos N)).1 [] h

/-- Conditional probability of the next outcome `x` given the transcript `h`,
under the hard-instance mixture (likelihoods are the Born masses of the mixture
and of its prefix). -/
noncomputable def hardConditionalMass {N ℓ k : ℕ} {M : Type} (c ε : ℝ)
    (V : Fin ℓ → PauliObservable N) (T : AdaptiveFamilyProtocol N k M)
    (h : List (Fin k)) (x : Fin k) : ℝ :=
  (∑ z : Fin ℓ → Bool,
      adaptiveTranscriptMass T (hardInstanceState c ε V z) [] (h ++ [x])) /
    (∑ z : Fin ℓ → Bool,
      adaptiveTranscriptMass T (hardInstanceState c ε V z) [] h)

/-- Conditional probability of the next outcome `x` given the transcript `h`,
under the maximally mixed state. -/
noncomputable def uniformConditionalMass {N k : ℕ} {M : Type}
    (T : AdaptiveFamilyProtocol N k M) (h : List (Fin k)) (x : Fin k) : ℝ :=
  adaptiveTranscriptMass T (maximallyMixed (2 ^ N) (two_pow_pos N)).1 [] (h ++ [x]) /
    adaptiveTranscriptMass T (maximallyMixed (2 ^ N) (two_pow_pos N)).1 [] h

/-- The Kullback–Leibler divergence `d_KL(q‖p) = Σ_x q(x) log(q(x)/p(x))` of two
finitely supported laws on `Fin k`. -/
noncomputable def klDivVec {k : ℕ} (q p : Fin k → ℝ) : ℝ :=
  ∑ x, q x * Real.log (q x / p x)

/-- Expected conditional KL divergence after `i` transcript symbols, as in
Lemma 5.4: the average over the length-`i` transcript of the KL divergence
between the next-outcome laws under the hard-instance mixture and under `ρ_mm`. -/
noncomputable def expectedConditionalKL {N ℓ k : ℕ} {M : Type} (c ε : ℝ)
    (V : Fin ℓ → PauliObservable N) (T : AdaptiveFamilyProtocol N k M)
    (i : ℕ) : ℝ :=
  ∑ h : Fin i → Fin k,
    hardMixtureMass c ε V T (List.ofFn h) *
      klDivVec (hardConditionalMass c ε V T (List.ofFn h))
        (uniformConditionalMass T (List.ofFn h))

/-- Joint mass of the `m`-th hard-instance bit taking value `b` together with a
transcript `h`, under `z ~ Rad(1/2)^{⊗ℓ}`. -/
noncomputable def hardMassGivenBit {N ℓ k : ℕ} {M : Type} (c ε : ℝ)
    (V : Fin ℓ → PauliObservable N) (T : AdaptiveFamilyProtocol N k M)
    (m : Fin ℓ) (b : Bool) (h : List (Fin k)) : ℝ :=
  (1 / (2 : ℝ) ^ (ℓ - 1)) *
    ∑ z : Fin ℓ → Bool,
      if z m = b then adaptiveTranscriptMass T (hardInstanceState c ε V z) [] h
      else 0

/-- The mutual information `I(z_m; x^i)` between the `m`-th hard-instance bit
and the first `i` transcript symbols. -/
noncomputable def bitMutualInfo {N ℓ k : ℕ} {M : Type} (c ε : ℝ)
    (V : Fin ℓ → PauliObservable N) (T : AdaptiveFamilyProtocol N k M)
    (i : ℕ) (m : Fin ℓ) : ℝ :=
  ∑ b : Bool, (1 / 2 : ℝ) *
    ∑ h : Fin i → Fin k,
      hardMassGivenBit c ε V T m b (List.ofFn h) *
        Real.log (hardMassGivenBit c ε V T m b (List.ofFn h) /
          hardMixtureMass c ε V T (List.ofFn h))


end Qatlib.Papers.MixednessTest26.MainResults.LowerBound
