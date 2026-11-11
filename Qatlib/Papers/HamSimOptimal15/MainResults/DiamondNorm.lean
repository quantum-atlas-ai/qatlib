/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorLeft

set_option backward.isDefEq.respectTransparency false

/-!
# DiamondNorm — Lemma 7 of arXiv:1501.01715v3

Paper: Berry–Childs–Kothari, *Hamiltonian simulation with nearly optimal
dependence on all parameters*, arXiv:1501.01715v3 (2015-12-07), Lemma 7 on p.9 and
its proof in the Appendix (p.18–19, eq.(61)–(83)).

Lemma 7 states two bounds.

1. For operators `U, V` with `‖U‖ ≤ 1`, `‖V‖ ≤ 1`, the diamond-norm distance
   `‖U − V‖_⋄` of the conjugation channels is at most `2‖U − V‖` (eq.(77)).
   The lemma in the repository is `finiteDiamondNorm`, the completely bounded trace
   norm over all finite reference registers (unnormalised, without the `1/2` factor).
   The paper's proof (74)–(77) bounds the trace-norm distance of `UρU†` and `VρV†`
   blockwise and then maximises over `ρ`; the repository already contains the
   per-input estimate as `finite_reference_conjugation_error` (Foundations,
   `RefTraceError`), so the bound follows by turning that estimate into the uniform
   raw-matrix bound via `finiteDiamondNorm_le_iff_uniform`.

2. If `V` is a genuine quantum channel `ρ ↦ VρV† + ∑_j V_jρV_j†` with
   `V†V + ∑_j V_j†V_j = 1` and `U(ρ) = UρU†`, then `‖U − V‖_⋄ ≤ 4‖U − V‖`
   (eq.(79)–(83)).  This part is recorded as a statement and is not proved here;
   the obstruction is described on the theorem.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open scoped Matrix.Norms.L2Operator BigOperators ENNReal

namespace Qatlib.Papers.HamSimOptimal15.MainResults

/-- **Lemma 7 (operator/conjugation form), arXiv:1501.01715v3 p.9 eq.(77)**:
for unitaries `U, V` on a `D`-dimensional space, the completely bounded trace norm of
the conjugation-channel difference `X ↦ U X U† − V X V†` is at most
`2‖U − V‖`.  Unitaries satisfy the paper's hypothesis `‖U‖ ≤ 1`, `‖V‖ ≤ 1`.

Proof route.  The paper (eq.(74)–(76)) shows
`‖UρU† − VρV†‖₁ ≤ 2‖U − V‖·‖ρ‖₁` for every (mixed) input `ρ`, tensors with the
identity, and then maximises over `ρ` (eq.(77)).  The per-input estimate, uniformly
in the reference register, is the repository theorem
`finite_reference_conjugation_error`; rewriting `tensorLeft` of a conjugation branch
with `tensorLeft_conjBranch` and applying `finiteDiamondNorm_le_iff_uniform` gives the
diamond bound.  (The repository's `finiteDiamondNorm` omits the conventional factor
`1/2`, and the paper's Lemma 7 is also stated without it, so the constants agree.) -/
theorem lemma7_operator_diamond_norm_le {D : ℕ} (U V : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    finiteDiamondNorm (conjBranch U - conjBranch V) ≤ ENNReal.ofReal (2 * ‖U - V‖) := by
  have hd : 0 ≤ 2 * ‖U - V‖ := by positivity
  refine (finiteDiamondNorm_le_iff_uniform D D (conjBranch U - conjBranch V)
    (2 * ‖U - V‖) hd).mpr ?_
  intro r X
  rw [diamond_tensorLeft_map_sub, tensorLeft_conjBranch, tensorLeft_conjBranch]
  exact finite_reference_conjugation_error U V r X hU hV

/-- **Lemma 7 (channel form), arXiv:1501.01715v3 p.9, eq.(79)–(83)**:
if `V(ρ) = V₀ρV₀† + ∑_j V_jρV_j†` is a channel (`V₀†V₀ + ∑_j V_j†V_j = 1`) and
`U(ρ) = UρU†` for a unitary `U`, then `‖U − V‖_⋄ ≤ 4‖U − V₀‖`.

Registered as a proposition, not proved.  Everything is fixed to
arXiv:1501.01715v3.  The paper's argument is eq.(79):
`Tr(V₀ρV₀†) ≥ 1 − 2‖U − V₀‖` for every normalised state `ρ`, hence
(81) `‖∑_j V_jρV_j†‖₁ ≤ 2‖U − V₀‖`, which together with part 1 gives
`‖C − U‖_⋄ ≤ 4‖U − V₀‖` by splitting `C(ρ) − UρU†` into
`(V₀ρV₀† − UρU†) + ∑_j V_jρV_j†` and taking the maximum over `ρ`.

Current Lean gap: (i) the paper's (79)–(81) step is stated only for normalised states
`ρ` with `Tr ρ = 1`, but `finiteDiamondNorm` maximises over all raw matrices with
`‖X‖₁ ≤ 1`, including non-positive-semidefinite `X` whose trace need not be `1`; a
faithful formalisation therefore needs the standard reduction from raw matrices to
states (or the observation that the extremum is attained at a state, which is not in
the repository); (ii) there is no lemma stating `Tr(V₀ρV₀†) ≥ 1 − 2‖U − V₀‖` for
`ρ` a state, nor the "trace of a nonnegative Hermitian matrix equals its trace norm"
step (`Matrix.PosSemidef.traceNorm_eq_trace` exists but the inequality above does not).

Candidate reusable dependencies:
`finite_reference_conjugation_error`,
`QuantumAlgorithm.Papers.RandCompiler19.ChannelBudget.finiteDiamondNorm_le_iff_uniform`,
`QuantumAlgorithm.Papers.RandCompiler19.ChannelBudget.finiteDiamondNorm_algebra`
(triangle inequality), `Matrix.PosSemidef.traceNorm_eq_trace`,
`QuantumAlgorithm.Foundations.AdaptiveCP.BranchTrace.trace_conjBranch_unitary`.

Suggested follow-up tactic: prove the state-level inequality
`1 - 2 * ‖U - V₀‖ ≤ (Matrix.trace (conjBranch V0 ρ)).re` for `ρ` PSD with unit trace
by `abs_trace_le_traceNorm` + `traceNorm_add_le` on
`UρU† − V₀ρV₀†`, then extend the uniform bound from states to raw matrices by
`Matrix.PosSemidef` decomposition of `X` into Hermitian positive and negative parts. -/
def lemma7_channel_diamond_norm_le {D : ℕ} (m : ℕ)
    (U V0 : Matrix (Fin D) (Fin D) ℂ) (Vj : Fin m → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin D) ℂ →
  V0ᴴ * V0 + ∑ j : Fin m, (Vj j)ᴴ * Vj j = 1 →
  finiteDiamondNorm (conjBranch V0 + ∑ j : Fin m, conjBranch (Vj j) - conjBranch U) ≤
    ENNReal.ofReal (4 * ‖U - V0‖)

end Qatlib.Papers.HamSimOptimal15.MainResults
