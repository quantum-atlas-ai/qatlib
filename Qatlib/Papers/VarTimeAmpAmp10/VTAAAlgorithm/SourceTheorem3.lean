/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmplificationAnswers
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

set_option backward.isDefEq.respectTransparency false

/-!
# Source Theorem 3 — the QLS running time

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  Theorem 3 is printed on p.4 (§2.2).

Source statement.  Let `C` be such that the evolution of the Hamiltonian `H`
for time `T` can be simulated in time `C·min(T,1)`.  Then we can generate
`|ψ′⟩` satisfying `‖ψ − ψ′‖ ≤ ε` in time

  `O(C·κ·log³(κ/ε)/ε³ · log²(1/ε))`.

The frozen library proves this endpoint as
`Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.clause66`: for every QLS
input there is one paid two-slot program whose readout has success mass above
`1/2`, whose output state is within trace distance `ε` of the normalized
pseudo-inverse solution, and whose charged unit-price access time is at most
`K` times the frozen cost shape `qlsThm3Cost Csim κ ε` — which is exactly
`C·κ·log³(κ/ε)/ε³·log²(1/ε)`.

The paper-layer theorem below restates the source conclusion (success `> 1/2`,
output within `ε`, cost `O(qlsThm3Cost)`) and derives it from `clause66`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped Classical BigOperators

set_option maxHeartbeats 2000000

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

/-- Fixed arXiv:1010.4458v2, Theorem 3 (printed p.4).

There is an absolute constant `K > 0` such that for every QLS input
(`qlsThm3Input`: spectral window `1/κ ≤ λ ≤ 1`, normalized right-hand side with
a solution, projected access, preparation access, error `0 < ε < 1/4`, and the
Hamiltonian-simulation constant `Csim`) there is one paid program whose run has
success mass `> 1/2` on the readout, whose output state is within trace-norm
`ε` of the normalized pseudo-inverse solution, and whose unit-price access cost
is at most `K·qlsThm3Cost Csim κ ε = K·Csim·κ·log³(κ/ε)/ε³·log²(1/ε)`.

Reused frozen result:
`Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.clause66` (with its
`UniqueEstData` block; only the source-visible success/error/cost conclusions
are kept here). -/
theorem source_theorem3 :
    ∃ K : ℝ, 0 < K ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (UA UB : Matrix H H ℂ) (L R : Matrix H I ℂ)
        (ω : QState H) (b : QState I) (κ Csim ε : ℝ),
        qlsThm3Input A UA UB L R ω b κ Csim ε →
        ∃ (prog : VtAmpProgram H) (hr : 0 < prog.r),
          stateGuarantee R prog.readout
            (run hr (pairOracles UA UB) prog.word ω)
            (normState (matrixPseudoinverse A *ᵥ b)) ε ∧
          ((prog.accessTime (fun _ => 1) : ℝ) ≤ K * qlsThm3Cost Csim κ ε) := by
  obtain ⟨K, hK, hgen⟩ := clause66
  refine ⟨K, hK, ?_⟩
  intro H I _ _ _ _ A UA UB L R ω b κ Csim ε hinput
  obtain ⟨prog, hr, sh, fa, est, pre, post,
    hlegal, huest, hword, hstate, hvec, hcost⟩ := hgen H I A UA UB L R ω b κ Csim ε hinput
  exact ⟨prog, hr, hstate, hcost⟩

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
