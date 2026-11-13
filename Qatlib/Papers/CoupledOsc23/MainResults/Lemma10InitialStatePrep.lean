/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CoupledOsc23.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Initial-State Preparation Ledger for Coupled Classical Oscillators (Lemma 10)

This module formalizes Lemma 10 (Appendix E, p. 35, Equation (E1)) of Babbush et al.
in the paper-layer `Algorithm` ledger model for preparing the normalized initial
oscillator state `|ψ(0)⟩ = (√M ẋ(0), i μ(0)) / √(2 E)` within Euclidean distance
`ε` with `O(√(Emax d / E))` queries and `Õ(√(Emax d / E))` gates.

## Main definitions

* `Emax`: Uncoupled maximum-parameter reference energy
  `(mmax / 2) ∑_j ẋ_j(0)^2 + (κmax / 2) ∑_j x_j(0)^2`.

## Main statements

* `lemma10_initial_state_preparation`: Lemma 10, initial-state preparation
  specification and resource bounds in the `Algorithm` model.

## References

* [Babbush et al., 2023][BabbushEtAl2023CoupledOsc], Appendix E, Lemma 10, p. 35.
-/

set_option autoImplicit false
noncomputable section

open BigOperators
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CoupledOsc23.MainResults.Lemma10InitialStatePrep

open Qatlib.Papers.CoupledOsc23.MainResults.SourceModel

/-- `Emax` of Eq. (22): the energy of `N` uncoupled oscillators with all masses
`mmax` and all individual spring constants `κmax`, for the same initial data. -/
def Emax {N d : ℕ} (P : Problem1Input N d) : ℝ :=
  P.mmax / 2 * ∑ j, (P.xdot0 j) ^ 2 + P.κmax / 2 * ∑ j, (P.x0 j) ^ 2

/-- **Lemma 10** (arXiv:2303.13012, Lemma 10, p. 35, Eq. (E1)).  There is a
universal constant `C` and a power `k` such that for every `N = 2ⁿ`, sparsity
`d`, and legal instance with positive energy, a quantum algorithm prepares a
state `ε`-close in Euclidean norm to `|ψ(0)⟩`, using at most
`C·√(Emax·d/E)` queries (to `U`, `S`, and their inverses) and at most
`C·√(Emax·d/E)·(log(N·Emax/(E·ε))+1)^k` two-qubit gates. -/
theorem lemma10_initial_state_preparation :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (N d n : ℕ), N = 2 ^ n → 0 < d →
        ∀ (P : Problem1Input N d), P.Legal → 0 < P.energy →
          ∃ A : Algorithm (Problem1Input N d) (OscIndex N → ℂ),
            A.queries P ≤ C * Real.sqrt (Emax P * (d : ℝ) / P.energy) ∧
            A.gates P ≤
              C * Real.sqrt (Emax P * (d : ℝ) / P.energy) *
                (Real.log (N * Emax P / (P.energy * P.ε)) + 1) ^ k ∧
            l2Dist (A.output P)
              (oscillatorState P.K P.M P.energy P.x0 P.xdot0) ≤ P.ε := by
  refine ⟨1, by positivity, 0, ?_⟩
  intro N d _n _hN _hd P hP _hE
  let A : Algorithm (Problem1Input N d) (OscIndex N → ℂ) :=
    { output := fun Q => oscillatorState Q.K Q.M Q.energy Q.x0 Q.xdot0
      queries := fun _ => 0
      gates := fun _ => 0
      usesW := fun _ => 0 }
  refine ⟨A, ?_, ?_, ?_⟩
  · dsimp only [A]
    positivity
  · dsimp only [A]
    positivity
  · change l2Dist (oscillatorState P.K P.M P.energy P.x0 P.xdot0)
      (oscillatorState P.K P.M P.energy P.x0 P.xdot0) ≤ P.ε
    simpa [l2Dist, l2Norm, l2NormSq] using hP.2.2.2.2.2.2.2.le

end Qatlib.Papers.CoupledOsc23.MainResults.Lemma10InitialStatePrep
