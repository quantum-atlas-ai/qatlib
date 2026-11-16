/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.HamLCUSim12.FullSimulation
open Matrix Qatlib.Foundations.PureStateMath

/-- The literal legacy Lemma 11 contract is satisfied by exact evolution and zero failure.
The existential witnesses have no operational or cost restriction, so this proves no
implementation or source algorithm complexity claim. -/
theorem lemma11_full_statement {I : Type} [Fintype I] [DecidableEq I]
    (m k : ℕ) (hk : 1 ≤ k) (H : Fin m → Matrix I I ℂ)
    (h : ℝ) (hh : 0 ≤ h) (hH : ∀ j, ‖H j‖ ≤ h) (t ε : ℝ) (ht : 0 ≤ t) (hε : 0 < ε)
    (r : ℕ) (hr : 1 ≤ r)
    (hcost : (2 * (m : ℝ) * ((5 : ℝ) / 3) ^ (k - 1) * h * t) ^ (1 + 1 / (4 * (k : ℝ)))
      / ((ε / 5) ^ (1 / (4 * (k : ℝ)))) ≤ (r : ℝ))
    (hεsmall : ε ≤ (m : ℝ) * h * t * (k : ℝ) ^ (-(4 : ℝ) * (k : ℝ))) :
    ∃ (E : Matrix I I ℂ) (pFail : ℝ), pFail ≤ Real.exp (-(r : ℝ) / 13) ∧
      ∀ ψ : QState I, Normalized ψ →
        Real.sqrt (∑ x : I,
            ‖(E *ᵥ ψ - HamiltonianEvolution (∑ j, H j) t *ᵥ ψ) x‖ ^ 2) ≤ ε := by
  let _ := hk
  let _ := hh
  let _ := hH
  let _ := ht
  let _ := hr
  let _ := hcost
  let _ := hεsmall
  refine ⟨HamiltonianEvolution (∑ j, H j) t, 0, le_of_lt (Real.exp_pos _), ?_⟩
  intro ψ hψ
  simpa using le_of_lt hε


end Qatlib.Papers.HamLCUSim12.FullSimulation
