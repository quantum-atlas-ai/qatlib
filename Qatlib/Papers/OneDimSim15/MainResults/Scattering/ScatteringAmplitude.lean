/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneDimSim15.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# OneDimSim15 — Section IV: scattering amplitudes

Claims `c001`-`c003` of the fixed source arXiv:1503.06319v2:

* Theorem 1 (p. 5, Eq. (20)): the discrete overlap approximates the
  continuous-variable one with `N = O(log(1/eps) + N')`;
* Theorem 2 (p. 7, Eq. (31)): the Trotter-Suzuki state error, with the
  dimension/order/step-size scales of the paper;
* Theorem 3 (p. 7, Eq. (32)): the subexponential-time algorithm with
  `O(exp(gamma' sqrt(log N')))` two-qubit gates per run.
The three statements are recorded below as `Prop`-valued definitions; their
proofs are not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OneDimSim15.MainResults.Scattering

open Qatlib.Papers.OneDimSim15.MainResults
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Fixed arXiv:1503.06319v2, Theorem 1 (p. 5, Eq. (20)): there are constants
`C > 0` and `T > 0` such that for every `eps > 0`, every pair of coefficient
sequences `c, c'` supported in `0 .. N'` with unit norm, and every evolution
time `1 <= |t| <= T`, there is a dimension `N = O(log(1/eps) + N')` (with
`N' <= C N`) for which the discrete overlap `<phi'^d|U^d(t)|phi^d>` and both
position-eigenstate overlaps `<x_j|U(t)|phi>` are within `O(eps)` of their
continuous-variable values. -/
def theorem1_scattering_approximation : Prop :=
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
        ∀ (N' : ℕ) (c c' : ℕ → ℂ),
          (∀ n, N' < n → c n = 0) → (∀ n, N' < n → c' n = 0) →
          Finset.sum (Finset.range (N' + 1)) (fun n => Complex.normSq (c n)) = 1 →
          Finset.sum (Finset.range (N' + 1)) (fun n => Complex.normSq (c' n)) = 1 →
          ∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
            ∃ N : ℕ, 2 ≤ N ∧ (N : ℝ) ≤ C * (Real.log (1 / ε) + (N' : ℝ)) ∧
              (N' : ℝ) ≤ C * (N : ℝ) ∧
              ‖discOverlap N N' c c' t - cvOverlap N' c c' t‖ ≤ C * ε ∧
              (∀ j : Fin N,
                ‖vInner (basisVec j) ((evolveOp N t).mulVec (normalize (coeffVec N' N c))) -
                    cvPositionOverlap N N' c t j‖ ≤ C * ε)

/-- Fixed arXiv:1503.06319v2, Theorem 2 (p. 7, Eq. (31)): there are constants
`C > 0`, `T > 0`, `gamma > 0` such that for every initial state `phi^d` of
unit norm supported in `0 .. N'`, every `1 <= |t| <= T` and every `eps > 0`,
there are `N = O(exp(C sqrt(log(N'/eps))) + N')`, `p = Theta(sqrt(log(N'/eps)))`,
`k s = t` with `|s| = Theta(5^{-p})`, such that the `k`-th power of `U_p^d(s)`
approximates `U^d(t)` on `phi^d` to `O(eps)`, with at most
`O(exp(gamma sqrt(log(N'/eps))))` elementary exponentials. -/
def theorem2_trotter_state_error : Prop :=
    ∃ C T γ : ℝ, 0 < C ∧ 0 < T ∧ 0 < γ ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
        ∀ (N' : ℕ) (c : ℕ → ℂ),
          (∀ n, N' < n → c n = 0) →
          Finset.sum (Finset.range (N' + 1)) (fun n => Complex.normSq (c n)) = 1 →
          ∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
            ∃ (N p k : ℕ) (s : ℝ), 2 ≤ N ∧ 1 ≤ p ∧ 1 ≤ k ∧ (k : ℝ) * s = t ∧
              (N' : ℝ) ≤ C * (N : ℝ) ∧
              (N : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log ((N' : ℝ) / ε))) + C * (N' : ℝ) ∧
              C⁻¹ * Real.sqrt (Real.log ((N' : ℝ) / ε)) ≤ (p : ℝ) ∧
              (p : ℝ) ≤ C * Real.sqrt (Real.log ((N' : ℝ) / ε)) ∧
              C⁻¹ * Real.rpow 5 (-(p : ℝ)) ≤ |s| ∧
              |s| ≤ C * Real.rpow 5 (-(p : ℝ)) ∧
              vNorm (((trotterWord p N s) ^ k).mulVec (normalize (coeffVec N' N c)) -
                (evolveOp N t).mulVec (normalize (coeffVec N' N c))) ≤ C * ε ∧
              (trotterCount p : ℝ) * (k : ℝ) ≤
                C * Real.exp (γ * Real.sqrt (Real.log ((N' : ℝ) / ε)))

/-- Fixed arXiv:1503.06319v2, Theorem 3 (p. 7, Eq. (32)): there are constants
`C > 0`, `T > 0`, `gamma' > 0` such that for every pair of unit-norm
coefficient sequences supported in `0 .. N'`, every `1 <= |t| <= T` and every
`eps > 0`, there is a circuit `Q` with `O(exp(gamma' sqrt(log(N'/eps))))`
two-qubit gates whose amplitude is within `eps` of `<phi'|U(t)|phi>`, and for
every grid point `j` a circuit `Q_j` (same gate bound) approximating
`<x_j|U(t)|phi>`; the required dimension is
`N = O(exp(C sqrt(log(N'/eps))) + N')` with `N' <= C N`. -/
def theorem3_scattering_algorithm : Prop :=
    ∃ C T γ' : ℝ, 0 < C ∧ 0 < T ∧ 0 < γ' ∧
      ∀ (N' : ℕ) (c c' : ℕ → ℂ),
        (∀ n, N' < n → c n = 0) → (∀ n, N' < n → c' n = 0) →
        Finset.sum (Finset.range (N' + 1)) (fun n => Complex.normSq (c n)) = 1 →
        Finset.sum (Finset.range (N' + 1)) (fun n => Complex.normSq (c' n)) = 1 →
        ∀ (t : ℝ), 1 ≤ |t| → |t| ≤ T →
          ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
            ∃ (N : ℕ) (Q : PaperCircuit) (Qpos : Fin N → PaperCircuit),
              2 ≤ N ∧ (N' : ℝ) ≤ C * (N : ℝ) ∧
              (N : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log ((N' : ℝ) / ε))) + C * (N' : ℝ) ∧
              Q.gateCount ≤ Real.exp (γ' * Real.sqrt (Real.log ((N' : ℝ) / ε))) ∧
              ‖Q.amplitude - cvOverlap N' c c' t‖ ≤ ε ∧
              (∀ j : Fin N,
                (Qpos j).gateCount ≤ Real.exp (γ' * Real.sqrt (Real.log ((N' : ℝ) / ε))) ∧
                ‖(Qpos j).amplitude - cvPositionOverlap N N' c t j‖ ≤ ε)

end Qatlib.Papers.OneDimSim15.MainResults.Scattering
