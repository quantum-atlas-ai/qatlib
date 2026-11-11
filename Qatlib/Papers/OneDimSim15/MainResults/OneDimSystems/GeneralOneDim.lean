/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneDimSim15.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# OneDimSim15 — Section VI: general one-dimensional systems

Claim `c007` of the fixed source arXiv:1503.06319v2: Theorem 7 (p. 11,
Eq. (56)), the simulation of `U^d(t) = exp(-i H^d t)` on arbitrary low-energy
superpositions `sum_{n <= N'} c_n |phi_n^d>` using
`O(N |t| polylog(N |t| / eps))` two-qubit gates, with
`N = O(N' log N')`.  The statement is recorded below as a `Prop`-valued
definition; its proof is not formalised.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OneDimSim15.MainResults.OneDimSystems

open Qatlib.Papers.OneDimSim15.MainResults
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The low-energy superposition `sum_{n=0}^{N'} c_n |phi_n^d>` of Theorem 7. -/
def eigenSum (N' N : ℕ) (c : ℕ → ℂ) (φ : ℕ → Fin N → ℂ) : Fin N → ℂ :=
  Finset.sum (Finset.range (N' + 1)) (fun n => c n • φ n)

/-- Fixed arXiv:1503.06319v2, Theorem 7 (p. 11, Eq. (56)): there are constants
`C > 0`, `N_0 >= 1` and `m : ℕ` such that for every `eps in (0, 1/2]`, every
`N'`, every `1 <= |t|`, there is `N = O(N' log N')` with `N' <= C N` and a
compiled unitary `W` with gate count `O(N |t| polylog(N |t| / eps))` such that
`||(W - U^d(t)) phi^d|| <= eps` for every unit-norm low-energy superposition
`phi^d = sum_{n <= N'} c_n |phi_n^d>` whose `|phi_n^d>` are normalized
approximate eigenstates of `H^d`. -/
def theorem7_general_one_dim : Prop :=
    ∃ C N₀ : ℝ, 0 < C ∧ 1 ≤ N₀ ∧ ∃ m : ℕ,
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
        ∀ (N' : ℕ) (t : ℝ), 1 ≤ |t| → N₀ ≤ (N' : ℝ) →
          ∃ N : ℕ, 2 ≤ N ∧ (N' : ℝ) ≤ C * (N : ℝ) ∧
            (N : ℝ) ≤ C * (N' : ℝ) * Real.log ((N' : ℝ)) + 2 ∧
            ∃ W : CompiledUnitary N,
              W.gateCount ≤ C * (N : ℝ) * |t| *
                (Real.log ((N : ℝ) * |t| / ε)) ^ m ∧
              ∀ (c : ℕ → ℂ) (φ : ℕ → Fin N → ℂ),
                (∀ n, N' < n → c n = 0) →
                (∀ n, n ≤ N' → ApproxEigenstate N n (φ n) (Real.exp (-(N : ℝ)))) →
                Finset.sum (Finset.range (N' + 1)) (fun n => Complex.normSq (c n)) = 1 →
                vNorm (W.mat.mulVec (eigenSum N' N c φ) -
                  (evolveOp N t).mulVec (eigenSum N' N c φ)) ≤ ε

end Qatlib.Papers.OneDimSim15.MainResults.OneDimSystems
