/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SlowHamSim26.FourierTrunc.Definitions
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SlowHamSim26 / MainComplexity — cost profiles and the simulation target

Fixed source: arXiv:2608.17653v1, §6.1.2–§6.2.2 (Theorems 6.2 and 6.4, pp. 42–49)
and §7 (Corollary 7.1, p. 52).  This file fixes the interfaces used by the
main-complexity statements:

* `SoftO`, `SoftO2` — the paper's `Õ(·)` notation: a bound up to a constant and
  a polylogarithmic factor in the leading term;
* `SolvesSchrodinger T H U` — `U` is the exact propagator of
  `i dU/dt = H(t/T) U` with `U(0) = 1` (Eq. (1.1) after the slow rescaling);
* `DerivativeAccess` / `ControlAccess` — the Section 6.1.1 / 6.2.1 oracle
  interfaces (`HAM′-T`, `HOHAM-1`, `HOHAM-0` respectively `HAM-T`);
* `normalizeVec` / `ApproximationWithConstantSuccess` — the post-selection
  conclusion of Corollary 7.1: a subnormalised output with constant success
  probability whose normalisation is `ε`-close to the normalised exact solution.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SlowHamSim26.MainComplexity

open scoped Matrix.Norms.L2Operator
open Matrix
open Qatlib.Papers.SlowHamSim26.FourierTrunc

/-- `f = Õ(g)`: `f x ≤ C · g x · (log (g x + 2))^k` for all `x ≥ 1`, for some
constants `C, k ≥ 0` (the paper's soft-`O` notation). -/
def SoftO (f g : ℝ → ℝ) : Prop :=
  ∃ C k : ℝ, 0 ≤ C ∧ 0 ≤ k ∧
    ∀ x : ℝ, 1 ≤ x → f x ≤ C * g x * (Real.log (g x + 2)) ^ k

/-- `f(t, ε) = Õ(g(t, ε))` uniformly for `t ≥ 0` and `0 < ε ≤ 1`. -/
def SoftO2 (f g : ℝ → ℝ → ℝ) : Prop :=
  ∃ C k : ℝ, 0 ≤ C ∧ 0 ≤ k ∧
    ∀ t ε : ℝ, 0 ≤ t → 0 < ε → ε ≤ 1 →
      f t ε ≤ C * g t ε * (Real.log (g t ε + 2)) ^ k

/-- `U` solves the rescaled Schrödinger equation `i U' = H(t/T) U`, `U(0) = 1`
(Eq. (1.1) with `H̃(t) = H(t/T)`). -/
def SolvesSchrodinger {d : ℕ} (T : ℝ) (H : ℝ → Matrix (Fin d) (Fin d) ℂ)
    (U : ℝ → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  U 0 = 1 ∧ ∀ t : ℝ, HasDerivAt U ((-Complex.I) • (H (t / T) * U t)) t

/-- The Section 6.1.1 oracle interface of Theorem 6.2: `HAM′-T` acts on
`L(ε₂,K)` controlled blocks, `HOHAM-1` and `HOHAM-0` on `C(ε₂,K)+1` controlled
blocks.  This paper layer records the register structure and unitarity of the
three oracles; their block-encoding accuracy `ε₂` is part of the algorithm's
error budget and is not tracked separately. -/
structure DerivativeAccess (Lc Cc : ℕ) (d : ℕ) where
  hamT : Matrix (Fin Lc × Fin d) (Fin Lc × Fin d) ℂ
  hoham1 : Matrix (Fin (Cc + 1) × Fin d) (Fin (Cc + 1) × Fin d) ℂ
  hoham0 : Matrix (Fin (Cc + 1) × Fin d) (Fin (Cc + 1) × Fin d) ℂ
  hamT_unitary : hamT ∈ Matrix.unitaryGroup (Fin Lc × Fin d) ℂ
  hoham1_unitary : hoham1 ∈ Matrix.unitaryGroup (Fin (Cc + 1) × Fin d) ℂ
  hoham0_unitary : hoham0 ∈ Matrix.unitaryGroup (Fin (Cc + 1) × Fin d) ℂ

/-- The Section 6.2.1 oracle interface of Theorem 6.4:
`HAM-T = Σ_{j<jmax} |j⟩⟨j| ⊗ O_j` on the `jmax` control register.  The
individual block encodings `O_j` of the matrices `M_j` are folded into the
`HAM-T` unitary; the accuracy of the encodings is part of the error budget. -/
structure ControlAccess (jmax d : ℕ) where
  hamT : Matrix (Fin jmax × Fin d) (Fin jmax × Fin d) ℂ
  hamT_unitary : hamT ∈ Matrix.unitaryGroup (Fin jmax × Fin d) ℂ

/-- The paper's `L(s) ⪰ 0` for the complex matrix `L(s)` in the Cartesian
decomposition `A(s) = L(s) + i·H(s)` of Corollary 7.1: `L(s)` is Hermitian and
its quadratic form has nonnegative real part on every vector. -/
def HermitianNonneg {d : ℕ} (L : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  Lᴴ = L ∧ ∀ x : Fin d → ℂ,
    0 ≤ Complex.re (∑ i, star (x i) * ∑ j, L i j * x j)

/-- Normalisation `ψ ↦ ψ/‖ψ‖` of an amplitude vector. -/
def normalizeVec {d : ℕ} (ψ : Vec d) : Vec d := (1 / l2norm ψ) • ψ

/-- Fixed arXiv:2608.17653v1, Eq. (7.5) and its proof (p. 52): a subnormalised
output state (`‖out‖ ≤ 1`) produced with success probability `‖out‖² ≥ 1/2`
whose normalisation is `ε`-close to the normalised exact state. -/
def ApproximationWithConstantSuccess {d : ℕ} (out exactV : Vec d) (ε : ℝ) : Prop :=
  l2norm out ≤ 1 ∧ (1 / 2 : ℝ) ≤ l2norm out ^ 2 ∧
    l2norm (normalizeVec out - normalizeVec exactV) ≤ ε

end Qatlib.Papers.SlowHamSim26.MainComplexity
