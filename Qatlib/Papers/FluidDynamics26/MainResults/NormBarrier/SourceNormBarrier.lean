/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FluidDynamics26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# FluidDynamics26 — norm barriers, error PDE and the comparison principle

Fixed source: Ameri–Carolan–Childs–Krovi, *Quantum lower bounds for simulating fluid
dynamics*, arXiv:2603.12161v1 (12 March 2026).

Claims formalised here (paper theorem/equation/page):

* c020 (support) — positivity of the constant `κ` of Eq. (191) under the hypotheses of
  Theorem 22 (`theorem22_kappa_pos`).

The analytic statements themselves (c001, c004–c007, c017–c021, c028) are not
formalized: they need the PDE a-priori estimates of Lemmas 2/6–9/19–21, the Grönwall
matrix-exponential analysis of Theorem 22, and the first-exit-time argument of the
comparison principle Theorem 32.  Their statements are preserved in this branch's
history; this file retains the shared vocabulary (`laplacian`, `SolvesLaplace`,
`vorticityL2Norm`, `convVorticity`, `GradVorticitySupLe`, `IsEquilibrium`) and the
proved positivity support for c020.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FluidDynamics26.MainResults

open MeasureTheory Filter
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open scoped BigOperators Topology

/-! ## Laplace equation and its solution operator -/

/-- The Laplacian `Δφ = ∑ i, ∂_i ∂_i φ` on the torus `𝕋^d`. -/
def laplacian {d : ℕ} (φ : (Fin d → ℝ) → ℝ) (r : Fin d → ℝ) : ℝ :=
  ∑ i, deriv (fun s : ℝ => pderiv (fun r _ => φ r) i (Function.update r i s) 0) (r i)

/-- The Laplace equation `Δφ = f` of Eq. (17), p. 9, on `𝕋^d`. -/
def SolvesLaplace {d : ℕ} (φ f : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ⊤ φ ∧ ∀ r, laplacian φ r = f r

/-! ## The specific norms used by the error analysis -/

/-- `L²` norm of the vorticity, `‖ω_η‖_{L²}`, Eq. (186), p. 26. -/
def vorticityL2Norm (u : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  torusL2Norm (fun r _ => vorticityOf u r t) 0

/-- The convection term `v · ∇ω_v` appearing in Lemma 21, Eq. (187), p. 27. -/
def convVorticity (v : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (r : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  ∑ j, v r t j * pderiv (fun r t => vorticityOf v r t) j r t

/-- The sup-norm bound `‖∇ω_ũ‖_{L^∞} ≤ M` used in Lemma 21, Eq. (187), p. 27. -/
def GradVorticitySupLe (u : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (M : ℝ) : Prop :=
  ∀ r t i, |pderiv (fun r t => vorticityOf u r t) i r t| ≤ M

/-! ## c017 — Lemma 19, Eqs. (168)–(169), p. 26 -/

/-- The equilibrium condition of Eq. (167), p. 26: `(u₀·∇)u₀ = -∇p₀`. -/
def IsEquilibrium (u₀ : (Fin 2 → ℝ) → Fin 2 → ℝ) (p₀ : (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ r i, (∑ j, u₀ r j * sderiv u₀ i j r) = -pderiv (fun r _ => p₀ r) i r 0

/-! ## c020 — Theorem 22, Eqs. (190)–(192), p. 27 -/

/-- Positivity of the constant `κ` of Eq. (191), p. 27, under the hypotheses of
Theorem 22: `α, β, b₁, b₂ > 0` and `αβ > 2γ_u`. -/
theorem theorem22_kappa_pos {α β b₁ b₂ γu : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hb1 : 0 < b₁) (hb2 : 0 < b₂)
    (hcond : 2 * γu < α * β) :
    0 < (b₁ + α * b₂ / (2 * β)) / (α * β - 2 * γu) := by
  have hnum : 0 < b₁ + α * b₂ / (2 * β) := by
    have h1 : 0 < α * b₂ := mul_pos hα hb2
    have h2 : 0 < 2 * β := by linarith
    have h3 : 0 < α * b₂ / (2 * β) := div_pos h1 h2
    linarith
  exact div_pos hnum (by linarith)

end Qatlib.Papers.FluidDynamics26.MainResults
