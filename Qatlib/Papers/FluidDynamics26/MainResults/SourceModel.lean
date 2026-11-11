/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity

set_option backward.isDefEq.respectTransparency false

/-!
# FluidDynamics26 — shared source model

Fixed source: Ameri–Carolan–Childs–Krovi, *Quantum lower bounds for simulating fluid
dynamics*, arXiv:2603.12161v1 (12 March 2026).  All theorem numbers, equation numbers and
page numbers below refer to that fixed version (arXiv v1; the metadata field
`arxiv_version_used` is empty, so v1 is the working assumption).

This file fixes the paper-layer vocabulary shared by the claim modules:

* `pureDistance` — the Euclidean distance between pure states, paper Eq. (21), p. 9;
* `SolvesKdV`, `VanishesAtInfinity`, `kdvL2NormSq` — the KdV model of Section 2.2, Eq. (26),
  p. 10;
* `SolvesEuler`, `SolvesLinearizedEuler`, `SolvesErrorPDE`, `vorticityOf`, and the torus
  norms — the Euler model of Section 2.3, Eqs. (36)–(38), pp. 11–12, and the error PDE of
  Lemma 19, Eq. (168), p. 26;
* `FinalStateAlgorithm`, `HistoryStateAlgorithm` — the source-model interface for the
  copy-complexity statements of Problems 1–3 (pp. 15–16) and Theorems 15/24/25/26.

Boundary of the model: scalar and vector fields are represented by functions on a
fundamental domain of the torus `[0, 2π]^d`; the paper's periodic boundary conditions are
recorded by the explicit periodicity hypotheses on the claims that need them.  The actual
quantum circuits for the encoding of Problems 1–3 are not modelled; a final-state (resp.
history-state) algorithm is represented by its copy count and its guaranteed error, which
is exactly the information used by the lower-bound proofs.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FluidDynamics26.MainResults

open MeasureTheory Filter
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Foundations.PureStateMath

open scoped BigOperators Topology

/-! ## Pure-state Euclidean distance (Eq. (21), p. 9) -/

/-- Paper Eq. (21), p. 9: `d(|ψ⟩,|φ⟩) = min_{|z|=1} ‖|ψ⟩ - z|φ⟩‖`, equivalently
`sqrt (2 - 2 |⟨ψ|φ⟩|)`.  This is the Euclidean distance used throughout Section 2.5. -/
def pureDistance {I : Type} [Fintype I] [DecidableEq I] (u v : QState I) : ℝ :=
  Real.sqrt (2 - 2 * ‖Inner u v‖)

/-- Trace distance `D(ρ,σ) = ‖ρ - σ‖₁ / 2` (Eq. (22), p. 10) for operators on an arbitrary
finite index set.  For `I = Fin n` this is definitionally the frozen
`QuantumAlgorithm.Foundations.MixedFidelity.FidelityMetric.traceDistance`, but it is also
needed for the tensor-power register `Fin k → Fin n` of Lemma 4, Eq. (24), p. 10. -/
def traceDistanceG {I : Type} [Fintype I] [DecidableEq I]
    (ρ σ : Matrix I I ℂ) : ℝ :=
  Matrix.traceNorm (ρ - σ) / 2

/-! ## KdV equation (Eq. (26), p. 10) -/

/-- First spatial derivative of a space-time scalar field. -/
def kdvDerivX (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x t => deriv (fun y => φ y t) x

/-- Third spatial derivative of a space-time scalar field. -/
def kdvThirdX (φ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  kdvDerivX (kdvDerivX (kdvDerivX φ))

/-- The KdV equation, Eq. (26), p. 10: `φ_t + φ_xxx - 6 φ φ_x = 0`, for a `C^∞` field. -/
def SolvesKdV (φ : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ (Function.uncurry φ) ∧
    ∀ x t, deriv (fun s => φ x s) t + kdvThirdX φ x t - 6 * φ x t * kdvDerivX φ x t = 0

/-- Vanishing at spatial infinity, the hypothesis of Lemma 6, p. 10. -/
def VanishesAtInfinity (φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ t, Tendsto (fun x => φ x t) atBot (𝓝 0) ∧
    Tendsto (fun x => φ x t) atTop (𝓝 0)

/-- Squared `L²` norm of a one-dimensional field over `ℝ`, Eq. (28), p. 10. -/
def kdvL2NormSq (φ : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, (φ x t) ^ 2

/-! ## Euler equations on the torus (Eqs. (36)–(38), pp. 11–12) -/

/-- Fundamental domain `[0, 2π]^d` of the torus `𝕋^d`. -/
def torusFund (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 (2 * Real.pi))

/-- Volume `(2π)^d` of the torus `𝕋^d`. -/
def torusVolume (d : ℕ) : ℝ := (2 * Real.pi) ^ d

/-- Coordinate partial derivative `∂_i f` of a space-time scalar field, where the
`i`-th spatial coordinate is moved. -/
def pderiv {d : ℕ} (f : (Fin d → ℝ) → ℝ → ℝ) (i : Fin d)
    (r : Fin d → ℝ) (t : ℝ) : ℝ :=
  deriv (fun s : ℝ => f (Function.update r i s) t) (r i)

/-- Coordinate partial derivative of a time-independent vector field. -/
def sderiv {d : ℕ} (f : (Fin d → ℝ) → Fin d → ℝ) (i j : Fin d)
    (r : Fin d → ℝ) : ℝ :=
  deriv (fun s : ℝ => f (Function.update r j s) i) (r j)

/-- The incompressible Euler equations, Eq. (36), p. 11, on `𝕋^d`: smooth velocity and
pressure, `∇·u = 0`, and `∂_t u + (u·∇)u = -∇P`. -/
def SolvesEuler (d : ℕ) (u : (Fin d → ℝ) → ℝ → Fin d → ℝ)
    (p : (Fin d → ℝ) → ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ (Function.uncurry u) ∧
    ContDiff ℝ ⊤ (Function.uncurry p) ∧
    (∀ r t, ∑ i, pderiv (fun r t => u r t i) i r t = 0) ∧
    (∀ r t i, deriv (fun s => u r s i) t =
      - (∑ j, u r t j * pderiv (fun r t => u r t i) j r t) - pderiv p i r t)

/-- Squared `L²` norm of a velocity field on `𝕋^d`. -/
def eulerL2NormSq {d : ℕ} (u : (Fin d → ℝ) → ℝ → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ r in torusFund d, ∑ i, (u r t i) ^ 2

/-- `L²` norm of a scalar field on `𝕋^d`. -/
def torusL2Norm {d : ℕ} (f : (Fin d → ℝ) → ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (∫ r in torusFund d, (f r t) ^ 2)

/-- `L⁴` norm of a scalar field on `𝕋^2`, Eq. (48), p. 12. -/
def torusL4Norm (f : (Fin 2 → ℝ) → ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.rpow (∫ r in torusFund 2, |f r t| ^ 4) (1 / 4)

/-- Pressure gauge, Eq. (38), p. 12: the average of `P` over the torus. -/
def pressureGauge {d : ℕ} (p : (Fin d → ℝ) → ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / torusVolume d) * ∫ r in torusFund d, p r t

/-- Vorticity of a two-dimensional velocity field, Eq. (15), p. 9:
`ω = ∂₁ u₂ - ∂₂ u₁`. -/
def vorticityOf (u : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (r : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  pderiv (fun r t => u r t 1) 0 r t - pderiv (fun r t => u r t 0) 1 r t

/-- Two-dimensional cross product of a vector with the scalar vorticity axis `k̂`:
`(a × (ω k̂))₀ = a₁ ω`, `(a × (ω k̂))₁ = -a₀ ω`. -/
def cross2 (a : Fin 2 → ℝ) (ω : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then a 1 * ω else -a 0 * ω

/-- Squared `L²` norm of a vector field on `𝕋²`. -/
def torusVecL2NormSq (u : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ r in torusFund 2, ∑ i, (u r t i) ^ 2

/-- `L²` norm of a vector field on `𝕋²`. -/
def torusVecL2Norm (u : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (torusVecL2NormSq u t)

/-! ## Linearized Euler equations (Eq. (132), p. 23) -/

/-- The linearized Euler equations, Eq. (132), p. 23, about the equilibrium `u₀`:
`∂_t ũ + (u₀·∇)ũ + (ũ·∇)u₀ = -∇P̃`, `∇·ũ = 0`. -/
def SolvesLinearizedEuler (d : ℕ) (u₀ : (Fin d → ℝ) → Fin d → ℝ)
    (u : (Fin d → ℝ) → ℝ → Fin d → ℝ) (P : (Fin d → ℝ) → ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ (Function.uncurry u) ∧
    ContDiff ℝ ⊤ (Function.uncurry P) ∧
    (∀ r t, ∑ i, pderiv (fun r t => u r t i) i r t = 0) ∧
    (∀ r t i, deriv (fun s => u r s i) t =
      - (∑ j, u₀ r j * pderiv (fun r t => u r t i) j r t)
        - (∑ j, u r t j * sderiv u₀ i j r) - pderiv P i r t)

/-- The error PDE of Lemma 19, Eq. (168), p. 26, for `η = u - ũ` and `η_p = P - P̃`. -/
def SolvesErrorPDE (uTilde : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (ε : ℝ)
    (v : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (η : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ)
    (ηp : (Fin 2 → ℝ) → ℝ → ℝ) : Prop :=
  (∀ r t, ∑ i, pderiv (fun r t => η r t i) i r t = 0) ∧
    ∀ r t i, deriv (fun s => η r s i) t =
      - pderiv (fun r t =>
          (∑ j, uTilde r t j * η r t j) + (1 / 2) * (∑ j, (η r t j) ^ 2) + ηp r t) i r t
        + cross2 (η r t) (vorticityOf uTilde r t) i
        + cross2 (uTilde r t) (vorticityOf η r t) i
        + cross2 (η r t) (vorticityOf η r t) i
        - ε ^ 2 * ∑ j, v r t j * pderiv (fun r t => v r t i) j r t

/-! ## Growth rates of Theorem 16 (Eqs. (126)–(129), p. 22) -/

/-- Cutoff wavenumber `k_cutoff = sqrt((sqrt 177 - 9)/6) * m`, Eq. (126), p. 22. -/
def kCutoff (m : ℝ) : ℝ := Real.sqrt ((Real.sqrt 177 - 9) / 6) * m

/-- Upper growth rate `γ_u`, Eq. (128), p. 22. -/
def gammaU (U₀ m k : ℝ) : ℝ :=
  U₀ * k * Real.sqrt ((1 / 2) * ((m ^ 2 - k ^ 2) / (m ^ 2 + k ^ 2)))

/-- Lower growth rate `γ_l`, Eq. (129), p. 22. -/
def gammaL (U₀ m k : ℝ) : ℝ :=
  U₀ * k * Real.sqrt ((1 / 2) *
    ((8 * m ^ 4 - 9 * m ^ 2 * k ^ 2 - 3 * k ^ 4) /
      ((m ^ 2 + k ^ 2) * (8 * m ^ 2 + 2 * k ^ 2))))

/-- The Fourier recurrence of Eq. (124), p. 22, written for complex coefficients. -/
def fourierRecurrence (U₀ γ : ℝ) (m k : ℤ) (c : ℤ → ℂ) : Prop :=
  ∀ j : ℤ,
    ((2 * γ ^ 2) / (k * U₀)) * ((j : ℂ) ^ 2 + (k : ℂ) ^ 2) * c j
      + ((k : ℂ) ^ 2 - (m : ℂ) ^ 2 + ((j : ℂ) - (m : ℂ)) ^ 2) * c (j - m)
      - ((k : ℂ) ^ 2 - (m : ℂ) ^ 2 + ((j : ℂ) + (m : ℂ)) ^ 2) * c (j + m) = 0

/-! ## Uniform separation bounds (Lemmas 20–21, pp. 27) -/

/-- `f` is bounded by `B` in sup norm on space-time. -/
def SupNormLe (f : (Fin 2 → ℝ) → ℝ → ℝ) (B : ℝ) : Prop := ∀ r t, |f r t| ≤ B

/-- `u` is bounded by `B` in sup norm on space-time. -/
def VecSupNormLe (u : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (B : ℝ) : Prop :=
  ∀ r t i, |u r t i| ≤ B

/-! ## Comparison principle (Theorem 32, Eq. (360), p. 49) -/

/-- The componentwise order `u ≤_c v` on `ℝ^n`, Definition 30, p. 49. -/
def VecLe {n : ℕ} (u v : Fin n → ℝ) : Prop := ∀ i, u i ≤ v i

/-- Quasimonotone nondecreasing vector field, Definition 31, p. 49. -/
def QuasimonotoneNondecreasing {n : ℕ} (f : ℝ → (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (u v : Fin n → ℝ) (t : ℝ), VecLe u v → ∀ i, f t u i ≤ f t v i

/-! ## Copy-complexity interface (Problems 1–3, pp. 15–16) -/

/-- Source-model interface for final-state preparation: `copies T` is the number of copies
of the initial encoding used, `error T` the accuracy guaranteed at time `T`.  The
contract of Problems 1–3 (pp. 15–16) is exactly that a claimed algorithm guarantees
`‖ψ'(T) - target(T)‖ ≤ error T` using `copies T` initial copies. -/
structure FinalStateAlgorithm where
  /-- number of copies of the initial state used at final time `T` -/
  copies : ℝ → ℕ
  /-- guaranteed error at final time `T` -/
  error : ℝ → ℝ

/-- Source-model interface for history-state preparation (Section 5, Eq. (242), p. 32). -/
structure HistoryStateAlgorithm where
  /-- number of copies of the initial state used -/
  copies : ℝ → ℕ
  /-- guaranteed error of the history state -/
  error : ℝ → ℝ

/-! ## Copy-complexity lower bounds (Problems 1–3, Theorems 15/24/25) -/

/-- `f` is a copy lower bound for final-state preparation to error `err`: every algorithm
whose error at time `T` is at most `err T` must use at least a constant multiple of `f T`
copies.  This is the quantifier structure of Theorem 15, Theorem 24 and Theorem 25. -/
def RequiresCopiesForError (f err : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (A : FinalStateAlgorithm) (T : ℝ), 1 ≤ T → A.error T ≤ err T →
    c * f T ≤ (A.copies T : ℝ)

/-- `f` is a copy lower bound for history-state preparation to error `err`. -/
def HistoryRequiresCopiesForError (f err : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (A : HistoryStateAlgorithm) (T : ℝ), 1 ≤ T → A.error T ≤ err T →
    c * f T ≤ (A.copies T : ℝ)

/-- Copy lower bound without an accuracy promise (Corollary 18, p. 25). -/
def RequiresCopies (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (A : FinalStateAlgorithm) (T : ℝ), 1 ≤ T →
    c * f T ≤ (A.copies T : ℝ)

/-- The post-selection step of Theorem 26, p. 32: `O(T)` copies of a history state suffice
to prepare the final-time state, i.e. every history-state algorithm induces a final-state
algorithm with the same guaranteed error using at most `C * T` times as many copies. -/
def HistoryPostselection (C : ℝ) : Prop :=
  ∀ H : HistoryStateAlgorithm, ∃ A : FinalStateAlgorithm,
    (∀ T : ℝ, A.error T = H.error T) ∧
      (∀ T : ℝ, 1 ≤ T → (A.copies T : ℝ) ≤ C * T * (H.copies T : ℝ))

end Qatlib.Papers.FluidDynamics26.MainResults
