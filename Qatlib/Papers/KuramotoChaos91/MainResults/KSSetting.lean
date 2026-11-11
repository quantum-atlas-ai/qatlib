/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
WARNING: this is provisional vocabulary, not an established representation of
the source dynamics. Finite sine support, eventual exact periodicity and
aperiodicity below have no proved equivalence to the paper's modal attractors,
periodic limit cycles or chaos. No core Claim coverage is asserted.

# Kuramoto–Sivashinsky setting for Papageorgiou–Smyrlis (1991)

Source: D. T. Papageorgiou and Y. S. Smyrlis, *The route to chaos for the
Kuramoto–Sivashinsky equation*, Theoretical and Computational Fluid Dynamics
**3** (1991), pp. 15–42, DOI `10.1007/BF00271514`.  Fixed version: the
publisher version of record (`arxiv_version_used = null` in
`metadata/papers/KuramotoChaos91.json`).

This module fixes the objects that the two active claims of the paper talk
about, so that the paper-layer statements can be written without inventing
per-claim notation:

* the spatially periodic Kuramoto–Sivashinsky initial-value problem with the
  paper's fixed initial condition `u₀(x) = -sin x`;
* the notions of a *viscosity window* and of a *regime* (steady fully modal,
  steady bimodal / trimodal / tetramodal, time periodic, period-doubling
  cascade, chaotic) that occur in the abstract of the paper;
* the order-theoretic structure of the route-to-chaos window sequence.

The definitions are deliberately conservative.  The paper is a numerical
study: it reports attractors of an infinite-dimensional dynamical system and
does not state these notions as formal predicates.  Where a definition is an
interpretation of the paper's wording, the docstring says so.  In particular
`FullyModalSteady` reads "fully modal" as "every mode of the resolved band
`{1, …, N}` carries a nonzero sine coefficient", and `ChaoticAttractor` uses
the operational (non-steady, non-eventually-periodic) sense that matches the
numerical diagnostics of the paper; neither definition is claimed to be the
unique formalisation of the source phrase.

The Kuramoto–Sivashinsky equation is normalised here as

`u_t + u u_x + u_xx + ν u_xxxx = 0`,

with `x` on the `2π`-periodic circle.  The paper quotes its viscosity windows
in its own (equivalently scaled) normalisation; the numeric constants of the
claims are transported verbatim in the claim modules, and no
normalisation-invariance is asserted here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.KuramotoChaos91.MainResults.KSSetting

noncomputable section

open Filter Topology
open scoped BigOperators

/-! ## The Kuramoto–Sivashinsky initial-value problem -/

/-- The `n`-fold iterated derivative of a real function.  Used to write the
spatial derivatives `u_x, u_xx, u_xxxx` of the Kuramoto–Sivashinsky equation
uniformly. -/
def iterDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (iterDeriv n f)

/-- The **(spatially periodic) Kuramoto–Sivashinsky initial-value problem with
viscosity `ν`**: `u : ℝ → ℝ → ℝ` is the solution `(t, x) ↦ u t x`, it starts
from the paper's fixed initial condition `u(0, x) = -sin x`, it is `2π`-periodic
in space for every time, and it satisfies

`u_t + u u_x + u_xx + ν u_xxxx = 0` for `t > 0`.

Source: Papageorgiou–Smyrlis 1991, §1 (p. 15) and the abstract, which fixes
"the initial condition … the same for all numerical experiments (a single sine
wave is used)". -/
def KSEquation (ν : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ x, u 0 x = -Real.sin x) ∧
  (∀ t, Function.Periodic (u t) (2 * Real.pi)) ∧
  ∀ t, 0 < t → ∀ x,
    deriv (fun s => u s x) t
      + u t x * iterDeriv 1 (u t) x
      + iterDeriv 2 (u t) x
      + ν * iterDeriv 4 (u t) x = 0

/-- A solution record for the Kuramoto–Sivashinsky initial-value problem with
positive viscosity.  Source: Papageorgiou–Smyrlis 1991, §1, p. 15 (the
dissipation parameter `ν` is positive throughout the paper). -/
structure KSSolution (ν : ℝ) where
  /-- The space-time solution `(t, x) ↦ u t x`. -/
  u : ℝ → ℝ → ℝ
  /-- The viscosity is positive. -/
  hν : 0 < ν
  /-- The fixed initial condition `u₀(x) = -sin x`. -/
  initial : ∀ x, u 0 x = -Real.sin x
  /-- Spatial `2π`-periodicity. -/
  periodic : ∀ t, Function.Periodic (u t) (2 * Real.pi)
  /-- The Kuramoto–Sivashinsky equation. -/
  equation : ∀ t, 0 < t → ∀ x,
    deriv (fun s => u s x) t
      + u t x * iterDeriv 1 (u t) x
      + iterDeriv 2 (u t) x
      + ν * iterDeriv 4 (u t) x = 0

/-- **Bridge lemma**: every `KSSolution` satisfies the bundled predicate
`KSEquation` of the same viscosity.  This is a definitional unfolding of the
solution record, used to state the paper's claims over `KSEquation`.
Source: Papageorgiou–Smyrlis 1991, §1, p. 15 (definition of the IVP). -/
theorem KSSolution.solves {ν : ℝ} (S : KSSolution ν) : KSEquation ν S.u :=
  ⟨S.initial, S.periodic, S.equation⟩

/-- The **experiment family** of the paper: one Kuramoto–Sivashinsky solution
for each viscosity `ν > 0`, all started from the same initial condition
`u₀(x) = -sin x`.  Source: Papageorgiou–Smyrlis 1991, abstract (p. 15):
"the initial condition is taken to be the same for all numerical experiments
(a single sine wave is used)". -/
structure KSExperiment where
  /-- The viscosity-indexed family of solutions `(ν, t, x) ↦ u ν t x`. -/
  u : ℝ → ℝ → ℝ → ℝ
  /-- Every member solves the Kuramoto–Sivashinsky IVP. -/
  solves : ∀ ν, 0 < ν → KSEquation ν (u ν)

/-! ## Long-time behaviour and attractor regimes -/

/-- **Steady limit**: the solution converges pointwise, as `t → ∞`, to the
steady profile `v`.  Source: Papageorgiou–Smyrlis 1991, abstract (p. 15),
which classifies the "large time evolution of the system" by the type of
attractor that is approached. -/
def SteadyLimit (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ x, Tendsto (fun t => u t x) atTop (𝓝 (v x))

/-- **Sine modal support**: the `2π`-periodic function `v` is a real sine
polynomial whose nonzero modes are exactly the finite set `S`; every mode in
`S` is positive and carries a nonzero coefficient.  The initial condition
`-sin x` is odd and the Kuramoto–Sivashinsky equation preserves oddness, so
the steady states reached in the paper's experiments have sine modes only.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15), where steady attractors
are named by their number of modes. -/
def HasSineSupport (v : ℝ → ℝ) (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, 1 ≤ n) ∧
  ∃ b : ℕ → ℝ,
    (∀ n ∈ S, b n ≠ 0) ∧
    (∀ n, n ∉ S → b n = 0) ∧
    ∀ x, v x = S.sum (fun n => b n * Real.sin (n * x))

/-- **A steady `k`-modal attractor**: the large-time limit is a steady state
with exactly `k` active sine modes.  For `k = 2, 3, 4` this is the paper's
bimodal, trimodal and tetramodal attractor.  Source: Papageorgiou–Smyrlis
1991, abstract (p. 15). -/
def ModalSteady (u : ℝ → ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ (v : ℝ → ℝ) (S : Finset ℕ), HasSineSupport v S ∧ S.card = k ∧ SteadyLimit u v

/-- **A steady fully modal attractor**: the large-time limit is a steady state
whose active sine modes are *all* the modes of a resolved band `{1, …, N}`
with `N ≥ 4`.  This is the reading of "steady fully modal attractor" used in
this development: full modal content within the resolved Galerkin band, as
opposed to the `k`-modal attractors with a fixed small `k`.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
def FullyModalSteady (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ N : ℕ, 4 ≤ N ∧
    ∃ v : ℝ → ℝ, HasSineSupport v (Finset.Icc 1 N) ∧ SteadyLimit u v

/-- **Eventually periodic**: for every spatial point `x`, the trajectory
`t ↦ u t x` is periodic with period `T > 0` after some time `t₀`.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15) ("a periodic (in time)
attractor"). -/
def EventuallyPeriodic (u : ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ ∀ x : ℝ, ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → u (t + T) x = u t x

/-- **A time-periodic attractor**: the large-time solution is eventually
periodic with some positive period and is not steady.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
def TimePeriodicAttractor (u : ℝ → ℝ → ℝ) : Prop :=
  (∃ T : ℝ, EventuallyPeriodic u T) ∧ ¬∃ v : ℝ → ℝ, SteadyLimit u v

/-- **A provisional aperiodic regime**, without a proved source bridge: the large-time solution is neither steady nor eventually
periodic (aperiodic).  The paper detects chaos numerically (non-decaying
aperiodic dynamics and period-doubling accumulation); positive Lyapunov
exponents and strange attractors are not formalised here.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15) ("to chaos"). -/
def ChaoticAttractor (u : ℝ → ℝ → ℝ) : Prop :=
  (¬∃ v : ℝ → ℝ, SteadyLimit u v) ∧
  ¬∃ T : ℝ, EventuallyPeriodic u T

/-- **A viscosity window**: a nonempty open interval `(lo, hi)` of positive
dissipation parameters.  Source: Papageorgiou–Smyrlis 1991, abstract
(p. 15): "windows, in parameter space, in which the solution has the following
characteristics as the viscosity is decreased". -/
structure ViscosityWindow where
  /-- Lower endpoint of the open window. -/
  lo : ℝ
  /-- Upper endpoint of the open window. -/
  hi : ℝ
  /-- The lower endpoint is positive. -/
  lo_pos : 0 < lo
  /-- The window is nonempty. -/
  lo_lt_hi : lo < hi

/-- Membership in an open viscosity window: `lo < ν < hi`.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
def ViscosityWindow.Contains (W : ViscosityWindow) (ν : ℝ) : Prop :=
  W.lo < ν ∧ ν < W.hi

/-- Inclusion of viscosity windows.  Source: Papageorgiou–Smyrlis 1991,
abstract (p. 15) (the subwindows of a cascade lie inside the cascade window). -/
def ViscosityWindow.Subset (W W' : ViscosityWindow) : Prop :=
  ∀ ν : ℝ, W.Contains ν → W'.Contains ν

/-! ## The regime vocabulary and the route-to-chaos ordering -/

/-- The attractor regimes named in the paper's route to chaos.
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
inductive AttractorRegime
  | fullyModalSteady
  | bimodalSteady
  | trimodalSteady
  | tetramodalSteady
  | timePeriodic
  | periodDoublingCascade
  | chaotic
  deriving DecidableEq, Repr

/-- **A period-doubling cascade on a viscosity window**: there is a depth
`n ≥ 4`, a period sequence `T` with `T (k+1) = 2 * T k`, and an ordered family
of subwindows inside `W` on which the solution is eventually periodic with
period `T k`; the periods double across subwindows in the direction of
decreasing viscosity.  Source: Papageorgiou–Smyrlis 1991, abstract (p. 15),
"another time-periodic attractor having a full sequence of period-doublings
(in the parameter space) to chaos". -/
def HasPeriodDoublingCascade (E : KSExperiment) (W : ViscosityWindow) : Prop :=
  ∃ (n : ℕ) (T : ℕ → ℝ) (sub : ℕ → ViscosityWindow),
    4 ≤ n ∧
    0 < T 0 ∧
    (∀ k : ℕ, T (k + 1) = 2 * T k) ∧
    (∀ k : ℕ, k < n → ViscosityWindow.Subset (sub k) W) ∧
    (∀ i j : ℕ, i < j → j < n → (sub j).hi ≤ (sub i).lo) ∧
    (∀ k : ℕ, k < n → ∀ ν : ℝ, (sub k).Contains ν → EventuallyPeriodic (E.u ν) (T k))

/-- **A regime holds on a viscosity window**: every viscosity in the window,
or (for the cascade regime) the whole window, exhibits the stated asymptotic
behaviour.  Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
def RegimeHoldsOn (E : KSExperiment) (W : ViscosityWindow) : AttractorRegime → Prop
  | .fullyModalSteady => ∀ ν : ℝ, W.Contains ν → FullyModalSteady (E.u ν)
  | .bimodalSteady => ∀ ν : ℝ, W.Contains ν → ModalSteady (E.u ν) 2
  | .trimodalSteady => ∀ ν : ℝ, W.Contains ν → ModalSteady (E.u ν) 3
  | .tetramodalSteady => ∀ ν : ℝ, W.Contains ν → ModalSteady (E.u ν) 4
  | .timePeriodic => ∀ ν : ℝ, W.Contains ν → TimePeriodicAttractor (E.u ν)
  | .periodDoublingCascade => HasPeriodDoublingCascade E W
  | .chaotic => ∀ ν : ℝ, W.Contains ν → ChaoticAttractor (E.u ν)

/-- **The windows descend with the viscosity**: for `i < j`, the whole window
`w j` lies at or below the lower endpoint of `w i`.  This is the ordering in
which the paper lists the route as "the viscosity is decreased".
Source: Papageorgiou–Smyrlis 1991, abstract (p. 15). -/
def WindowsDescend {n : ℕ} (w : Fin n → ViscosityWindow) : Prop :=
  ∀ i j : Fin n, i < j → (w j).hi ≤ (w i).lo

/-! ## Order-theoretic consequences of the window sequence -/

/-- **The upper endpoints strictly decrease along the route.**  If the windows
descend, then the upper endpoint of a later window is strictly below the upper
endpoint of an earlier one.  Source: Papageorgiou–Smyrlis 1991, abstract
(p. 15); formal consequence of `WindowsDescend` and the nonemptiness of a
window. -/
theorem windowsDescend_hi_strict {n : ℕ} {w : Fin n → ViscosityWindow}
    (h : WindowsDescend w) {i j : Fin n} (hij : i < j) :
    (w j).hi < (w i).hi :=
  lt_of_le_of_lt (h i j hij) (w i).lo_lt_hi

/-- **The lower endpoints strictly decrease along the route.**  Source:
Papageorgiou–Smyrlis 1991, abstract (p. 15); formal consequence of
`WindowsDescend` and the nonemptiness of a window. -/
theorem windowsDescend_lo_strict {n : ℕ} {w : Fin n → ViscosityWindow}
    (h : WindowsDescend w) {i j : Fin n} (hij : i < j) :
    (w j).lo < (w i).lo :=
  lt_of_lt_of_le (w j).lo_lt_hi (h i j hij)

/-- **Distinct windows in the route are disjoint.**  For `i < j`, no viscosity
lies in both `w i` and `w j`.  Source: Papageorgiou–Smyrlis 1991, abstract
(p. 15); formal consequence of the ordering and of the windows being open.
-/
theorem windowsDescend_disjoint {n : ℕ} {w : Fin n → ViscosityWindow}
    (h : WindowsDescend w) {i j : Fin n} (hij : i < j) :
    ∀ ν : ℝ, ¬((w i).Contains ν ∧ (w j).Contains ν) := by
  intro ν hc
  have hle : (w j).hi ≤ (w i).lo := h i j hij
  exact absurd (lt_of_lt_of_le hc.2.2 hle) (not_lt.mpr (le_of_lt hc.1.1))

end

end Qatlib.Papers.KuramotoChaos91.MainResults.KSSetting
