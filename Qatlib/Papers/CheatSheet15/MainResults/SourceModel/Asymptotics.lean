/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# `Õ`, `Ω̃`, `Θ̃` notation for arXiv:1511.01937

The paper states all of its separations up to polylogarithmic factors.  Two
renderings are used in this development:

* `BigOTilde a b` for sequences `a b : ℕ → ℝ`: eventual domination
  `a n ≤ C · b n · (log (n + 2))^k` for some constants `C > 0`, `k ∈ ℕ`.
  `OmegaTilde` and `ThetaTilde` are the dual and the two-sided version.
* `OLog N a b` for a single instance: `a ≤ C · b · (log (N + 2))^k`, with
  `OmegaLog` and `ThetaLog` dual and two-sided.

The shift `n + 2` keeps the logarithm positive for `n = 0, 1`, so the definitions
make sense at every index with no side conditions.
-/

set_option autoImplicit false

open Filter

namespace Qatlib.Papers.CheatSheet15.MainResults.SourceModel

/-- `a = Õ(b)` for sequences: `a` is at most `b` times a polylogarithm in the
input length, eventually. -/
def BigOTilde (a b : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ᶠ n in atTop, a n ≤ C * b n * (Real.log ((n : ℝ) + 2)) ^ k

/-- `a = Ω̃(b)` for sequences. -/
def OmegaTilde (a b : ℕ → ℝ) : Prop := BigOTilde b a

/-- `a = Θ̃(b)` for sequences. -/
def ThetaTilde (a b : ℕ → ℝ) : Prop := BigOTilde a b ∧ BigOTilde b a

/-- `a = Õ(b)` at a single input size `N`. -/
def OLog (N : ℕ) (a b : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 < C ∧ a ≤ C * b * (Real.log ((N : ℝ) + 2)) ^ k

/-- `a = Ω̃(b)` at a single input size `N`. -/
def OmegaLog (N : ℕ) (a b : ℝ) : Prop := OLog N b a

/-- `a = Θ̃(b)` at a single input size `N`. -/
def ThetaLog (N : ℕ) (a b : ℝ) : Prop := OLog N a b ∧ OLog N b a

/-- The `bigOTilde_refl` result for the CheatSheet15 paper model. -/
theorem bigOTilde_refl (a : ℕ → ℝ) : BigOTilde a a := by
  refine ⟨1, 0, by norm_num, ?_⟩
  filter_upwards with n
  simp

/-- The `omegaTilde_refl` result for the CheatSheet15 paper model. -/
theorem omegaTilde_refl (a : ℕ → ℝ) : OmegaTilde a a := bigOTilde_refl a

/-- The `thetaTilde_refl` result for the CheatSheet15 paper model. -/
theorem thetaTilde_refl (a : ℕ → ℝ) : ThetaTilde a a :=
  ⟨bigOTilde_refl a, bigOTilde_refl a⟩

/-- The `oLog_refl` result for the CheatSheet15 paper model. -/
theorem oLog_refl (N : ℕ) (a : ℝ) : OLog N a a := by
  refine ⟨1, 0, by norm_num, ?_⟩
  simp

/-- The `omegaLog_refl` result for the CheatSheet15 paper model. -/
theorem omegaLog_refl (N : ℕ) (a : ℝ) : OmegaLog N a a := oLog_refl N a

/-- The `thetaLog_refl` result for the CheatSheet15 paper model. -/
theorem thetaLog_refl (N : ℕ) (a : ℝ) : ThetaLog N a a :=
  ⟨oLog_refl N a, oLog_refl N a⟩

/-- `Θ̃` in the sequence sense gives `Õ` in both directions. -/
theorem ThetaTilde.left {a b : ℕ → ℝ} (h : ThetaTilde a b) : BigOTilde a b := h.1

/-- `Θ̃` in the sequence sense gives `Ω̃` in the reverse direction. -/
theorem ThetaTilde.right {a b : ℕ → ℝ} (h : ThetaTilde a b) : OmegaTilde a b := h.2

/-- `Θ̃` at a single size gives `Õ` in both directions. -/
theorem ThetaLog.left {N : ℕ} {a b : ℝ} (h : ThetaLog N a b) : OLog N a b := h.1

/-- `Θ̃` at a single size gives `Ω̃` in the reverse direction. -/
theorem ThetaLog.right {N : ℕ} {a b : ℝ} (h : ThetaLog N a b) : OmegaLog N a b := h.2

end Qatlib.Papers.CheatSheet15.MainResults.SourceModel
