/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # A genuine forward-Euler instability in the left half-plane

Demand: HighOrderODE10 Eq.(6), and the incorrect unrestricted A-stability
application in its Lemma 4 proof. This is an actual characteristic root at
mu=-3, not a theorem about an arbitrary free amplification proxy.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MultistepODE.MethodCert.Euler

/-- The actual forward-Euler amplification factor for the scalar test equation. -/
def root (mu : ℂ) : ℂ := 1 + mu

/-- The actual rho(z)-mu*sigma(z) characteristic polynomial of forward Euler. -/
def char (mu z : ℂ) : ℂ := z - 1 - mu

/-- The Euler amplification is a genuine root of its characteristic equation. -/
theorem rootEq (mu : ℂ) : char mu (root mu) = 0 := by simp [char, root]

/-- A negative-real test parameter has an actual characteristic root outside the unit disk. -/
theorem unstable : (-3 : ℂ).re ≤ 0 ∧ char (-3) (root (-3)) = 0 ∧ 1 < ‖root (-3)‖ := by
  refine ⟨by norm_num, rootEq _, ?_⟩
  norm_num [root]

/-- Forward Euler fails the necessary left-half-plane root condition for A-stability. -/
theorem notAStable : ¬∀ mu z : ℂ, mu.re ≤ 0 → char mu z = 0 → ‖z‖ ≤ 1 := by
  intro hs
  exact (not_le_of_gt unstable.2.2) (hs (-3) (root (-3)) unstable.1 unstable.2.1)

end Qatlib.Concepts.MultistepODE.MethodCert.Euler
