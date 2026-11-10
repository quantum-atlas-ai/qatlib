/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.TensorHyper20.MainResults.Definitions
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.LambdaTHC

open scoped BigOperators

noncomputable def lambdaZeta {M : ℕ} (ζ : Fin M → Fin M → ℝ) : ℝ :=
  (1 / 2) * ∑ μ, ∑ ν, |ζ μ ν|

noncomputable def lambdaTHC {K M : ℕ} (t : Fin K → ℝ) (ζ : Fin M → Fin M → ℝ) : ℝ :=
  ∑ ℓ, |t ℓ| + lambdaZeta ζ

theorem lambdaTHC_eq {K M : ℕ} (t : Fin K → ℝ) (ζ : Fin M → Fin M → ℝ) :
    lambdaTHC t ζ = ∑ ℓ, |t ℓ| + (1 / 2) * ∑ μ, ∑ ν, |ζ μ ν| := rfl

theorem lambdaZeta_nonneg {M : ℕ} (ζ : Fin M → Fin M → ℝ) : 0 ≤ lambdaZeta ζ := by
  unfold lambdaZeta
  positivity

theorem lambdaTHC_le_two_lambdaZeta {K M : ℕ} (t : Fin K → ℝ)
    (ζ : Fin M → Fin M → ℝ) (h : ∑ ℓ, |t ℓ| ≤ lambdaZeta ζ) :
    lambdaTHC t ζ ≤ 2 * lambdaZeta ζ := by
  unfold lambdaTHC
  linarith

theorem lambdaTHC_asymptotic {K M : ℕ} (t : Fin K → ℝ) (ζ : Fin M → Fin M → ℝ)
    (c : ℝ) (h : ∑ ℓ, |t ℓ| ≤ c * lambdaZeta ζ) :
    lambdaTHC t ζ ≤ (c + 1) * lambdaZeta ζ := by
  unfold lambdaTHC
  have hz := lambdaZeta_nonneg ζ
  linarith

end Qatlib.Papers.TensorHyper20.MainResults.LambdaTHC
