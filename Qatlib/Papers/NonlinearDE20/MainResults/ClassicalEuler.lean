/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# Forced classical Euler steps and iterates

The definitions `eulerStep` and `eulerIterate` describe forward Euler updates for a
real-module-valued field with time-dependent forcing. The module records their recurrences, the
linear step operator, and the unforced iterate formula underlying the discrete dynamics in
[LloydEtAl2020].

## Main statements

* `eulerIterate_succ`: The successor Euler iterate subtracts the scaled field and adds the
  scaled successor forcing vector.
* `linearStep_eq_id_sub_smul`: The linear Euler step is the operator `1 - Δt • A` applied to
  `x`, followed by addition of the scaled forcing.
* `eulerIterate_noDriving_eq_iterate`: With zero forcing and a linear field, the Euler
  trajectory is the function iterate of the unforced linear update.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonlinearDE20.MainResults.ClassicalEuler

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The forced Euler update `x - Δt • f x + Δt • b`. -/
def eulerStep (f : E → E) (Δt : ℝ) (b : E) (x : E) : E :=
  x - Δt • f x + Δt • b

/-- The Euler trajectory from `x₀`, using the forcing value `b (k + 1)` in the update from step
`k`. -/
def eulerIterate (f : E → E) (b : ℕ → E) (Δt : ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => eulerStep f Δt (b (k + 1)) (eulerIterate f b Δt x₀ k)

/-- The Euler trajectory at step zero is its initial state. -/
@[simp] theorem eulerIterate_zero (f : E → E) (b : ℕ → E) (Δt : ℝ) (x₀ : E) :
    eulerIterate f b Δt x₀ 0 = x₀ := rfl

/-- The successor Euler iterate subtracts the scaled field and adds the scaled successor forcing
vector. -/
theorem eulerIterate_succ (f : E → E) (b : ℕ → E) (Δt : ℝ) (x₀ : E) (k : ℕ) :
    eulerIterate f b Δt x₀ (k + 1) =
      eulerIterate f b Δt x₀ k - Δt • f (eulerIterate f b Δt x₀ k) + Δt • b (k + 1) :=
  rfl

/-- The successor Euler iterate is the unforced update applied to the current iterate plus the
scaled successor forcing vector. -/
theorem eulerIterate_succ_unfold (f : E → E) (b : ℕ → E) (Δt : ℝ) (x₀ : E) (k : ℕ) :
    eulerIterate f b Δt x₀ (k + 1) =
      (fun x : E => x - Δt • f x) (eulerIterate f b Δt x₀ k) + Δt • b (k + 1) :=
  rfl

/-- The forced Euler update for a real linear map `A`. -/
def linearStep (A : E →ₗ[ℝ] E) (Δt : ℝ) (b : E) (x : E) : E :=
  x - Δt • A x + Δt • b

/-- The linear Euler step is the operator `1 - Δt • A` applied to `x`, followed by addition of
the scaled forcing. -/
theorem linearStep_eq_id_sub_smul (A : E →ₗ[ℝ] E) (Δt : ℝ) (b x : E) :
    linearStep A Δt b x = ((1 : E →ₗ[ℝ] E) - Δt • A) x + Δt • b := by
  simp [linearStep, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]

/-- With zero forcing and a linear field, the Euler trajectory is the function iterate of the
unforced linear update. -/
theorem eulerIterate_noDriving_eq_iterate (A : E →ₗ[ℝ] E) (Δt : ℝ) (x₀ : E) (k : ℕ) :
    eulerIterate (fun x => A x) (fun _ => 0) Δt x₀ k =
      ((fun x : E => x - Δt • A x)^[k]) x₀ := by
  induction k with
  | zero => simp [eulerIterate]
  | succ k ih =>
      rw [eulerIterate_succ, ih, Function.iterate_succ_apply']
      simp

end Qatlib.Papers.NonlinearDE20.MainResults.ClassicalEuler
