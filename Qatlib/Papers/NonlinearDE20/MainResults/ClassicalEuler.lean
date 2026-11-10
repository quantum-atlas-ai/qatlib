/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonlinearDE20.MainResults.ClassicalEuler

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def eulerStep (f : E → E) (Δt : ℝ) (b : E) (x : E) : E :=
  x - Δt • f x + Δt • b

def eulerIterate (f : E → E) (b : ℕ → E) (Δt : ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => eulerStep f Δt (b (k + 1)) (eulerIterate f b Δt x₀ k)

@[simp] theorem eulerIterate_zero (f : E → E) (b : ℕ → E) (Δt : ℝ) (x₀ : E) :
    eulerIterate f b Δt x₀ 0 = x₀ := rfl

theorem eulerIterate_succ (f : E → E) (b : ℕ → E) (Δt : ℝ) (x₀ : E) (k : ℕ) :
    eulerIterate f b Δt x₀ (k + 1) =
      eulerIterate f b Δt x₀ k - Δt • f (eulerIterate f b Δt x₀ k) + Δt • b (k + 1) :=
  rfl

theorem eulerIterate_succ_unfold (f : E → E) (b : ℕ → E) (Δt : ℝ) (x₀ : E) (k : ℕ) :
    eulerIterate f b Δt x₀ (k + 1) =
      (fun x : E => x - Δt • f x) (eulerIterate f b Δt x₀ k) + Δt • b (k + 1) :=
  rfl

def linearStep (A : E →ₗ[ℝ] E) (Δt : ℝ) (b : E) (x : E) : E :=
  x - Δt • A x + Δt • b

theorem linearStep_eq_id_sub_smul (A : E →ₗ[ℝ] E) (Δt : ℝ) (b x : E) :
    linearStep A Δt b x = ((1 : E →ₗ[ℝ] E) - Δt • A) x + Δt • b := by
  simp [linearStep, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]

theorem eulerIterate_noDriving_eq_iterate (A : E →ₗ[ℝ] E) (Δt : ℝ) (x₀ : E) (k : ℕ) :
    eulerIterate (fun x => A x) (fun _ => 0) Δt x₀ k =
      ((fun x : E => x - Δt • A x)^[k]) x₀ := by
  induction k with
  | zero => simp [eulerIterate]
  | succ k ih =>
      rw [eulerIterate_succ, ih, Function.iterate_succ_apply']
      simp

end Qatlib.Papers.NonlinearDE20.MainResults.ClassicalEuler
