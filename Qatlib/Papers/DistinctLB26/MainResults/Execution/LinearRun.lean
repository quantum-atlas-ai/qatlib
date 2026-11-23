/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.DistinctLB26.MainResults.Execution.UniformInput

@[expose] public section

/-!
# Linearity of actual query execution

This identifies the executed zero-label Fourier state with the coherent
superposition of the same algorithm run on every actual computational input.
Both output and query count come from the executed instruction list.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Execution

variable {n q : ℕ} [NeZero q] {W : Type*} [Fintype W]

/-- The actual controlled Fourier query as a complex linear map. -/
def queryLinear : Joint n q W →ₗ[ℂ] Joint n q W where
  toFun := query
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A real work-register gate extended to all input slices as a linear map. -/
def localLinear (U : Local n q W ≃ₗᵢ[ℂ] Local n q W) :
    Joint n q W →ₗ[ℂ] Joint n q W where
  toFun := localGate U
  map_add' ψ φ := by
    ext z
    change U (fiber (ψ + φ) z.1) z.2 = U (fiber ψ z.1) z.2 + U (fiber φ z.1) z.2
    rw [show fiber (ψ + φ) z.1 = fiber ψ z.1 + fiber φ z.1 from rfl, map_add]
    rfl
  map_smul' c ψ := by
    ext z
    change U (fiber (c • ψ) z.1) z.2 = c * U (fiber ψ z.1) z.2
    rw [show fiber (c • ψ) z.1 = c • fiber ψ z.1 from rfl, U.map_smul]
    rfl

/-- Compose precisely the instructions that define the actual execution. -/
def executeLinear : List (Instr n q W) → Joint n q W →ₗ[ℂ] Joint n q W
  | [] => LinearMap.id
  | .gate U :: rest => (executeLinear rest).comp (localLinear U)
  | .oracle :: rest => (executeLinear rest).comp queryLinear

/-- The recursively compiled linear map agrees with the original execution. -/
theorem executeLinear_apply (prog : List (Instr n q W)) (ψ : Joint n q W) :
    executeLinear prog ψ = execute prog ψ := by
  induction prog generalizing ψ with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | gate U => exact ih (localGate U ψ)
    | oracle => exact ih (query ψ)

/-- The actual algorithm maps the uniform input to the superposition of its physical executions. -/
theorem execute_uniform (prog : List (Instr n q W)) (φ : Local n q W) :
    execute prog (zeroInput φ) =
      ((Real.sqrt (Fintype.card (Label n q)) : ℂ)⁻¹) •
        ∑ x : Label n q, plane x (inputRun x prog φ) := by
  rw [← executeLinear_apply, ← uniform_plane, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [executeLinear_apply, execute_plane]

variable [DecidableEq W]

/-- A computational work basis vector at the zero input label is the actual prepared state. -/
theorem zeroInput_basis (a₀ : Work n q W) :
    zeroInput (EuclideanSpace.basisFun (Work n q W) ℂ a₀) = initial a₀ := by
  classical
  ext z
  by_cases hσ : z.1 = 0
  · by_cases ha : z.2 = a₀
    · have hz : z = (0, a₀) := Prod.ext hσ ha
      simp [zeroInput, initial, hz, EuclideanSpace.basisFun_apply]
    · have hz : z ≠ (0, a₀) := fun h => ha (congrArg Prod.snd h)
      simp [zeroInput, initial, hσ, hz, EuclideanSpace.basisFun_apply, ha]
  · have hz : z ≠ (0, a₀) := fun h => hσ (congrArg Prod.fst h)
    simp [zeroInput, initial, hσ, hz]

/-- The Fourier degree bound applies to the coherent state of genuine physical input runs. -/
theorem physical_degree (prog : List (Instr n q W)) (a₀ : Work n q W) :
    Supported (queryCount prog)
      (((Real.sqrt (Fintype.card (Label n q)) : ℂ)⁻¹) •
        ∑ x : Label n q,
          plane x (inputRun x prog (EuclideanSpace.basisFun (Work n q W) ℂ a₀))) := by
  rw [← execute_uniform, zeroInput_basis]
  exact (uniform_degree prog a₀).1

end Qatlib.Papers.DistinctLB26.MainResults.Execution
