/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Shows that a constant function has zero variance under a normalized cube weight. -/
theorem cube_variance_const {n : ℕ} {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w) (c : ℝ) :
    cubeVar n w (fun _ => c)=0 := by
  have he : cubeExpect n w (fun _ => c)=c := by
    unfold cubeExpect
    rw [← Finset.sum_mul,hw.2,one_mul]
  unfold cubeVar
  rw [he]
  simp [cubeExpect]

/-- Shows that every function on the zero-dimensional cube has zero variance. -/
theorem cube_zero_dimension_variance {w : (Fin 0 → Bool) → ℝ} (hw : CubeWeight 0 w)
    (f : (Fin 0 → Bool) → ℝ) : cubeVar 0 w f=0 := by
  let x : Fin 0 → Bool := fun i => Fin.elim0 i
  have hf : f=(fun _ => f x) := by ext y; exact congrArg f (Subsingleton.elim y x)
  rw [hf]
  exact cube_variance_const hw _

/-- Shows that a cube function of degree zero is constant. -/
theorem cube_degree_zero_constant {n : ℕ} {f : (Fin n → Bool) → ℝ} (hd : CubeDegreeLE 0 f) :
    ∃ c : ℝ, ∀ x, f x=c := by
  obtain ⟨c,hc,hf⟩ := hd
  refine ⟨c ∅,fun x => ?_⟩
  rw [hf x]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro S _ hS
    rw [hc S (Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hS)),zero_mul]
  · simp

/-- Shows that a cube function of degree zero has zero variance under a normalized cube weight. -/
theorem cube_degree_zero_variance {n : ℕ} {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    {f : (Fin n → Bool) → ℝ} (hd : CubeDegreeLE 0 f) : cubeVar n w f=0 := by
  obtain ⟨c,hc⟩ := cube_degree_zero_constant hd
  have hf : f=(fun _ => c) := funext hc
  rw [hf]
  exact cube_variance_const hw c

end Qatlib.Concepts.ProbabilityCore.DistributionAA
