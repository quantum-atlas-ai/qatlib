/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinDynamics23.Kernel.ActualUnitaryTruncation

@[expose] public section

/-!
# Pathwise LCHS kernel truncation

Lemma 30 of arXiv:2603.12398v1 applies the same deterministic kernel
tail bound to every realized path. The propagation interval is
independent of the kernel cutoff.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.LinDynamics23.Kernel
open Qatlib.Concepts.LchsSimulation.Kernel
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Papers.NonlinearSDE26.StochSimulation

variable {Ω I : Type} [Fintype I] [DecidableEq I]

/-- The kernel truncation error of the actual time-ordered propagator
between source times zero and `T`, at frequency cutoff `K`. -/
def lchsKernelError (L H : ℝ → Matrix I I ℂ) (T β K : ℝ) : ℝ :=
  ‖(∫ k : ℝ, highKernelG β k • lchsPropagator L H 0 T k) -
    (∫ k in -K..K, highKernelG β k • lchsPropagator L H 0 T k)‖

/-- Unitarity of the kernel propagator needs Hermitian generators on the
real frequency axis. -/
private theorem kernelPropagator_unitary (L H : ℝ → Matrix I I ℂ)
    (hL : Continuous L) (hH : Continuous H)
    (hLh : ∀ u, (L u).IsHermitian) (hHh : ∀ u, (H u).IsHermitian) (T k : ℝ) :
    lchsPropagator L H 0 T k ∈ Matrix.unitaryGroup I ℂ :=
  ordered_evolution_hermitian_unitary I (fun t => H t + k • L t)
    (hH.add (hL.const_smul k))
    (fun t => (hHh t).add ((hLh t).smul (R := ℝ) (IsSelfAdjoint.all k))) 0 T

/-- Lemma 30(1), Eq. (160), as an everywhere pathwise bound with the source
tail constant. The paths have continuous Hermitian generators. -/
theorem pathwise_lchs_truncation (L H : Ω → ℝ → Matrix I I ℂ) (T β K : ℝ)
    (hβ : 0 < β) (hβ1 : β < 1) (hK : 1 ≤ K)
    (hcont : ∀ ω, Continuous (L ω) ∧ Continuous (H ω))
    (hherm : ∀ ω t, (L ω t).IsHermitian ∧ (H ω t).IsHermitian) :
    ∀ ω, lchsKernelError (L ω) (H ω) T β K ≤
      (highKernelTailC β / K) * Real.exp (-(K ^ β) * Real.cos (β * Real.pi / 2) / 2) := by
  intro ω
  exact (near_exponential_kernel_actual_unitary_tail I β K (lchsPropagator (L ω) (H ω) 0 T)
    hβ hβ1 hK (lchsPropagator_continuous _ _ (hcont ω).1 (hcont ω).2 0 T)
    (kernelPropagator_unitary _ _ (hcont ω).1 (hcont ω).2
      (fun t => (hherm ω t).1) (fun t => (hherm ω t).2) T)).2

/-- Lemma 30(2): the explicit cutoff is the same for all realizations
and attains the requested absolute precision. -/
theorem pathwise_lchs_precision_window (L H : Ω → ℝ → Matrix I I ℂ) (T β ε : ℝ)
    (hβ : 0 < β) (hβ1 : β < 1) (hε : 0 < ε)
    (hcont : ∀ ω, Continuous (L ω) ∧ Continuous (H ω))
    (hherm : ∀ ω t, (L ω t).IsHermitian ∧ (H ω t).IsHermitian) :
    let K : ℝ := highKernelCutoff β ε
    1 ≤ K ∧ ∀ ω, lchsKernelError (L ω) (H ω) T β K ≤ ε := by
  have hK : (1 : ℝ) ≤ (highKernelCutoff β ε : ℝ) := by
    exact_mod_cast highKernelCutoff_one_le β ε
  exact ⟨hK, fun ω =>
    (pathwise_lchs_truncation L H T β _ hβ hβ1 hK hcont hherm ω).trans
      (highKernelCutoff_tail_le β ε hβ hβ1 hε)⟩

end Qatlib.Papers.NonlinearSDE26.StochSimulation
