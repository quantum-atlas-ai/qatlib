/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolutionDefs

/-!
# Refined copy-evolution endpoints

This module augments copy-evolution endpoint specifications with injectivity of the backend
encoding, the exact phase-estimation basis size, and a loading-description cost bound. It also
exposes the off-grid instrument and repeated-copy sampling guarantees as separate statements.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `walkGoal_endpoint`: the loading endpoint with refined resource guarantees.
* `clause16_endpoint`: the self-tomography endpoint with explicit branch and sampling
  properties.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.WalkSpectrum
open Qatlib.Concepts.CopyEvolution.SelfTomography
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolutionRefined

open Matrix
open Qatlib
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The backend-alphabet encoding into source codes is injective. -/
theorem walkGoal_backend_faithful : Function.Injective BackendAlphabet.toSourceCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [BackendAlphabet.toSourceCode]

/-- The label, Boolean, and system product basis has cardinality `qpePeakSpace D M`. -/
theorem walkGoal_peak_space (D M : ℕ) :
    Fintype.card (Fin M × (Bool × Fin D)) = qpePeakSpace D M := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, qpePeakSpace]
  ring

/-- The total source-description bit length of the loading program is at least its `n * b`
per-instruction loading bit costs. -/
theorem walkGoal_bit_time (n b a aw t m ml : ℕ) :
    (n * b) * copyEvolutionLoadingBitCost a aw t m ml ≤
      sourceBitTime (copyEvolutionLoadingProgram n b a aw t m ml) := by
  have hdesc : copyEvolutionLoadingBitCost a aw t m ml
      ≤ (sourceDescription (.qram a aw t m ml)).length := by
    exact codeBits_le_description_length _
  simp only [sourceBitTime, copyEvolutionLoadingProgram, List.map_replicate,
    List.sum_replicate]
  exact mul_le_mul_of_nonneg_left hdesc (by positivity)

/-- A nonnegative spectral decomposition of a density operator identifies ideal copy-QPE blocks
with positive semidefinite off-grid branches of nonnegative mass. -/
theorem clause16_offgrid_instrument :
    ∀ (D M : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ),
    0 < M → IsDensityOperator ρ → V ∈ Matrix.unitaryGroup (Fin D) ℂ →
    ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ → (∀ i, 0 ≤ eig i) →
      (∀ (z : Fin M) (j j' : Fin D),
        copyQPEIdealOutput D M ρ ⟨z, (false, j)⟩ ⟨z, (false, j')⟩ =
          offgridBranch D M eig V z j j') ∧
      (∀ (z : Fin M), (offgridBranch D M eig V z).PosSemidef) ∧
      (∀ (z : Fin M), 0 ≤ offgridBranchMass D M eig V z) := by
  intro D M ρ V eig hM hρ hV hs heig
  have h := (Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution.clause16_endpoint).1
    D M ρ V eig hM hρ hV hs heig
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The repeated-copy label law has total mass one and the prescribed original-law marginal at
every coordinate. -/
theorem clause16_mcopy_sampling (M m : ℕ) (p : LabelLaw M) :
    (∑ t : Fin m → Fin M, mCopyLaw M m p t = 1) ∧
    (∀ (j : Fin m) (z : Fin M),
      (∑ t : Fin m → Fin M, mCopyLaw M m p t * (if t j = z then 1 else 0)) = p.mass z) := by
  have h := (Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution.clause16_endpoint).2.1 M m p
  exact ⟨h.1, h.2⟩

/-- Combines `walkGoalEndpointSpec` with backend-encoding injectivity, the exact
phase-estimation basis size, and the loading-description cost bound. -/
theorem walkGoal_endpoint :
    Qatlib.Concepts.CopyEvolution.SelfTomography.walkGoalEndpointSpec ∧
    Function.Injective BackendAlphabet.toSourceCode ∧
    (∀ (D M : ℕ), Fintype.card (Fin M × (Bool × Fin D)) = qpePeakSpace D M) ∧
    (∀ (n b a aw t m ml : ℕ),
      (n * b) * copyEvolutionLoadingBitCost a aw t m ml ≤
        sourceBitTime (copyEvolutionLoadingProgram n b a aw t m ml)) := by
  refine ⟨Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution.walkGoal_endpoint, ?_, ?_, ?_⟩
  · exact walkGoal_backend_faithful
  · intro D M
    exact walkGoal_peak_space D M
  · intro n b a aw t m ml
    exact walkGoal_bit_time n b a aw t m ml

/-- Combines `clause16EndpointSpec` with explicit off-grid branch identification, positivity,
and repeated-copy sampling normalization and marginals. -/
theorem clause16_endpoint :
    Qatlib.Concepts.CopyEvolution.SelfTomography.clause16EndpointSpec ∧
    (∀ (D M : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ),
      0 < M → IsDensityOperator ρ → V ∈ Matrix.unitaryGroup (Fin D) ℂ →
      ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ → (∀ i, 0 ≤ eig i) →
        (∀ (z : Fin M) (j j' : Fin D),
          copyQPEIdealOutput D M ρ ⟨z, (false, j)⟩ ⟨z, (false, j')⟩ =
            offgridBranch D M eig V z j j') ∧
        (∀ (z : Fin M), (offgridBranch D M eig V z).PosSemidef) ∧
        (∀ (z : Fin M), 0 ≤ offgridBranchMass D M eig V z)) ∧
    (∀ (M m : ℕ) (p : LabelLaw M),
      (∑ t : Fin m → Fin M, mCopyLaw M m p t = 1) ∧
      (∀ (j : Fin m) (z : Fin M),
        (∑ t : Fin m → Fin M, mCopyLaw M m p t * (if t j = z then 1 else 0)) = p.mass z)) := by
  refine ⟨Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution.clause16_endpoint, ?_, ?_⟩
  · intro D M ρ V eig hM hρ hV hs heig
    exact (clause16_offgrid_instrument D M ρ V eig hM hρ hV hs heig)
  · intro M m p
    exact clause16_mcopy_sampling M m p

end Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolutionRefined
