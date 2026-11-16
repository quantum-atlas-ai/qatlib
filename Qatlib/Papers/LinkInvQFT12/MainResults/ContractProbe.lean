/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LinkInvQFT12.MainResults.Theorem2
public import Qatlib.Papers.LinkInvQFT12.MainResults.Theorem3
public import Qatlib.Papers.LinkInvQFT12.MainResults.SourceModel

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.LinkInvQFT12.MainResults

open Qatlib.Papers.LinkInvQFT12.MainResults

/-- The legacy approximation contract permits exact outputs with zero declared cost. -/
noncomputable def exactLedger {G : Type*} [Group G] (I : Qatlib.Papers.LinkInvQFT12.MainResults.ClosureInvariants G)
    (Λ : Qatlib.Papers.LinkInvQFT12.MainResults.DGIrrep G) (ε : ℝ) (hε : 0 ≤ ε) (kind : Qatlib.Papers.LinkInvQFT12.MainResults.AlgorithmKind) :
    Qatlib.Papers.LinkInvQFT12.MainResults.LinkAlgorithm G I Λ ε where
  kind := kind
  cost := fun _ _ _ _ => 0
  outTrace := I.traceClosure Λ
  outPlat := I.platClosure Λ
  trace_ok := fun _ => by simpa using hε
  plat_ok := fun _ => by simpa using hε

/-- Every choice of closure maps satisfies the legacy quantum ledger contract. -/
theorem arbitraryQuantum {G : Type*} [Group G] [Fintype G]
    (I : Qatlib.Papers.LinkInvQFT12.MainResults.ClosureInvariants G) (Λ : Qatlib.Papers.LinkInvQFT12.MainResults.DGIrrep G) {ε : ℝ} (hε : 0 < ε) :
    Qatlib.Papers.LinkInvQFT12.MainResults.theorem2_quantum_additive_approximation I Λ hε := by
  refine ⟨exactLedger I Λ ε hε.le .quantum, rfl, 0, 0, le_rfl, ?_⟩
  intros
  simp [exactLedger]

/-- A one-dimensional charge supplies the same weak classical ledger contract. -/
theorem arbitraryClassical {G : Type*} [Group G] [Fintype G]
    (I : Qatlib.Papers.LinkInvQFT12.MainResults.ClosureInvariants G) (Λ : Qatlib.Papers.LinkInvQFT12.MainResults.DGIrrep G) (hflux : Λ.chargeDim = 1)
    {ε : ℝ} (hε : 0 < ε) :
    Qatlib.Papers.LinkInvQFT12.MainResults.theorem3_classical_additive_approximation I Λ hflux hε := by
  refine ⟨exactLedger I Λ ε hε.le .classical, rfl, 0, 0, le_rfl, ?_⟩
  intros
  simp [exactLedger]

/-- The Dev identity-reduction certificate holds for every function and every class. -/
theorem arbitraryComplete {ι : Type*}
    (C : Qatlib.Papers.LinkInvQFT12.MainResults.ComplexityClass) (f : ι → ℂ) :
    Qatlib.Papers.LinkInvQFT12.MainResults.CompleteFor C f := by
  refine ⟨⟨C, id, fun _ => 0, ?_, fun _ => rfl⟩, rfl, fun _ => rfl⟩
  exact ⟨0, 0, by simp⟩

end Qatlib.Papers.LinkInvQFT12.MainResults
