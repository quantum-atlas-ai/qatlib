/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QMAExpGap16.MainResults.SourceModel
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMAExpGap16.MainResults

open Qatlib.Papers.QMAExpGap16.MainResults

/-- The exact legacy hardness predicate, using YES/NO preserving polynomial reductions. -/
def IsPSPACEHard (B : PromiseProblem) : Prop := ∀ A, A ∈ PSPACE → ReducesTo A B

/-- The exact legacy completeness predicate: membership together with hardness. -/
def IsPSPACEComplete (B : PromiseProblem) : Prop := B ∈ PSPACE ∧ IsPSPACEHard B

/-- A nonempty positive promise problem with no negative instances. -/
def allYes : PromiseProblem where
  yes := Set.univ
  no := ∅

/-- A constant accepting zero-space decider recognizes the all-positive promise. -/
theorem allYesPSPACE : allYes ∈ PSPACE := by
  refine ⟨?_, (fun _ => 0), ⟨0, 0, ?_⟩, {
    run := fun _ => true
    correct_yes := by intro x hx; rfl
    correct_no := by intro x hx; exact False.elim hx
    space := fun _ => 0
  }, ?_⟩
  · intro x _hy hn
    exact False.elim hn
  · intro n
    simp
  · intro x
    exact le_rfl

/-- The succinct-decoding interface permits an encoding that rejects every input. -/
def emptyDecoder : SuccinctMatrixEncoding where
  decode := fun _ => none

/-- The legacy universal succinct-matrix hardness claim fails for the empty decoder. -/
theorem gst_hard_counter :
    ¬ IsPSPACEHard (GappedSuccinctMatrixSingularity emptyDecoder) := by
  intro h
  obtain ⟨r⟩ := h allYes allYesPSPACE
  have hx := r.map_yes [] (Set.mem_univ [])
  obtain ⟨M, hdecode, _⟩ := hx
  change (none : Option MatrixCertificate) = some M at hdecode
  cases hdecode

/-- An everywhere-invalid ground-energy oracle also prevents PSPACE hardness.
This diagnoses the encoding requirement independently of the logarithmic hypothesis. -/
theorem emptyEnergy_bad (k : ℕ) (a b : ℕ → ℝ) :
    ¬ IsPSPACEHard (PreciseKLocalHamiltonian (fun _ => none) k a b) := by
  intro h
  obtain ⟨r⟩ := h allYes allYesPSPACE
  have hx := r.map_yes [] (Set.mem_univ [])
  obtain ⟨_hk, E, hdecode, _⟩ := hx
  change (none : Option ℝ) = some E at hdecode
  cases hdecode

/-- The untyped logarithmic binder of the legacy local-Hamiltonian theorem is real.
At n=-1 the bound forces k=0, contradicting its stated k-at-least-three assumption. -/
theorem badLogAssum (k : ℕ) (hk3 : 3 ≤ k)
    (hlog : ∃ C : ℝ, ∀ n : ℝ, (k : ℝ) ≤ C * Real.log (n + 2)) : False := by
  obtain ⟨C, hC⟩ := hlog
  have h := hC (-1)
  norm_num at h
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  linarith

end Qatlib.Papers.QMAExpGap16.MainResults
