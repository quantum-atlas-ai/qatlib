/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ShortPathOpt18.MainResults.SourceModel
public import Mathlib.Tactic

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ShortPathOpt18.MainResults
open Qatlib.Papers.ShortPathOpt18.MainResults

/-- The assumed ground-energy bounds and inclusion of all excited eigenpairs in the range of `Q` imply a gap of at least `EQ - E0`. Establishing the decoupling hypothesis for the paper Hamiltonian is a separate obligation. -/
theorem source_lemma6 {N : ℕ} (energy : Config N → ℝ) (B : ℝ) (K : ℕ) (s : ℝ)
    (Q : Matrix (Config N) (Config N) ℝ) (E0 EQ : ℝ)
    (hground : IsGroundEnergy (hsMatrix energy B K s) E0)
    (hQ : IsGroundEnergyOnRange Q (hsMatrix energy B K s) EQ)
    (hdecouple : ∀ ψ E, IsEigenpair (hsMatrix energy B K s) ψ E → E0 < E →
      IsEigenpairOnRange Q (hsMatrix energy B K s) ψ E) :
    HasSpectralGap (hsMatrix energy B K s) E0 (EQ - E0) := by
  refine ⟨hground, ?_⟩
  intro ψ E hψE hE
  have hrange := hdecouple ψ E hψE hE
  have hle := hQ.2 ψ E hrange
  linarith

/-- An assumed lower bound on the compressed ground energy transfers to the full spectral gap under the stated excited-eigenpair inclusion. The compressed-energy comparison and decoupling remain hypotheses. -/
theorem source_lemma6_gap_one {N : ℕ} (energy : Config N → ℝ) (B : ℝ) (K : ℕ) (s : ℝ)
    (Q : Matrix (Config N) (Config N) ℝ) (E0 EQs EQ1 : ℝ)
    (hground : IsGroundEnergy (hsMatrix energy B K s) E0)
    (hQ : IsGroundEnergyOnRange Q (hsMatrix energy B K s) EQs)
    (hmono : EQ1 ≤ EQs)
    (hdecouple : ∀ ψ E, IsEigenpair (hsMatrix energy B K s) ψ E → E0 < E →
      IsEigenpairOnRange Q (hsMatrix energy B K s) ψ E) :
    HasSpectralGap (hsMatrix energy B K s) E0 (EQ1 - E0) := by
  have h := source_lemma6 energy B K s Q E0 EQs hground hQ hdecouple
  refine ⟨h.1, ?_⟩
  intro ψ E hψE hE
  have := h.2 ψ E hψE hE
  linarith

/-- The supplied ground-energy comparison and excited-eigenpair inclusion imply a spectral gap of at least one half. Deriving these hypotheses from the paper's Hamiltonian assumptions is a separate source bridge. -/
theorem source_theorem3_gap {N : ℕ} (energy : Config N → ℝ) (B : ℝ) (K : ℕ) (s : ℝ)
    (Q : Matrix (Config N) (Config N) ℝ) (E0 EQs : ℝ)
    (hground : IsGroundEnergy (hsMatrix energy B K s) E0)
    (hQ : IsGroundEnergyOnRange Q (hsMatrix energy B K s) EQs)
    (hE : E0 + 1 / 2 ≤ EQs)
    (hdecouple : ∀ ψ E, IsEigenpair (hsMatrix energy B K s) ψ E → E0 < E →
      IsEigenpairOnRange Q (hsMatrix energy B K s) ψ E) :
    HasSpectralGap (hsMatrix energy B K s) E0 (1 / 2) := by
  have h := source_lemma6 energy B K s Q E0 EQs hground hQ hdecouple
  refine ⟨h.1, ?_⟩
  intro ψ E hψE hE
  have := h.2 ψ E hψE hE
  linarith

end Qatlib.Papers.ShortPathOpt18.MainResults
